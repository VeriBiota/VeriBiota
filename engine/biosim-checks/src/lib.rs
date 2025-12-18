use anyhow::{anyhow, Context, Result};
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use base64::Engine;
use ed25519_dalek::Verifier;
use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::ffi::CStr;
use std::os::raw::{c_char, c_int};
use std::sync::Mutex;

#[repr(C)]
pub struct Snapshot<'a> {
    pub t: f64,
    pub counts: Option<&'a [i64]>,
    pub conc: Option<&'a [f64]>,
}

#[repr(C)]
#[derive(Default, Clone, Copy)]
pub struct Outcome {
    pub t: f64,
    pub any_neg: bool,
    pub violated: bool,
    pub max_abs_drift: f64,
    pub max_rel_drift: f64,
}

#[derive(Clone, Copy)]
pub enum SigMode {
    Unsigned,
    SignedSoft,
    SignedEnforced,
}

impl SigMode {
    fn requires_signature(&self) -> bool {
        matches!(self, SigMode::SignedSoft | SigMode::SignedEnforced)
    }
    fn from_int(value: c_int) -> Result<Self> {
        match value {
            0 => Ok(SigMode::Unsigned),
            1 => Ok(SigMode::SignedSoft),
            2 => Ok(SigMode::SignedEnforced),
            other => Err(anyhow!("unknown signature mode {}", other)),
        }
    }
}

pub trait RuntimeChecks {
    fn preload_jwks(&mut self, _jwks_json: &str) -> Result<()> {
        Ok(())
    }
    fn load_checks(&mut self, checks_json: &str, _mode: SigMode) -> Result<()>;
    fn evaluate(&self, snap: &Snapshot) -> Outcome;
}

#[derive(Deserialize, Clone, Default, Serialize)]
struct Tolerance {
    mode: String,
    value: f64,
}

#[derive(Deserialize, Clone, Serialize)]
#[serde(tag = "type")]
enum CheckSpec {
    #[serde(rename = "positivity_counts")]
    PosCounts { species: Vec<String> },
    #[serde(rename = "positivity_conc")]
    PosConc { species: Vec<String>, #[serde(default)] tolerance: Option<f64> },
    #[serde(rename = "lin_invariant")]
    LinInv {
        name: String,
        #[serde(rename = "proofId")]
        proof_id: String,
        weights: serde_json::Value, // object: species->int
        tolerance: Tolerance,
        #[serde(default)]
        strict: bool,
        #[serde(default = "zero_baseline")]
        baseline: f64,
    },
}

#[derive(Default, Clone)]
struct ParsedInvariant {
    weights: Vec<(usize, f64)>,
    tolerance: Tolerance,
    strict: bool,
    baseline: f64,
}

#[derive(Default)]
struct StubChecks {
    model_hash: String,
    checks: Vec<CheckSpec>,
    invariants: Vec<ParsedInvariant>,
    species_index: HashMap<String, usize>,
    has_pos_counts: bool,
    has_pos_conc: bool,
}

impl RuntimeChecks for StubChecks {
    fn load_checks(&mut self, checks_json: &str, _mode: SigMode) -> Result<()> {
        let bundle: ChecksBundle = serde_json::from_str(checks_json)
            .context("parse checks bundle JSON")?;
        self.model_hash = bundle.model_hash;
        self.species_index = bundle
            .species
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), i))
            .collect();
        self.has_pos_counts = bundle
            .checks
            .iter()
            .any(|c| matches!(c, CheckSpec::PosCounts { .. }));
        self.has_pos_conc = bundle
            .checks
            .iter()
            .any(|c| matches!(c, CheckSpec::PosConc { .. }));
        self.checks = bundle.checks.clone();
        // Parse linear invariants
        self.invariants = bundle
            .checks
            .iter()
            .filter_map(|c| match c {
                CheckSpec::LinInv { weights, tolerance, strict, baseline, .. } => {
                    match weights_from_json(weights, &self.species_index) {
                        Ok(w) => Some(ParsedInvariant { weights: w, tolerance: tolerance.clone(), strict: *strict, baseline: *baseline }),
                        Err(_) => None,
                    }
                }
                _ => None,
            })
            .collect();
        Ok(())
    }

    fn evaluate(&self, snap: &Snapshot) -> Outcome {
        let mut outcome = Outcome::default();
        outcome.t = snap.t;

        // Choose working values (conc preferred, else counts)
        let mut values: Vec<f64> = Vec::new();
        if let Some(conc) = snap.conc {
            values.extend_from_slice(conc);
        } else if let Some(counts) = snap.counts {
            values.extend(counts.iter().map(|&x| x as f64));
        }

        // Positivity
        if self.has_pos_counts {
            if let Some(counts) = snap.counts {
                if counts.iter().any(|&v| v < 0) {
                    outcome.any_neg = true;
                    outcome.violated = true;
                    return outcome; // early exit on strict positivity violation
                }
            }
        }
        if self.has_pos_conc {
            if let Some(conc) = snap.conc {
                if conc.iter().any(|&v| v < 0.0 || v.is_nan()) {
                    outcome.any_neg = true;
                    outcome.violated = true;
                    return outcome;
                }
            }
        }

        // Linear invariants relative to baseline 0.0 (strict conservation)
        for inv in &self.invariants {
            let curr: f64 = inv
                .weights
                .iter()
                .map(|(i, a)| values.get(*i).copied().unwrap_or(0.0) * a)
                .sum();
            let base = inv.baseline;
            let abs = (curr - base).abs();
            let rel = if base.abs() > 1e-12 { abs / base.abs() } else { 0.0 };
            if abs > outcome.max_abs_drift {
                outcome.max_abs_drift = abs;
            }
            if rel > outcome.max_rel_drift {
                outcome.max_rel_drift = rel;
            }
            let exceeds = match inv.tolerance.mode.as_str() {
                "absolute" => abs > inv.tolerance.value,
                "relative" => rel > inv.tolerance.value,
                _ => false,
            };
            if inv.strict && exceeds {
                outcome.violated = true;
                // keep computing to retain max_* stats; do not early return here
            }
        }
        outcome
    }
}

/// High-level helper for Rust engines to evaluate VeriBiota checks without FFI.
pub struct Evaluator {
    inner: StubChecks,
}

impl Evaluator {
    pub fn from_json(checks_json: &str) -> Result<Self> {
        let mut inner = StubChecks::default();
        inner.load_checks(checks_json, SigMode::Unsigned)?;
        Ok(Self { inner })
    }

    pub fn evaluate_conc(&self, t: f64, conc: &[f64]) -> Outcome {
        let snapshot = Snapshot { t, counts: None, conc: Some(conc) };
        self.inner.evaluate(&snapshot)
    }

    pub fn evaluate_counts(&self, t: f64, counts: &[i64]) -> Outcome {
        let snapshot = Snapshot { t, counts: Some(counts), conc: None };
        self.inner.evaluate(&snapshot)
    }
}

#[derive(Deserialize, Serialize)]
struct ChecksBundle {
    #[serde(rename = "modelHash")]
    model_hash: String,
    checks: Vec<CheckSpec>,
    #[serde(default)]
    species: Vec<String>,
}

fn weights_from_json(v: &serde_json::Value, index: &HashMap<String, usize>) -> Result<Vec<(usize, f64)>> {
    let obj = v
        .as_object()
        .ok_or_else(|| anyhow!("weights must be an object"))?;
    let mut out = Vec::new();
    for (k, val) in obj.iter() {
        let idx = if !index.is_empty() {
            match index.get(k) {
                Some(i) => *i,
                None => continue,
            }
        } else {
            match k.as_str() {
                "S" => 0,
                "I" => 1,
                "R" => 2,
                _ => continue,
            }
        };
        let w = if let Some(n) = val.as_i64() {
            n as f64
        } else if let Some(f) = val.as_f64() {
            f
        } else {
            return Err(anyhow!("weight for '{}' must be numeric", k));
        };
        out.push((idx, w));
    }
    Ok(out)
}

static CHECKS_STATE: OnceCell<Mutex<Option<StubChecks>>> = OnceCell::new();

fn state() -> &'static Mutex<Option<StubChecks>> {
    CHECKS_STATE.get_or_init(|| Mutex::new(None))
}

fn cstr_to_string(ptr: *const c_char) -> Result<String> {
    if ptr.is_null() {
        return Err(anyhow!("null pointer"));
    }
    unsafe { Ok(CStr::from_ptr(ptr).to_string_lossy().into_owned()) }
}

fn with_counts<'a>(ptr: *const i64, len: usize) -> Option<&'a [i64]> {
    if ptr.is_null() || len == 0 {
        None
    } else {
        Some(unsafe { std::slice::from_raw_parts(ptr, len) })
    }
}

fn with_conc<'a>(ptr: *const f64, len: usize) -> Option<&'a [f64]> {
    if ptr.is_null() || len == 0 {
        None
    } else {
        Some(unsafe { std::slice::from_raw_parts(ptr, len) })
    }
}

#[derive(Deserialize)]
struct SignatureBlock {
    #[serde(default)]
    alg: String,
    #[serde(default)]
    kid: String,
    #[serde(default)]
    #[serde(rename = "payloadHash")]
    payload_hash: String,
    #[serde(default)]
    jws: String,
}

#[derive(Deserialize)]
struct JwksDoc {
    #[serde(default)]
    keys: Vec<JwkEntry>,
}

#[derive(Deserialize)]
struct JwkEntry {
    #[serde(default)]
    kty: String,
    #[serde(default)]
    crv: String,
    #[serde(default)]
    kid: String,
    #[serde(default)]
    x: String,
}

fn parse_jwks(raw: &str) -> Result<HashMap<String, Vec<u8>>> {
    let doc: JwksDoc = serde_json::from_str(raw).context("parse JWKS JSON")?;
    let mut map = HashMap::new();
    for key in doc.keys {
        if key.kty != "OKP" || key.crv != "Ed25519" || key.kid.is_empty() || key.x.is_empty() {
            continue;
        }
        let decoded = URL_SAFE_NO_PAD
            .decode(key.x.as_bytes())
            .map_err(|e| anyhow!("decode JWKS x: {e}"))?;
        map.insert(key.kid.clone(), decoded);
    }
    if map.is_empty() {
        Err(anyhow!("no usable Ed25519 keys in JWKS"))
    } else {
        Ok(map)
    }
}

fn zero_baseline() -> f64 {
    0.0
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    hex::encode(digest)
}

fn verify_jws(jws: &str, jwks: &HashMap<String, Vec<u8>>) -> Result<(String, Vec<u8>)> {
    let mut parts = jws.split('.');
    let header_b64 = parts.next().ok_or_else(|| anyhow!("invalid JWS"))?;
    let payload_b64 = parts.next().ok_or_else(|| anyhow!("invalid JWS"))?;
    let signature_b64 = parts.next().ok_or_else(|| anyhow!("invalid JWS"))?;
    if parts.next().is_some() {
        return Err(anyhow!("invalid JWS segment count"));
    }

    let header_bytes = URL_SAFE_NO_PAD
        .decode(header_b64.as_bytes())
        .map_err(|e| anyhow!("decode JWS header: {e}"))?;
    let payload_bytes = URL_SAFE_NO_PAD
        .decode(payload_b64.as_bytes())
        .map_err(|e| anyhow!("decode JWS payload: {e}"))?;
    let signature_bytes = URL_SAFE_NO_PAD
        .decode(signature_b64.as_bytes())
        .map_err(|e| anyhow!("decode JWS signature: {e}"))?;

    let header_json: serde_json::Value = serde_json::from_slice(&header_bytes)
        .context("parse JWS header JSON")?;
    let kid = header_json
        .get("kid")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("JWS header missing kid"))?;
    let alg = header_json
        .get("alg")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("JWS header missing alg"))?;
    if alg != "EdDSA" {
        return Err(anyhow!("unsupported JWS alg {}", alg));
    }
    let pubkey = jwks
        .get(kid)
        .ok_or_else(|| anyhow!("no jwk for kid {}", kid))?;
    let verifying_key =
        ed25519_dalek::PublicKey::from_bytes(pubkey).context("build verifying key")?;
    let sig = ed25519_dalek::Signature::from_bytes(&signature_bytes)
        .context("parse signature bytes")?;
    let signing_input = format!("{}.{}", header_b64, payload_b64);
    verifying_key
        .verify(signing_input.as_bytes(), &sig)
        .context("signature verification failed")?;
    Ok((kid.to_string(), payload_bytes))
}

fn parse_signed_bundle(
    checks_json: &str,
    sig_mode: SigMode,
    jwks_json: Option<&str>,
) -> Result<ChecksBundle> {
    let unsigned_bundle: ChecksBundle = serde_json::from_str(checks_json)
        .context("parse checks bundle JSON")?;
    if !sig_mode.requires_signature() {
        return Ok(unsigned_bundle);
    }
    let doc: serde_json::Value =
        serde_json::from_str(checks_json).context("parse checks JSON for signature")?;
    let sig_obj = doc
        .get("signature")
        .ok_or_else(|| anyhow!("missing signature"))?;
    let sig: SignatureBlock =
        serde_json::from_value(sig_obj.clone()).context("decode signature block")?;
    if sig.jws.is_empty() {
        return Err(anyhow!("missing jws in signature"));
    }
    let jwks_raw = jwks_json.ok_or_else(|| anyhow!("JWKS required for signed mode"))?;
    let jwks = parse_jwks(jwks_raw)?;
    let (_kid, payload_bytes) = verify_jws(&sig.jws, &jwks)?;
    let payload_hash = format!("sha256:{}", sha256_hex(&payload_bytes));
    if sig.payload_hash != payload_hash {
        return Err(anyhow!("payloadHash mismatch"));
    }
    let bundle: ChecksBundle = serde_json::from_slice(&payload_bytes)
        .context("parse unsigned payload from JWS")?;
    Ok(bundle)
}

#[repr(C)]
pub struct VeribiotaSnapshot {
    pub t: f64,
    pub counts: *const i64,
    pub counts_len: usize,
    pub conc: *const f64,
    pub conc_len: usize,
}

#[repr(C)]
pub struct VeribiotaOutcome {
    pub t: f64,
    pub any_neg: bool,
    pub violated: bool,
    pub max_abs_drift: f64,
    pub max_rel_drift: f64,
}

#[no_mangle]
pub extern "C" fn veribiota_checks_init(
    jwks_json: *const c_char,
    checks_json: *const c_char,
    sig_mode: c_int,
) -> c_int {
    let result: Result<(), anyhow::Error> = (|| {
        let checks_str = cstr_to_string(checks_json)?;
        let mode = SigMode::from_int(sig_mode)?;
        let jwks_str: Option<String> = if jwks_json.is_null() {
            None
        } else {
            Some(cstr_to_string(jwks_json)?)
        };
        let bundle = parse_signed_bundle(&checks_str, mode, jwks_str.as_deref())?;
        let mut guard = state()
            .lock()
            .map_err(|_| anyhow!("failed to lock runtime state"))?;
        let mut stub = guard.take().unwrap_or_default();
        stub.load_checks(&serde_json::to_string(&bundle)?, mode)?;
        *guard = Some(stub);
        Ok(())
    })();
    match result {
        Ok(_) => 0,
        Err(err) => {
            eprintln!("veribiota_checks_init error: {err}");
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn veribiota_checks_eval(
    snap: *const VeribiotaSnapshot,
    out: *mut VeribiotaOutcome,
) -> c_int {
    if snap.is_null() || out.is_null() {
        eprintln!("veribiota_checks_eval received null pointers");
        return -1;
    }
    let result: Result<(), anyhow::Error> = (|| {
        let guard = state()
            .lock()
            .map_err(|_| anyhow!("failed to lock runtime state"))?;
        let runtime = guard.as_ref().ok_or_else(|| anyhow!("runtime not initialized"))?;
        let snapshot = unsafe { &*snap };
        let snapshot = Snapshot {
            t: snapshot.t,
            counts: with_counts(snapshot.counts, snapshot.counts_len),
            conc: with_conc(snapshot.conc, snapshot.conc_len),
        };
        let evaluation = runtime.evaluate(&snapshot);
        unsafe {
            (*out).t = evaluation.t;
            (*out).any_neg = evaluation.any_neg;
            (*out).violated = evaluation.violated;
            (*out).max_abs_drift = evaluation.max_abs_drift;
            (*out).max_rel_drift = evaluation.max_rel_drift;
        }
        // Return 2 on checks violation (contract), 0 otherwise
        if evaluation.violated { Err(anyhow!("checks-violation")) } else { Ok(()) }
    })();
    match result {
        Ok(_) => 0,
        Err(err) => {
            let msg = err.to_string();
            if msg.contains("checks-violation") {
                2
            } else {
                eprintln!("veribiota_checks_eval error: {err}");
                -1
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn veribiota_checks_free() {
    if let Ok(mut guard) = state().lock() {
        *guard = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::OsRng;
    use std::ptr;
    use ed25519_dalek::Signer;

    fn make_signed_bundle() -> (String, String) {
        let keypair = ed25519_dalek::Keypair::generate(&mut OsRng);
        let payload = serde_json::json!({
            "modelHash": "sha256:test",
            "checks": []
        });
        let payload_bytes = serde_json::to_vec(&payload).unwrap();
        let payload_hash = format!("sha256:{}", sha256_hex(&payload_bytes));

        let header = serde_json::json!({
            "alg": "EdDSA",
            "kid": "test-kid",
            "veribiotaCanon": "veribiota-canon-v1"
        });
        let header_b64 = URL_SAFE_NO_PAD.encode(serde_json::to_vec(&header).unwrap());
        let payload_b64 = URL_SAFE_NO_PAD.encode(&payload_bytes);
        let signing_input = format!("{}.{}", header_b64, payload_b64);
        let sig = keypair.sign(signing_input.as_bytes());
        let sig_b64 = URL_SAFE_NO_PAD.encode(sig.to_bytes());
        let jws = format!("{}.{}.{}", header_b64, payload_b64, sig_b64);

        let signature_block = serde_json::json!({
            "alg": "Ed25519",
            "kid": "test-kid",
            "issuedAt": "2026-01-01T00:00:00Z",
            "payloadHash": payload_hash,
            "canonicalization": { "scheme": "veribiota-canon-v1", "newlineTerminated": true },
            "jws": jws
        });

        let mut full = payload;
        full["signature"] = signature_block;
        let checks_json = serde_json::to_string(&full).unwrap();

        let jwks = serde_json::json!({
            "keys": [{
                "kty": "OKP",
                "crv": "Ed25519",
                "kid": "test-kid",
                "x": URL_SAFE_NO_PAD.encode(keypair.public.to_bytes())
            }]
        });
        (checks_json, jwks.to_string())
    }

    fn init_with(mode: SigMode, checks: &str, jwks: Option<&str>) -> c_int {
        let checks_c = std::ffi::CString::new(checks).unwrap();
        let jwks_c = jwks.map(|j| std::ffi::CString::new(j).unwrap());
        let jwks_ptr = jwks_c.as_ref().map(|c| c.as_ptr()).unwrap_or(ptr::null());
        veribiota_checks_init(jwks_ptr, checks_c.as_ptr(), mode as c_int)
    }

    #[test]
    fn signed_init_ok() {
        let (checks, jwks) = make_signed_bundle();
        let code = init_with(SigMode::SignedEnforced, &checks, Some(&jwks));
        assert_eq!(code, 0);
        veribiota_checks_free();
    }

    #[test]
    fn signed_init_rejects_bad_signature() {
        let (mut checks, jwks) = make_signed_bundle();
        checks = checks.replacen("jws\":\"", "jws\":\"A", 1);
        let code = init_with(SigMode::SignedEnforced, &checks, Some(&jwks));
        assert_ne!(code, 0);
        veribiota_checks_free();
    }

    #[test]
    fn signed_init_rejects_payload_hash_mismatch() {
        let (checks, jwks) = make_signed_bundle();
        let mut json: serde_json::Value = serde_json::from_str(&checks).unwrap();
        if let Some(sig) = json.get_mut("signature") {
            if let Some(obj) = sig.as_object_mut() {
                obj.insert(
                    "payloadHash".to_string(),
                    serde_json::Value::String("sha256:deadbeef".to_string()),
                );
            }
        }
        let tampered = serde_json::to_string(&json).unwrap();
        let code = init_with(SigMode::SignedEnforced, &tampered, Some(&jwks));
        assert_ne!(code, 0);
        veribiota_checks_free();
    }

    #[test]
    fn signed_init_requires_signature() {
        let (checks, jwks) = make_signed_bundle();
        let mut json: serde_json::Value = serde_json::from_str(&checks).unwrap();
        json.as_object_mut().unwrap().remove("signature");
        let without_sig = serde_json::to_string(&json).unwrap();
        let code = init_with(SigMode::SignedEnforced, &without_sig, Some(&jwks));
        assert_ne!(code, 0);
        veribiota_checks_free();
    }

    fn sample_checks_json() -> String {
        serde_json::json!({
            "schema": "veribiota.checks.v1",
            "modelHash": "sha256:test",
            "generatedAt": "2026-01-01T00:00:00Z",
            "canonicalization": { "scheme": "veribiota-canon-v1", "newlineTerminated": true },
            "toolchain": { "lean": "4", "mathlib": "x" },
            "species": ["S", "I", "R"],
            "checks": [
                { "type": "positivity_counts", "species": ["S", "I", "R"] },
                {
                    "type": "lin_invariant",
                    "name": "mass",
                    "proofId": "demo.mass",
                    "weights": { "S": 1, "I": 1, "R": 1 },
                    "tolerance": { "mode": "absolute", "value": 0.5 },
                    "strict": true,
                    "baseline": 100.0
                }
            ]
        })
        .to_string()
    }

    #[test]
    fn positivity_violation_detected() {
        let eval = Evaluator::from_json(&sample_checks_json()).unwrap();
        let out = eval.evaluate_counts(0.0, &[99, -1, 2]);
        assert!(out.any_neg);
        assert!(out.violated);
    }

    #[test]
    fn invariant_drift_detected_with_baseline() {
        let eval = Evaluator::from_json(&sample_checks_json()).unwrap();
        // Baseline is 100; drift to 120 should violate strict absolute tol 0.5
        let out = eval.evaluate_counts(0.0, &[110, 10, 0]);
        assert!(out.violated);
        assert!(out.max_abs_drift >= 19.9);
    }

    #[test]
    fn invariant_ok_at_baseline() {
        let eval = Evaluator::from_json(&sample_checks_json()).unwrap();
        let out = eval.evaluate_counts(0.0, &[100, 0, 0]);
        assert!(!out.violated);
        assert!(out.max_abs_drift < 1e-6);
    }
}
