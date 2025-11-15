use anyhow::{anyhow, Context, Result};
use once_cell::sync::OnceCell;
use serde::Deserialize;
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

#[derive(Deserialize, Clone)]
struct Tolerance {
    mode: String,
    value: f64,
}

#[derive(Deserialize, Clone)]
#[serde(tag = "type")]
enum CheckSpec {
    #[serde(rename = "positivity_counts")]
    PosCounts { species: Vec<String> },
    #[serde(rename = "positivity_conc")]
    PosConc { species: Vec<String>, #[serde(default)] tolerance: Option<f64> },
    #[serde(rename = "lin_invariant")]
    LinInv {
        name: String,
        proofId: String,
        weights: serde_json::Value, // object: species->int
        tolerance: Tolerance,
        #[serde(default)]
        strict: bool,
    },
}

#[derive(Default, Clone)]
struct ParsedInvariant {
    weights: Vec<(usize, f64)>,
    tolerance: Tolerance,
    strict: bool,
}

#[derive(Default)]
struct StubChecks {
    model_hash: String,
    checks: Vec<CheckSpec>,
    invariants: Vec<ParsedInvariant>,
    has_pos_counts: bool,
    has_pos_conc: bool,
}

impl RuntimeChecks for StubChecks {
    fn load_checks(&mut self, checks_json: &str, _mode: SigMode) -> Result<()> {
        let bundle: ChecksBundle = serde_json::from_str(checks_json)
            .context("parse checks bundle JSON")?;
        self.model_hash = bundle.model_hash;
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
                CheckSpec::LinInv { weights, tolerance, strict, .. } => {
                    match weights_from_json(weights) {
                        Ok(w) => Some(ParsedInvariant { weights: w, tolerance: tolerance.clone(), strict: *strict }),
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
            let base = 0.0f64;
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

#[derive(Deserialize)]
struct ChecksBundle {
    #[serde(rename = "modelHash")]
    model_hash: String,
    checks: Vec<CheckSpec>,
}

fn weights_from_json(v: &serde_json::Value) -> Result<Vec<(usize, f64)>> {
    let obj = v
        .as_object()
        .ok_or_else(|| anyhow!("weights must be an object"))?;
    // Species indices are unknown; for demo assume order [S, I, R] keyed by names
    let mut out = Vec::new();
    for (k, val) in obj.iter() {
        let idx = match k.as_str() {
            "S" => 0,
            "I" => 1,
            "R" => 2,
            _ => continue,
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
    _jwks_json: *const c_char,
    checks_json: *const c_char,
    sig_mode: c_int,
) -> c_int {
    let result = (|| {
        let checks_str = cstr_to_string(checks_json)?;
        let mode = SigMode::from_int(sig_mode)?;
        let mut guard = state()
            .lock()
            .map_err(|_| anyhow!("failed to lock runtime state"))?;
        let mut stub = guard.take().unwrap_or_default();
        stub.load_checks(&checks_str, mode)?;
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
    let result = (|| {
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
