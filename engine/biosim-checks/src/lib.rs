use anyhow::{anyhow, Result};
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

#[derive(Default)]
struct StubChecks {
    model_hash: String,
}

impl RuntimeChecks for StubChecks {
    fn load_checks(&mut self, checks_json: &str, _mode: SigMode) -> Result<()> {
        let bundle: ChecksBundle = serde_json::from_str(checks_json)?;
        self.model_hash = bundle.model_hash;
        Ok(())
    }

    fn evaluate(&self, snap: &Snapshot) -> Outcome {
        let mut outcome = Outcome::default();
        outcome.t = snap.t;
        if let Some(counts) = snap.counts {
            outcome.any_neg = counts.iter().any(|&v| v < 0);
        }
        outcome.violated = outcome.any_neg;
        outcome
    }
}

#[derive(Deserialize)]
struct ChecksBundle {
    #[serde(rename = "modelHash")]
    model_hash: String,
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
        Ok(())
    })();
    match result {
        Ok(_) => 0,
        Err(err) => {
            eprintln!("veribiota_checks_eval error: {err}");
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn veribiota_checks_free() {
    if let Ok(mut guard) = state().lock() {
        *guard = None;
    }
}
