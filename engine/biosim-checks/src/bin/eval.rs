use anyhow::{anyhow, Context, Result};
use serde::Deserialize;
use std::fs::File;
use std::io::{BufRead, BufReader};

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
    PosConc { species: Vec<String>, tolerance: Option<f64> },
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

#[derive(Deserialize)]
struct ChecksBundle {
    #[serde(rename = "modelHash")]
    model_hash: String,
    checks: Vec<CheckSpec>,
}

#[derive(Deserialize)]
struct ResultLine {
    t: f64,
    #[serde(default)]
    counts: Option<serde_json::Value>,
    #[serde(default)]
    conc: Option<Vec<f64>>,
    #[serde(rename = "modelHash")]
    model_hash: String,
    #[serde(default)]
    #[allow(dead_code)]
    checksDigest: Option<String>,
}

fn to_vec_f64(val: &serde_json::Value) -> Result<Vec<f64>> {
    let arr = val
        .as_array()
        .ok_or_else(|| anyhow!("counts must be an array"))?;
    let mut out = Vec::with_capacity(arr.len());
    for v in arr {
        if let Some(i) = v.as_i64() {
            out.push(i as f64);
        } else if let Some(f) = v.as_f64() {
            out.push(f);
        } else {
            return Err(anyhow!("counts must contain numeric elements"));
        }
    }
    Ok(out)
}

fn weights_from_json(v: &serde_json::Value) -> Result<Vec<(usize, f64)>> {
    let obj = v
        .as_object()
        .ok_or_else(|| anyhow!("weights must be an object"))?;
    // Species indices are unknown; for demo assume order [S,I,R] and map by keys "S","I","R".
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

fn evaluate(bundle: &ChecksBundle, path: &str) -> Result<()> {
    let file = File::open(path).with_context(|| format!("open results file: {}", path))?;
    let reader = BufReader::new(file);
    let mut any_neg = false;
    let mut violated = false;
    let mut max_abs_drift = 0.0f64;
    let mut max_rel_drift = 0.0f64;
    // Baselines for invariants
    let mut base_vals: Vec<f64> = Vec::new();
    let invs: Vec<(Vec<(usize, f64)>, Tolerance, bool)> = bundle
        .checks
        .iter()
        .filter_map(|c| match c {
            CheckSpec::LinInv {
                weights,
                tolerance,
                strict,
                ..
            } => match weights_from_json(weights) {
                Ok(w) => Some((w, tolerance.clone(), *strict)),
                Err(_) => None,
            },
            _ => None,
        })
        .collect();

    for (line_no, line) in reader.lines().enumerate() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let rec: ResultLine = serde_json::from_str(&line)
            .with_context(|| format!("parse JSONL at line {}", line_no + 1))?;
        if rec.model_hash != bundle.model_hash {
            return Err(anyhow!(
                "modelHash mismatch at line {}: expected {}, got {}",
                line_no + 1,
                bundle.model_hash,
                rec.model_hash
            ));
        }
        let values: Vec<f64> = if let Some(v) = rec.conc {
            v
        } else if let Some(c) = rec.counts {
            to_vec_f64(&c)?
        } else {
            Vec::new()
        };
        if values.iter().any(|&v| v < 0.0) {
            any_neg = true;
            violated = true;
        }
        // Invariants
        if !invs.is_empty() {
            if base_vals.is_empty() {
                base_vals = invs
                    .iter()
                    .map(|(w, _, _)| w.iter().map(|(i, a)| values.get(*i).copied().unwrap_or(0.0) * a).sum())
                    .collect();
            }
            for (k, (w, tol, strict)) in invs.iter().enumerate() {
                let curr: f64 = w
                    .iter()
                    .map(|(i, a)| values.get(*i).copied().unwrap_or(0.0) * a)
                    .sum();
                let base = base_vals[k];
                let abs = (curr - base).abs();
                let rel = if base.abs() > 1e-12 { abs / base.abs() } else { 0.0 };
                if abs > max_abs_drift {
                    max_abs_drift = abs;
                }
                if rel > max_rel_drift {
                    max_rel_drift = rel;
                }
                let exceeds = match tol.mode.as_str() {
                    "absolute" => abs > tol.value,
                    "relative" => rel > tol.value,
                    _ => false,
                };
                if *strict && exceeds {
                    violated = true;
                }
            }
        }
    }

    println!(
        "tally: any_neg={} violated={} max_abs_drift={:.6} max_rel_drift={:.6}",
        any_neg, violated, max_abs_drift, max_rel_drift
    );
    Ok(())
}

fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let mut checks = None;
    let mut results = None;
    let mut json = false;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--checks" => checks = args.next(),
            "--results" => results = args.next(),
            "--json" => json = true,
            _ => {}
        }
    }
    let checks_path = checks.ok_or_else(|| anyhow!("missing --checks"))?;
    let results_path = results.ok_or_else(|| anyhow!("missing --results"))?;
    let bundle: ChecksBundle = serde_json::from_reader(
        File::open(&checks_path).with_context(|| format!("open checks: {}", checks_path))?,
    )?;
    // Intercept stdout by capturing metrics; re-run evaluation internally
    // For simplicity, duplicate logic here to produce JSON output when requested
    if json {
        // Re-evaluate in JSON mode
        let file = File::open(&results_path).with_context(|| format!("open results file: {}", results_path))?;
        let reader = BufReader::new(file);
        let mut any_neg = false;
        let mut violated = false;
        let mut max_abs_drift = 0.0f64;
        let mut max_rel_drift = 0.0f64;
        let mut base_vals: Vec<f64> = Vec::new();
        let invs: Vec<(Vec<(usize, f64)>, Tolerance, bool)> = bundle
            .checks
            .iter()
            .filter_map(|c| match c {
                CheckSpec::LinInv { weights, tolerance, strict, .. } =>
                    match weights_from_json(weights) {
                        Ok(w) => Some((w, tolerance.clone(), *strict)),
                        Err(_) => None,
                    },
                _ => None,
            })
            .collect();
        for (line_no, line) in reader.lines().enumerate() {
            let line = line?;
            if line.trim().is_empty() { continue; }
            let rec: ResultLine = serde_json::from_str(&line)
                .with_context(|| format!("parse JSONL at line {}", line_no + 1))?;
            if rec.model_hash != bundle.model_hash {
                return Err(anyhow!("modelHash mismatch at line {}", line_no + 1));
            }
            let values: Vec<f64> = if let Some(v) = rec.conc {
                v
            } else if let Some(c) = rec.counts {
                to_vec_f64(&c)?
            } else { Vec::new() };
            if values.iter().any(|&v| v < 0.0) { any_neg = true; violated = true; }
            if !invs.is_empty() {
                if base_vals.is_empty() {
                    base_vals = invs.iter().map(|(w,_,_)| w.iter().map(|(i,a)| values.get(*i).copied().unwrap_or(0.0)*a).sum()).collect();
                }
                for (k, (w, tol, strict)) in invs.iter().enumerate() {
                    let curr: f64 = w.iter().map(|(i,a)| values.get(*i).copied().unwrap_or(0.0)*a).sum();
                    let base = base_vals[k];
                    let abs = (curr - base).abs();
                    let rel = if base.abs() > 1e-12 { abs / base.abs() } else { 0.0 };
                    if abs > max_abs_drift { max_abs_drift = abs; }
                    if rel > max_rel_drift { max_rel_drift = rel; }
                    let exceeds = match tol.mode.as_str() { "absolute" => abs > tol.value, "relative" => rel > tol.value, _ => false };
                    if *strict && exceeds { violated = true; }
                }
            }
        }
        let summary = serde_json::json!({
            "any_neg": any_neg,
            "violated": violated,
            "max_abs_drift": max_abs_drift,
            "max_rel_drift": max_rel_drift,
        });
        println!("{}", serde_json::to_string(&summary)?);
        Ok(())
    } else {
        evaluate(&bundle, &results_path)
    }
}
