use anyhow::{Context, Result};
use biosim_checks::Evaluator;
use serde::Deserialize;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

#[derive(Deserialize)]
struct Sample {
    t: f64,
    conc: Option<Vec<f64>>,
    counts: Option<Vec<f64>>,
}

const DEFAULT_CHECKS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/checks.mass.json");
const DEFAULT_TRAJ: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/trajectory.sample.jsonl");

fn load_args() -> (PathBuf, PathBuf) {
    let mut args = env::args().skip(1);
    let mut checks = PathBuf::from(DEFAULT_CHECKS);
    let mut traj = PathBuf::from(DEFAULT_TRAJ);
    while let Some(flag) = args.next() {
        match flag.as_str() {
            "--checks" => {
                if let Some(path) = args.next() {
                    checks = PathBuf::from(path);
                }
            }
            "--trajectory" => {
                if let Some(path) = args.next() {
                    traj = PathBuf::from(path);
                }
            }
            other => eprintln!("Ignoring unknown arg: {}", other),
        }
    }
    (checks, traj)
}

fn main() -> Result<()> {
    let (checks_path, traj_path) = load_args();
    let checks = std::fs::read_to_string(&checks_path)
        .with_context(|| format!("read checks: {}", checks_path.display()))?;
    let evaluator = Evaluator::from_json(&checks)?;

    let file = File::open(&traj_path)
        .with_context(|| format!("open trajectory: {}", traj_path.display()))?;
    let reader = BufReader::new(file);

    for (idx, line) in reader.lines().enumerate() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let rec: Sample = serde_json::from_str(&line)
            .with_context(|| format!("parse trajectory line {}", idx + 1))?;
        let conc = if let Some(c) = rec.conc {
            c
        } else if let Some(counts) = rec.counts {
            counts
        } else {
            Vec::new()
        };
        let outcome = evaluator.evaluate_conc(rec.t, &conc);
        if outcome.violated {
            eprintln!(
                "[FAIL] t={:.3} max_abs={} max_rel={}",
                rec.t, outcome.max_abs_drift, outcome.max_rel_drift
            );
            std::process::exit(2);
        }
    }

    println!(
        "Trajectory {} satisfied all invariants in {}",
        traj_path.display(),
        checks_path.display()
    );
    Ok(())
}
