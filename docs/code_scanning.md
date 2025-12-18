# Code scanning (CodeQL) and `analyze-cpp`

## What `analyze-cpp` is

When GitHub Actions shows a job like `analyze (c-cpp)` (often paraphrased as “`analyze-cpp`”), that is **GitHub CodeQL’s C/C++ analysis** from `.github/workflows/codeql.yml`.

CodeQL for C/C++ is not a “lint pass”:

- It **builds** the code to capture a compilation trace (so it can model macros, includes, templates, etc.).
- It then runs **whole-program static analysis**, including dataflow/path exploration across functions and files.
- It does **not** get faster just because you already ran tests or because you’re cutting a release tag — it’s a separate analysis pipeline.

On nontrivial C/C++ codebases, CodeQL’s build + analysis can easily take **60–120 minutes** on GitHub-hosted runners.

## Why it can be slow in this repo

VeriBiota’s “product core” is Lean + deterministic artifacts; the C/C++ footprint is currently just a small adapter demo under `adapters/cpp/`.

Unfortunately, CodeQL’s default C/C++ “autobuild” heuristics tend to pick a repo’s **root build entrypoint** (often `make`). In this repo, that can trigger Lean tooling (`lake`), which is unrelated to C/C++ scanning and can turn the C/C++ CodeQL leg into a long job.

To avoid burning CI time for low marginal security value, the workflow builds only the C++ adapter explicitly (CMake) instead of running an open-ended root autobuild.

## Policy (what we run where)

- CodeQL runs on **PRs** and **pushes to `main`/`master`**.
- CodeQL does **not** run on **release tags** (`v*`) — releases should optimize for speed, determinism, and reproducibility, not marathon whole-program scans.
- The C/C++ CodeQL leg is intentionally scoped to `adapters/cpp/`. If the repo grows real C/C++ product surface area, expand the explicit build to cover it (or add a compilation database).

## How to confirm in logs

In the CodeQL job log you should see, in order:

1. CodeQL “Initialize”
2. A build step (either “Autobuild” for non-C++ languages, or the explicit CMake build for `c-cpp`)
3. CodeQL “Analyze”

If you see repeated compilation of unrelated targets, you’re probably on the default autobuild path and should tighten the build step further.

