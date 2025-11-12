# Contributing to VeriBiota

Thanks for your interest in contributing! This guide helps you build, test, and propose changes effectively.

## Build & Test
- Toolchain
  - `elan toolchain install $(cat lean-toolchain)`
  - `lake update && lake build`
- Lean tests
  - `lake env lean Tests/Main.lean`
- CLI quickstart
  - `./veribiota --help`

## Artifacts & Signing
- Emit unsigned artifacts: `make emit`
- Local signing (disposable key): see `docs/getting-started.md` for a one‑liner to create `security/jwks.json` and run `make sign-soft`.
- CI gate: Signing in CI only runs on trusted contexts with secrets; forked PRs run build/tests/docs without signing.

## Docs
- Local preview: `pip install mkdocs mkdocs-material && mkdocs serve`
- Docs live at https://veribiota.github.io/VeriBiota/

## Pull Requests
- Keep changes focused; include rationale in the PR description.
- Ensure `lake build` and docs build (`mkdocs build --strict`) pass locally.
- Avoid committing generated artifacts, secrets, or private keys.

## Coding Style
- Lean: follow existing module structure and naming conventions.
- Scripts: POSIX sh/bash, `set -euo pipefail` for reliability.
- JSON: canonicalize when comparing or hashing; prefer LF endings and trailing newline.

## Security
- Do not include secrets in logs, commits, or examples.
- Use `security/jwks.json` locally; it is `.gitignore`d.
- See `SECURITY.md` for reporting vulnerabilities.

## License
By contributing, you agree that your contributions are licensed under the Apache 2.0 License (see `LICENSE`).
