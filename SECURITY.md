# Security Policy

We take security seriously and appreciate coordinated disclosures.

## Reporting a Vulnerability
- Use GitHub’s “Report a vulnerability” (Security tab → Advisories) for a private report; or
- Email security@veribiota.ai with details and a proof of concept, if possible.

We aim to acknowledge reports within 72 hours and provide status updates as we triage and remediate.

## Scope
- Open-source repository contents: Lean proofs, CLI, schemas, and scripts.
- Excludes any enterprise/private components not present in this repo.

## Keys & Signing
- Do not commit private keys. The path `security/jwks.json` is ignored by Git for local use.
- For development, generate a disposable Ed25519 key and JWKS as described in `docs/getting-started.md`.
