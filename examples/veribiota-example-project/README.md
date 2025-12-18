# VeriBiota Example Project

This directory sketches a minimal project layout that integrates VeriBiota
EditDAG checks in CI. In practice, this would live in a separate repository,
e.g. `omniscoder/veribiota-example-project`.

## Layout

- `pyproject.toml` – depends on the `veribiota` Python package.
- `tests/dags/*.dag.json` – normalized `veribiota.edit_dag.v1` DAGs.
- `.github/workflows/veribiota.yml` – GitHub Actions workflow that runs
  VeriBiota DAG checks via the reusable action.

## JSON schema

Each DAG uses the normalized schema:

- Schema ID: `veribiota.edit_dag.v1`
- Schema file: `schema/veribiota.edit_dag.v1.json` (in the VeriBiota repo)

Example (`tests/dags/micro.dag.json`):

```json
{
  "version": "veribiota.edit_dag.v1",
  "nodes": [
    { "id": "n0", "depth": 0, "prob": 1.0 },
    { "id": "n1", "depth": 1, "prob": 1.0 }
  ],
  "edges": [
    { "src": "n0", "dst": "n1", "prob": 1.0, "event_kind": "cut" }
  ],
  "root": "n0"
}
```

## CI integration

The example workflow under `.github/workflows/veribiota.yml` shows how to wire
VeriBiota checks into any project that emits DAG JSONs:

```yaml
name: veribiota-checks

on:
  push:
    branches: ["main", "master"]
  pull_request:

jobs:
  veribiota-dag-checks:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout project
        uses: actions/checkout@v4

      - name: Run VeriBiota DAG checks
        uses: OmnisGenomics/VeriBiota/.github/actions/veribiota-check@v0.1.0
        with:
          project-name: Example
          dag-glob: tests/dags/*.dag.json
          veribiota-ref: v0.1.0
```

Projects adopting VeriBiota should:

1. Emit normalized DAGs under a predictable path (e.g. `tests/dags/*.dag.json`).
2. Add the reusable action as shown above.
3. Optionally depend on `veribiota` in `pyproject.toml` to run local checks:

   ```bash
   pip install veribiota
   veribiota check-json --input 'tests/dags/*.dag.json'
   veribiota generate-suite --input 'tests/dags/*.dag.json' --project Example --suite DAGs
   ```
