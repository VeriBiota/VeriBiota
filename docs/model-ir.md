# Model IR (`veribiota.model.v1`)

Deterministic JSON for submitting models to VeriBiota.

```json
{
  "schema": "veribiota.model.v1",
  "canonicalization": { "scheme": "veribiota-canon-v1", "newlineTerminated": true },
  "meta": {
    "toolchain": { "lean": "4.x.y", "mathlib": "<commit>" },
    "createdAt": "2025-11-11T00:00:00Z"
  },
  "model": {
    "id": "sir-demo",
    "species": ["S","I","R"],
    "parameters": { "beta": 0.2, "gamma": 0.1 },
    "reactions": [
      { "name":"infect",  "in":{"S":1,"I":1}, "out":{"I":2}, "rate":{"kind":"mass_action","k":"beta"} },
      { "name":"recover", "in":{"I":1},       "out":{"R":1}, "rate":{"kind":"mass_action","k":"gamma"} }
    ],
    "units": { "S":"count", "I":"count", "R":"count" }
  },
  "hash": "sha256:<64-hex>"
}
```

Rules:

- LF endings with a single trailing newline.
- Stable ordering for objects (species/reaction maps sorted by key).
- `hash` is computed over the canonical bytes after enforcing the rules above.

Use `veribiota import --in <model.json> --emit-all --out build/artifacts`
to canonicalize the model, emit certificates & checks, and attach `.sha256`
sidecars ready for signing.
