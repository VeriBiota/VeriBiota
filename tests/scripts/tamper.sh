#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: tests/scripts/tamper.sh <checks.json>" >&2
  exit 1
fi

SOURCE="$1"
if [[ ! -f "$SOURCE" ]]; then
  echo "Checks file not found: $SOURCE" >&2
  exit 1
fi

PAYLOAD_OUT="${SOURCE%.json}.flip_payload.json"
SIG_OUT="${SOURCE%.json}.flip_sig.json"

cp "$SOURCE" "$PAYLOAD_OUT"
python3 - <<'PY' "$PAYLOAD_OUT"
import json, sys
path = sys.argv[1]
with open(path) as fh:
    data = json.load(fh)
data["modelHash"] = "sha256:deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
with open(path, "w") as fh:
    json.dump(data, fh, separators=(',', ':'))
    fh.write("\n")
PY

cp "$SOURCE" "$SIG_OUT"
python3 - <<'PY' "$SIG_OUT"
import json, sys
path = sys.argv[1]
with open(path) as fh:
    data = json.load(fh)
sig = data.get("signature", {})
jws = sig.get("jws", "")
parts = jws.split(".")
if len(parts) != 3:
    raise SystemExit("Signature JWS must have three segments to mutate")
sig_segment = list(parts[2])
if not sig_segment:
    raise SystemExit("No signature payload present to mutate")
idx = 5 if len(sig_segment) > 5 else 0
sig_segment[idx] = "A" if sig_segment[idx] != "A" else "B"
parts[2] = "".join(sig_segment)
sig["jws"] = ".".join(parts)
data["signature"] = sig
with open(path, "w") as fh:
    json.dump(data, fh, separators=(',', ':'))
    fh.write("\n")
PY

echo "Tampered payload written to $PAYLOAD_OUT"
echo "Tampered signature written to $SIG_OUT"
