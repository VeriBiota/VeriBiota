import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "python"))

from veribiota import BundleValidationError, validate_bundle
BUNDLE_EXAMPLE = ROOT / "examples" / "veribundle" / "minimal_v0_1.json"


class VeriBundleValidationTests(unittest.TestCase):
  def setUp(self) -> None:  # type: ignore[override]
    self.example = json.loads(BUNDLE_EXAMPLE.read_text(encoding="utf-8"))

  def test_valid_bundle_parses(self) -> None:
    bundle = validate_bundle(self.example)
    self.assertEqual(bundle.bundle_version, "0.1")
    self.assertEqual(bundle.summary.overall_result, "pass")
    self.assertEqual(bundle.claims[0].id, "vb.variant.normalized")

  def test_invalid_digest_rejected(self) -> None:
    payload = dict(self.example)
    payload["subject"] = dict(payload["subject"])
    payload["subject"]["digest"] = {"alg": "sha256", "hex": "1234"}
    with self.assertRaises(BundleValidationError):
      validate_bundle(payload)

  def test_missing_claims_rejected(self) -> None:
    payload = dict(self.example)
    payload["claims"] = []
    with self.assertRaises(BundleValidationError):
      validate_bundle(payload)


if __name__ == "__main__":  # pragma: no cover
  unittest.main()
