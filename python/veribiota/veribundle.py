from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any, Dict, List, Mapping, Optional


class BundleValidationError(ValueError):
  """Raised when a VeriBundle fails structural validation."""


@dataclass
class Digest:
  alg: str
  hex: str


@dataclass
class Attachment:
  media_type: str
  digest: Digest
  size_bytes: int
  privacy: str
  name: Optional[str] = None
  inline_base64: Optional[str] = None
  uri: Optional[str] = None


@dataclass
class SubjectRef:
  kind: str
  format: str
  digest: Digest
  uri: Optional[str] = None
  label: Optional[str] = None


@dataclass
class IoRef:
  name: str
  digest: Digest
  role: str
  uri: Optional[str] = None


@dataclass
class SoftwareRef:
  name: str
  version: str
  container_digest: Optional[Digest] = None
  git_commit: Optional[str] = None


@dataclass
class Provenance:
  inputs: List[IoRef]
  references: List[IoRef]
  software: List[SoftwareRef]
  parameters: Dict[str, Any]
  timestamp_utc: str
  annotations: List[IoRef]


@dataclass
class EvidenceRef:
  type: str
  tcb_mode: str
  attachment_digest: Digest
  summary: Optional[Dict[str, Any]] = None


@dataclass
class WitnessRef:
  type: str
  attachment_digest: Digest
  hint: Optional[str] = None


@dataclass
class ClaimResult:
  id: str
  title: str
  severity: str
  result: str
  reason: str
  scope: Optional[Dict[str, Any]] = None
  assumptions: List[str] = field(default_factory=list)
  evidence: List[EvidenceRef] = field(default_factory=list)
  witness: Optional[WitnessRef] = None
  metrics: Optional[Dict[str, Any]] = None


@dataclass
class ProfileRef:
  id: str
  digest: Digest


@dataclass
class Summary:
  overall_result: str
  highest_severity_failed: str
  profile: ProfileRef


@dataclass
class TrustedComponent:
  name: str
  version: str
  digest: Digest
  mode: str
  parameters: Optional[Dict[str, Any]] = None


@dataclass
class VeriCert:
  cert_version: str
  bundle_digest: Digest
  signer_key_id: str
  signer_alg: str
  signature: str
  bundle_payload_cbor_base64: Optional[str] = None


@dataclass
class VeriBundle:
  bundle_version: str
  subject: SubjectRef
  provenance: Provenance
  claims: List[ClaimResult]
  summary: Summary
  attachments: List[Attachment]
  tcb: List[TrustedComponent]
  assumption_defs: List[Dict[str, str]]
  ir: Dict[str, SubjectRef]
  signatures: List[VeriCert]


def _fail(path: str, message: str) -> None:
  raise BundleValidationError(f"{path}: {message}")


def _as_str(value: Any, path: str, *, allow_empty: bool = False) -> str:
  if isinstance(value, str) and (allow_empty or value):
    return value
  _fail(path, "must be a non-empty string")


def _as_int(value: Any, path: str, *, min_value: int = 0) -> int:
  if isinstance(value, int) and value >= min_value:
    return value
  _fail(path, f"must be an integer >= {min_value}")


def _as_dict(value: Any, path: str) -> Dict[str, Any]:
  if isinstance(value, Mapping):
    return dict(value)
  _fail(path, "must be an object")


def _as_enum(value: Any, path: str, allowed: List[str]) -> str:
  s = _as_str(value, path)
  if s not in allowed:
    _fail(path, f"must be one of {allowed}")
  return s


def _as_digest(value: Any, path: str) -> Digest:
  obj = _as_dict(value, path)
  alg = _as_str(obj.get("alg"), f"{path}.alg")
  hex_value = _as_str(obj.get("hex"), f"{path}.hex")
  if alg != "sha256":
    _fail(f"{path}.alg", "must be 'sha256'")
  if len(hex_value) != 64 or any(ch not in "0123456789abcdefABCDEF" for ch in hex_value):
    _fail(f"{path}.hex", "must be 64 hex characters")
  return Digest(alg=alg, hex=hex_value.lower())


def _parse_io_ref(value: Any, path: str) -> IoRef:
  obj = _as_dict(value, path)
  name = _as_str(obj.get("name"), f"{path}.name")
  digest = _as_digest(obj.get("digest"), f"{path}.digest")
  role = _as_str(obj.get("role"), f"{path}.role")
  uri = obj.get("uri")
  if uri is not None:
    _as_str(uri, f"{path}.uri", allow_empty=False)
  return IoRef(name=name, digest=digest, role=role, uri=uri)


def _parse_software_ref(value: Any, path: str) -> SoftwareRef:
  obj = _as_dict(value, path)
  name = _as_str(obj.get("name"), f"{path}.name")
  version = _as_str(obj.get("version"), f"{path}.version")
  container_digest = None
  if "container_digest" in obj:
    container_digest = _as_digest(obj["container_digest"], f"{path}.container_digest")
  git_commit = None
  if "git_commit" in obj:
    git_commit = _as_str(obj["git_commit"], f"{path}.git_commit", allow_empty=False)
  return SoftwareRef(
    name=name,
    version=version,
    container_digest=container_digest,
    git_commit=git_commit,
  )


def _parse_provenance(value: Any, path: str = "provenance") -> Provenance:
  obj = _as_dict(value, path)
  inputs_raw = obj.get("inputs")
  references_raw = obj.get("references")
  software_raw = obj.get("software")
  parameters_raw = obj.get("parameters", {})
  timestamp = _as_str(obj.get("timestamp_utc"), f"{path}.timestamp_utc")

  if not isinstance(inputs_raw, list) or not inputs_raw:
    _fail(f"{path}.inputs", "must be a non-empty array")
  if not isinstance(references_raw, list) or not references_raw:
    _fail(f"{path}.references", "must be a non-empty array")
  if not isinstance(software_raw, list) or not software_raw:
    _fail(f"{path}.software", "must be a non-empty array")
  if not isinstance(parameters_raw, Mapping):
    _fail(f"{path}.parameters", "must be an object")

  inputs = [_parse_io_ref(v, f"{path}.inputs[{idx}]") for idx, v in enumerate(inputs_raw)]
  references = [_parse_io_ref(v, f"{path}.references[{idx}]") for idx, v in enumerate(references_raw)]
  annotations_raw = obj.get("annotations", [])
  if not isinstance(annotations_raw, list):
    _fail(f"{path}.annotations", "must be an array if present")
  annotations = [_parse_io_ref(v, f"{path}.annotations[{idx}]") for idx, v in enumerate(annotations_raw)]
  software = [_parse_software_ref(v, f"{path}.software[{idx}]") for idx, v in enumerate(software_raw)]

  return Provenance(
    inputs=inputs,
    references=references,
    software=software,
    parameters=dict(parameters_raw),
    timestamp_utc=timestamp,
    annotations=annotations,
  )


def _parse_subject(value: Any, path: str = "subject") -> SubjectRef:
  obj = _as_dict(value, path)
  kind = _as_enum(
    obj.get("kind"),
    f"{path}.kind",
    ["Sequence", "VariantSet", "EditPlan", "Network", "PipelineRun", "File"],
  )
  fmt = _as_str(obj.get("format"), f"{path}.format")
  digest = _as_digest(obj.get("digest"), f"{path}.digest")
  uri = obj.get("uri")
  if uri is not None:
    _as_str(uri, f"{path}.uri", allow_empty=False)
  label = obj.get("label")
  if label is not None:
    _as_str(label, f"{path}.label", allow_empty=False)
  return SubjectRef(kind=kind, format=fmt, digest=digest, uri=uri, label=label)


def _parse_attachment(value: Any, path: str) -> Attachment:
  obj = _as_dict(value, path)
  media_type = _as_str(obj.get("media_type"), f"{path}.media_type")
  digest = _as_digest(obj.get("digest"), f"{path}.digest")
  size_bytes = _as_int(obj.get("size_bytes"), f"{path}.size_bytes", min_value=0)
  privacy = _as_enum(obj.get("privacy"), f"{path}.privacy", ["public", "restricted", "secret"])
  name = obj.get("name")
  if name is not None:
    _as_str(name, f"{path}.name", allow_empty=False)
  inline_b64 = obj.get("inline_base64")
  if inline_b64 is not None:
    _as_str(inline_b64, f"{path}.inline_base64", allow_empty=True)
  uri = obj.get("uri")
  if uri is not None:
    _as_str(uri, f"{path}.uri", allow_empty=False)
  return Attachment(
    media_type=media_type,
    digest=digest,
    size_bytes=size_bytes,
    privacy=privacy,
    name=name,
    inline_base64=inline_b64,
    uri=uri,
  )


def _parse_evidence(value: Any, path: str) -> EvidenceRef:
  obj = _as_dict(value, path)
  evidence_type = _as_enum(
    obj.get("type"),
    f"{path}.type",
    ["lean_proof", "replay_trace", "stat_test", "report", "attestation"],
  )
  tcb_mode = _as_enum(
    obj.get("tcb_mode"),
    f"{path}.tcb_mode",
    ["proof_checked", "replayable", "trusted_computation", "statistical", "human"],
  )
  attachment_digest = _as_digest(obj.get("attachment_digest"), f"{path}.attachment_digest")
  summary = None
  if "summary" in obj:
    summary_value = obj["summary"]
    if not isinstance(summary_value, Mapping):
      _fail(f"{path}.summary", "must be an object if present")
    summary = dict(summary_value)
  return EvidenceRef(
    type=evidence_type,
    tcb_mode=tcb_mode,
    attachment_digest=attachment_digest,
    summary=summary,
  )


def _parse_witness(value: Any, path: str) -> WitnessRef:
  obj = _as_dict(value, path)
  witness_type = _as_enum(
    obj.get("type"),
    f"{path}.type",
    ["counterexample", "minimal_case", "data_pointer"],
  )
  attachment_digest = _as_digest(obj.get("attachment_digest"), f"{path}.attachment_digest")
  hint = obj.get("hint")
  if hint is not None:
    _as_str(hint, f"{path}.hint", allow_empty=False)
  return WitnessRef(type=witness_type, attachment_digest=attachment_digest, hint=hint)


def _parse_claim(value: Any, path: str) -> ClaimResult:
  obj = _as_dict(value, path)
  claim_id = _as_str(obj.get("id"), f"{path}.id")
  title = _as_str(obj.get("title"), f"{path}.title")
  severity = _as_enum(obj.get("severity"), f"{path}.severity", ["blocker", "warning", "info"])
  result = _as_enum(obj.get("result"), f"{path}.result", ["pass", "fail", "inconclusive"])
  reason = _as_str(obj.get("reason"), f"{path}.reason")

  scope = None
  if "scope" in obj:
    scope_val = obj["scope"]
    if not isinstance(scope_val, Mapping):
      _fail(f"{path}.scope", "must be an object if present")
    scope = dict(scope_val)

  assumptions_raw = obj.get("assumptions", [])
  if not isinstance(assumptions_raw, list):
    _fail(f"{path}.assumptions", "must be an array if present")
  assumptions = []
  for idx, entry in enumerate(assumptions_raw):
    assumptions.append(_as_str(entry, f"{path}.assumptions[{idx}]"))

  evidence_raw = obj.get("evidence", [])
  if evidence_raw is not None and not isinstance(evidence_raw, list):
    _fail(f"{path}.evidence", "must be an array if present")
  evidence = []
  for idx, entry in enumerate(evidence_raw or []):
    evidence.append(_parse_evidence(entry, f"{path}.evidence[{idx}]"))

  witness = None
  if "witness" in obj and obj["witness"] is not None:
    witness = _parse_witness(obj["witness"], f"{path}.witness")

  metrics = None
  if "metrics" in obj:
    metrics_val = obj["metrics"]
    if not isinstance(metrics_val, Mapping):
      _fail(f"{path}.metrics", "must be an object if present")
    metrics = dict(metrics_val)

  return ClaimResult(
    id=claim_id,
    title=title,
    severity=severity,
    result=result,
    reason=reason,
    scope=scope,
    assumptions=assumptions,
    evidence=evidence,
    witness=witness,
    metrics=metrics,
  )


def _parse_profile_ref(value: Any, path: str) -> ProfileRef:
  obj = _as_dict(value, path)
  pid = _as_str(obj.get("id"), f"{path}.id")
  digest = _as_digest(obj.get("digest"), f"{path}.digest")
  return ProfileRef(id=pid, digest=digest)


def _parse_summary(value: Any, path: str = "summary") -> Summary:
  obj = _as_dict(value, path)
  overall = _as_enum(obj.get("overall_result"), f"{path}.overall_result", ["pass", "fail", "inconclusive"])
  highest = _as_enum(
    obj.get("highest_severity_failed"),
    f"{path}.highest_severity_failed",
    ["blocker", "warning", "info", "none"],
  )
  profile = _parse_profile_ref(obj.get("profile"), f"{path}.profile")
  return Summary(overall_result=overall, highest_severity_failed=highest, profile=profile)


def _parse_trusted_component(value: Any, path: str) -> TrustedComponent:
  obj = _as_dict(value, path)
  name = _as_str(obj.get("name"), f"{path}.name")
  version = _as_str(obj.get("version"), f"{path}.version")
  digest = _as_digest(obj.get("digest"), f"{path}.digest")
  mode = _as_enum(
    obj.get("mode"),
    f"{path}.mode",
    ["proof_checked", "replayable", "trusted_computation", "statistical"],
  )
  params = None
  if "parameters" in obj:
    params_val = obj["parameters"]
    if not isinstance(params_val, Mapping):
      _fail(f"{path}.parameters", "must be an object if present")
    params = dict(params_val)
  return TrustedComponent(name=name, version=version, digest=digest, mode=mode, parameters=params)


def _parse_vericert(value: Any, path: str) -> VeriCert:
  obj = _as_dict(value, path)
  cert_version = _as_str(obj.get("cert_version"), f"{path}.cert_version")
  if cert_version != "0.1":
    _fail(f"{path}.cert_version", "must be '0.1'")
  bundle_digest = _as_digest(obj.get("bundle_digest"), f"{path}.bundle_digest")
  signer = _as_dict(obj.get("signer"), f"{path}.signer")
  signer_key = _as_str(signer.get("key_id"), f"{path}.signer.key_id")
  signer_alg = _as_str(signer.get("alg"), f"{path}.signer.alg")
  signature = _as_str(obj.get("signature"), f"{path}.signature")
  payload_b64 = None
  if "bundle_payload_cbor_base64" in obj:
    payload_b64 = _as_str(obj["bundle_payload_cbor_base64"], f"{path}.bundle_payload_cbor_base64", allow_empty=False)
  return VeriCert(
    cert_version=cert_version,
    bundle_digest=bundle_digest,
    signer_key_id=signer_key,
    signer_alg=signer_alg,
    signature=signature,
    bundle_payload_cbor_base64=payload_b64,
  )


def _parse_ir(value: Any, path: str = "ir") -> Dict[str, SubjectRef]:
  if value is None:
    return {}
  if not isinstance(value, Mapping):
    _fail(path, "must be an object if present")
  return {k: _parse_subject(v, f"{path}.{k}") for k, v in value.items()}


def load_bundle(obj: Mapping[str, Any]) -> VeriBundle:
  bundle_version = _as_str(obj.get("bundle_version"), "bundle_version")
  if bundle_version != "0.1":
    _fail("bundle_version", "must be '0.1'")

  subject = _parse_subject(obj.get("subject"), "subject")
  provenance = _parse_provenance(obj.get("provenance"), "provenance")

  claims_raw = obj.get("claims")
  if not isinstance(claims_raw, list) or not claims_raw:
    _fail("claims", "must be a non-empty array")
  claims = [_parse_claim(entry, f"claims[{idx}]") for idx, entry in enumerate(claims_raw)]

  summary = _parse_summary(obj.get("summary"), "summary")

  attachments_raw = obj.get("attachments", [])
  if attachments_raw is not None and not isinstance(attachments_raw, list):
    _fail("attachments", "must be an array if present")
  attachments = [_parse_attachment(entry, f"attachments[{idx}]") for idx, entry in enumerate(attachments_raw or [])]

  tcb_raw = obj.get("tcb", [])
  if tcb_raw is not None and not isinstance(tcb_raw, list):
    _fail("tcb", "must be an array if present")
  tcb = [_parse_trusted_component(entry, f"tcb[{idx}]") for idx, entry in enumerate(tcb_raw or [])]

  assumption_defs_raw = obj.get("assumption_defs", [])
  if assumption_defs_raw is not None and not isinstance(assumption_defs_raw, list):
    _fail("assumption_defs", "must be an array if present")
  assumption_defs: List[Dict[str, str]] = []
  for idx, entry in enumerate(assumption_defs_raw or []):
    if not isinstance(entry, Mapping):
      _fail(f"assumption_defs[{idx}]", "must be an object")
    assumption_defs.append({k: v for k, v in entry.items()})

  ir = _parse_ir(obj.get("ir"), "ir")

  signatures_raw = obj.get("signatures", [])
  if signatures_raw is not None and not isinstance(signatures_raw, list):
    _fail("signatures", "must be an array if present")
  signatures = [_parse_vericert(entry, f"signatures[{idx}]") for idx, entry in enumerate(signatures_raw or [])]

  return VeriBundle(
    bundle_version=bundle_version,
    subject=subject,
    provenance=provenance,
    claims=claims,
    summary=summary,
    attachments=attachments,
    tcb=tcb,
    assumption_defs=assumption_defs,
    ir=ir,
    signatures=signatures,
  )


def validate_bundle(obj: Mapping[str, Any]) -> VeriBundle:
  """Validate and return a parsed VeriBundle structure."""

  return load_bundle(obj)


def load_bundle_json(payload: str) -> VeriBundle:
  """Parse JSON text and validate as a VeriBundle."""

  try:
    parsed = json.loads(payload)
  except json.JSONDecodeError as exc:  # pragma: no cover - surfaced to caller
    raise BundleValidationError(f"invalid JSON: {exc}") from exc
  if not isinstance(parsed, Mapping):
    _fail("$", "top-level JSON must be an object")
  return load_bundle(parsed)


__all__ = [
  "Attachment",
  "BundleValidationError",
  "ClaimResult",
  "Digest",
  "EvidenceRef",
  "IoRef",
  "ProfileRef",
  "Provenance",
  "SubjectRef",
  "Summary",
  "TrustedComponent",
  "VeriBundle",
  "VeriCert",
  "WitnessRef",
  "load_bundle",
  "load_bundle_json",
  "validate_bundle",
]
