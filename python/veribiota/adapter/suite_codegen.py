from __future__ import annotations

from pathlib import Path
from typing import List, Mapping, Sequence

from .schema import EditDAGPayload, load_edit_dag


def _namespace_open(module_name: str) -> str:
  parts = module_name.split(".")
  return "\n".join(f"namespace {part}" for part in parts)


def _namespace_close(module_name: str) -> str:
  parts = module_name.split(".")
  return "\n".join(f"end {part}" for part in reversed(parts))


def _render_float(value: float) -> str:
  text = repr(float(value))
  if text.endswith(".0"):
    return text[:-2] + ".0"
  return text


def _render_dag_def(name: str, payload: EditDAGPayload, idx: int) -> str:
  node_lines: List[str] = []
  for i, node in enumerate(payload.nodes):
    node_lines.append(
      "    { id := "
      + str(i)
      + ", depth := "
      + str(node.depth)
      + ", sequence := { chroms := [] }, probMass := "
      + _render_float(node.prob)
      + " }"
    )
  nodes_block = "[\n" + ",\n".join(node_lines) + "\n  ]" if node_lines else "[]"

  id_to_index = {node.node_id: i for i, node in enumerate(payload.nodes)}

  edge_lines: List[str] = []
  for edge in payload.edges:
    edge_lines.append(
      "    { src := "
      + str(id_to_index[edge.src])
      + ", dst := "
      + str(id_to_index[edge.dst])
      + ", event := none, prob := "
      + _render_float(edge.prob)
      + " }"
    )
  edges_block = "[\n" + ",\n".join(edge_lines) + "\n  ]" if edge_lines else "[]"

  root_index = id_to_index[payload.root]

  return (
    f"def {name} : Biosim.VeriBiota.EditDAG :=\n"
    "  { nodes :=\n"
    f"  {nodes_block},\n"
    "    edges :=\n"
    f"  {edges_block},\n"
    f"    root := {root_index} }}\n"
  )


def generate_lean_suite(
  dags: Sequence[EditDAGPayload] | Sequence[Mapping[str, object]],
  module_name: str,
  out_path: str | Path,
) -> Path:
  """Generate a Lean module that instantiates EditDAG values.

  The generated module defines one `EditDAG` per input DAG plus an
  `allDags` list collecting them. It intentionally avoids embedding proofs,
  leaving semantic reasoning to the VeriBiota Lean library.
  """

  if not dags:
    raise ValueError("generate_lean_suite requires at least one DAG")

  normalized: List[EditDAGPayload] = []
  for obj in dags:
    if isinstance(obj, EditDAGPayload):
      normalized.append(obj)
    elif isinstance(obj, Mapping):
      normalized.append(load_edit_dag(obj))
    else:
      raise TypeError("dags must be EditDAGPayload or mapping objects")

  module_path = Path(out_path)
  module_path.parent.mkdir(parents=True, exist_ok=True)

  # Build Lean source.
  header = "\n".join(
    [
      "import Biosim.VeriBiota.EditDAG",
      "",
      "set_option maxHeartbeats 200000",
      "",
      _namespace_open(module_name),
      "",
      "open Biosim",
      "open Biosim.VeriBiota",
      "",
    ]
  )

  body_lines: List[str] = [header]

  dag_names: List[str] = []
  for idx, payload in enumerate(normalized):
    name = f"dag_{idx}"
    dag_names.append(name)
    body_lines.append(_render_dag_def(name, payload, idx))
    body_lines.append("")

  all_dags_list = ", ".join(dag_names)
  body_lines.append(
    "def allDags : List Biosim.VeriBiota.EditDAG :=\n"
    f"  [{all_dags_list}]\n"
  )
  body_lines.append("")
  body_lines.append(_namespace_close(module_name))
  body_lines.append("")

  content = "\n".join(body_lines)
  module_path.write_text(content, encoding="utf-8")
  return module_path


def write_generated_aggregator(
  project: str,
  suite: str,
  out_path: str | Path | None = None,
) -> Path:
  """Write a small aggregator that exposes `Generated.allDags`.

  This keeps `Biosim.VeriBiota.CheckAll` stable while allowing project-
  specific modules such as `Biosim.VeriBiota.Helix.DAGs`.
  """

  module_path = Path(out_path) if out_path is not None else Path(
    "Biosim/VeriBiota/Generated.lean"
  )
  module_path.parent.mkdir(parents=True, exist_ok=True)

  lines = [
    "import Biosim.VeriBiota.EditDAG",
    f"import Biosim.VeriBiota.{project}.{suite}",
    "",
    "namespace Biosim",
    "namespace VeriBiota",
    "",
    "def Generated.allDags : List EditDAG :=",
    f"  {project}.{suite}.allDags",
    "",
    "end VeriBiota",
    "end Biosim",
    "",
  ]
  module_path.write_text("\n".join(lines), encoding="utf-8")
  return module_path


__all__ = ["generate_lean_suite", "write_generated_aggregator"]
