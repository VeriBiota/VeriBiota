import Mathlib.Data.List.Basic

namespace Biosim
namespace VeriBiota

/-- Representation of a collection of chromosomes and their sequences. -/
structure Genome where
  chroms : List (String × String)
  deriving Repr, Inhabited, DecidableEq

/-- Description of an edit introduced by a guide at a specific position. -/
structure CutEvent where
  chrom : String
  pos   : Nat
  guide : String
  kind  : String
  deriving Repr, Inhabited, DecidableEq

/-- Node in the edit DAG along with its probability mass. -/
structure Node where
  id        : Nat
  depth     : Nat
  sequence  : Genome
  probMass  : Float
  deriving Repr, Inhabited

/-- Edge describes a stochastic transition between nodes. -/
structure Edge where
  src   : Nat
  dst   : Nat
  event : Option CutEvent
  prob  : Float
  deriving Repr, Inhabited

/-- A finite DAG capturing edits emitted by the importer/tooling. -/
structure EditDAG where
  nodes : List Node
  edges : List Edge
  root  : Nat
  deriving Repr, Inhabited

/-- Splice helper used to describe simple cut semantics. -/
private def spliceSequence (seq : String) (pos : Nat) (segment : String) : String :=
  let head := seq.data.take pos
  let tail := seq.data.drop pos
  String.mk (head ++ segment.data ++ tail)

namespace Genome

/-- Update the specified chromosome using `f`, adding it if absent. -/
def modifyChrom (g : Genome) (chrom : String) (f : String → String) : Genome :=
  let mutated := g.chroms.map fun (name, seq) =>
    if name = chrom then (name, f seq) else (name, seq)
  if g.chroms.any (fun entry => entry.fst = chrom) then
    { g with chroms := mutated }
  else
    { g with chroms := (chrom, f "") :: mutated }

/-- Apply the pure semantics of a cut to the genome. -/
def applyCut (g : Genome) (event : CutEvent) : Genome :=
  modifyChrom g event.chrom (fun seq => spliceSequence seq event.pos event.guide)

end Genome

/-- Convenient namespace-level alias. -/
def applyCut (g : Genome) (event : CutEvent) : Genome :=
  Genome.applyCut g event

namespace EditDAG

/-- Small numerical tolerance used for probability conservation. -/
def probabilityTolerance : Float := 1e-4

/-- Approximate equality against 1.0 within the workflow tolerance. -/
def approxOne (value : Float) : Prop :=
  Float.abs (value - 1.0) ≤ probabilityTolerance

/-- Retrieve a node by identifier. -/
def getNode? (dag : EditDAG) (id : Nat) : Option Node :=
  dag.nodes.find? (fun n => n.id = id)

/-- Retrieve the distinguished root node, if present. -/
def rootNode? (dag : EditDAG) : Option Node :=
  dag.getNode? dag.root

/-- Whether an edge from `u` to `v` exists. -/
def hasEdge (dag : EditDAG) (u v : Nat) : Prop :=
  ∃ e ∈ dag.edges, e.src = u ∧ e.dst = v

/-- Outgoing edges for a particular node identifier. -/
def outgoingEdges (dag : EditDAG) (id : Nat) : List Edge :=
  dag.edges.filter (fun edge => edge.src = id)

/-- Incoming edges for a particular node identifier. -/
def incomingEdges (dag : EditDAG) (id : Nat) : List Edge :=
  dag.edges.filter (fun edge => edge.dst = id)

/-- Sum of probabilities on the outgoing fanout of a node. -/
def outgoingProbabilitySum (dag : EditDAG) (id : Nat) : Float :=
  (dag.outgoingEdges id).foldl (fun acc e => acc + e.prob) 0.0

/-- Node set that owns no outgoing transitions. -/
def leafNodes (dag : EditDAG) : List Node :=
  dag.nodes.filter fun n => (dag.outgoingEdges n.id).isEmpty

/-- Aggregate probability mass present on the leaves. -/
def leafMass (dag : EditDAG) : Float :=
  dag.leafNodes.foldl (fun acc n => acc + n.probMass) 0.0

/-- Root must be unique and start at depth 0. -/
def rootIsUnique (dag : EditDAG) : Prop :=
  ∃ rootNode, rootNode ∈ dag.nodes ∧ rootNode.id = dag.root ∧ rootNode.depth = 0 ∧
    ∀ other, other ∈ dag.nodes → other.id = dag.root → other = rootNode

/-- Edge relation induced by the DAG. -/
def EdgeRel (dag : EditDAG) (u v : Nat) : Prop :=
  dag.hasEdge u v

/-- Reachability via one-or-more edges. -/
inductive Reachable (dag : EditDAG) : Nat → Nat → Prop
  | step {u v} (h : dag.EdgeRel u v) : Reachable dag u v
  | trans {u v w} (h : dag.EdgeRel u v) (rest : Reachable dag v w) :
      Reachable dag u w

/-- The edit graph must be acyclic. -/
def acyclic (dag : EditDAG) : Prop :=
  ∀ {id}, ¬ Reachable dag id id

/-- Depth increases strictly along every realized edge. -/
def depthIncreasesAlongEdges (dag : EditDAG) : Prop :=
  ∀ e ∈ dag.edges,
    match dag.getNode? e.src, dag.getNode? e.dst with
    | some srcNode, some dstNode => srcNode.depth.succ ≤ dstNode.depth
    | _, _ => False

/-- Outgoing transitions from a branching node conserve probability mass. -/
def transitionsConserveProbability (dag : EditDAG) : Prop :=
  ∀ node ∈ dag.nodes,
    let fanout := dag.outgoingEdges node.id
    fanout.isEmpty ∨ approxOne (fanout.foldl (fun acc e => acc + e.prob) 0.0)

/-- Leaf probability mass is normalized. -/
def leavesConserveProbability (dag : EditDAG) : Prop :=
  approxOne dag.leafMass

/-- Semantic check for a single edge in the JSON. -/
def edgeRespectsSemantics (dag : EditDAG) (edge : Edge) : Prop :=
  match dag.getNode? edge.src, dag.getNode? edge.dst, edge.event with
  | some srcNode, some dstNode, some cut =>
      dstNode.sequence = applyCut srcNode.sequence cut
  | some srcNode, some dstNode, none =>
      dstNode.sequence = srcNode.sequence
  | _, _, _ => False

/-- Global semantic check for every edge. -/
def edgesRespectSemantics (dag : EditDAG) : Prop :=
  ∀ edge ∈ dag.edges, dag.edgeRespectsSemantics edge

/-- Paths extracted from JSON must reference existing nodes and edges. -/
def validPath (dag : EditDAG) : List Nat → Prop
  | [] => False
  | start :: rest =>
      start = dag.root ∧
      (∀ id ∈ start :: rest, ∃ node, dag.getNode? id = some node) ∧
      List.Chain dag.hasEdge start rest

/-- Every consecutive pair must satisfy the small-step semantics. -/
def pathRespectsSemantics (dag : EditDAG) : List Nat → Prop
  | [] => False
  | [_] => True
  | u :: v :: rest =>
      ∃ edge, edge ∈ dag.edges ∧ edge.src = u ∧ edge.dst = v ∧
        dag.edgeRespectsSemantics edge ∧
        dag.pathRespectsSemantics (v :: rest)

/-- Aggregate well-formedness predicate mirroring the JSON intent. -/
def wellFormed (dag : EditDAG) : Prop :=
  dag.acyclic ∧ dag.rootIsUnique ∧ dag.depthIncreasesAlongEdges ∧
    dag.transitionsConserveProbability ∧ dag.leavesConserveProbability ∧
    dag.edgesRespectSemantics

lemma pathRespectsSemantics_of_chain
    {dag : EditDAG} (hsem : dag.edgesRespectSemantics)
    {start : Nat} {rest : List Nat}
    (hchain : List.Chain dag.hasEdge start rest) :
    dag.pathRespectsSemantics (start :: rest) := by
  induction rest generalizing start with
  | nil =>
      simp [pathRespectsSemantics]
  | cons next tail ih =>
      obtain ⟨hedge, htail⟩ :=
        (by simpa [List.Chain] using hchain)
      rcases hedge with ⟨edge, hedgeMem, hedgeSrc, hedgeDst⟩
      have htailSem : dag.pathRespectsSemantics (next :: tail) := ih htail
      simpa [pathRespectsSemantics] using
        ⟨edge, hedgeMem, hedgeSrc, hedgeDst, hsem _ hedgeMem, htailSem⟩

/-- Along any syntactically valid path, repeated cuts agree with the JSON payload. -/
theorem all_paths_respect_semantics
    (dag : EditDAG) (h : dag.wellFormed)
    {path : List Nat} (hp : dag.validPath path) :
    dag.pathRespectsSemantics path := by
  obtain ⟨_, _, _, _, _, hsem⟩ := h
  cases path with
  | nil => cases hp
  | cons start rest =>
      rcases hp with ⟨_, _, hchain⟩
      exact pathRespectsSemantics_of_chain hsem hchain

end EditDAG

end VeriBiota
end Biosim
