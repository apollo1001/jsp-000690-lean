import Mathlib.Tactic

namespace JSP690

/-
JSP-000690 / Erdős Problem #834.

Finite list encoding of Ruiliang Li's explicit witness.
Paper vertices 1,...,9 are represented by Lean vertices 0,...,8.

We deliberately use List rather than Finset for the finite computation layer.
This avoids version-specific Finset.all / Finset.any API issues.
Nodup checks ensure the lists encode an ordinary simple hypergraph.
-/

abbrev Vertex := Fin 9
abbrev Edge := List Vertex
abbrev Hypergraph := List Edge

def edge (a b c : Vertex) : Edge :=
  [a, b, c]

def allVertices : List Vertex :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- Li's explicit 22-edge hypergraph. -/
def liHypergraph : Hypergraph :=
  [
    edge 0 1 2, edge 0 1 8, edge 0 2 7,
    edge 0 3 5, edge 0 3 7, edge 0 3 8,
    edge 0 4 6, edge 0 4 7, edge 0 4 8,
    edge 0 5 6,
    edge 1 2 5, edge 1 2 6, edge 1 3 8,
    edge 1 4 8, edge 1 5 6,
    edge 2 3 7, edge 2 4 7, edge 2 5 6,
    edge 3 5 7, edge 3 5 8,
    edge 4 6 7, edge 4 6 8
  ]

/--
Boolean validity check for a simple 3-uniform hypergraph:
* no repeated edges;
* each edge has exactly three entries;
* no edge repeats a vertex.
-/
def ThreeUniformB (H : Hypergraph) : Bool :=
  decide H.Nodup &&
  H.all (fun e =>
    decide e.Nodup &&
    decide (e.length = 3))

def ThreeUniform (H : Hypergraph) : Prop :=
  ThreeUniformB H = true

/-- No edge is monochromatic under c. -/
def ProperB {C : Type} [DecidableEq C]
    (H : Hypergraph) (c : Vertex → C) : Bool :=
  H.all fun e =>
    e.any fun x =>
      e.any fun y =>
        decide (c x ≠ c y)

def Proper {C : Type} [DecidableEq C]
    (H : Hypergraph) (c : Vertex → C) : Prop :=
  ProperB H c = true

/--
The n-th binary colouring of the nine vertices.
The bit in position v is the colour of vertex v.
-/
def binaryColouring (n : Nat) (v : Vertex) : Bool :=
  decide (((n / (2 ^ v.val)) % 2) = 1)

/-- Exhaustive search through all 2^9 = 512 binary colourings. -/
def TwoColorableB (H : Hypergraph) : Bool :=
  (List.range 512).any
    (fun n => ProperB H (binaryColouring n))

def NotTwoColorable (H : Hypergraph) : Prop :=
  TwoColorableB H = false

def ThreeColorable (H : Hypergraph) : Prop :=
  ∃ c : Vertex → Fin 3, Proper H c

def ThreeChromatic (H : Hypergraph) : Prop :=
  ThreeColorable H ∧ NotTwoColorable H

def deleteEdge (H : Hypergraph) (e : Edge) : Hypergraph :=
  H.erase e

/--
Delete every edge incident with v.
The deleted vertex remains isolated in the ambient Fin 9.
-/
def deleteVertex (H : Hypergraph) (v : Vertex) : Hypergraph :=
  H.filter (fun e => decide (v ∉ e))

def blueSet (S : List Vertex) (v : Vertex) : Bool :=
  decide (v ∈ S)

/-
Li's 22 explicit edge-deletion colouring certificates,
translated from paper vertices 1,...,9 to Lean 0,...,8.
-/
def liEdgeColouring (e : Edge) : Vertex → Bool :=
  if e = edge 0 1 2 then blueSet [5, 6, 7, 8]
  else if e = edge 0 1 8 then blueSet [2, 3, 4, 5]
  else if e = edge 0 2 7 then blueSet [1, 3, 4, 5]
  else if e = edge 0 3 5 then blueSet [1, 6, 7, 8]
  else if e = edge 0 3 7 then blueSet [2, 4, 5, 8]
  else if e = edge 0 3 8 then blueSet [1, 4, 5, 7]
  else if e = edge 0 4 6 then blueSet [1, 5, 7, 8]
  else if e = edge 0 4 7 then blueSet [2, 3, 6, 8]
  else if e = edge 0 4 8 then blueSet [1, 3, 6, 7]
  else if e = edge 0 5 6 then blueSet [1, 2, 3, 4]
  else if e = edge 1 2 5 then blueSet [0, 6, 7, 8]
  else if e = edge 1 2 6 then blueSet [0, 5, 7, 8]
  else if e = edge 1 3 8 then blueSet [0, 2, 4, 5]
  else if e = edge 1 4 8 then blueSet [0, 2, 3, 6]
  else if e = edge 1 5 6 then blueSet [0, 2, 3, 4]
  else if e = edge 2 3 7 then blueSet [0, 1, 4, 5]
  else if e = edge 2 4 7 then blueSet [0, 1, 3, 6]
  else if e = edge 2 5 6 then blueSet [0, 1, 3, 4]
  else if e = edge 3 5 7 then blueSet [0, 2, 6, 8]
  else if e = edge 3 5 8 then blueSet [0, 1, 6, 7]
  else if e = edge 4 6 7 then blueSet [0, 2, 5, 8]
  else if e = edge 4 6 8 then blueSet [0, 1, 5, 7]
  else blueSet []

def EdgeDeletionCertificatesValidB
    (H : Hypergraph)
    (cert : Edge → Vertex → Bool) : Bool :=
  H.all (fun e => ProperB (deleteEdge H e) (cert e))

def EdgeDeletionCritical (H : Hypergraph) : Prop :=
  ∃ cert : Edge → Vertex → Bool,
    EdgeDeletionCertificatesValidB H cert = true

/-- Li's 9 explicit vertex-deletion colouring certificates. -/
def liVertexColouring (v : Vertex) : Vertex → Bool :=
  if v = 0 then blueSet [1, 2, 3, 4]
  else if v = 1 then blueSet [0, 2, 3, 4]
  else if v = 2 then blueSet [0, 1, 3, 4]
  else if v = 3 then blueSet [0, 1, 4, 5]
  else if v = 4 then blueSet [0, 1, 3, 6]
  else if v = 5 then blueSet [0, 1, 3, 4]
  else if v = 6 then blueSet [0, 1, 3, 4]
  else if v = 7 then blueSet [0, 1, 3, 6]
  else blueSet [0, 1, 5, 7]

def VertexDeletionCertificatesValidB
    (H : Hypergraph)
    (cert : Vertex → Vertex → Bool) : Bool :=
  allVertices.all
    (fun v => ProperB (deleteVertex H v) (cert v))

def VertexDeletionCritical (H : Hypergraph) : Prop :=
  ∃ cert : Vertex → Vertex → Bool,
    VertexDeletionCertificatesValidB H cert = true

def CriticallyThreeChromatic (H : Hypergraph) : Prop :=
  ThreeChromatic H ∧
  EdgeDeletionCritical H ∧
  VertexDeletionCritical H

def degree (H : Hypergraph) (v : Vertex) : Nat :=
  (H.filter (fun e => decide (v ∈ e))).length

def MinDegreeAtLeastB (H : Hypergraph) (d : Nat) : Bool :=
  allVertices.all (fun v => decide (d ≤ degree H v))

def MinDegreeAtLeast (H : Hypergraph) (d : Nat) : Prop :=
  MinDegreeAtLeastB H d = true

/-
Li's proper 3-colouring.

Paper colour 1: {1,2,4,5} -> Lean {0,1,3,4}
Paper colour 2: {3,6,8,9} -> Lean {2,5,7,8}
Paper colour 3: {7}       -> Lean {6}
-/
def liThreeColouring (v : Vertex) : Fin 3 :=
  if v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 4 then
    0
  else if v = 6 then
    2
  else
    1

theorem li_three_uniform :
    ThreeUniform liHypergraph := by
  change ThreeUniformB liHypergraph = true
  decide

theorem li_three_colorable :
    ThreeColorable liHypergraph := by
  refine ⟨liThreeColouring, ?_⟩
  change ProperB liHypergraph liThreeColouring = true
  decide

/-- Exhaustive verification of all 512 binary colourings. -/
theorem li_not_two_colorable :
    NotTwoColorable liHypergraph := by
  change TwoColorableB liHypergraph = false
  set_option maxRecDepth 100000 in
    decide

theorem li_edge_deletion_critical :
    EdgeDeletionCritical liHypergraph := by
  refine ⟨liEdgeColouring, ?_⟩
  decide

theorem li_vertex_deletion_critical :
    VertexDeletionCritical liHypergraph := by
  refine ⟨liVertexColouring, ?_⟩
  decide

theorem li_critically_three_chromatic :
    CriticallyThreeChromatic liHypergraph := by
  constructor
  · exact ⟨li_three_colorable, li_not_two_colorable⟩
  constructor
  · exact li_edge_deletion_critical
  · exact li_vertex_deletion_critical

theorem li_min_degree :
    MinDegreeAtLeast liHypergraph 7 := by
  change MinDegreeAtLeastB liHypergraph 7 = true
  decide

/--
JSP-000690:
There exists a simple three-uniform critically three-chromatic hypergraph
with minimum degree at least seven.
-/
theorem jsp_000690 :
    ∃ H : Hypergraph,
      ThreeUniform H ∧
      CriticallyThreeChromatic H ∧
      MinDegreeAtLeast H 7 := by
  exact ⟨
    liHypergraph,
    li_three_uniform,
    li_critically_three_chromatic,
    li_min_degree
  ⟩

#print axioms JSP690.jsp_000690

end JSP690
