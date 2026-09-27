import Mathlib.Tactic

namespace JSP690

/-
JSP-000690 / Erdős Problem #834.

Formalisation of Ruiliang Li's explicit 9-vertex, 22-edge witness.

Paper vertices 1,...,9 are represented by Lean vertices 0,...,8.

Edges are stored as lists for transparent finite computation.  `ThreeUniform`
checks that every edge has three distinct vertices and that the underlying
Finsets of the 22 edges are pairwise distinct, so ordering cannot create
duplicate mathematical hyperedges.
-/

abbrev Vertex := Fin 9
abbrev Edge := List Vertex
abbrev Hypergraph := List Edge

def edge (a b c : Vertex) : Edge :=
  [a, b, c]

def underlyingEdge (e : Edge) : Finset Vertex :=
  e.toFinset

def allVertices : List Vertex :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8]

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

/- Small transparent Boolean iterators. -/

def allB {α : Type} : List α → (α → Bool) → Bool
  | [], _ => true
  | a :: l, p => p a && allB l p

def anyB {α : Type} : List α → (α → Bool) → Bool
  | [], _ => false
  | a :: l, p => p a || anyB l p

theorem allB_true_of_mem {α : Type} {l : List α} {p : α → Bool}
    (hAll : allB l p = true) {a : α} (ha : a ∈ l) :
    p a = true := by
  induction l with
  | nil =>
      simp at ha
  | cons b l ih =>
      simp only [allB, Bool.and_eq_true] at hAll
      rcases hAll with ⟨hb, hl⟩
      simp only [List.mem_cons] at ha
      rcases ha with hba | ha
      · subst a
        exact hb
      · exact ih hl ha

theorem anyB_true_of_mem {α : Type} {l : List α} {p : α → Bool}
    {a : α} (ha : a ∈ l) (hp : p a = true) :
    anyB l p = true := by
  induction l generalizing a with
  | nil =>
      simp at ha
  | cons b l ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [anyB, hp]
      · cases hpb : p b with
        | false =>
            simp [anyB, hpb, ih ha hp]
        | true =>
            simp [anyB, hpb]


/-- `allB` is exactly universal quantification over list membership. -/
theorem allB_eq_true_iff {α : Type} {l : List α} {p : α → Bool} :
    allB l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil =>
      simp [allB]
  | cons b l ih =>
      simp [allB, ih]

/-- `anyB` is exactly existential quantification over list membership. -/
theorem anyB_eq_true_iff {α : Type} {l : List α} {p : α → Bool} :
    anyB l p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil =>
      simp [anyB]
  | cons b l ih =>
      simp [anyB, ih]

/--
A simple 3-uniform hypergraph in the list encoding:
each edge has three distinct vertices, and the underlying sets are distinct.
-/
def ThreeUniform (H : Hypergraph) : Prop :=
  allB H (fun e => decide e.Nodup && decide (e.length = 3)) = true ∧
  (H.map underlyingEdge).Nodup

/-- Boolean proper-colouring checker. -/
def ProperB {C : Type} [DecidableEq C]
    (H : Hypergraph) (c : Vertex → C) : Bool :=
  allB H fun e =>
    anyB e fun x =>
      anyB e fun y =>
        decide (c x ≠ c y)

/-- Semantic assertion that c is a proper colouring. -/
def Proper {C : Type} [DecidableEq C]
    (H : Hypergraph) (c : Vertex → C) : Prop :=
  ProperB H c = true


/--
Semantic specification of proper weak hypergraph colouring.

A colouring is proper exactly when every hyperedge contains two vertices
with different colours; equivalently, no hyperedge is monochromatic.
-/
theorem proper_iff {C : Type} [DecidableEq C]
    (H : Hypergraph) (c : Vertex → C) :
    Proper H c ↔
      ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  simp [Proper, ProperB, allB_eq_true_iff, anyB_eq_true_iff]

/-
A structural enumeration of ALL Boolean functions Fin n → Bool.

The recursive construction doubles the list at each successor:
for each colouring of Fin n, prepend false and prepend true.
-/
def allBoolFns : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 =>
      (allBoolFns n).flatMap fun f =>
        [Fin.cases false f, Fin.cases true f]

/-- Every Boolean function on Fin n occurs in allBoolFns n. -/
theorem mem_allBoolFns :
    ∀ {n : Nat} (c : Fin n → Bool), c ∈ allBoolFns n := by
  intro n
  induction n with
  | zero =>
      intro c
      have hc : c = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      simp [allBoolFns, hc]
  | succ n ih =>
      intro c
      let tail : Fin n → Bool := fun i => c i.succ
      have ht : tail ∈ allBoolFns n := ih tail
      have hc : c = Fin.cases (c 0) tail := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      cases h0 : c 0 with
      | false =>
          rw [hc, h0]
          simp only [allBoolFns]
          apply List.mem_flatMap.mpr
          refine ⟨tail, ht, ?_⟩
          simp
      | true =>
          rw [hc, h0]
          simp only [allBoolFns]
          apply List.mem_flatMap.mpr
          refine ⟨tail, ht, ?_⟩
          simp

/-- Exhaustive Boolean search over the formally proved complete enumeration. -/
def TwoColorableB (H : Hypergraph) : Bool :=
  anyB (allBoolFns 9) (fun c => ProperB H c)

/-- Ordinary semantic 2-colourability. -/
def TwoColorable (H : Hypergraph) : Prop :=
  ∃ c : Vertex → Bool, Proper H c

/-- Ordinary semantic 3-colourability. -/
def ThreeColorable (H : Hypergraph) : Prop :=
  ∃ c : Vertex → Fin 3, Proper H c

def ThreeChromatic (H : Hypergraph) : Prop :=
  ThreeColorable H ∧ ¬ TwoColorable H

def deleteEdge (H : Hypergraph) (e : Edge) : Hypergraph :=
  H.erase e

def deleteVertex (H : Hypergraph) (v : Vertex) : Hypergraph :=
  H.filter (fun e => decide (v ∉ e))

def blueSet (S : List Vertex) (v : Vertex) : Bool :=
  decide (v ∈ S)

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
  allB H (fun e => ProperB (deleteEdge H e) (cert e))

/-- Semantic edge-criticality. -/
def EdgeDeletionCritical (H : Hypergraph) : Prop :=
  ∀ e : Edge, e ∈ H → TwoColorable (deleteEdge H e)

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
  allB allVertices
    (fun v => ProperB (deleteVertex H v) (cert v))

/-- Semantic vertex-criticality. -/
def VertexDeletionCritical (H : Hypergraph) : Prop :=
  ∀ v : Vertex, TwoColorable (deleteVertex H v)

def CriticallyThreeChromatic (H : Hypergraph) : Prop :=
  ThreeChromatic H ∧
  EdgeDeletionCritical H ∧
  VertexDeletionCritical H

def degree (H : Hypergraph) (v : Vertex) : Nat :=
  (H.filter (fun e => decide (v ∈ e))).length

/-- Semantic minimum-degree condition. -/
def MinDegreeAtLeast (H : Hypergraph) (d : Nat) : Prop :=
  ∀ v : Vertex, d ≤ degree H v

def liThreeColouring (v : Vertex) : Fin 3 :=
  if v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 4 then
    0
  else if v = 6 then
    2
  else
    1

/--
If a semantic 2-colouring exists, the exhaustive Boolean search finds one.
This is the formal bridge from the search program to the mathematical notion.
-/
theorem twoColorableB_true_of_twoColorable {H : Hypergraph}
    (h : TwoColorable H) :
    TwoColorableB H = true := by
  rcases h with ⟨c, hc⟩
  exact anyB_true_of_mem (mem_allBoolFns c) hc

/-- The 22 encoded edges are distinct underlying 3-element sets. -/
theorem li_three_uniform :
    ThreeUniform liHypergraph := by
  constructor
  · decide
  · decide

theorem li_three_colorable :
    ThreeColorable liHypergraph := by
  refine ⟨liThreeColouring, ?_⟩
  change ProperB liHypergraph liThreeColouring = true
  decide

/-- Exhaustive kernel computation over the complete 512-element enumeration. -/
theorem li_twoColorableB_false :
    TwoColorableB liHypergraph = false := by
  set_option maxRecDepth 100000 in
    decide

/-- Semantic non-2-colourability, using the formally proved exhaustion bridge. -/
theorem li_not_two_colorable :
    ¬ TwoColorable liHypergraph := by
  intro h
  have ht : TwoColorableB liHypergraph = true :=
    twoColorableB_true_of_twoColorable h
  have hf : TwoColorableB liHypergraph = false :=
    li_twoColorableB_false
  rw [hf] at ht
  cases ht

/-- Li's 22 edge-deletion certificates all check. -/
theorem li_edge_certificates :
    EdgeDeletionCertificatesValidB liHypergraph liEdgeColouring = true := by
  decide

/-- Therefore deletion of every edge is semantically 2-colourable. -/
theorem li_edge_deletion_critical :
    EdgeDeletionCritical liHypergraph := by
  intro e he
  refine ⟨liEdgeColouring e, ?_⟩
  exact allB_true_of_mem li_edge_certificates he

/-- Li's 9 vertex-deletion certificates all check. -/
theorem li_vertex_certificates :
    VertexDeletionCertificatesValidB liHypergraph liVertexColouring = true := by
  decide

theorem vertex_mem_allVertices (v : Vertex) :
    v ∈ allVertices := by
  fin_cases v <;> decide

/-- Therefore deletion of every vertex is semantically 2-colourable. -/
theorem li_vertex_deletion_critical :
    VertexDeletionCritical liHypergraph := by
  intro v
  refine ⟨liVertexColouring v, ?_⟩
  exact allB_true_of_mem li_vertex_certificates (vertex_mem_allVertices v)

theorem li_critically_three_chromatic :
    CriticallyThreeChromatic liHypergraph := by
  constructor
  · exact ⟨li_three_colorable, li_not_two_colorable⟩
  constructor
  · exact li_edge_deletion_critical
  · exact li_vertex_deletion_critical

/-- The degree sequence is 10,7,7,7,7,7,7,7,7. -/
theorem li_min_degree :
    MinDegreeAtLeast liHypergraph 7 := by
  intro v
  fin_cases v <;> decide

/--
JSP-000690.

There exists a simple three-uniform, critically three-chromatic hypergraph
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
