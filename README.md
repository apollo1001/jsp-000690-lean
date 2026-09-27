\# JSP-000690 Lean formalisation



Lean formalisation of JSP-000690 / Erdős Problem #834.



The theorem proved is:



JSP690.jsp\_000690



This formalises Ruiliang Li's explicit 9-vertex, 22-edge construction of a

three-uniform, critically three-chromatic hypergraph of minimum degree at least 7.



\## Files



\- JSP690.lean — formal proof

\- lean-toolchain — pinned Lean toolchain

\- lakefile.toml — project configuration

\- lake-manifest.json — pinned dependency manifest



\## Reproduction



From a clean checkout:



lake exe cache get

lake env lean JSP690.lean



Expected final axiom report:



'JSP690.jsp\_000690' depends on axioms: \[propext, Classical.choice, Quot.sound]



\## Formal statement



The submitted theorem is:



JSP690.jsp\_000690



It proves that there exists a hypergraph H such that:



\- H is simple and three-uniform;

\- H is three-chromatic;

\- deleting any edge makes H two-colourable;

\- deleting any vertex makes H two-colourable;

\- every vertex has degree at least 7.



This is the chromatic interpretation of JSP-000690 / Erdős Problem #834.



\## Mathematical correspondence



The formalisation uses Li's explicit witness on 9 vertices with 22 edges.



Paper vertices 1,...,9 are represented by Lean vertices 0,...,8.



\### Three-uniformity and simplicity



For computation, each edge is stored as a list of vertices.



Lean verifies that:



\- every encoded edge has exactly three entries;

\- every encoded edge contains three distinct vertices;

\- the underlying Finsets of the 22 edges are pairwise distinct.



The final condition rules out any possibility that two different list

orderings represent the same mathematical hyperedge.



\### Proper weak colouring



The computational predicate Proper is explicitly connected to the standard

semantic weak-colouring definition.



The theorem proper\_iff proves:



Proper H c if and only if for every hyperedge e in H there exist vertices

x and y in e with c x ≠ c y.



Thus the formal notion of proper colouring is exactly the ordinary statement

that no hyperedge is monochromatic.



\### Three-colourability



Li's explicit proper 3-colouring is supplied directly and checked by Lean.



\### Non-two-colourability



TwoColorable is defined semantically as:



there exists a function c : Fin 9 -> Bool such that c is a proper colouring.



The finite search used to refute this statement is not treated as an

unverified enumeration.



The formalisation defines allBoolFns n recursively and proves the theorem

mem\_allBoolFns, which states that every function Fin n -> Bool occurs in

allBoolFns n.



Thus allBoolFns 9 is a formally certified exhaustive list of all 2^9 = 512

binary colourings.



Lean then checks that none of these 512 colourings is proper.



The theorem twoColorableB\_true\_of\_twoColorable proves that if a semantic

2-colouring existed, the exhaustive Boolean search would necessarily find one.



Combining this bridge theorem with the verified false search result gives the

semantic theorem:



not TwoColorable liHypergraph.



\### Edge criticality



Li's 22 explicit edge-deletion 2-colouring certificates are encoded directly.



Lean first verifies the complete certificate table, then proves the semantic

statement that for every edge e in the hypergraph, deleteEdge H e is

two-colourable.



\### Vertex criticality



Li's 9 explicit vertex-deletion 2-colouring certificates are encoded directly.



Lean verifies all certificates and proves the semantic statement that for

every vertex v, deleteVertex H v is two-colourable.



The implementation keeps the ambient vertex type Fin 9 and removes every

edge incident with v. The deleted vertex therefore remains only as an

isolated point, which does not affect colourability.



\### Minimum degree



Lean proves directly that every vertex has degree at least 7.



For Li's witness the degree sequence is:



10, 7, 7, 7, 7, 7, 7, 7, 7.



\## Trust / axioms



The final theorem has axiom report:



\[propext, Classical.choice, Quot.sound]



The proof contains no sorry, admit, custom axiom, unsafe proof step, or

native\_decide dependency.



\## Source



Ruiliang Li,

On an Erdős--Lovász problem: 3-critical 3-graphs of minimum degree 7,

2025\.



arXiv:2512.24850



Erdős Problem #834 / JSP-000690.

