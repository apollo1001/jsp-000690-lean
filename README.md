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



\## Mathematical correspondence



The formalisation uses:



\- Vertex := Fin 9

\- Li's explicit 22-edge hypergraph

\- direct verification that every edge has three distinct vertices

\- Li's explicit proper 3-colouring

\- exhaustive verification of all 2^9 = 512 binary colourings to prove non-2-colourability

\- Li's 22 explicit edge-deletion 2-colouring certificates

\- Li's 9 explicit vertex-deletion 2-colouring certificates

\- direct computation of minimum degree at least 7



Thus JSP690.jsp\_000690 gives a positive answer to JSP-000690.



\## Source



Ruiliang Li,

On an Erdős--Lovász problem: 3-critical 3-graphs of minimum degree 7,

2025\.



Erdős Problem #834 / JSP-000690.

