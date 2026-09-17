# Verification scope

The current real-scalar manuscript is formalized modulo exactly
`OsajdaExpanderGroup`, an explicit proposition supplying a countable group with
a finite connected Cayley graph generating set and isometric expander copies.
Only `exists_group_not_coarsely_embeddable_in_propertyH` assumes this proposition.
No project axiom or proof placeholder substitutes for its construction.

## Degree and Property (H)

The manuscript uses degree zero for arbitrary Banach spheres without assuming
finite dimension or equal dimensions. With the author's explicit approval,
`HasDegreeZero` means that the induced maps on reduced integral singular homology
vanish in every nonnegative degree. It is not defined as null-homotopy. The proof
constructs a null-homotopy and deduces this conclusion. Where integer degree can
be expressed with integral homology generators,
`HasDegreeZero.homologyDegree_eq_zero` proves it is zero.

`HasPropertyH` and `HasRationalPropertyH` use the manuscript's real ℓ₂ target,
increasing finite-dimensional stages, dense source union, and respectively
one or nonzero integral degree on restrictions. Generators are existentially
chosen, so degree one means degree one after orientation choices. The ambient
zero-dimensional empty-sphere case is explicit in both definitions. Reduced H₀
handles the one-dimensional ambient case. No sphere-homology calculation or
homeomorphism-classification theorem is assumed as an external hypothesis.

## Other conventions

A finite set whose Cayley graph is connected witnesses finite generation. The
group in Corollary 3 is chosen once, before all Banach targets; coarse controls
may depend on the embedding. All target universes are supported by the theorem.

Uniform finite sup-space containment allows nonlinear biLipschitz maps with one
common bound, and therefore includes linear containment. Normalization proves
average norms converge to one. Poincaré has no size or nonemptiness restriction;
the empty sum and `0⁻¹ = 0` give zero on the left for an empty graph.

## Verification and minimality

Run `python3 scripts/test_audit.py` and
`sh scripts/audit.sh --terminal --modulo-external`. The audit builds the library,
checks every source declaration against the ten current manuscript roots and
the inventory, and permits only `propext`, `Classical.choice`, and `Quot.sound`
in axiom reports. The unconditional gate rejects Osajda as intended.

Necessity is measured relative to current proof terms and source references,
including elaboration dependencies. This is not an absolute shortest-proof claim.
Johnson's deleted corollary and its exclusive Brouwer/topology dependencies are
removed. The old universal-target group statements are replaced, not retained.
Upstream license/provenance records are preserved as attribution records.
Source-to-statement review remains distinct from mechanical verification.
