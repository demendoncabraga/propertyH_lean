# Verification scope

The final real-scalar manuscript is formalized **modulo Osajda only**.
`OsajdaExpanderGroup` is an ordinary proposition asserting that one countable,
finitely generated group has a Cayley graph containing an expander family
isometrically. It is an explicit parameter of the group corollary, not an axiom
or a proof placeholder. Osajda's construction is outside this scope; its unused
partial development has been removed.

Every other manuscript result needs no external mathematical hypothesis.
Uniform finite sup-space containment is assumed directly in the revised
corollary. No Maurey–Pisier theorem or cotype characterization is used.

## Definition conventions

All Banach and L₁ spaces are real. `HasPropertyH` follows the manuscript's ℓ₂
formulation directly: a uniformly continuous sphere map, increasing finite
source and target stages, a dense source union, and degree-one restrictions.
No additional arbitrary-Hilbert or dense-domain comparison is needed for this
manuscript; those unused generalizations have been removed.

Degree uses top reduced integral singular homology. The two generators are
existentially chosen, so the condition means degree one after choosing
orientations (absolute degree one relative to fixed orientations). The
zero-dimensional empty-sphere case is explicit; reduced H₀ treats S⁰.
No homeomorphism-classification hypothesis is assumed.

`UniformlyContainsFiniteSup` allows nonlinear maps with one common symmetric
biLipschitz bound, after rescaling the embeddings. It therefore covers linear
containment as well. Distance coordinates embed finite metrics into finite sup
spaces; zero extension embeds these spaces isometrically into c₀.

## Verification and minimality

Run `sh scripts/audit.sh --terminal --modulo-external`. It requires a complete
inventory, exactly the Osajda external hypothesis, no proof placeholders or
project axioms, and only standard foundational axioms for all declarations.

The dependency audit starts at ten statements covering the numbered results,
the c₀ witness and the Poincaré estimate. It follows both compiled proof terms
and Lean's source-reference index. Every source declaration must lie in this
closure; source references include lemmas needed to elaborate tactics even when
they disappear from the compiled proof term. This checks necessity relative to
the retained proofs, not an absolute shortest possible proof of the paper.
Supporting finite-metric biLipschitz estimates and the licensed Brouwer proof
remain because the current corollaries use them. Old theorem versions and
unrelated developments are absent.

`python3 scripts/test_audit.py` checks the external-scope gate. The unconditional
terminal gate deliberately rejects Osajda. The source-to-statement review remains
a separate mathematical obligation; contextual literature and historical claims
are not asserted to be formalized.
