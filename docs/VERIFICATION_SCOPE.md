# Verification scope

The scope is the current real-scalar paper **modulo Osajda only**. Every numbered result and its mathematical proof dependencies is checked in Lean relative to the single external hypothesis below. The detailed source review is in [SOURCE_COVERAGE_REVIEW.md](SOURCE_COVERAGE_REVIEW.md).

## The external hypothesis

`OsajdaExpanderGroup`: a countable finitely generated group has a Cayley graph containing one expander sequence isometrically.

This is an ordinary proposition passed as an explicit parameter (`hOsajda`) to the group-universality corollary, not a project axiom or a proof placeholder. The main theorem, normalization lemma, coarse expander obstruction, uniform finite sup-space containment corollary, Johnson conclusion and c₀ conclusion require no external hypothesis.

The revised `Cor.Prop.H` assumes uniform distortion containment of finite-dimensional ℓ∞ spaces directly. `UniformlyContainsFiniteSup` expresses this by maps with a common symmetric biLipschitz bound after rescaling. The maps need not be linear, so the formal result also covers linear containment. Finite metric distance coordinates give the implication to expander containment, and zero extension verifies the c₀ example. No cotype characterization or Maurey–Pisier result is used. The obsolete Maurey–Pisier hypothesis and its conditional consequences have been removed; the independently proved c₀ cotype fact remains legacy support.

The internal high-girth, labeling and no-shortening steps of Osajda's construction are outside this agreed scope. Earlier verified supporting lemmas are retained, and the unfinished construction details are archived in `coverage.json` under `excluded_external_proof_details`; they are not additional external assumptions.

## Definition conventions

The manuscript's degree-one definition of Property (H) is used. Degree is the integer induced on top reduced integral singular homology after choosing fundamental-class generators. The manuscript fixes no orientations, so these are chosen independently; this is degree one after choosing orientations, or absolute degree one relative to separately fixed orientations. Empty sphere stages are explicitly allowed, and reduced H₀ treats S⁰ correctly. No equivalence between degree-one maps and maps homotopic to homeomorphisms is assumed.

The arbitrary real Hilbert target reduces to ℓ₂: the closed span of its countably many finite-dimensional stages is separable and embeds linearly isometrically into ℓ₂. The sphere maps and their degree-one restrictions transfer along this embedding. Dense-domain sphere maps extend uniformly, and the finite-dimensional domain paving forces source separability. These reductions are proved, not external assumptions.

## Validation

Run:

```sh
lake build
python3 scripts/test_audit.py
sh scripts/audit.sh --terminal --modulo-external
```

The modulo terminal gate requires a complete inventory, every non-external entry verified, exactly the named Osajda proposition, no proof placeholders, no project axioms, and only `propext`, `Classical.choice`, and `Quot.sound` in every registered declaration's axiom report. The eight audit regression tests ensure the scope gate rejects extra or substituted assumptions, incomplete coverage and unverified entries.

`sh scripts/audit.sh --terminal` without the scope flag deliberately rejects the Osajda assumption: it is the stronger, unconditional completion gate. The successful modulo audit does not prove Osajda itself.

Contextual literature citations and historical discussion are documented in the source review. They are not hypotheses used in this paper's proofs, and their full theorems are not claimed to have been re-proved here.
