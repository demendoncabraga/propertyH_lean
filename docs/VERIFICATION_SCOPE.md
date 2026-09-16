# Verification scope

The agreed scope is the revised real-scalar paper **modulo Maurey–Pisier and Osajda**, as explicitly requested by the author. Every numbered result and its mathematical proof dependencies is checked in Lean relative to the two hypotheses below. The detailed source review is in [SOURCE_COVERAGE_REVIEW.md](SOURCE_COVERAGE_REVIEW.md).

## The two external hypotheses

- `MaureyPisierFiniteRepresentability X`: if `X` has trivial Rademacher cotype, each finite-dimensional real sup space has a linear embedding into `X` with lower norm bound one and upper bound `1 + ε`, for every positive `ε`.
- `OsajdaExpanderGroup`: a countable finitely generated group has a Cayley graph containing one expander sequence isometrically.

These are ordinary propositions passed as explicit theorem parameters. They are **not project axioms or `sorry` proofs**. The trivial-cotype corollary takes `hMP`; the group-universality corollary takes `hOsajda`. Their actual parameter lists are the authoritative statements. The main theorem, normalization lemma, coarse expander obstruction, Johnson conclusion, c₀ conclusion and c₀ trivial-cotype proof require neither external hypothesis.

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

The modulo terminal gate requires a complete inventory, every non-external entry verified, exactly the two named external propositions, no proof placeholders, no project axioms, and only `propext`, `Classical.choice`, and `Quot.sound` in every registered declaration's axiom report. The six audit regression tests ensure the scope gate rejects extra or substituted assumptions, incomplete coverage and unverified entries.

`sh scripts/audit.sh --terminal` without the scope flag deliberately rejects the two external assumptions: it is the stronger, unconditional completion gate. The successful modulo audit does not prove Maurey–Pisier or Osajda themselves.

Contextual literature citations and historical discussion are documented in the source review. They are not hypotheses used in this paper's proofs, and their full theorems are not claimed to have been re-proved here.
