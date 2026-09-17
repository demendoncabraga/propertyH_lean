# Expanders prevent Property (H)

Lean 4 / Mathlib **v4.33.1** formalization of `paper/main.tex`.
The main theorem and ball-normalization proposition conclude degree zero.
The expander obstruction includes rational Property (H). The group corollary
exhibits one finitely generated group excluded from every Property (H) Banach
space, conditional only on the explicit Osajda expander-group hypothesis.
All other manuscript results require no external mathematical hypothesis.

For arbitrary Banach spheres, degree zero means that every induced map on
reduced integral homology vanishes. This interpretation was approved by the
author; whenever integral degree is defined using homology generators, its
value is zero. See [verification scope](docs/VERIFICATION_SCOPE.md).

## Read the formalization

| Result | File under `lean/PropertyH/` |
| --- | --- |
| Theorem 1: eventual degree zero | `CoarseMain.lean` |
| Corollary 2: ordinary and rational Property (H) obstruction | `CoarseMain.lean` |
| Uniform finite sup-space containment and c₀ | `UniversalFinite.lean`, `Corollaries.lean` |
| Corollary 3: one group excluded from every Property (H) space | `CoarseGroupCorollary.lean` |
| Lemma 4: normalization | `CoarseNormalized.lean` |
| Proposition 5: degree zero of normalized boundary map | `NullHomotopy.lean` |
| L₁ Poincaré inequality | `ExpanderEstimates.lean` |

The [source correspondence](docs/SOURCE_COVERAGE_REVIEW.md) records definitions,
statements, and proof conventions. `lean/coverage.json` inventories every source
declaration. The deleted Johnson corollary and its exclusive sphere-topology
and Brouwer dependencies are no longer in the Lean source tree. The upstream
license and provenance records are retained.

## Reproduce verification

Run `sh scripts/setup.sh` for initial setup, then:

```sh
python3 scripts/test_audit.py
sh scripts/audit.sh --terminal --modulo-external
```

The audit builds the library, checks source and proof dependencies against the
manuscript roots, verifies the inventory, rejects proof placeholders and project
axioms, and checks all axiom reports. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The unconditional `--terminal` gate deliberately
rejects the explicit Osajda hypothesis. Mathematical correspondence is reviewed
separately from these mechanical checks.
