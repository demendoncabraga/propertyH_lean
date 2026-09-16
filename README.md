# Expanders prevent Property (H)

Lean 4 / Mathlib **v4.33.1** formalization of `paper/main.tex`, modulo the explicit
Osajda expander-group hypothesis. The main theorem, normalization lemma,
Property (H) obstruction, uniform finite sup-space containment corollary,
c₀ conclusion and Johnson corollary require no external mathematical hypothesis.
Only the group-universality corollary assumes Osajda.

The source tree contains the current manuscript's results and their proof
support. Obsolete biLipschitz/quasi-isometric theorem versions, cotype results,
unused generalizations and partial Osajda-construction work have been removed.
BiLipschitz bounds remain only as intermediate estimates for the finite metric
embeddings used in the corollaries. The retained Brouwer proof has its upstream
license and provenance alongside the code.

## Read the formalization

| Result | File under `lean/PropertyH/` |
| --- | --- |
| Main coarse theorem and expander obstruction | `CoarseMain.lean` |
| Uniform finite sup-space containment corollary | `UniversalFinite.lean` |
| c₀ and Johnson conclusions | `Corollaries.lean` |
| Group-universality corollary | `StandardGroupCorollary.lean` |
| Normalization lemma | `CoarseNormalized.lean` |
| Ball-normalization proposition | `NullHomotopy.lean` |
| L₁ Poincaré inequality | `ExpanderEstimates.lean` |

See [source review](docs/SOURCE_COVERAGE_REVIEW.md) for the theorem names and
[verification scope](docs/VERIFICATION_SCOPE.md) for definitions and conventions.
`lean/coverage.json` inventories every retained source declaration.

## Reproduce verification

For initial setup, run `sh scripts/setup.sh` from the repository root. It installs
the pinned Lean toolchain, obtains the Mathlib cache and builds the library.
Then run:

```sh
python3 scripts/test_audit.py
sh scripts/audit.sh --terminal --modulo-external
```

The terminal audit builds the project, checks that every retained declaration
supports the manuscript, compares the inventory with the source tree, rejects
proof placeholders and project axioms, and checks foundational axiom dependencies.
The only allowed foundational axioms are `propext`, `Classical.choice` and
`Quot.sound`. Mathematical correspondence with the manuscript still requires
human review.

The stricter `--terminal` command without `--modulo-external` deliberately rejects
the Osajda hypothesis. It is not a claim of unconditional verification.
