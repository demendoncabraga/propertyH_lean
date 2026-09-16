# Source coverage review

Authoritative source: `paper/main.tex`, SHA256 `01a562684f5bbbf9ee64554ae891212cbfe0a8124d367a0e53a4c9abea760ac9`.
Reviewed 2026-09-16 against the current Lean statements and proofs. The manuscript was not edited. This is the source-to-statement review; the mechanical audit separately checks builds and axiom dependencies.

## Every numbered result

| Source label | Lean declaration (namespace `PropertyH`) | External hypothesis |
| --- | --- | --- |
| `Thm.main` | `sphere_maps_eventually_nullhomotopic_coarse` | None |
| `Cor.Prop.H`, coarse obstruction | `not_hasPropertyH_of_containsCoarseExpanders` | None |
| `Cor.Prop.H`, uniform finite sup-space containment | `not_hasPropertyH_of_uniformlyContainsFiniteSup` | None |
| `Cor.Prop.H`, c₀ example | `uniformlyContainsFiniteSup_cZero`, `not_hasPropertyH_cZero` | None |
| `Cor.no.PropH.cL.universal` | `not_standard_coarsely_universal_groups_of_hasPropertyH` | `OsajdaExpanderGroup` |
| `Corollary.Johnson` | `no_equiUniform_sphere_homeomorphisms` | None |
| `Lemma`, `Eq.prop.psi` | `exists_coarse_normalization` | None |
| `Prop.null.homotopy` | `ball_normalization_nullhomotopic` | None |

The main theorem has the actual common coarse compression and common upper control, arbitrary sequences of real Banach domains, and real L₁-embeddable targets. A version permitting different target measures is also proved. The normalization gives zero sum and unit-ball bounds at every index, global Lipschitz bounds tending to zero, and average norms converging to one, which implies the source liminf conclusion. The ball proposition retains the positive-infimum assumption; a stronger nonvanishing formulation is available internally.

## Definitions and proof dependencies

- `ExpanderFamily`, `IsVertexExpander` and `EquiCoarseGraphEmbeddings` implement the source hypotheses. Connectivity is proved. Empty finite prefixes are handled. Compression on nonnegative reals is represented by a monotone extension to all reals, with nonnegativity required on nonnegative inputs.
- `HasPropertyH` implements increasing finite-dimensional source/target stages, dense source union, a uniformly continuous ambient sphere map, and degree-one restrictions. `SphereMapDegreeOne` uses actual Mathlib integral singular homology. Homotopy invariance, zero induced maps for null-homotopies, and the degree-one obstruction are proved in `ReducedHomology` and `SphereDegree`.
- Orientation choices and the empty-sphere convention are explicit in [VERIFICATION_SCOPE.md](VERIFICATION_SCOPE.md). `HasHomeomorphicPropertyH` is retained solely as the legacy predicate; no classification or equivalence with that predicate is assumed.
- P.I. (`PIII`) is `expander_poincare`, proved by scalar coarea/cut expansion followed by L₁ integration. `expander_poincare_embedded` transports it through the specified linear isometry.
- The normalization proof uses `coarse_average_norm_tendsto_atTop`, finite-average estimates and bounded-degree ball counting. `CoarseTruncation` proves the truncation norm/error identities, 2-Lipschitz bound, centering and quantitative spread bounds. `CoarseNormalized` assembles the sequence.
- Radial extensions, common moduli on radius-two balls, continuity of the averaging homotopy, Poincaré deviation bounds, nonvanishing and the boundary homotopy are covered by `RadialExtension`, `RadialUniform`, `CommonModulus`, `AveragingFamily`, `MainProof`, `SmallDeviation`, `BoundaryHomotopy` and `NormalizedMain`.
- The Property (H) corollary uses checked finite-paving approximation (`CoarsePaving`), uniform restrictions (`VaryingMain`), Gaussian linear isometries into L₁ (`HilbertL1`) and the degree-one obstruction.
- `HilbertReduction`, `DegreeTransport` and `HilbertPropertyH` prove separability of the source and target paving span, the arbitrary-Hilbert-to-ℓ₂ reduction preserving degree, and the dense-domain-to-full-sphere comparison. Thus the target comparison is closed.
- Finite metrics embed isometrically in finite sup spaces (`FiniteSup`) and in c₀ (`CZero`). `not_hasPropertyH_cZero` is proved directly. `hasTrivialCotype_cZero` is retained as an independent legacy supporting result, not needed by the revised paper.
- `UniformlyContainsFiniteSup` expresses uniform distortion containment of finite sup spaces using a common symmetric biLipschitz bound. `uniformlyContainsFiniteMetrics_of_uniformlyContainsFiniteSup` composes these embeddings with finite metric distance coordinates. `not_hasPropertyH_of_uniformlyContainsFiniteSup` then applies the expander obstruction. `uniformlyContainsFiniteSup_cZero` uses isometric zero extension. These results require no external hypothesis. The removed trivial-cotype assertion and near-isometric-distortion discussion are no longer source claims; their conditional Maurey–Pisier declarations have been removed.
- `CoarseControl` proves equivalence of ordinary two-control-function coarse embeddings and linear upper control on Cayley graphs. The group corollary rules out universality already for finitely generated groups, which suffices to rule out universality for all countable groups. Controls may depend on the group and generating set.
- Johnson's conclusion has checked finite metric coordinates, reindexing, expander existence (`PermutationExpanders.exists_expanderFamily`) and finite-sphere noncontractibility. The latter uses the retained licensed Brouwer proof port. None depends on the external Osajda hypothesis.

## Equivalent proof choices

The formal proof uses an integer-radius ball estimate `1 + k^r`, sufficient to prove the average-norm divergence, instead of duplicating the informal real-exponent estimate. It uses the positive normalization constant `1 + 2kL/h` instead of `2kL/h`. Epsilon/delta choices are packaged in quantitative lemmas rather than copying every intermediate numerical choice. These are alternative proofs of the same stated conclusions, not weakened statements.

All Banach and L₁ spaces are real, the established project convention. No complex-scalar extension is claimed. Earlier biLipschitz, quasi-isometric and diameter estimates are retained as verified support; their old source labels do not stand in for the revised coarse results.

## Contextual references

The introduction's Novikov theorem, positive Property (H) examples from Odell–Schlumprecht and Cheng–Wang, the full Aharoni theorem, historical priority, status of open questions and AI-use discussion are contextual. None is a proof dependency here. The full contextual theorems are not claimed formalized; the needed finite-metric route is proved directly.

Under this explicitly recorded mathematical-proof scope, every source result and required dependency is mapped to a checked declaration, with exactly Osajda supplied as a hypothesis. Its construction is not claimed verified. Exact declaration records, retained supporting lemmas and external assumptions are in `lean/coverage.json`.
