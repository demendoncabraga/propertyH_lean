# Source coverage review

Authoritative manuscript: `paper/main.tex`.
SHA256: `01a562684f5bbbf9ee64554ae891212cbfe0a8124d367a0e53a4c9abea760ac9`.
Reviewed against the final-draft cleanup on 2026-09-16. The manuscript was not edited.

## Statements

All declaration names below are in namespace `PropertyH`.

| Source | Declaration | File under `lean/PropertyH/` | External hypothesis |
| --- | --- | --- | --- |
| `Thm.main` | `sphere_maps_eventually_nullhomotopic_coarse` | `CoarseMain.lean` | None |
| `Cor.Prop.H`, first assertion | `not_hasPropertyH_of_containsCoarseExpanders` | `CoarseMain.lean` | None |
| `Cor.Prop.H`, second assertion | `not_hasPropertyH_of_uniformlyContainsFiniteSup` | `UniversalFinite.lean` | None |
| c₀ example | `uniformlyContainsFiniteSup_cZero` | `UniversalFinite.lean` | None |
| c₀ conclusion | `not_hasPropertyH_cZero` | `Corollaries.lean` | None |
| `Cor.no.PropH.cL.universal` | `not_standard_coarsely_universal_groups_of_hasPropertyH` | `StandardGroupCorollary.lean` | `OsajdaExpanderGroup` |
| `Corollary.Johnson` | `no_equiUniform_sphere_homeomorphisms` | `Corollaries.lean` | None |
| `Lemma`, `Eq.prop.psi` | `exists_coarse_normalization` | `CoarseNormalized.lean` | None |
| `Prop.null.homotopy` | `ball_normalization_nullhomotopic` | `NullHomotopy.lean` | None |
| P.I. (`PIII`) | `expander_poincare` | `ExpanderEstimates.lean` | None |

The main theorem uses genuine common coarse compression and upper bounds,
arbitrary sequences of real Banach spaces, and real L₁-embeddable targets. Its
varying-measure helper is used by the corollaries. Normalization supplies zero
sum, unit-ball bounds, vanishing global Lipschitz bounds, and average norms
converging to one (hence the stated liminf). The ball proposition retains the
positive-infimum hypothesis.

## Definitions and proof support

- `Basic`, `Expanders` and `CoarseEmbeddings` define spheres, equi-uniform
  continuity, expanders and equi-coarse graph embeddings. Connectivity is proved;
  empty initial graph stages are permitted. Compression is extended monotonically
  to all reals, with nonnegativity required on nonnegative arguments.
- `PropertyH`, `SphereDegree` and `ReducedHomology` define the manuscript's
  degree-one Property (H) and prove its obstruction to null-homotopy. Orientation
  and empty-sphere conventions are specified in `VERIFICATION_SCOPE.md`.
- `PoincareScalar` and `PoincareL1` prove the Poincaré estimate by cut expansion,
  coarea and integration; `PoincareTransfer` transports it through an L₁ isometry.
- Coarse ball counting, radial truncation and centering prove the normalization.
  Radial extensions, averaging and nonvanishing then prove null-homotopy.
- `CoarsePaving`, `SphereRestrictions` and `HilbertL1` supply the finite-stage
  approximation, common continuity modulus and Gaussian L₁ embedding used in
  the Property (H) corollary.
- `FiniteSup`, `GraphMetricSpace`, `UniversalFinite` and `CZero` give the finite
  metric constructions. Their elementary biLipschitz bounds are proof support,
  not alternative versions of the paper's coarse theorem.
- `CoarseControl` obtains linear upper control on Cayley graphs from general
  coarse control. The group corollary already excludes universality for finitely
  generated groups, which suffices for the manuscript's countable-group claim.
  Controls may depend on the group and finite generating set.
- Johnson's conclusion uses the coarse theorem, constructed expanders and finite
  sphere noncontractibility. The licensed cubical-Sperner/Brouwer development is
  retained because it proves that last prerequisite without an external assumption.

## Proof choices and limits

The formal proof uses the sufficient integer-radius ball bound `1 + k^r` and
the positive normalization constant `1 + 2kL/h`. Quantitative lemmas package the
paper's epsilon/delta choices. These are proof choices, not weakened conclusions.
No complex-scalar extension is claimed. Contextual Novikov and positive Property
(H) results, the full Aharoni theorem, historical claims and open-question status
are not proof dependencies and are not claimed re-proved.

Every retained source declaration is registered in `lean/coverage.json` and
checked against the dependency closure of the ten statements above. Obsolete
biLipschitz/quasi-isometric theorem versions, cotype results, unused generalizations
and partial Osajda-construction details have been removed rather than archived in
the active source tree. Earlier versions remain in Git history.
