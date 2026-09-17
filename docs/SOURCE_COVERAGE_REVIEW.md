# Source coverage review

Authoritative manuscript: `paper/main.tex`.
SHA256: `1a4f01003edff194d8910d7853249d9e5f1760383f90bfb7d722b08ca4d4c0e1`.
Reviewed against the current revision on 2026-09-17. The manuscript was not edited.
Commented-out LaTeX statements are excluded from the inventory.

## Current numbered results

All declaration names are in namespace `PropertyH`.

| Paper | Hypotheses and conclusion | Declaration | File under `lean/PropertyH/` |
| --- | --- | --- | --- |
| Theorem 1, `Thm.main` | Finite-dimensional real normed spaces Xₙ,Yₙ with Yₙ linearly isometric to subspaces of L₁; equi-coarse expander embeddings into Xₙ; equi-uniformly continuous sphere maps Fₙ. Eventually Fₙ has degree zero. | `sphere_maps_eventually_degreeZero_coarse` | `CoarseMain.lean` |
| Corollary 2, `Cor.Prop.H` | A Banach space containing equi-coarse expanders fails Property (H), including rational Property (H). | `not_hasPropertyH_of_containsCoarseExpanders`, `not_hasRationalPropertyH_of_containsCoarseExpanders` | `CoarseMain.lean` |
| Corollary 2, in particular | Uniform distortion containment of every finite sup space implies failure of Property (H). | `not_hasPropertyH_of_uniformlyContainsFiniteSup` | `UniversalFinite.lean` |
| Corollary 2, c₀ example | c₀ uniformly contains the finite sup spaces and fails Property (H). | `uniformlyContainsFiniteSup_cZero`, `not_hasPropertyH_cZero` | `UniversalFinite.lean`, `Corollaries.lean` |
| Corollary 3, `Cor.Group` | There exists one finitely generated group that coarsely embeds into no Banach space with Property (H). | `exists_group_not_coarsely_embeddable_in_propertyH` | `CoarseGroupCorollary.lean` |
| Lemma 4, `Lemma`, `Eq.prop.psi` | Equi-coarse expander embeddings yield unit-ball maps with zero sums, average-norm liminf at least 1, and Lipschitz constants tending to zero. | `exists_coarse_normalization` | `CoarseNormalized.lean` |
| Proposition 5, `Prop.null.homotopy` | Continuous f:Bₓ→Bᵧ with positive infimum of its norm has a degree-zero normalized boundary map. | `ball_normalization_degreeZero` | `NullHomotopy.lean` |
| P.I., `PIII` | For a finite (k,h)-expander and an L₁-valued map with Lipschitz bound L, mean deviation is at most (2k/h)L. | `expander_poincare` | `ExpanderEstimates.lean` |

Only Corollary 3 has an external mathematical hypothesis, `OsajdaExpanderGroup`.
The group is selected before quantifying over all target Banach spaces. A finite
set with connected Cayley graph witnesses finite generation; its graph distance
is the word metric. Coarse embeddings have the usual two nondecreasing control
functions, with lower control tending to infinity.

## Definitions

- `UnitSphere` and `UnitBall`: unit sphere and closed unit ball.
- `IsVertexExpander`: positive h, maximum degree k, and external vertex boundary
  of size at least h|A| for every subset with 2|A| ≤ |V|.
- `ExpanderFamily`: common k,h with finite vertex cardinalities tending to infinity.
- `EquiCoarseGraphEmbeddings`: common L>0 and nondecreasing compression ρ tending
  to infinity, with ρ(d(v,u)) ≤ ‖φ(v)-φ(u)‖ ≤ Ld(v,u). The compression is extended
  to all real inputs and is nonnegative on nonnegative inputs.
- `EquiUniformContinuous`: one epsilon-delta bound works for every index.
- `HasPropertyH`: a uniformly continuous sphere map into real ℓ₂, increasing
  finite-dimensional source and target stages, dense source union, and degree-one
  restrictions, expressed by `SphereMapDegreeOne`.
- `HasRationalPropertyH`: the same data with nonzero-degree restrictions,
  expressed by `SphereMapNonzeroDegree`.
- `UniformlyContainsFiniteSup`: maps of all finite sup spaces with one common
  symmetric biLipschitz bound. This includes linear uniform containment.
- `HasDegreeZero`: all induced maps on reduced integral homology vanish. This
  interpretation was explicitly approved by the author; the main theorem now
  restricts its source and target spaces to finite dimension.
  `HasDegreeZero.homologyDegree_eq_zero` proves the integer-degree conclusion
  whenever homology generators are given.

## Proof correspondence and conventions

The null-homotopy construction remains as proof support for the current degree-zero
results and the rational obstruction. It is not retained as an obsolete public
manuscript theorem. Homology generators specify orientations; degree one permits
choosing orientations. Nonzero degree is independent of those choices. Empty
finite stages have the same explicit convention in both Property (H) definitions.

The normalization proof supplies average norms converging to 1, which implies
the stated liminf. It uses C=1+2kL/h to ensure positivity, and the sufficient
integer-radius graph-ball bound 1+k^r. These are unchanged proof choices; the
manuscript conclusions and Poincaré constant are preserved. The Poincaré theorem
has no size restriction; Lean's empty-vertex case has zero left-hand side.

Scalar coarea and integration prove Poincaré. Coarse ball counting, truncation,
and centering prove normalization. Radial extensions, averaging, and nonvanishing
prove null-homotopy and hence degree zero. Dense-stage approximation and Gaussian
L₁ isometries prove the Property (H) obstruction. Constructed expanders, finite
metric distance coordinates, and zero extension into c₀ prove the remaining
parts of Corollary 2. Osajda supplies only the group witness in Corollary 3.

## Revision and deletion review

Git's available manuscript baseline is commit `fb0f809`. Its diff confirms the
new degree-zero conclusions, rational Property (H), the replacement group
statement, and deletion of `Corollary.Johnson`. The normalization statement and
Poincaré constant are unchanged. The older trivial-cotype formulation in that
commit had already been replaced in the working formalization by finite-sup
containment before this revision.

Removed Johnson's theorem, its two assembly helpers, its reindexing and expander
existence wrappers, six exclusive topology/assembly modules, and five vendored
Brouwer modules. The license/provenance records remain. Removed old group-universality
interfaces and their wrapper module, replacing them with embedding of a specified
group. Shared expander constructions, finite metric embeddings, reduced homology,
and analytic dependencies remain.

Every retained source declaration is inventoried in `lean/coverage.json` and must
belong to the kernel/source-reference closure of the ten current manuscript roots.
Contextual Novikov results, positive Property (H) examples, historical claims, and
open-question status are not asserted to be re-proved. Scalars remain real.

The main theorem and its shared coarse null-homotopy helper now assume finite
dimension for both space families. Completeness is inferred, rather than assumed.
The previous arbitrary-Banach-space main statement is replaced in place.
