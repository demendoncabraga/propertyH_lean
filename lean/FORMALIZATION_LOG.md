# Property (H) formalization log

## Target and current state

- Authoritative source: `paper/main.tex`, *Expanders prevent Property (H)*.
- Package: `propertyh`; Lean library and namespace: `PropertyH`; source directory: `lean/`.
- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- Build: `lake build`.
- Status: formalization started. Proposition `Prop.null.homotopy` is proved; the other numbered results and the full statement skeleton remain open.
- The absence of proof placeholders in the initial empty library is not mathematical progress.

## Coverage inventory

`lean/coverage.json` contains the five numbered results and an initial list of
proof-relevant definitions and dependencies. Verified entries now record the ball-normalization proposition and its supporting vocabulary.
This is a preliminary inventory, not a certified complete list.

Before setting `inventory_complete` to `true`, review the complete manuscript and add
every proof-relevant unnumbered claim and cited dependency. Do not silently omit a
corollary because it needs substantial external theory. Background discussion and
historical claims are not automatically formalization targets unless used in a proof.

For each entry, record the exact Lean declaration once it exists. A declaration may be
from the project or pinned Mathlib; its signature must match the required statement.
Use `in_progress` while a statement or its dependencies remain unfinished, and
`verified` only after checking its statement against the source and auditing its proof.
One source item may be split into additional entries when several declarations are needed.

## Proof debt

Four numbered results and their remaining prerequisites are open. Current explicit
proof holes: the main theorem (MainTheorem.lean), three corollaries
(Corollaries.lean), : four total. PI, PII and PIII are now proved.
Untranscribed claims in coverage.json are additional mathematical debt.
The normalization proposition, averaging inequalities and connectivity are proved.

The terminal audit rejects this initial state because the inventory is open and
the entries have no registered declarations.

## Pass history

- Setup: renamed the supplied manuscript without changing its bytes; configured
  `PropertyH`; retained the dependency pins; created an empty library, coverage inventory,
  setup script and audit scripts; updated project instructions and workflow documentation.
- Validation of this setup is recorded in `SETUP_REPORT.md` at the repository root.

- Toolchain upgrade (September 16, 2026): at the user's request, updated Lean and
  Mathlib to `v4.33.1` and regenerated the dependency manifest. Downloaded the
  compiled cache. `sh scripts/setup.sh` (including `lake build`) and
  `sh scripts/audit.sh` passed. The terminal audit correctly rejects all 18 open
  inventory entries. The manuscript is unchanged; formalization remains unstarted.

- First proof pass (September 16, 2026): validated the solo workflow on
  `Prop.null.homotopy`. Defined the sphere and closed ball using Mathlib metric
  subtypes. Proved continuous normalization, nonvanishing from positive infimum,
  and null-homotopy by convex contractibility. Completeness is not needed.
  The proposition's axiom report contains only `propext`, `Classical.choice`, and
  `Quot.sound`. Extended the preliminary inventory with missing proof obligations.
  Real scalar conventions are used for this proposition; complex normed spaces
  can also be treated through their underlying real normed-space structure.
  The full paper skeleton is not yet complete. Source review and statement
  transcription continue; no unproved external result is a project axiom.

- Statement/bootstrap pass (September 16, 2026): all five numbered results now have
  typed Lean statements. Four remain unfinished. PI, PII, PIII also have typed
  statements and open proofs. Added real Hilbert space, Property(H), vertex
  expanders, expander families, graph embeddings, and group quasi-isometry vocabulary.
  L1 in the main theorem is a genuine Lp space over an arbitrary common measure;
  the targets embed linearly isometrically into it. Corollary R03 is formulated
  more strongly using only finitely generated countable groups as test objects.
  The full dependency skeleton and inventory closure remain unfinished.
- Source review: no confirmed false statement found. Explicitly track the additive
  quasi-isometry error for the group corollary, reindexing in both sphere corollaries,
  and the relation of the manuscript's Property(H) definition to the cited original.
  Sources checked by the review worker: Osajda Theorem 4, arxiv.org/pdf/1406.5015;
  Kasparov-Yu Definition 1.1, msp.org/gt/2012/16-3/gt-v16-n3-p14-s.pdf.
- Independent proof contributions, centrally integrated: finite-average norm and
  pairwise/translation inequalities (Averages.lean); connectivity from vertex
  expansion (Connectivity.lean). These contain no proof placeholders.

- Supporting proof pass: proved norm-preserving radial extension, its sphere
  restriction and continuity including the origin (RadialExtension.lean).
  Equi-uniform continuity for families is still open. Also proved k>=2 for
  expanders with at least five vertices (DegreeBound.lean). Both modules contain
  no proof holes. The seven statement-skeleton proof holes remain unchanged.

- Supporting proof pass: BoundaryHomotopy.lean. Proved composition of normalized boundary homotopy with the nonvanishing terminal ball map.

- Supporting proof pass: AveragingFamily.lean. Proved joint continuity of finite averaging family and norm/deviation and zero-mean estimates.

- Expander and uniform-continuity pass: PI and PII are proved with their exact
  stated constants. DiameterBound.lean proves growth of finite metric balls and
  a stronger distance/log bound, then the paper's diameter bound. PairwiseDistances.lean
  proves bounded-degree ball-cardinality estimates and the pairwise logarithmic
  lower bound. Both proofs depend only on checked foundations. PIII remains open.
  RadialUniform.lean proves equi-uniform continuity of radial extensions on closed
  radius-two balls, including the near-zero cases. Five explicit proof holes remain.

- Supporting proof pass: SmallDeviation.lean. Proved the full null-homotopy conclusion from the small mean-deviation estimate, zero mean, and positive normalized spread.

- Supporting proof pass: SphereTopology.lean. Proved reduction of nullhomotopic homeomorphisms to contractibility, and empty/real-line sphere cases. Higher-dimensional sphere noncontractibility remains open.

- Supporting proof pass: NormalizedEmbeddings.lean. Proved the concrete centered/image-diameter normalization and its finite quantitative bounds. The sequence-level asymptotic assembly remains open.

- Supporting proof pass: GraphLipschitz.lean. Proved that a common edge bound yields a Lipschitz bound for graph distance by summing along shortest walks.

- Supporting proof pass: AffineShifts.lean. Proved shifted points stay in the radius-two ball and shifts do not enlarge edge distances.

- Supporting proof pass: SphereRetraction.lean. Proved finite-dimensional nullhomotopic sphere maps extend to the ball, and sphere contractibility implies a continuous retraction. No-retraction remains open.

- Supporting proof pass: PoincareScalar.lean. Proved scalar Poincare with the exact constant via cut expansion and coarea, plus generic mean-to-pairwise bounds. L1 lifting remains open.

- Poincare transport: the linear-isometric subspace reduction is proved in
  PoincareTransfer.lean, but inherits unfinished proof debt from PIII.

- Supporting proof pass: FiniteApproximation.lean. Proved finite approximation in a dense increasing paving and retention of uniform graph distortion.

- Closed PIII: PoincareL1.lean integrates the checked scalar edge inequality
  through representatives of the actual Lp functions. The exact L1 estimate and
  its isometric-target transport are proved. PI--PIII no longer carry proof debt.
- NormalizedFamily.lean assembles actual normalized embeddings with edge constants
  tending to zero and a uniform positive average-norm lower bound. It uses only
  checked PI and PII. Main theorem and three corollaries remain the four explicit
  proof holes; untranscribed external/topological dependencies remain in inventory.

- Supporting proof pass: MainProof.lean. Proved the main theorem with no extra assumptions or proof holes.

- Supporting proof pass: FiniteSup.lean. Proved distance-coordinate isometries and preservation of equi-uniform continuity.

- Supporting proof pass: HilbertL1.lean. Constructed exact Gaussian L1 isometries for finite-dimensional real Hilbert spaces.

Main theorem integration: R01 now proved through MainProof. Three corollary placeholders remain; full inventory and external dependency formalization remain incomplete.

- Supporting proof pass: VaryingMain.lean. Extended main theorem to varying measures; reduced Property(H) corollary to finite sphere noncontractibility.

- Supporting proof pass: SphereFixedPoint.lean. Checked conditional reduction from sphere noncontractibility to the ball fixed-point property; Brouwer is not yet proved.

- Supporting proof pass: PermutationExpanders.lean. Checked permutation graph construction and finite counting criterion; uniform numerical existence estimates remain open.

- Supporting proof pass: CZero.lean. Proved every finite metric space embeds isometrically into c0 by zero-extending distance coordinates.

- Supporting proof pass: QuasiNormalized.lean. Proved full normalized-family estimates for quasi-isometric embeddings, preserving additive errors.

- Supporting proof pass: PermutationCount.lean. Proved exact permutation restriction counts and sampling bounds.

- Supporting proof pass: GraphMetricSpace.lean. Connected graph metric and exact sup-space embeddings for every expander family.

- Supporting proof pass: ExpanderNumerics.lean. Proved the uniform bad-cut numerical sum is less than one for 32 permutations.

- Supporting proof pass: SpernerParity.lean. Proved parity engine for incidence counting; labeled triangulations and Brouwer remain open.

- Supporting proof pass: QuasiMain.lean. Proved quasi main theorem and group corollary assembly conditional explicitly on sphere noncontractibility and Osajda data.

- Supporting proof pass: GraphMetricSpace.lean. Added ContainsExpanders c0 from an arbitrary expander family.

- Supporting proof pass: JohnsonAssembly.lean. Completed Johnson deduction with explicit expander-existence and sphere-topology prerequisites.

- Supporting proof pass: ExpanderExistence.lean. Proved unbounded degree-64 expansion-1/2 family by the full permutation counting construction.

- Supporting proof pass: DiameterGrowth.lean. Proved graph diameters tend to infinity with vertex counts.

- Supporting proof pass: CommonModulus.lean. Proved a common nonnegative monotone modulus tending to zero for bounded equi-uniformly continuous families.

- Supporting proof pass: GroupEmbeddings.lean. Moved group metric convention to a shared module to avoid an import cycle.

Corollary decomposition pass: all three numbered corollaries and the introductory c0 conclusion now have assembled proofs, but remain IN PROGRESS. Exactly two explicit sorry leaves remain: finiteDimensional_ball_fixedPoint (Brouwer) and exists_group_with_isometric_expanders (Osajda). SphereFixedPoint/SphereRetraction and SpernerParity provide partial topology infrastructure; the triangulation and labeling arguments are not proved. Expander existence, all analytic deductions, Gaussian L1 embeddings, quasi-isometric normalization, finite paving, and finite sup/c0 embeddings are proved. No project axiom was added. Inventory completeness is still false; the manuscript-to-Kasparov-Yu definition comparison and final source inventory review are also open.

Statement review: main theorem, estimates and expander construction match the manuscript under real Banach/L1 conventions. Radial uniformity is needed and proved on radius-two balls. The manuscript does not explicitly specify scalars; complex-L1 to real-L1 identification has not been formalized.

- Supporting proof pass: PresentedCayley.lean. Proved countability and connected Cayley graph for any presentation over a finite alphabet.

- Supporting proof pass: ApproximateFixedPoint.lean. Proved compact approximate-fixed-point criterion.

- Supporting proof pass: GirthFoundations.lean. Proved short-path geodesicity/uniqueness and logarithmic-girth diameter bound.

- Supporting proof pass: GraphicalPresentation.lean. Proved walk labels, relators, path independence, and vertex Cayley edges; no isometry claimed.

Brouwer closure pass: ported the MIT-licensed harfe/fixed-point-theorems-lean4 proof at revision 770940ddf9878cf61952ed53d910b92bca841838 from Lean/Mathlib4.32.0 to pinned4.33.1. Five required source modules, full license and adaptation provenance are retained in lean/PropertyH/External/FixedPointTheorems. No dependency or toolchain pin changed. Scratch axiom audits of cubical Sperner, convex homeomorphism, Brouwer, unit-ball bridge and sphere noncontractibility use only standard foundations. R02, R04 and the c0 conclusion are now marked verified, subject to central audit below. Only the Osajda group theorem retains an explicit sorry. Its construction still requires high-girth expanders, a finite graphical small-cancellation labeling, and the no-shortcut isometry argument; foundational graph/presentation lemmas were added without claiming these prerequisites closed.

GraphicalMetric: proved canonical vertex maps into a common relator presentation, their distance upper bound, and the exact no-shortening criterion for isometry. The difficult small-cancellation argument establishing that criterion is still open.

- Supporting proof pass: GroupAssembly.lean. Constructed the countable finitely generated group from explicit finite-alphabet expander labeling/no-shortening data.

- Supporting proof pass: ExpansionRobustness.lean. Proved edge-expansion survives bounded incident-edge deletion, yielding vertex expansion.

- Supporting proof pass: LabelingAvoidance.lean. Proved exact counts and probabilities for finite forbidden label patterns; Lovasz local lemma remains open.

- Supporting proof pass: DefinitionBridge.lean. Proved dense-paving sphere extension and the homeomorphism-witness implication; full degree-one definition correspondence remains open.

Central Brouwer audit passed: R02, R04, c0 and all Brouwer/sphere roots now report only propext, Classical.choice and Quot.sound. Osajda remains the only explicit sorry. Further Osajda work proves presented-group countability/connectivity, exact graphical distance/no-shortening equivalence, finite label-event probabilities and edge-deletion robustness. Its high-girth family, full small-cancellation labeling and no-shortening proof are explicitly tracked as unfinished dependencies; one literal sorry is not a claim that only one small lemma remains. The original Kasparov-Yu generalized degree-one definition correspondence is also not yet formally proved.

- Supporting proof pass: LovaszLocal.lean. Proved the full finite asymmetric Lovasz Local Lemma with explicit independence and event bounds.

- Supporting proof pass: LabelingCompactness.lean. Proved finite satisfiability of finite-support labeling constraints implies a global labeling.

- Supporting proof pass: LabelingLocalLemma.lean. Specialized the full local lemma to random finite-alphabet labelings, proving support-disjoint joint independence and exact word-count bounds.

- Supporting proof pass: ReducedLabeling.lean. Proved literal reduced words preserve lengths of nonbacktracking walks and graph paths.

- Supporting proof pass: PathCounting.lean. Proved bounded-degree walk and simple-path counting estimates needed for labeling dependency bounds.

- Supporting proof pass: CoarseEmbeddings.lean. Added equi-coarse expander embedding definitions, retaining the old biLipschitz definitions and their implication.

- Supporting proof pass: CoarseGrowth.lean. Proved divergence of average norms from coarse compression and bounded-degree ball counting.

- Supporting proof pass: CoarseTruncation.lean. Proved radial truncation Lipschitz and normalized spread estimates for the revised normalization lemma.

- Supporting proof pass: NormalizedMain.lean. Factored the existing homotopy proof through its precise normalized-family input, ready for coarse normalization.

- Supporting proof pass: UniversalFinite.lean. Proved uniform finite metric containment implies failure of Property (H); this premise is not identified with trivial cotype.

- Supporting proof pass: CoarsePaving.lean. Proved coarse embeddings persist in the dense finite-dimensional paving used for Property (H).

- Supporting proof pass: CoarseGroups.lean. Defined coarse universality for finitely generated groups and proved restriction to isometric expander copies, without using or proving Osajda.

- Supporting proof pass: CoarseNormalized.lean. Proved revised Lemma: global zero-mean unit-ball maps, vanishing Lipschitz bounds and mean norms converging to one; preserved compatibility with existing homotopy proof.

- Supporting proof pass: CoarseMain.lean. Proved revised coarse main theorem and coarse Property (H) obstruction using the new normalization and existing homotopy/topology arguments, with standard axioms only.


## Revised manuscript: coarse embeddings (2026-09-16)

Authoritative source SHA256: 3c19b78eac7c4bb501b7249112ae4902025309e07d1ce7090ad34043b850da8f. The TeX file was read,
not edited. A pre-update source snapshot is at /tmp/propertyh-before-coarse-update.tar.gz
(temporary recovery artifact, not a permanent version-control backup).

Added CoarseEmbeddings, CoarseGrowth, CoarseTruncation, CoarseNormalized,
NormalizedMain, CoarsePaving, CoarseMain, CoarseGroups, CoarseGroupCorollary,
UniversalFinite and TrivialCotype. Old Lean modules and pins are preserved.
The revised main theorem and first assertion of Cor.Prop.H are proved via common
compression, truncation normalization, and the existing homotopy argument.
The exact normalization has zero sum and unit-ball bounds for every n, global
Lipschitz bounds tending to zero, and average norms converging to one (stronger
than the stated liminf). C=1+2kL/h is used to make positivity immediate; this
changes only the existential construction, not the statement. Empty prefixes are
handled. Growth uses the proved integer-radius ball bound 1+k^r, avoiding any
implicit k>=2 premise in the informal intermediate estimate.

New explicit proof debt: maureyPisier_finite_sup_representability in
TrivialCotype.lean. Cotype is defined by finite-sign Rademacher second moments,
not by metric universality. The genuine linear finite-representability theorem
is transcribed with one sorry; its metric-containment and Property(H) consequences
remain in_progress. The original publisher PDF download returned HTTP403;
statement crosschecked in Mendel–Naor, Metric Cotype, §1.1. The original MP proof
has not been inspected or ported. Source URL:
https://www.impan.pl/shop/publication/transaction/download/product/101288
Statement reference: https://annals.math.princeton.edu/wp-content/uploads/annals-v168-n1-p07.pdf

Existing explicit proof debt: exists_group_with_isometric_expanders in
OsajdaGroup.lean. The user declined further Osajda construction work; no such
work was resumed. The coarse group deduction conditional on this theorem is
checked, but the unconditional group corollary still inherits sorryAx.
D30 (original Kasparov–Yu definition correspondence) and inventory closure remain
open as before. Real-scalar convention retained. No project axioms introduced.
Validation results follow after the central audit.

Central revision validation: `sh scripts/audit.sh` passed, including the full
library build and every registered declaration's axiom report. The new coarse
normalization, main theorem, Property(H) obstruction, and conditional group
deduction use only propext, Classical.choice and Quot.sound. Exactly two explicit
sorry leaves remain: OsajdaGroup and TrivialCotype (Maurey–Pisier). Their dependent
roots are in_progress and report sorryAx. `sh scripts/audit.sh --terminal` failed
as expected on the recorded open entries and incomplete source inventory.
Snapshot comparison confirmed all pre-existing mathematical module files were
preserved; only root imports, generated audit, README, log and coverage changed,
besides the added modules. Manuscript SHA256 is unchanged.

- Supporting proof pass: ReducedHomology.lean. Defined reduced integral singular homology from Mathlib and proved homotopy invariance and vanishing of null-homotopic induced maps, including degree zero.


## Degree-one definition revision (2026-09-16)

Source SHA256: d6f25cf20ff8add31d74630ca7d9725699476287f12f6431a55f883b18b323f8. Read the revised paragraph before
Cor.Prop.H; the manuscript was not edited. Recovery snapshot of preceding Lean
sources and the current manuscript: /tmp/propertyh-before-degree-update.tar.gz.

HasPropertyH now requires degree-one finite-stage sphere maps. The earlier
homotopic-homeomorphism predicate remains as HasHomeomorphicPropertyH; no
unproved identification between them is used. ReducedHomology constructs integral
singular homology using Mathlib and its reduced part as the kernel of the map to
a point. It proves homotopy invariance and that null-homotopic maps induce zero.
Universe lifts are homeomorphic copies and preserve the existing generic universes.
SphereDegree defines the integer coefficient on chosen top reduced-homology
generators and proves SphereMapDegreeOne.not_nullhomotopic. Because the manuscript
fixes no orientations, independent generators are chosen: this is degree one after
choosing orientations, equivalently absolute degree one relative to fixed choices.
Reduced H0 handles S0; a separate empty-sphere branch permits zero paving stages.
No degree-one/homotopy-equivalence classification theorem is assumed.

Updated VaryingMain, QuasiMain and CoarseMain to contradict degree-one
non-null-homotopy directly. All existing Property(H) corollaries thereby target
the new definition. The main analytic theorem and normalization are unchanged.
DefinitionBridge now proves the dense-paving degree-one implication for target
ℓ2, retaining the old homeomorphism bridge with an explicitly legacy name.
The original arbitrary-Hilbert-target reduction is still not formalized, so D30
remains in_progress; the former degree/homeomorphism comparison is no longer a
prerequisite for the manuscript's revised proof.

Primary source review: Kasparov–Yu Definition1.1,
https://msp.org/gt/2012/16-3/gt-v16-n3-p14-s.pdf;
Hatcher, Algebraic Topology pp134,258 (degree and dependence on orientation),
https://pi.math.cornell.edu/~hatcher/AT/AT..pdf.
No new proof holes or project axioms were introduced. Existing Maurey–Pisier and
Osajda debt is unchanged; no Osajda construction work was resumed.
Central build/audit results follow.

Degree revision central validation: full `lake build` passed (8788 jobs), and
`sh scripts/audit.sh` passed. Every new degree/homology root, the dense-degree
bridge, the revised coarse obstruction and c0 conclusion use only propext,
Classical.choice and Quot.sound. No new sorry terms: the only explicit holes are
still OsajdaGroup.lean:16 and TrivialCotype.lean:36. The terminal audit remains
failing on the existing external dependencies, D30 and inventory closure.
Independent source-to-statement review confirmed the orientation-choice and
empty/S0 conventions and no hidden homotopy-classification hypothesis. General
sphere-homology computation and equivalence with the legacy definition are not
claimed; neither is needed for the revised manuscript-specific obstruction.
Manuscript SHA256 remained d6f25cf20ff8add31d74630ca7d9725699476287f12f6431a55f883b18b323f8.

- Supporting proof pass: HilbertReduction.lean. Proved separable real Hilbert spaces, and closed spans of finite-dimensional pavings, embed linearly isometrically into ell2.

- Supporting proof pass: DegreeTransport.lean. Proved degree-one sphere maps retain degree one under target linear isometry equivalences.

- Supporting proof pass: CZeroCotype.lean. Proved c0 has trivial Rademacher cotype directly from coordinate vectors, without Maurey–Pisier.

- Supporting proof pass: CoarseControl.lean. Proved standard two-function coarse control is equivalent to linear upper control on Cayley graphs.

- Supporting proof pass: HilbertPropertyH.lean. Closed the arbitrary-Hilbert and dense-paving reductions to the manuscript ell2 definition; proved source separability.

- Supporting proof pass: StandardGroupCorollary.lean. Proved the group-universality corollary with standard coarse controls and the explicit Osajda hypothesis.


## Completion scope: modulo Maurey–Pisier and Osajda (2026-09-16)

The author explicitly requested the entire paper modulo these two results.
This supersedes the older unconditional recursive-proof scope. Replaced the two
literal sorry leaves with ordinary proposition definitions and explicit proof
parameters: MaureyPisierFiniteRepresentability X and OsajdaExpanderGroup. Every
conditional consequence is now a kernel-checked theorem with standard axioms.
No project axiom or nonstandard trusted theorem is asserted.

Completed arbitrary-Hilbert-to-ell2 transport, source separability, closed-paving
span separability, Hilbert embedding, degree transport, and the dense-domain
bridge. D30 is closed. Proved c0 trivial cotype directly and arbitrary-near-one
finite metric distortion under the MP hypothesis. Proved equivalence of standard
coarse controls and linear upper controls on Cayley graphs, and the group result
in standard coarse terminology under the Osajda hypothesis.

Completed source review is docs/SOURCE_COVERAGE_REVIEW.md. Inventory completeness
now refers to every numbered result, substantive mathematical proof claim and
required dependency in the agreed real-scalar scope. Contextual literature/history
is explicitly catalogued, not claimed re-proved. Osajda construction substeps
D32-D34 are archived under excluded_external_proof_details, not silently verified
and not counted as extra assumptions. Earlier checked supporting work is retained.

Added the strict modulo completion gate --terminal --modulo-external. It requires
exactly the two named proposition hypotheses, complete coverage, no other open
items, no proof placeholders/project axioms, and standard axiom cones for every
registered declaration. The unconditional --terminal gate still rejects the
external hypotheses. Six scope-gate regression tests passed before integration.
No manuscript or dependency pin was changed. Central validation follows.

Central completion validation: `sh scripts/audit.sh --terminal --modulo-external`
PASSED, including the full library build and every registered declaration's axiom
report. All report only propext, Classical.choice and Quot.sound (or subsets).
There are no Lean proof placeholders or project axioms. All six regression tests
in scripts/test_audit.py passed. The unconditional `--terminal` audit fails on
exactly D12 (OsajdaExpanderGroup) and modulo_MaureyPisierFiniteRepresentability,
confirming that unconditional verification is not being claimed. The source
checksum is unchanged. The requested mathematical-proof scope is complete modulo
exactly the two explicit external hypotheses.


## Manuscript revision: uniform finite sup-space containment (2026-09-16)

The author replaced the trivial-cotype clause of Cor.Prop.H with uniform
containment of finite-dimensional ℓ∞ spaces. Added UniformlyContainsFiniteSup,
the finite-metric bridge, the resulting Property (H) obstruction, and the direct
c₀ containment witness. The formal condition allows nonlinear embeddings and
therefore also covers linear containment. The symmetric common bound uses the
usual normalization by rescaling embeddings into a normed space.

Removed the obsolete MaureyPisierFiniteRepresentability proposition and its five
conditional consequences. Retained Rademacher cotype definitions and the independent
c₀ cotype proof as legacy support, with corrected coverage provenance. Updated the
source fingerprint, current scope documents and inventory. The modulo terminal
gate now permits exactly Osajda, and regression tests explicitly reject adding
Maurey–Pisier back, the former scope, and duplicate Osajda entries. The author's
manuscript was preserved unchanged. Validation results follow after checking.

Validation: full `lake build` passed; all eight audit regression tests passed;
`sh scripts/audit.sh --terminal --modulo-external` passed with only standard
foundational axioms in all registered declarations. The unconditional terminal
gate rejects exactly D12 (Osajda), as intended. The revised corollary and the c₀
containment witness have no external hypothesis. The source SHA256 in coverage
and the source review matches the author's revised manuscript.
