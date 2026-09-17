import PropertyH.CoarseNormalized
import PropertyH.CoarsePaving
import PropertyH.HilbertL1
import PropertyH.NormalizedMain
import PropertyH.SphereRestrictions

noncomputable section
namespace PropertyH
open Filter MeasureTheory
open scoped Topology

/-- Proof support for `Thm.main`: construct null-homotopies with varying L¹ measures. -/
theorem sphere_maps_eventually_nullhomotopic_coarse_varying
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, FiniteDimensional ℝ (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, FiniteDimensional ℝ (Y n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 (μ n))
    (hE : EquiCoarseGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  exact sphere_maps_eventually_nullhomotopic_of_normalized E X Y μ j
    (exists_normalized_coarse_expander_embeddings E X hE) F hF

/-- Source: `Thm.main`, for finite-dimensional real normed spaces, with degree zero
in the reduced-homology sense. Completeness follows from finite dimension. -/
theorem sphere_maps_eventually_degreeZero_coarse
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, FiniteDimensional ℝ (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, FiniteDimensional ℝ (Y n)]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 μ)
    (hE : EquiCoarseGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, HasDegreeZero (F n) := by
  exact (sphere_maps_eventually_nullhomotopic_coarse_varying E X Y (fun _ => μ) j hE F hF).mono
    (fun n hn => hasDegreeZero_of_nullhomotopic (F n) hn)

/-- Source: `Cor.Prop.H`, including rational Property (H). -/
theorem not_hasRationalPropertyH_of_containsCoarseExpanders
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : ContainsCoarseExpanders X) : ¬ HasRationalPropertyH X := by
  classical
  rintro ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hdense, hrest⟩
  obtain ⟨E, hE⟩ := hX
  obtain ⟨m, hm⟩ := exists_paving_coarse_graph_embeddings E hE A hA hdense
  choose f hf hdegree using hrest
  let : ∀ n, FiniteDimensional ℝ (A n) := hAfin
  let : ∀ n, FiniteDimensional ℝ (B n) := hBfin
  let : ∀ n, MeasurableSpace (B (m n)) := fun n => borel (B (m n))
  let : ∀ n, BorelSpace (B (m n)) := fun n => ⟨rfl⟩
  let μ := fun n => ProbabilityTheory.stdGaussian (B (m n))
  let j := fun n => hilbertGaussianL1Isometry (E := B (m n))
  have hmod := equiUniformContinuous_submodule_restrictions F hF
    (fun n => A (m n)) (fun n => B (m n)) (fun n => f (m n)) (fun n => hf (m n))
  have hnull := sphere_maps_eventually_nullhomotopic_coarse_varying E
    (fun n => A (m n)) (fun n => B (m n)) μ j hm (fun n => f (m n)) hmod
  obtain ⟨n, y, hy⟩ := hnull.exists
  exact (hdegree (m n)).not_nullhomotopic ⟨y, hy⟩

/-- Source: `Cor.Prop.H`, ordinary Property (H) follows from the rational obstruction. -/
theorem not_hasPropertyH_of_containsCoarseExpanders
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : ContainsCoarseExpanders X) : ¬ HasPropertyH X := by
  exact fun h => not_hasRationalPropertyH_of_containsCoarseExpanders X hX h.to_rational

end PropertyH
