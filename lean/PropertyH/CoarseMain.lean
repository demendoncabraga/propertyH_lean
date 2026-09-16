import PropertyH.CoarseNormalized
import PropertyH.NormalizedMain
import PropertyH.CoarsePaving
import PropertyH.VaryingMain
import PropertyH.BrouwerFixedPoint

noncomputable section
namespace PropertyH
open Filter MeasureTheory
open scoped Topology

/-- Source: revised `Thm.main`, allowing a different L¹ target measure for each n. -/
theorem sphere_maps_eventually_nullhomotopic_coarse_varying
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 (μ n))
    (hE : EquiCoarseGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  exact sphere_maps_eventually_nullhomotopic_of_normalized E X Y μ j
    (exists_normalized_coarse_expander_embeddings E X hE) F hF

theorem sphere_maps_eventually_nullhomotopic_coarse
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 μ)
    (hE : EquiCoarseGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  exact sphere_maps_eventually_nullhomotopic_coarse_varying E X Y (fun _ => μ) j hE F hF

/-- Source: `Cor.Prop.H` with degree-one restrictions. -/
theorem not_hasPropertyH_of_containsCoarseExpanders
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : ContainsCoarseExpanders X) : ¬ HasPropertyH X := by
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

/-- Compatibility wrapper retaining the old helper signature.
Degree-one non-null-homotopy makes the extra sphere-topology premise unnecessary. -/
theorem not_hasPropertyH_of_containsCoarseExpanders_of_sphere_noncontractible
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (_hsphere : ∀ S : Submodule ℝ X, FiniteDimensional ℝ S → ¬ ContractibleSpace (UnitSphere S))
    (hX : ContainsCoarseExpanders X) : ¬ HasPropertyH X :=
  not_hasPropertyH_of_containsCoarseExpanders X hX

end PropertyH
