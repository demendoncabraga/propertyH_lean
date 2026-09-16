import PropertyH.FiniteSup
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section
namespace PropertyH
open Filter Topology
open scoped ZeroAtInfty

/-- The real Banach space of sequences converging to zero, with the supremum norm. -/
abbrev CZero := C₀(ℕ, ℝ)

def finiteToCZero (n : ℕ) (f : Fin n → ℝ) : CZero where
  toFun k := if h : k < n then f ⟨k,h⟩ else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    have he : (fun k : ℕ => if h : k < n then f ⟨k,h⟩ else 0) =ᶠ[cocompact ℕ] 0 := by
      simp only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop n] with k hk
      simp [not_lt.mpr hk]
    exact tendsto_const_nhds.congr' he.symm
theorem finiteToCZero_isometry (n : ℕ) : Isometry (finiteToCZero n) := by
  apply Isometry.of_dist_eq
  intro f g
  apply le_antisymm
  · apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro k
    by_cases hk : k < n
    · simpa [finiteToCZero, ZeroAtInftyContinuousMap.toBCF, hk] using dist_le_pi_dist f g (⟨k,hk⟩ : Fin n)
    · simp [finiteToCZero, ZeroAtInftyContinuousMap.toBCF, hk]
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    simpa only [ZeroAtInftyContinuousMap.dist_toBCF_eq_dist, show (finiteToCZero n f).toBCF i.val = f i from dif_pos i.isLt, show (finiteToCZero n g).toBCF i.val = g i from dif_pos i.isLt] using
      (BoundedContinuousFunction.dist_coe_le_dist
        (f := (finiteToCZero n f).toBCF) (g := (finiteToCZero n g).toBCF) i.val)
/-- The finite metric embeddings needed for the paper's c₀ consequence. -/
theorem finite_metric_embeds_cZero {V : Type*} [Fintype V] [PseudoMetricSpace V] :
    ∃ f : V → CZero, Isometry f := by
  exact ⟨_, (finiteToCZero_isometry (Fintype.card V)).comp finiteDistanceCoordinates_isometry⟩
end PropertyH
