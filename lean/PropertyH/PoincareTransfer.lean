import PropertyH.ExpanderEstimates
import PropertyH.Averages

/-! Transport PIII through the target space's linear isometric embedding into L1. -/
noncomputable section
namespace PropertyH
open MeasureTheory

/-- Source: `$Y_n\subseteq L_1$` and the application of PIII to the averaging family. -/
theorem expander_poincare_embedded {V Y : Type*} [Fintype V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (G : SimpleGraph V) (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h)
    (hV : 5 ≤ Fintype.card V) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (j : Y →ₗᵢ[ℝ] Lp ℝ 1 μ) (f : V → Y) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ v u, ‖f v - f u‖ ≤ L * G.dist v u) :
    average (fun v => ‖f v - average f‖) ≤ (2 * k / h) * L := by
  have hf' : ∀ v u, ‖j (f v) - j (f u)‖ ≤ L * G.dist v u := by
    intro v u
    simpa only [← map_sub, LinearIsometry.norm_map] using hf v u
  have hp := expander_poincare G k h hG hV μ (fun v => j (f v)) L hL hf'
  simpa only [average, smul_eq_mul, ← map_sum, ← map_smul, ← map_sub,
    LinearIsometry.norm_map] using hp

end PropertyH
