import PropertyH.AffineShifts
import PropertyH.AveragingFamily
import PropertyH.Connectivity
import PropertyH.GraphLipschitz
import PropertyH.PoincareTransfer
import PropertyH.RadialExtension

noncomputable section
namespace PropertyH
open Filter MeasureTheory
open scoped unitInterval Topology

/-- Source: PIII applied to the shifted radial extensions, `eq:deviation`. -/
theorem radial_average_deviation_bound
    {V X Y : Type*} [Fintype V] [Nonempty V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (G : SimpleGraph V) (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h)
    (hV : 5 ≤ Fintype.card V) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (j : Y →ₗᵢ[ℝ] Lp ℝ 1 μ) (F : C(UnitSphere X, UnitSphere Y))
    (ψ : V → X) (hψ : ∀ v, ‖ψ v‖ ≤ 1) (K δ η : ℝ) (hη : 0 ≤ η) (hKδ : K < δ)
    (hedge : ∀ v u, G.Adj v u → ‖ψ v - ψ u‖ ≤ K)
    (hmod : ∀ z w : Metric.closedBall (0 : X) 2, dist z w < δ →
      dist (radialExtension F z) (radialExtension F w) < η)
    (t : I) (x : UnitBall X) :
    average (fun v => ‖radialExtension F ((x : X) + (t : ℝ) • ψ v) -
      averagingFamily ψ (radialExtensionMap F) (t, x)‖) ≤ (2 * k / h) * η := by
  let f : V → Y := fun v => radialExtension F ((x : X) + (t : ℝ) • ψ v)
  have he : ∀ v u, G.Adj v u → dist (f v) (f u) ≤ η := by
    intro v u hvu
    apply le_of_lt
    apply hmod ⟨_, shifted_mem_closedBall_two x (ψ v) (hψ v) t⟩
      ⟨_, shifted_mem_closedBall_two x (ψ u) (hψ u) t⟩
    have hs := dist_affine_shift_le (x : X) (ψ v) (ψ u) t
    simpa only [Subtype.dist_eq] using hs.trans_lt
      (by simpa only [dist_eq_norm] using (hedge v u hvu).trans_lt hKδ)
  have hp := expander_poincare_embedded G k h hG hV μ j f η hη
    (fun v u => by simpa only [dist_eq_norm] using dist_le_mul_graph_dist hG.connected f η he v u)
  simpa only [f, averagingFamily, radialExtensionMap, ContinuousMap.coe_mk] using hp

end PropertyH

