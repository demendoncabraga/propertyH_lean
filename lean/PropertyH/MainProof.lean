import PropertyH.NormalizedFamily
import PropertyH.SmallDeviation
import PropertyH.RadialUniform
import PropertyH.GraphLipschitz
import PropertyH.AffineShifts
import PropertyH.PoincareTransfer

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
/-- Source: `Thm.main`. Normalize the graph embeddings, use uniform continuity
to make radial edge differences small, apply PIII, and normalize the resulting
nonvanishing averaging homotopy. No unproved external assumption is used. -/
theorem sphere_maps_eventually_nullhomotopic_proved
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 μ)
    (hE : EquiGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  obtain ⟨ψ, K, a, ha, hKlim, hKnonneg, hψ⟩ := exists_normalized_expander_embeddings E X hE
  have hlarge : ∀ᶠ n in atTop, 5 ≤ Fintype.card (E.V n) :=
    E.grows.eventually (eventually_ge_atTop 5)
  obtain ⟨n₀, hn₀⟩ := hlarge.exists
  have hk : (0 : ℝ) < E.degreeBound := by
    exact_mod_cast (show 0 < E.degreeBound by have := (E.expands n₀).two_le_degreeBound hn₀; omega)
  let c : ℝ := 2 * E.degreeBound / E.expansion
  have hc : 0 < c := div_pos (mul_pos (by norm_num) hk) (E.expands 0).1
  let ε : ℝ := min (1 / 2) (a / 4)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hη : 0 < ε / c := div_pos hε hc
  obtain ⟨δ, hδ, hmod⟩ := equiUniformContinuous_radialExtension F hF (ε / c) hη
  filter_upwards [hψ, hlarge, hKlim.eventually_lt_const hδ] with n hn hncard hnK
  obtain ⟨hV, hzero, hnorm, hedge, hspread⟩ := hn
  let : Nonempty (E.V n) := hV
  apply nullhomotopic_of_small_average_deviation (F n) (ψ n) hzero a ε hspread
  · exact (min_le_left _ _).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  · exact (min_le_right _ _).trans_lt (by linarith : a / 4 < a / 2)
  · intro t x
    have hp := radial_average_deviation_bound (E.graph n) E.degreeBound E.expansion
      (E.expands n) hncard μ (j n) (F n) (ψ n) hnorm (K n) δ (ε / c) hη.le hnK
      hedge (hmod n) t x
    simpa only [show (2 * (E.degreeBound : ℝ) / E.expansion) = c from rfl,
      mul_div_cancel₀ ε hc.ne'] using hp

end PropertyH

