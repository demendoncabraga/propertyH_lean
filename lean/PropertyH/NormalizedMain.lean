import PropertyH.DegreeBound
import PropertyH.MainProof
import PropertyH.RadialUniform
import PropertyH.SmallDeviation
noncomputable section
namespace PropertyH
open Filter MeasureTheory
open scoped unitInterval Topology
/-- Source: `Thm.main`. Normalize the graph embeddings, use uniform continuity
to make radial edge differences small, apply PIII, and normalize the resulting
nonvanishing averaging homotopy. No unproved external assumption is used. -/
theorem sphere_maps_eventually_nullhomotopic_of_normalized
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 (μ n))
    (hnormalized : ∃ (ψ : ∀ n, E.V n → X n) (K : ℕ → ℝ) (a : ℝ), 0 < a ∧
      Tendsto K atTop (𝓝 0) ∧ (∀ n, 0 ≤ K n) ∧ ∀ᶠ n in atTop,
        Nonempty (E.V n) ∧ (∑ v, ψ n v = 0) ∧ (∀ v, ‖ψ n v‖ ≤ 1) ∧
        (∀ v u, (E.graph n).Adj v u → ‖ψ n v - ψ n u‖ ≤ K n) ∧
        a ≤ average (fun v => ‖ψ n v‖))
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  obtain ⟨ψ, K, a, ha, hKlim, hKnonneg, hψ⟩ := hnormalized
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
  filter_upwards [hψ, hKlim.eventually_lt_const hδ] with n hn hnK
  obtain ⟨hV, hzero, hnorm, hedge, hspread⟩ := hn
  let : Nonempty (E.V n) := hV
  apply nullhomotopic_of_small_average_deviation (F n) (ψ n) hzero a ε hspread
  · exact (min_le_left _ _).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  · exact (min_le_right _ _).trans_lt (by linarith : a / 4 < a / 2)
  · intro t x
    have hp := radial_average_deviation_bound (E.graph n) E.degreeBound E.expansion
      (E.expands n) (μ n) (j n) (F n) (ψ n) hnorm (K n) δ (ε / c) hη.le hnK
      hedge (hmod n) t x
    simpa only [show (2 * (E.degreeBound : ℝ) / E.expansion) = c from rfl,
      mul_div_cancel₀ ε hc.ne'] using hp

end PropertyH
