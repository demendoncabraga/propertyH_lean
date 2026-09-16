import PropertyH.Basic

namespace PropertyH
open scoped unitInterval
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Source: `$x+s\psi(v)\in2B_X$` in the averaging construction. -/
theorem shifted_mem_closedBall_two (x : UnitBall X) (y : X) (hy : ‖y‖ ≤ 1) (t : I) :
    (x : X) + (t : ℝ) • y ∈ Metric.closedBall (0 : X) 2 := by
  rw [mem_closedBall_zero_iff]
  have hx := mem_closedBall_zero_iff.mp x.property
  have hsmul : ‖(t : ℝ) • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg t.property.1]
    exact mul_le_one₀ t.property.2 (norm_nonneg _) hy
  linarith [norm_add_le (x : X) ((t : ℝ) • y)]

/-- Source: the shifts used in averaging do not enlarge an edge difference. -/
theorem dist_affine_shift_le (x a b : X) (t : I) :
    dist (x + (t : ℝ) • a) (x + (t : ℝ) • b) ≤ dist a b := by
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg t.property.1]
  exact mul_le_of_le_one_left (norm_nonneg _) t.property.2

end PropertyH
