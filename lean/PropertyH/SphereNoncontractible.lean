import PropertyH.Basic
import PropertyH.External.FixedPointTheorems.brouwer

namespace PropertyH

/-- Finite-dimensional closed real unit balls have the Brouwer fixed-point property. -/
theorem unitBall_fixedPoint {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (f : C(UnitBall X, UnitBall X)) : ∃ x, f x = x := by
  exact brouwer_fixed_point (Metric.closedBall (0 : X) 1) (convex_closedBall _ _)
    (isCompact_closedBall _ _) ⟨0, Metric.mem_closedBall_self zero_le_one⟩ f

end PropertyH

