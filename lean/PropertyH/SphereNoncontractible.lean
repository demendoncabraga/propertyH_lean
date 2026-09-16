import PropertyH.External.FixedPointTheorems.brouwer
import PropertyH.SphereFixedPoint

namespace PropertyH

/-- Finite-dimensional closed real unit balls have the Brouwer fixed-point property. -/
theorem unitBall_fixedPoint {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (f : C(UnitBall X, UnitBall X)) : ∃ x, f x = x := by
  exact brouwer_fixed_point (Metric.closedBall (0 : X) 1) (convex_closedBall _ _)
    (isCompact_closedBall _ _) ⟨0, Metric.mem_closedBall_self zero_le_one⟩ f

/-- A finite-dimensional real unit sphere is not contractible, including the empty sphere. -/
theorem finiteDimensional_unitSphere_not_contractible {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    ¬ ContractibleSpace (UnitSphere X) :=
  sphere_not_contractible_of_fixedPoint_property unitBall_fixedPoint

end PropertyH

