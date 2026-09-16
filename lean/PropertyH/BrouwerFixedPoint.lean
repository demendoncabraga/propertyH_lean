import PropertyH.SphereFixedPoint
import PropertyH.SphereNoncontractible
namespace PropertyH

/-- Source: finite-dimensional sphere noncontractibility used in the corollaries.
Proved by the ported cubical Sperner argument; see the retained upstream license
and provenance in External/FixedPointTheorems. -/
theorem finiteDimensional_ball_fixedPoint {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (f : C(UnitBall X, UnitBall X)) : ∃ x, f x = x := by
  exact unitBall_fixedPoint f

/-- Source: a finite-dimensional sphere is not contractible, including the empty sphere. -/
theorem finiteDimensional_sphere_not_contractible {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    ¬ ContractibleSpace (UnitSphere X) :=
  sphere_not_contractible_of_fixedPoint_property finiteDimensional_ball_fixedPoint
end PropertyH
