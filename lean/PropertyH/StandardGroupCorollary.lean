import PropertyH.CoarseControl
import PropertyH.CoarseGroupCorollary

namespace PropertyH
/-- Source: Cor.no.PropH.cL.universal in the usual two-control-function convention.
Excluding all finitely generated groups already excludes all countable groups. -/
theorem not_standard_coarsely_universal_groups_of_hasPropertyH (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hOsajda : OsajdaExpanderGroup) (hX : HasPropertyH X) :
    ¬ StandardCoarselyContainsAllFinitelyGeneratedGroups X := by
  intro h
  exact not_coarsely_universal_groups_of_hasPropertyH X hOsajda hX h.to_linear_control
end PropertyH
