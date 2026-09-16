import PropertyH.CoarseGroups
import PropertyH.CoarseMain
import PropertyH.OsajdaGroup

namespace PropertyH
/-- The revised group corollary with its expander-group prerequisite explicit. -/
theorem not_coarsely_universal_groups_of_hasPropertyH_of_expander_group
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : HasPropertyH X)
    (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ)
    (hc : (SimpleGraph.mulCayley (S : Set Γ)).Connected)
    (E : ExpanderFamily) (ι : ∀ n, E.V n → Γ)
    (hι : ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) =
      (E.graph n).dist v u) : ¬ CoarselyContainsAllFinitelyGeneratedGroups X := by
  intro huniv
  exact not_hasPropertyH_of_containsCoarseExpanders X
    ⟨E, coarse_expander_maps_of_universal_groups X huniv Γ S hc E ι hι⟩ hX

/-- Source: revised `Cor.no.PropH.cL.universal`. Conditional on the explicitly supplied Osajda group-construction hypothesis. -/
theorem not_coarsely_universal_groups_of_hasPropertyH (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hOsajda : OsajdaExpanderGroup) (hX : HasPropertyH X) : ¬ CoarselyContainsAllFinitelyGeneratedGroups X := by
  obtain ⟨Γ, g, hcount, S, hc, E, ι, hι⟩ := exists_group_with_isometric_expanders hOsajda
  let : Group Γ := g
  let : Countable Γ := hcount
  exact not_coarsely_universal_groups_of_hasPropertyH_of_expander_group X hX Γ S hc E ι hι
end PropertyH
