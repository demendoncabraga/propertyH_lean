import PropertyH.CoarseGroups
import PropertyH.CoarseMain
import PropertyH.OsajdaGroup

namespace PropertyH
universe u

/-- Source: `Cor.Group`. A finite generating set is witnessed by connectedness
of its Cayley graph. The group is chosen before all target Banach spaces.
Osajda is the only external mathematical hypothesis. -/
theorem exists_group_not_coarsely_embeddable_in_propertyH
    (hOsajda : OsajdaExpanderGroup) :
    ∃ (Γ : Type) (g : Group Γ) (_ : Countable Γ),
      letI := g
      ∃ S : Finset Γ, (SimpleGraph.mulCayley (S : Set Γ)).Connected ∧
        ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
          HasPropertyH X → ¬ CoarselyEmbedsCayley Γ S X := by
  obtain ⟨Γ, g, hcount, S, hc, E, ι, hι⟩ := exists_group_with_isometric_expanders hOsajda
  let : Group Γ := g
  let : Countable Γ := hcount
  exact ⟨Γ, g, hcount, S, hc, fun X _ _ _ hX hemb =>
    not_hasPropertyH_of_containsCoarseExpanders X
      ⟨E, coarse_expander_maps_of_cayley_embedding X Γ S hc hemb E ι hι⟩ hX⟩
end PropertyH
