import PropertyH.Expanders
namespace PropertyH

/-- External Osajda group-construction statement, explicitly assumed under the
user's modulo-two-results scope. Its construction is not part of this verification. -/
def OsajdaExpanderGroup : Prop :=
    ∃ (Γ : Type) (g : Group Γ) (_ : Countable Γ),
      letI := g
      ∃ S : Finset Γ, (SimpleGraph.mulCayley (S : Set Γ)).Connected ∧
        ∃ (E : ExpanderFamily) (ι : ∀ n, E.V n → Γ),
          ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) =
            (E.graph n).dist v u

/-- Unpack the explicitly supplied Osajda hypothesis. -/
theorem exists_group_with_isometric_expanders (hOsajda : OsajdaExpanderGroup) :
    ∃ (Γ : Type) (g : Group Γ) (_ : Countable Γ),
      letI := g
      ∃ S : Finset Γ, (SimpleGraph.mulCayley (S : Set Γ)).Connected ∧
        ∃ (E : ExpanderFamily) (ι : ∀ n, E.V n → Γ),
          ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) =
            (E.graph n).dist v u := hOsajda
end PropertyH
