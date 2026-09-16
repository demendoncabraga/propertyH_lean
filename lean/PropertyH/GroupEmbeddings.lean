import PropertyH.Expanders
namespace PropertyH
/-- Source: the quasi-isometric copies in `Cor.no.PropH.cL.universal`.
This tests only finitely generated countable groups with their Cayley graph metrics.
Ruling out this smaller test class suffices to rule out all countable groups. -/
def ContainsAllFinitelyGeneratedGroups (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ),
    (SimpleGraph.mulCayley (S : Set Γ)).Connected →
    ∃ (f : Γ → X) (L A : ℝ), 1 ≤ L ∧ 0 ≤ A ∧
      ∀ g h, (SimpleGraph.mulCayley (S : Set Γ)).dist g h / L - A ≤ ‖f g - f h‖ ∧
        ‖f g - f h‖ ≤ L * (SimpleGraph.mulCayley (S : Set Γ)).dist g h + A

end PropertyH
