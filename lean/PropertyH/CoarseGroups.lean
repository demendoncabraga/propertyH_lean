import PropertyH.CoarseEmbeddings

namespace PropertyH
open Filter

/-- Source: `Cor.no.PropH.cL.universal`, revised coarse-copy hypothesis.
On a Cayley graph the upper coarse control can be taken linear by summing over edges.
The controls may depend on the group and generating set. -/
def CoarselyContainsAllFinitelyGeneratedGroups (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ),
    (SimpleGraph.mulCayley (S : Set Γ)).Connected →
    ∃ (f : Γ → X) (L : ℝ) (ρ : ℝ → ℝ), 0 < L ∧ Monotone ρ ∧
      (∀ t, 0 ≤ t → 0 ≤ ρ t) ∧ Tendsto ρ atTop atTop ∧
      ∀ g h, ρ ((SimpleGraph.mulCayley (S : Set Γ)).dist g h) ≤ ‖f g - f h‖ ∧
        ‖f g - f h‖ ≤ L * (SimpleGraph.mulCayley (S : Set Γ)).dist g h

/-- Restrict the coarse group embedding to the isometric expander copies. -/
theorem coarse_expander_maps_of_universal_groups (X : Type*) [NormedAddCommGroup X]
    (hX : CoarselyContainsAllFinitelyGeneratedGroups X)
    (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ)
    (hc : (SimpleGraph.mulCayley (S : Set Γ)).Connected)
    (E : ExpanderFamily) (ι : ∀ n, E.V n → Γ)
    (hι : ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) =
      (E.graph n).dist v u) : EquiCoarseGraphEmbeddings E (fun _ => X) := by
  obtain ⟨f, L, ρ, hL, hmono, hnonneg, hproper, hf⟩ := hX Γ S hc
  refine ⟨L, ρ, hL, hmono, hnonneg, hproper, fun n v => f (ι n v), ?_⟩
  intro n v u
  simpa only [hι] using hf (ι n v) (ι n u)
end PropertyH
