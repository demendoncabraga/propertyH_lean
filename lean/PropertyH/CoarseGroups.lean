import PropertyH.CoarseEmbeddings
import PropertyH.CoarseControl

namespace PropertyH
open Filter

/-- Coarse embedding of a specified finitely generated group with its word metric.
Both controls are nondecreasing; the lower control tends to infinity. -/
def CoarselyEmbedsCayley (Γ : Type*) [Group Γ] (S : Finset Γ)
    (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ (f : Γ → X) (ρ ω : ℝ → ℝ), Monotone ρ ∧
    (∀ t, 0 ≤ t → 0 ≤ ρ t) ∧ Tendsto ρ atTop atTop ∧
    Monotone ω ∧ (∀ t, 0 ≤ t → 0 ≤ ω t) ∧
    ∀ g h, ρ ((SimpleGraph.mulCayley (S : Set Γ)).dist g h) ≤ ‖f g - f h‖ ∧
      ‖f g - f h‖ ≤ ω ((SimpleGraph.mulCayley (S : Set Γ)).dist g h)

/-- Restrict one coarse group embedding to its isometric expander copies. -/
theorem coarse_expander_maps_of_cayley_embedding (X : Type*) [NormedAddCommGroup X]
    (Γ : Type*) [Group Γ] (S : Finset Γ)
    (hc : (SimpleGraph.mulCayley (S : Set Γ)).Connected)
    (hX : CoarselyEmbedsCayley Γ S X)
    (E : ExpanderFamily) (ι : ∀ n, E.V n → Γ)
    (hι : ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) =
      (E.graph n).dist v u) : EquiCoarseGraphEmbeddings E (fun _ => X) := by
  obtain ⟨f, ρ, ω, hmono, hnonneg, hproper, _, _, hf⟩ := hX
  refine ⟨max 1 (ω 1), ρ, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    hmono, hnonneg, hproper, fun n v => f (ι n v), ?_⟩
  intro n v u
  simpa only [hι] using
    And.intro (hf (ι n v) (ι n u)).1
      (norm_sub_le_linear_graph_control hc f ω (fun a b => (hf a b).2) (ι n v) (ι n u))
end PropertyH
