import PropertyH.CoarseGroups
import PropertyH.GraphLipschitz

namespace PropertyH
open Filter

/-- On a connected graph, an arbitrary upper coarse control becomes a linear
control by applying its value at one to successive edges of a shortest path. -/
theorem norm_sub_le_linear_graph_control {V X : Type*} [NormedAddCommGroup X]
    {G : SimpleGraph V} (hc : G.Connected) (f : V → X) (ω : ℝ → ℝ)
    (hf : ∀ u v, ‖f u - f v‖ ≤ ω (G.dist u v)) (u v : V) :
    ‖f u - f v‖ ≤ max 1 (ω 1) * G.dist u v := by
  rw [← dist_eq_norm]
  apply dist_le_mul_graph_dist hc f _ _ u v
  intro a b hab
  rw [dist_eq_norm]
  have h := hf a b
  rw [G.dist_eq_one_iff_adj.mpr hab, Nat.cast_one] at h
  exact h.trans (le_max_right _ _)

/-- The usual two-control-function formulation of containing coarse copies of
all finitely generated groups. Controls may depend on the group and generating set. -/
def StandardCoarselyContainsAllFinitelyGeneratedGroups (X : Type*)
    [NormedAddCommGroup X] : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ),
    (SimpleGraph.mulCayley (S : Set Γ)).Connected →
    ∃ (f : Γ → X) (ρ ω : ℝ → ℝ), Monotone ρ ∧
      (∀ t, 0 ≤ t → 0 ≤ ρ t) ∧ Tendsto ρ atTop atTop ∧
      Monotone ω ∧ (∀ t, 0 ≤ t → 0 ≤ ω t) ∧
      ∀ g h, ρ ((SimpleGraph.mulCayley (S : Set Γ)).dist g h) ≤ ‖f g - f h‖ ∧
        ‖f g - f h‖ ≤ ω ((SimpleGraph.mulCayley (S : Set Γ)).dist g h)

theorem StandardCoarselyContainsAllFinitelyGeneratedGroups.to_linear_control
    {X : Type*} [NormedAddCommGroup X]
    (hX : StandardCoarselyContainsAllFinitelyGeneratedGroups X) :
    CoarselyContainsAllFinitelyGeneratedGroups X := by
  intro Γ _ _ S hc
  obtain ⟨f, ρ, ω, hρ, hρ0, hρproper, _, _, hf⟩ := hX Γ S hc
  refine ⟨f, max 1 (ω 1), ρ, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    hρ, hρ0, hρproper, ?_⟩
  intro g h
  exact ⟨(hf g h).1, norm_sub_le_linear_graph_control hc f ω (fun a b => (hf a b).2) g h⟩

end PropertyH
