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

end PropertyH
