import PropertyH.Basic

namespace PropertyH
variable {V Y : Type*} {G : SimpleGraph V} [PseudoMetricSpace Y]

/-- Source: applying PIII after controlling differences across edges.
An edgewise bound accumulates along a walk. -/
theorem dist_le_mul_walk_length (f : V → Y) (L : ℝ)
    (hf : ∀ u v, G.Adj u v → dist (f u) (f v) ≤ L)
    {u v : V} (p : G.Walk u v) : dist (f u) (f v) ≤ L * p.length := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have ht := (dist_triangle (f u) (f v) (f w)).trans (add_le_add (hf u v huv) ih)
    simpa [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one, mul_add, add_comm] using ht

/-- Source: the edgewise modulus bound implies the global Lipschitz bound for PIII. -/
theorem dist_le_mul_graph_dist (hc : G.Connected) (f : V → Y) (L : ℝ)
    (hf : ∀ u v, G.Adj u v → dist (f u) (f v) ≤ L) (u v : V) :
    dist (f u) (f v) ≤ L * G.dist u v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  simpa only [hp] using dist_le_mul_walk_length f L hf p

end PropertyH
