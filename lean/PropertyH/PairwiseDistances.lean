import Mathlib
import Mathlib.Data.Set.Card.Arithmetic

namespace PropertyH

/-- A vertex within `n + 1` steps is the center or within `n` steps of a neighbor. -/
lemma dist_succ_cover {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (u w : V) (n : ℕ) (hw : G.dist u w ≤ n + 1) :
    w = u ∨ ∃ v, G.Adj u v ∧ G.dist v w ≤ n := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u w
  cases p with
  | nil => exact Or.inl rfl
  | cons huv p =>
    refine Or.inr ⟨_, huv, ?_⟩
    have hpdist := G.dist_le p
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

/-- Bounded degree bounds the cardinality of every closed graph ball. -/
lemma card_dist_le_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) {k : ℕ} (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (u : V) (n : ℕ) :
    ({w | G.dist u w ≤ n} : Set V).ncard ≤ 1 + k ^ n := by
  classical
  induction n generalizing u with
  | zero =>
    simp [hc.dist_eq_zero_iff]
  | succ n ih =>
    let B : V → Set V := fun v => {w | G.dist v w ≤ n}
    have hsmall : ∀ v : G.neighborSet u, (B v \ {u}).ncard ≤ k ^ n := by
      intro v
      cases n with
      | zero =>
        simpa [B, hc.dist_eq_zero_iff] using
          (Set.ncard_sdiff_singleton_le ({(v : V)} : Set V) u)
      | succ m =>
        have hu : u ∈ B v := by
          simp only [B, Set.mem_ofPred_eq, SimpleGraph.dist_eq_one_iff_adj.mpr v.property.symm]
          omega
        have hcard := Set.ncard_sdiff_singleton_add_one hu
        have hv := ih v
        change (B v).ncard ≤ 1 + k ^ (m + 1) at hv
        omega
    have hcover : {w | G.dist u w ≤ n + 1} ⊆
        insert u (⋃ v : G.neighborSet u, B v \ {u}) := by
      intro w hw
      rcases dist_succ_cover hc u w n hw with rfl | ⟨v, huv, hv⟩
      · exact Set.mem_insert _ _
      · by_cases hwu : w = u
        · exact Or.inl hwu
        · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v, huv⟩, hv, hwu⟩)
    calc
      _ ≤ (insert u (⋃ v : G.neighborSet u, B v \ {u})).ncard := Set.ncard_le_ncard hcover
      _ ≤ (⋃ v : G.neighborSet u, B v \ {u}).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (∑ v : G.neighborSet u, (B v \ {u}).ncard) + 1 :=
        Nat.add_le_add_right (Set.ncard_iUnion_le_of_fintype _) _
      _ ≤ (∑ _v : G.neighborSet u, k ^ n) + 1 :=
        Nat.add_le_add_right (Finset.sum_le_sum fun v _ => hsmall v) _
      _ ≤ 1 + k ^ (n + 1) := by
        simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Set.fintypeCard_eq_ncard,
          pow_succ, Nat.mul_comm, Nat.add_comm] using
          Nat.add_le_add_right (Nat.mul_le_mul_right (k ^ n) (hdeg u)) 1

end PropertyH
