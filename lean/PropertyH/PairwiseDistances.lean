import PropertyH.DegreeBound
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

/-- At least half the vertices lie beyond the logarithmic distance threshold. -/
lemma sum_dist_lower_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) {k : ℕ} (hk : 2 ≤ k)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k) (hV : 5 ≤ Fintype.card V) (u : V) :
    (Fintype.card V : ℝ) / 2 * Real.logb k ((Fintype.card V : ℝ) / 2 - 1) ≤
      ∑ w, (G.dist u w : ℝ) := by
  classical
  let N : ℝ := Fintype.card V
  let t : ℝ := Real.logb k (N / 2 - 1)
  have hN : 5 ≤ N := by dsimp [N]; exact_mod_cast hV
  have hkR : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have ht : 0 ≤ t := Real.logb_nonneg hkR (by dsimp [N] at *; linarith)
  have hpow : ((k ^ ⌊t⌋₊ : ℕ) : ℝ) ≤ N / 2 - 1 := by
    simpa only [Nat.cast_pow, Real.rpow_natCast] using
      (Real.le_logb_iff_rpow_le hkR (by linarith : 0 < N / 2 - 1)).mp (Nat.floor_le ht)
  let A : Finset V := Finset.univ.filter (fun w => G.dist u w ≤ ⌊t⌋₊)
  have hAc : A.card ≤ 1 + k ^ ⌊t⌋₊ := by
    simpa [A, Set.ncard_eq_toFinset_card'] using card_dist_le_bound hc hdeg u ⌊t⌋₊
  have hAcR : (A.card : ℝ) ≤ N / 2 := by
    have : (A.card : ℝ) ≤ 1 + ((k ^ ⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hAc
    linarith
  have hBcR : N / 2 ≤ (Aᶜ.card : ℝ) := by
    have : (A.card : ℝ) + (Aᶜ.card : ℝ) = N := by
      dsimp [N]
      exact_mod_cast Finset.card_add_card_compl A
    linarith
  have hfar : ∀ w ∈ Aᶜ, t ≤ (G.dist u w : ℝ) := by
    intro w hw
    have hw' : ⌊t⌋₊ < G.dist u w := by simpa [A] using hw
    exact (Nat.lt_of_floor_lt hw').le
  calc
    N / 2 * t ≤ (Aᶜ.card : ℝ) * t := mul_le_mul_of_nonneg_right hBcR ht
    _ = ∑ _w ∈ Aᶜ, t := by simp
    _ ≤ ∑ w ∈ Aᶜ, (G.dist u w : ℝ) := Finset.sum_le_sum hfar
    _ ≤ ∑ w, (G.dist u w : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

/-- Source: PII. Sum the logarithmic distance lower bound over all centers. -/
theorem expander_pairwise_distance_bound_proved {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h) (hV : 5 ≤ Fintype.card V) :
    (Fintype.card V : ℝ)^2 / 2 * Real.logb k ((Fintype.card V : ℝ) / 2 - 1) ≤
      ∑ v, ∑ u, ((G.dist v u : ℕ) : ℝ) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => sum_dist_lower_bound hG.connected (hG.two_le_degreeBound hV) hG.2.1 hV v)
  simpa [Finset.sum_const, nsmul_eq_mul, pow_two, mul_div_assoc, mul_assoc] using hsum

end PropertyH
