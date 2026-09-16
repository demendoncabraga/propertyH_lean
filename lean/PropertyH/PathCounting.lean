import PropertyH.Basic

noncomputable section
open Classical
namespace PropertyH

/-- At most `k^r` walks of length `r` start at a given vertex of a graph of maximum degree `k`. -/
theorem card_walks_from_le_pow {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k) (r : ℕ) (u : V) :
    (∑ v, Fintype.card {p : G.Walk u v // p.length = r}) ≤ k ^ r := by
  classical
  have hc (v : V) : Fintype.card {p : G.Walk u v // p.length = r} = (G.finsetWalkLength r u v).card := by
    exact Fintype.card_ofFinset (G.finsetWalkLength r u v) (fun p => SimpleGraph.mem_finsetWalkLength_iff)
  simp only [hc]
  clear hc
  induction r generalizing u with
  | zero =>
    have hz (v : V) : (G.finsetWalkLength 0 u v).card = if u = v then 1 else 0 := by
      by_cases h : u = v
      · subst v
        simp [SimpleGraph.finsetWalkLength]
      · simp [SimpleGraph.finsetWalkLength, h]
    simp [hz]
  | succ r ih =>
    calc
      _ ≤ ∑ v, ∑ w : G.neighborSet u, (G.finsetWalkLength r w v).card := by
        apply Finset.sum_le_sum
        intro v _
        simpa only [SimpleGraph.finsetWalkLength, Finset.card_map] using
          (Finset.card_biUnion_le (s := Finset.univ)
            (t := fun w : G.neighborSet u => (G.finsetWalkLength r w v).map
              ⟨fun p => SimpleGraph.Walk.cons w.property p, fun _ _ h => by cases h; rfl⟩))
      _ = ∑ w : G.neighborSet u, ∑ v, (G.finsetWalkLength r w v).card := Finset.sum_comm
      _ ≤ ∑ _w : G.neighborSet u, k ^ r := Finset.sum_le_sum fun w _ => ih w
      _ ≤ k ^ (r + 1) := by
        simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Set.fintypeCard_eq_ncard, pow_succ, Nat.mul_comm] using
          Nat.mul_le_mul_right (k ^ r) (hdeg u)

/-- Across all starting vertices, there are at most `|V| * k^r` walks of length `r`. -/
theorem card_all_walks_le_card_mul_pow {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k) (r : ℕ) :
    (∑ u, ∑ v, Fintype.card {p : G.Walk u v // p.length = r}) ≤ Fintype.card V * k ^ r := by
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun u _ => card_walks_from_le_pow G hdeg r u)

/-- Restricting to simple paths gives the same degree-power bound. -/
theorem card_paths_from_le_pow {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k) (r : ℕ) (u : V) :
    (∑ v, Fintype.card {p : G.Walk u v // p.IsPath ∧ p.length = r}) ≤ k ^ r := by
  apply le_trans _ (card_walks_from_le_pow G hdeg r u)
  apply Finset.sum_le_sum
  intro v _
  exact Fintype.card_le_of_injective
    (fun p : {p : G.Walk u v // p.IsPath ∧ p.length = r} =>
      (⟨p.val, p.property.2⟩ : {p : G.Walk u v // p.length = r}))
    (fun _ _ h => Subtype.ext (congrArg (fun p : {p : G.Walk u v // p.length = r} => p.val) h))

/-- Total simple-path count, bounded by the total walk estimate. -/
theorem card_all_paths_le_card_mul_pow {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k) (r : ℕ) :
    (∑ u, ∑ v, Fintype.card {p : G.Walk u v // p.IsPath ∧ p.length = r}) ≤
      Fintype.card V * k ^ r := by
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun u _ => card_paths_from_le_pow G hdeg r u)

end PropertyH

