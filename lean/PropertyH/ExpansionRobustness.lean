import PropertyH.PoincareScalar

noncomputable section
namespace PropertyH

/-- A crossing-edge count is bounded by maximum degree times vertex-boundary size. -/
theorem cutSize_le_degree_mul_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k) (A : Finset V) :
    cutSize G A ≤ k * ({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V).ncard := by
  classical
  let B := Aᶜ.filter fun v => ∃ u ∈ A, G.Adj v u
  have hB : ({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V) = (B : Set V) := by
    ext v
    simp [B]
  rw [hB, Set.ncard_coe_finset]
  have hrow : ∀ v, (A.filter fun u => G.Adj v u).card ≤ k := by
    intro v
    have hsub : (↑(A.filter fun u => G.Adj v u) : Set V) ⊆ G.neighborSet v := by
      intro u hu
      exact (Finset.mem_filter.mp hu).2
    have hcard := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset] at hcard
    exact hcard.trans (hdeg v)
  have heq : cutSize G A = ∑ v ∈ B, (A.filter fun u => G.Adj v u).card := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hvB
    have hno : ¬∃ u ∈ A, G.Adj v u := by
      intro hu
      exact hvB (Finset.mem_filter.mpr ⟨hv, hu⟩)
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact hno ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
  rw [heq]
  have hs := Finset.sum_le_sum (s := B) (fun v _ => hrow v)
  simpa [mul_comm] using hs

/-- Deleting at most r incident edges per vertex loses at most r|A| cut edges. -/
theorem cutSize_le_cutSize_add_deleted_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (r : ℕ)
    (hdel : ∀ v, ({u | G.Adj v u ∧ ¬H.Adj v u} : Set V).ncard ≤ r) (A : Finset V) :
    cutSize G A ≤ cutSize H A + r*A.card := by
  classical
  have hrow : ∀ v, (Aᶜ.filter fun u => G.Adj v u).card ≤
      (Aᶜ.filter fun u => H.Adj v u).card + r := by
    intro v
    let D := Finset.univ.filter fun u => G.Adj v u ∧ ¬H.Adj v u
    have hD : ({u | G.Adj v u ∧ ¬H.Adj v u} : Set V) = (D : Set V) := by
      ext u
      simp [D]
    have hd := hdel v
    rw [hD, Set.ncard_coe_finset] at hd
    have hsub : (Aᶜ.filter fun u => G.Adj v u) ⊆ (Aᶜ.filter fun u => H.Adj v u) ∪ D := by
      intro u hu
      by_cases hh : H.Adj v u
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, hh⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2, hh⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hd _))
  have hs := Finset.sum_le_sum (s := A) (fun v _ => hrow v)
  have heqG : cutSize G A = ∑ v ∈ A, (Aᶜ.filter fun u => G.Adj v u).card := by
    rw [← cutSize_compl G A]
    simp only [cutSize, compl_compl]
  have heqH : cutSize H A = ∑ v ∈ A, (Aᶜ.filter fun u => H.Adj v u).card := by
    rw [← cutSize_compl H A]
    simp only [cutSize, compl_compl]
  rw [heqG, heqH]
  simpa [Finset.sum_add_distrib, mul_comm] using hs

/-- Edge expansion exceeding the local deletion budget yields a vertex expander after deletion. -/
theorem vertex_expander_of_edge_expansion_after_deletion
    {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    (k r : ℕ) (c : ℝ) (hk : 0 < k) (hc : (r : ℝ) < c) (hHG : H ≤ G)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (hedge : ∀ A : Finset V, 2*A.card ≤ Fintype.card V →
      c * (A.card : ℝ) ≤ cutSize G A)
    (hdel : ∀ v, ({u | G.Adj v u ∧ ¬H.Adj v u} : Set V).ncard ≤ r) :
    IsVertexExpander H k ((c-r)/k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdegH : ∀ v, (H.neighborSet v).ncard ≤ k := by
    intro v
    exact (Set.ncard_le_ncard (fun u hu => hHG hu)).trans (hdeg v)
  refine ⟨div_pos (sub_pos.mpr hc) hkR, hdegH, ?_⟩
  intro A hA
  have hi := hedge A hA
  have hd : (cutSize G A : ℝ) ≤ cutSize H A + (r : ℝ)*A.card := by
    exact_mod_cast cutSize_le_cutSize_add_deleted_degree G H r hdel A
  have hb : (cutSize H A : ℝ) ≤ (k : ℝ) *
      ({v | v ∉ A ∧ ∃ u ∈ A, H.Adj v u} : Set V).ncard := by
    exact_mod_cast cutSize_le_degree_mul_boundary H k hdegH A
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hkR).mpr
  nlinarith

/-- At a nonempty exact-half cut, a global vertex-expansion constant cannot exceed one. -/
theorem IsVertexExpander.expansion_le_one_of_half_set
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h)
    (A : Finset V) (hne : A.Nonempty) (hhalf : 2*A.card = Fintype.card V) : h ≤ 1 := by
  have hi := hex.2.2 A hhalf.le
  have hs : ({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V) ⊆ (↑Aᶜ : Set V) := by
    intro v hv
    exact Finset.mem_compl.mpr hv.1
  have hc := Set.ncard_le_ncard hs
  rw [Set.ncard_coe_finset] at hc
  have hcards := Finset.card_add_card_compl A
  have heq : Aᶜ.card = A.card := by omega
  rw [heq] at hc
  have hcR : (({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V).ncard : ℝ) ≤ A.card := by
    exact_mod_cast hc
  have haR : (0 : ℝ) < A.card := by exact_mod_cast hne.card_pos
  nlinarith
end PropertyH
