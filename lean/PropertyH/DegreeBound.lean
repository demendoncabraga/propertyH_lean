import PropertyH.Connectivity

namespace PropertyH

/-- Source: PII requires logarithmic base k > 1; expansion and |V| ≥ 5 force k ≥ 2. -/
theorem IsVertexExpander.two_le_degreeBound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h)
    (hcard : 5 ≤ Fintype.card V) : 2 ≤ k := by
  classical
  by_contra! hk
  have hsub : ∀ v, (G.neighborSet v).Subsingleton := fun v =>
    (Set.ncard_le_one (Set.toFinite _)).mp (by have := hex.2.1 v; omega)
  obtain ⟨u⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_cases hadj : ∃ v, G.Adj u v
  · obtain ⟨v, huv⟩ := hadj
    have hclosed : ∀ x ∈ ({u, v} : Finset V), ∀ y, G.Adj x y → y ∈ ({u, v} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro x (rfl | rfl) y hxy
      · exact Or.inr (hsub _ hxy huv)
      · exact Or.inl (hsub _ hxy huv.symm)
    have hlarge := hex.card_lt_twice_of_closed {u, v} (by simp) hclosed
    simp only [Finset.card_pair huv.ne] at hlarge
    omega
  · have hclosed : ∀ x ∈ ({u} : Finset V), ∀ y, G.Adj x y → y ∈ ({u} : Finset V) := by
      simp only [Finset.mem_singleton]
      rintro x rfl y hxy
      exact (hadj ⟨y, hxy⟩).elim
    have hlarge := hex.card_lt_twice_of_closed {u} (by simp) hclosed
    simp only [Finset.card_singleton] at hlarge
    omega
end PropertyH
