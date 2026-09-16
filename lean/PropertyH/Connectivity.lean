import PropertyH.Expanders

namespace PropertyH

/-- A nonempty set closed under adjacency occupies more than half an expander. -/
theorem IsVertexExpander.card_lt_twice_of_closed {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h)
    (A : Finset V) (hne : A.Nonempty)
    (hclosed : ∀ u ∈ A, ∀ v, G.Adj u v → v ∈ A) :
    Fintype.card V < 2 * A.card := by
  by_contra! hsmall
  have hboundary : ({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V) = ∅ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    exact fun hv u hu hadj => hv (hclosed u hu v hadj.symm)
  have hbound := hex.2.2 A hsmall
  rw [hboundary, Set.ncard_empty, Nat.cast_zero] at hbound
  exact (not_lt_of_ge hbound) (mul_pos hex.1 (by exact_mod_cast hne.card_pos))

/-- Positive vertex expansion forces a nonempty finite graph to be connected. -/
theorem IsVertexExpander.connected {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) :
    G.Connected := by
  classical
  refine ⟨fun u v => ?_⟩
  by_contra huv
  let A : Finset V := Finset.univ.filter (G.Reachable u)
  have hA : ∀ x, x ∈ A ↔ G.Reachable u x := by simp [A]
  have hAne : A.Nonempty := ⟨u, (hA u).2 (.refl _)⟩
  have hlarge := hex.card_lt_twice_of_closed A hAne
    (fun x hx y hxy => (hA y).2 (((hA x).1 hx).trans hxy.reachable))
  have hAcne : Aᶜ.Nonempty := ⟨v, by simpa [hA] using huv⟩
  have hclarge := hex.card_lt_twice_of_closed Aᶜ hAcne (by
    simp only [Finset.mem_compl, hA]
    exact fun x hx y hxy huy => hx (huy.trans hxy.symm.reachable))
  have hcards := Finset.card_add_card_compl A
  omega
end PropertyH
