import PropertyH.Basic

namespace PropertyH

/-- Double counting the incidences between finite families of chambers and facets. -/
theorem incidence_degree_sum {C F : Type*} [Fintype C] [Fintype F]
    (R : C → F → Prop) [DecidableRel R] :
    (∑ c, (Finset.univ.filter (R c)).card) =
      ∑ f, (Finset.univ.filter (fun c => R c f)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The parity of the number of odd-degree chambers equals that of odd-degree facets. -/
theorem incidence_odd_degree_parity {C F : Type*} [Fintype C] [Fintype F]
    (R : C → F → Prop) [DecidableRel R] :
    Odd (Finset.univ.filter (fun c => Odd (Finset.univ.filter (R c)).card)).card ↔
      Odd (Finset.univ.filter (fun f => Odd (Finset.univ.filter (fun c => R c f)).card)).card := by
  rw [← Finset.odd_sum_iff_odd_card_odd, ← Finset.odd_sum_iff_odd_card_odd,
    incidence_degree_sum]

/-- The local `0/1/2` incidence pattern used in Sperner's argument transfers boundary parity
to the chambers incident with exactly one distinguished facet. -/
theorem sperner_incidence_parity {C F : Type*} [Fintype C] [Fintype F]
    (R : C → F → Prop) [DecidableRel R]
    (hc : ∀ c, (Finset.univ.filter (R c)).card ≤ 2)
    (hf : ∀ f, (Finset.univ.filter (fun c => R c f)).card ≤ 2) :
    Odd (Finset.univ.filter (fun c => (Finset.univ.filter (R c)).card = 1)).card ↔
      Odd (Finset.univ.filter (fun f => (Finset.univ.filter (fun c => R c f)).card = 1)).card := by
  have hlocal : ∀ n : ℕ, n ≤ 2 → (Odd n ↔ n = 1) := by
    intro n hn
    rw [Nat.odd_iff]
    omega
  simpa only [hlocal _ (hc _), hlocal _ (hf _)] using incidence_odd_degree_parity R

/-- An odd number of boundary facets forces a chamber with exactly one distinguished facet.
To apply this to Sperner, the geometric triangulation and labeling must separately establish
the incidence bounds and identify these chambers with fully labeled simplices. -/
theorem exists_single_incident_chamber_of_odd_boundary {C F : Type*}
    [Fintype C] [Fintype F] (R : C → F → Prop) [DecidableRel R]
    (hc : ∀ c, (Finset.univ.filter (R c)).card ≤ 2)
    (hf : ∀ f, (Finset.univ.filter (fun c => R c f)).card ≤ 2)
    (hboundary : Odd (Finset.univ.filter
      (fun f => (Finset.univ.filter (fun c => R c f)).card = 1)).card) :
    ∃ c, (Finset.univ.filter (R c)).card = 1 := by
  have hodd := (sperner_incidence_parity R hc hf).mpr hboundary
  have hpos := hodd.pos
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  exact ⟨c, (Finset.mem_filter.mp hc).2⟩

end PropertyH
