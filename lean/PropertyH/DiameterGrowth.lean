import PropertyH.NormalizedFamily
noncomputable section
namespace PropertyH
open Filter

/-- Source: the graph diameters diverge with the vertex counts. -/
theorem expander_diameter_tendsto_atTop (E : ExpanderFamily) :
    Tendsto (fun n => (graphDiameter (E.graph n) : ℝ)) atTop atTop := by
  have hlarge : ∀ᶠ n in atTop, 16 ≤ Fintype.card (E.V n) :=
    E.grows.eventually (eventually_ge_atTop 16)
  obtain ⟨n₀, hn₀⟩ := hlarge.exists
  have hk : 1 < (E.degreeBound : ℝ) := by
    exact_mod_cast ((E.expands n₀).two_le_degreeBound (by omega : 5 ≤ Fintype.card (E.V n₀)))
  have hA : 0 < 1 / (4 * Real.log E.degreeBound) :=
    one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hk))
  have hloglim : Tendsto (fun n => Real.log (Fintype.card (E.V n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp E.grows)
  apply tendsto_atTop_mono' atTop _ (hloglim.const_mul_atTop hA)
  filter_upwards [hlarge] with n hn
  have : Nonempty (E.V n) := Fintype.card_pos_iff.mp (by omega)
  apply (expander_average_distance_log_lower (E.graph n) E.degreeBound E.expansion (E.expands n) hn).trans
  apply average_pairwise_le_const
  intro v u
  exact_mod_cast ((Finset.le_sup (f := (E.graph n).dist v) (Finset.mem_univ u)).trans
    (Finset.le_sup (f := fun v => Finset.univ.sup ((E.graph n).dist v)) (Finset.mem_univ v)))
end PropertyH
