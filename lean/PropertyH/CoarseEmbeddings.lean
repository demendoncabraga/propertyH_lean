import PropertyH.Expanders

namespace PropertyH
open Filter
/-- Revised manuscript: a common proper compression function and a common Lipschitz bound.
The compression is extended to all reals; only nonnegative arguments are used. -/
def EquiCoarseGraphEmbeddings (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] : Prop :=
  ∃ (L : ℝ) (ρ : ℝ → ℝ), 0 < L ∧ Monotone ρ ∧
    (∀ t, 0 ≤ t → 0 ≤ ρ t) ∧ Tendsto ρ atTop atTop ∧
    ∃ φ : ∀ n, E.V n → X n, ∀ n v u,
      ρ ((E.graph n).dist v u) ≤ ‖φ n v - φ n u‖ ∧
      ‖φ n v - φ n u‖ ≤ L * (E.graph n).dist v u

def ContainsCoarseExpanders (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ E : ExpanderFamily, EquiCoarseGraphEmbeddings E (fun _ => X)

/-- The previous biLipschitz hypothesis is a special case of the revised hypothesis. -/
theorem EquiGraphEmbeddings.to_coarse {E : ExpanderFamily} {X : ℕ → Type*}
    [∀ n, NormedAddCommGroup (X n)] (h : EquiGraphEmbeddings E X) :
    EquiCoarseGraphEmbeddings E X := by
  obtain ⟨L, hL, φ, hφ⟩ := h
  have hpos : 0 < L := by linarith
  refine ⟨L, fun t => t / L, hpos, ?_, ?_, ?_, φ, hφ⟩
  · exact fun a b hab => div_le_div_of_nonneg_right hab hpos.le
  · exact fun t ht => div_nonneg ht hpos.le
  · exact tendsto_id.atTop_div_const hpos
end PropertyH
