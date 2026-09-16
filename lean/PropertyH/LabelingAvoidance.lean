import PropertyH.Basic
import Mathlib.Probability.Distributions.Uniform

/-! Finite independent edge-label counting used in Osajda's Lemmas 2.2 and 2.5.
The local-lemma step is separate: these results give its exact event probabilities.
Source: https://arxiv.org/pdf/1406.5015, equations (21)--(23). -/
open scoped ENNReal
namespace PropertyH.LabelingAvoidance
noncomputable section
variable {E A : Type*} [Fintype E] [Fintype A]
local instance : DecidableEq E := Classical.decEq E

/-- A forbidden local word fixes labels only on its support; all other edge labels
remain freely assignable. -/
def restrictionEventEquiv (s : Set E) (B : Set (s → A)) :
    {f : E → A // (fun e : s => f e) ∈ B} ≃ B × (↥(sᶜ) → A) := by
  classical
  exact (Equiv.subtypeEquiv (Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => A))
    (fun _ => Iff.rfl)).trans Equiv.prodSubtypeFstEquivSubtypeProd

theorem card_restriction_event (s : Set E) (B : Set (s → A)) :
    Nat.card {f : E → A // (fun e : s => f e) ∈ B} =
      Nat.card B * Fintype.card A ^ Nat.card ↥(sᶜ) := by
  classical
  simpa [Nat.card_eq_fintype_card] using
    Fintype.card_congr (restrictionEventEquiv s B)

/-- Probability under independent uniform labels is exactly the fraction of
forbidden local words, regardless of the number of edges outside their support. -/
theorem probability_restriction_event [Nonempty A] (s : Set E) (B : Set (s → A)) :
    (PMF.uniformOfFintype (E → A)).toOuterMeasure
      {f | (fun e : s => f e) ∈ B} =
      (Nat.card B : ℝ≥0∞) / (Fintype.card A : ℝ≥0∞) ^ Nat.card s := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hnum := card_restriction_event (A := A) s B
  have hden := Fintype.card_congr (Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => A))
  simp only [Fintype.card_prod, Fintype.card_fun] at hden
  change (Fintype.card {f : E → A // (fun e : s => f e) ∈ B} : ℝ≥0∞) /
    Fintype.card (E → A) = _
  have hnum' : Fintype.card {f : E → A // (fun e : s => f e) ∈ B} =
      Nat.card B * Fintype.card A ^ Nat.card ↥(sᶜ) := by
    simpa only [Nat.card_eq_fintype_card] using hnum
  rw [hnum', Fintype.card_fun, hden]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.card_eq_fintype_card]
  exact ENNReal.mul_div_mul_right _ _
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero (α := A)))
    (ENNReal.pow_ne_top (by simp))
/-- A bound on the number of forbidden local words gives the bad-event estimate
used as input to a local lemma. -/
theorem probability_restriction_event_le [Nonempty A] (s : Set E)
    (B : Set (s → A)) (M : ℕ) (hM : Nat.card B ≤ M) :
    (PMF.uniformOfFintype (E → A)).toOuterMeasure
      {f | (fun e : s => f e) ∈ B} ≤
      (M : ℝ≥0∞) / (Fintype.card A : ℝ≥0∞) ^ Nat.card s := by
  rw [probability_restriction_event]
  exact ENNReal.div_le_div_right (by exact_mod_cast hM) _

/-- Basic finite avoidance when the total forbidden probability is below one.
This auxiliary criterion does not replace Osajda's stronger local-lemma step. -/
theorem exists_avoiding_labeling [Nonempty A] {I : Type*} [Fintype I]
    (s : I → Set E) (B : ∀ i, Set (s i → A))
    (hsmall : (∑ i, (Nat.card (B i) : ℝ≥0∞) /
      (Fintype.card A : ℝ≥0∞) ^ Nat.card (s i)) < 1) :
    ∃ f : E → A, ∀ i, (fun e : s i => f e) ∉ B i := by
  classical
  by_contra h
  push Not at h
  have hcover : (⋃ i, {f : E → A | (fun e : s i => f e) ∈ B i}) = Set.univ := by
    ext f
    simpa using h f
  have hb := MeasureTheory.measure_iUnion_fintype_le
    (PMF.uniformOfFintype (E → A)).toOuterMeasure
    (fun i => {f : E → A | (fun e : s i => f e) ∈ B i})
  simp_rw [probability_restriction_event] at hb
  rw [hcover] at hb
  have hone : (PMF.uniformOfFintype (E → A)).toOuterMeasure Set.univ = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)
  rw [hone] at hb
  exact (not_lt_of_ge hb) hsmall

end
end PropertyH.LabelingAvoidance

