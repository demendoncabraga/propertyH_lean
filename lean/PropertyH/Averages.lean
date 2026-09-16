import PropertyH.Basic

noncomputable section
namespace PropertyH
variable {I X : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Source: the finite averages used in `Eq.psi.lowe.bound.sum` and `eq:ball`. -/
def average (f : I → X) : X := (Fintype.card I : ℝ)⁻¹ • ∑ i, f i

/-- Source: triangle inequality for finite averages in the proof of `Thm.main`. -/
theorem norm_average_le_average_norm (f : I → X) :
    ‖average f‖ ≤ average (fun i => ‖f i‖) := by
  simpa [average, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)] using
    mul_le_mul_of_nonneg_left (norm_sum_le Finset.univ f)
      (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)

omit [NormedSpace ℝ X] in
/-- Source: the first inequality of `Eq.psi.lowe.bound.sum`. -/
theorem average_pairwise_norm_le_two_average_norm (f : I → X) :
    average (fun i => average (fun j => ‖f i - f j‖)) ≤
      2 * average (fun i => ‖f i‖) := by
  have hp : (∑ i, ∑ j, ‖f i - f j‖) ≤ ∑ i, ∑ j, (‖f i‖ + ‖f j‖) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => norm_sub_le _ _))
  have hs : (∑ i, ∑ j, ‖f i - f j‖) ≤ 2 * (Fintype.card I : ℝ) * ∑ i, ‖f i‖ := by
    simpa [Finset.sum_add_distrib, Finset.mul_sum, two_mul, add_mul] using hp
  simpa [average, ← Finset.mul_sum, ← mul_assoc, mul_left_comm, mul_comm, Fintype.card_ne_zero] using
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs
      (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity))
      (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)

/-- Source: `eq:ball`, the zero-mean estimate preceding it. -/
theorem average_norm_le_two_average_translate_norm (ψ : I → X)
    (hψ : ∑ i, ψ i = 0) (x : X) :
    average (fun i => ‖ψ i‖) ≤ 2 * average (fun i => ‖x + ψ i‖) := by
  have hx : ‖x‖ ≤ average (fun i => ‖x + ψ i‖) := by
    have := norm_average_le_average_norm (fun i => x + ψ i)
    simpa [average, Finset.sum_add_distrib, hψ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Fintype.card_ne_zero] using this
  have hp : ∑ i, ‖ψ i‖ ≤ ∑ i, (‖x + ψ i‖ + ‖x‖) :=
    Finset.sum_le_sum (fun i _ => by simpa using norm_sub_le (x + ψ i) x)
  have hav : average (fun i => ‖ψ i‖) ≤ average (fun i => ‖x + ψ i‖) + ‖x‖ := by
    simpa [average, Finset.sum_add_distrib, mul_add, Fintype.card_ne_zero] using
      mul_le_mul_of_nonneg_left hp (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)
  linarith
end PropertyH

