import PropertyH.TrivialCotype
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace PropertyH
open Filter
open scoped BigOperators

/-- Zero extension from the finite-dimensional sup space into real c₀ is linear. -/
def finiteToCZeroLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] CZero where
  toFun := finiteToCZero n
  map_add' f g := by
    ext k
    by_cases hk : k < n <;> simp [finiteToCZero, hk]
  map_smul' c f := by
    ext k
    by_cases hk : k < n <;> simp [finiteToCZero, hk]

/-- The zero-extension linear map preserves the supremum norm. -/
theorem finiteToCZeroLinear_norm (n : ℕ) (f : Fin n → ℝ) : ‖finiteToCZeroLinear n f‖ = ‖f‖ := by
  have h := (finiteToCZero_isometry n).dist_eq f 0
  change dist (finiteToCZeroLinear n f) (finiteToCZeroLinear n 0) = dist f 0 at h
  simpa only [dist_eq_norm, map_zero, sub_zero] using h

/-- Every signed sum of distinct unit coordinate vectors has supremum norm at most one. -/
theorem cZero_sign_sum_le (n : ℕ) (ε : Fin n → Bool) :
    ‖∑ i, (if ε i then (1 : ℝ) else -1) •
      finiteToCZeroLinear n (Pi.single i 1)‖ ≤ 1 := by
  rw [show (∑ i, (if ε i then (1 : ℝ) else -1) • finiteToCZeroLinear n (Pi.single i 1)) =
    finiteToCZeroLinear n (∑ i, (if ε i then (1 : ℝ) else -1) • Pi.single i 1) by
      simp only [map_sum, map_smul]]
  rw [finiteToCZeroLinear_norm]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  split <;> norm_num

/-- The unnormalized second Rademacher moment of n coordinate vectors is at most 2ⁿ. -/
theorem cZero_sign_secondmoment_le (n : ℕ) :
    (∑ ε : Fin n → Bool, ‖∑ i, (if ε i then (1 : ℝ) else -1) •
      finiteToCZeroLinear n (Pi.single i 1)‖ ^ 2) ≤ 2 ^ n := by
  calc
    _ ≤ ∑ _ε : Fin n → Bool, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ε _
      nlinarith [cZero_sign_sum_le n ε, norm_nonneg (∑ i, (if ε i then (1 : ℝ) else -1) • finiteToCZeroLinear n (Pi.single i 1))]
    _ = 2 ^ n := by simp

/-- Source: Cor.Prop.H, the parenthetical example that c₀ has trivial cotype.
For coordinate vectors, a hypothetical finite cotype bound gives n^(1/q) ≤ C
for all n, contradicting divergence. No Maurey--Pisier theorem is used. -/
theorem hasTrivialCotype_cZero : HasTrivialCotype CZero := by
  intro q hq hc
  obtain ⟨_, C, hC, hc⟩ := hc
  have hbound : ∀ n : ℕ, (n : ℝ) ^ (1 / q) ≤ C := by
    intro n
    have hn := hc n (fun i => finiteToCZeroLinear n (Pi.single i 1))
    simp only [finiteToCZeroLinear_norm, Pi.norm_single, norm_one, Real.one_rpow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hn
    have hs := Real.sqrt_le_sqrt (cZero_sign_secondmoment_le n)
    have hm := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ C * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ by positivity)
    rw [Real.sqrt_inv] at hn
    have hh := hn.trans hm
    simpa only [mul_assoc, inv_mul_cancel₀
      (ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < (2 : ℝ) ^ n))), mul_one]
      using hh
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / q)) atTop atTop := (tendsto_rpow_atTop (by positivity : 0 < 1 / q)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_atTop C)).exists
  exact (not_lt_of_ge (hbound n)) hn
end PropertyH

