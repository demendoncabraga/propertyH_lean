import PropertyH.RadialUniform
import PropertyH.Averages

noncomputable section
namespace PropertyH
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def radialTruncate (A : ℝ) (x : X) : X :=
  if ‖x‖ ≤ A then x else (A / ‖x‖) • x

theorem norm_radialTruncate (A : ℝ) (hA : 0 ≤ A) (x : X) :
    ‖radialTruncate A x‖ = min ‖x‖ A := by
  by_cases h : ‖x‖ ≤ A
  · simp [radialTruncate, h]
  · have hx : 0 < ‖x‖ := lt_of_le_of_lt hA (lt_of_not_ge h)
    simp [radialTruncate, h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hA,
      div_mul_cancel₀ _ hx.ne', min_eq_right (le_of_not_ge h)]

theorem norm_radialTruncate_sub_self (A : ℝ) (hA : 0 ≤ A) (x : X) :
    ‖radialTruncate A x - x‖ = max (‖x‖ - A) 0 := by
  by_cases h : ‖x‖ ≤ A
  · simp [radialTruncate, h]
  · have hx : 0 < ‖x‖ := lt_of_le_of_lt hA (lt_of_not_ge h)
    have hr : A / ‖x‖ - 1 ≤ 0 := sub_nonpos.mpr ((div_le_one hx).mpr (le_of_not_ge h))
    rw [radialTruncate, if_neg h]
    have he : (A / ‖x‖) • x - x = (A / ‖x‖ - 1) • x := by module
    rw [he, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonpos hr]
    rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    field_simp
    ring

theorem norm_radialTruncate_error_le (A : ℝ) (hA : 0 ≤ A) (x : X) :
    ‖radialTruncate A x - x‖ ≤ |‖x‖ - A| := by
  rw [norm_radialTruncate_sub_self A hA]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem radialTruncate_dist_le (A : ℝ) (hA : 0 ≤ A) (x y : X) :
    dist (radialTruncate A x) (radialTruncate A y) ≤ 2 * dist x y := by
  have hmixed : ∀ x y : X, ‖x‖ ≤ A → A < ‖y‖ →
      dist (radialTruncate A x) (radialTruncate A y) ≤ 2 * dist x y := by
    intro x y hx hy
    have he := norm_radialTruncate_sub_self A hA y
    rw [max_eq_left (sub_nonneg.mpr hy.le)] at he
    have hn := norm_sub_norm_le y x
    have ht := dist_triangle x y (radialTruncate A y)
    rw [dist_comm y, dist_eq_norm (radialTruncate A y), he] at ht
    rw [show radialTruncate A x = x by simp [radialTruncate, hx]]
    rw [norm_sub_rev, ← dist_eq_norm] at hn
    linarith
  by_cases hx : ‖x‖ ≤ A
  · by_cases hy : ‖y‖ ≤ A
    · simp only [radialTruncate, if_pos hx, if_pos hy]
      linarith [dist_nonneg (x := x) (y := y)]
    · exact hmixed x y hx (lt_of_not_ge hy)
  · by_cases hy : ‖y‖ ≤ A
    · simpa only [dist_comm] using hmixed y x hy (lt_of_not_ge hx)
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hA (lt_of_not_ge hx))
      have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hA (lt_of_not_ge hy))
      have ht := norm_mul_dist_sphereNormalize_le x y hx0 hy0
      have hscale := mul_le_mul_of_nonneg_right (le_of_not_ge hx)
        (dist_nonneg (x := sphereNormalize x hx0) (y := sphereNormalize y hy0))
      have he : dist (radialTruncate A x) (radialTruncate A y) =
          A * dist (sphereNormalize x hx0) (sphereNormalize y hy0) := by
        simp only [radialTruncate, if_neg hx, if_neg hy, sphereNormalize,
          div_eq_mul_inv, mul_smul, Subtype.dist_eq, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hA]
      rw [he]
      exact hscale.trans ht
theorem radialTruncate_lipschitz (A : ℝ) (hA : 0 ≤ A) :
    LipschitzWith 2 (radialTruncate (X := X) A) := by
  exact LipschitzWith.of_dist_le_mul (radialTruncate_dist_le A hA)

variable {I : Type*} [Fintype I] [Nonempty I]

theorem trunc_average_mono {f g : I → ℝ} (h : ∀ i, f i ≤ g i) : average f ≤ average g := by
  unfold average
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h i)) (by positivity)

def truncatedNormalization (φ : I → X) (A C : ℝ) (i : I) : X :=
  (A + C)⁻¹ • (radialTruncate A (φ i) - average (fun j => radialTruncate A (φ j)))

theorem truncatedNormalization_bounds (φ : I → X) (A C : ℝ)
    (hmean : average (fun i => ‖φ i‖) = A) (hzero : ∑ i, φ i = 0)
    (hdev : average (fun i => |‖φ i‖ - A|) ≤ C) (hC : 0 < C) :
    (∑ i, truncatedNormalization φ A C i) = 0 ∧
    (∀ i, ‖truncatedNormalization φ A C i‖ ≤ 1) ∧
    (∀ i j, ‖truncatedNormalization φ A C i - truncatedNormalization φ A C j‖ ≤
      (2 / (A + C)) * ‖φ i - φ j‖) ∧
    (A - 2 * C) / (A + C) ≤ average (fun i => ‖truncatedNormalization φ A C i‖) := by
  have hA : 0 ≤ A := by rw [← hmean]; unfold average; positivity
  have hAC : 0 < A + C := by linarith
  let T : I → X := fun i => radialTruncate A (φ i)
  have herr : average (fun i => ‖T i - φ i‖) ≤ C :=
    (trunc_average_mono (fun i => norm_radialTruncate_error_le A hA (φ i))).trans hdev
  have havg : average (fun i => T i - φ i) = average T := by
    simp [average, Finset.sum_sub_distrib, hzero]
  have hcenter : ‖average T‖ ≤ C := by
    have hh := norm_average_le_average_norm (fun i => T i - φ i)
    rw [havg] at hh
    exact hh.trans herr
  have hnorm : ∀ i, ‖T i - average T‖ ≤ A + C := by
    intro i
    have hi : ‖T i‖ ≤ A := by
      change ‖radialTruncate A (φ i)‖ ≤ A
      rw [norm_radialTruncate A hA]
      exact min_le_right _ _
    exact (norm_sub_le _ _).trans (add_le_add hi hcenter)
  have hlower : A - 2 * C ≤ average (fun i => ‖T i - average T‖) := by
    have hp : ∀ i, ‖φ i‖ ≤ ‖T i - average T‖ + ‖average T‖ + ‖T i - φ i‖ := by
      intro i
      have hh := norm_le_norm_add_norm_sub (T i) (φ i)
      have hh' := norm_le_norm_add_norm_sub (average T) (T i)
      rw [norm_sub_rev (average T)] at hh'
      linarith
    have hh := trunc_average_mono hp
    have he : average (fun i => ‖T i - average T‖ + ‖average T‖ + ‖T i - φ i‖) =
        average (fun i => ‖T i - average T‖) + ‖average T‖ +
          average (fun i => ‖T i - φ i‖) := by
      simp [average, Finset.sum_add_distrib, mul_add, Fintype.card_ne_zero]
    rw [he, hmean] at hh
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [truncatedNormalization, ← Finset.smul_sum, Finset.sum_sub_distrib,
      average, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Fintype.card_ne_zero]
  · intro i
    have hh := mul_le_mul_of_nonneg_left (hnorm i) (le_of_lt (inv_pos.mpr hAC))
    simpa [truncatedNormalization, norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hAC)),
      hAC.ne', T] using hh
  · intro i j
    have hh := radialTruncate_dist_le A hA (φ i) (φ j)
    rw [dist_eq_norm, dist_eq_norm] at hh
    have hs := mul_le_mul_of_nonneg_left hh (le_of_lt (inv_pos.mpr hAC))
    simpa [truncatedNormalization, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hAC)), div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hs
  · have hh := mul_le_mul_of_nonneg_left hlower (le_of_lt (inv_pos.mpr hAC))
    simpa [truncatedNormalization, norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hAC)),
      average, ← Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, T] using hh
end PropertyH

