import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory
noncomputable section
namespace PropertyH

/-- The positive first absolute moment of a standard real Gaussian. -/
def gaussianAbsMoment : ℝ := ∫ t : ℝ, |t| ∂gaussianReal 0 1

theorem gaussianAbsMoment_pos : 0 < gaussianAbsMoment := by
  have hi : Integrable (fun t : ℝ => |t|) (gaussianReal 0 1) :=
    (memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)).abs
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  unfold gaussianAbsMoment
  rw [integral_pos_iff_support_of_nonneg (fun t => abs_nonneg t) hi]
  have hs : Function.support (fun t : ℝ => |t|) = ({0} : Set ℝ)ᶜ := by
    ext t
    simp
  rw [hs, measure_compl (measurableSet_singleton 0) (by simp)]
  simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian dual evaluation has an L1 norm proportional to its Hilbert dual norm. -/
theorem integral_abs_dual_stdGaussian (L : StrongDual ℝ E) :
    (∫ x, |L x| ∂stdGaussian E) = gaussianAbsMoment * ‖L‖ := by
  have hmap : (stdGaussian E).map L = (gaussianReal 0 1).map (fun t => ‖L‖ * t) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    congr 1
    simp only [mul_zero]
    ext
    simp
  rw [← integral_map L.continuous.aemeasurable (by fun_prop), hmap,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, abs_norm, integral_const_mul]
  exact mul_comm _ _

/-- Dual evaluation as an actual linear map into Gaussian L1. -/
def gaussianDualToL1 : StrongDual ℝ E →ₗ[ℝ] Lp ℝ 1 (stdGaussian E) where
  toFun L := (IsGaussian.memLp_dual (stdGaussian E) L 1 (by simp)).toLp L
  map_add' L M := by
    exact MemLp.toLp_add (IsGaussian.memLp_dual (stdGaussian E) L 1 (by simp))
      (IsGaussian.memLp_dual (stdGaussian E) M 1 (by simp))
  map_smul' c L := by
    exact MemLp.toLp_const_smul c (IsGaussian.memLp_dual (stdGaussian E) L 1 (by simp))

theorem norm_gaussianDualToL1 (L : StrongDual ℝ E) :
    ‖gaussianDualToL1 L‖ = gaussianAbsMoment * ‖L‖ := by
  rw [L1.norm_eq_integral_norm, ← integral_abs_dual_stdGaussian]
  apply integral_congr_ae
  filter_upwards [(IsGaussian.memLp_dual (stdGaussian E) L 1 (by simp)).coeFn_toLp] with x hx
  simp only [gaussianDualToL1, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
  rw [hx]

/-- Gaussian evaluation, normalized to preserve norms exactly. -/
def gaussianDualL1Isometry : StrongDual ℝ E →ₗᵢ[ℝ] Lp ℝ 1 (stdGaussian E) where
  toLinearMap := gaussianAbsMoment⁻¹ • gaussianDualToL1
  norm_map' L := by
    change ‖gaussianAbsMoment⁻¹ • gaussianDualToL1 L‖ = ‖L‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr gaussianAbsMoment_pos),
      norm_gaussianDualToL1, ← mul_assoc, inv_mul_cancel₀ gaussianAbsMoment_pos.ne', one_mul]

/-- Every finite-dimensional real Hilbert space embeds linearly and isometrically in L1. -/
def hilbertGaussianL1Isometry : E →ₗᵢ[ℝ] Lp ℝ 1 (stdGaussian E) :=
  gaussianDualL1Isometry.comp (InnerProductSpace.toDual ℝ E).toLinearIsometry
end PropertyH
