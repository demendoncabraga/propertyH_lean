import PropertyH.Averages
import PropertyH.RadialExtension

/-! Continuous finite averages and the quantitative lower bounds in the main proof. -/
noncomputable section
namespace PropertyH
open scoped unitInterval

variable {V X Y : Type*} [Fintype V] [Nonempty V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Source: `$H_s(x)=|V|^{-1}\sum_v G(x+s\psi(v))$`, `eq:average`. -/
def averagingFamily (ψ : V → X) (G : C(X, Y)) : C(I × UnitBall X, Y) where
  toFun p := average (fun v => G ((p.2 : X) + (p.1 : ℝ) • ψ v))
  continuous_toFun := by
    unfold average
    fun_prop

/-- Source: `$H_0=G$`, used in `eq:homotopy`. -/
theorem averagingFamily_zero (ψ : V → X) (G : C(X, Y)) (x : UnitBall X) :
    averagingFamily ψ G (0, x) = G (x : X) := by
  simp [averagingFamily, average, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    Fintype.card_ne_zero]

/-- Source: `eq:key`, the triangle inequality comparing mean norm and norm of mean. -/
theorem average_norm_sub_deviation_le (f : V → Y) :
    average (fun v => ‖f v‖) - average (fun v => ‖f v - average f‖) ≤ ‖average f‖ := by
  have hp : ∑ v, ‖f v‖ ≤ ∑ v, (‖f v - average f‖ + ‖average f‖) :=
    Finset.sum_le_sum (fun v _ => by simpa only [sub_add_cancel] using norm_add_le (f v - average f) (average f))
  have hav : average (fun v => ‖f v‖) ≤
      average (fun v => ‖f v - average f‖) + ‖average f‖ := by
    simpa [average, Finset.sum_add_distrib, mul_add, Fintype.card_ne_zero] using
      mul_le_mul_of_nonneg_left hp (show 0 ≤ (Fintype.card V : ℝ)⁻¹ by positivity)
  linarith

/-- Source: zero mean implies the average translated norm is at least `‖x‖`. -/
theorem norm_le_average_translate_smul_norm (ψ : V → X) (hψ : ∑ v, ψ v = 0)
    (x : X) (t : ℝ) : ‖x‖ ≤ average (fun v => ‖x + t • ψ v‖) := by
  simpa [average, Finset.sum_add_distrib, ← Finset.smul_sum, hψ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Fintype.card_ne_zero] using
      norm_average_le_average_norm (fun v => x + t • ψ v)

end PropertyH
