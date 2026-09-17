import PropertyH.PoincareScalar
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
namespace PropertyH
open MeasureTheory
open scoped BigOperators

/-- Pairwise L1 distance is the integral of pairwise scalar representative distance. -/
theorem L1_integral_abs_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Lp ℝ 1 μ) : (∫ x, |f x - g x| ∂μ) = ‖f - g‖ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  simp only [Real.norm_eq_abs, hx, Pi.sub_apply]

/-- Coarea's scalar pairwise estimate integrates to arbitrary real L1 spaces. -/
theorem IsVertexExpander.L1_pairwise_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : V → Lp ℝ 1 μ) :
    h * (∑ v, ∑ u, ‖f v - f u‖) ≤
      2 * (Fintype.card V : ℝ) *
        (∑ v, ∑ u, if G.Adj v u then ‖f v - f u‖ else 0) := by
  classical
  have hint : ∀ v u, Integrable (fun x => |f v x - f u x|) μ := by
    intro v u
    exact ((L1.integrable_coeFn (f v)).sub (L1.integrable_coeFn (f u))).abs
  have heint : ∀ v u, Integrable (fun x => if G.Adj v u then |f v x - f u x| else 0) μ := by
    intro v u
    split_ifs
    · exact hint v u
    · exact integrable_zero _ _ _
  have hpoint : ∀ x, h * (∑ v, ∑ u, |f v x - f u x|) ≤
      2 * (Fintype.card V : ℝ) * (∑ v, ∑ u, if G.Adj v u then |f v x - f u x| else 0) :=
    fun x => by
      have hs := hex.scalar_pairwise_bound (fun v => f v x)
      have heq : edgeVariation G (fun v => f v x) =
          ∑ v, ∑ u, if G.Adj v u then |f v x - f u x| else 0 := by
        unfold edgeVariation
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hadj : G.Adj v u <;> simp [hadj]
      rw [heq] at hs
      exact hs
  have hi := integral_mono
    ((integrable_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => hint v u))).const_mul h)
    ((integrable_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => heint v u))).const_mul
      (2 * (Fintype.card V : ℝ))) hpoint
  simp only [integral_const_mul] at hi
  rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => hint v u)),
    integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => heint v u))] at hi
  simp_rw [integral_finsetSum _ (fun u _ => hint _ u), L1_integral_abs_sub] at hi
  have heval : ∀ v, (∫ x, ∑ u, if G.Adj v u then |f v x - f u x| else 0 ∂μ) =
      ∑ u, if G.Adj v u then ‖f v - f u‖ else 0 := by
    intro v
    rw [integral_finsetSum _ (fun u _ => heint v u)]
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs
    · exact L1_integral_abs_sub _ _ _
    · simp
  simp_rw [heval] at hi
  exact hi
theorem norm_edge_sum_le_of_lipschitz {V X : Type*} [Fintype V]
    [NormedAddCommGroup X] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (f : V → X) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ v u, ‖f v - f u‖ ≤ L * G.dist v u) :
    (∑ v, ∑ u, if G.Adj v u then ‖f v - f u‖ else 0) ≤ (Fintype.card V : ℝ) * k * L := by
  classical
  have hrow : ∀ v, (∑ u, if G.Adj v u then ‖f v - f u‖ else 0) ≤ (k : ℝ) * L := by
    intro v
    have hi : (∑ u, if G.Adj v u then ‖f v - f u‖ else 0) ≤
        ∑ u, if G.Adj v u then L else 0 := by
      apply Finset.sum_le_sum
      intro u hu
      split_ifs with hadj
      · simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, Nat.cast_one, mul_one] using hf v u
      · rfl
    have hcard : (Finset.univ.filter fun u => G.Adj v u).card ≤ k := by
      have heq : G.neighborSet v = (↑(Finset.univ.filter fun u => G.Adj v u) : Set V) := by
        ext u
        simp
      simpa only [heq, Set.ncard_coe_finset] using hdeg v
    calc
      _ ≤ ∑ u, if G.Adj v u then L else 0 := hi
      _ = ((Finset.univ.filter fun u => G.Adj v u).card : ℝ) * L := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (k : ℝ) * L := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hL
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hrow v)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hs

/-- Source PIII: the L1-valued Poincare inequality with the manuscript constant. -/
theorem expander_poincare_proved {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : V → Lp ℝ 1 μ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ v u, ‖f v - f u‖ ≤ L * G.dist v u) :
    (Fintype.card V : ℝ)⁻¹ *
      (∑ v, ‖f v - (Fintype.card V : ℝ)⁻¹ • ∑ u, f u‖) ≤ (2 * k / h) * L := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hEmpty =>
    simp only [Fintype.card_eq_zero, Nat.cast_zero, inv_zero, zero_mul]
    exact mul_nonneg (div_nonneg (by positivity) hG.1.le) hL
  | inr hNonempty =>
    have hp := hG.L1_pairwise_bound μ f
    have hj := mean_deviation_le_pairwise f
    have he := norm_edge_sum_le_of_lipschitz hG.2.1 f L hL hf
    have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have hm : h * (∑ v, ‖f v - average f‖) ≤
        2 * (∑ v, ∑ u, if G.Adj v u then ‖f v - f u‖ else 0) := by
      nlinarith [mul_le_mul_of_nonneg_left hj hG.1.le]
    have hb : h * (∑ v, ‖f v - average f‖) ≤ 2 * (Fintype.card V : ℝ) * k * L := by
      nlinarith
    have hs : (∑ v, ‖f v - average f‖) ≤ (2 * (Fintype.card V : ℝ) * k * L) / h :=
      (le_div_iff₀ hG.1).mpr (by nlinarith)
    change (Fintype.card V : ℝ)⁻¹ * (∑ v, ‖f v - average f‖) ≤ _
    calc
      _ = (∑ v, ‖f v - average f‖) / (Fintype.card V : ℝ) := by ring
      _ ≤ ((2 * (Fintype.card V : ℝ) * k * L) / h) / Fintype.card V :=
        div_le_div_of_nonneg_right hs hN.le
      _ = _ := by field_simp
end PropertyH
