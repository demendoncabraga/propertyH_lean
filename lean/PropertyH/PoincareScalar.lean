import PropertyH.Averages
import PropertyH.Expanders
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
namespace PropertyH
open scoped BigOperators

/-- Number of oriented edges exiting a finite vertex set. -/
def cutSize {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V) : ℕ := by
  classical
  exact ∑ v ∈ Aᶜ, ((A.filter fun u => G.Adj v u).card)

/-- Every external boundary vertex contributes at least one crossing edge. -/
theorem boundary_card_le_cutSize {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) :
    ({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V).ncard ≤ cutSize G A := by
  classical
  let B := Aᶜ.filter fun v => ∃ u ∈ A, G.Adj v u
  have hB : ({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V) = (B : Set V) := by
    ext v
    simp [B]
  rw [hB, Set.ncard_coe_finset]
  change B.card ≤ ∑ v ∈ Aᶜ, (A.filter fun u => G.Adj v u).card
  calc
    B.card = ∑ v ∈ B, 1 := by simp
    _ ≤ ∑ v ∈ B, (A.filter fun u => G.Adj v u).card := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hadj⟩⟩
    _ ≤ ∑ v ∈ Aᶜ, (A.filter fun u => G.Adj v u).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem IsVertexExpander.cut_expansion {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h)
    (A : Finset V) (hsmall : 2 * A.card ≤ Fintype.card V) :
    h * (A.card : ℝ) ≤ cutSize G A := by
  exact (hex.2.2 A hsmall).trans (by exact_mod_cast boundary_card_le_cutSize G A)
theorem cutSize_compl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    cutSize G Aᶜ = cutSize G A := by
  classical
  unfold cutSize
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [compl_compl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  simp only [G.adj_comm]

/-- Expansion controls every cut by its smaller side. -/
theorem IsVertexExpander.cut_expansion_min {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h)
    (A : Finset V) :
    h * (min A.card Aᶜ.card : ℝ) ≤ cutSize G A := by
  have hcards := Finset.card_add_card_compl A
  by_cases ha : A.card ≤ Aᶜ.card
  · rw [min_eq_left (show (A.card : ℝ) ≤ Aᶜ.card by exact_mod_cast ha)]
    exact hex.cut_expansion A (by omega)
  · rw [min_eq_right (show (Aᶜ.card : ℝ) ≤ A.card by exact_mod_cast (show Aᶜ.card ≤ A.card by omega))]
    simpa only [cutSize_compl] using hex.cut_expansion Aᶜ (by omega)

open MeasureTheory

def thresholdDistance (a b t : ℝ) : ℝ :=
  |(if t < a then 1 else 0) - (if t < b then 1 else 0)|

theorem thresholdDistance_eq_indicator (a b : ℝ) :
    thresholdDistance a b = (Set.Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) := by
  funext t
  unfold thresholdDistance
  by_cases ha : t < a <;> by_cases hb : t < b <;>
    simp [ha, hb, Set.indicator, Set.mem_Ico]

theorem integrable_thresholdDistance (a b : ℝ) : Integrable (thresholdDistance a b) := by
  rw [thresholdDistance_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (by simp [Real.volume_Ico]))

theorem integral_thresholdDistance (a b : ℝ) :
    ∫ t, thresholdDistance a b t = |a-b| := by
  rw [thresholdDistance_eq_indicator, integral_indicator measurableSet_Ico]
  simp only [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ico,
    smul_eq_mul, mul_one]
  rw [max_eq_left (sub_nonneg.mpr (min_le_max))]
  simpa only [abs_sub_comm] using max_sub_min_eq_abs a b

def cutValue {V : Type*} [DecidableEq V] (A : Finset V) (v : V) : ℝ :=
  if v ∈ A then 1 else 0

theorem cutValue_row_sum {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V) (v : V) :
    ∑ u, |cutValue A v - cutValue A u| = if v ∈ A then (Aᶜ.card : ℝ) else A.card := by
  classical
  by_cases hv : v ∈ A
  · simp only [cutValue, hv, if_true]
    have heq : ∀ u, |(1 : ℝ) - (if u ∈ A then 1 else 0)| = if u ∈ Aᶜ then 1 else 0 := by
      intro u
      by_cases hu : u ∈ A <;> simp [hu]
    calc
      _ = ∑ u, (if u ∈ Aᶜ then (1 : ℝ) else 0) := Finset.sum_congr rfl (fun u _ => heq u)
      _ = _ := by rw [Finset.sum_boole]; congr 2; ext u; simp
  · simp only [cutValue, hv, if_false]
    have heq : ∀ u, |(0 : ℝ) - (if u ∈ A then 1 else 0)| = if u ∈ A then 1 else 0 := by
      intro u
      by_cases hu : u ∈ A <;> simp [hu]
    calc
      _ = ∑ u, (if u ∈ A then (1 : ℝ) else 0) := Finset.sum_congr rfl (fun u _ => heq u)
      _ = _ := by simp

theorem cutValue_pair_sum {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V) :
    ∑ v, ∑ u, |cutValue A v - cutValue A u| = 2 * (A.card : ℝ) * Aᶜ.card := by
  simp only [cutValue_row_sum]
  rw [← Finset.sum_add_sum_compl A]
  rw [Finset.sum_congr rfl (fun i hi => if_pos hi)]
  have hcomp : ∀ i ∈ Aᶜ, (if i ∈ A then (Aᶜ.card : ℝ) else A.card) = A.card :=
    fun i hi => if_neg (Finset.mem_compl.mp hi)
  rw [Finset.sum_congr rfl hcomp]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

def edgeVariation {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℝ) : ℝ := by
  classical
  exact ∑ v, ∑ u, if G.Adj v u then |f v - f u| else 0

theorem cutSize_le_edgeVariation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) :
    (cutSize G A : ℝ) ≤ edgeVariation G (cutValue A) := by
  classical
  unfold cutSize edgeVariation
  push_cast
  have heq : ∀ v ∈ Aᶜ, ((A.filter fun u => G.Adj v u).card : ℝ) =
      ∑ u ∈ A, if G.Adj v u then |cutValue A v - cutValue A u| else 0 := by
    intro v hv
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro u hu
    simp [cutValue, hu, Finset.mem_compl.mp hv]
  rw [Finset.sum_congr rfl heq]
  calc
    _ ≤ ∑ v ∈ Aᶜ, ∑ u, if G.Adj v u then |cutValue A v - cutValue A u| else 0 := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

theorem IsVertexExpander.cut_pairwise_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) (A : Finset V) :
    h * (∑ v, ∑ u, |cutValue A v - cutValue A u|) ≤
      2 * (Fintype.card V : ℝ) * edgeVariation G (cutValue A) := by
  rw [cutValue_pair_sum]
  have hm := hex.cut_expansion_min A
  have he := cutSize_le_edgeVariation G A
  have hA : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ A
  have hAc : (Aᶜ.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ Aᶜ
  have hnn : (0 : ℝ) ≤ A.card := by positivity
  have hcn : (0 : ℝ) ≤ Aᶜ.card := by positivity
  by_cases ha : (A.card : ℝ) ≤ Aᶜ.card
  · rw [min_eq_left ha] at hm
    nlinarith [mul_le_mul_of_nonneg_left hAc (mul_nonneg hex.1.le hnn)]
  · rw [min_eq_right (le_of_not_ge ha)] at hm
    nlinarith [mul_le_mul_of_nonneg_left hA (mul_nonneg hex.1.le hcn)]

/-- Scalar coarea turns the cut estimate into a sum-of-edge-differences bound. -/
theorem IsVertexExpander.scalar_pairwise_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) (f : V → ℝ) :
    h * (∑ v, ∑ u, |f v - f u|) ≤
      2 * (Fintype.card V : ℝ) * edgeVariation G f := by
  classical
  have hcut : ∀ t, h * (∑ v, ∑ u, thresholdDistance (f v) (f u) t) ≤
      2 * (Fintype.card V : ℝ) *
        (∑ v, ∑ u, if G.Adj v u then thresholdDistance (f v) (f u) t else 0) := by
    intro t
    simpa only [cutValue, Finset.mem_filter, Finset.mem_univ, true_and, thresholdDistance,
      edgeVariation] using hex.cut_pairwise_bound (Finset.univ.filter fun v => t < f v)
  have hint : ∀ v u, Integrable (thresholdDistance (f v) (f u)) :=
    fun v u => integrable_thresholdDistance _ _
  have heint : ∀ v u, Integrable (fun t => if G.Adj v u then thresholdDistance (f v) (f u) t else 0) := by
    intro v u
    split_ifs
    · exact hint v u
    · exact integrable_zero _ _ _
  have hi := integral_mono
    ((integrable_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => hint v u))).const_mul h)
    ((integrable_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => heint v u))).const_mul
      (2 * (Fintype.card V : ℝ))) hcut
  simp only [integral_const_mul] at hi
  rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => hint v u)),
    integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => heint v u))] at hi
  simp_rw [integral_finsetSum _ (fun u _ => hint _ u), integral_thresholdDistance] at hi
  have heval : ∀ v, (∫ t, ∑ u, if G.Adj v u then thresholdDistance (f v) (f u) t else 0) =
      ∑ u, if G.Adj v u then |f v - f u| else 0 := by
    intro v
    rw [integral_finsetSum _ (fun u _ => heint v u)]
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs
    · exact integral_thresholdDistance _ _
    · simp
  simp_rw [heval] at hi
  exact hi

/-- Jensen's triangle bound, ready to use for both scalar and L1 functions. -/
theorem mean_deviation_le_pairwise {V X : Type*} [Fintype V] [Nonempty V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (f : V → X) :
    (Fintype.card V : ℝ) * ∑ v, ‖f v - average f‖ ≤ ∑ v, ∑ u, ‖f v - f u‖ := by
  have heq : ∀ v, average (fun u => f v - f u) = f v - average f := by
    intro v
    simp [average, Finset.sum_sub_distrib, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub,
      smul_smul, Fintype.card_ne_zero]
  have hp := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => norm_average_le_average_norm (fun u => f v - f u))
  simp_rw [heq] at hp
  simp only [average, smul_eq_mul, ← Finset.mul_sum] at hp
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ht := mul_le_mul_of_nonneg_left hp hN.le
  simpa only [average, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] using ht

/-- The scalar mean-deviation form, retaining edge sums for later integration. -/
theorem IsVertexExpander.scalar_mean_bound {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) (f : V → ℝ) :
    h * (∑ v, |f v - average f|) ≤ 2 * edgeVariation G f := by
  have hp := hex.scalar_pairwise_bound f
  have hj := mean_deviation_le_pairwise f
  simp only [Real.norm_eq_abs] at hj
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  nlinarith [mul_le_mul_of_nonneg_left hj hex.1.le]

theorem edgeVariation_le_of_lipschitz {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (f : V → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ v u, |f v - f u| ≤ L * G.dist v u) :
    edgeVariation G f ≤ (Fintype.card V : ℝ) * k * L := by
  classical
  have hrow : ∀ v, (∑ u, if G.Adj v u then |f v - f u| else 0) ≤ (k : ℝ) * L := by
    intro v
    have hi : (∑ u, if G.Adj v u then |f v - f u| else 0) ≤
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
  simpa only [edgeVariation, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hs

/-- The real-valued PIII estimate, with the exact manuscript constant. -/
theorem IsVertexExpander.scalar_poincare {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h)
    (f : V → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ v u, |f v - f u| ≤ L * G.dist v u) :
    (Fintype.card V : ℝ)⁻¹ * (∑ v, |f v - average f|) ≤ (2 * k / h) * L := by
  have hm := hex.scalar_mean_bound f
  have he := edgeVariation_le_of_lipschitz hex.2.1 f L hL hf
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hb : h * (∑ v, |f v - average f|) ≤ 2 * (Fintype.card V : ℝ) * k * L := by nlinarith
  have hs : (∑ v, |f v - average f|) ≤ (2 * (Fintype.card V : ℝ) * k * L) / h :=
    (le_div_iff₀ hex.1).mpr (by nlinarith)
  calc
    _ = (∑ v, |f v - average f|) / (Fintype.card V : ℝ) := by ring
    _ ≤ ((2 * (Fintype.card V : ℝ) * k * L) / h) / Fintype.card V :=
      div_le_div_of_nonneg_right hs hN.le
    _ = _ := by field_simp
end PropertyH
