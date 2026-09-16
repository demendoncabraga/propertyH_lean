import PropertyH.Averages
import PropertyH.Connectivity
import PropertyH.PairwiseDistances

noncomputable section
namespace PropertyH
open Filter

lemma coarse_const_le_average {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (c : ℝ) (hf : ∀ v, c ≤ f v) : c ≤ average f := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hf v)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (Fintype.card V : ℝ)⁻¹ by positivity)
  simpa [average, Fintype.card_ne_zero] using hm

/-- The average row distance is large when at least half the vertices lie outside a fixed ball. -/
theorem coarse_average_row_lower {V X : Type*} [Fintype V] [Nonempty V]
    [NormedAddCommGroup X] {G : SimpleGraph V} (hc : G.Connected)
    (k r : ℕ) (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (hlarge : 2*(1+k^r) ≤ Fintype.card V) (φ : V → X) (ρ : ℝ → ℝ)
    (hmono : Monotone ρ) (hrho : 0 ≤ ρ r)
    (hlower : ∀ v u, ρ (G.dist v u) ≤ ‖φ v - φ u‖) (v : V) :
    ρ r / 2 ≤ average (fun u => ‖φ v - φ u‖) := by
  classical
  let B := Finset.univ.filter fun u => G.dist v u ≤ r
  have hB : ({u | G.dist v u ≤ r} : Set V) = (B : Set V) := by ext u; simp [B]
  have hsmall := card_dist_le_bound hc hdeg v r
  rw [hB, Set.ncard_coe_finset] at hsmall
  have hcards := Finset.card_add_card_compl B
  have hfar : Fintype.card V ≤ 2*Bᶜ.card := by omega
  have hrow : ρ r * (Bᶜ.card : ℝ) ≤ ∑ u, ‖φ v - φ u‖ := by
    calc
      _ = ∑ _u ∈ Bᶜ, ρ r := by simp [mul_comm]
      _ ≤ ∑ u ∈ Bᶜ, ‖φ v - φ u‖ := by
        apply Finset.sum_le_sum
        intro u hu
        have hd : r < G.dist v u := by simpa [B] using hu
        exact (hmono (by exact_mod_cast hd.le)).trans (hlower v u)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hfarR : (Fintype.card V : ℝ) ≤ 2*(Bᶜ.card : ℝ) := by exact_mod_cast hfar
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hs : ρ r / 2 * (Fintype.card V : ℝ) ≤ ∑ u, ‖φ v - φ u‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hfarR hrho]
  have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hN.le)
  simpa [average, mul_comm, mul_left_comm, mul_assoc, hN.ne'] using hm

/-- Source: `Eq.Antoinfty`. Coarse compression forces the average norm to diverge.
No centering or upper Lipschitz estimate is needed for this part. -/
theorem coarse_average_norm_tendsto_atTop (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] (φ : ∀ n, E.V n → X n) (ρ : ℝ → ℝ)
    (hmono : Monotone ρ) (hrho : Tendsto ρ atTop atTop)
    (hlower : ∀ n v u, ρ ((E.graph n).dist v u) ≤ ‖φ n v - φ n u‖) :
    Tendsto (fun n => average (fun v => ‖φ n v‖)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hnat : Tendsto (fun r : ℕ => ρ (r : ℝ)) atTop atTop :=
    hrho.comp tendsto_natCast_atTop_atTop
  obtain ⟨r, hr⟩ := (hnat.eventually (eventually_ge_atTop (4*max b 0))).exists
  have hr0 : 0 ≤ ρ (r : ℝ) := by have := le_max_right b 0; linarith
  have hlarge : ∀ᶠ n in atTop, max 5 (2*(1+E.degreeBound^r)) ≤ Fintype.card (E.V n) :=
    E.grows.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with n hn
  have hfive : 5 ≤ Fintype.card (E.V n) := (le_max_left _ _).trans hn
  have hball : 2*(1+E.degreeBound^r) ≤ Fintype.card (E.V n) := (le_max_right _ _).trans hn
  have : Nonempty (E.V n) := Fintype.card_pos_iff.mp (by omega)
  have hrow : ∀ v, ρ (r : ℝ) / 2 ≤ average (fun u => ‖φ n v - φ n u‖) :=
    coarse_average_row_lower (E.expands n).connected E.degreeBound r (E.expands n).2.1
      hball (φ n) ρ hmono hr0 (hlower n)
  have havg := coarse_const_le_average _ _ hrow
  have htri := average_pairwise_norm_le_two_average_norm (φ n)
  have hb := le_max_left b 0
  linarith
end PropertyH
