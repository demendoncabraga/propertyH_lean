import PropertyH.CoarseEmbeddings
import PropertyH.CoarseGrowth
import PropertyH.CoarseTruncation
import PropertyH.PoincareScalar

noncomputable section
namespace PropertyH
open Filter
open scoped Topology

/-- Revised normalization lemma: zero mean, unit-ball range, vanishing global
Lipschitz constants, and average norms converging to one. -/
theorem exists_coarse_normalization (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    (hemb : EquiCoarseGraphEmbeddings E X) :
    ∃ (ψ : ∀ n, E.V n → X n) (K : ℕ → ℝ),
      Tendsto K atTop (𝓝 0) ∧ (∀ n, 0 ≤ K n) ∧
      (∀ n, ∑ v, ψ n v = 0) ∧ (∀ n v, ‖ψ n v‖ ≤ 1) ∧
      (∀ n v u, ‖ψ n v - ψ n u‖ ≤ K n * (E.graph n).dist v u) ∧
      Tendsto (fun n => average (fun v => ‖ψ n v‖)) atTop (𝓝 1) := by
  classical
  obtain ⟨L, ρ, hL, hmono, hr0, hrinf, φ, hφ⟩ := hemb
  let f : ∀ n, E.V n → X n := fun n v => φ n v - average (φ n)
  have hdiff : ∀ n v u, f n v - f n u = φ n v - φ n u := by
    intros; dsimp [f]; abel
  have hf : ∀ n v u, ‖f n v - f n u‖ ≤ L * (E.graph n).dist v u := by
    intro n v u; rw [hdiff]; exact (hφ n v u).2
  let A : ℕ → ℝ := fun n => average (fun v => ‖f n v‖)
  have hA : ∀ n, 0 ≤ A n := by intro n; dsimp [A, average]; positivity
  have hAlim : Tendsto A atTop atTop :=
    coarse_average_norm_tendsto_atTop E X f ρ hmono hrinf
      (fun n v u => by rw [hdiff]; exact (hφ n v u).1)
  let C : ℝ := 1 + (2 * E.degreeBound / E.expansion) * L
  have hC : 0 < C := by
    have hh : 0 < E.expansion := (E.expands 0).1
    dsimp [C]; positivity
  let ψ : ∀ n, E.V n → X n := fun n => truncatedNormalization (f n) (A n) C
  let K : ℕ → ℝ := fun n => 2 * L / (A n + C)
  have hdata : ∀ n, Nonempty (E.V n) →
      (∑ v, ψ n v = 0) ∧ (∀ v, ‖ψ n v‖ ≤ 1) ∧
      (∀ v u, ‖ψ n v - ψ n u‖ ≤ K n * (E.graph n).dist v u) ∧
      (A n - 2 * C) / (A n + C) ≤ average (fun v => ‖ψ n v‖) := by
    intro n hn
    let : Nonempty (E.V n) := hn
    have hz : ∑ v, f n v = 0 := by
      simp [f, Finset.sum_sub_distrib, average, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul, Fintype.card_ne_zero]
    have hdev : average (fun v => |‖f n v‖ - A n|) ≤ C := by
      have hp := (E.expands n).scalar_poincare (fun v => ‖f n v‖) L hL.le
        (fun v u => (abs_norm_sub_norm_le (f n v) (f n u)).trans (hf n v u))
      have hp' : average (fun v => |‖f n v‖ - A n|) ≤
          (2 * E.degreeBound / E.expansion) * L := hp
      exact hp'.trans (by dsimp [C]; linarith)
    obtain ⟨hz', hb, hd, havg⟩ := truncatedNormalization_bounds (f n) (A n) C rfl hz hdev hC
    refine ⟨hz', hb, ?_, havg⟩
    intro v u
    have ht := (hd v u).trans (mul_le_mul_of_nonneg_left (hf n v u)
      (div_nonneg (by norm_num) (by linarith [hA n])))
    simpa [K, mul_div_assoc, div_mul_eq_mul_div, mul_assoc] using ht
  have hAC : ∀ n, 0 < A n + C := fun n => by linarith [hA n]
  have hAClim : Tendsto (fun n => A n + C) atTop atTop := by
    apply tendsto_atTop_mono (fun n => le_add_of_nonneg_right hC.le) hAlim
  have hKlim : Tendsto K atTop (𝓝 0) := by
    simpa [K, div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hAClim).const_mul (2 * L)
  refine ⟨ψ, K, hKlim, (fun n => div_nonneg (by positivity) (hAC n).le), ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : Nonempty (E.V n)
    · exact (hdata n hn).1
    · let : IsEmpty (E.V n) := not_nonempty_iff.mp hn
      simp
  · intro n v
    exact (hdata n ⟨v⟩).2.1 v
  · intro n v u
    exact (hdata n ⟨v⟩).2.2.1 v u
  · have hlowlim : Tendsto (fun n => (A n - 2 * C) / (A n + C)) atTop (𝓝 1) := by
      have he : (fun n => (A n - 2 * C) / (A n + C)) =
          (fun n => 1 - (3 * C) * (A n + C)⁻¹) := by
        funext n
        field_simp [(hAC n).ne']
        ring
      rw [he]
      simpa using tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.comp hAClim).const_mul (3 * C))
    have hlarge : ∀ᶠ n in atTop, 1 ≤ Fintype.card (E.V n) :=
      E.grows.eventually (eventually_ge_atTop 1)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim tendsto_const_nhds
    · filter_upwards [hlarge] with n hn
      exact (hdata n (Fintype.card_pos_iff.mp hn)).2.2.2
    · filter_upwards [hlarge] with n hn
      let : Nonempty (E.V n) := Fintype.card_pos_iff.mp hn
      have hh := trunc_average_mono (fun v => (hdata n inferInstance).2.1 v)
      simpa [average, Fintype.card_ne_zero] using hh
/-- Compatibility interface for the common null-homotopy argument. -/
theorem exists_normalized_coarse_expander_embeddings (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    (hemb : EquiCoarseGraphEmbeddings E X) :
    ∃ (ψ : ∀ n, E.V n → X n) (K : ℕ → ℝ) (a : ℝ), 0 < a ∧
      Tendsto K atTop (𝓝 0) ∧ (∀ n, 0 ≤ K n) ∧ ∀ᶠ n in atTop,
        Nonempty (E.V n) ∧ (∑ v, ψ n v = 0) ∧ (∀ v, ‖ψ n v‖ ≤ 1) ∧
        (∀ v u, (E.graph n).Adj v u → ‖ψ n v - ψ n u‖ ≤ K n) ∧
        a ≤ average (fun v => ‖ψ n v‖) := by
  obtain ⟨ψ, K, hK, hK0, hzero, hnorm, hLip, hmean⟩ := exists_coarse_normalization E X hemb
  refine ⟨ψ, K, 1 / 2, by norm_num, hK, hK0, ?_⟩
  have hlarge := E.grows.eventually (eventually_ge_atTop 1)
  have hmean' : ∀ᶠ n in atTop, (1 : ℝ) / 2 < average (fun v => ‖ψ n v‖) :=
    (tendsto_order.mp hmean).1 _ (by norm_num)
  filter_upwards [hlarge, hmean'] with n hn hm
  refine ⟨Fintype.card_pos_iff.mp hn, hzero n, hnorm n, ?_, hm.le⟩
  intro v u hadj
  simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, Nat.cast_one, mul_one] using hLip n v u
end PropertyH

