import PropertyH.NormalizedFamily

noncomputable section
namespace PropertyH
open Filter
open scoped Topology

/-- Source: the additive-error version of the image diameter upper estimate. -/
theorem imageDiameter_le_graphDiameter_add {V X : Type*} [Fintype V]
    [NormedAddCommGroup X] (φ : V → X) (G : SimpleGraph V)
    (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hφ : ∀ i j, ‖φ i - φ j‖ ≤ L * G.dist i j + A) :
    imageDiameter φ ≤ L * graphDiameter G + A := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  have hg : G.dist i j ≤ graphDiameter G :=
    (Finset.le_sup (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun v => Finset.univ.sup (G.dist v)) (Finset.mem_univ i))
  simpa [dist_eq_norm] using (hφ i j).trans
    (add_le_add (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hg) hL) (le_refl A))

/-- Subtracting a constant before averaging subtracts that same constant from the result. -/
theorem average_pairwise_sub_const {V : Type*} [Fintype V] [Nonempty V]
    (q : V → V → ℝ) (b : ℝ) :
    average (fun i => average (fun j => q i j - b)) =
      average (fun i => average (q i)) - b := by
  simp [average, Finset.sum_sub_distrib, mul_sub, Fintype.card_ne_zero]

/-- Source: a quasi-isometric expander embedding, retaining its additive error. -/
def EquiQuasiGraphEmbeddings (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] : Prop :=
  ∃ L A : ℝ, 1 ≤ L ∧ 0 ≤ A ∧ ∃ φ : ∀ n, E.V n → X n,
    ∀ n v u, (E.graph n).dist v u / L - A ≤ ‖φ n v - φ n u‖ ∧
      ‖φ n v - φ n u‖ ≤ L * (E.graph n).dist v u + A

/-- Source: normalization for the quasi-isometric group corollary; additive errors vanish. -/
theorem exists_normalized_expander_quasi_embeddings (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    (hemb : EquiQuasiGraphEmbeddings E X) :
    ∃ (ψ : ∀ n, E.V n → X n) (K : ℕ → ℝ) (a : ℝ), 0 < a ∧
      Tendsto K atTop (𝓝 0) ∧ (∀ n, 0 ≤ K n) ∧ ∀ᶠ n in atTop,
        Nonempty (E.V n) ∧ (∑ v, ψ n v = 0) ∧ (∀ v, ‖ψ n v‖ ≤ 1) ∧
        (∀ v u, (E.graph n).Adj v u → ‖ψ n v - ψ n u‖ ≤ K n) ∧
        a ≤ average (fun v => ‖ψ n v‖) := by
  obtain ⟨L, B, hL1, hB, φ, hφ⟩ := hemb
  have hL : 0 < L := by linarith
  have hlarge : ∀ᶠ n in atTop, 16 ≤ Fintype.card (E.V n) :=
    E.grows.eventually (eventually_ge_atTop 16)
  obtain ⟨n₀, hn₀⟩ := hlarge.exists
  have hk : 1 < (E.degreeBound : ℝ) := by
    exact_mod_cast ((E.expands n₀).two_le_degreeBound (by omega : 5 ≤ Fintype.card (E.V n₀)))
  let A : ℝ := 1 / (4 * Real.log E.degreeBound)
  have hA : 0 < A := one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hk))
  let C₀ : ℝ := L * (2 / Real.log (1 + E.expansion / E.degreeBound))
  have hC₀ : 0 < C₀ := by
    have hh := (E.expands 0).1
    have hlog : 0 < Real.log (1 + E.expansion / E.degreeBound) :=
      Real.log_pos (by have := div_pos hh (by linarith : (0 : ℝ) < E.degreeBound); linarith)
    dsimp [C₀]
    positivity
  let C := C₀ + B
  have hC : 0 < C := by dsimp [C]; linarith
  have hq : ∀ n v u, ((E.graph n).dist v u : ℝ) - L * B ≤ L * ‖φ n v - φ n u‖ := by
    intro n v u
    have hb := (div_le_iff₀ hL).mp
      (show ((E.graph n).dist v u : ℝ) / L ≤ ‖φ n v - φ n u‖ + B by linarith [(hφ n v u).1])
    nlinarith
  have hdata : ∀ n, 16 ≤ Fintype.card (E.V n) →
      A * Real.log (Fintype.card (E.V n)) - L * B ≤
        average (fun v => average (fun u => ((E.graph n).dist v u : ℝ) - L * B)) ∧
      imageDiameter (φ n) ≤ C₀ * Real.log (Fintype.card (E.V n)) + B ∧
      (A * Real.log (Fintype.card (E.V n)) - L * B) / L ≤ imageDiameter (φ n) := by
    intro n hn
    let : Nonempty (E.V n) := Fintype.card_pos_iff.mp (by omega)
    have havg : A * Real.log (Fintype.card (E.V n)) - L * B ≤
        average (fun v => average (fun u => ((E.graph n).dist v u : ℝ) - L * B)) := by
      rw [average_pairwise_sub_const]
      exact sub_le_sub_right (expander_average_distance_log_lower (E.graph n)
        E.degreeBound E.expansion (E.expands n) hn) (L * B)
    have hupper : imageDiameter (φ n) ≤ C₀ * Real.log (Fintype.card (E.V n)) + B := by
      have hm := mul_le_mul_of_nonneg_left
        (expander_diameter_bound (E.graph n) E.degreeBound E.expansion (E.expands n) (by omega)) hL.le
      simpa [C₀, mul_assoc] using
        (imageDiameter_le_graphDiameter_add (φ n) (E.graph n) L B hL.le hB
          (fun v u => (hφ n v u).2)).trans (add_le_add hm (le_refl B))
    refine ⟨havg, hupper, (div_le_iff₀ hL).mpr ?_⟩
    apply havg.trans
    have hb := average_pairwise_le_const
      (fun v u => ((E.graph n).dist v u : ℝ) - L * B) (L * imageDiameter (φ n))
      (fun v u => (hq n v u).trans
        (mul_le_mul_of_nonneg_left (norm_sub_le_imageDiameter (φ n) v u) hL.le))
    simpa [mul_comm] using hb
  have hloglim : Tendsto (fun n => Real.log (Fintype.card (E.V n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp E.grows)
  have hlowlim : Tendsto (fun n => (A * Real.log (Fintype.card (E.V n)) - L * B) / L) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(hloglim.const_mul_atTop hA).eventually (eventually_ge_atTop (L * b + L * B))] with n hn
    apply (le_div_iff₀ hL).mpr
    nlinarith
  have hDlim : Tendsto (fun n => imageDiameter (φ n)) atTop atTop :=
    tendsto_atTop_mono' atTop (hlarge.mono (fun n hn => (hdata n hn).2.2)) hlowlim
  refine ⟨(fun n => normalizedEmbedding (φ n)), (fun n => (L + B) / imageDiameter (φ n)),
    (A / 2) / (2 * L * C), by positivity, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hDlim).const_mul (L + B)
  · intro n
    exact div_nonneg (by linarith) Metric.diam_nonneg
  · filter_upwards [hlarge, hDlim.eventually (eventually_gt_atTop 0),
      hloglim.eventually (eventually_ge_atTop 1),
      (hloglim.const_mul_atTop hA).eventually (eventually_ge_atTop (2 * L * B))]
      with n hn hD hlog1 hdom
    let : Nonempty (E.V n) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨havg, hupper, _⟩ := hdata n hn
    refine ⟨inferInstance, sum_normalizedEmbedding (φ n),
      norm_normalizedEmbedding_le_one (φ n) hD, ?_, ?_⟩
    · intro v u hadj
      rw [norm_normalizedEmbedding_sub (φ n) hD]
      have hp := (hφ n v u).2
      simpa [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left hp (le_of_lt (inv_pos.mpr hD))
    · apply normalized_average_lower_bound (φ n) hD
        (fun v u => ((E.graph n).dist v u : ℝ) - L * B) L C (A / 2)
        (Real.log (Fintype.card (E.V n))) hL hC (by linarith) (hq n)
      · nlinarith
      · dsimp [C]
        nlinarith
end PropertyH

