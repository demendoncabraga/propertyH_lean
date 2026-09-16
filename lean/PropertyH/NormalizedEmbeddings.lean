import PropertyH.Expanders
import PropertyH.ExpanderEstimates
import PropertyH.Averages

noncomputable section
namespace PropertyH
variable {I X : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Source: `diam(φ_n(V_n))` in the normalization formula. -/
def imageDiameter (φ : I → X) : ℝ := Metric.diam (Set.range φ)

/-- Source: `ψ_n(v)=(φ_n(v)-average φ_n)/diam(φ_n(V_n))`. -/
def normalizedEmbedding (φ : I → X) (i : I) : X :=
  (imageDiameter φ)⁻¹ • (φ i - average φ)

/-- Source: the normalized embeddings have zero sum. -/
theorem sum_normalizedEmbedding (φ : I → X) : ∑ i, normalizedEmbedding φ i = 0 := by
  simp [normalizedEmbedding, ← Finset.smul_sum, Finset.sum_sub_distrib,
    average, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Fintype.card_ne_zero]

omit [Nonempty I] [NormedSpace ℝ X] in
/-- Source: all pairwise image distances are bounded by the image diameter. -/
theorem norm_sub_le_imageDiameter (φ : I → X) (i j : I) :
    ‖φ i - φ j‖ ≤ imageDiameter φ := by
  simpa [dist_eq_norm, imageDiameter] using Metric.dist_le_diam_of_mem (Set.finite_range φ).isBounded
    (Set.mem_range_self i) (Set.mem_range_self j)

/-- Source: the centered image lies in the ball of radius `diam(φ(V))`. -/
theorem norm_sub_average_le_imageDiameter (φ : I → X) (i : I) :
    ‖φ i - average φ‖ ≤ imageDiameter φ := by
  have ha := norm_average_le_average_norm (fun j => φ i - φ j)
  have hc : average (fun j => φ i - φ j) = φ i - average φ := by
    simp [average, Finset.sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, Fintype.card_ne_zero]
  have hb : average (fun j => ‖φ i - φ j‖) ≤ imageDiameter φ := by
    simpa [average, Fintype.card_ne_zero] using
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => norm_sub_le_imageDiameter φ i j))
        (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)
  exact hc ▸ ha.trans hb

/-- Source: each `ψ_n` has image in the unit ball. -/
theorem norm_normalizedEmbedding_le_one (φ : I → X) (hD : 0 < imageDiameter φ) (i : I) :
    ‖normalizedEmbedding φ i‖ ≤ 1 := by
  simpa [normalizedEmbedding, norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hD)), hD.ne'] using
    mul_le_mul_of_nonneg_left (norm_sub_average_le_imageDiameter φ i)
      (le_of_lt (inv_pos.mpr hD))

omit [Nonempty I] in
/-- Source: centering does not affect differences and normalization scales their norms. -/
theorem norm_normalizedEmbedding_sub (φ : I → X) (hD : 0 < imageDiameter φ) (i j : I) :
    ‖normalizedEmbedding φ i - normalizedEmbedding φ j‖ =
      (imageDiameter φ)⁻¹ * ‖φ i - φ j‖ := by
  simp [normalizedEmbedding, ← smul_sub, norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hD))]

/-- Source: the first inequality of `Eq.psi.lowe.bound.sum`, before normalization. -/
theorem average_pairwise_le_normalized_average (φ : I → X) (hD : 0 < imageDiameter φ) :
    average (fun i => average (fun j => ‖φ i - φ j‖)) ≤
      2 * imageDiameter φ * average (fun i => ‖normalizedEmbedding φ i‖) := by
  have hp := average_pairwise_norm_le_two_average_norm (normalizedEmbedding φ)
  have he : average (fun i => average (fun j => ‖normalizedEmbedding φ i - normalizedEmbedding φ j‖)) =
      (imageDiameter φ)⁻¹ * average (fun i => average (fun j => ‖φ i - φ j‖)) := by
    simp [norm_normalizedEmbedding_sub φ hD, average, ← Finset.mul_sum, mul_left_comm]
  simpa [he, ← mul_assoc, hD.ne', mul_comm (imageDiameter φ) 2] using
    mul_le_mul_of_nonneg_left hp hD.le

/-- Source: the average graph-distance lower bound transfers through normalization. -/
theorem average_pairwise_lower_le_normalized (φ : I → X) (hD : 0 < imageDiameter φ)
    (q : I → I → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hq : ∀ i j, q i j ≤ L * ‖φ i - φ j‖) :
    average (fun i => average (q i)) ≤
      2 * L * imageDiameter φ * average (fun i => ‖normalizedEmbedding φ i‖) := by
  have hs : (∑ i, ∑ j, q i j) ≤ ∑ i, ∑ j, L * ‖φ i - φ j‖ :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hq i j))
  have ha : average (fun i => average (q i)) ≤
      L * average (fun i => average (fun j => ‖φ i - φ j‖)) := by
    simpa [average, ← Finset.mul_sum, mul_left_comm] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs
        (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity))
        (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)
  exact ha.trans (by simpa [mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left (average_pairwise_le_normalized_average φ hD) hL)

/-- Source: `Eq.psi.lowe.bound.sum`; the logarithmic scale cancels from the estimates. -/
theorem normalized_average_lower_bound (φ : I → X) (hD : 0 < imageDiameter φ)
    (q : I → I → ℝ) (L C a T : ℝ) (hL : 0 < L) (hC : 0 < C) (hT : 0 < T)
    (hq : ∀ i j, q i j ≤ L * ‖φ i - φ j‖)
    (havg : a * T ≤ average (fun i => average (q i)))
    (hdiam : imageDiameter φ ≤ C * T) :
    a / (2 * L * C) ≤ average (fun i => ‖normalizedEmbedding φ i‖) := by
  have hn : 0 ≤ average (fun i => ‖normalizedEmbedding φ i‖) := by
    unfold average
    positivity
  have hbase := havg.trans (average_pairwise_lower_le_normalized φ hD q L hL.le hq)
  have hb : 2 * L * imageDiameter φ * average (fun i => ‖normalizedEmbedding φ i‖) ≤
      2 * L * (C * T) * average (fun i => ‖normalizedEmbedding φ i‖) := by
    gcongr
  apply (div_le_iff₀ (show 0 < 2 * L * C by positivity)).mpr
  nlinarith [hbase.trans hb]

omit [Nonempty I] [NormedSpace ℝ X] in
/-- Source: the upper Lipschitz estimate bounds the image diameter. -/
theorem imageDiameter_le_graphDiameter (φ : I → X) (G : SimpleGraph I)
    (L : ℝ) (hL : 0 ≤ L) (hφ : ∀ i j, ‖φ i - φ j‖ ≤ L * G.dist i j) :
    imageDiameter φ ≤ L * graphDiameter G := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  have hg : G.dist i j ≤ graphDiameter G :=
    (Finset.le_sup (Finset.mem_univ j)).trans (Finset.le_sup (f := fun v => Finset.univ.sup (G.dist v)) (Finset.mem_univ i))
  simpa [dist_eq_norm] using (hφ i j).trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hg) hL)

omit [Nonempty I] [NormedSpace ℝ X] in
/-- Source: the lower embedding estimate guarantees a positive normalization denominator. -/
theorem imageDiameter_pos_of_graph_embedding [Nontrivial I]
    (φ : I → X) (G : SimpleGraph I) (hG : G.Connected)
    (L : ℝ) (hL : 0 < L) (hφ : ∀ i j, (G.dist i j : ℝ) / L ≤ ‖φ i - φ j‖) :
    0 < imageDiameter φ := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  exact (div_pos (Nat.cast_pos.mpr (hG.pos_dist_of_ne hij)) hL).trans_le
    ((hφ i j).trans (norm_sub_le_imageDiameter φ i j))

omit [Nonempty I] in
/-- Source: the Lipschitz constants of `ψ_n` are at most `L/diam(φ_n(V_n))`. -/
theorem normalizedEmbedding_edge_bound (φ : I → X) (G : SimpleGraph I)
    (hD : 0 < imageDiameter φ) (L : ℝ)
    (hφ : ∀ i j, ‖φ i - φ j‖ ≤ L * G.dist i j) (i j : I) (hij : G.Adj i j) :
    ‖normalizedEmbedding φ i - normalizedEmbedding φ j‖ ≤ L / imageDiameter φ := by
  rw [norm_normalizedEmbedding_sub φ hD]
  have h := hφ i j
  simpa [SimpleGraph.dist_eq_one_iff_adj.mpr hij, div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hD))
end PropertyH

