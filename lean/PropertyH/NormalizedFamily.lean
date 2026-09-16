import PropertyH.ExpanderEstimates
import PropertyH.NormalizedEmbeddings
noncomputable section
namespace PropertyH
open Filter
open scoped Topology

/-- Uniform logarithmic simplification of PII after discarding finitely many terms. -/
theorem log_half_sub_one_lower {N : ℝ} (hN : 16 ≤ N) :
    Real.log N / 2 ≤ Real.log (N / 2 - 1) := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hN
  have he : Real.log (16 : ℝ) = 2 * Real.log 4 := by
    simpa only [show (4 : ℝ)^2 = 16 by norm_num, Nat.cast_ofNat] using Real.log_pow (4 : ℝ) 2
  have hb := Real.log_le_log (by linarith : 0 < N / 4) (by linarith : N / 4 ≤ N / 2 - 1)
  rw [Real.log_div (by linarith : N ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)] at hb
  linarith

/-- Source: PII gives a lower bound proportional to the logarithm of the vertex count. -/
theorem expander_average_distance_log_lower {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h)
    (hV : 16 ≤ Fintype.card V) :
    (1 / (4 * Real.log k)) * Real.log (Fintype.card V) ≤
      average (fun v => average (fun u => (G.dist v u : ℝ))) := by
  have hk : 1 < (k : ℝ) := by exact_mod_cast (hG.two_le_degreeBound (by omega : 5 ≤ Fintype.card V))
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hpi := expander_pairwise_distance_bound G k h hG (by omega)
  have havg : Real.logb k ((Fintype.card V : ℝ) / 2 - 1) / 2 ≤
      average (fun v => average (fun u => (G.dist v u : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left hpi
      (show 0 ≤ (Fintype.card V : ℝ)⁻¹ * (Fintype.card V : ℝ)⁻¹ by positivity)
    convert! hm using 1
    · field_simp
    · simp [average, ← Finset.mul_sum, mul_assoc]
  apply le_trans ?_ havg
  have hlog := log_half_sub_one_lower (show (16 : ℝ) ≤ Fintype.card V by exact_mod_cast hV)
  have hm := div_le_div_of_nonneg_right hlog (Real.log_pos hk).le
  convert! div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 2) using 1
  · field_simp
    ring

/-- The average of a finite double family is bounded by any pointwise upper bound. -/
theorem average_pairwise_le_const {I : Type*} [Fintype I] [Nonempty I]
    (q : I → I → ℝ) (C : ℝ) (hq : ∀ i j, q i j ≤ C) :
    average (fun i => average (q i)) ≤ C := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hq i j))
  simpa [average, ← Finset.mul_sum, mul_assoc, Fintype.card_ne_zero] using
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs
      (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity))
      (show 0 ≤ (Fintype.card I : ℝ)⁻¹ by positivity)

/-- Source: all properties of the normalized graph embeddings used in `Thm.main`. -/
theorem exists_normalized_expander_embeddings (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    (hemb : EquiGraphEmbeddings E X) :
    ∃ (ψ : ∀ n, E.V n → X n) (K : ℕ → ℝ) (a : ℝ), 0 < a ∧
      Tendsto K atTop (𝓝 0) ∧ (∀ n, 0 ≤ K n) ∧ ∀ᶠ n in atTop,
        Nonempty (E.V n) ∧ (∑ v, ψ n v = 0) ∧ (∀ v, ‖ψ n v‖ ≤ 1) ∧
        (∀ v u, (E.graph n).Adj v u → ‖ψ n v - ψ n u‖ ≤ K n) ∧
        a ≤ average (fun v => ‖ψ n v‖) := by
  obtain ⟨L, hL1, φ, hφ⟩ := hemb
  have hL : 0 < L := by linarith
  have hlarge : ∀ᶠ n in atTop, 16 ≤ Fintype.card (E.V n) :=
    E.grows.eventually (eventually_ge_atTop 16)
  obtain ⟨n₀, hn₀⟩ := hlarge.exists
  have hk : 1 < (E.degreeBound : ℝ) := by
    exact_mod_cast ((E.expands n₀).two_le_degreeBound (by omega : 5 ≤ Fintype.card (E.V n₀)))
  let A : ℝ := 1 / (4 * Real.log E.degreeBound)
  have hA : 0 < A := one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hk))
  let C : ℝ := L * (2 / Real.log (1 + E.expansion / E.degreeBound))
  have hC : 0 < C := by
    have hh := (E.expands 0).1
    have hlog : 0 < Real.log (1 + E.expansion / E.degreeBound) :=
      Real.log_pos (by have := div_pos hh (by linarith : (0 : ℝ) < E.degreeBound); linarith)
    dsimp [C]
    positivity
  have hdata : ∀ n, 16 ≤ Fintype.card (E.V n) →
      0 < imageDiameter (φ n) ∧
      A * Real.log (Fintype.card (E.V n)) ≤
        average (fun v => average (fun u => ((E.graph n).dist v u : ℝ))) ∧
      imageDiameter (φ n) ≤ C * Real.log (Fintype.card (E.V n)) ∧
      A * Real.log (Fintype.card (E.V n)) / L ≤ imageDiameter (φ n) := by
    intro n hn
    let : Nonempty (E.V n) := Fintype.card_pos_iff.mp (by omega)
    let : Nontrivial (E.V n) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hD := imageDiameter_pos_of_graph_embedding (φ n) (E.graph n) (E.expands n).connected
      L hL (fun v u => (hφ n v u).1)
    have havg := expander_average_distance_log_lower (E.graph n) E.degreeBound E.expansion (E.expands n) hn
    have hupper : imageDiameter (φ n) ≤ C * Real.log (Fintype.card (E.V n)) := by
      have hm := mul_le_mul_of_nonneg_left
        (expander_diameter_bound (E.graph n) E.degreeBound E.expansion (E.expands n) (by omega)) hL.le
      simpa [C, mul_assoc] using
        (imageDiameter_le_graphDiameter (φ n) (E.graph n) L hL.le (fun v u => (hφ n v u).2)).trans hm
    refine ⟨hD, havg, hupper, (div_le_iff₀ hL).mpr ?_⟩
    apply havg.trans
    have hb := average_pairwise_le_const
      (fun v u => ((E.graph n).dist v u : ℝ)) (L * imageDiameter (φ n))
      (fun v u => ((div_le_iff₀ hL).mp (hφ n v u).1).trans
        (by simpa [mul_comm] using mul_le_mul_of_nonneg_left (norm_sub_le_imageDiameter (φ n) v u) hL.le))
    simpa [mul_comm] using hb
  have hloglim : Tendsto (fun n => Real.log (Fintype.card (E.V n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp E.grows)
  have hDlim : Tendsto (fun n => imageDiameter (φ n)) atTop atTop :=
    tendsto_atTop_mono' atTop (hlarge.mono (fun n hn => (hdata n hn).2.2.2))
      ((hloglim.const_mul_atTop hA).atTop_div_const hL)
  refine ⟨(fun n => normalizedEmbedding (φ n)), (fun n => L / imageDiameter (φ n)),
    A / (2 * L * C), by positivity, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hDlim).const_mul L
  · intro n
    exact div_nonneg hL.le Metric.diam_nonneg
  · filter_upwards [hlarge] with n hn
    let : Nonempty (E.V n) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨hD, havg, hupper, _⟩ := hdata n hn
    refine ⟨inferInstance, sum_normalizedEmbedding (φ n),
      norm_normalizedEmbedding_le_one (φ n) hD, ?_, ?_⟩
    · exact fun v u hadj => normalizedEmbedding_edge_bound (φ n) (E.graph n) hD L
        (fun v u => (hφ n v u).2) v u hadj
    · exact normalized_average_lower_bound (φ n) hD
        (fun v u => ((E.graph n).dist v u : ℝ)) L C A
        (Real.log (Fintype.card (E.V n))) hL hC
        (Real.log_pos (by exact_mod_cast (by omega : 1 < Fintype.card (E.V n))))
        (fun v u => by simpa [mul_comm] using (div_le_iff₀ hL).mp (hφ n v u).1)
        havg hupper
end PropertyH

