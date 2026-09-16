import PropertyH.Basic

noncomputable section
namespace PropertyH
open Filter
open scoped Topology

variable {X Y : ℕ → Type*} [∀ n, PseudoMetricSpace (X n)] [∀ n, PseudoMetricSpace (Y n)]

/-- The canonical common modulus, extended by zero at negative arguments. -/
def commonModulus (f : ∀ n, X n → Y n) (t : ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ n x y, dist x y ≤ t ∧ r = dist (f n x) (f n y)})

lemma commonModulus_bddAbove (f : ∀ n, X n → Y n) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ M) (t : ℝ) :
    BddAbove (insert 0 {r : ℝ | ∃ n x y, dist x y ≤ t ∧ r = dist (f n x) (f n y)}) := by
  refine ⟨M, ?_⟩
  rintro r (rfl | ⟨n, x, y, _, rfl⟩)
  · exact hM
  · exact hbound n x y

lemma commonModulus_nonneg (f : ∀ n, X n → Y n) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ M) (t : ℝ) :
    0 ≤ commonModulus f t :=
  le_csSup (commonModulus_bddAbove f hM hbound t) (Set.mem_insert 0 _)

lemma commonModulus_controls_dist (f : ∀ n, X n → Y n) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ M) (n : ℕ) (x y : X n) :
    dist (f n x) (f n y) ≤ commonModulus f (dist x y) :=
  le_csSup (commonModulus_bddAbove f hM hbound _) (Or.inr ⟨n, x, y, le_rfl, rfl⟩)

lemma commonModulus_monotone (f : ∀ n, X n → Y n) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ M) : Monotone (commonModulus f) := by
  intro s t hst
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨n, x, y, hxy, rfl⟩)
  · exact commonModulus_nonneg f hM hbound t
  · exact le_csSup (commonModulus_bddAbove f hM hbound t)
      (Or.inr ⟨n, x, y, hxy.trans hst, rfl⟩)

lemma commonModulus_tendsto_zero (f : ∀ n, X n → Y n) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ M) (hf : EquiUniformContinuous f) :
    Tendsto (commonModulus f) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := hf (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have htδ : t < δ := lt_of_le_of_lt (le_abs_self t) (by simpa using ht)
  have hω : commonModulus f t ≤ ε / 2 := by
    apply csSup_le (Set.insert_nonempty _ _)
    rintro r (rfl | ⟨n, x, y, hxy, rfl⟩)
    · positivity
    · exact (hmod n x y (hxy.trans_lt htδ)).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (commonModulus_nonneg f hM hbound t)]
  linarith

lemma commonModulus_zero (f : ∀ n, X n → Y n) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ M) (hf : EquiUniformContinuous f) :
    commonModulus f 0 = 0 := by
  apply le_antisymm _ (commonModulus_nonneg f hM hbound 0)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := hf ε hε
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨n, x, y, hxy, rfl⟩)
  · positivity
  · simpa only [zero_add] using (hmod n x y (hxy.trans_lt hδ)).le

/-- A bounded equi-uniformly continuous family has one monotone common modulus tending to zero. -/
theorem EquiUniformContinuous.exists_common_modulus {f : ∀ n, X n → Y n}
    (hf : EquiUniformContinuous f) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n x y, dist (f n x) (f n y) ≤ M) :
    ∃ ω : ℝ → ℝ, Monotone ω ∧ (∀ t, 0 ≤ ω t) ∧ ω 0 = 0 ∧
      Tendsto ω (𝓝 0) (𝓝 0) ∧ ∀ n x y, dist (f n x) (f n y) ≤ ω (dist x y) := by
  exact ⟨commonModulus f, commonModulus_monotone f hM hbound,
    commonModulus_nonneg f hM hbound, commonModulus_zero f hM hbound hf,
    commonModulus_tendsto_zero f hM hbound hf, commonModulus_controls_dist f hM hbound⟩

end PropertyH
