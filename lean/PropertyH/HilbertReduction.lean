import PropertyH.PropertyH

noncomputable section
namespace PropertyH
open TopologicalSpace

 theorem orthonormal_countable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [SeparableSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal ℝ v) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (1 / 2 : ℝ))
  · intro i j hij
    apply Metric.ball_disjoint_ball
    have h := (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (v i) (v j)).2
      (hv.2 hij)
    rw [hv.1 i, hv.1 j] at h
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  · exact fun _ => Metric.isOpen_ball
  · exact fun _ => Metric.nonempty_ball.mpr (by norm_num)

/-- Every separable real Hilbert space has a linear isometric embedding in ℓ₂(ℕ). -/
def separableHilbertEmbedding (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [SeparableSpace E] : E →ₗᵢ[ℝ] Hilbert := by
  classical
  let w := (exists_hilbertBasis ℝ E).choose
  let b := (exists_hilbertBasis ℝ E).choose_spec.choose
  letI : Countable w := orthonormal_countable b.orthonormal
  letI : Encodable w := Encodable.ofCountable w
  let c : HilbertBasis ℕ ℝ Hilbert := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ Hilbert)
  let h := c.orthonormal.comp (Encodable.encode : w → ℕ) Encodable.encode_injective
  exact h.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry

/-- The closed linear span of a separable subset is separable. -/
theorem separableSpace_closedSpan {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : IsSeparable s) :
    SeparableSpace (Submodule.span ℝ s).topologicalClosure := by
  apply IsSeparable.separableSpace
  simpa only [Submodule.topologicalClosure_coe] using hs.span.closure

/-- A continuous image of a separable domain lies in a separable closed subspace. -/
theorem separableSpace_closedSpan_range {X E : Type*} [TopologicalSpace X]
    [SeparableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} (hf : Continuous f) :
    SeparableSpace (Submodule.span ℝ (Set.range f)).topologicalClosure :=
  separableSpace_closedSpan (isSeparable_range hf)

/-- The closed span of countably many finite-dimensional paving stages is separable. -/
theorem separableSpace_closedSpan_paving {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : ℕ → Submodule ℝ E) [∀ n, FiniteDimensional ℝ (B n)] :
    SeparableSpace (Submodule.span ℝ (⋃ n, (B n : Set E))).topologicalClosure := by
  apply separableSpace_closedSpan
  apply IsSeparable.iUnion
  intro n
  exact isSeparable_range (B n).subtypeL.continuous |>.mono (by simp)

/-- Every paving stage is contained in the separable closed span of the paving. -/
theorem paving_le_closedSpan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℕ → Submodule ℝ E) (n : ℕ) :
    B n ≤ (Submodule.span ℝ (⋃ m, (B m : Set E))).topologicalClosure := by
  intro x hx
  exact Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_iUnion.mpr ⟨n, hx⟩))

/-- A Hilbert target can be replaced by ℓ₂ on the closed span of its paving. -/
def hilbertPavingEmbedding {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : ℕ → Submodule ℝ E) [∀ n, FiniteDimensional ℝ (B n)] :
    (Submodule.span ℝ (⋃ n, (B n : Set E))).topologicalClosure →ₗᵢ[ℝ] Hilbert := by
  letI := separableSpace_closedSpan_paving B
  exact separableHilbertEmbedding _

end PropertyH
