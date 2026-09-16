import PropertyH.Corollaries
import PropertyH.GraphMetricSpace

noncomputable section
namespace PropertyH

/-- A uniform metric containment hypothesis, distinct from the definition of cotype. -/
def UniformlyContainsFiniteMetrics (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ L : ℝ, 1 ≤ L ∧ ∀ (V : Type) [Fintype V] [MetricSpace V],
    ∃ f : V → X, ∀ v w,
      dist v w / L ≤ ‖f v - f w‖ ∧ ‖f v - f w‖ ≤ L * dist v w

theorem expander_embeddings_of_uniformlyContainsFiniteMetrics
    {X : Type*} [NormedAddCommGroup X]
    (hX : UniformlyContainsFiniteMetrics X) (E : ExpanderFamily) :
    EquiGraphEmbeddings E (fun _ => X) := by
  obtain ⟨L, hL, h⟩ := hX
  have hf : ∀ n, ∃ f : E.V n → X, ∀ v w,
      ((E.graph n).dist v w : ℝ) / L ≤ ‖f v - f w‖ ∧
      ‖f v - f w‖ ≤ L * ((E.graph n).dist v w : ℝ) := by
    intro n
    cases isEmpty_or_nonempty (E.V n) with
    | inl he => exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩
    | inr hn =>
      let := graphMetricSpace (E.graph n) (E.expands n).connected
      exact h (E.V n)
  choose f hf using hf
  exact ⟨L, hL, f, hf⟩
/-- The elementary part after the finite representability theorem. -/
theorem uniformlyContainsFiniteMetrics_of_sup_embeddings
    {X : Type*} [NormedAddCommGroup X] (L : ℝ) (hL : 1 ≤ L)
    (h : ∀ n : ℕ, ∃ f : (Fin n → ℝ) → X, ∀ v w,
      ‖v - w‖ / L ≤ ‖f v - f w‖ ∧ ‖f v - f w‖ ≤ L * ‖v - w‖) :
    UniformlyContainsFiniteMetrics X := by
  refine ⟨L, hL, ?_⟩
  intro V _ _
  obtain ⟨f, hf⟩ := h (Fintype.card V)
  refine ⟨fun v => f (finiteDistanceCoordinates v), fun v w => ?_⟩
  simpa only [← dist_eq_norm, finiteDistanceCoordinates_isometry.dist_eq] using
    hf (finiteDistanceCoordinates v) (finiteDistanceCoordinates w)

theorem containsExpanders_of_uniformlyContainsFiniteMetrics
    {X : Type*} [NormedAddCommGroup X]
    (hX : UniformlyContainsFiniteMetrics X) : ContainsExpanders X :=
  ⟨PermutationExpanders.constructedExpanderFamily,
    expander_embeddings_of_uniformlyContainsFiniteMetrics hX _⟩

theorem not_hasPropertyH_of_uniformlyContainsFiniteMetrics
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : UniformlyContainsFiniteMetrics X) : ¬ HasPropertyH X :=
  not_hasPropertyH_of_containsExpanders X
    (containsExpanders_of_uniformlyContainsFiniteMetrics hX)

end PropertyH

