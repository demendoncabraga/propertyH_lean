import PropertyH.CoarseMain
import PropertyH.ExpanderExistence
import PropertyH.GraphMetricSpace

noncomputable section
namespace PropertyH

/-- Source: `Cor.Prop.H`, uniform distortion containment of the finite sup spaces.
The maps need not be linear. A single bound works for all dimensions, after
rescaling each embedding into the normed target. -/
def UniformlyContainsFiniteSup (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ L : ℝ, 1 ≤ L ∧ ∀ n : ℕ, ∃ f : (Fin n → ℝ) → X, ∀ v w,
    ‖v - w‖ / L ≤ ‖f v - f w‖ ∧ ‖f v - f w‖ ≤ L * ‖v - w‖

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
/-- Finite metric distance coordinates transfer uniform sup-space embeddings. -/
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

theorem not_hasPropertyH_of_uniformlyContainsFiniteMetrics
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : UniformlyContainsFiniteMetrics X) : ¬ HasPropertyH X :=
  not_hasPropertyH_of_containsCoarseExpanders X
    ⟨PermutationExpanders.constructedExpanderFamily,
      (expander_embeddings_of_uniformlyContainsFiniteMetrics hX _).to_coarse⟩

/-- Uniformly containing finite sup spaces suffices to contain every finite metric. -/
theorem uniformlyContainsFiniteMetrics_of_uniformlyContainsFiniteSup
    {X : Type*} [NormedAddCommGroup X] (hX : UniformlyContainsFiniteSup X) :
    UniformlyContainsFiniteMetrics X := by
  exact uniformlyContainsFiniteMetrics_of_sup_embeddings hX.choose hX.choose_spec.1
    hX.choose_spec.2

/-- Source: revised `Cor.Prop.H`, second assertion. No external theorem is needed. -/
theorem not_hasPropertyH_of_uniformlyContainsFiniteSup
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : UniformlyContainsFiniteSup X) : ¬ HasPropertyH X := by
  exact not_hasPropertyH_of_uniformlyContainsFiniteMetrics
    (uniformlyContainsFiniteMetrics_of_uniformlyContainsFiniteSup hX)

/-- Source: `Cor.Prop.H`, the parenthetical c₀ example, by zero extension. -/
theorem uniformlyContainsFiniteSup_cZero : UniformlyContainsFiniteSup CZero := by
  refine ⟨1, le_rfl, fun n => ⟨finiteToCZero n, fun v w => ?_⟩⟩
  simp [← dist_eq_norm, (finiteToCZero_isometry n).dist_eq]

end PropertyH

