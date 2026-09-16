import PropertyH.UniversalFinite

noncomputable section
open scoped BigOperators
namespace PropertyH

/-- Finite Rademacher cotype, using the uniform second moment over all sign vectors.
The exponent `q` is real and finite; the condition `2 ≤ q` is part of the definition. -/
def HasRademacherCotype (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℝ) : Prop :=
  2 ≤ q ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → X),
    (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤
      C * Real.sqrt ((2 : ℝ) ^ n)⁻¹ *
        Real.sqrt (∑ ε : Fin n → Bool,
          ‖∑ i, (if ε i then (1 : ℝ) else -1) • x i‖ ^ 2)

/-- Trivial cotype means the absence of every finite Rademacher cotype.
It is not defined through containment of finite metric spaces. -/
def HasTrivialCotype (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ q : ℝ, 2 ≤ q → ¬ HasRademacherCotype X q

/-- Explicit external hypothesis authorized by the user: the Maurey–Pisier
finite-representability implication, for the ambient Banach space X.
No axiom or proof placeholder is introduced. -/
def MaureyPisierFiniteRepresentability (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  HasTrivialCotype X → ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
    ∃ T : (Fin n → ℝ) →ₗ[ℝ] X, ∀ v,
      ‖v‖ ≤ ‖T v‖ ∧ ‖T v‖ ≤ (1 + ε) * ‖v‖

/-- Use of the explicitly supplied Maurey–Pisier hypothesis. -/
theorem maureyPisier_finite_sup_representability
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hMP : MaureyPisierFiniteRepresentability X)
    (hX : HasTrivialCotype X) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    ∃ T : (Fin n → ℝ) →ₗ[ℝ] X, ∀ v,
      ‖v‖ ≤ ‖T v‖ ∧ ‖T v‖ ≤ (1 + ε) * ‖v‖ := hMP hX ε hε n

/-- Verified conditional deduction from the explicit Maurey–Pisier hypothesis. -/
theorem uniformlyContainsFiniteMetrics_of_hasTrivialCotype
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hMP : MaureyPisierFiniteRepresentability X) (hX : HasTrivialCotype X) : UniformlyContainsFiniteMetrics X := by
  apply uniformlyContainsFiniteMetrics_of_sup_embeddings 2 (by norm_num)
  intro n
  obtain ⟨T, hT⟩ := maureyPisier_finite_sup_representability hMP hX 1 (by norm_num) n
  refine ⟨T, fun v w => ?_⟩
  have hh := hT (v - w)
  rw [map_sub] at hh
  constructor <;> nlinarith [norm_nonneg (v - w)]

/-- The expander-containment step; conditional on Maurey–Pisier. -/
theorem containsExpanders_of_hasTrivialCotype
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hMP : MaureyPisierFiniteRepresentability X) (hX : HasTrivialCotype X) : ContainsExpanders X :=
  containsExpanders_of_uniformlyContainsFiniteMetrics
    (uniformlyContainsFiniteMetrics_of_hasTrivialCotype hMP hX)

/-- Source: `Cor.Prop.H`, second assertion: no Banach space with trivial cotype
has Property (H). Conditional on the explicit Maurey–Pisier hypothesis above. -/
theorem not_hasPropertyH_of_hasTrivialCotype
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hMP : MaureyPisierFiniteRepresentability X) (hX : HasTrivialCotype X) : ¬ HasPropertyH X :=
  not_hasPropertyH_of_uniformlyContainsFiniteMetrics
    (uniformlyContainsFiniteMetrics_of_hasTrivialCotype hMP hX)

/-- Source: paragraph following Cor.Prop.H, arbitrary distortion close to one. -/
theorem finite_metrics_near_isometric_of_hasTrivialCotype
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hMP : MaureyPisierFiniteRepresentability X) (hX : HasTrivialCotype X)
    (ε : ℝ) (hε : 0 < ε) (V : Type*) [Fintype V] [MetricSpace V] :
    ∃ f : V → X, ∀ v w, dist v w ≤ ‖f v - f w‖ ∧
      ‖f v - f w‖ ≤ (1 + ε) * dist v w := by
  obtain ⟨T, hT⟩ := hMP hX ε hε (Fintype.card V)
  refine ⟨fun v => T (finiteDistanceCoordinates v), fun v w => ?_⟩
  simpa only [map_sub, ← dist_eq_norm, finiteDistanceCoordinates_isometry.dist_eq] using
    hT (finiteDistanceCoordinates v - finiteDistanceCoordinates w)

end PropertyH

