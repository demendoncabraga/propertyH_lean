import PropertyH.UniversalFinite

noncomputable section
open scoped BigOperators
namespace PropertyH

/-! Legacy cotype definitions, retained for the independent c₀ cotype proof.
The current manuscript uses uniform finite sup-space containment instead. -/

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

end PropertyH
