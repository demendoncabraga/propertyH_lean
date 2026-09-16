import PropertyH.PoincareL1

/-! The manuscript’s L₁ Poincaré estimate, proved from vertex expansion. -/
noncomputable section
namespace PropertyH
open MeasureTheory

/-- Source: PIII, the `L_1`-valued Poincare inequality.
The nonnegative `L` is any Lipschitz bound; this avoids assuming that an optimal
Lipschitz constant has already been constructed.
Proof plan: scalar cut/level-set inequality from expansion, then integrate in L1. -/
theorem expander_poincare {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h) (hV : 5 ≤ Fintype.card V)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : V → Lp ℝ 1 μ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ v u, ‖f v - f u‖ ≤ L * G.dist v u) :
    (Fintype.card V : ℝ)⁻¹ *
      (∑ v, ‖f v - (Fintype.card V : ℝ)⁻¹ • ∑ u, f u‖) ≤ (2 * k / h) * L := by
  exact expander_poincare_proved G k h hG hV μ f L hL hf

end PropertyH
