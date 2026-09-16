import PropertyH.PoincareL1
import PropertyH.DiameterBound
import PropertyH.PairwiseDistances

/-! Expander estimates PI, PII, PIII. All three estimates are proved from the vertex-expansion definition. -/
noncomputable section
namespace PropertyH
open MeasureTheory

/-- Source: PI, `$\operatorname{diam}(V)\le 2\log(|V|)/\log(1+h/k)$`.
Proof plan: use expansion to grow metric balls until two balls intersect. -/
theorem expander_diameter_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h) (hV : 5 ≤ Fintype.card V) :
    (graphDiameter G : ℝ) ≤ (2 / Real.log (1 + h / k)) * Real.log (Fintype.card V) := by
  exact expander_diameter_bound_proved G k h hG hV

/-- Source: PII,
`$\sum_{v,u\in V} d(v,u)\ge |V|^2\log_k(|V|/2-1)/2$`.
Proof plan: bounded degree limits the sizes of metric balls; at least half
of the ordered vertex pairs have distance at least the indicated threshold. -/
theorem expander_pairwise_distance_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h) (hV : 5 ≤ Fintype.card V) :
    (Fintype.card V : ℝ)^2 / 2 * Real.logb k ((Fintype.card V : ℝ) / 2 - 1) ≤
      ∑ v, ∑ u, ((G.dist v u : ℕ) : ℝ) := by
  exact expander_pairwise_distance_bound_proved G k h hG hV

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
