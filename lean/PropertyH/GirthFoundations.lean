import PropertyH.ExpanderEstimates
import Mathlib.Combinatorics.SimpleGraph.Girth

noncomputable section
namespace PropertyH

/-- Distinct paths between the same endpoints force a cycle no longer than their combined length. -/
theorem egirth_le_length_add_of_distinct_paths {V : Type*} {G : SimpleGraph V}
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath) (hne : p ≠ q) :
    G.egirth ≤ ((p.length + q.length : ℕ) : ℕ∞) := by
  obtain ⟨u', v', p', q', hpp, hqq, hcycle⟩ := hp.exists_isCycle_of_ne hq hne
  have hlen : (p'.append q'.reverse).length ≤ p.length + q.length := by
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    exact Nat.add_le_add (SimpleGraph.Walk.length_le_of_isSubwalk hpp)
      (SimpleGraph.Walk.length_le_of_isSubwalk hqq)
  exact (SimpleGraph.egirth_le_length hcycle).trans (by exact_mod_cast hlen)

/-- Below the girth threshold, paths with common endpoints are unique. -/
theorem paths_eq_of_length_add_lt_egirth {V : Type*} {G : SimpleGraph V}
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hshort : ((p.length + q.length : ℕ) : ℕ∞) < G.egirth) : p = q := by
  by_contra hne
  exact (not_le_of_gt hshort) (egirth_le_length_add_of_distinct_paths hp hq hne)

/-- A path shorter than half the extended girth is a shortest path. -/
theorem short_path_is_geodesic {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hshort : ((2 * p.length : ℕ) : ℕ∞) < G.egirth) : p.length = G.dist u v := by
  obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
  have hql : q.length ≤ p.length := hq.trans_le (SimpleGraph.dist_le p)
  have hsum : ((p.length + q.length : ℕ) : ℕ∞) < G.egirth :=
    lt_of_le_of_lt (by exact_mod_cast (show p.length + q.length ≤ 2*p.length by omega)) hshort
  have heq := paths_eq_of_length_add_lt_egirth hp (q.isPath_of_length_eq_dist hq) hsum
  exact heq ▸ hq

/-- Short paths are uniquely geodesic, the local uniqueness input for tree-ball arguments. -/
theorem short_geodesic_unique {V : Type*} {G : SimpleGraph V}
    {u v : V} {p q : G.Walk u v} (hp : p.length = G.dist u v) (hq : q.length = G.dist u v)
    (hshort : ((2 * G.dist u v : ℕ) : ℕ∞) < G.egirth) : p = q := by
  apply paths_eq_of_length_add_lt_egirth (p.isPath_of_length_eq_dist hp) (q.isPath_of_length_eq_dist hq)
  simpa only [hp, hq, two_mul] using hshort

/-- Logarithmic girth plus expansion implies Osajda's bounded diameter/girth ratio. -/
theorem diameter_le_mul_girth_of_log_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (h : ℝ) (hex : IsVertexExpander G k h)
    (hV : 5 ≤ Fintype.card V) (C : ℝ)
    (hgirth : Real.log (Fintype.card V) ≤ C * (G.girth : ℝ)) :
    (graphDiameter G : ℝ) ≤ ((2 / Real.log (1+h/k)) * C) * G.girth := by
  have hk : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by have := hex.two_le_degreeBound hV; omega)
  have hlog : 0 < Real.log (1+h/k) := Real.log_pos (by have := div_pos hex.1 hk; linarith)
  exact (expander_diameter_bound G k h hex hV).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgirth (by positivity : 0 ≤ 2 / Real.log (1+h/k)))
end PropertyH
