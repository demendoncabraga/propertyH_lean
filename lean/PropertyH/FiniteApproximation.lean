import PropertyH.Basic

namespace PropertyH

/-- A finite configuration can be approximated in a single stage of a dense increasing union. -/
theorem finite_approximation_in_submodule {X V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [Finite V] (A : ℕ → Submodule ℝ X) (hA : Monotone A)
    (hdense : Dense (⋃ n, (A n : Set X))) (φ : V → X) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, ∃ ψ : V → A m, ∀ v, dist (ψ v : X) (φ v) < ε := by
  classical
  let := Fintype.ofFinite V
  have happ : ∀ v, ∃ n, ∃ x : X, x ∈ A n ∧ dist x (φ v) < ε := by
    intro v
    obtain ⟨x, hx, hdist⟩ := hdense.exists_dist_lt (φ v) hε
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨n, x, hn, by simpa only [dist_comm] using hdist⟩
  choose n x hx hdist using happ
  let m := Finset.univ.sup n
  refine ⟨m, fun v => ⟨x v, ?_⟩, ?_⟩
  · exact hA (Finset.le_sup (Finset.mem_univ v)) (hx v)
  · exact hdist

/-- Moving each point by less than ε changes each pairwise distance by less than 2ε. -/
theorem pairwise_dist_perturbation {V X : Type*} [PseudoMetricSpace X]
    {φ ψ : V → X} {ε : ℝ} (hclose : ∀ v, dist (ψ v) (φ v) < ε) (v w : V) :
    |dist (ψ v) (ψ w) - dist (φ v) (φ w)| < 2 * ε := by
  have h := dist_dist_dist_le (ψ v) (ψ w) (φ v) (φ w)
  rw [Real.dist_eq] at h
  linarith [hclose v, hclose w]

/-- Additive error at most `1 / (2L)` preserves a biLipschitz bound with constant `2L`
on pairs whose original distance is at least one. -/
theorem bilipschitz_bounds_stable {d L a b : ℝ} (hL : 1 ≤ L) (hd : 1 ≤ d)
    (ha : d / L ≤ a ∧ a ≤ L * d) (herr : |b - a| ≤ 1 / (2 * L)) :
    d / (2 * L) ≤ b ∧ b ≤ (2 * L) * d := by
  have hLpos : 0 < L := by linarith
  have h2Lpos : 0 < 2 * L := by positivity
  obtain ⟨herrlo, herrhi⟩ := abs_le.mp herr
  have hlow : d ≤ a * L := (div_le_iff₀ hLpos).mp ha.1
  have herror : |b - a| * (2 * L) ≤ 1 := (le_div_iff₀ h2Lpos).mp herr
  have habslo := (neg_le_abs (b - a))
  have habshi := (le_abs_self (b - a))
  constructor
  · rw [div_le_iff₀ h2Lpos]
    nlinarith [mul_le_mul_of_nonneg_right habslo h2Lpos.le]
  · have hsmall : 1 / (2 * L) ≤ 1 := (div_le_one h2Lpos).mpr (by linarith)
    have hprod : 1 ≤ L * d := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hd)]
    linarith

/-- Approximation in a dense increasing union preserves graph embeddings with constant `2L`. -/
theorem finite_graph_embedding_in_submodule {X V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [Finite V] (A : ℕ → Submodule ℝ X) (hA : Monotone A)
    (hdense : Dense (⋃ n, (A n : Set X))) (G : SimpleGraph V) (hc : G.Connected)
    (φ : V → X) {L : ℝ} (hL : 1 ≤ L)
    (hφ : ∀ v w, (G.dist v w : ℝ) / L ≤ dist (φ v) (φ w) ∧
      dist (φ v) (φ w) ≤ L * G.dist v w) :
    ∃ m, ∃ ψ : V → A m, ∀ v w,
      (G.dist v w : ℝ) / (2 * L) ≤ dist (ψ v) (ψ w) ∧
      dist (ψ v) (ψ w) ≤ (2 * L) * G.dist v w := by
  have hLpos : 0 < L := by linarith
  obtain ⟨m, ψ, hψ⟩ := finite_approximation_in_submodule A hA hdense φ
    (show 0 < 1 / (4 * L) by positivity)
  refine ⟨m, ψ, fun v w => ?_⟩
  by_cases hvw : v = w
  · subst w
    simp
  · have hd : 1 ≤ (G.dist v w : ℝ) := by exact_mod_cast hc.pos_dist_of_ne hvw
    apply bilipschitz_bounds_stable hL hd (hφ v w)
    have herr := (pairwise_dist_perturbation hψ v w).le
    have heps : 2 * (1 / (4 * L)) = 1 / (2 * L) := by ring
    simpa only [heps, Subtype.dist_eq] using herr

end PropertyH
