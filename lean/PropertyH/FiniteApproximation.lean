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

end PropertyH
