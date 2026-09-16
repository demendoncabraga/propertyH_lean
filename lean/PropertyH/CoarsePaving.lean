import PropertyH.CoarseEmbeddings
import PropertyH.Connectivity
import PropertyH.FiniteApproximation

noncomputable section
namespace PropertyH
open Filter

/-- Unit-error finite approximation preserves a proper compression after subtracting two. -/
theorem finite_coarse_graph_embedding_in_submodule {X V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [Finite V] (A : ℕ → Submodule ℝ X) (hA : Monotone A)
    (hdense : Dense (⋃ n, (A n : Set X))) (G : SimpleGraph V) (hc : G.Connected)
    (φ : V → X) (L : ℝ) (ρ : ℝ → ℝ)
    (hφ : ∀ v w, ρ (G.dist v w) ≤ dist (φ v) (φ w) ∧
      dist (φ v) (φ w) ≤ L * G.dist v w) :
    ∃ m, ∃ ψ : V → A m, ∀ v w,
      max 0 (ρ (G.dist v w)-2) ≤ dist (ψ v) (ψ w) ∧
        dist (ψ v) (ψ w) ≤ (L+2) * G.dist v w := by
  obtain ⟨m, ψ, hψ⟩ := finite_approximation_in_submodule A hA hdense φ (by norm_num : (0 : ℝ) < 1)
  refine ⟨m, ψ, fun v w => ?_⟩
  have herr := abs_lt.mp (pairwise_dist_perturbation hψ v w)
  have hold := hφ v w
  constructor
  · apply max_le
    · exact dist_nonneg
    · simp only [Subtype.dist_eq]
      linarith
  · by_cases hvw : v = w
    · subst w
      simp
    · have hd : (1 : ℝ) ≤ G.dist v w := by exact_mod_cast hc.pos_dist_of_ne hvw
      simp only [Subtype.dist_eq]
      nlinarith

/-- Coarse expander configurations persist in stages of a dense increasing paving. -/
theorem exists_paving_coarse_graph_embeddings (E : ExpanderFamily) {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hE : EquiCoarseGraphEmbeddings E (fun _ => X))
    (A : ℕ → Submodule ℝ X) (hA : Monotone A) (hdense : Dense (⋃ n, (A n : Set X))) :
    ∃ m : ℕ → ℕ, EquiCoarseGraphEmbeddings E (fun n => A (m n)) := by
  classical
  obtain ⟨L, ρ, hL, hmono, hnonneg, hrho, φ, hφ⟩ := hE
  have happ : ∀ n, ∃ m, ∃ ψ : E.V n → A m, ∀ v u,
      max 0 (ρ ((E.graph n).dist v u)-2) ≤ dist (ψ v) (ψ u) ∧
        dist (ψ v) (ψ u) ≤ (L+2) * (E.graph n).dist v u := by
    intro n
    cases isEmpty_or_nonempty (E.V n) with
    | inl h => exact ⟨0, fun v => isEmptyElim v, fun v => isEmptyElim v⟩
    | inr h =>
      apply finite_coarse_graph_embedding_in_submodule A hA hdense (E.graph n)
        (E.expands n).connected (φ n) L ρ
      simpa only [dist_eq_norm] using hφ n
  choose m ψ hψ using happ
  refine ⟨m, L+2, fun t => max 0 (ρ t-2), by linarith, ?_, ?_, ?_, ψ, ?_⟩
  · exact fun a b hab => max_le_max le_rfl (sub_le_sub_right (hmono hab) _)
  · exact fun t _ => le_max_left _ _
  · apply tendsto_atTop_mono (fun t => le_max_right 0 (ρ t-2))
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hrho.eventually (eventually_ge_atTop (b+2))] with t ht
    linarith
  · simpa only [dist_eq_norm] using hψ
end PropertyH
