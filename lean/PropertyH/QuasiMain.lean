import PropertyH.QuasiNormalized
import PropertyH.VaryingMain
import PropertyH.GroupEmbeddings


noncomputable section
namespace PropertyH
open Filter MeasureTheory
open scoped unitInterval Topology

/-- Finite paving approximation preserves coarse linear bounds, with additive error increased by two. -/
theorem finite_quasi_graph_embedding_in_submodule {X V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [Finite V] (A : ℕ → Submodule ℝ X) (hA : Monotone A)
    (hdense : Dense (⋃ n, (A n : Set X))) (G : SimpleGraph V)
    (φ : V → X) (L B : ℝ)
    (hφ : ∀ v w, (G.dist v w : ℝ) / L - B ≤ dist (φ v) (φ w) ∧
      dist (φ v) (φ w) ≤ L * G.dist v w + B) :
    ∃ m, ∃ ψ : V → A m, ∀ v w,
      (G.dist v w : ℝ) / L - (B + 2) ≤ dist (ψ v) (ψ w) ∧
      dist (ψ v) (ψ w) ≤ L * G.dist v w + (B + 2) := by
  obtain ⟨m, ψ, hψ⟩ := finite_approximation_in_submodule A hA hdense φ (by norm_num : (0 : ℝ) < 1)
  refine ⟨m, ψ, fun v w => ?_⟩
  have herr := abs_lt.mp (pairwise_dist_perturbation hψ v w)
  have hold := hφ v w
  simp only [Subtype.dist_eq] at ⊢
  constructor <;> linarith

/-- Source: restrict a quasi-isometric group copy to the isometrically embedded expanders. -/
theorem quasi_expander_maps_of_universal_groups (X : Type*) [NormedAddCommGroup X]
    (hX : ContainsAllFinitelyGeneratedGroups X)
    (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ)
    (hc : (SimpleGraph.mulCayley (S : Set Γ)).Connected)
    (E : ExpanderFamily) (ι : ∀ n, E.V n → Γ)
    (hι : ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) = (E.graph n).dist v u) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 ≤ B ∧ ∃ φ : ∀ n, E.V n → X,
      ∀ n v u, (E.graph n).dist v u / L - B ≤ ‖φ n v - φ n u‖ ∧
        ‖φ n v - φ n u‖ ≤ L * (E.graph n).dist v u + B := by
  obtain ⟨f, L, B, hL, hB, hf⟩ := hX Γ S hc
  refine ⟨L, B, hL, hB, fun n v => f (ι n v), ?_⟩
  intro n v u
  simpa only [hι] using hf (ι n v) (ι n u)
/-- Source: `Thm.main`. Normalize the graph embeddings, use uniform continuity
to make radial edge differences small, apply PIII, and normalize the resulting
nonvanishing averaging homotopy. No unproved external assumption is used. -/
theorem sphere_maps_eventually_nullhomotopic_quasi
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 (μ n))
    (hE : EquiQuasiGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  obtain ⟨ψ, K, a, ha, hKlim, hKnonneg, hψ⟩ := exists_normalized_expander_quasi_embeddings E X hE
  have hlarge : ∀ᶠ n in atTop, 5 ≤ Fintype.card (E.V n) :=
    E.grows.eventually (eventually_ge_atTop 5)
  obtain ⟨n₀, hn₀⟩ := hlarge.exists
  have hk : (0 : ℝ) < E.degreeBound := by
    exact_mod_cast (show 0 < E.degreeBound by have := (E.expands n₀).two_le_degreeBound hn₀; omega)
  let c : ℝ := 2 * E.degreeBound / E.expansion
  have hc : 0 < c := div_pos (mul_pos (by norm_num) hk) (E.expands 0).1
  let ε : ℝ := min (1 / 2) (a / 4)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hη : 0 < ε / c := div_pos hε hc
  obtain ⟨δ, hδ, hmod⟩ := equiUniformContinuous_radialExtension F hF (ε / c) hη
  filter_upwards [hψ, hlarge, hKlim.eventually_lt_const hδ] with n hn hncard hnK
  obtain ⟨hV, hzero, hnorm, hedge, hspread⟩ := hn
  let : Nonempty (E.V n) := hV
  apply nullhomotopic_of_small_average_deviation (F n) (ψ n) hzero a ε hspread
  · exact (min_le_left _ _).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  · exact (min_le_right _ _).trans_lt (by linarith : a / 4 < a / 2)
  · intro t x
    have hp := radial_average_deviation_bound (E.graph n) E.degreeBound E.expansion
      (E.expands n) hncard (μ n) (j n) (F n) (ψ n) hnorm (K n) δ (ε / c) hη.le hnK
      hedge (hmod n) t x
    simpa only [show (2 * (E.degreeBound : ℝ) / E.expansion) = c from rfl,
      mul_div_cancel₀ ε hc.ne'] using hp



/-- Source: quasi-isometric expander images can be approximated in a Property (H) paving. -/
theorem exists_paving_quasi_graph_embeddings (E : ExpanderFamily) {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hE : EquiQuasiGraphEmbeddings E (fun _ => X))
    (A : ℕ → Submodule ℝ X) (hA : Monotone A) (hdense : Dense (⋃ n, (A n : Set X))) :
    ∃ m : ℕ → ℕ, EquiQuasiGraphEmbeddings E (fun n => A (m n)) := by
  classical
  obtain ⟨L, B, hL, hB, φ, hφ⟩ := hE
  have happ : ∀ n, ∃ m, ∃ ψ : E.V n → A m, ∀ v u,
      ((E.graph n).dist v u : ℝ) / L - (B + 2) ≤ dist (ψ v) (ψ u) ∧
        dist (ψ v) (ψ u) ≤ L * (E.graph n).dist v u + (B + 2) := by
    intro n
    apply finite_quasi_graph_embedding_in_submodule A hA hdense (E.graph n) (φ n) L B
    simpa only [dist_eq_norm] using hφ n
  choose m ψ hψ using happ
  refine ⟨m, L, B + 2, hL, by linarith, ψ, ?_⟩
  simpa only [dist_eq_norm] using hψ
/-- Source: `Cor.Prop.H`, using degree-one non-null-homotopy; the old topology premise is retained for compatibility. -/
theorem not_hasPropertyH_of_quasi_expanders_of_sphere_noncontractible
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (_hsphere : ∀ S : Submodule ℝ X, FiniteDimensional ℝ S → ¬ ContractibleSpace (UnitSphere S))
    (E : ExpanderFamily) (hE : EquiQuasiGraphEmbeddings E (fun _ => X)) : ¬ HasPropertyH X := by
  classical
  rintro ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hdense, hrest⟩
  obtain ⟨m, hm⟩ := exists_paving_quasi_graph_embeddings E hE A hA hdense
  choose f hf hdegree using hrest
  let : ∀ n, FiniteDimensional ℝ (A n) := hAfin
  let : ∀ n, FiniteDimensional ℝ (B n) := hBfin
  let : ∀ n, MeasurableSpace (B (m n)) := fun n => borel (B (m n))
  let : ∀ n, BorelSpace (B (m n)) := fun n => ⟨rfl⟩
  let μ := fun n => ProbabilityTheory.stdGaussian (B (m n))
  let j := fun n => hilbertGaussianL1Isometry (E := B (m n))
  have hmod := equiUniformContinuous_submodule_restrictions F hF
    (fun n => A (m n)) (fun n => B (m n)) (fun n => f (m n)) (fun n => hf (m n))
  have hnull := sphere_maps_eventually_nullhomotopic_quasi E
    (fun n => A (m n)) (fun n => B (m n)) μ j hm (fun n => f (m n)) hmod
  obtain ⟨n, y, hy⟩ := hnull.exists
  exact (hdegree (m n)).not_nullhomotopic ⟨y, hy⟩

/-- Source: `Cor.no.PropH.cL.universal`, reduced exactly to sphere topology and Osajda's group. -/
theorem not_universal_groups_of_hasPropertyH_of_expander_group
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hsphere : ∀ S : Submodule ℝ X, FiniteDimensional ℝ S → ¬ ContractibleSpace (UnitSphere S))
    (hX : HasPropertyH X)
    (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ)
    (hc : (SimpleGraph.mulCayley (S : Set Γ)).Connected)
    (E : ExpanderFamily) (ι : ∀ n, E.V n → Γ)
    (hι : ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) = (E.graph n).dist v u) :
    ¬ ContainsAllFinitelyGeneratedGroups X := by
  intro huniv
  have hemb : EquiQuasiGraphEmbeddings E (fun _ => X) :=
    quasi_expander_maps_of_universal_groups X huniv Γ S hc E ι hι
  exact not_hasPropertyH_of_quasi_expanders_of_sphere_noncontractible X hsphere E hemb hX
end PropertyH

