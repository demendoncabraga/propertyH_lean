import PropertyH.HilbertL1
import PropertyH.MainProof
import PropertyH.PropertyH
import PropertyH.FiniteApproximation
import PropertyH.SphereTopology
noncomputable section
namespace PropertyH
open Filter MeasureTheory
open scoped unitInterval Topology
/-- Source: `Thm.main`. Normalize the graph embeddings, use uniform continuity
to make radial edge differences small, apply PIII, and normalize the resulting
nonvanishing averaging homotopy. No unproved external assumption is used. -/
theorem sphere_maps_eventually_nullhomotopic_varying
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 (μ n))
    (hE : EquiGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  obtain ⟨ψ, K, a, ha, hKlim, hKnonneg, hψ⟩ := exists_normalized_expander_embeddings E X hE
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


/-- Restricting one uniformly continuous sphere map to varying subspaces preserves a common modulus. -/
theorem equiUniformContinuous_submodule_restrictions {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : C(UnitSphere X, UnitSphere Y)) (hF : UniformContinuous F)
    (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ Y)
    (f : ∀ n, C(UnitSphere (A n), UnitSphere (B n)))
    (hf : ∀ n, (submoduleSphereInclusion (B n)).comp (f n) =
      F.comp (submoduleSphereInclusion (A n))) :
    EquiUniformContinuous (fun n => f n) := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hF ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n x y hxy
  have hx := DFunLike.congr_fun (hf n) x
  have hy := DFunLike.congr_fun (hf n) y
  have hs : dist (submoduleSphereInclusion (A n) x) (submoduleSphereInclusion (A n) y) < δ := by
    simpa only [submoduleSphereInclusion, ContinuousMap.coe_mk, Subtype.dist_eq] using hxy
  have ht := hmod hs
  simp only [ContinuousMap.comp_apply] at hx hy
  rw [← hx, ← hy] at ht
  simpa only [submoduleSphereInclusion, ContinuousMap.coe_mk, Subtype.dist_eq] using ht

/-- Source: finite graph images can be moved into stages of the Property (H) paving. -/
theorem exists_paving_graph_embeddings (E : ExpanderFamily) {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hE : EquiGraphEmbeddings E (fun _ => X))
    (A : ℕ → Submodule ℝ X) (hA : Monotone A) (hdense : Dense (⋃ n, (A n : Set X))) :
    ∃ m : ℕ → ℕ, EquiGraphEmbeddings E (fun n => A (m n)) := by
  classical
  obtain ⟨L, hL, φ, hφ⟩ := hE
  have happ : ∀ n, ∃ m, ∃ ψ : E.V n → A m, ∀ v u,
      ((E.graph n).dist v u : ℝ) / (2 * L) ≤ dist (ψ v) (ψ u) ∧
        dist (ψ v) (ψ u) ≤ (2 * L) * (E.graph n).dist v u := by
    intro n
    cases isEmpty_or_nonempty (E.V n) with
    | inl h => exact ⟨0, fun v => isEmptyElim v, fun v => isEmptyElim v⟩
    | inr h =>
      apply finite_graph_embedding_in_submodule A hA hdense (E.graph n) (E.expands n).connected (φ n) hL
      simpa only [dist_eq_norm] using hφ n
  choose m ψ hψ using happ
  refine ⟨m, 2 * L, by linarith, ψ, ?_⟩
  simpa only [dist_eq_norm] using hψ

/-- Source: `Cor.Prop.H`, using degree-one non-null-homotopy; the old topology premise is retained for compatibility. -/
theorem not_hasPropertyH_of_containsExpanders_of_sphere_noncontractible
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (_hsphere : ∀ S : Submodule ℝ X, FiniteDimensional ℝ S → ¬ ContractibleSpace (UnitSphere S))
    (hX : ContainsExpanders X) : ¬ HasPropertyH X := by
  classical
  rintro ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hdense, hrest⟩
  obtain ⟨E, hE⟩ := hX
  obtain ⟨m, hm⟩ := exists_paving_graph_embeddings E hE A hA hdense
  choose f hf hdegree using hrest
  let : ∀ n, FiniteDimensional ℝ (A n) := hAfin
  let : ∀ n, FiniteDimensional ℝ (B n) := hBfin
  let : ∀ n, MeasurableSpace (B (m n)) := fun n => borel (B (m n))
  let : ∀ n, BorelSpace (B (m n)) := fun n => ⟨rfl⟩
  let μ := fun n => ProbabilityTheory.stdGaussian (B (m n))
  let j := fun n => hilbertGaussianL1Isometry (E := B (m n))
  have hmod := equiUniformContinuous_submodule_restrictions F hF
    (fun n => A (m n)) (fun n => B (m n)) (fun n => f (m n)) (fun n => hf (m n))
  have hnull := sphere_maps_eventually_nullhomotopic_varying E
    (fun n => A (m n)) (fun n => B (m n)) μ j hm (fun n => f (m n)) hmod
  obtain ⟨n, y, hy⟩ := hnull.exists
  exact (hdegree (m n)).not_nullhomotopic ⟨y, hy⟩
end PropertyH

