import PropertyH.HilbertReduction
import PropertyH.DegreeTransport
import PropertyH.DefinitionBridge

noncomputable section
namespace PropertyH

/-- The degree-one Property (H) definition with a specified ambient target. -/
def HasPropertyHIn (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] : Prop :=
  ∃ F : C(UnitSphere X, UnitSphere H), UniformContinuous F ∧
    ∃ (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ H),
      Monotone A ∧ Monotone B ∧
      (∀ n, FiniteDimensional ℝ (A n)) ∧ (∀ n, FiniteDimensional ℝ (B n)) ∧
      Dense (⋃ n, (A n : Set X)) ∧
      ∀ n, ∃ f : C(UnitSphere (A n), UnitSphere (B n)),
        (submoduleSphereInclusion (B n)).comp f = F.comp (submoduleSphereInclusion (A n)) ∧
        SphereMapDegreeOne f

theorem hasPropertyHIn_hilbert_iff {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] : HasPropertyHIn X Hilbert ↔ HasPropertyH X := Iff.rfl

theorem sphereMap_mem_closedSpan_paving {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ H)
    (hd : Dense (⋃ n, (A n : Set X)))
    (F : C(UnitSphere X, UnitSphere H))
    (hF : ∀ n x, ((F (submoduleSphereInclusion (A n) x) : UnitSphere H) : H) ∈ B n)
    (x : UnitSphere X) :
    (F x : H) ∈ (Submodule.span ℝ (⋃ n, (B n : Set H))).topologicalClosure := by
  apply (pavingSphere_dense A hd).induction (P := fun x =>
    (F x : H) ∈ (Submodule.span ℝ (⋃ n, (B n : Set H))).topologicalClosure) ?_ ?_ x
  · intro y hy
    obtain ⟨n, hn⟩ := hy
    exact paving_le_closedSpan B n (hF n ⟨⟨y, hn⟩, y.property⟩)
  · exact (Submodule.isClosed_topologicalClosure _).preimage
      (continuous_subtype_val.comp F.continuous)

/-- The arbitrary real Hilbert target in Property (H) may be replaced by ℓ₂. -/
theorem hasPropertyH_of_hasPropertyHIn {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (h : HasPropertyHIn X H) :
    HasPropertyH X := by
  classical
  obtain ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hd, hg⟩ := h
  let := hBfin
  choose g hgeq hgdeg using hg
  let M := (Submodule.span ℝ (⋃ n, (B n : Set H))).topologicalClosure
  let j : M →ₗᵢ[ℝ] Hilbert := hilbertPavingEmbedding B
  let i : ∀ n, B n →ₗᵢ[ℝ] M := fun n =>
    { Submodule.inclusion (paving_le_closedSpan B n) with norm_map' := fun _ => rfl }
  let q : ∀ n, B n →ₗᵢ[ℝ] Hilbert := fun n => j.comp (i n)
  let D : ℕ → Submodule ℝ Hilbert := fun n => (q n).range
  have hmem : ∀ x : UnitSphere X, (F x : H) ∈ M := by
    apply sphereMap_mem_closedSpan_paving A B hd F
    intro n x
    have heq := congrArg (fun f : C(UnitSphere (A n), UnitSphere H) => f x) (hgeq n)
    simp only [ContinuousMap.comp_apply] at heq
    rw [← heq]
    exact (g n x : B n).property
  let fM : UnitSphere X → M := fun x => ⟨F x, hmem x⟩
  have hfM : UniformContinuous fM := (uniformContinuous_subtype_val.comp hF).subtype_mk _
  let f : UnitSphere X → UnitSphere Hilbert := fun x =>
    ⟨j (fM x), mem_sphere_zero_iff_norm.mpr (by
      rw [j.norm_map]
      exact mem_sphere_zero_iff_norm.mp (F x).property)⟩
  have hf : UniformContinuous f := (j.isometry.uniformContinuous.comp hfM).subtype_mk _
  refine ⟨⟨f, hf.continuous⟩, hf, A, D, hA, ?_, hAfin, ?_, hd, ?_⟩
  · intro n m hnm y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨⟨x, hB hnm x.property⟩, rfl⟩
  · intro n
    change FiniteDimensional ℝ (LinearMap.range (q n).toLinearMap)
    infer_instance
  · intro n
    let e := linearIsometrySphereHomeomorph (q n).equivRange
    refine ⟨(⟨e, e.continuous⟩ : C(_, _)).comp (g n), ?_,
      (hgdeg n).postcompose_linearIsometryEquiv (q n).equivRange⟩
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change j (i n (g n x)) = j (fM (submoduleSphereInclusion (A n) x))
    congr 1
    apply Subtype.ext
    exact congrArg (fun z : UnitSphere H => (z : H))
      (congrArg (fun k : C(UnitSphere (A n), UnitSphere H) => k x) (hgeq n))

/-- Property (H)'s countable finite-dimensional paving forces separability. -/
theorem HasPropertyHIn.separableSpace {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (h : HasPropertyHIn X H) : TopologicalSpace.SeparableSpace X := by
  obtain ⟨_, _, A, _, _, _, hAfin, _, hd, _⟩ := h
  let := hAfin
  apply hd.isSeparable_iff.mp
  apply TopologicalSpace.IsSeparable.iUnion
  intro n
  exact TopologicalSpace.isSeparable_range (A n).subtypeL.continuous |>.mono (by simp)

/-- Source separability in the manuscript's fixed-target formulation. -/
theorem HasPropertyH.separableSpace {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (h : HasPropertyH X) : TopologicalSpace.SeparableSpace X :=
  HasPropertyHIn.separableSpace ((hasPropertyHIn_hilbert_iff).mpr h)

/-- The original dense-paving, arbitrary-Hilbert-target degree-one formulation
implies the manuscript's full-sphere ℓ₂ formulation. -/
theorem hasPropertyH_of_dense_degreeOne_hilbert {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ H)
    (hA : Monotone A) (hB : Monotone B)
    (hAfin : ∀ n, FiniteDimensional ℝ (A n)) (hBfin : ∀ n, FiniteDimensional ℝ (B n))
    (hd : Dense (⋃ n, (A n : Set X)))
    (f : pavingSphere A → UnitSphere H) (hf : UniformContinuous f)
    (g : ∀ n, C(UnitSphere (A n), UnitSphere (B n)))
    (hg : ∀ n, SphereMapDegreeOne (g n))
    (he : ∀ n x, submoduleSphereInclusion (B n) (g n x) = f (pavingSphereInclusion A n x)) :
    HasPropertyH X := by
  apply hasPropertyH_of_hasPropertyHIn (H := H)
  obtain ⟨F, hF, hFeq⟩ := extend_uniform_pavingSphere_map A hd f hf
  refine ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hd, fun n => ⟨g n, ?_, hg n⟩⟩
  apply ContinuousMap.ext
  intro x
  exact (he n x).trans (hFeq (pavingSphereInclusion A n x)).symm

end PropertyH
