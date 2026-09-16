import PropertyH.PropertyH
import PropertyH.RadialUniform

noncomputable section
namespace PropertyH

/-- The part of the ambient sphere lying in the union of a sequence of subspaces. -/
def pavingSphere {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ℕ → Submodule ℝ X) : Set (UnitSphere X) :=
  {x | ∃ n, (x : X) ∈ A n}

/-- Density of the union of subspaces implies density of its unit sphere. -/
theorem pavingSphere_dense {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ℕ → Submodule ℝ X) (hd : Dense (⋃ n, (A n : Set X))) :
    Dense (pavingSphere A) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨y, hy, hxy⟩ := hd.exists_dist_lt (x : X) (show 0 < min (ε / 2) (1 / 2) by positivity)
  have hxn : ‖(x : X)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hx : (x : X) ≠ 0 := norm_ne_zero_iff.mp (by rw [hxn]; norm_num)
  have hy0 : y ≠ 0 := by
    intro hy0
    simp only [hy0, dist_zero_right, hxn, lt_min_iff] at hxy
    linarith [hxy.2]
  refine ⟨sphereNormalize y hy0, ?_, ?_⟩
  · have hb := norm_mul_dist_sphereNormalize_le (x : X) y hx hy0
    have hxnorm : sphereNormalize (x : X) hx = x := by
      apply Subtype.ext
      simp [sphereNormalize, hxn]
    rw [hxn, one_mul, hxnorm] at hb
    have hxy' := hxy.trans_le (min_le_left _ _)
    rw [Metric.mem_ball, dist_comm]
    linarith
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    exact ⟨n, (A n).smul_mem _ hn⟩

/-- The dense-union formulation of a uniformly continuous sphere map extends to the whole
sphere when the target ambient space is complete. -/
theorem extend_uniform_pavingSphere_map {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [CompleteSpace Y]
    (A : ℕ → Submodule ℝ X) (hd : Dense (⋃ n, (A n : Set X)))
    (f : pavingSphere A → UnitSphere Y) (hf : UniformContinuous f) :
    ∃ F : C(UnitSphere X, UnitSphere Y), UniformContinuous F ∧
      ∀ x : pavingSphere A, F x = f x := by
  have : CompleteSpace (UnitSphere Y) := Metric.isClosed_sphere.isComplete.completeSpace_coe
  have hdS := pavingSphere_dense A hd
  have hcont := hdS.uniformContinuous_extend hf
  exact ⟨⟨hdS.extend f, hcont.continuous⟩, hcont, fun x => hdS.extend_of_ind hf x⟩

/-- Inclusion of a finite-stage sphere into the sphere of the union. -/
def pavingSphereInclusion {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ℕ → Submodule ℝ X) (n : ℕ) : UnitSphere (A n) → pavingSphere A :=
  fun x => ⟨submoduleSphereInclusion (A n) x, n, (x : A n).property⟩

/-- The homeomorphism-only dense-paving definition, with Hilbert target fixed to ℓ2,
implies the legacy homeomorphism formulation. No equivalence with degree one is claimed. -/
theorem hasHomeomorphicPropertyH_of_dense_paving_homeomorphisms {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ Hilbert)
    (hA : Monotone A) (hB : Monotone B)
    (hAfin : ∀ n, FiniteDimensional ℝ (A n)) (hBfin : ∀ n, FiniteDimensional ℝ (B n))
    (hd : Dense (⋃ n, (A n : Set X)))
    (f : pavingSphere A → UnitSphere Hilbert) (hf : UniformContinuous f)
    (e : ∀ n, UnitSphere (A n) ≃ₜ UnitSphere (B n))
    (he : ∀ n x, submoduleSphereInclusion (B n) (e n x) = f (pavingSphereInclusion A n x)) :
    HasHomeomorphicPropertyH X := by
  obtain ⟨F, hF, hFeq⟩ := extend_uniform_pavingSphere_map A hd f hf
  refine ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hd, fun n => ?_⟩
  refine ⟨(e n : C(_, _)), ?_, e n, ?_⟩
  · apply ContinuousMap.ext
    intro x
    exact (he n x).trans (hFeq (pavingSphereInclusion A n x)).symm
  · exact ContinuousMap.Homotopic.refl _


/-- The dense-paving degree-one definition with target ℓ₂ extends to the revised
full-sphere definition. Degree witnesses stay on exactly the same stage maps. -/
theorem hasPropertyH_of_dense_paving_degreeOne {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ Hilbert)
    (hA : Monotone A) (hB : Monotone B)
    (hAfin : ∀ n, FiniteDimensional ℝ (A n)) (hBfin : ∀ n, FiniteDimensional ℝ (B n))
    (hd : Dense (⋃ n, (A n : Set X)))
    (f : pavingSphere A → UnitSphere Hilbert) (hf : UniformContinuous f)
    (g : ∀ n, C(UnitSphere (A n), UnitSphere (B n)))
    (hg : ∀ n, SphereMapDegreeOne (g n))
    (he : ∀ n x, submoduleSphereInclusion (B n) (g n x) = f (pavingSphereInclusion A n x)) :
    HasPropertyH X := by
  obtain ⟨F, hF, hFeq⟩ := extend_uniform_pavingSphere_map A hd f hf
  refine ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hd, fun n => ⟨g n, ?_, hg n⟩⟩
  apply ContinuousMap.ext
  intro x
  exact (he n x).trans (hFeq (pavingSphereInclusion A n x)).symm

end PropertyH
