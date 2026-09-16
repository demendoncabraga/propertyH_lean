import PropertyH.PropertyH
noncomputable section
namespace PropertyH
open Filter MeasureTheory
open scoped unitInterval Topology

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

end PropertyH

