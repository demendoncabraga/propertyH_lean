import PropertyH.Basic
import PropertyH.ReducedHomology

noncomputable section
namespace PropertyH
universe u v

/-- Integral degree relative to specified generators of reduced homology.
For an `(n+1)`-dimensional normed space, its sphere uses degree `n` homology. -/
def homologyDegree {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y))
    (bX : Module.Basis Unit ℤ ↥(reducedHomology n (TopCat.of (ULift.{v} X))))
    (bY : Module.Basis Unit ℤ ↥(reducedHomology n (TopCat.of (ULift.{u} Y)))) : ℤ :=
  bY.repr (reducedHomologyMap n (TopCat.ofHom (liftedContinuousMap f)) (bX ())) ()

/-- Degree one for finite-dimensional spheres, with orientations explicitly chosen
through generators of top reduced integral homology. The manuscript fixes no
orientations: existential generators mean degree one after choosing orientations
(equivalently absolute degree one relative to any fixed orientations).

The zero-dimensional ambient case is the unique empty-sphere map. Reduced H₀
handles one-dimensional ambient spaces; ordinary H₀ would not suffice here.
Finite dimensionality is supplied by the surrounding Property (H) definition. -/
def SphereMapDegreeOne {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : C(UnitSphere X, UnitSphere Y)) : Prop :=
  Module.finrank ℝ X = Module.finrank ℝ Y ∧
    ((Module.finrank ℝ X = 0 ∧ IsEmpty (UnitSphere X) ∧ IsEmpty (UnitSphere Y)) ∨
      (0 < Module.finrank ℝ X ∧
        ∃ (bX : Module.Basis Unit ℤ ↥(reducedHomology (Module.finrank ℝ X - 1)
          (TopCat.of (ULift.{v} (UnitSphere X)))))
          (bY : Module.Basis Unit ℤ ↥(reducedHomology (Module.finrank ℝ X - 1)
          (TopCat.of (ULift.{u} (UnitSphere Y))))),
          homologyDegree (Module.finrank ℝ X - 1) f bX bY = 1))

theorem homologyDegree_eq_zero_of_nullhomotopic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y))
    (bX : Module.Basis Unit ℤ ↥(reducedHomology n (TopCat.of (ULift.{v} X))))
    (bY : Module.Basis Unit ℤ ↥(reducedHomology n (TopCat.of (ULift.{u} Y))))
    (hf : f.Nullhomotopic) : homologyDegree n f bX bY = 0 := by
  unfold homologyDegree
  rw [reducedHomologyMap_nullhomotopic n (TopCat.ofHom (liftedContinuousMap f)) (liftedContinuousMap_nullhomotopic f hf)]
  simp

/-- Source: a degree-one map between finite-dimensional spheres is never null-homotopic. -/
theorem SphereMapDegreeOne.not_nullhomotopic {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : C(UnitSphere X, UnitSphere Y)} (hf : SphereMapDegreeOne f) :
    ¬ f.Nullhomotopic := by
  intro hnull
  rcases hf.2 with ⟨_, _, hy⟩ | ⟨_, bX, bY, hdegree⟩
  · obtain ⟨y, _⟩ := hnull
    exact hy.false y
  · have hzero := homologyDegree_eq_zero_of_nullhomotopic _ f bX bY hnull
    omega

end PropertyH
