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

/-- The manuscript's degree-zero conclusion for arbitrary Banach spheres:
all induced maps on reduced integral homology vanish. -/
def HasDegreeZero {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  ∀ n : ℕ, reducedHomologyMap n (TopCat.ofHom (liftedContinuousMap f)) = 0

theorem hasDegreeZero_of_nullhomotopic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : f.Nullhomotopic) : HasDegreeZero f := by
  exact fun n => reducedHomologyMap_nullhomotopic n
    (TopCat.ofHom (liftedContinuousMap f)) (liftedContinuousMap_nullhomotopic f hf)

/-- In every degree with chosen integral generators, the integer degree is zero. -/
theorem HasDegreeZero.homologyDegree_eq_zero
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : HasDegreeZero f) (n : ℕ)
    (bX : Module.Basis Unit ℤ ↥(reducedHomology n (TopCat.of (ULift.{v} X))))
    (bY : Module.Basis Unit ℤ ↥(reducedHomology n (TopCat.of (ULift.{u} Y)))) :
    homologyDegree n f bX bY = 0 := by
  simp [homologyDegree, hf n]

/-- Nonzero degree for the finite stages of rational Property (H).
The empty-stage convention agrees with degree one. -/
def SphereMapNonzeroDegree {X : Type u} {Y : Type v}
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
          homologyDegree (Module.finrank ℝ X - 1) f bX bY ≠ 0))


theorem SphereMapDegreeOne.nonzero {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : C(UnitSphere X, UnitSphere Y)} (hf : SphereMapDegreeOne f) :
    SphereMapNonzeroDegree f := by
  exact ⟨hf.1, hf.2.imp id (fun ⟨hp, bX, bY, hd⟩ => ⟨hp, bX, bY, by omega⟩)⟩

/-- A nonzero-degree finite-stage map cannot be null-homotopic. -/
theorem SphereMapNonzeroDegree.not_nullhomotopic {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : C(UnitSphere X, UnitSphere Y)} (hf : SphereMapNonzeroDegree f) :
    ¬ f.Nullhomotopic := by
  intro hnull
  rcases hf.2 with ⟨_, _, hy⟩ | ⟨_, bX, bY, hdegree⟩
  · obtain ⟨y, _⟩ := hnull
    exact hy.false y
  · exact hdegree ((hasDegreeZero_of_nullhomotopic f hnull).homologyDegree_eq_zero _ bX bY)

end PropertyH
