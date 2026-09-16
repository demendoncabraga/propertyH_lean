import PropertyH.SphereDegree

open CategoryTheory
noncomputable section
namespace PropertyH
universe u v

def reducedHomologyEquiv (n : ℕ) {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ↥(reducedHomology n (TopCat.of X)) ≃ₗ[ℤ] ↥(reducedHomology n (TopCat.of Y)) where
  toLinearMap := reducedHomologyMap n (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))
  invFun := reducedHomologyMap n (TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(Y, X)))
  left_inv := by
    intro x
    change ((reducedHomologyMap n (TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(Y, X)))).comp
      (reducedHomologyMap n (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y))))) x = x
    rw [← reducedHomologyMap_comp]
    have h : TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)) ≫ TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(Y, X)) = 𝟙 (TopCat.of X) := by ext; simp
    rw [h, reducedHomologyMap_id]
    rfl
  right_inv := by
    intro x
    change ((reducedHomologyMap n (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))).comp
      (reducedHomologyMap n (TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(Y, X))))) x = x
    rw [← reducedHomologyMap_comp]
    have h : TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(Y, X)) ≫ TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)) = 𝟙 (TopCat.of Y) := by ext; simp
    rw [h, reducedHomologyMap_id]
    rfl

def liftedHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : ULift.{v} X ≃ₜ ULift.{u} Y :=
  Homeomorph.ulift.trans (e.trans Homeomorph.ulift.symm)

theorem SphereMapDegreeOne.postcompose_homeomorph
    {X : Type u} {Y Z : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : C(UnitSphere X, UnitSphere Y)} (hf : SphereMapDegreeOne f)
    (e : UnitSphere Y ≃ₜ UnitSphere Z)
    (hdim : Module.finrank ℝ Y = Module.finrank ℝ Z) :
    SphereMapDegreeOne ((⟨e, e.continuous⟩ : C(UnitSphere Y, UnitSphere Z)).comp f) := by
  refine ⟨hf.1.trans hdim, ?_⟩
  rcases hf.2 with ⟨hz, hx, hy⟩ | ⟨hpos, bx, by_, hd⟩
  · exact Or.inl ⟨hz, hx, ⟨fun z => hy.false (e.symm z)⟩⟩
  · let el : ULift.{u} (UnitSphere Y) ≃ₜ ULift.{u} (UnitSphere Z) :=
      Homeomorph.ulift.trans (e.trans Homeomorph.ulift.symm)
    let E := reducedHomologyEquiv (Module.finrank ℝ X - 1) el
    refine Or.inr ⟨hpos, bx, by_.map E, ?_⟩
    unfold homologyDegree
    rw [Module.Basis.map_repr]
    have heq : TopCat.ofHom (liftedContinuousMap
        ((⟨e, e.continuous⟩ : C(UnitSphere Y, UnitSphere Z)).comp f)) =
        TopCat.ofHom (liftedContinuousMap f) ≫
          TopCat.ofHom (⟨el, el.continuous⟩ : C(_, _)) := rfl
    rw [heq, reducedHomologyMap_comp]
    change by_.repr (E.symm (E ((reducedHomologyMap _
      (TopCat.ofHom (liftedContinuousMap f))) (bx ())))) () = 1
    simpa [homologyDegree] using hd

/-- The sphere homeomorphism induced by a linear isometry equivalence. -/
def linearIsometrySphereHomeomorph {Y : Type u} {Z : Type v}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : Y ≃ₗᵢ[ℝ] Z) : UnitSphere Y ≃ₜ UnitSphere Z :=
  e.toHomeomorph.sets (by ext x; simp)

theorem SphereMapDegreeOne.postcompose_linearIsometryEquiv
    {X : Type u} {Y Z : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : C(UnitSphere X, UnitSphere Y)} (hf : SphereMapDegreeOne f)
    (e : Y ≃ₗᵢ[ℝ] Z) :
    SphereMapDegreeOne ((⟨linearIsometrySphereHomeomorph e,
      (linearIsometrySphereHomeomorph e).continuous⟩ :
        C(UnitSphere Y, UnitSphere Z)).comp f) :=
  hf.postcompose_homeomorph (linearIsometrySphereHomeomorph e) e.toLinearEquiv.finrank_eq

end PropertyH
