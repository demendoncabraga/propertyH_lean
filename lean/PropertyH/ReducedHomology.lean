import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Topology.Homotopy.Contractible

/-!
Integral reduced singular homology, represented as the kernel of the map to a point.
This gives the usual reduced homology in nonnegative degrees, including degree zero.
The induced maps come from Mathlib's singular homology functor; homotopy invariance
comes from Mathlib's singular-chain homotopy theorem. No sphere-homology calculation
is assumed here.
-/

open CategoryTheory AlgebraicTopology
namespace PropertyH
universe u
noncomputable section

/-- Singular homology with integer coefficients. -/
def integralHomology (n : ℕ) : TopCat.{u} ⥤ ModuleCat.{u} ℤ :=
  (singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))

def collapse (X : TopCat.{u}) : X ⟶ TopCat.of PUnit.{u+1} :=
  TopCat.ofHom (ContinuousMap.const X PUnit.unit)

/-- Reduced integral singular homology in nonnegative degree. -/
def reducedHomology (n : ℕ) (X : TopCat.{u}) :=
  LinearMap.ker (((integralHomology n).map (collapse X)).hom)

theorem collapse_comp {X Y : TopCat.{u}} (f : X ⟶ Y) : f ≫ collapse Y = collapse X := by
  ext x

/-- The induced map on reduced integral singular homology. -/
def reducedHomologyMap (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ↥(reducedHomology n X) →ₗ[ℤ] ↥(reducedHomology n Y) :=
  (((integralHomology n).map f).hom).restrict (p := reducedHomology n X) (q := reducedHomology n Y) (by
    intro x hx
    change (((integralHomology n).map (collapse Y)).hom)
      ((((integralHomology n).map f).hom) x) = 0
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp, collapse_comp]
    exact hx)

theorem reducedHomologyMap_homotopic (n : ℕ) {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (h : f.hom.Homotopic g.hom) : reducedHomologyMap n f = reducedHomologyMap n g := by
  obtain ⟨H⟩ := h
  have hh : (integralHomology n).map f = (integralHomology n).map g :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℤ (ULift.{u} ℤ)) n
  simp only [reducedHomologyMap, hh]

theorem reducedHomologyMap_const (n : ℕ) {X Y : TopCat.{u}} (y : Y) :
    reducedHomologyMap n (TopCat.ofHom (ContinuousMap.const X y)) = 0 := by
  have hfactor : TopCat.ofHom (ContinuousMap.const X y) =
      collapse X ≫ TopCat.ofHom (ContinuousMap.const PUnit.{u+1} y) := by ext; rfl
  ext x
  change (((integralHomology n).map (TopCat.ofHom (ContinuousMap.const X y))).hom) x = 0
  rw [hfactor, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [show (((integralHomology n).map (collapse X)).hom) x = 0 from x.property]
  exact map_zero _

theorem reducedHomologyMap_nullhomotopic (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
    (h : f.hom.Nullhomotopic) : reducedHomologyMap n f = 0 := by
  obtain ⟨y, hy⟩ := h
  exact (reducedHomologyMap_homotopic n hy).trans (reducedHomologyMap_const n y)

theorem reducedHomologyMap_id (n : ℕ) (X : TopCat.{u}) :
    reducedHomologyMap n (𝟙 X) = LinearMap.id := by
  ext x
  change (((integralHomology n).map (𝟙 X)).hom) x = x
  simp

theorem reducedHomologyMap_comp (n : ℕ) {X Y Z : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    reducedHomologyMap n (f ≫ g) =
      (reducedHomologyMap n g).comp (reducedHomologyMap n f) := by
  ext x
  change (((integralHomology n).map (f ≫ g)).hom) x =
    (((integralHomology n).map g).hom) ((((integralHomology n).map f).hom) x)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end
end PropertyH

universe u v
namespace PropertyH
noncomputable def liftedContinuousMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)) :
    C(ULift.{v} X, ULift.{u} Y) :=
  ((⟨ULift.up, continuous_uliftUp⟩ : C(Y, ULift.{u} Y)).comp f).comp
    (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{v} X, X))

theorem liftedContinuousMap_nullhomotopic {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)) (h : f.Nullhomotopic) :
    (liftedContinuousMap f).Nullhomotopic := by
  exact (h.comp_right (⟨ULift.up, continuous_uliftUp⟩ : C(Y, ULift.{u} Y))).comp_left
    (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{v} X, X))
end PropertyH

