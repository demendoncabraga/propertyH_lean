import PropertyH.Basic

noncomputable section
namespace PropertyH
open unitInterval

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The closed ball as the radial image of interval times sphere. -/
def radialBallMap : C(unitInterval × UnitSphere X, UnitBall X) where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : X), by
    apply mem_closedBall_zero_iff.mpr
    calc
      _ = (p.1 : ℝ) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.property.1,
          mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
      _ ≤ 1 := p.1.property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd))

lemma radialBallMap_surjective [Nonempty (UnitSphere X)] :
    Function.Surjective (radialBallMap (X := X)) := by
  intro x
  by_cases hx : (x : X) = 0
  · obtain ⟨v⟩ := ‹Nonempty (UnitSphere X)›
    refine ⟨(0, v), Subtype.ext ?_⟩
    simpa [radialBallMap] using hx.symm
  · let t : unitInterval := ⟨‖(x : X)‖, norm_nonneg _, mem_closedBall_zero_iff.mp x.property⟩
    let v : UnitSphere X := ⟨‖(x : X)‖⁻¹ • (x : X),
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx)⟩
    refine ⟨(t, v), Subtype.ext ?_⟩
    simp [radialBallMap, t, v, smul_smul, norm_ne_zero_iff.mpr hx]

lemma radialBallMap_norm (p : unitInterval × UnitSphere X) :
    ‖(radialBallMap p : X)‖ = (p.1 : ℝ) := by
  simp [radialBallMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.property.1,
    mem_sphere_zero_iff_norm.mp p.2.property]

lemma radial_homotopy_factors {Y : Type*} [TopologicalSpace Y] (y : Y)
    (f : C(UnitSphere X, Y)) (H : (ContinuousMap.const (UnitSphere X) y).Homotopy f) :
    Function.FactorsThrough H (radialBallMap (X := X)) := by
  intro p q hpq
  have ht : (p.1 : ℝ) = (q.1 : ℝ) := by
    simpa only [radialBallMap_norm] using congrArg (fun x : UnitBall X => ‖(x : X)‖) hpq
  by_cases ht0 : (p.1 : ℝ) = 0
  · have hp0 : p.1 = 0 := Subtype.ext ht0
    have hq0 : q.1 = 0 := Subtype.ext (ht.symm.trans ht0)
    change H (p.1, p.2) = H (q.1, q.2)
    rw [hp0, hq0]
    exact (H.map_zero_left p.2).trans (H.map_zero_left q.2).symm
  · have hs : (p.1 : ℝ) • (p.2 : X) = (p.1 : ℝ) • (q.2 : X) := by
      simpa only [radialBallMap, ContinuousMap.coe_mk, ht] using congrArg Subtype.val hpq
    have hv : p.2 = q.2 := Subtype.ext ((smul_right_injective X ht0) hs)
    exact congrArg H (Prod.ext (Subtype.ext ht) hv)

/-- Finite-dimensional compactness makes the radial parametrization a quotient map. -/
lemma radialBallMap_isQuotientMap [FiniteDimensional ℝ X] [Nonempty (UnitSphere X)] :
    Topology.IsQuotientMap (radialBallMap (X := X)) := by
  have : CompactSpace (UnitSphere X) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X) 1)
  exact Topology.IsQuotientMap.of_surjective_continuous
    radialBallMap_surjective radialBallMap.continuous

/-- A nullhomotopic sphere map extends continuously across the closed ball. -/
theorem sphere_nullhomotopic_extends_ball [FiniteDimensional ℝ X]
    [Nonempty (UnitSphere X)] {Y : Type*} [TopologicalSpace Y]
    (f : C(UnitSphere X, Y)) (hf : f.Nullhomotopic) :
    ∃ F : C(UnitBall X, Y), F.comp (sphereInclusion X) = f := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  let hq := radialBallMap_isQuotientMap (X := X)
  let F := hq.lift H.symm.toContinuousMap (radial_homotopy_factors y f H.symm)
  refine ⟨F, ?_⟩
  ext x
  have heq := congrArg (fun g : C(unitInterval × UnitSphere X, Y) => g (1, x))
    (hq.lift_comp H.symm.toContinuousMap (radial_homotopy_factors y f H.symm))
  have hboundary : radialBallMap (1, x) = sphereInclusion X x := by
    apply Subtype.ext
    change (1 : ℝ) • (x : X) = (x : X)
    exact one_smul ℝ _
  change F (radialBallMap (1, x)) = H.symm (1, x) at heq
  rw [hboundary] at heq
  exact heq.trans (H.symm.map_one_left x)

/-- Contractibility of a finite-dimensional unit sphere would yield a ball retraction. -/
theorem sphere_contractible_retraction [FiniteDimensional ℝ X]
    (h : ContractibleSpace (UnitSphere X)) :
    ∃ r : C(UnitBall X, UnitSphere X),
      r.comp (sphereInclusion X) = ContinuousMap.id (UnitSphere X) := by
  have : Nonempty (UnitSphere X) := inferInstance
  exact sphere_nullhomotopic_extends_ball _ (id_nullhomotopic _)

end PropertyH
