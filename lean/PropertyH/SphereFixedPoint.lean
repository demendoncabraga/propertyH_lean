import PropertyH.SphereRetraction

noncomputable section
namespace PropertyH
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Negating the values of a sphere-valued ball map produces a ball self-map. -/
def negatedSphereMap (r : C(UnitBall X, UnitSphere X)) : C(UnitBall X, UnitBall X) where
  toFun x := ⟨-(r x : X), by
    apply mem_closedBall_zero_iff.mpr
    rw [norm_neg, mem_sphere_zero_iff_norm.mp (r x).property]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact r.continuous.subtype_val.neg

/-- A ball retraction would give a continuous self-map of the ball without a fixed point. -/
theorem negatedSphereMap_ne_self (r : C(UnitBall X, UnitSphere X))
    (hr : r.comp (sphereInclusion X) = ContinuousMap.id (UnitSphere X))
    (x : UnitBall X) : negatedSphereMap r x ≠ x := by
  intro hx
  have heq : -(r x : X) = (x : X) := congrArg Subtype.val hx
  have hxnorm : ‖(x : X)‖ = 1 := by
    rw [← heq, norm_neg]
    exact mem_sphere_zero_iff_norm.mp (r x).property
  let sx : UnitSphere X := ⟨x, mem_sphere_zero_iff_norm.mpr hxnorm⟩
  have hincl : sphereInclusion X sx = x := rfl
  have hrx : r x = sx := by
    have h := congrArg (fun f : C(UnitSphere X, UnitSphere X) => f sx) hr
    simpa only [ContinuousMap.comp_apply, hincl, ContinuousMap.id_apply] using h
  have hneg : -(x : X) = (x : X) := by simpa only [hrx] using heq
  have htwo : (2 : ℝ) • (x : X) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hneg.symm
  have hxzero : (x : X) = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  simp [hxzero] at hxnorm

/-- The fixed-point property of the ball rules out a retraction onto the sphere. -/
theorem no_sphere_retraction_of_fixedPoint_property
    (hfixed : ∀ f : C(UnitBall X, UnitBall X), ∃ x, f x = x) :
    ¬ ∃ r : C(UnitBall X, UnitSphere X),
      r.comp (sphereInclusion X) = ContinuousMap.id (UnitSphere X) := by
  rintro ⟨r, hr⟩
  obtain ⟨x, hx⟩ := hfixed (negatedSphereMap r)
  exact negatedSphereMap_ne_self r hr x hx

/-- A precise reduction of finite-dimensional sphere noncontractibility to Brouwer's
fixed-point property. This lemma does not assume or prove that property automatically. -/
theorem sphere_not_contractible_of_fixedPoint_property [FiniteDimensional ℝ X]
    (hfixed : ∀ f : C(UnitBall X, UnitBall X), ∃ x, f x = x) :
    ¬ ContractibleSpace (UnitSphere X) :=
  fun hc => no_sphere_retraction_of_fixedPoint_property hfixed (sphere_contractible_retraction hc)

end PropertyH
