import PropertyH.NullHomotopy
noncomputable section
open Classical
namespace PropertyH
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Source: radial extension `G_n` in the proof of `Thm.main`. -/
def radialExtension (F : C(UnitSphere X, UnitSphere Y)) (x : X) : Y :=
  if hx : x = 0 then 0 else
    ‖x‖ • (F ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩ : Y)

@[simp] theorem radialExtension_zero (F : C(UnitSphere X, UnitSphere Y)) :
    radialExtension F 0 = 0 := by simp [radialExtension]

/-- Source: each radial extension is norm preserving. -/
@[simp] theorem norm_radialExtension (F : C(UnitSphere X, UnitSphere Y)) (x : X) :
    ‖radialExtension F x‖ = ‖x‖ := by
  unfold radialExtension
  split_ifs with hx
  · simp [hx]
  · simp [norm_smul,
      mem_sphere_zero_iff_norm.mp (F ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr
        (norm_smul_inv_norm hx)⟩).property]

/-- Source: the radial extension agrees with the sphere map. -/
@[simp] theorem radialExtension_sphere (F : C(UnitSphere X, UnitSphere Y))
    (x : UnitSphere X) : radialExtension F x = (F x : Y) := by
  have hx : ‖(x : X)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp [radialExtension, norm_ne_zero_iff.mp (show ‖(x : X)‖ ≠ 0 by rw [hx]; norm_num), hx]

/-- Source: continuity of `G_n`, including at the origin. -/
theorem continuous_radialExtension (F : C(UnitSphere X, UnitSphere Y)) :
    Continuous (radialExtension F) := by
  have hnonzero : ContinuousOn (radialExtension F) {x : X | x ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    let incl : C({x : X // x ≠ 0}, X) := ⟨Subtype.val, continuous_subtype_val⟩
    change Continuous (fun x : {x : X // x ≠ 0} => radialExtension F x)
    convert incl.continuous.norm.smul
      (F.continuous.comp (normalizeMap incl (fun x => x.property)).continuous).subtype_val using 1
    funext x
    simp [radialExtension, x.property, normalizeMap, incl]
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    exact fun ε hε => ⟨ε, hε, fun x hx => by simpa [dist_zero_right] using hx⟩
  · exact hnonzero.continuousAt (isOpen_ne.mem_nhds hx)

/-- Source: the continuous radial extension of a sphere map to the ambient space. -/
def radialExtensionMap (F : C(UnitSphere X, UnitSphere Y)) : C(X, Y) :=
  ⟨radialExtension F, continuous_radialExtension F⟩

end PropertyH
