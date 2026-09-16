import PropertyH.RadialExtension
noncomputable section
namespace PropertyH
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Normalization of a nonzero vector as a point of the unit sphere. -/
def sphereNormalize (x : X) (hx : x ≠ 0) : UnitSphere X :=
  ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)⟩

@[simp] theorem norm_smul_sphereNormalize (x : X) (hx : x ≠ 0) :
    ‖x‖ • (sphereNormalize x hx : X) = x := by
  simp [sphereNormalize, smul_smul, norm_ne_zero_iff.mpr hx]

/-- Source: quantitative continuity of normalization away from zero. -/
theorem norm_mul_dist_sphereNormalize_le (x y : X) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ * dist (sphereNormalize x hx) (sphereNormalize y hy) ≤ 2 * dist x y := by
  have ht := dist_triangle x y (‖x‖ • (sphereNormalize y hy : X))
  have hr : dist y (‖x‖ • (sphereNormalize y hy : X)) ≤ dist x y := by
    conv_lhs => lhs; rw [← norm_smul_sphereNormalize y hy]
    simpa only [dist_eq_norm, ← sub_smul, norm_smul, mul_one,
      mem_sphere_zero_iff_norm.mp (sphereNormalize y hy).property, norm_sub_rev, Real.norm_eq_abs] using
      dist_norm_norm_le y x
  have hl : ‖x‖ * dist (sphereNormalize x hx) (sphereNormalize y hy) =
      dist x (‖x‖ • (sphereNormalize y hy : X)) := by
    simpa only [norm_norm, norm_smul_sphereNormalize, Subtype.dist_eq] using
      (dist_smul₀ ‖x‖ (sphereNormalize x hx : X) (sphereNormalize y hy : X)).symm
  linarith

/-- Source: radial extension continuity estimate used for `G_n`. -/
theorem dist_radialExtension_le (F : C(UnitSphere X, UnitSphere Y))
    (x y : X) (hx : x ≠ 0) (hy : y ≠ 0) :
    dist (radialExtension F x) (radialExtension F y) ≤
      ‖x‖ * dist (F (sphereNormalize x hx)) (F (sphereNormalize y hy)) + dist x y := by
  have ht := dist_triangle (radialExtension F x)
    (‖x‖ • (F (sphereNormalize y hy) : Y)) (radialExtension F y)
  have hr : dist (‖x‖ • (F (sphereNormalize y hy) : Y)) (radialExtension F y) ≤ dist x y := by
    simpa [radialExtension, hy, sphereNormalize, dist_eq_norm, ← sub_smul, norm_smul,
      mem_sphere_zero_iff_norm.mp (F (sphereNormalize y hy)).property] using dist_norm_norm_le x y
  have hl : dist (radialExtension F x) (‖x‖ • (F (sphereNormalize y hy) : Y)) =
      ‖x‖ * dist (F (sphereNormalize x hx)) (F (sphereNormalize y hy)) := by
    simp [radialExtension, hx, sphereNormalize, dist_smul₀, Subtype.dist_eq]
  linarith

/-- Source: the radial extensions `G_n` are equi-uniformly continuous on `2B_{X_n}`. -/
theorem equiUniformContinuous_radialExtension
    {X Y : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    EquiUniformContinuous (fun n (x : Metric.closedBall (0 : X n) 2) =>
      radialExtension (F n) x) := by
  intro ε hε
  obtain ⟨η, hη, hFη⟩ := hF (ε / 8) (by positivity)
  refine ⟨min (ε / 4) (η * ε / 16), by positivity, ?_⟩
  intro n x y hxy
  have hd : dist (x : X n) (y : X n) < ε / 4 ∧
      dist (x : X n) (y : X n) < η * ε / 16 := by
    simpa [Subtype.dist_eq, lt_min_iff] using hxy
  change dist (radialExtension (F n) x) (radialExtension (F n) y) < ε
  by_cases hsmall : ‖(x : X n)‖ < ε / 4
  · have hb := norm_sub_le (radialExtension (F n) x) (radialExtension (F n) y)
    have hn : ‖(y : X n)‖ ≤ ‖(x : X n)‖ + dist (x : X n) y := by
      simpa [dist_eq_norm, norm_sub_rev] using norm_le_norm_add_norm_sub (x : X n) y
    simp only [norm_radialExtension, ← dist_eq_norm] at hb
    linarith [hd.1]
  · have hx : (x : X n) ≠ 0 := norm_pos_iff.mp (by linarith)
    by_cases hy : (y : X n) = 0
    · simpa [hy, dist_zero_right] using (hd.1.trans (by linarith : ε / 4 < ε))
    · have hnorm : dist (sphereNormalize (x : X n) hx) (sphereNormalize (y : X n) hy) < η := by
        have hn := norm_mul_dist_sphereNormalize_le (x : X n) y hx hy
        nlinarith [hd.2, mul_pos hη hε, norm_pos_iff.mpr hx]
      have hout := hFη n _ _ hnorm
      have hbound := dist_radialExtension_le (F n) (x : X n) y hx hy
      have hx2 : ‖(x : X n)‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
      nlinarith [hd.1, norm_nonneg (x : X n),
        dist_nonneg (x := (F n) (sphereNormalize (x : X n) hx))
          (y := (F n) (sphereNormalize (y : X n) hy))]
end PropertyH
