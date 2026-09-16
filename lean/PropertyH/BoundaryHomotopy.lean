import PropertyH.NullHomotopy

/-! Normalization of a nonvanishing boundary homotopy. -/
noncomputable section
namespace PropertyH
open scoped unitInterval

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Source: `$H^n_1$`, the terminal slice of the averaging family. -/
def terminalSlice (H : C(I × UnitBall X, Y)) : C(UnitBall X, Y) where
  toFun x := H (1, x)
  continuous_toFun := H.continuous.comp (continuous_const.prodMk continuous_id)

/-- Source: the normalized homotopy `$f^n_s(x)=H^n_s(x)/\|H^n_s(x)\|$`.
The input family is only required to avoid zero on the boundary. -/
def normalizedBoundaryFamily (H : C(I × UnitBall X, Y))
    (hH : ∀ t x, H (t, sphereInclusion X x) ≠ 0) : C(I × UnitSphere X, UnitSphere Y) :=
  normalizeMap
    ⟨fun p => H (p.1, sphereInclusion X p.2), by fun_prop⟩
    (fun p => hH p.1 p.2)

/-- Source: the two homotopies at the end of the proof of `Thm.main`.
Normalize on the boundary, then use the nonvanishing terminal ball map. -/
theorem nullhomotopic_of_nonvanishing_ball_family
    (F : C(UnitSphere X, UnitSphere Y)) (H : C(I × UnitBall X, Y))
    (h0 : ∀ x, H (0, sphereInclusion X x) = (F x : Y))
    (hboundary : ∀ t x, H (t, sphereInclusion X x) ≠ 0)
    (hterminal : ∀ x, H (1, x) ≠ 0) : F.Nullhomotopic := by
  let f₁ := (normalizeMap (terminalSlice H) hterminal).comp (sphereInclusion X)
  have hF : F.Homotopic f₁ := by
    refine ⟨{
      toContinuousMap := normalizedBoundaryFamily H hboundary
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      apply Subtype.ext
      change ‖H (0, sphereInclusion X x)‖⁻¹ • H (0, sphereInclusion X x) = (F x : Y)
      simp only [h0, mem_sphere_zero_iff_norm.mp (F x).property, inv_one, one_smul]
    · exact fun _ => rfl
  obtain ⟨y, hy⟩ := normalized_boundary_nullhomotopic (terminalSlice H) hterminal
  exact ⟨y, hF.trans hy⟩

end PropertyH
