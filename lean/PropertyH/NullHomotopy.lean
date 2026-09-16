import PropertyH.Basic

/-! The normalization construction in `Prop.null.homotopy`. -/

noncomputable section
namespace PropertyH

variable {A X Y : Type*} [TopologicalSpace A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Source: `$F(x)=f(x)/\|f(x)\|$`. -/
def normalizeMap (f : C(A, Y)) (hf : ∀ x, f x ≠ 0) : C(A, UnitSphere Y) where
  toFun x := ⟨‖f x‖⁻¹ • f x, by
    exact mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) (hf x))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (f.continuous.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hf x))).smul f.continuous

/-- Source: `$G_s(x)=f(g_s(x))/\|f(g_s(x))\|$`.
A continuous nonvanishing map on the ball has a null-homotopic normalized boundary.
Proof sketch: the ball is convex and nonempty, hence contractible; compose its
identity null-homotopy with normalization and the boundary inclusion. -/
theorem normalized_boundary_nullhomotopic (f : C(UnitBall X, Y))
    (hf : ∀ x, f x ≠ 0) :
    ((normalizeMap f hf).comp (sphereInclusion X)).Nullhomotopic := by
  let : ContractibleSpace (UnitBall X) :=
    (convex_closedBall (0 : X) (1 : ℝ)).contractibleSpace
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  exact ((id_nullhomotopic (UnitBall X)).comp_right (normalizeMap f hf)).comp_left
    (sphereInclusion X)

omit [TopologicalSpace A] [NormedSpace ℝ Y] in
/-- Source: `$\inf_{x\in B_X}\|f(x)\|>0$` implies that `f` avoids zero. -/
theorem nonvanishing_of_positive_infimum (f : A → Y)
    (hf : 0 < sInf (Set.range (fun x => ‖f x‖))) (x : A) : f x ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le hf
    (csInf_le ⟨0, fun _ ⟨y, hy⟩ => hy ▸ norm_nonneg (f y)⟩ ⟨x, rfl⟩))

/-- Source: `$f\colon B_X\to B_Y$`, regarded as an ambient-space map. -/
def ballMapToAmbient (f : C(UnitBall X, UnitBall Y)) : C(UnitBall X, Y) where
  toFun x := (f x : Y)
  continuous_toFun := f.continuous.subtype_val

/-- Source: `Prop.null.homotopy`.
`$\inf_{x\in B_X}\|f(x)\|>0$`; the map
`$F(x)=f(x)/\|f(x)\|$` on `$S_X$` is null-homotopic.
Completeness is unnecessary, so this also applies to Banach spaces. -/
theorem ball_normalization_nullhomotopic (f : C(UnitBall X, UnitBall Y))
    (hf : 0 < sInf (Set.range (fun x => ‖(f x : Y)‖))) :
    ((normalizeMap (ballMapToAmbient f)
      (nonvanishing_of_positive_infimum (ballMapToAmbient f) hf)).comp
        (sphereInclusion X)).Nullhomotopic := by
  exact normalized_boundary_nullhomotopic _ _

end PropertyH

