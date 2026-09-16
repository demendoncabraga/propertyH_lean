import PropertyH.Basic

namespace PropertyH

/-- A homeomorphism can be nullhomotopic precisely when its domain is contractible. -/
theorem homeomorph_nullhomotopic_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    (e : C(X, Y)).Nullhomotopic ↔ ContractibleSpace X := by
  constructor
  · intro he
    apply (contractible_iff_id_nullhomotopic X).mpr
    simpa only [Homeomorph.symm_comp_toContinuousMap] using
      he.comp_right (e.symm : C(Y, X))
  · intro hX
    simpa using (id_nullhomotopic X).comp_right (e : C(X, Y))

/-- A map into the unit sphere of a zero-dimensional space cannot be nullhomotopic:
there is no possible constant value. -/
theorem not_nullhomotopic_to_sphere_of_subsingleton {A Y : Type*} [TopologicalSpace A]
    [NormedAddCommGroup Y] [Subsingleton Y] (f : C(A, UnitSphere Y)) :
    ¬ f.Nullhomotopic := by
  rintro ⟨y, _⟩
  exact isEmptyElim y

/-- The real unit sphere consists of two isolated points, hence is not contractible. -/
theorem real_unitSphere_not_contractible : ¬ ContractibleSpace (UnitSphere ℝ) := by
  intro hc
  have hs : (Metric.sphere (0 : ℝ) 1).Finite := by
    rw [Real.sphere_eq_pair _ zero_le_one]
    exact (Set.finite_singleton _).insert _
  have : Finite (UnitSphere ℝ) := hs
  have : Subsingleton (UnitSphere ℝ) := subsingleton_of_preconnected_totallyDisconnected
  have heq := Subsingleton.elim (⟨1, by simp⟩ : UnitSphere ℝ) (⟨-1, by simp⟩ : UnitSphere ℝ)
  have : (1 : ℝ) = -1 := congrArg Subtype.val heq
  norm_num at this

/-- In dimension one, a sphere homeomorphism is not nullhomotopic. -/
theorem real_unitSphere_homeomorph_not_nullhomotopic {Y : Type*} [TopologicalSpace Y]
    (e : UnitSphere ℝ ≃ₜ Y) : ¬ (e : C(UnitSphere ℝ, Y)).Nullhomotopic :=
  fun he => real_unitSphere_not_contractible ((homeomorph_nullhomotopic_iff e).mp he)

end PropertyH
