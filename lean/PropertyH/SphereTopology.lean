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

end PropertyH
