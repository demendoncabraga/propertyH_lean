import PropertyH.SphereDegree

/-! The manuscript’s degree-one definition of Property (H). -/
noncomputable section
namespace PropertyH

/-- Source: `$\ell_2$`, with real scalars. -/
abbrev Hilbert := lp (fun _ : ℕ => ℝ) 2

/-- Inclusion of the sphere of a linear subspace into the ambient sphere. -/
def submoduleSphereInclusion {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Submodule ℝ X) : C(UnitSphere S, UnitSphere X) where
  toFun x := ⟨((x : S) : X), x.property⟩
  continuous_toFun := by fun_prop

/-- Source: paragraph before `Cor.Prop.H` in the revised manuscript.
Each finite-stage restriction has degree one, witnessed on top reduced integral
homology after choosing orientations. No homeomorphism or homotopy equivalence
is included in this condition. See `SphereMapDegreeOne` for the empty-stage convention. -/
def HasPropertyH (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ F : C(UnitSphere X, UnitSphere Hilbert), UniformContinuous F ∧
    ∃ (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ Hilbert),
      Monotone A ∧ Monotone B ∧
      (∀ n, FiniteDimensional ℝ (A n)) ∧ (∀ n, FiniteDimensional ℝ (B n)) ∧
      Dense (⋃ n, (A n : Set X)) ∧
      ∀ n, ∃ f : C(UnitSphere (A n), UnitSphere (B n)),
        (submoduleSphereInclusion (B n)).comp f = F.comp (submoduleSphereInclusion (A n)) ∧
        SphereMapDegreeOne f

/-- Source: rational Property (H), with nonzero-degree finite-stage restrictions. -/
def HasRationalPropertyH (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ F : C(UnitSphere X, UnitSphere Hilbert), UniformContinuous F ∧
    ∃ (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ Hilbert),
      Monotone A ∧ Monotone B ∧
      (∀ n, FiniteDimensional ℝ (A n)) ∧ (∀ n, FiniteDimensional ℝ (B n)) ∧
      Dense (⋃ n, (A n : Set X)) ∧
      ∀ n, ∃ f : C(UnitSphere (A n), UnitSphere (B n)),
        (submoduleSphereInclusion (B n)).comp f = F.comp (submoduleSphereInclusion (A n)) ∧
        SphereMapNonzeroDegree f


theorem HasPropertyH.to_rational {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (h : HasPropertyH X) :
    HasRationalPropertyH X := by
  exact (fun ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hdense, hrest⟩ =>
    ⟨F, hF, A, B, hA, hB, hAfin, hBfin, hdense,
      fun n => (hrest n).imp (fun f ⟨hc, hd⟩ => ⟨hc, hd.nonzero⟩)⟩) h

end PropertyH
