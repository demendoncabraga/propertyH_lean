import PropertyH.SphereDegree

/-! Degree-one Property (H), with the earlier homeomorphism formulation retained. -/
noncomputable section
namespace PropertyH

/-- Source: `$\ell_2$`, with real scalars. -/
abbrev Hilbert := lp (fun _ : ℕ => ℝ) 2

/-- Inclusion of the sphere of a linear subspace into the ambient sphere. -/
def submoduleSphereInclusion {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Submodule ℝ X) : C(UnitSphere S, UnitSphere X) where
  toFun x := ⟨((x : S) : X), x.property⟩
  continuous_toFun := by fun_prop

/-- Legacy definition from the earlier manuscript (homotopic homeomorphism restrictions).
`$F\colon S_X\to S_{\ell_2}$` is uniformly continuous; increasing finite-dimensional
`$X_n,H_n$` satisfy `$X=\overline{\bigcup_nX_n}$`, and the restrictions of `F`
map into `$S_{H_n}$` and are homotopic to homeomorphisms. -/
def HasHomeomorphicPropertyH (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ F : C(UnitSphere X, UnitSphere Hilbert), UniformContinuous F ∧
    ∃ (A : ℕ → Submodule ℝ X) (B : ℕ → Submodule ℝ Hilbert),
      Monotone A ∧ Monotone B ∧
      (∀ n, FiniteDimensional ℝ (A n)) ∧ (∀ n, FiniteDimensional ℝ (B n)) ∧
      Dense (⋃ n, (A n : Set X)) ∧
      ∀ n, ∃ f : C(UnitSphere (A n), UnitSphere (B n)),
        (submoduleSphereInclusion (B n)).comp f = F.comp (submoduleSphereInclusion (A n)) ∧
        ∃ e : UnitSphere (A n) ≃ₜ UnitSphere (B n), f.Homotopic ⟨e, e.continuous⟩

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

end PropertyH
