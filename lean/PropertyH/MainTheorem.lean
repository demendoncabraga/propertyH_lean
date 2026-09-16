import PropertyH.MainProof

/-! The main theorem, proved through the expander averaging construction. -/
noncomputable section
namespace PropertyH
open Filter MeasureTheory

/-- Source: `Thm.main`.
`$Y_n\subseteq L_1$` is represented by linear isometric embeddings into a genuine
Mathlib `Lp` space. The ambient measure is arbitrary. The maps are bundled as
continuous maps; their common continuity modulus is required separately.
Proof plan: normalize centered graph embeddings, extend radially, average,
apply Poincare, and normalize the resulting uniformly nonvanishing homotopy. -/
theorem sphere_maps_eventually_nullhomotopic
    (E : ExpanderFamily) (X Y : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
    [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (j : ∀ n, Y n →ₗᵢ[ℝ] Lp ℝ 1 μ)
    (hE : EquiGraphEmbeddings E X)
    (F : ∀ n, C(UnitSphere (X n), UnitSphere (Y n)))
    (hF : EquiUniformContinuous (fun n => F n)) :
    ∀ᶠ n in atTop, (F n).Nullhomotopic := by
  exact sphere_maps_eventually_nullhomotopic_proved E X Y μ j hE F hF

end PropertyH
