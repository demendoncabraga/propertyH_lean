import PropertyH.AveragingFamily
import PropertyH.BoundaryHomotopy

/-! Analytic conclusion from the uniform mean-deviation estimate, before Poincare. -/
noncomputable section
namespace PropertyH
open scoped unitInterval
variable {V X Y : Type*} [Fintype V] [Nonempty V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Source: `eq:key`, using norm preservation of the radial extension. -/
theorem averagingFamily_norm_lower (F : C(UnitSphere X, UnitSphere Y)) (ψ : V → X)
    (ε : ℝ) (t : I) (x : UnitBall X)
    (hdev : average (fun v => ‖radialExtension F ((x : X) + (t : ℝ) • ψ v) -
      averagingFamily ψ (radialExtensionMap F) (t, x)‖) ≤ ε) :
    average (fun v => ‖(x : X) + (t : ℝ) • ψ v‖) - ε ≤
      ‖averagingFamily ψ (radialExtensionMap F) (t, x)‖ := by
  have h := average_norm_sub_deviation_le
    (fun v => radialExtension F ((x : X) + (t : ℝ) • ψ v))
  simp only [norm_radialExtension] at h
  exact (sub_le_sub_left hdev _).trans h

/-- Source: `Eq.lowerboundH1-eps`, `eq:ball`, and the final application of
`Prop.null.homotopy`. A sufficiently small mean deviation forces null-homotopy. -/
theorem nullhomotopic_of_small_average_deviation
    (F : C(UnitSphere X, UnitSphere Y)) (ψ : V → X)
    (hψ : ∑ v, ψ v = 0) (a ε : ℝ)
    (hspread : a ≤ average (fun v => ‖ψ v‖))
    (hεone : ε < 1) (hεspread : ε < a / 2)
    (hdev : ∀ (t : I) (x : UnitBall X),
      average (fun v => ‖radialExtension F ((x : X) + (t : ℝ) • ψ v) -
        averagingFamily ψ (radialExtensionMap F) (t, x)‖) ≤ ε) :
    F.Nullhomotopic := by
  refine nullhomotopic_of_nonvanishing_ball_family F
    (averagingFamily ψ (radialExtensionMap F)) ?_ ?_ ?_
  · exact fun x => (averagingFamily_zero ψ (radialExtensionMap F) (sphereInclusion X x)).trans
      (radialExtension_sphere F x)
  · intro t x
    have hlower := averagingFamily_norm_lower F ψ ε t (sphereInclusion X x) (hdev t _)
    change average (fun v => ‖(x : X) + (t : ℝ) • ψ v‖) - ε ≤
      ‖averagingFamily ψ (radialExtensionMap F) (t, sphereInclusion X x)‖ at hlower
    have hmean := norm_le_average_translate_smul_norm ψ hψ (x : X) (t : ℝ)
    have hx : ‖(x : X)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    apply norm_pos_iff.mp
    linarith
  · intro x
    have hlower := averagingFamily_norm_lower F ψ ε (1 : I) x (hdev 1 x)
    have hmean := average_norm_le_two_average_translate_norm ψ hψ (x : X)
    simp only [show ((1 : I) : ℝ) = 1 from rfl, one_smul] at hlower
    apply norm_pos_iff.mp
    linarith

end PropertyH
