import Mathlib

/-! Shared vocabulary for `paper/main.tex`. All carriers use Mathlib constructions. -/

noncomputable section

namespace PropertyH

/-- Source: `$S_X$`, the unit sphere of a normed space. -/
abbrev UnitSphere (X : Type*) [NormedAddCommGroup X] := ↥(Metric.sphere (0 : X) 1)

/-- Source: `$B_X$`, the closed unit ball (as required by the sphere restriction). -/
abbrev UnitBall (X : Type*) [NormedAddCommGroup X] := ↥(Metric.closedBall (0 : X) 1)

/-- Source: the inclusion `$S_X \subseteq B_X$`. -/
def sphereInclusion (X : Type*) [NormedAddCommGroup X] : C(UnitSphere X, UnitBall X) :=
  ContinuousMap.inclusion Metric.sphere_subset_closedBall

/-- Source: `$(F_n)_n$ are equi-uniformly continuous`.
The spaces may vary with `n`, so the same epsilon-delta bound is used for all indices. -/
def EquiUniformContinuous {X Y : ℕ → Type*}
    [∀ n, PseudoMetricSpace (X n)] [∀ n, PseudoMetricSpace (Y n)]
    (f : ∀ n, X n → Y n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ n x y, dist x y < δ → dist (f n x) (f n y) < ε

end PropertyH
