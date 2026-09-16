import PropertyH.Basic

noncomputable section
namespace PropertyH

/-- A fixed-point-free continuous map on a compact space has uniformly positive displacement. -/
theorem positive_displacement_of_no_fixed_point {K : Type*} [MetricSpace K]
    [CompactSpace K] [Nonempty K] (f : C(K, K)) (hnofix : ∀ x, f x ≠ x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ dist (f x) x := by
  have hc : Continuous (fun x => dist (f x) x) := f.continuous.dist continuous_id
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  refine ⟨dist (f x) x, dist_pos.mpr (hnofix x), ?_⟩
  exact fun y => hx (Set.mem_univ y)

/-- On a compact metric space, arbitrarily accurate approximate fixed points yield a fixed point. -/
theorem fixed_point_of_approximate {K : Type*} [MetricSpace K]
    [CompactSpace K] [Nonempty K] (f : C(K, K))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x, dist (f x) x < ε) : ∃ x, f x = x := by
  by_contra! hnofix
  obtain ⟨ε, hε, hbound⟩ := positive_displacement_of_no_fixed_point f hnofix
  obtain ⟨x, hx⟩ := happrox ε hε
  exact (not_lt_of_ge (hbound x)) hx

/-- A countable sequence of displacement bounds is enough. -/
theorem fixed_point_of_reciprocal_approximate {K : Type*} [MetricSpace K]
    [CompactSpace K] [Nonempty K] (f : C(K, K))
    (happrox : ∀ n : ℕ, ∃ x, dist (f x) x ≤ 1 / ((n : ℝ)+1)) : ∃ x, f x = x := by
  apply fixed_point_of_approximate f
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨x, hx⟩ := happrox n
  exact ⟨x, hx.trans_lt hn⟩

/-- The approximate-fixed-point criterion for the unit ball of a finite-dimensional real space. -/
theorem unitBall_fixed_point_of_approximate {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (f : C(UnitBall X, UnitBall X))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x, dist (f x) x < ε) : ∃ x, f x = x := by
  have : Nonempty (UnitBall X) := ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩⟩
  exact fixed_point_of_approximate f happrox
end PropertyH
