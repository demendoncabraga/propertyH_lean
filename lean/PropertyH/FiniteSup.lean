import PropertyH.Basic

noncomputable section
namespace PropertyH

/-- Distance coordinates in the finite-dimensional sup-norm space. -/
def finiteDistanceCoordinates {V : Type*} [Fintype V] [PseudoMetricSpace V]
    (v : V) (i : Fin (Fintype.card V)) : ℝ :=
  dist v ((Fintype.equivFin V).symm i)

/-- Every finite metric space admits an isometric distance-coordinate embedding in a sup space. -/
theorem finiteDistanceCoordinates_isometry {V : Type*} [Fintype V] [PseudoMetricSpace V] :
    Isometry (finiteDistanceCoordinates (V := V)) := by
  apply Isometry.of_dist_eq
  intro v w
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    exact abs_dist_sub_le v w ((Fintype.equivFin V).symm i)
  · simpa [finiteDistanceCoordinates, Real.dist_eq, dist_comm, abs_of_nonneg dist_nonneg] using
      dist_le_pi_dist (finiteDistanceCoordinates v) (finiteDistanceCoordinates w)
        (Fintype.equivFin V v)

/-- A common uniform-continuity modulus survives arbitrary reindexing. -/
theorem EquiUniformContinuous.reindex {X Y : ℕ → Type*}
    [∀ n, PseudoMetricSpace (X n)] [∀ n, PseudoMetricSpace (Y n)]
    {f : ∀ n, X n → Y n} (hf : EquiUniformContinuous f) (r : ℕ → ℕ) :
    EquiUniformContinuous (fun n => f (r n)) := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  exact ⟨δ, hδ, fun n x y hxy => hfδ (r n) x y hxy⟩

end PropertyH
