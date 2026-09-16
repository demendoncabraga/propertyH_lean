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

/-- Isometric changes of domain preserve a common uniform-continuity modulus. -/
theorem EquiUniformContinuous.comp_isometries {X Y Z : ℕ → Type*}
    [∀ n, PseudoMetricSpace (X n)] [∀ n, PseudoMetricSpace (Y n)]
    [∀ n, PseudoMetricSpace (Z n)] {f : ∀ n, X n → Y n}
    (hf : EquiUniformContinuous f) (g : ∀ n, Z n → X n) (hg : ∀ n, Isometry (g n)) :
    EquiUniformContinuous (fun n x => f n (g n x)) := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  refine ⟨δ, hδ, fun n x y hxy => hfδ n (g n x) (g n y) ?_⟩
  simpa only [(hg n).dist_eq] using hxy

/-- Isometric changes of codomain preserve a common uniform-continuity modulus. -/
theorem EquiUniformContinuous.isometries_comp {X Y Z : ℕ → Type*}
    [∀ n, PseudoMetricSpace (X n)] [∀ n, PseudoMetricSpace (Y n)]
    [∀ n, PseudoMetricSpace (Z n)] {f : ∀ n, X n → Y n}
    (hf : EquiUniformContinuous f) (g : ∀ n, Y n → Z n) (hg : ∀ n, Isometry (g n)) :
    EquiUniformContinuous (fun n x => g n (f n x)) := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  refine ⟨δ, hδ, fun n x y hxy => ?_⟩
  simpa only [(hg n).dist_eq] using hfδ n x y hxy

/-- Restriction of a real linear isometry to unit spheres. -/
def sphereLinearIsometry {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X →ₗᵢ[ℝ] Y) :
    UnitSphere X → UnitSphere Y :=
  fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr
    ((e.norm_map x).trans (mem_sphere_zero_iff_norm.mp x.property))⟩

/-- The induced sphere map is isometric in the inherited metrics. -/
theorem sphereLinearIsometry_isometry {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X →ₗᵢ[ℝ] Y) :
    Isometry (sphereLinearIsometry e) := by
  apply Isometry.of_dist_eq
  intro x y
  exact e.isometry.dist_eq x y

end PropertyH
