import PropertyH.BrouwerFixedPoint
import PropertyH.ExpanderExistence
import PropertyH.JohnsonAssembly

noncomputable section
namespace PropertyH
/-- Source: `Corollary.Johnson`.
`There is no sequence of homeomorphisms
(F_n : S_{ell_infty^n} → S_{ell_2^n})_n which is equi-uniformly continuous.`
Proof plan: use finite metric embeddings into sup-norm spaces, apply the main
result along the expander-cardinality subsequence, and use sphere noncontractibility. -/
theorem no_equiUniform_sphere_homeomorphisms :
    ¬ ∃ F : ∀ n : ℕ, UnitSphere (Fin n → ℝ) ≃ₜ UnitSphere (EuclideanSpace ℝ (Fin n)),
      EquiUniformContinuous (fun n => F n) := by
  obtain ⟨E⟩ := PermutationExpanders.exists_expanderFamily
  exact no_equiUniform_sphere_homeomorphisms_of_expander_of_sphere_noncontractible E
    (fun _ => finiteDimensional_sphere_not_contractible)

/-- Source: the introductory conclusion that c₀ fails Property (H). -/
theorem not_hasPropertyH_cZero : ¬ HasPropertyH CZero :=
  not_hasPropertyH_of_containsCoarseExpanders CZero
    ⟨PermutationExpanders.constructedExpanderFamily,
      (expander_cZero_embeddings PermutationExpanders.constructedExpanderFamily).to_coarse⟩

end PropertyH
