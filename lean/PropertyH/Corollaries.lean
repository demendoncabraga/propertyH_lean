import PropertyH.QuasiMain
import PropertyH.VaryingMain
import PropertyH.JohnsonAssembly
import PropertyH.BrouwerFixedPoint
import PropertyH.OsajdaGroup
import PropertyH.ExpanderExistence

noncomputable section
namespace PropertyH
/-- Source: `Cor.Prop.H`.
`If a Banach space X contains equi-biLipschitzly a sequence of expander graphs,
then X does not have Property (H).`
Proof plan: approximate finite graph images in the finite-dimensional paving,
restrict the sphere map, apply the main theorem, and contradict non-null-homotopy. -/
theorem not_hasPropertyH_of_containsExpanders (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : ContainsExpanders X) : ¬ HasPropertyH X := by
  apply not_hasPropertyH_of_containsExpanders_of_sphere_noncontractible X ?_ hX
  intro S hS
  let : FiniteDimensional ℝ S := hS
  exact finiteDimensional_sphere_not_contractible

/-- Source: `Cor.no.PropH.cL.universal`.
A stronger formulation: already the finitely generated countable groups suffice.
Proof plan: use Osajda's group with isometric expanders, and extend the averaging
argument to the additive error in quasi-isometric embeddings. -/
theorem not_universal_groups_of_hasPropertyH (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hOsajda : OsajdaExpanderGroup) (hX : HasPropertyH X) : ¬ ContainsAllFinitelyGeneratedGroups X := by
  obtain ⟨Γ, g, hcount, S, hc, E, ι, hι⟩ := exists_group_with_isometric_expanders hOsajda
  let : Group Γ := g
  let : Countable Γ := hcount
  apply not_universal_groups_of_hasPropertyH_of_expander_group X ?_ hX Γ S hc E ι hι
  intro T hT
  let : FiniteDimensional ℝ T := hT
  exact finiteDimensional_sphere_not_contractible

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
  not_hasPropertyH_of_containsExpanders CZero
    (containsExpanders_cZero PermutationExpanders.constructedExpanderFamily)

end PropertyH
