import PropertyH.VaryingMain
import PropertyH.FiniteSup
import PropertyH.GraphMetricSpace

noncomputable section
namespace PropertyH
open MeasureTheory

/-- Johnson's conclusion follows from the main theorem once graph embeddings into finite
sup spaces and sphere noncontractibility are supplied. -/
theorem no_equiUniform_sphere_homeomorphisms_of_sup_embeddings
    (E : ExpanderFamily)
    (hE : EquiGraphEmbeddings E (fun n => Fin (Fintype.card (E.V n)) → ℝ))
    (hsphere : ∀ n : ℕ, ¬ ContractibleSpace (UnitSphere (Fin n → ℝ))) :
    ¬ ∃ F : ∀ n : ℕ, UnitSphere (Fin n → ℝ) ≃ₜ UnitSphere (EuclideanSpace ℝ (Fin n)),
      EquiUniformContinuous (fun n => F n) := by
  rintro ⟨F, hF⟩
  let d : ℕ → ℕ := fun n => Fintype.card (E.V n)
  let μ := fun n => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (d n)))
  let j := fun n => hilbertGaussianL1Isometry (E := EuclideanSpace ℝ (Fin (d n)))
  let f : ∀ n, C(UnitSphere (Fin (d n) → ℝ), UnitSphere (EuclideanSpace ℝ (Fin (d n)))) :=
    fun n => F (d n)
  have hmod : EquiUniformContinuous (fun n => f n) := hF.reindex d
  have hnull := sphere_maps_eventually_nullhomotopic_varying E
    (fun n => Fin (d n) → ℝ) (fun n => EuclideanSpace ℝ (Fin (d n)))
    (Ω := fun n => EuclideanSpace ℝ (Fin (d n))) μ j hE f hmod
  obtain ⟨n, hn⟩ := hnull.exists
  exact hsphere (d n) ((homeomorph_nullhomotopic_iff (F (d n))).mp hn)

/-- Source: `Corollary.Johnson`, with exactly the expander-existence and sphere-topology
prerequisites exposed. The finite embeddings and all analytic steps are proved. -/
theorem no_equiUniform_sphere_homeomorphisms_of_expander_of_sphere_noncontractible
    (E : ExpanderFamily)
    (hsphere : ∀ n : ℕ, ¬ ContractibleSpace (UnitSphere (Fin n → ℝ))) :
    ¬ ∃ F : ∀ n : ℕ, UnitSphere (Fin n → ℝ) ≃ₜ UnitSphere (EuclideanSpace ℝ (Fin n)),
      EquiUniformContinuous (fun n => F n) :=
  no_equiUniform_sphere_homeomorphisms_of_sup_embeddings E (expander_sup_embeddings E) hsphere

end PropertyH

