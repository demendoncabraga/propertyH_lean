import PropertyH.GraphicalMetric
import PropertyH.Connectivity

namespace PropertyH
/-- From finite-alphabet graphical data satisfying the no-shortening condition,
construct the countable finitely generated group required by Osajda's conclusion.
The labeling and no-shortening hypotheses are explicit and must still be proved. -/
theorem group_from_graphical_expanders
    (E : ExpanderFamily) (m : ℕ)
    (L : ∀ n, GraphicalPresentation.Labeling (A := Fin m) (E.graph n))
    (R : Set (FreeGroup (Fin m))) (hR : ∀ n, (L n).relators ⊆ R)
    (b : ∀ n, E.V n) (paths : ∀ n v, (E.graph n).Walk (b n) v)
    (hletters : ∀ n {u v} (h : (E.graph n).Adj u v),
      ∃ a : Fin m, (L n).edge h = FreeGroup.of a ∨ (L n).edge h = (FreeGroup.of a)⁻¹)
    (hshort : ∀ n u v (xs : List (PresentedGroup R)),
      (∀ x ∈ xs, x ∈ (presentationGenerators R : Set _) ∨
        x⁻¹ ∈ (presentationGenerators R : Set _)) →
      xs.prod = ((L n).vertexMapInto R (b n) (paths n) u)⁻¹ *
        (L n).vertexMapInto R (b n) (paths n) v → (E.graph n).dist u v ≤ xs.length) :
    ∃ (Γ : Type) (g : Group Γ) (_ : Countable Γ),
      letI := g
      ∃ S : Finset Γ, (SimpleGraph.mulCayley (S : Set Γ)).Connected ∧
        ∃ (ι : ∀ n, E.V n → Γ),
          ∀ n v u, (SimpleGraph.mulCayley (S : Set Γ)).dist (ι n v) (ι n u) =
            (E.graph n).dist v u := by
  refine ⟨PresentedGroup R, inferInstance, presentation_countable R,
    presentationGenerators R, presentation_cayley_connected R,
    fun n => (L n).vertexMapInto R (b n) (paths n), ?_⟩
  intro n v u
  let : Nonempty (E.V n) := ⟨b n⟩
  exact ((L n).vertexMapInto_isometric_iff_no_shortening R (hR n) (b n)
    (paths n) (hletters n) (E.expands n).connected).mpr (hshort n) v u
end PropertyH
