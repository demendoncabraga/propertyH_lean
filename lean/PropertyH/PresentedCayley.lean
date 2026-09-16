import PropertyH.Expanders
import Mathlib.GroupTheory.PresentedGroup

namespace PropertyH
/-- A generating set connects its Cayley graph, including generators equal to one. -/
theorem cayley_connected_of_generates {Γ : Type*} [Group Γ] (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  have hr : ∀ g : Γ, ∀ u, (SimpleGraph.mulCayley S).Reachable u (u * g) := by
    intro g
    have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro u
      by_cases h : u = u * g
      · exact h ▸ SimpleGraph.Reachable.refl u
      · exact ((SimpleGraph.mulCayley_adj' S u (u * g)).mpr ⟨h, g, hg, Or.inl rfl⟩).reachable
    | one => intro u; simp
    | mul g h hg hh ihg ihh => exact fun u => by simpa [mul_assoc] using (ihg u).trans (ihh (u * g))
    | inv g hg ih => exact fun u => by simpa [mul_assoc] using (ih (u * g⁻¹)).symm
  exact ⟨fun u v => by simpa [mul_assoc] using hr (u⁻¹ * v) u⟩

noncomputable section
/-- The finite alphabet supplies a finite generating set in any presented quotient. -/
def presentationGenerators {α : Type*} [Fintype α] (R : Set (FreeGroup α)) :
    Finset (PresentedGroup R) := by classical exact Finset.univ.image PresentedGroup.of

theorem presentation_cayley_connected {α : Type*} [Fintype α] (R : Set (FreeGroup α)) :
    (SimpleGraph.mulCayley (presentationGenerators R : Set (PresentedGroup R))).Connected := by
  apply cayley_connected_of_generates
  simp [presentationGenerators]
/-- A countable alphabet gives a countable presented group, even with infinitely many relators. -/
theorem presentation_countable {α : Type*} [Countable α] (R : Set (FreeGroup α)) :
    Countable (PresentedGroup R) := by
  have : Countable (FreeGroup α) := by unfold FreeGroup; infer_instance
  exact (PresentedGroup.mk_surjective R).countable
end
end PropertyH
