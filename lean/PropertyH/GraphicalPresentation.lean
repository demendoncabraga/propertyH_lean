import PropertyH.Basic
import Mathlib.GroupTheory.PresentedGroup

/-! Graphical-presentation foundations for Osajda, §3: closed labelled walks
become relations, so the image of a vertex does not depend on a chosen path.
Source: https://arxiv.org/pdf/1406.5015, paragraph preceding Lemma 3.1.
No small-cancellation or isometric-embedding assertion is assumed here. -/
namespace PropertyH.GraphicalPresentation

variable {V A : Type*} (G : SimpleGraph V)

/-- Labels of oriented edges, with reversing an edge inverting its label. -/
structure Labeling where
  edge : ∀ {u v}, G.Adj u v → FreeGroup A
  reverse : ∀ {u v} (h : G.Adj u v), edge h.symm = (edge h)⁻¹

namespace Labeling

variable {G} (L : Labeling (A := A) G)

def word {u v : V} : G.Walk u v → FreeGroup A
  | .nil => 1
  | .cons h p => L.edge h * word p

@[simp] theorem word_nil (u : V) : L.word (.nil : G.Walk u u) = 1 := rfl
@[simp] theorem word_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    L.word (.cons h p) = L.edge h * L.word p := rfl

@[simp] theorem word_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    L.word (p.append q) = L.word p * L.word q := by
  induction p with
  | nil => simp [SimpleGraph.Walk.append]
  | cons h p ih => simp [SimpleGraph.Walk.append, ih, mul_assoc]

@[simp] theorem word_reverse {u v : V} (p : G.Walk u v) :
    L.word p.reverse = (L.word p)⁻¹ := by
  induction p with
  | nil => simp
  | cons h p ih => simpa only [SimpleGraph.Walk.reverse_cons, word_append, word_cons, word_nil, mul_one, ih, mul_inv_rev] using congrArg ((L.word p)⁻¹ * ·) (L.reverse h)

/-- Relations consist of the words read around all closed walks. -/
def relators : Set (FreeGroup A) := {w | ∃ (v : V) (p : G.Walk v v), L.word p = w}

theorem closed_word_eq_one {v : V} (p : G.Walk v v) :
    PresentedGroup.mk L.relators (L.word p) = 1 :=
  PresentedGroup.one_of_mem ⟨v, p, rfl⟩

theorem path_independent {u v : V} (p q : G.Walk u v) :
    PresentedGroup.mk L.relators (L.word p) =
      PresentedGroup.mk L.relators (L.word q) := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨u, p.append q.reverse, by simp⟩

/-- Path independence also holds after adjoining relations from other graphs. -/
theorem path_independent_of_relators_subset (R : Set (FreeGroup A))
    (hR : L.relators ⊆ R) {u v : V} (p q : G.Walk u v) :
    PresentedGroup.mk R (L.word p) = PresentedGroup.mk R (L.word q) := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact hR ⟨u, p.append q.reverse, by simp⟩

/-- A vertex map, after choosing a walk from a base vertex to each vertex. -/
def vertexMap (b : V) (paths : ∀ v, G.Walk b v) (v : V) : PresentedGroup L.relators :=
  PresentedGroup.mk L.relators (L.word (paths v))

theorem vertexMap_independent (b : V) (paths paths' : ∀ v, G.Walk b v) (v : V) :
    L.vertexMap b paths v = L.vertexMap b paths' v :=
  L.path_independent (paths v) (paths' v)

/-- Traversing an edge multiplies the vertex image by its edge label. -/
theorem vertexMap_edge (b : V) (paths : ∀ v, G.Walk b v) {u v : V}
    (h : G.Adj u v) :
    L.vertexMap b paths v = L.vertexMap b paths u *
      PresentedGroup.mk L.relators (L.edge h) := by
  have he := L.path_independent (paths v) ((paths u).append (.cons h .nil))
  simpa [vertexMap] using he

/-- In a graphical presentation the image of an edge is an edge or a collapsed edge.
Small cancellation is needed later to rule out collapse and prove distance preservation. -/
theorem vertexMap_adj_or_eq (b : V) (paths : ∀ v, G.Walk b v)
    (S : Set (PresentedGroup L.relators))
    (hlabels : ∀ {u v} (h : G.Adj u v),
      PresentedGroup.mk L.relators (L.edge h) ∈ S ∨
        (PresentedGroup.mk L.relators (L.edge h))⁻¹ ∈ S)
    {u v : V} (h : G.Adj u v) :
    (SimpleGraph.mulCayley S).Adj (L.vertexMap b paths u) (L.vertexMap b paths v) ∨
      L.vertexMap b paths u = L.vertexMap b paths v := by
  by_cases he : L.vertexMap b paths u = L.vertexMap b paths v
  · exact Or.inr he
  · apply Or.inl
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨he, ?_⟩
    rw [L.vertexMap_edge b paths h]
    simpa using hlabels h

end Labeling
end PropertyH.GraphicalPresentation

