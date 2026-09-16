import PropertyH.GraphicalPresentation
import Mathlib.GroupTheory.FreeGroup.Reduce

noncomputable section
namespace PropertyH.GraphicalPresentation

/-- Single-letter oriented labels, with inverses on reversal and distinct outgoing labels. -/
structure ReducedLabeling {V : Type*} (G : SimpleGraph V) (A : Type*) where
  letter : G.Dart → A × Bool
  reverse : ∀ d, letter d.symm = ((letter d).1, !(letter d).2)
  locallyReduced : ∀ d e, d.fst = e.fst → letter d = letter e → d = e

namespace ReducedLabeling
variable {V A : Type*} {G : SimpleGraph V} (L : ReducedLabeling G A)

/-- Adjacent oriented edges with no immediate reversal cannot have cancelling labels. -/
theorem adjacent_letters_reduced (d e : G.Dart) (hjoin : d.snd = e.fst) (hnb : d.symm ≠ e) :
    (L.letter d).1 = (L.letter e).1 → (L.letter d).2 = (L.letter e).2 := by
  intro hgen
  by_contra hsign
  apply hnb
  apply L.locallyReduced _ _ hjoin
  rw [L.reverse]
  apply Prod.ext
  · exact hgen
  · cases hd : (L.letter d).2 <;> cases he : (L.letter e).2 <;> simp_all

/-- The signed-letter word literally read along a graph walk. -/
def letters {u v : V} (p : G.Walk u v) : List (A × Bool) := p.darts.map L.letter

/-- Along an actual walk, adjacency is automatic; the second conjunct rules out backtracking. -/
def Nonbacktracking {u v : V} (p : G.Walk u v) : Prop :=
  p.darts.IsChain (fun d e => d.snd = e.fst ∧ d.symm ≠ e)

/-- Every graph path has no backtracking. -/
theorem nonbacktracking_of_isPath {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    Nonbacktracking p := by
  induction p with
  | nil => exact .nil
  | @cons u v w h p ih =>
    have ht := ih hp.of_cons
    cases p with
    | nil => exact .singleton _
    | @cons v z w h' q =>
      apply List.IsChain.cons_cons _ ht
      refine ⟨rfl, ?_⟩
      intro heq
      have he : u = z := congrArg (fun d : G.Dart => d.snd) heq
      have hn := (List.nodup_cons.mp hp.support_nodup).1
      apply hn
      rw [he]
      exact List.mem_cons_of_mem _ q.start_mem_support

theorem letters_isReduced {u v : V} (p : G.Walk u v) (hp : Nonbacktracking p) :
    FreeGroup.IsReduced (L.letters p) := by
  rw [FreeGroup.IsReduced, letters, List.isChain_map]
  exact List.IsChain.imp (fun {d e} h => L.adjacent_letters_reduced d e h.1 h.2) hp

/-- Forget the single-letter/reduced properties to obtain the existing graphical labeling. -/
def toLabeling : Labeling (A := A) G where
  edge h := FreeGroup.mk [L.letter ⟨⟨_, _⟩, h⟩]
  reverse h := by
    rw [FreeGroup.inv_mk]
    change FreeGroup.mk [L.letter (SimpleGraph.Dart.symm ⟨⟨_, _⟩, h⟩)] = _
    rw [L.reverse]
    rfl

theorem word_eq_mk_letters {u v : V} (p : G.Walk u v) :
    L.toLabeling.word p = FreeGroup.mk (L.letters p) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [Labeling.word_cons, ih]
    change FreeGroup.mk [L.letter ⟨⟨_, _⟩, h⟩] * FreeGroup.mk (L.letters p) = _
    rw [FreeGroup.mul_mk]
    rfl

/-- A nonbacktracking walk undergoes no free reduction in a locally reduced labeling. -/
theorem toWord_eq_letters [DecidableEq A] {u v : V} (p : G.Walk u v) (hp : Nonbacktracking p) :
    (L.toLabeling.word p).toWord = L.letters p := by
  rw [L.word_eq_mk_letters, FreeGroup.toWord_mk, (L.letters_isReduced p hp).reduce_eq]

/-- The reduced free-group word has exactly as many letters as the walk has edges. -/
theorem reduced_word_length_eq_walk_length [DecidableEq A] {u v : V}
    (p : G.Walk u v) (hp : Nonbacktracking p) :
    (L.toLabeling.word p).toWord.length = p.length := by
  rw [L.toWord_eq_letters p hp]
  simp [letters]
end ReducedLabeling
end PropertyH.GraphicalPresentation
