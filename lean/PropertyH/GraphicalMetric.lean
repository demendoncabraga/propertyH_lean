import PropertyH.GraphicalPresentation
import PropertyH.PresentedCayley

namespace PropertyH.GraphicalPresentation.Labeling
variable {V A : Type*} {G : SimpleGraph V} (L : Labeling (A := A) G)
variable (R : Set (FreeGroup A)) (hR : L.relators ⊆ R)

def vertexMapInto (b : V) (paths : ∀ v, G.Walk b v) (v : V) : PresentedGroup R :=
  PresentedGroup.mk R (L.word (paths v))

include hR in
theorem vertexMapInto_independent (b : V) (paths paths' : ∀ v, G.Walk b v) (v : V) :
    L.vertexMapInto R b paths v = L.vertexMapInto R b paths' v :=
  L.path_independent_of_relators_subset R hR (paths v) (paths' v)

include hR in
theorem vertexMapInto_edge (b : V) (paths : ∀ v, G.Walk b v) {u v : V}
    (h : G.Adj u v) :
    L.vertexMapInto R b paths v = L.vertexMapInto R b paths u *
      PresentedGroup.mk R (L.edge h) := by
  have he := L.path_independent_of_relators_subset R hR (paths v)
    ((paths u).append (.cons h .nil))
  simpa [vertexMapInto] using he

include hR in
theorem vertexMapInto_adj_or_eq (b : V) (paths : ∀ v, G.Walk b v)
    (S : Set (PresentedGroup R))
    (hlabels : ∀ {u v} (h : G.Adj u v),
      PresentedGroup.mk R (L.edge h) ∈ S ∨ (PresentedGroup.mk R (L.edge h))⁻¹ ∈ S)
    {u v : V} (h : G.Adj u v) :
    (SimpleGraph.mulCayley S).Adj (L.vertexMapInto R b paths u)
      (L.vertexMapInto R b paths v) ∨
      L.vertexMapInto R b paths u = L.vertexMapInto R b paths v := by
  by_cases he : L.vertexMapInto R b paths u = L.vertexMapInto R b paths v
  · exact Or.inr he
  · apply Or.inl
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨he, ?_⟩
    rw [L.vertexMapInto_edge R hR b paths h]
    simpa using hlabels h
end PropertyH.GraphicalPresentation.Labeling

namespace PropertyH
/-- A graph map allowing collapsed edges does not increase graph distances
when the source is connected. -/
theorem graph_dist_le_of_adj_or_eq {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : V → W)
    (hf : ∀ {u v}, G.Adj u v → H.Adj (f u) (f v) ∨ f u = f v)
    (hc : G.Connected) (u v : V) : H.dist (f u) (f v) ≤ G.dist u v := by
  have hw : ∀ {u v} (p : G.Walk u v), ∃ q : H.Walk (f u) (f v), q.length ≤ p.length := by
    intro u v p
    induction p with
    | nil => exact ⟨.nil, le_rfl⟩
    | @cons u v w h p ih =>
      obtain ⟨q, hq⟩ := ih
      rcases hf h with hh | hh
      · exact ⟨.cons hh q, Nat.succ_le_succ hq⟩
      · rw [hh]
        exact ⟨q, hq.trans (Nat.le_succ _)⟩
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  obtain ⟨q, hq⟩ := hw p
  exact (H.dist_le q).trans (hp ▸ hq)
end PropertyH

namespace PropertyH
/-- Read a Cayley walk as a word in generators and their inverses. -/
theorem cayley_walk_word {Γ : Type*} [Group Γ] (S : Set Γ)
    {u v : Γ} (p : (SimpleGraph.mulCayley S).Walk u v) :
    ∃ xs : List Γ, (∀ x ∈ xs, x ∈ S ∨ x⁻¹ ∈ S) ∧
      xs.prod = u⁻¹ * v ∧ xs.length = p.length := by
  induction p with
  | nil => exact ⟨[], by simp, by simp, rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨xs, hxs, hp, hl⟩ := ih
    refine ⟨(u⁻¹ * v) :: xs, ?_, ?_, congrArg Nat.succ hl⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using ((SimpleGraph.mulCayley_adj S u v).mp h).2
      · exact hxs x hx
    · simp [hp, mul_assoc]

/-- A signed generator word bounds the distance to its evaluated endpoint. -/
theorem cayley_dist_le_word_length {Γ : Type*} [Group Γ] (S : Set Γ)
    (hc : (SimpleGraph.mulCayley S).Connected)
    (xs : List Γ) (hxs : ∀ x ∈ xs, x ∈ S ∨ x⁻¹ ∈ S) (u : Γ) :
    (SimpleGraph.mulCayley S).dist u (u * xs.prod) ≤ xs.length := by
  induction xs generalizing u with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) (u * x)
    have hx := hxs x (List.mem_cons_self ..)
    have hedge : (SimpleGraph.mulCayley S).dist u (u * x) ≤ 1 := by
      by_cases he : u = u * x
      · rw [← he]; simp
      · have ha : (SimpleGraph.mulCayley S).Adj u (u * x) := by
          rw [SimpleGraph.mulCayley_adj]
          exact ⟨he, by simpa using hx⟩
        exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr ha)
    have htri := hc.dist_triangle (u := u) (v := u * x) (w := (u * x) * xs.prod)
    simpa [mul_assoc, Nat.add_comm] using htri.trans (Nat.add_le_add hedge ht)

/-- Exact reverse-distance criterion: no signed generator word representing the
relative images of two vertices is shorter than their original graph distance. -/
theorem graph_dist_le_cayley_iff_no_shortening {V Γ : Type*} [Group Γ]
    (G : SimpleGraph V) (S : Set Γ) (hc : (SimpleGraph.mulCayley S).Connected)
    (f : V → Γ) :
    (∀ u v, G.dist u v ≤ (SimpleGraph.mulCayley S).dist (f u) (f v)) ↔
      ∀ u v (xs : List Γ), (∀ x ∈ xs, x ∈ S ∨ x⁻¹ ∈ S) →
        xs.prod = (f u)⁻¹ * f v → G.dist u v ≤ xs.length := by
  constructor
  · intro h u v xs hxs hp
    have hb := cayley_dist_le_word_length S hc xs hxs (f u)
    rw [hp, ← mul_assoc, mul_inv_cancel, one_mul] at hb
    exact (h u v).trans hb
  · intro h u v
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist (f u) (f v)
    obtain ⟨xs, hxs, he, hl⟩ := cayley_walk_word S p
    exact (h u v xs hxs he).trans (le_of_eq (hl.trans hp))
end PropertyH

namespace PropertyH.GraphicalPresentation.Labeling
variable {V A : Type*} {G : SimpleGraph V} (L : Labeling (A := A) G)
variable [Fintype A] (R : Set (FreeGroup A)) (hR : L.relators ⊆ R)
variable (b : V) (paths : ∀ v, G.Walk b v)

/-- Literal alphabet labels, allowing either orientation, are Cayley generators. -/
theorem alphabet_labels_mem_generators
    (hletters : ∀ {u v} (h : G.Adj u v),
      ∃ a : A, L.edge h = FreeGroup.of a ∨ L.edge h = (FreeGroup.of a)⁻¹)
    {u v : V} (h : G.Adj u v) :
    PresentedGroup.mk R (L.edge h) ∈ (presentationGenerators R : Set _) ∨
      (PresentedGroup.mk R (L.edge h))⁻¹ ∈ (presentationGenerators R : Set _) := by
  classical
  obtain ⟨a, ha | ha⟩ := hletters h
  · left
    simp [ha, presentationGenerators, PresentedGroup.of]
  · right
    simp [ha, presentationGenerators, PresentedGroup.of]

include hR

/-- The canonical map from any relator graph into the common presented group
never increases distance. This requires no small-cancellation hypothesis. -/
theorem vertexMapInto_dist_le
    (hletters : ∀ {u v} (h : G.Adj u v),
      ∃ a : A, L.edge h = FreeGroup.of a ∨ L.edge h = (FreeGroup.of a)⁻¹)
    (hc : G.Connected) (u v : V) :
    (SimpleGraph.mulCayley (presentationGenerators R : Set _)).dist
      (L.vertexMapInto R b paths u) (L.vertexMapInto R b paths v) ≤ G.dist u v := by
  apply graph_dist_le_of_adj_or_eq _ ?_ hc
  exact fun h => L.vertexMapInto_adj_or_eq R hR b paths _
    (fun h => L.alphabet_labels_mem_generators R hletters h) h

/-- Isometry of a graphical relator is equivalent to the precise no-shortening
condition which the graphical small-cancellation theorem must supply. -/
theorem vertexMapInto_isometric_iff_no_shortening
    (hletters : ∀ {u v} (h : G.Adj u v),
      ∃ a : A, L.edge h = FreeGroup.of a ∨ L.edge h = (FreeGroup.of a)⁻¹)
    (hc : G.Connected) :
    (∀ u v, (SimpleGraph.mulCayley (presentationGenerators R : Set _)).dist
      (L.vertexMapInto R b paths u) (L.vertexMapInto R b paths v) = G.dist u v) ↔
    ∀ u v (xs : List (PresentedGroup R)),
      (∀ x ∈ xs, x ∈ (presentationGenerators R : Set _) ∨
        x⁻¹ ∈ (presentationGenerators R : Set _)) →
      xs.prod = (L.vertexMapInto R b paths u)⁻¹ * L.vertexMapInto R b paths v →
      G.dist u v ≤ xs.length := by
  rw [← graph_dist_le_cayley_iff_no_shortening G _ (presentation_cayley_connected R)]
  constructor
  · intro h u v
    exact le_of_eq (h u v).symm
  · intro h u v
    exact Nat.le_antisymm (L.vertexMapInto_dist_le R hR b paths hletters hc u v) (h u v)
end PropertyH.GraphicalPresentation.Labeling

