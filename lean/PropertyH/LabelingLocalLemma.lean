import PropertyH.LovaszLocal
import PropertyH.LabelingAvoidance

namespace PropertyH.LabelingLocalLemma
noncomputable section
variable {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]

/-- Uniform mass in a finite space, expressed as a real number. -/
def uniformMass (P : Set Ω) : ℝ := (Nat.card P : ℝ) / Fintype.card Ω

theorem uniformMass_equiv (e : Ω ≃ X) (P : Set X) :
    uniformMass (e ⁻¹' P) = uniformMass P := by
  classical
  unfold uniformMass
  congr 1
  · exact_mod_cast Nat.card_congr (Equiv.subtypeEquivOfSubtype (p := (· ∈ P)) e)
  · exact_mod_cast Fintype.card_congr e

/-- The two coordinate blocks of a uniform finite product are independent. -/
theorem uniformMass_product [Nonempty X] [Nonempty Y] (P : Set X) (Q : Set Y) :
    uniformMass {z : X × Y | z.1 ∈ P ∧ z.2 ∈ Q} =
      uniformMass {z : X × Y | z.1 ∈ P} * uniformMass {z : X × Y | z.2 ∈ Q} := by
  classical
  have hboth := Fintype.card_congr
    (Equiv.subtypeProdEquivProd (p := (· ∈ P)) (q := (· ∈ Q)))
  have hleft := Fintype.card_congr
    (Equiv.prodSubtypeFstEquivSubtypeProd (α := X) (β := Y) (p := (· ∈ P)))
  have hright : Fintype.card {z : X × Y // z.2 ∈ Q} = Fintype.card X * Fintype.card Q := by
    have he : {z : X × Y // z.2 ∈ Q} ≃ X × Q :=
      ⟨fun z => (z.1.1, ⟨z.1.2, z.2⟩), fun z => ⟨(z.1, z.2), z.2.property⟩,
        fun _ => rfl, fun _ => rfl⟩
    simpa using Fintype.card_congr he
  unfold uniformMass
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod] at hboth hleft ⊢
  change (Fintype.card {z : X × Y // z.1 ∈ P ∧ z.2 ∈ Q} : ℝ) / _ =
    (Fintype.card {z : X × Y // z.1 ∈ P} : ℝ) / _ *
      ((Fintype.card {z : X × Y // z.2 ∈ Q} : ℝ) / _)
  rw [hboth, hleft, hright]
  push_cast
  have hx : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := X)
  have hy : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := Y)
  field_simp
variable {E A : Type*} [Fintype E] [Fintype A]
local instance : DecidableEq E := Classical.decEq E

/-- Membership in an event is determined by labels on its support. -/
def Supported (s : Set E) (P : Set (E → A)) : Prop :=
  ∀ f g, (∀ e ∈ s, f e = g e) → (f ∈ P ↔ g ∈ P)

theorem uniformMass_independent_of_complement_support [Nonempty A]
    (s : Set E) (P Q : Set (E → A)) (hP : Supported s P) (hQ : Supported sᶜ Q) :
    uniformMass (P ∩ Q) = uniformMass P * uniformMass Q := by
  classical
  let a : A := Classical.choice inferInstance
  let e := Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => A)
  let P' : Set (s → A) := {f | e.symm (f, fun _ => a) ∈ P}
  let Q' : Set (↥(sᶜ) → A) := {f | e.symm (fun _ => a, f) ∈ Q}
  have hp : e ⁻¹' {z | z.1 ∈ P'} = P := by
    ext f
    exact (hP _ _ (fun k hk => by simp [e, hk])).symm
  have hq : e ⁻¹' {z | z.2 ∈ Q'} = Q := by
    ext f
    exact (hQ _ _ (fun k hk => by simp [e, show k ∉ s from hk])).symm
  have hb : e ⁻¹' {z | z.1 ∈ P' ∧ z.2 ∈ Q'} = P ∩ Q := by
    rw [← hp, ← hq]
    rfl
  rw [← hb, ← hp, ← hq, uniformMass_equiv, uniformMass_equiv, uniformMass_equiv]
  exact uniformMass_product P' Q'

/-- Disjoint coordinate sets imply event independence. The second set can be a
union of supports, so this supplies joint dependency-graph independence. -/
theorem uniformMass_independent_of_disjoint_support [Nonempty A]
    (s t : Set E) (P Q : Set (E → A)) (hd : Disjoint s t)
    (hP : Supported s P) (hQ : Supported t Q) :
    uniformMass (P ∩ Q) = uniformMass P * uniformMass Q := by
  apply uniformMass_independent_of_complement_support s P Q hP
  intro f g hfg
  exact hQ f g (fun e he => hfg e (fun hes => Set.disjoint_left.mp hd hes he))

/-- The normalized constant weights agree with uniform cardinal probabilities. -/
theorem mass_uniform (F : Finset Ω) :
    LovaszLocal.mass (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹) F = uniformMass (F : Set Ω) := by
  classical
  simp [LovaszLocal.mass, uniformMass, Nat.card_eq_fintype_card, div_eq_mul_inv]

def overlapNeighbors {I : Type*} [Fintype I] (s : I → Set E) (i : I) : Finset I := by
  classical
  exact Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (s i) (s j))

/-- Full finite local lemma for arbitrary events with specified coordinate supports. -/
theorem exists_avoiding_supported_events [Nonempty A]
    {I : Type*} [Fintype I] (s : I → Set E) (P : I → Set (E → A))
    (hs : ∀ i, Supported (s i) (P i)) (x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hb : ∀ i, uniformMass (P i) ≤ x i *
      ∏ j ∈ overlapNeighbors s i, (1 - x j)) :
    ∃ f : E → A, ∀ i, f ∉ P i := by
  classical
  let events : I → Finset (E → A) := fun i => (P i).toFinset
  have hnorm : ∑ f : E → A, (Fintype.card (E → A) : ℝ)⁻¹ = 1 := by
    simp [Fintype.card_ne_zero]
  have hind : ∀ i T, i ∉ T → Disjoint T (overlapNeighbors s i) →
      LovaszLocal.mass (fun _ : E → A => (Fintype.card (E → A) : ℝ)⁻¹)
        (events i ∩ LovaszLocal.avoid events T) =
      LovaszLocal.mass (fun _ : E → A => (Fintype.card (E → A) : ℝ)⁻¹) (events i) *
        LovaszLocal.mass (fun _ : E → A => (Fintype.card (E → A) : ℝ)⁻¹)
          (LovaszLocal.avoid events T) := by
    intro i T hi hd
    simp_rw [mass_uniform]
    have hQ : Supported (s i)ᶜ (LovaszLocal.avoid events T : Set (E → A)) := by
      intro f g hfg
      simp only [Finset.mem_coe, LovaszLocal.mem_avoid]
      have heq : ∀ j ∈ T, (f ∈ events j ↔ g ∈ events j) := by
        intro j hj
        have hji : j ≠ i := fun he => hi (he ▸ hj)
        have hdis : Disjoint (s i) (s j) := by
          by_contra hn
          exact Finset.disjoint_left.mp hd hj (by simp [overlapNeighbors, hji, hn])
        simpa only [events, Set.mem_toFinset] using hs j f g
          (fun e he => hfg e (fun hei => Set.disjoint_left.mp hdis hei he))
      exact forall_congr' (fun j => forall_congr' (fun hj => not_congr (heq j hj)))
    have hh := uniformMass_independent_of_complement_support (s i)
      (P i) (LovaszLocal.avoid events T : Set (E → A)) (hs i) hQ
    simpa [events] using hh
  obtain ⟨f, hf⟩ := LovaszLocal.exists_avoiding_of_local_lemma
    (fun _ : E → A => (Fintype.card (E → A) : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hnorm events (overlapNeighbors s) x
    hx0 hx1 hind (fun i => by rw [mass_uniform]; simpa only [events, Set.coe_toFinset] using hb i) Finset.univ
  exact ⟨f, fun i => by simpa [events] using hf i (Finset.mem_univ i)⟩

/-- Exact local-word probability in real-valued form for the local lemma. -/
theorem uniformMass_restriction [Nonempty A] (s : Set E) (B : Set (s → A)) :
    uniformMass {f : E → A | (fun e : s => f e) ∈ B} =
      (Nat.card B : ℝ) / (Fintype.card A : ℝ) ^ Nat.card s := by
  classical
  have hnum := LabelingAvoidance.card_restriction_event (A := A) s B
  have hden := Fintype.card_congr (Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => A))
  simp only [Fintype.card_prod, Fintype.card_fun] at hden
  unfold uniformMass
  change (Nat.card {f : E → A // (fun e : s => f e) ∈ B} : ℝ) /
    Fintype.card (E → A) = _
  rw [hnum, Fintype.card_fun, hden]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.card_eq_fintype_card]
  exact mul_div_mul_right _ _ (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero (α := A)))

/-- Concrete finite random-labeling local lemma: forbidden words on overlapping
supports are the only dependencies, and their probabilities are counted exactly. -/
theorem exists_avoiding_local_patterns [Nonempty A]
    {I : Type*} [Fintype I] (s : I → Set E) (B : ∀ i, Set (s i → A))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hb : ∀ i, (Nat.card (B i) : ℝ) / (Fintype.card A : ℝ) ^ Nat.card (s i) ≤
      x i * ∏ j ∈ overlapNeighbors s i, (1 - x j)) :
    ∃ f : E → A, ∀ i, (fun e : s i => f e) ∉ B i := by
  refine exists_avoiding_supported_events s (fun i => {f | (fun e : s i => f e) ∈ B i})
    ?_ x hx0 hx1 ?_
  · intro i f g hfg
    have he : (fun e : s i => f e) = (fun e : s i => g e) :=
      funext (fun e => hfg e e.property)
    change (fun e : s i => f e) ∈ B i ↔ (fun e : s i => g e) ∈ B i
    rw [he]
  · intro i
    rw [uniformMass_restriction]
    exact hb i

end
end PropertyH.LabelingLocalLemma

