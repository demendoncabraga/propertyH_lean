import PropertyH.Basic

/-! Finite asymmetric local lemma. The algebraic induction is separated from
its finite probability-space specialization. This supplies the finite local-lemma
prerequisite in Osajda, Lemma 2.1 (https://arxiv.org/pdf/1406.5015).
The proof uses strong induction on conditioning sets, separating neighbors from
non-neighbors; no local lemma or conditional-probability inequality is assumed. -/
namespace PropertyH.LovaszLocal
variable {I : Type*} [DecidableEq I]

/-- Iterating lower bounds for avoiding one more event. -/
theorem avoidance_product_bound (q : Finset I → ℝ) (r : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (T U : Finset I) (hd : Disjoint T U)
    (hstep : ∀ R ⊆ U, ∀ j ∈ U, j ∉ R →
      r j * q (T ∪ R) ≤ q (insert j (T ∪ R))) :
    (∏ j ∈ U, r j) * q T ≤ q (T ∪ U) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
    have hdU := (Finset.disjoint_insert_right.mp hd).2
    have hih := ih hdU (fun R hR j hj hjR => hstep R
      (hR.trans (Finset.subset_insert _ _)) j (Finset.mem_insert_of_mem hj) hjR)
    have hs := hstep U (Finset.subset_insert _ _) a (Finset.mem_insert_self ..) ha
    rw [Finset.prod_insert ha, mul_assoc, Finset.union_insert]
    exact (mul_le_mul_of_nonneg_left hih (hr a)).trans hs

/-- Conditional-probability induction, in denominator-free form. The dependency
hypothesis bounds the bad event intersected with avoidance of `S` by its
unconditional bound times avoidance of the non-neighbors in `S`. -/
theorem local_lemma_step (q : Finset I → ℝ) (p x : I → ℝ) (N : I → Finset I)
    (hq : ∀ S, 0 ≤ q S) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hdep : ∀ S i, i ∉ S → q S - q (insert i S) ≤ p i * q (S \ N i)) :
    ∀ S i, i ∉ S → (1 - x i) * q S ≤ q (insert i S) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro i hi
    let T := S \ N i
    let U := S ∩ N i
    have hTU : T ∪ U = S := by ext j; simp [T, U]; tauto
    have hd : Disjoint T U := by
      simp only [T, U, Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hprod : (∏ j ∈ U, (1 - x j)) * q T ≤ q S := by
      rw [← hTU]
      apply avoidance_product_bound q (fun j => 1 - x j) (fun j => by linarith [hx1 j]) T U hd
      intro R hR j hj hjR
      have hsub : T ∪ R ⊆ S := by
        intro k hk
        rcases Finset.mem_union.mp hk with hk | hk
        · exact (Finset.mem_sdiff.mp hk).1
        · exact (Finset.mem_inter.mp (hR hk)).1
      have hjT : j ∉ T := fun hjT => Finset.disjoint_left.mp hd hjT hj
      have hjnot : j ∉ T ∪ R := by simp [hjT, hjR]
      have hproper : T ∪ R ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
        intro he
        exact hjnot (he ▸ (Finset.mem_inter.mp hj).1)
      exact ih (T ∪ R) hproper j hjnot
    have hprods : (∏ j ∈ N i, (1 - x j)) ≤ ∏ j ∈ U, (1 - x j) := by
      apply Finset.prod_le_prod_of_subset_of_le_one
      · exact Finset.inter_subset_right
      · intro j hj; linarith [hx1 j]
      · intro j hj hjU; linarith [hx0 j]
    have hp' := (hp i).trans (mul_le_mul_of_nonneg_left hprods (hx0 i))
    have hb := (hdep S i hi).trans (mul_le_mul_of_nonneg_right hp' (hq T))
    have hc := mul_le_mul_of_nonneg_left hprod (hx0 i)
    nlinarith

/-- Quantitative finite asymmetric local lemma for avoidance probabilities. -/
theorem local_lemma_product (q : Finset I → ℝ) (p x : I → ℝ) (N : I → Finset I)
    (hq : ∀ S, 0 ≤ q S) (hq0 : q ∅ = 1)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hdep : ∀ S i, i ∉ S → q S - q (insert i S) ≤ p i * q (S \ N i))
    (S : Finset I) : (∏ j ∈ S, (1 - x j)) ≤ q S := by
  have hh := avoidance_product_bound q (fun j => 1 - x j)
    (fun j => by linarith [hx1 j]) ∅ S (by simp)
    (fun R _ j _ hj => by simpa using local_lemma_step q p x N hq hx0 hx1 hp hdep R j hj)
  simpa [hq0] using hh

section FiniteProbability
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def mass (w : Ω → ℝ) (s : Finset Ω) : ℝ := ∑ ω ∈ s, w ω

def avoid (A : I → Finset Ω) (S : Finset I) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ i ∈ S, ω ∉ A i)

omit [DecidableEq I] in
@[simp] theorem mem_avoid (A : I → Finset Ω) (S : Finset I) (ω : Ω) :
    ω ∈ avoid A S ↔ ∀ i ∈ S, ω ∉ A i := by simp [avoid]

omit [DecidableEq I] in
@[simp] theorem avoid_empty (A : I → Finset Ω) : avoid A ∅ = Finset.univ := by
  ext ω; simp

theorem avoid_insert (A : I → Finset Ω) (S : Finset I) (i : I) :
    avoid A (insert i S) = avoid A S \ A i := by
  ext ω
  simp only [mem_avoid, Finset.mem_insert, forall_eq_or_imp, Finset.mem_sdiff]
  tauto

omit [DecidableEq I] in
theorem avoid_antitone (A : I → Finset Ω) {S T : Finset I} (h : S ⊆ T) :
    avoid A T ⊆ avoid A S := by
  intro ω hω
  exact (mem_avoid A S ω).mpr (fun i hi => (mem_avoid A T ω).mp hω i (h hi))

omit [Fintype Ω] [DecidableEq Ω] in
theorem mass_nonneg (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (s : Finset Ω) : 0 ≤ mass w s :=
  Finset.sum_nonneg (fun ω _ => hw ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem mass_mono (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) {s t : Finset Ω}
    (h : s ⊆ t) : mass w s ≤ mass w t :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun ω _ _ => hw ω)

theorem mass_avoid_sub_insert (w : Ω → ℝ) (A : I → Finset Ω) (S : Finset I) (i : I) :
    mass w (avoid A S) - mass w (avoid A (insert i S)) =
      mass w (A i ∩ avoid A S) := by
  rw [avoid_insert]
  unfold mass
  have hh := Finset.sum_inter_add_sum_sdiff (avoid A S) (A i) w
  rw [Finset.inter_comm] at hh
  linarith
/-- Finite asymmetric Lovász Local Lemma on a weighted finite probability space.
An event is independent of the conjunction of complements of every collection
of its non-neighbors. No symmetry of the supplied dependency relation is needed. -/
theorem finite_local_lemma
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (A : I → Finset Ω) (N : I → Finset I) (x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      mass w (A i ∩ avoid A T) = mass w (A i) * mass w (avoid A T))
    (hp : ∀ i, mass w (A i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (S : Finset I) :
    (∏ j ∈ S, (1 - x j)) ≤ mass w (avoid A S) ∧ 0 < mass w (avoid A S) := by
  have hdep : ∀ T i, i ∉ T →
      mass w (avoid A T) - mass w (avoid A (insert i T)) ≤
        mass w (A i) * mass w (avoid A (T \ N i)) := by
    intro T i hi
    rw [mass_avoid_sub_insert]
    have hmono := mass_mono w hw (s := A i ∩ avoid A T)
      (Finset.inter_subset_inter_left (avoid_antitone A (Finset.sdiff_subset : T \ N i ⊆ T)))
    have hni : i ∉ T \ N i := fun h => hi (Finset.mem_sdiff.mp h).1
    have hd : Disjoint (T \ N i) (N i) := Finset.sdiff_disjoint
    exact hmono.trans_eq (hind i (T \ N i) hni hd)
  have hbound := local_lemma_product (fun T => mass w (avoid A T))
    (fun i => mass w (A i)) x N (fun T => mass_nonneg w hw _)
    (by simpa [mass] using hw1) hx0 hx1 hp hdep S
  exact ⟨hbound, (Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i))).trans_le hbound⟩

/-- The local lemma gives an actual outcome avoiding every specified bad event. -/
theorem exists_avoiding_of_local_lemma
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (A : I → Finset Ω) (N : I → Finset I) (x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      mass w (A i ∩ avoid A T) = mass w (A i) * mass w (avoid A T))
    (hp : ∀ i, mass w (A i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (S : Finset I) : ∃ ω, ∀ i ∈ S, ω ∉ A i := by
  have hpos := (finite_local_lemma w hw hw1 A N x hx0 hx1 hind hp S).2
  have hne : (avoid A S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hpos
    simp [mass] at hpos
  obtain ⟨ω, hω⟩ := hne
  exact ⟨ω, (mem_avoid A S ω).mp hω⟩

end FiniteProbability
end PropertyH.LovaszLocal

