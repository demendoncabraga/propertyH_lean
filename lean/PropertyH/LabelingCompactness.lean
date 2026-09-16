import PropertyH.Basic

namespace PropertyH
/-- Finite satisfiability of closed local constraints on a finite alphabet gives a global labeling. -/
theorem exists_labeling_of_finite_constraints {E A I : Type*}
    [TopologicalSpace A] [CompactSpace A] [Nonempty A]
    (C : I → Set (E → A)) (hC : ∀ i, IsClosed (C i))
    (hfinite : ∀ s : Finset I, ∃ f : E → A, ∀ i ∈ s, f ∈ C i) :
    ∃ f : E → A, ∀ i, f ∈ C i := by
  have h : (⋂ i, C i).Nonempty := by
    apply CompactSpace.iInter_nonempty hC
    simpa only [Set.nonempty_def, Set.mem_iInter] using hfinite
  simpa only [Set.nonempty_def, Set.mem_iInter] using h
/-- Forbidden words on finite supports extend from finitely satisfiable constraints
on arbitrarily many edges to one global finite-alphabet labeling. -/
theorem exists_labeling_avoiding_finite_patterns {E A I : Type*}
    [TopologicalSpace A] [DiscreteTopology A] [Finite A] [Nonempty A]
    (s : I → Finset E) (B : ∀ i, Set ((s i) → A))
    (hfinite : ∀ t : Finset I, ∃ f : E → A,
      ∀ i ∈ t, (fun e : s i => f e) ∉ B i) :
    ∃ f : E → A, ∀ i, (fun e : s i => f e) ∉ B i := by
  apply exists_labeling_of_finite_constraints
    (fun i => {f : E → A | (fun e : s i => f e) ∉ B i}) ?_ hfinite
  intro i
  have hc : Continuous (fun f : E → A => fun e : s i => f e) := continuous_pi (fun e => continuous_apply (e : E))
  exact IsClosed.preimage hc (isClosed_discrete ((B i)ᶜ))
end PropertyH
