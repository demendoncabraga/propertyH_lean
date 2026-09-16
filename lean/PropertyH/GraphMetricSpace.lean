import PropertyH.CZero
import PropertyH.Connectivity
import PropertyH.FiniteSup
noncomputable section
namespace PropertyH

@[instance_reducible]
def graphMetricSpace {V : Type*} (G : SimpleGraph V) (hc : G.Connected) : MetricSpace V where
  dist v w := G.dist v w
  dist_self v := by simp
  dist_comm v w := by simp [G.dist_comm]
  dist_triangle v w z := by
    exact_mod_cast (hc.preconnected w z).dist_triangle_right v
  eq_of_dist_eq_zero := by
    exact fun h => hc.dist_eq_zero_iff.mp (Nat.cast_eq_zero.mp h)
theorem finite_graph_embeds_sup {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hc : G.Connected) :
    ∃ f : V → (Fin (Fintype.card V) → ℝ), ∀ v w, ‖f v - f w‖ = (G.dist v w : ℝ) := by
  let := graphMetricSpace G hc
  have hd : ∀ v w : V, dist v w = (G.dist v w : ℝ) := fun _ _ => rfl
  exact ⟨finiteDistanceCoordinates, fun v w => by simpa only [dist_eq_norm, hd] using (finiteDistanceCoordinates_isometry (V := V)).dist_eq v w⟩
theorem expander_sup_embeddings (E : ExpanderFamily) :
    EquiGraphEmbeddings E (fun n => Fin (Fintype.card (E.V n)) → ℝ) := by
  classical
  have hf : ∀ n, ∃ f : E.V n → (Fin (Fintype.card (E.V n)) → ℝ),
      ∀ v w, ‖f v - f w‖ = ((E.graph n).dist v w : ℝ) := by
    intro n
    cases isEmpty_or_nonempty (E.V n) with
    | inl h => exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩
    | inr h => exact finite_graph_embeds_sup (E.graph n) (E.expands n).connected
  choose f hf using hf
  exact ⟨1, le_rfl, f, fun n v w => by simp [hf]⟩
/-- Every expander family embeds into c₀; existence of such a family is separate. -/
theorem expander_cZero_embeddings (E : ExpanderFamily) :
    EquiGraphEmbeddings E (fun _ => CZero) := by
  obtain ⟨L, hL, φ, hφ⟩ := expander_sup_embeddings E
  refine ⟨L, hL, fun n v => finiteToCZero _ (φ n v), ?_⟩
  intro n v u
  simpa only [← dist_eq_norm, (finiteToCZero_isometry _).dist_eq] using hφ n v u
end PropertyH
