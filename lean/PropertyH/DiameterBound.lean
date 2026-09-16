import PropertyH.DegreeBound
import PropertyH.GraphMetric

noncomputable section
namespace PropertyH

def metricBall {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun u => G.dist v u ≤ r

theorem metricBall_growth {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) (hc : G.Connected)
    (v : V) (r : ℕ) (hsmall : 2 * (metricBall G v r).card ≤ Fintype.card V) :
    (1 + h) * ((metricBall G v r).card : ℝ) ≤ (metricBall G v (r + 1)).card := by
  classical
  let A := metricBall G v r
  let B : Finset V := Finset.univ.filter fun w => w ∉ A ∧ ∃ u ∈ A, G.Adj w u
  have hg := hex.2.2 A hsmall
  have hB : ({w | w ∉ A ∧ ∃ u ∈ A, G.Adj w u} : Set V) = (B : Set V) := by
    ext w
    simp [B]
  rw [hB, Set.ncard_coe_finset] at hg
  have hdis : Disjoint A B := by
    simp only [Finset.disjoint_left, B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun w hw hb => hb.1 hw
  have hsub : A ∪ B ⊆ metricBall G v (r + 1) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · simp only [A, metricBall, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      omega
    · obtain ⟨_, u, hu, hadj⟩ := (Finset.mem_filter.mp hw).2
      have hdist := hc.dist_triangle (u := v) (v := u) (w := w)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at hdist
      simp only [A, metricBall, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hcard
  have hcardR : (A.card : ℝ) + B.card ≤ (metricBall G v (r + 1)).card := by exact_mod_cast hcard
  change (1 + h) * (A.card : ℝ) ≤ _
  nlinarith
theorem metricBall_mono {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    {r s : ℕ} (hrs : r ≤ s) : metricBall G v r ⊆ metricBall G v s := by
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.trans hrs⟩

/-- Exponential growth up to the half-volume threshold. -/
theorem metricBall_power_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) (hc : G.Connected)
    (v : V) (r : ℕ) (hsmall : 2 * (metricBall G v r).card ≤ Fintype.card V) :
    (1 + h)^r ≤ ((metricBall G v r).card : ℝ) := by
  induction r with
  | zero =>
    have hmem : v ∈ metricBall G v 0 := by simp [metricBall]
    have hpos := Finset.card_pos.mpr ⟨v, hmem⟩
    simpa using (show (1 : ℝ) ≤ (metricBall G v 0).card by exact_mod_cast hpos)
  | succ r ih =>
    have hmono := Finset.card_le_card (metricBall_mono G v (Nat.le_succ r))
    have hsmall' : 2 * (metricBall G v r).card ≤ Fintype.card V := (Nat.mul_le_mul_left 2 hmono).trans hsmall
    have hi := ih hsmall'
    have hg := metricBall_growth hex hc v r hsmall'
    rw [pow_succ']
    exact (mul_le_mul_of_nonneg_left hi (by linarith [hex.1])).trans hg
theorem metricBall_disjoint {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (u v : V) (r : ℕ) (hd : 2 * r < G.dist u v) :
    Disjoint (metricBall G u r) (metricBall G v r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hu hv
  have hu' := (Finset.mem_filter.mp hu).2
  have hv' := (Finset.mem_filter.mp hv).2
  have ht := hc.dist_triangle (u := u) (v := w) (w := v)
  rw [SimpleGraph.dist_comm (u := w) (v := v)] at ht
  omega

/-- At least one of two disjoint balls has at most half the vertices. -/
theorem metricBall_one_small {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (u v : V) (r : ℕ) (hd : 2 * r < G.dist u v) :
    2 * (metricBall G u r).card ≤ Fintype.card V ∨
      2 * (metricBall G v r).card ≤ Fintype.card V := by
  classical
  have hcard := Finset.card_le_univ (metricBall G u r ∪ metricBall G v r)
  rw [Finset.card_union_of_disjoint (metricBall_disjoint hc u v r hd)] at hcard
  omega

/-- Expansion bounds how long two vertex balls can remain disjoint. -/
theorem expander_distance_power_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) (hc : G.Connected)
    (u v : V) (r : ℕ) (hd : 2 * r < G.dist u v) :
    (1 + h)^(r+1) ≤ (Fintype.card V : ℝ) := by
  have hball : ∀ w, 2 * (metricBall G w r).card ≤ Fintype.card V →
      (1 + h)^(r+1) ≤ (Fintype.card V : ℝ) := by
    intro w hw
    have hp := metricBall_power_le hex hc w r hw
    have hg := metricBall_growth hex hc w r hw
    have hn : ((metricBall G w (r+1)).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Finset.card_le_univ (metricBall G w (r+1))
    rw [pow_succ']
    exact ((mul_le_mul_of_nonneg_left hp (by linarith [hex.1])).trans hg).trans hn
  exact (metricBall_one_small hc u v r hd).elim (hball u) (hball v)
theorem expander_distance_log_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {h : ℝ} (hex : IsVertexExpander G k h) (hc : G.Connected)
    (u v : V) :
    (G.dist u v : ℝ) ≤ 2 * Real.log (Fintype.card V) / Real.log (1+h) := by
  have hlog : 0 < Real.log (1+h) := Real.log_pos (by linarith [hex.1])
  have hN : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hlogN := Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card V by exact_mod_cast hN)
  apply (le_div_iff₀ hlog).mpr
  by_cases hd : G.dist u v = 0
  · simp only [hd, Nat.cast_zero, zero_mul]
    positivity
  · let r := (G.dist u v - 1) / 2
    have hr : 2 * r < G.dist u v := by dsimp [r]; omega
    have hd' : G.dist u v ≤ 2 * (r + 1) := by dsimp [r]; omega
    have hp := expander_distance_power_bound hex hc u v r hr
    have hl := Real.log_le_log (pow_pos (show 0 < 1+h by linarith [hex.1]) _) hp
    rw [Real.log_pow] at hl
    have hdR : (G.dist u v : ℝ) ≤ 2 * ((r+1 : ℕ) : ℝ) := by exact_mod_cast hd'
    nlinarith
theorem expander_diameter_bound_proved {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (h : ℝ) (hG : IsVertexExpander G k h) (hV : 5 ≤ Fintype.card V) :
    (graphDiameter G : ℝ) ≤ (2 / Real.log (1 + h / k)) * Real.log (Fintype.card V) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V)
    Finset.univ_nonempty (fun u => Finset.univ.sup (G.dist u))
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V)
    Finset.univ_nonempty (G.dist u)
  have hd : graphDiameter G = G.dist u v := hu.trans hv
  rw [hd]
  have hb := expander_distance_log_bound hG hG.connected u v
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by have := hG.two_le_degreeBound hV; omega)
  have hkh : 0 < h / k := div_pos hG.1 (by linarith)
  have hlog : 0 < Real.log (1 + h / k) := Real.log_pos (by linarith)
  have hfrac : h / k ≤ h := (div_le_iff₀ (by linarith : (0 : ℝ) < k)).mpr (by nlinarith [hG.1])
  have hlogs : Real.log (1+h/k) ≤ Real.log (1+h) :=
    Real.log_le_log (by linarith) (by linarith)
  have hn : 0 ≤ 2 * Real.log (Fintype.card V) := by
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ Fintype.card V by omega))
  have ht := div_le_div_of_nonneg_left hn hlog hlogs
  calc
    (G.dist u v : ℝ) ≤ 2 * Real.log (Fintype.card V) / Real.log (1+h) := hb
    _ ≤ 2 * Real.log (Fintype.card V) / Real.log (1+h/k) := ht
    _ = (2 / Real.log (1+h/k)) * Real.log (Fintype.card V) := by ring
end PropertyH
