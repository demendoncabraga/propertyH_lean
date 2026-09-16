import PropertyH.Basic

/-! The paper's bounded-degree vertex expanders and their embeddings. -/

noncomputable section
namespace PropertyH
open Filter

/-- Source: `$|\{v\in V\setminus A\mid \exists u\in A, (v,u)\in E\}|\ge h|A|$`
and each vertex has at most `k` neighbors. -/
def IsVertexExpander {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : ℝ) : Prop :=
  0 < h ∧ (∀ v, (G.neighborSet v).ncard ≤ k) ∧
    ∀ A : Finset V, 2 * A.card ≤ Fintype.card V →
      h * (A.card : ℝ) ≤ (({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V).ncard : ℝ)

/-- Source: `$(G_n=(V_n,E_n))_n$` are `(k,h)`-expanders for fixed `k,h`,
with `$\lim_n|V_n|=\infty$`. -/
structure ExpanderFamily where
  V : ℕ → Type
  fintype : ∀ n, Fintype (V n)
  graph : ∀ n, SimpleGraph (V n)
  degreeBound : ℕ
  expansion : ℝ
  expands : ∀ n, @IsVertexExpander (V n) (fintype n) (graph n) degreeBound expansion
  grows : Tendsto (fun n => @Fintype.card (V n) (fintype n)) atTop atTop

attribute [instance] ExpanderFamily.fintype

/-- Source: `Eq.Lip.Con`:
`$d_n(v,u)/L \le \|\varphi_n(v)-\varphi_n(u)\| \le Ld_n(v,u)$`, `$L\ge1$`. -/
def EquiGraphEmbeddings (E : ExpanderFamily) (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] : Prop :=
  ∃ L : ℝ, 1 ≤ L ∧ ∃ φ : ∀ n, E.V n → X n,
    ∀ n v u, (E.graph n).dist v u / L ≤ ‖φ n v - φ n u‖ ∧
      ‖φ n v - φ n u‖ ≤ L * (E.graph n).dist v u

/-- Source: a Banach space contains equi-biLipschitz copies of an expander sequence. -/
def ContainsExpanders (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ E : ExpanderFamily, EquiGraphEmbeddings E (fun _ => X)

end PropertyH
