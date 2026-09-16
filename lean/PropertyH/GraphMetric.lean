import PropertyH.Expanders

noncomputable section
namespace PropertyH

/-- Source: `$\operatorname{diam}(V)$`, for a finite graph with its shortest-path distance. -/
def graphDiameter {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup (fun v => Finset.univ.sup (G.dist v))

end PropertyH
