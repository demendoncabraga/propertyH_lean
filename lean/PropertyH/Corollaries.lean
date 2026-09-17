import PropertyH.CoarseMain
import PropertyH.ExpanderExistence
import PropertyH.GraphMetricSpace

noncomputable section
namespace PropertyH
/-- Source: the introductory conclusion that c₀ fails Property (H). -/
theorem not_hasPropertyH_cZero : ¬ HasPropertyH CZero :=
  not_hasPropertyH_of_containsCoarseExpanders CZero
    ⟨PermutationExpanders.constructedExpanderFamily,
      (expander_cZero_embeddings PermutationExpanders.constructedExpanderFamily).to_coarse⟩

end PropertyH
