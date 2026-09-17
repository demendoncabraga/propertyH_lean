# Current manuscript synchronization

## Scope

Real-scalar `paper/main.tex`, unchanged by this synchronization. Degree zero for
arbitrary Banach spheres is interpreted as vanishing reduced integral homology
maps, with the author's approval. Osajda is the sole external hypothesis.

## Changes by paper result

- Theorem 1: expose eventual degree zero; retain the null-homotopy construction
  only as shared proof support. Remove the old common-target public wrapper.
- Corollary 2: define rational Property (H), prove the nonzero-degree obstruction,
  and derive the ordinary obstruction via Property (H) implying its rational
  version. Preserve uniform finite sup-space containment and c₀ proofs.
- Corollary 3: select one Osajda group before every target Banach space. Replace
  group-universality predicates with a specified-group coarse embedding and its
  restriction to expanders; remove the superseded wrapper module.
- Lemma 4 and P.I.: retain their established proofs and constants; Poincaré
  continues to have no cardinality or nonemptiness restriction.
- Proposition 5: replace the public null-homotopy conclusion with degree zero.
- Deleted Johnson corollary: remove 116 exclusive declarations, including six
  assembly/topology modules and five vendored Brouwer modules. Preserve upstream
  attribution files. Preserve every shared expander and finite-metric dependency.

## Verification

- `lake build` passed with no reported warnings.
- All 14 audit regression tests passed.
- Terminal audit passed modulo Osajda: 179 declarations in 45 modules, all
  supporting the ten current manuscript roots; no placeholders or nonstandard
  axioms. The unconditional gate rejected exactly D12 (Osajda), as intended.
- All local imports resolve. No new scratch or backup files enter the repository.
- The current manuscript SHA256 remains
  `261e4624587497db03a3a2d07fef80e1bbf541c2f3c65884eac280783abbbb40`.
- Upstream license and provenance records are preserved; no vendored Lean code
  remains in the active dependency tree.
