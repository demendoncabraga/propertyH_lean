# Current manuscript synchronization

## Scope

Real-scalar `paper/main.tex`, unchanged by this synchronization. The main theorem
now assumes finite-dimensional normed spaces on both sides. Degree zero is
interpreted as vanishing reduced integral homology maps, with the author's
approval. Osajda is the sole external hypothesis.

## Changes by paper result

- Theorem 1: eventual degree zero for finite-dimensional real normed spaces.
  Replace completeness assumptions by finite-dimensionality in the main theorem
  and its shared coarse null-homotopy helper; Lean infers completeness. The
  previous general main statement is replaced in place, without a legacy copy.
  Retain the null-homotopy construction only as necessary proof support.
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

Rechecked on 2026-09-17 after the finite-dimensional statement update.

- `lake build` passed with no reported warnings.
- All 14 audit regression tests passed.
- Terminal audit passed modulo Osajda: 179 declarations in 45 modules, all
  supporting the ten current manuscript roots; no placeholders or nonstandard
  axioms. The unconditional gate remains configured to reject D12 (Osajda);
  that gate was checked during the preceding synchronization.
- All local imports resolve. No new scratch or backup files enter the repository.
- The current manuscript SHA256 is
  `1a4f01003edff194d8910d7853249d9e5f1760383f90bfb7d722b08ca4d4c0e1`.
- Upstream license and provenance records are preserved; no vendored Lean code
  remains in the active dependency tree.
