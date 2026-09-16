# Informalizer design

This document describes an optional future operation for `PropertyH`.
No informalization, graph, closure checker, or mathematical glossary exists yet.
The operational method is `prompts/INFORMALIZE.md`.

## Purpose

Render verified Lean mathematics as a readable natural-language paper, with exact
links back to the formal statements and proofs. Use the `PropertyH` library under
`lean/`; place future outputs under `lean/informal/`. The source for a later
comparison is `paper/main.tex`.

## Principles

1. Derive the mathematical prose from the actual Lean declarations. Docstrings and
   manuscript excerpts are navigation aids, not proof evidence.
2. Traverse dependencies from foundations toward the main results, maintaining a
   mathematical glossary. Use one agreed rendering of each concept throughout.
3. Surface numbered results and substantive supporting lemmas. Administrative Lean
   details can be absorbed into the prose, but mathematical hypotheses cannot be hidden.
4. Check each rendering independently: statement equivalence, cited dependencies,
   and the proof's mathematical case structure must agree with Lean.
5. Compare the verified prose to the manuscript only after the Lean-based reading is
   fixed. Document every material difference; never silently claim equivalence.
6. Expose unfinished proof dependencies explicitly. A compiled statement supported by
   a placeholder is not a verified result.
7. Inspect the pinned Lean environment before deciding whether a dependency extractor
   can access proof terms. Source-name searches can both miss and invent dependencies.

## Future outputs

- `lean/informal/PAPER.md`: assembled mathematical prose.
- `lean/informal/GLOSSARY.md`: mathematical terminology linked to declarations.
- `lean/informal/INFORMALIZATION_LOG.md`: coverage, verification and divergence records.
- A closure checker, if implemented, must check real coverage and citation integrity.

These are planned outputs, not required inputs for beginning the formalization.
The current state is recorded only in `lean/FORMALIZATION_LOG.md`.
