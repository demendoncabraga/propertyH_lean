# Workflow glossary

This glossary describes the current `PropertyH` project and reusable operations.
The mathematical source is `paper/main.tex`.

| Term | Meaning in this repository |
| --- | --- |
| Formalization | Translating and proving the manuscript's mathematical claims in Lean, following `prompts/RECURSIVE_FORMALIZATION.md`. |
| Library | `PropertyH`, rooted at `lean/PropertyH.lean`, with mathematical modules under `lean/PropertyH/`. |
| Setup | Project configuration and an empty library. No mathematical claims have yet been checked. |
| Statement skeleton | The paper's actual definitions and theorem statements have been transcribed and typechecked; temporary proof debt is visible. |
| Coverage inventory | `lean/coverage.json`: source claims, dependencies, statuses and exact Lean declarations. |
| Per-instance log | `lean/FORMALIZATION_LOG.md`: decisions, open work, verification evidence and pass history. |
| Proof debt | All unproved or untranscribed required mathematics, including cited dependencies; not merely occurrences of `sorry`. |
| Axiom audit | Checking `#print axioms` for the registered declarations. Only the standard foundations are permitted at completion. |
| Standard foundations | `propext`, `Classical.choice`, `Quot.sound`, or a subset. |
| Terminal state | Complete source coverage and statement review, verified proofs, a passing build, and a passing terminal audit. |
| Provenance comment | A source label and the original mathematical statement recorded beside its Lean declaration. |
| Pass | A coherent increment of work, followed by a build, audit and log update. |
| Dependency cone | A declaration and the mathematical results on which its proof depends transitively. |
| Visualization | An optional dependency graph produced with `prompts/VISUALIZE_LEAN_GRAPH.md`; no graph exists yet. |
| Informalization | A verified natural-language rendering of Lean statements and proofs, following `prompts/INFORMALIZE.md`; no such artifact exists yet. |

An intermediate audit may report `sorryAx` for unfinished work. This is never a
completion certificate. Project-specific `axiom` declarations are forbidden.
There is no exception for scope-boundary files.

For an eventual informalization, use `lean/informal/` for the mathematical glossary,
prose and its own log. Definitions must follow the Lean statements, and differences
from the manuscript must be reported explicitly. Dependency graphs are navigation
aids; source text and checked declarations remain the evidence for mathematical claims.
