# Formalize this paper completely

Formalize the complete mathematical content of `paper/main.tex` in Lean 4, following
`prompts/RECURSIVE_FORMALIZATION.md` exactly.

Before starting, read any repository instruction file that is present, `docs/GLOSSARY.md`, and the
complete recursive-formalization prompt. Treat `paper/main.tex` as the authoritative source.

The current project is already configured as package `propertyh`, library and namespace
`PropertyH`, with source directory `lean/`. Preserve its pinned Lean/Mathlib versions.
Run `sh scripts/setup.sh` to install/fetch dependencies if needed. The initial Lean files
reserve the namespace only; no mathematical statements have yet been transcribed.

Execute the remaining bootstrap stage yourself:
complete `lean/coverage.json` with every proof-relevant definition and claim,
transcribe the complete statement skeleton, and update `lean/FORMALIZATION_LOG.md`.

Then continue recursively until the entire paper and all of its proof-relevant dependencies are
formally verified relative to the pinned Mathlib. If Mathlib lacks a required result, formalize that
result and its prerequisites recursively. Do not stop at a compiling scaffold, skeleton-green state,
reduced debt count, or documented missing theory.

Completion requires every terminal gate in `prompts/RECURSIVE_FORMALIZATION.md` to pass:

- the full Lean library builds;
- the coverage inventory is closed;
- there are zero `sorry` or `admit` terms;
- there are zero project-specific axioms or scope boundaries;
- there are no unverified placeholder definitions; and
- `#print axioms` on every coverage root reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

Treat `prompts/INIT.md` as legacy reference material only. Do not use its axiom-based shortcuts.

Register exact declaration names and statuses in `lean/coverage.json` as the work progresses.
Run `sh scripts/audit.sh` after each pass and `sh scripts/audit.sh --terminal` before
claiming completion. The generated `lean/Audit.lean` follows that inventory. Source-to-statement
review is required in addition to the mechanical audit; do not mark an entry verified
merely because a different or weaker proposition was proved.

Keep the build green and update the coverage inventory, debt ledger, and pass history after every
pass. Continue automatically to the next open dependency until terminal verification is reached.
Pause only for a genuinely false or materially ambiguous source statement, an unavailable required
source, or an environment that cannot run Lean. Difficulty, duration, or missing Mathlib
infrastructure are not reasons to stop.

You are explicitly authorized to use subagents whenever they materially accelerate the work. Follow
the orchestration rules in `prompts/RECURSIVE_FORMALIZATION.md`: begin by validating the decomposition
pattern, give agents disjoint file ownership, cluster coupled leaves under one owner, isolate
concurrent work with Git worktrees when necessary, verify each returned branch centrally, and never
allow agents to introduce axioms or silently change theorem signatures.

Preserve unrelated files and user changes. Work through as many passes and commits as necessary,
and do not report the formalization complete until every terminal condition above has been verified.
