# Repository guidelines

## Current project

The authoritative manuscript is `paper/main.tex`, *Expanders prevent Property (H)*.
The Lean package is `propertyh`, its library and namespace are `PropertyH`, and its
source directory is `lean/`. `lean/PropertyH.lean` imports all paper modules.
`lean/PropertyH/Basic.lean` is the initial shared vocabulary module.

The current author-authorized scope is the entire mathematical proof modulo exactly
Maurey–Pisier and Osajda. Read `docs/VERIFICATION_SCOPE.md` and
`docs/SOURCE_COVERAGE_REVIEW.md`; run `sh scripts/audit.sh --terminal --modulo-external`
for this scope. The older unconditional completion workflow remains a stricter gate.
Do not resume proving the two external constructions unless the user changes this scope.

The repository contains the formalization. Consult `lean/coverage.json` and
`lean/FORMALIZATION_LOG.md` for the actual current proof status. Preserve the manuscript unless the user
requests changes. Flag false or materially ambiguous statements instead of silently
changing hypotheses or conclusions to make them provable.

## Workflow

- For complete formalization, read `prompts/FORMALIZE_PAPER.md`,
  `prompts/RECURSIVE_FORMALIZATION.md`, `docs/GLOSSARY.md`, and the current log.
- `lean/FORMALIZATION_LOG.md` records decisions, proof debt and progress.
- `lean/coverage.json` records source claims and their actual Lean declarations.
  Expand its initial inventory before marking it complete. Register all required
  definitions, results and external proof dependencies, not just the main theorem.
- The setup task does not itself authorize starting the full mathematical formalization.
- Some reusable method examples describe historical projects. They are examples only;
  no historical library or proof is present or assumed here.
- `prompts/INIT.md` is a retired representation-test prompt and is not applicable.

## Build and validation

Run commands from the repository root:

```sh
sh scripts/setup.sh
lake build
sh scripts/audit.sh
sh scripts/audit.sh --terminal
```

The setup script installs the version manager if needed, obtains the pinned Lean
toolchain and Mathlib cache, and builds the initial project. It requires network
access, Git, curl and Python 3. Keep the existing dependency pins unless a change
is explicitly justified; do not run an unrequested dependency upgrade.

The ordinary audit permits explicitly tracked temporary proof debt but rejects
project axiom declarations and unexpected foundational axioms. The terminal audit
also requires a complete inventory, verified entries with actual declarations, no
proof placeholders, and only `propext`, `Classical.choice`, and `Quot.sound` in the
registered declarations' axiom reports. `lean/Audit.lean` is generated from the
inventory by the audit script. The audit does not replace a source-to-statement review.

To compile the manuscript, run `latexmk -pdf -interaction=nonstopmode
-halt-on-error main.tex` from `paper/`, when a suitable TeX installation is available.
If the manuscript is edited, inspect the resulting PDF and resolve broken references.

## Editing conventions

Use the manuscript's existing notation in provenance comments. Prefer two-space
indentation in Lean. Keep shared definitions in `Basic.lean` or coherent dedicated
modules. Import all mathematical modules through the root library. Preserve unrelated
user work. Do not commit generated build caches or LaTeX auxiliary files.

The standard trusted base is Lean and the pinned Mathlib. Never add project axioms
or silently weaken statements. A passing empty build is not evidence that a paper
result is formalized. Report verification limits accurately.

When Git is available, keep commits focused and report the actual build and audit
results. A ZIP export need not include a Git repository.
