# Expanders prevent Property (H): Lean project

The current real-scalar manuscript in `paper/main.tex` is formalized **modulo
Osajda**. All numbered results and their proof dependencies are covered. Osajda's
result appears as an explicit hypothesis of the group-universality corollary;
there are no proof placeholders or project axioms.

The main theorem, coarse normalization, degree-one Property (H) obstruction,
uniform finite sup-space containment corollary, Johnson conclusion and c₀
conclusion require no external hypothesis. The revised manuscript assumes
uniform containment of finite-dimensional ℓ∞ spaces directly, so Maurey–Pisier
is no longer needed. The former conditional Maurey–Pisier deductions have been
removed. The independent c₀ trivial-cotype proof is retained as legacy support.

See [verification scope](docs/VERIFICATION_SCOPE.md) for the exact hypothesis,
real-scalar and orientation conventions, and [source review](docs/SOURCE_COVERAGE_REVIEW.md)
for the mathematical-proof coverage. Introductory contextual literature
results are catalogued separately and are not claimed re-proved.

Run the agreed completion gate:

```sh
lake build
python3 scripts/test_audit.py
sh scripts/audit.sh --terminal --modulo-external
```

The unconditional `--terminal` gate without `--modulo-external` deliberately fails
because Osajda is a supplied hypothesis. Previous proofs and
legacy definitions are retained; no Lean or Mathlib pin was changed.

## Starting with a coding assistant

Give the assistant this repository and the following instruction:

> Formalize `paper/main.tex` in Lean by following `prompts/FORMALIZE_PAPER.md`.
> Use the existing `PropertyH` setup, maintain the coverage inventory and log, and
> distinguish verified results from unfinished dependencies. Preserve the manuscript
> and flag mathematical problems rather than silently changing its statements.

For changes to the paper, update the existing proofs and source inventory incrementally.
The agreed current scope is recorded in `docs/VERIFICATION_SCOPE.md`.

## Building locally on macOS or Linux

Open a terminal in this extracted folder and run:

```sh
sh scripts/setup.sh
```

This obtains the pinned Lean toolchain, downloads Mathlib's compiled cache and builds
the initial project. It needs internet access, Git, curl and Python 3. The Lean
version manager is installed if absent; the script does not change your shell profile.
Future script invocations find its standard installation automatically.

To check subsequent formalization work:

```sh
sh scripts/audit.sh
sh scripts/audit.sh --terminal --modulo-external
```

The modulo terminal command checks the agreed scope. The strict unconditional
terminal gate remains separate. Source-to-statement review is recorded in
`docs/SOURCE_COVERAGE_REVIEW.md`.

## Files

| Path | Purpose |
| --- | --- |
| `paper/main.tex` | Complete manuscript, including its bibliography. |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Pinned Lean/Mathlib configuration. |
| `lean/PropertyH.lean` | Root module; imports every formalization module. |
| `lean/PropertyH/Basic.lean` | Initial namespace and future shared definitions. |
| `lean/coverage.json` | Closed source inventory, external hypotheses and declaration mapping. |
| `lean/FORMALIZATION_LOG.md` | Mathematical progress, decisions and open work. |
| `lean/Audit.lean` | Generated axiom checks for registered declarations. |
| `scripts/` | Setup and audit commands. |
| `prompts/` | Formalization and optional later workflows. |

Lean and Mathlib are pinned to `v4.33.1`, matching an installed Lean toolchain.
The dependency manifest records the resolved revisions for this release. Downloaded
compilers and the Mathlib build cache are not part of the project source.

Installation references: [official Lean installation guide](https://lean-lang.org/install/manual/)
and [Elan version manager](https://github.com/leanprover/elan).
