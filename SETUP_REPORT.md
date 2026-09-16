# Repository setup report

## Verified upgrade to the installed toolchain — September 16, 2026

At the user's request, the project now uses installed Lean `v4.33.1` and matching
Mathlib `v4.33.1` (commit `0df444a360eaa60ab8c11dca51a86af692955474`).
Lake regenerated `lake-manifest.json` with the matching dependency revisions.
The README and formalization log reflect these pins.

Validation in the current environment:

- `lean --version` and `lake --version` both select Lean `4.33.1`.
- `lake update` succeeded and fetched the compiled Mathlib cache.
- `sh scripts/setup.sh` succeeded, including `lake exe cache get` and `lake build`.
- `sh scripts/audit.sh` succeeded and explicitly reported that no mathematical
  declarations are registered yet.
- `sh scripts/audit.sh --terminal` failed as expected because all 18 inventory
  entries remain unfinished. This is not a toolchain failure.
- The manuscript SHA-256 remains
  `248468d4ca1d82050ebe06dc3d3aa6932b9bc4da15a7d34baba14f760a04ced4`.

The earlier runtime limitation below does not apply to this verified setup.
The project is ready for mathematical formalization; no paper result has been proved.

## Original preparation

- Renamed `paper/propertyH.bbl.tex` to `paper/main.tex` without changing its contents.
- Set the package name to `propertyh` and the library, root module and namespace to
  `PropertyH`. Updated the manifest's root package name; retained every dependency
  revision and the original Lean/Mathlib `v4.30.0` pins.
- Added the initial root module, an empty shared-definitions module, a generated-audit
  location, a preliminary coverage inventory and a formalization log.
- Added setup and audit scripts. The terminal audit rejects an incomplete or empty
  inventory and unfinished proofs; a successful empty build cannot pass as completion.
- Updated repository guidance and the starting prompt for the new project. Replaced
  obsolete instance documentation with current or generic guidance. Retained reusable
  workflow examples with explicit historical labels. Retired the old axiom-based
  representation-test prompt.
- Added a README with a ready-to-use instruction for a coding assistant.
- Excluded generated caches and operating-system archive metadata from the edited ZIP.

## Validation performed

- Verified exact byte equality between the uploaded manuscript and `paper/main.tex`.
  SHA-256: `248468d4ca1d82050ebe06dc3d3aa6932b9bc4da15a7d34baba14f760a04ced4`.
- Parsed the TOML and JSON configuration, checked agreement between package names,
  and checked that the configured default library has its matching root module.
- Compared every dependency entry with the uploaded manifest; all are unchanged.
- Checked the shell scripts' syntax and compiled the Python audit script to bytecode.
- Confirmed that the terminal audit rejects the actual initial, unfinished inventory.
- Exercised the audit parser and rejection paths with simulated Lake output: standard
  foundations, no-axiom and wrapped reports; missing reports; temporary proof debt;
  unexpected axioms; source-level project axioms; and comment/string filtering.
  These script checks are not Lean compilation or mathematical verification.

## Historical Lean runtime limitation (original preparation)

The preparation environment initially had no Lean tools. An isolated Elan installation
and the pinned Lean `v4.30.0` toolchain were downloaded. Lake reports the expected
Lean version, but invoking the Lean executable fails before compilation with:

```text
error: failed to locate application
```

The supplied `scripts/setup.sh` was attempted and stopped at that failure. Consequently,
the project's Lean build and the Mathlib cache download have not been verified here.
The setup script is included so the same pinned project can be initialized in a
working Lean environment. Downloaded tools and caches are not included in the ZIP.

## Mathematical status

This delivery prepares the repository only. It does not formalize, proofread, or
certify the paper. All five numbered results and their required dependencies remain
open. The preliminary inventory must be completed during the mathematical bootstrap.
No manuscript theorem has been replaced by a weakened statement or an axiom.
