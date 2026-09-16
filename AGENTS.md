# Repository guidelines

The authoritative manuscript is `paper/main.tex`, *Expanders prevent Property (H)*.
Preserve it unless the author requests changes. The Lean library is `PropertyH`,
under `lean/`, pinned to Lean/Mathlib v4.33.1.

Formalize the current real-scalar paper modulo exactly `OsajdaExpanderGroup`.
Do not add external hypotheses, project axioms, proof placeholders, or silently
weaken statements. Report mathematical ambiguities to the author. Do not resume
Osajda's construction unless the author changes the scope.

The source tree should contain only current manuscript statements and their
proof dependencies. Update `lean/coverage.json`, `docs/SOURCE_COVERAGE_REVIEW.md`
and `docs/VERIFICATION_SCOPE.md` when the manuscript or statements change.
`scripts/DependencyAudit.lean` lists the final manuscript roots; keep its list
consistent with `paper_roots` in the inventory. Do not retain obsolete theorem
versions or unused developments. Preserve vendored licenses and provenance.

Validate from the repository root:

```sh
python3 scripts/test_audit.py
sh scripts/audit.sh --terminal --modulo-external
```

The terminal audit builds Lean, checks source-dependency closure and inventory,
rejects placeholders/project axioms, and checks all registered axiom reports.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted foundational
axioms. The unconditional gate deliberately rejects the explicit Osajda parameter.
A passing audit does not replace a mathematical source-to-statement review.

Keep dependency pins unchanged. Use two-space indentation in Lean and focused
commits. Do not commit build caches or LaTeX auxiliary files. Preserve unrelated
user work. The current verification record is `lean/FORMALIZATION_LOG.md`;
historical development is available in Git history.
