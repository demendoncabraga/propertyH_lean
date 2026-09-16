# Final manuscript verification record

## Scope

Real-scalar `paper/main.tex`, modulo the explicit Osajda expander-group hypothesis.
Maurey–Pisier is not used. The manuscript is unchanged by this cleanup.

## Final-draft cleanup (2026-09-16)

Rewired the finite-sup/c₀ and Johnson corollaries to the coarse main theorem.
Removed the obsolete biLipschitz and quasi-isometric main-theorem routes,
cotype developments, unused Hilbert-space and definition-comparison generalizations,
unused diameter/normalization estimates, and partial Osajda construction work.
Removed dead declarations from retained modules. Renamed the surviving sphere
restriction helper module to `SphereRestrictions`.

Removed retired prompts, informalization-design documents and the historical
setup report. Replaced the historical log with this current verification record;
Git history retains the earlier development. Kept the licensed Brouwer proof and
its provenance because Johnson's corollary needs sphere noncontractibility.

The terminal audit now checks kernel and source-reference dependencies from the
final manuscript statements and requires every source declaration to be both
needed and inventoried. It rejects stale inventory records and orphan modules.
Supporting biLipschitz finite-metric estimates remain only where the current
proofs use them. This is dependency minimality relative to the retained proofs,
not a claim of globally shortest proofs.

## Validation

- Source modules: 87 → 57. Source declarations: 501 → 292 (210 old
  declarations removed, one focused c₀ embedding helper added).
- Clean build passed after removing all project build artifacts from the test
  checkout; the pinned Mathlib dependency cache was retained.
- Terminal audit passed modulo Osajda, including all 292 axiom reports and the
  dependency/inventory check. No proof placeholders or nonstandard axioms.
- All 14 regression tests passed, covering both the external-scope gate and
  the dependency/inventory gate.
- The unconditional terminal audit rejects exactly D12 (Osajda), as intended.
- The compiled types of all ten final manuscript statements were compared with
  the pre-cleanup version and are identical.
- The manuscript checksum is unchanged, and the source diff has no whitespace
  errors. No dependency pin was changed.
