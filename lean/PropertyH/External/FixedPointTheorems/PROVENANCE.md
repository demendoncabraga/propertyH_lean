# Brouwer fixed-point proof provenance

Upstream: https://github.com/harfe/fixed-point-theorems-lean4
Revision: `770940ddf9878cf61952ed53d910b92bca841838`.
Copyright (c) 2026 harfe; MIT license retained in LICENSE.
Upstream pins Lean and Mathlib v4.32.0. These sources are ported to this project’s pinned Lean/Mathlib v4.33.1.

Only the five modules needed for Brouwer are vendored; Kakutani is excluded.
Unused declarations have been removed after tracing the final manuscript’s proof dependencies. Original declaration namespaces are preserved. Imports are relocated under `PropertyH.External.FixedPointTheorems`.
Adaptations: mark noncomputable sections; use Fin.ext_iff for a Fin equality; make a dependent Fin-index change explicit; enable backward.isDefEq.respectTransparency.types=false in cubical_sperner; add local classical to strong_cubical_sperner; replace deprecated set lemmas and haveI style.

The proof follows cubical Sperner (Kuhn, 1960), then approximate fixed points and compactness, then homeomorphisms of compact convex sets.
Trust audit roots: `strong_cubical_sperner`, `weaker_cubical_sperner`, `fixed_point_unit_cube`, `brouwer_fixed_point`, and `PropertyH.finiteDimensional_unitSphere_not_contractible`.
No sorry, project axiom, native_decide, unsafe declaration, or external proof oracle is used.
