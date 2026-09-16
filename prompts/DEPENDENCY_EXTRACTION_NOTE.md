# Dependency extraction: optional future tooling

No dependency extractor is implemented in the initial `PropertyH` project.
This note is a design reference for `prompts/INFORMALIZE.md` and
`prompts/VISUALIZE_LEAN_GRAPH.md`, not a claim about an existing graph.

For a declaration, distinguish constants in its type from constants in its
elaborated proof or definition. Traverse both terms when the pinned Lean API
provides them, then filter to the intended namespace for a project-only graph.
Retain external dependencies separately when auditing mathematical foundations.

First test on small known examples whether imported proof bodies are available
and whether the API returns genuine bodies, missing values, or fallback objects.
Do not assume behavior from another toolchain or an earlier project's notes.
Consult the installed Lean source and official documentation for the exact API.

If only a source-text dependency scan is available, label its edges as heuristic.
Such a scan may omit implicit typeclass, simplifier or tactic dependencies, and
may include names that the proof does not use. It is neither an exact graph nor
a substitute for `#print axioms` and statement-level review.

Validate an extractor on examples involving explicit lemmas, typeclass inference,
and simplification before relying on it. Keep any graph generator outside the
audited root import tree, and record the extraction method in its output.
