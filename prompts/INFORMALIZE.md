# Informalize method

> Current instance: `PropertyH`, under `lean/`, for `paper/main.tex`.
> References below to `Paper`, `Paper3`, `lean_2`, `lean_3`, or other past mathematics
> are historical workflow examples only. Those libraries and generated artifacts
> do not exist in this repository. Use `AGENTS.md` and the current formalization log.

A reusable method for turning a **`sorry`-free, axiom-free Lean library** back into natural-language
mathematics — the inverse of `RECURSIVE_FORMALIZATION.md`. The output is a standalone paper whose every
claim is backed by the machine check the Lean already passed. Paper-agnostic: pair this doc with a
**per-instance log** (`INFORMALIZATION_LOG.md`) recording the concrete library, decisions, glossary, and
progress for one application. The full rationale behind every rule here is `docs/INFORMALIZER_DESIGN.md`.

## Preconditions

- A Lean library at (or near) **terminal state**: the numbered results are proved, ideally
  `sorry`-free and resting only on Mathlib's standard axioms (`#print axioms` shows no `sorryAx`). A
  result still carrying `sorry` can be informalized, but its prose **must** flag the gap — never
  informalize a `sorry` into a claim of proof.
- A **dependency dump** for the library (e.g. the `graph-data.js` produced by the visualizer): one node
  per declaration, with statement-type edges and proof-source edges. Used for traversal order and the
  closure gate.
- The **source paper** (`paper.md` or equivalent), used **only** by the divergence-differ role (below),
  never by the informalizer or verifier.

## The faithfulness contract (the one inviolable rule)

**The formal Lean statement is the sole ground truth.** Every sentence of output English is derived from,
and reconciled against, the `theorem`/`def` signature it renders. Docstrings, embedded proof sketches,
and `/- LaTeX — paper.md §X -/` provenance comments are **untrusted leads**: usable to *find* the right
phrasing or the paper locator, never as the source of a claim. They demonstrably drift from the
statements they sit beside; trusting them reintroduces exactly the error informalization exists to
expose. If a docstring and its statement disagree, the statement wins and the disagreement is logged.

## Three tiers — what gets surfaced

Classify every declaration reached, **explicitly, per declaration** (record the call + reason in the
log). `private`/naming are signals, not the test; the test is *"does this carry mathematical content a
human prover would assert, or is it an artifact of working in `Lp` / a.e. equality?"*

- **T1 — numbered results.** The paper's theorems/props/lemmas/cors. **Surfaced with proofs.**
- **T2 — substantive named lemmas.** The genuine mathematical infrastructure (often the gap-filling
  content the source paper assumed). **Surfaced with proofs.**
- **T3 — formalization plumbing.** `private` defs, `=ᵐ`/coercion/representative/measurability bridges,
  CLM-view shims — present only to make Lean typecheck. **Informalized internally** (so the proof that
  needs them is verified and complete) but **absorbed into the prose** of their parent and **not
  surfaced** as standalone statements. Surface them only on explicit request (an appendix mapping prose
  steps to their Lean bridges).

## Proofs — full human granularity, three checks

Surfaced results get **human-granularity proofs**: case splits, invoked lemmas, key identities — depth
scaled to the math (a T1 result that is glue over three lemmas gets a short orchestration paragraph; a
T2 workhorse gets a full multi-step proof). **Elide all Lean-only plumbing** (representative-bridging,
coercion unfolding, `simp`/`ring` bookkeeping). A human proof does **not** map 1:1 onto the tactic block;
"faithful" means three checkable things:

1. **No unsupported assertion** — every mathematical claim in the prose is actually established by the
   tactic proof. Nothing asserted that the Lean does not prove.
2. **Matching dependency set** — the named results the prose *cites* are exactly the T1/T2 declarations
   the formal proof *depends on* (modulo elided T3). Read this set off the proof source (a tactic proof
   must name every T1/T2 lemma it uses); cross-check against the dependency dump as a second opinion.
3. **Matching case structure** — the prose's case splits / inductions mirror the proof's (`by_cases`,
   `induction`, `match`, the `if/then/else` branches).

## The bottom-up engine and the glossary

1. **Topologically sort** the library's dependency DAG. **Leaves = declarations whose only dependencies
   are Mathlib** (no same-library deps).
2. **Walk bottom-up.** When you informalize a declaration, the renderings of all its dependencies
   already exist; write its statement and proof **in terms of those established informal names**, not
   from scratch.
3. **Maintain a first-class glossary** (`GLOSSARY.md`). Every carrier object and surfaced lemma is
   **named once, at its deepest occurrence, and reused upward** — a concept gets *one* agreed
   natural-language name + notation the first time it is reached, and every downstream statement reuses
   it verbatim. The glossary is the informal counterpart of the carrier file (`Basic.lean`); its entries
   map *informal name → Lean declaration → one-line definition*.

The run **terminates** when the numbered results at the top of the DAG have all been reached, rendered,
and accepted.

## The three roles (a per-declaration pipeline)

Informalization has **no objective oracle** (a checker mapping English to Lean would itself be an
autoformalizer), so the faithfulness checks are LLM judgments — and a self-checking writer shares its own
blind spots. Separate the roles; make the verifier adversarial and blind.

- **Informalizer.** Input: the formal statement + proof source (+ docstrings as untrusted leads). Blind
  to the source paper's claims. Output: the English statement + proof + glossary entries, in terms of the
  existing glossary.
- **Adversarial verifier.** A *separate* agent, **blind to the docstrings**. Input: only the formal
  statement, the formal proof, and the produced English. Task: **refute** — find any drift; default to
  "flag if uncertain." Checklist: the three proof checks **plus a statement round-trip** — *"given only
  this English statement, what Lean signature would you write, and does it match the actual one up to
  defeq (same binders, hypotheses, conclusion)?"* This gates glossary admission: an entry is **admitted
  (and reusable upward) only after sign-off.** A flag returns to the informalizer (or the human) before
  the term is reused.
- **Divergence-differ.** The **only** role that reads the source paper's claims, run **after** a result
  is locked. Diffs (locked verified English) ⟷ (paper's claim) and emits **inline `⚠ differs from
  [source]: …` markers** + entries in a consolidated **"Divergences"** section. Machinery with no paper
  counterpart is logged there as "assumed by [author], built here." It **annotates only — gates
  nothing.**

## Output — generated bottom-up, presented top-down

A single assembled paper (`PAPER.md`), in the source paper's house format (callout theorems, `$…$` /
`$$…$$` math, KaTeX-parseable):

- **§-by-§ narrative** mirroring the source paper's sections (the Lean modules usually already map to
  them).
- A **"Supporting development"** section for the from-scratch machinery that has no place in the source
  paper's narrative.
- A **"Divergences from the original"** section (the headline artifact).
- **Lean back-references inline.** Every surfaced statement carries a `[Lib.decl_name]` backlink to its
  Lean declaration — the exact inverse of the Lean files' `/- LaTeX — paper.md §X -/` provenance
  comments, closing the loop both ways.
- **Underscores.** Leave `_` **bare** in prose backlink identifiers (`[Paper3.foo_bar]`) and in ordinary
  `$…$`/`$$…$$` math (there `_` is a subscript; `K_{2m}` must stay bare — escaping it prints a literal
  underscore and breaks the subscript). **Escape `_` → `\_` only inside text-mode macros *within* math**
  — `\text{…}` (and `\mathrm{…}`/`\operatorname{…}` etc.), where `_` is still the subscript operator but
  the content is a literal label. E.g. a backlink placed in a display-math callout:
  `$$ K_{2(m+1)} = \tfrac{2m+1}{d+2m}K_{2m} \qquad\text{`[Paper3.Kmoment\_rec]`} $$` — the two `K_{…}`
  subscripts stay bare, the `Kmoment\_rec` inside `\text{}` is escaped. (The closure-checker strips the
  backslash when resolving such ids.)

## The mechanical gate — the closure-checker

The one objective oracle under the judgment-based process. A small script asserts:

- **Coverage** — `cone(numbered results) \ glossary_keys` contains only T3 declarations (every in-cone
  T1/T2 declaration has an accepted glossary entry).
- **Citation closure** — every `[Lib.decl]` backlink / cited name in `PAPER.md` resolves to a glossary
  entry (`prose_citations ⊆ glossary_keys`). No proof invokes an un-informalized lemma.
- **Math renders** — `PAPER.md`'s math is KaTeX-parseable.

**Per-pass invariant** (the "build stays green" analog): the assembled paper + glossary are **closed** —
no prose references an un-admitted concept. **Terminal state:** full numbered-cone accepted, glossary
closed, divergences documented, `PAPER.md` assembled, closure-checker green.

## Orchestration

- **Solo-first.** Prove the informalizer → verifier → glossary pipeline *solo* on one declaration chain
  before scaling out — decompose the cone, informalize bottom-up, verify (a genuine separate verifier
  agent even in solo-first, so the adversarial/blind property is real), diff, close, log.
- **Wave 0 — the glossary floor.** Informalize the shared carrier vocabulary + the deep leaves first;
  everything upward reuses their names.
- **Wave 1+ — sections in parallel.** With the floor fixed, the §-narratives parallelize with **disjoint
  output ownership** (each agent owns one section's prose, may read the whole glossary, appends only its
  own new T2 entries). Serialize glossary admission (or merge section-scoped fragments). Same caution as
  the formalization run: never naive-parallel — contention here is glossary writes.
- **Batched divergence pass**, then **assemble**.
- Sub-agents **only on explicit go-ahead**; **one commit per section-branch** (bisectable).

## Per-instance log (`INFORMALIZATION_LOG.md`)

Records: the target library + source paper; the file layout; the glossary (or a pointer to it); a
**ledger** of every declaration in the numbered cone — tier, status (TODO / informalized / verified /
accepted / flagged), verifier + round-trip verdict; the divergence findings; and a pass-by-pass history.
The ledger is the live to-do list (cone minus accepted), empty at terminal.
