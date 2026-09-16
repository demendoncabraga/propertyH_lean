# Recursive formalization method

> Current instance: `PropertyH`, under `lean/`, for `paper/main.tex`.
> References below to `Paper`, `Paper3`, `lean_2`, `lean_3`, or other past mathematics
> are historical workflow examples only. Those libraries and generated artifacts
> do not exist in this repository. Use `AGENTS.md` and the current formalization log.

A reusable method for turning a math paper into a Lean **program that compiles, ultimately
`sorry`-free and project-axiom-free**, so that "it builds" *is* the proof-check of the math. Paper-agnostic: pair this doc
with a **per-instance log** (see "Per-instance log" below) that records the concrete paper, library,
file layout, decisions, and progress for one application.

## Completion mandate — recurse until everything is verified

When the user asks to **formalize the paper completely**, that instruction is explicit authorization
to continue through every proof-relevant claim and every missing dependency until the terminal gate
below passes. Do not treat a representation test, a compiling skeleton, completed paper-level glue,
a reduced `sorry` count, or a documented missing theory as completion.

- **Coverage means the whole proof-relevant paper.** Inventory every definition, numbered result,
  substantive unnumbered claim used by another result, and externally cited mathematical result on
  which the paper depends. Every inventory item must either resolve to a verified Mathlib declaration
  with the required signature or become a verified declaration in this library.
- **Recurse through dependencies.** If Mathlib lacks a required result, formalize that result and its
  prerequisites recursively. A whole missing theory is a large subtree, not a stopping point. The
  instruction to formalize completely is the go-ahead to develop it across as many passes as needed.
- **No trust expansion.** The project may contain no `axiom` declarations, no `sorry`/`admit`, and no
  unverified placeholder definitions at terminal. The trusted base is Lean's kernel plus the pinned
  Mathlib only.
- **Persist across passes.** Keep the build green and the debt ledger exact after each pass, then pick
  the next open leaf. Do not report success while the ledger, coverage inventory, or axiom audit is
  nonempty.
- **Pause only for a real blocker.** Stop and ask the user only if the source statement is false or
  materially ambiguous, a required external source is unavailable, or the environment cannot run the
  verifier. Difficulty, expected duration, or missing Mathlib infrastructure are not completion and
  are not reasons to abandon the recursion.

At terminal: the coverage inventory is closed; `grep` finds no `sorry`, `admit`, or project `axiom`;
the full library builds; and `#print axioms` on every inventory root reports only Lean/Mathlib's
standard foundations (`propext`, `Classical.choice`, `Quot.sound`). This verifies the paper *relative
to the pinned Mathlib*; it does not reprove Mathlib itself.

## Preconditions

- The paper's math already exists as Lean **statements** in a buildable library — each
  Lemma/Prop/Theorem present as `theorem … := sorry`, typechecking against a pinned Mathlib. (An
  abstract carrier / vocabulary is **grounded in Mathlib or deferred as `def := sorry`** — never
  axiomatized; the `axiom` keyword is forbidden in the project, see "The axiom gate".)
- A single build command checks the library, and Mathlib is pinned + cached (never rebuilt).

## Bootstrap when the preconditions are absent

If the repository contains only a source paper, satisfy the preconditions first; do not stop and ask
the user to manufacture a Lean skeleton manually.

1. Treat the supplied source (`.tex`, `.md`, or equivalent) as authoritative. A Markdown render or
   blueprint may be created for navigation, but audit it against the source and never let conversion
   artifacts override the original mathematics.
2. Create a Lean 4 project with a pinned Mathlib revision and one command that builds the entire paper
   library. Fetch the binary cache; do not rebuild Mathlib.
3. Create a coverage inventory of all proof-relevant definitions and claims, including external
   dependencies. Record the proposed Lean name, source location, module, and status of every item in
   the per-instance log.
4. Ground the carrier and vocabulary in real Mathlib constructions. Transcribe every inventory item
   into a precisely typed Lean declaration, one module per coherent paper section, with the verbatim
   source formula in a provenance comment. Initial proofs and genuinely unfinished definitions may
   use `sorry`; never introduce an `axiom`.
5. Wire the root module, build the complete statement skeleton, record all open `sorry`s in the debt
   ledger, and then immediately continue with the recursive method below.

`prompts/INIT.md` is a legacy representation-test experiment whose axiom-based shortcuts are
incompatible with complete formalization. It is not authoritative for this workflow.

## Method — recursive divide-and-conquer

Writing any one theorem's full proof is enormous, so decompose recursively:

1. **Pick a target** theorem (see "Traversal" — breadth-first over the numbered-theorem layer).
2. **Attempt its proof.** After a *reasonable effort* (see "Effort threshold"), identify the
   complex chunks.
3. **Abstract each chunk into a `sorry`'d lemma in its own new file**, with a *precise statement* +
   a short *proof sketch* (what it must show, what it may assume). **Use these lemmas to complete
   the current proof** — the current file ends with **no local `sorry`**; the debt moves into the
   leaf files.
4. **Recurse.** Each deferred lemma is a unit of work a later iteration / sub-agent picks up and
   decomposes the same way, until chunks are small enough to discharge directly.
5. **Termination floor = real Mathlib.** Leaves are `sorry`'d lemmas/defs *intended to be discharged
   later*, **never `axiom`s** (the `axiom` keyword is forbidden — see
   "The axiom gate"). A deferred property is a `theorem := sorry`; a deferred object / scalar /
   operator is a `def := sorry`; a missing space is **grounded in Mathlib** (`Lp` over the relevant
   measure) or, if genuinely blocked, a `def := sorry` + `instance := sorry`. The debt is the set of
   open `sorry`s, tracked by the `sorry` warning — not an axiom inventory. The moment a chunk *can* be
   grounded in real Mathlib, do it (see "Grounding") — that is the recursion terminating, one object
   at a time. The *terminal state* of a run is **zero `sorry` and zero project axioms** (see
   "Terminal state").

### Invariant

The library build stays **green** at the end of every pass — the only remaining `sorry`s live in
the deferred leaf-lemma files.

## Grounding — use Mathlib, do not mint axioms

The overriding principle: **ground every object in real Mathlib as much as possible.** The trusted
base should shrink, never grow, as you work.

- **Search Mathlib before writing anything.** A leaf that "should be in Mathlib" usually is — search
  by concept *and* by likely name. Mathlib already has, e.g., orthogonal projections
  (`Submodule.starProjection`: self-adjoint, idempotent, norm-nonincreasing as theorems), Hermite
  polynomials (`Polynomial.hermite`), the Gaussian (`gaussianReal`), `Lp` spaces, and Haar measure
  on compact groups. Reproving a Mathlib one-liner is the most common waste here.
- **Ground spaces in Mathlib; build operators from real constructions.** Prefer a real carrier
  (`L2 := Lp ℝ 2 (gaussian …)`, which is automatically `NormedAddCommGroup`/`InnerProductSpace ℝ`/
  `CompleteSpace`) so its laws are theorems. Build projections as `(subspace).starProjection` rather
  than an opaque map + idempotence/self-adjointness/norm-bound facts — those then come free from
  Mathlib. If a space genuinely has no Mathlib construction yet, defer it as `def Space : Type :=
  sorry` (+ `instance := sorry`), **not** an `axiom`.
- **Ground the *object* over a deferred *property* — it makes the laws free and isolates the one
  missing fact (often net −1 `sorry`).** Instead of an opaque `def op := sorry` whose laws are then
  separate `sorry`s, realize the object as a real Mathlib construction parameterized by a single
  deferred fact, so the laws fall out as theorems. Worked examples (lean_3): a deferred closed
  subspace as `Submodule.topologicalClosure (…)` makes its `HasOrthogonalProjection` a **theorem**
  (was a sorried instance); `ridge`/`act` as `Lp.compMeasurePreservingₗᵢ … h` over one deferred
  `MeasurePreserving h` make `ridge_norm`/`act_radialSine`/`radialSine_isRadial` **proved** — two
  sorried laws replaced by one deeper, atomic measure-preserving leaf. The deferred fact is then
  often itself groundable (see "Probe for enabling primitives").
- **`axiom` is forbidden in the project.** Everything you defer is a
  `sorry`, never an axiom: a deferred **property** is a `theorem := sorry`; a deferred **object /
  scalar / operator / subspace** is a `def := sorry` (`sorry` inhabits any `Sort`, including `Type`
  and instance goals, and surfaces as `sorryAx` — tracked, in-place-upgradeable debt). There is no
  "structure axiom" category and no "carrier-axiom floor": missing structure is a sorried `def`, not
  an `axiom`. This is **enforced**, not advised — see "The axiom gate".
- **Why `sorry`, not `axiom`.** Both inject the trusted base (a `sorry` is `sorryAx`), so the gain is
  *not* soundness — it is **visibility** (the `sorry` warning is a greppable, CI-enforceable debt
  ledger), **honesty** (`#print axioms` shows `sorryAx` = "not actually proved", instead of dressing
  an assumption up as a trusted primitive), and **dischargeability in place** (swap `sorry` for a
  proof/definition with no declaration churn). Relocating a `sorry` into an `axiom` is not progress —
  it hides the debt and is rejected by the gate. **Never** turn a numbered paper theorem into an
  `axiom`.
- **Audit with `#print axioms <thm>`.** Before terminal its only non-Mathlib dependency may be
  `sorryAx` for leaves that remain open. A fully discharged result shows only Mathlib's standard
  axioms (`propext`/`Classical.choice`/`Quot.sound`) and **no `sorryAx`**. Any other named axiom is a
  gate violation — replace it with a real construction or proof.
- **`sorryAx`-free is the per-declaration "done" signal — track the front, not just the count.** Run
  `#print axioms` per declaration: a `sorryAx`-free one is genuinely complete (rests only on the
  Mathlib base), even if the raw `grep sorry` count elsewhere is still high. The
  honest progress metric is *which* declarations are `sorryAx`-free, not the headline number — a run
  can have its entire carrier `sorryAx`-free while section glue still carries debt (see "Two kinds of
  deep leaf"). The lean_3 viz encodes exactly this (green border = `sorryAx`-free) so the completion
  front is visible at a glance.

### Probe for enabling primitives, not just the target lemma (and re-probe each pass)

**"Not in Mathlib as a named lemma" ≠ "infeasible."** Mathlib routinely has the *enabling primitives*
— a measure construction, an FTC variant, a `withDensity` / change-of-variables bridge, an
isometry-invariance — even when it lacks your target theorem. Before deferring a leaf as `sorry`,
grep for the **building blocks the proof would reduce to**, not just its name; and **re-probe after
every lemma you prove**, since each new tool unlocks the next. (A shallow recon — even a thorough one
by a sub-agent — will under-report what is reachable; trust a primitive-hunt over a name-search.)

Worked example — the lean_3 carrier went to **zero `sorry`** this way:
- A shallow search "concluded" the Gaussian distributional facts were multi-month. A deeper probe
  found `ProbabilityTheory.stdGaussian` + `map_pi_eq_stdGaussian` + `stdGaussian_map` (isometry-
  invariance), turning "an orthogonal `U` preserves `γ^d`" and "a unit dual pushes `γ^d → γ`" into
  ~20-line proofs.
- The Hermite `L²(γ)` orthogonality is genuinely absent, but was *buildable* from
  `integral_eq_zero_of_hasDerivAt_of_integrable` (whole-line FTC) + `integrable_withDensity_iff_…` +
  `Polynomial.hasDerivAt`: → **Stein's identity** → the Hermite derivative recurrence → the
  orthogonality induction → `⟨h_m,h_n⟩ = m!·δ`, then `Hbasis_inner` by one Fubini step.
- Each proof cascaded: Stein gave the Gaussian moments *and* the orthogonality; the orthogonality
  made the tensor case a one-liner. What was a "deep leaf" three passes ago became a short proof.

So **deferral is a last resort after a genuine primitive-hunt, revisited as the run accumulates
tools** — and the run's own foundational lemmas (a Stein identity, a Parseval) are the highest-value
primitives to build first, because one discharges a whole cluster of siblings.

## Terminal state — zero `sorry` and zero project axioms

Fully discharging everything down to bare Mathlib can be a multi-month subproject (building the
missing infrastructure for real). That is the *only* honest terminal state: there is **no
intermediate "clean floor" milestone** in which missing facts are parked as axioms. Until the deep
objects (e.g. Wiener chaos, a uniform-sphere measure) are actually built, the run sits at **"skeleton
green"** — every numbered theorem proved as glue over still-open sorried leaves, build green — and
that is reported honestly as debt, not dressed up as a clean floor.

The working state of a run is therefore: **the library builds green, the numbered theorems are
complete glue, and the debt is the enumerated set of open `sorry`s** (the ledger), shrinking pass by
pass. The *terminal* state is when that ledger is empty.

### Two kinds of deep leaf — categorize before estimating

When a leaf bottoms out in "missing Mathlib," decide *which* kind it is — the effort differs by orders
of magnitude, and conflating them either wastes a primitive-hunt or wrongly defers a short proof:

- **Buildable-now (enabling primitives exist).** The target theorem is absent, but the primitives it
  reduces to are present, so it is a bounded build (tens–few-hundred lines) you should just *do* — not
  defer. E.g. (lean_3) Stein's identity, the Hermite `L²` orthogonality, the Gaussian
  measure-preserving facts. These are how the carrier reached zero `sorry`.
- **Whole-missing-theory (no primitive bridges it).** The leaf needs an entire absent theory — a
  genuine multi-day/week subproject. **Name the specific missing theory in the ledger** and, under a
  complete-formalization mandate, recursively build it rather than treating it as a boundary. E.g.
  (lean_3) the Wiener-chaos decomposition needs *polynomial
  density in `L²(γ)`* (the Gaussian moment problem); the sphere-moment formulas need a
  `Measure.toSphere` transformation/invariance law; the ridge identity needs the *Hermite EGF*; the §6
  energy bound needs the *`χ²_d` distribution* — none in Mathlib, none bridged by an existing
  primitive.

The split is real and worth reporting honestly: a run can be **carrier-complete** (`Basic`/Core at
zero `sorry`, audited `sorryAx`-free) while the **section glue** still rests on whole-missing-theory
leaves. The carrier being done does **not** mean the library is — `grep sorry` over the whole tree is
the source of truth. A `sorry` blocked on a whole missing theory may be an honest intermediate status,
but it is never a completed formalization; keep decomposing and proving that theory until it closes.

**Acceptance gate for "finished":**
- build green, **zero `sorry` terms** (grep the source, don't just trust warnings);
- `rg -n '^[[:space:]]*axiom[[:space:]]' <srcDir> -g '*.lean'` returns no project declarations;
- `rg -n '\b(sorry|admit)\b' <srcDir> -g '*.lean'` returns no proof holes (excluding comments that merely
  discuss the words);
- `#print axioms` on every coverage-inventory root and every project leaf shows **no `sorryAx`** and
  only `propext`, `Classical.choice`, and `Quot.sound`;
- every proof-relevant source claim and external dependency is marked verified in the instance log;
- the debt ledger is empty.

**Per-pass acceptance** (the green-build invariant, made mechanical): build green; the axiom-gate
search passes; `#print axioms` on touched theorems shows only `propext`, `Classical.choice`,
`Quot.sound`, and temporary `sorryAx`; the `sorry` search is the updated debt ledger. `sorryAx` *is expected* every pass before terminal — it
is the honest signal of remaining work, not a failure.

## The axiom gate — the one mechanical rule

The single rule that keeps the trusted base from growing, enforced by a script so it cannot be
quietly ignored (an earlier run *had* the "prefer `sorry`" advice and ignored it — advice without
teeth loses to whatever the acceptance gate rewards):

- **Zero project axioms.** There is no `ScopeBoundary.lean` escape hatch in a complete formalization.
  Modeling limits and asymptotic claims must be represented precisely and proved, not declared.
- **The grep gate (run every pass).** `rg -n '^[[:space:]]*axiom[[:space:]]' <srcDir> -g '*.lean'`
  must return no lines. Any project axiom fails the pass — replace it with a grounded definition and a proof. Temporary
  deferral uses `def := sorry` / `theorem := sorry`, which remains visible in the debt ledger.
- **The `#print axioms` audit.** On every touched theorem, the only entries may be Mathlib's standard
  three plus `sorryAx` while leaves remain. A different named axiom means one slipped in through a
  project or imported dependency — track it down and eliminate it.
- **The `sorry` ledger.** `rg -n '\b(sorry|admit)\b' <srcDir> -g '*.lean'` is the live debt list after
  comment-only matches are excluded; it equals the set of open leaves, shrinks every pass, and is
  empty at terminal.

Deferral without axioms, by kind: **property** → `theorem … := sorry`; **scalar / element / operator
/ subspace** → `def … := sorry`; **space / type** → ground as Mathlib `Lp` if possible, else
`def … : Type := sorry` + `instance … := sorry`. All surface as `sorryAx`: visible, greppable,
upgradeable-in-place debt.

## Leaf artifact format (per deferred lemma)

Each spawned leaf file contains, at minimum:

- the **exact `theorem`/`lemma` signature** it must satisfy — a rigid contract; the parent proof
  depends on it. Do not change it without updating the parent (see "Signature discipline").
- a **docstring**: what it proves (paper reference if any), what it may assume, a one-paragraph
  **proof sketch**.
- the **source LaTeX math** the statement transcribes, as a comment immediately above the
  declaration (see "Provenance comments").
- `:= by sorry`.

## Traversal — breadth-first over the numbered-theorem layer

When the preconditions hold, **all** the paper's numbered theorems already exist as stated `sorry`s
that reference each other as sorried lemmas, so none is blocked on another. Exploit this: work
**breadth-first** on the numbered-theorem layer, **depth-first** only inside the deep foundational
leaves.

The coverage inventory, not numbering alone, defines the roots. Apply the same treatment to every
substantive unnumbered claim used by the paper; numbering is only the usual organizational layer.

- **Wave 0 — prove every numbered theorem's *glue*.** Formalize each paper proof, treating cited
  numbered results **and** atomic facts as sorried. Order within the wave is free (all statements
  exist). After Wave 0, every paper theorem is "proved modulo named atomic lemmas" — a complete,
  green, inspectable skeleton of the whole paper.
- **Wave 1+ — discharge the atomic leaves**, each possibly spawning its own sub-leaves; recurse.
- **Depth-first for the deep leaves.** The genuinely foundational subtrees (heavy real-analysis
  lemmas; the carrier's real definitions / missing-Mathlib infrastructure) are each their own
  subproject, done DFS *within* themselves.

Why breadth-first here: it mirrors the paper's structure (one glue task per numbered proof);
it **surfaces shared atomic needs together** so they become one shared facts file instead of
duplicated per-branch leaves; it parallelizes cleanly (a wave is a batch of independent tasks, one
per theorem — ideal for sub-agents); and it validates every signature early.

## Operating rules

- **Per-pass scope.** One numbered theorem fully reduced per pass (its proof has no local `sorry`,
  all gaps pushed to named leaves, build green) — or, with sub-agents, one wave.
- **Reuse, don't re-spawn.** Cited numbered theorems are used as sorried children; create new leaf
  files only for genuinely-new atomic gaps.
- **Effort threshold.** Defer a chunk after a real **primitive-hunt** (grep for the *building blocks*
  the proof reduces to — a measure construction, an FTC/`withDensity` bridge, an invariance lemma —
  not just the target's name; see "Probe for enabling primitives" under Grounding) and a few failed
  tactic attempts with no progress. If the primitives exist, it is **buildable-now** — build it, don't
  defer. Defer only when the chunk is a genuine sub-theorem with no primitive to bridge it (a
  whole-missing-theory leaf), and **re-attempt deferred leaves as later passes add tools** — a foundational
  lemma you prove (a Stein identity, a Parseval) often turns a sibling's `sorry` into a short proof.
- **Factor shared primitives (BFS one level down).** When a leaf does not reduce to anything that
  exists yet, push it *one level* to a more-primitive **named** fact that several siblings share,
  rather than leaving each sibling an independent opaque `sorry`. Factor out the common scalar /
  object the paper's own proof isolates (e.g. a moment, a kernel) so the siblings become glue over
  one primitive. Do **not** do this by relocating the literal statement into an `axiom` (no gain, see
  "Grounding") — the factored primitive is itself a sorried `def`/`theorem` in a shared facts file,
  strictly *more primitive* and *closer to Mathlib* than the leaves it discharges.
- **Defining-value leaves.** Some "theorems" are really the *defining value* of a carrier
  scalar/object — a closed form for a moment `K_n`, `𝔼[V^α]`, etc. Give the object a **real `def`
  grounded in Mathlib** (e.g. `K_n := gaussMoment n / gaussNormMoment d n`, or a moment as an
  integral) so its value-equations and relations become provable `theorem`s; if the construction is
  blocked on deeper infrastructure, use a `def := sorry` placeholder. **Never give it a value as an
  `axiom`.** The value-equations/inequalities themselves are `theorem … := sorry` discharged later,
  and the numbered theorem becomes `rw`/`rfl`/`field_simp` glue over them.
- **Isolate the finite→infinite bridge.** Keep `tsum`/`Filter.Tendsto`/Parseval out of *intermediate*
  statements. When a proof genuinely needs the infinite sum, put the finite→infinite step in a *single
  named* bridge lemma (`theorem … := sorry`, e.g. a Parseval `‖P x‖² = ∑' …` + its `Summable`) and do
  everything else finitely. (ℓ²-Cauchy–Schwarz over a tail is Mathlib's `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` with
  `p = q = 2`.)
- **Don't force `whnf` on opaque carrier terms.** A `‖·‖`-vs-`|·|` (or coercion) mismatch on an opaque
  inner-product / carrier term can blow up `whnf` and the heartbeat budget. Bridge the notation in a
  separate `have` (e.g. `Real.norm_eq_abs`) rather than letting a tactic try to unfold the opaque term;
  this fixes it with no `maxHeartbeats` bump.
- **Leaf granularity & location.** One file per leaf lemma, named after the lemma. **Shared atomic
  facts** (e.g. structural properties of the carrier that many theorems need) go in a single shared
  *facts* module so siblings reuse one statement; **one-off** leaves specific to a single parent go
  under a per-parent leaf directory. BFS makes the shared ones visible — prefer the shared module
  whenever ≥2 theorems need the fact.
- **Execution model.** Prove the pattern *solo* on one theorem first (no sub-agents): decompose,
  complete the proof against fresh sorried leaves, green build, update the log. Only then scale out
  by dispatching **sub-agents** — see "Sub-agent orchestration". Spawn agents only on explicit go-ahead.
- **Signature discipline.** Never silently change a statement's signature — downstream proofs and
  sibling leaves depend on it. If a statement is too weak / too strong / wrong (e.g. an
  under-constrained hypothesis that makes it false), **stop and flag it** with a recommended fix
  before changing it.
- **Provenance comments.** Above each transcribed declaration, include the **source LaTeX math** it
  formalizes as a comment, so the Lean is traceable back to the paper at a glance. Put the verbatim
  paper formula (e.g. `$\Pi_{\mathrm{Rad}}(g^v) = \sum_n \sum_{|\alpha|=n} \dots$`) on a comment line
  just above the `theorem`/`def`; keep the math as written in the paper (don't pretty-print it into
  Lean syntax — that's what the declaration itself is). For multi-line statements use a `/-- … -/`
  docstring or a `/- … -/` block. This is the bridge that makes the "LaTeX → Lean as a faithful
  representation" check inspectable.

## Sub-agent orchestration (parallel branches)

Once the solo pattern is proven and the leaf set is enumerated, dispatch sub-agents — but the leaves
are less independent than they look. Hard-won mechanics:

- **Disjoint file ownership.** Give each agent its own section file(s) *plus a new facts/leaf file*
  for any sorried leaves it introduces. Two agents must never edit the same file, and **no agent edits
  the shared carrier** (`Basic`/Core) **or `ScopeBoundary.lean`**: new sorried `def`/`theorem` leaves
  go in new files, so ownership stays disjoint and integration is trivial.
- **Cluster coupled leaves under one agent.** Leaves that share structure (e.g. all the chaos /
  Parseval facts, or all of one section's moment values) go to a *single* agent, so the shared sorried
  primitives are introduced once and stay consistent. Splitting them invites duplicated or subtly
  inconsistent leaf statements.
- **Sequential, or worktree-isolated — never naive-parallel in one repo.** Concurrent `lake build` in
  the same working tree contends on the build lock, and worse, one agent's build compiles another
  agent's half-written file and reports spurious errors that send it thrashing on problems that aren't
  its own. Run agents one at a time in the shared repo (simplest, and the agent's build validates
  directly), or give each its own git worktree.
- **Agent contract.** Each agent: reads this method doc + its paper section + the carrier + the
  already-proved facts it may reuse; edits **only its owned files**; **changes no signature**;
  **introduces no `axiom`**; grounds in Mathlib first, else introduces minimal
  sorried leaves (`def`/`theorem := sorry`, gap-tagged, with provenance) strictly more primitive than
  the theorem; keeps the build green; **does not commit**; and reports back its new sorried-leaf list
  (each with a "to be proved by …" sketch) plus the axiom-gate search + a `#print axioms` audit (only
  `propext`, `Classical.choice`, `Quot.sound`, and temporary `sorryAx`).
- **Orchestrator integrates per branch.** After each agent returns: re-run the build, run the
  `#print axioms` audit yourself on the newly-proved theorems, commit *that branch alone*, and update
  the log. One commit per branch keeps history bisectable; verifying each branch before the next keeps
  a bad branch from poisoning the rest.

## Per-instance log

Keep a separate, per-application log next to the instance's code (not in this method doc) recording:
the target paper and library, the concrete file layout, the complete coverage inventory,
instance-specific decisions, known issues / flagged signature problems, and a **ledger** of every
deferred leaf (parent, status:
TODO / in-progress / proved) plus a pass-by-pass history. This keeps the method reusable across
papers while the log captures one concrete formalization.

Throughout a run, the log carries a **debt ledger**: every open sorried leaf (`def`/`theorem :=
sorry`), with parent and a one-line discharge sketch — the live to-do list, equal to the actual proof
holes reported by `rg -n '\b(sorry|admit)\b' <srcDir> -g '*.lean'`. There is **no** axiom "floor" and
no scope-boundary exception: missing
structure is temporary sorried debt, not an axiom. At terminal the coverage inventory is closed, the
ledger is empty, and the project contains no axioms.
