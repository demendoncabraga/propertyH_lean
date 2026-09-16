# Prompt: build an interactive HTML dependency graph of a Lean library

> Current instance: `PropertyH`, under `lean/`, for `paper/main.tex`.
> References below to `Paper`, `Paper3`, `lean_2`, `lean_3`, or other past mathematics
> are historical workflow examples only. Those libraries and generated artifacts
> do not exist in this repository. Use `AGENTS.md` and the current formalization log.

Reusable prompt that reproduces the `lean/viz/` visualization for any Lean 4 / Mathlib library in
the repo. Hand it to an agent together with the target library's **name**, **namespace root**, and
**source directory** (for the `Paper` library these are `Paper`, `` `Paper ``, and `lean/`).

The output is a standalone HTML graph: nodes are the library's declarations (axioms / theorems /
defs), edges are the dependencies between them; clicking a node shows its rendered math, the axioms
it rests on, the Mathlib lemmas its proof cites, and the verbatim Lean source. It opens **offline**
by double-clicking — no server, no internet.

---

## Inputs (fill these in per library)

- `LIB` — the `lake` library name and its `srcDir` (e.g. `Paper`, `lean/`). Confirm in `lakefile.toml`.
- `ROOT` — the namespace root that tags this library's declarations (e.g. `` `Paper ``). All nodes
  are constants whose `Name.getRoot == ROOT`.
- `OUT` — output directory for the viz (default: `<srcDir>/viz/`, e.g. `lean/viz/`).
- `GEN` — the generator module, placed **outside** the library's import tree (e.g.
  `lean/<LIB>/Viz/DumpGraph.lean`), so nothing imports it and it never affects the audited build.

## Fixed decisions (do not re-litigate)

1. **Check the pinned toolchain before selecting an extraction method.** Inspect whether
   imported declarations expose genuine elaborated proof bodies. Use semantic proof-term
   dependencies when available; otherwise label source-text dependencies as heuristic.
   Do not infer proof availability from another project's experience. Distinguish:
   - `type` edges: constants in a declaration's type;
   - `axiom` edges: transitive foundational dependencies from the axiom audit;
   - `proof` edges: proof-term dependencies when verified available, or explicitly labeled
     source-text approximations otherwise.
   A source-text scan is not a faithful substitute for an exact proof dependency set.
2. **One node per real source declaration.** Keep only constants with `Name.getRoot == ROOT`, not
   `Name.isInternalDetail`, of kind axiom/theorem/def, and that have a `findDeclarationRanges?`.
   Other (Mathlib) constants are **not** nodes; record the proof's external citations as node
   *metadata* only.
3. **Generator is a Lean meta module outside the import tree.** A `run_cmd … Command.liftCoreM` that
   walks the environment and writes `OUT/graph-data.js` as `window.<LIB>_GRAPH = {nodes,edges};`
   (build it with `Lean.Json`; `.compress` for serialization, which handles escaping). It must read
   the source files itself (it has `IO`) to slice verbatim text and extract provenance.
4. **Renderer is hand-written, static, offline.** `OUT/index.html` + `OUT/app.js` are checked in;
   only `graph-data.js` is generated. Data is delivered as a JS global (not `fetch`), so the page
   opens over `file://` with no server. **Vendor every library locally** (see step 6) — no CDN.
5. **Encoding.** Color = kind (axiom / theorem / def). Shape = a distinct shape for "headline"
   declarations (those carrying a provenance/`LaTeX` comment block) vs. the rest. Size ∝ in-degree.
   Layout: dagre, top→bottom, so foundations (axioms) settle toward the bottom. *(For an in-progress
   library where the goal is showing how much is done, prefer the radial "progress onion" layout
   below instead of dagre.)*

## Build steps

### 1. Inspect proof availability in the pinned toolchain

Before choosing a graph model, inspect the environment with a throwaway module that
`import`s the library:

```lean
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← getEnv
  let ci := (env.find? `<ROOT>.<some_theorem>).get!
  logInfo s!"hasValue={ci.value?.isSome}"      -- false ⇒ proofs stripped ⇒ hybrid model
  logInfo s!"axioms={(← collectAxioms `<ROOT>.<some_theorem>).toList}"  -- should be real axioms
```

### 2. Collect nodes

`env.constants.fold` to gather constants with `Name.getRoot == ROOT`; filter to
`!isInternalDetail && kind ∈ {axiom,theorem,def}` and `findDeclarationRanges?` present. Build a
`NameSet` of node names and a short-name → full-name table (short name = full name minus `ROOT.`).

### 3. Compute edges per node

- `type`: `ci.type.getUsedConstants ∩ nodeSet`.
- `axiom`: `(← collectAxioms n) ∩ nodeSet`, minus the `type` set. (Also keep the full
  `collectAxioms` list as node metadata — it shows the foundational `propext`/`Classical.choice`/
  `Quot.sound` grounding too.)
- `proof`: strip comments from the declaration's source (handle nested `/- … -/` and `-- …`), split
  into `[A-Za-z0-9_.]+` tokens, map each token (after stripping a leading `ROOT.`) through the
  short-name table; subtract the `type` and `axiom` sets. Tokens that look qualified (contain `.`)
  but match no node are recorded as Mathlib-citation metadata.

### 4. Slice source + provenance

Use `findDeclarationRanges?` for `[startLine, endLine]`, and `env.getModuleIdxFor?` +
`env.header.moduleNames` → module name → source path (`srcDir/Components/Of/Module.lean`). Read the
file, slice the range, and **walk upward** over contiguous comment blocks (skipping blanks, stopping
at a `/-!` module-doc or a code line) to also capture the preceding doc/provenance comment. If a
captured comment contains your math marker (e.g. `LaTeX`), extract that block as the node's `latex`.

### 5. Emit and run

Write `window.<LIB>_GRAPH = <json>;`. Per node store: `id, label, kind, numbered (has latex),
file, line, source, latex, axioms[], mathlib[]`. Per edge: `source, target, kind`.
Build/run from the **project root** (the generator uses paths relative to CWD):
`touch <GEN> && lake build <module-name-of-GEN>`. The `touch` forces re-elaboration since `lake`
skips unchanged modules and the file is written as an elaboration side effect.

### 6. Renderer (`index.html` + `app.js`)

- **Vendor offline:** download Cytoscape, dagre, cytoscape-dagre, and KaTeX (CSS + JS +
  `auto-render`) into `OUT/vendor/`, plus the woff2 fonts the KaTeX CSS references (grep
  `fonts/KaTeX_*.woff2` out of `katex.min.css`; woff2-first ordering means browsers fetch only those).
  Point `index.html` at `vendor/…`, not any CDN.
- **Graph:** Cytoscape + `dagre` layout (`rankDir: "TB"`). Color by kind, shape by "headline" flag,
  edge `line-style` by kind (solid/dotted/dashed), arrows `dependent → dependency`.
- **Interactions:** click a node → dim everything except its `successors()` (dependencies, one color)
  and `predecessors()` (dependents, another); detail panel with the rendered `latex`
  (`renderMathInElement`), the axiom-grounding pills, the Mathlib-citation list, and the verbatim
  source in a `<pre>`. A search box (Enter → center first label match), kind/edge-kind toggles, a
  reset button, and a `#sel=<id>` deep-link on load.
- **Load KaTeX synchronously** (no `defer`) so `renderMathInElement` is defined before the first
  render (e.g. a deep-link selection in `cy.ready`).

## Variant: the progress onion (for an *in-progress* recursive formalization)

When the library is mid-formalization (some leaves still `sorry`), a generic dagre DAG **hides
progress** — the proved nodes and the open ones are scattered. A **radial "dependency onion"** keyed
to the recursive method makes the formalization frontier legible. This is what `lean_3/viz/` uses
(its `app.js` diverges from `lean/viz/`); adopt it when the goal is *showing how much is done*, not
just the structure.

- **Radius = dependency depth.** Inject one synthetic **paper** hub node at the center (the only
  non-`ROOT` node; exclude it from filters/overlays). Compute each real node's `depth` = longest path
  from an in-degree-0 *root* theorem along `dependent → dependency` edges (memoized DFS; the graph is a
  DAG so this terminates). Lay out with Cytoscape `preset` (not concentric — you want full control):
  `pos(paper) = origin`, and on ring `d` place nodes at `radius(d)`, evenly by angle. Make
  `radius(d)` adaptive (`max(prev + gap, count·spacing/2π)`) so a populous inner ring still fits.
  **Gotcha:** `preset`'s `positions` callback is passed the **node element**, not the id —
  `positions: node => pos[node.id()]`; returning by a bare id silently collapses every node to the
  origin.
- **Why this surfaces progress.** The recursive method discharges debt *into leaves*, and the headline
  theorem is the shallowest node — so the live `sorry`s and everything they taint land in the **inner**
  rings while the proved/grounded carrier fills the **rim**. Progress then reads as *the amber core
  shrinking inward*. (Verify with real data first: in `lean_3` all debt sat in rings 1–4 and rings
  5–12 were 100 % proved — confirm your library's completion is actually depth-correlated before
  committing to this story.)
- **Solid-ground field.** Paint a translucent **green** radial-gradient blob under every proved
  (`sorryAx`-free) node on a `<canvas>` *under* the Cytoscape canvas (a `#stage` wrapper holding
  `#ground` + a transparent `#cy`), redrawn on `cy.on("render pan zoom")` (rAF-coalesced) using
  `node.renderedPosition()`/`renderedWidth()`. Additive blending (`globalCompositeOperation =
  "lighter"`) merges neighbours into a *field*; keep per-blob alpha low (~0.1–0.15) or a dense cluster
  blows out to white. Add an **amber** haze under the live-`sorry` nodes for the unfinished core, and
  faint concentric **ring guides**. Make the field a toggle.
- **Primary sorries + blast radius.** Have the generator emit `selfSorry` (the literal `sorry` keyword
  survives **comment-stripping** of the decl's own source — so `sorryAx` and a "sorry" inside a comment
  do *not* count) and `section` (paper-section bucket, for angular grouping). Render `selfSorry` nodes
  with a distinct fill, and on click light their **blast radius** = the transitive `predecessors()`
  (everything that depends on the open leaf), reporting the cone size. Note that early on most cones
  are size 0 — a still-`sorry`ed leaf's consumers are themselves unwritten, so the proof-edges don't
  exist yet; the cones fill in as the formalization proceeds.
- **Border ring still encodes per-node completeness** (green = `sorryAx`-free, amber = rests on a
  `sorry`), computed from the cached `collectAxioms` set; the onion + field are the *aggregate* view on
  top of it. Drop the now-unused `dagre`/`cytoscape-dagre` script tags (the layout is computed in JS).

## Gotchas (seen on Lean v4.30)

- The newer `String.Slice` API: `String.drop` returns a `String.Slice` (use
  `(s.toSubstring.drop k).toString`); `String.trim` is deprecated (warning only). A type mismatch in
  a `run_cmd` helper silently becomes `sorry` and aborts evaluation with "depends on the 'sorry'
  axiom" — fix the helper, don't reach for `#eval!`.
- Nested block comments: a `/-` inside a doc comment opens a nested comment. Don't put a literal
  `/-` in the generator's own docstrings.
- `lake build` runs the generator's `IO` with CWD = project root; run it from there or relative
  `readFile`/`writeFile` paths break.
- Inspect proof-body and axiom-report behavior on the actual pinned toolchain. The
  historical proof-stripping observation is not evidence about this project's environment.

## Done when

- `lake build <GEN module>` prints "wrote …/graph-data.js: N nodes, M edges".
- `OUT/index.html` opens offline (verify with network disabled, e.g. `unshare -rn -- google-chrome
  --headless=new --screenshot=… file://…`) and renders the graph + KaTeX math.
- A `<srcDir>/viz/README.md` documents how to open and regenerate; `AGENTS.md` gets a pointer.
- Commit everything.
