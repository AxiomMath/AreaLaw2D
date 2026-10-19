You are going to refactor the Lean formalization in `OpenAI/` (and the library it rests on in `Arealaw/`) into a one-to-one translation of the paper.

References you are going to use:

- The paper: `paper/paper.pdf`, LaTeX source in `paper/sections/*.tex` (OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026).
- The digest: `digest/00-overview.md` and `digest/01-introduction.md` … `digest/11-geometry.md`. One file per paper section. Every result, definition and load-bearing proof step of the paper has an anchor `D<section>.<n>` with its proof broken into numbered steps `D<section>.<n>.<k>`, the inputs it consumes (**Used from**), what later sections take from it (**Output**), and whether it is a textbook fact (**Standard?**). The digest was checked line by line against the LaTeX. It is the specification. When the digest and the Lean code disagree about what a proof does, the digest wins; when the digest and the paper disagree, the paper wins and you fix the digest.
- Do not read `docs/oai265/`, `HISTORY.md` or any Lean docstring that narrates the history of the development. They describe how the current code came to be, not what it should be. Delete them in Step 2.

While refactoring, you are going to log notes in `RefactoringResult.md`. Simple, detailed, concise. The format is fixed in the last section of this file.

Frozen, never edited:

- `OpenAI/Statements.lean`: the statement layer. Every paper result is a `def … : Prop` there (`AreaLaw`, `AreaLawCorollary`, `PositiveReplacement`, `CollarBound`, `Amplification`, `TwoFamilyCancellation`, `TwoFamilyDecomposition`, `ConditionalContinuity`, `MarginalTails`, `BufferDiscount`, `InitialBoxEstimate`). The refactored development must prove exactly these props. You may add local notation and abbreviations on top of them; you may not change them.
- `Challenge/Basic.lean`, `Solution/Basic.lean`, `Comparator/`. The comparator run must still accept `Solution/` against the refactored code. `Solution/` may be re-pointed at new names, nothing else.

Baseline, measured on the current tree (audit files excluded everywhere, they are `#print axioms` scripts and never count):

| Quantity | Value |
|---|---|
| Paper | 7 069 LaTeX lines, 11 sections, 1 theorem, 10 propositions, 24 lemmas; 238 digest anchors |
| `OpenAI/` | 916 files, 181 500 lines; `Arealaw/` 35 files, 5 700 lines |
| Declarations in `OpenAI/` | 7 784 (6 292 `theorem`, 131 `lemma`, 1 083 `def`, 37 `abbrev`, 34 `structure`, 39 `instance`) |
| Declarations whose name occurs nowhere else in the tree | 1 398 |
| Declarations whose name occurs exactly once elsewhere | 2 543 |
| Files under 80 lines | 136; files at top level of `OpenAI/` (no subdirectory) 575, of which 94 begin with `Replica` |
| Import depth of `OpenAI.AreaLaw` | 48 |
| Files not in the import closure of `OpenAI.AreaLaw` | 46 (6 342 lines) |
| Lean lines per paper line | 26 |

Target: ≤ 90 000 lines for everything that proves the frozen statements (−50 %), with the structure of the paper visible in the file tree, the declaration names and the proof bodies.


# Step 0: the map

Before changing any proof, build `Map.md`: one table per digest file, one row per anchor.

| Anchor | Paper label | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|

Status is one of:

- `faithful`: one Lean declaration states the anchor and its proof follows the digest's steps in order.
- `drift`: the Lean proof reaches the anchor's conclusion by a different route than D*.n.1 … D*.n.k. Record the two routes in one line each.
- `smeared`: the anchor exists in Lean only as the sum of several declarations, none of which states the anchor itself.
- `missing`: no declaration states the anchor; the downstream code worked around it.
- `overbuilt`: the anchor is there but with generality, hypotheses or auxiliary theory the paper does not have (a parameter the paper fixes, a class the paper never varies, a lemma stated for all `k` when the paper needs `k = 2`).

Action is one of `keep`, `golf`, `merge into <anchor>`, `inline into <anchor>`, `restate`, `prove` (for `missing`), `cut`.

Then do the reverse pass: every declaration in `OpenAI/` and `Arealaw/` that is in no row of `Map.md` is listed in `Map.md` under "Unmapped", with one of:

- `standard`: a textbook fact the paper uses in one line. Check Mathlib and Physlib for it (`lean_leansearch`, `lean_loogle`, `grep` in `.lake/packages/mathlib` and `.lake/packages/Physlib`). Found → `replace-by <name>`. Not found → it goes to the library tree of Step 2, stated once, in Mathlib's generality and naming.
- `scaffold`: bridges between two encodings of the same object, typecasts, wrappers that rename a hypothesis, restatements with one argument specialised. Action `cut` once the two sides are unified.
- `dead`: not reachable from `OpenAI.AreaLaw`, `OpenAI.PositiveReplacement` or any other frozen statement's proof, and not a Mathlib candidate. Action `cut`. The 46 files outside the import closure start here, but confirm each by name search, not only by import.
- `foreign`: proved for a different paper (file headers that cite a tensor-network or PEPS paper, or "ported from" another repository with no paper anchor). Action `cut`, unless the reverse pass finds a use on the path to a frozen statement, in which case it becomes `standard` or gets an anchor.

`Map.md` is the contract for Step 1. Every row's Action is executed; every executed row is ticked. You will find that most of the 1 398 never-referenced and 2 543 once-referenced declarations fall under `inline`, `scaffold` or `dead`. Do not trust the count: confirm by search before cutting.

Two things to look at first because they decide the shape of everything else:

1. The scalar field. The paper works over $\mathbb C$. The frozen statements quantify over `[RCLike 𝕜]`. Decide once: develop everything over `ℂ` as the paper does and prove the frozen `𝕜`-generic statements by a single transfer theorem at the top, or carry `𝕜` through. Choose the first unless a specific anchor makes it impossible; record the decision and the reason. Delete every piecewise transfer that the choice makes unnecessary.
2. The encoding of regions, partial traces and entropy. The statements use `Reg`, `pureState`, `SubState.regionEntropy`, `mutualInfo` from `Arealaw/`. Any second encoding of the same notions inside `OpenAI/` (a different tensor-product type, a different entropy, a bridge file between them) is scaffolding: pick the statement encoding, re-prove what the other encoding carried, delete the bridge.


# Step 1: the golfed draft

Write `AreaLawRefactored/`, one file per paper section, in dependency order as given by `digest/00-overview.md` ("Proof architecture"): `S02_Preliminaries`, `S03_InitialBox`, `S04_Quasilocal`, `S05_Conditional`, `S06_Replicas`, `S07_Transport`, `S08_Comparators`, `S09_Scanner`, `S10_Amplification`, `S11_Geometry`, `S01_AreaLaw` (the assembly, Theorem 1.1 and Corollary 1.2 last). Each file imports only the files of the sections its digest lists under **Dependencies** and the library tree. The reason this is not a single file as in the Cohn–Elkies refactor is size: 180 000 lines do not elaborate as one module. Everything else about the single-file discipline applies: one pass, nothing left behind in `OpenAI/`.

The rules.

- One declaration per anchor. Its name is the paper's label, not a description: `lemma_6_4`, `prop_9_6`, `eq_replicas_leaf_metric` for a labelled equation, `step_11_26_3` for an unnumbered step the digest anchors. The docstring is the anchor id and the digest's **Statement** line, nothing more. Mathlib naming conventions do not apply; this code is not going to Mathlib and the reader has the paper open.
- The proof of an anchor follows its digest steps in order. Each step `D*.n.k` is a `have` (or a `calc` line) carrying the inequality the digest states for it, with a comment `-- D*.n.k`. If a step is a separate anchor, the `have` is an application of that anchor's declaration. If the step needs more than ~15 lines, it is wrong: either the digest step is itself a lemma the paper names (then it has its own anchor, add it to the digest and to the file) or you are proving something the paper does not.
- Definitions use the paper's symbols and the paper's parameters. `ε`, `β`, `α`, `ℓ`, `δ₀`, `ζ`, `ρ₀`, `D₀`, `C_tpl`, `n_*` are named once (`local notation` or a `def`) with the value the digest's "Parameters and constants" table gives, and used by name everywhere. Numerals like `1/100000` appear exactly once, inside those definitions. The constants are introduced in the order `digest/00-overview.md` §2.3 item 11 fixes (`q,R,J,Δ` → `D₀`, `C_tpl` → `C_pad` → `M, p₀, e₀` → `p, c_*, g` → exponents → `C₀` → `C₁` → `n_*` → `S_*, k₀` → `C` of Prop 11.2); a declaration that takes a later constant as a hypothesis of an earlier one is drift. The copy number `k → ∞` is taken strictly after the finite system, the schedule, `n`, `a`, `τ` are fixed (same section): statements quantify in that order.
- Variables carry the paper's letters: `Λ`, `A`, `Ω`, `H`, `Δ`, `T`, `S₀`, `X`, `Y`, `k_i`, `W_{P,k}`. Rename every project-specific name to the paper's (`leafMetric` → `A_k`, and so on). `open` and `open scoped` so that `π`, `‖·‖`, `⊗ₖ`, `∑`, `⨂` read as in the paper; no `Real.pi`, no fully qualified names in proof bodies.
- Typecasts: remove the ones that are there to move between `ℕ`, `ℝ`, `ℕ∞`, `ENNReal` for a quantity the paper keeps in one type. Pick the paper's type (ambient distances are real, `d_Λ` is `ℕ∞`, exponents are real) and stay in it.
- A declaration used once is inlined, unless it is an anchor. A declaration used twice is inlined if both uses are inside one anchor's proof.
- Generality: a lemma stated for arbitrary finite types, arbitrary `k`, arbitrary normed fields or arbitrary graphs when the paper uses it for `ℤ²`, `k = 2` or `ℂ` is restated at the paper's generality, unless the general version is what Mathlib would want, in which case it goes to the library tree of Step 2 and the section file uses it.
- Drift: when the current Lean proof reaches an anchor by a route the paper does not take, rewrite along the digest's steps. Exception: the paper's route depends on a fact that Lean cannot get at reasonable cost (a compactness argument, an analytic identity with no Mathlib support). Then keep the formal route, and record in `RefactoringResult.md` the anchor, the paper's route, the formal route and the reason, as the Cohn–Elkies refactor did for the Phragmén–Lindelöf substitution. This exception is for mathematics, not for convenience.
- Mathlib and Physlib first. Before keeping any `standard` declaration, search. Record each replacement and each failed search (the name you looked for and what you tried) in `RefactoringResult.md`.
- Constants: the paper's explicit constants (`512 e ϑ 𝓑`, `C_h = 1 + 2/e`, `4` in Lemma 2.1, `B_M = 4(C_pad+2)M`, the exponent table of D9.22 and D9.26) are the ones in the code. Where the current Lean proves a different constant, change it to the paper's or record why. The exponents `10⁻⁵`, `2·10⁻⁶`, `10⁻⁶`, `2·10⁻⁷` are interlocked (`digest/00-overview.md` §4, global pitfall): never adjust one to make a proof close; if a proof does not close with the paper's exponent, the proof is wrong, not the exponent.
- Use `mathlib-quality:cleanup` on each finished section file; then `lean4:golf`. Line count is not the goal, readability is, but expect each section file to be at most half the lines of the code it replaces.

Proving what is not there. Every anchor with status `missing` or `smeared` gets a declaration and a proof. There is no sorry in the finished draft. The paper's unnumbered but load-bearing steps are anchors too (the digest has 238 anchors for 35 numbered results); they get declarations when the digest gives them their own proof steps, and `have`s inside the parent otherwise.

Order of work inside a section: definitions and notation; anchors in paper order; the section's exported proposition last, stated as the frozen `def … : Prop` of `OpenAI/Statements.lean` where one exists. Build after every anchor. Commit after every section with the section's line count before and after in the message.

Gate for leaving Step 1: `lake build` clean, no `sorry`, `#print axioms` on each frozen statement gives only `propext`, `Classical.choice`, `Quot.sound`; `Solution/Basic.lean` builds against `AreaLawRefactored` and the comparator accepts it; `OpenAI/` contains only `Statements.lean`.


# Step 2: separation

Split `AreaLawRefactored/` into two trees.

- `AreaLaw/`: the paper. Keep the section files; split a section file only when it passes 1 500 lines, and then along the paper's subsections (`S09_Scanner/MovingPartitions`, `S09_Scanner/CollarInformation`). Nothing in `AreaLaw/` is stated more generally than the paper states it.
- `AreaLawForMathlib/`: the `standard` declarations that Mathlib and Physlib do not have, in Mathlib's generality, naming and style, in the directory Mathlib would put them in (`AreaLawForMathlib/Analysis/Matrix/…`, `AreaLawForMathlib/LinearAlgebra/Matrix/…`, `AreaLawForMathlib/RepresentationTheory/…`, `AreaLawForMathlib/InformationTheory/…`, `AreaLawForMathlib/Combinatorics/SimpleGraph/…`). Each file's docstring says which Mathlib file it extends. Run `mathlib-quality:mathlibable` on each declaration; those it rejects as "mathlib has it" are replaced, those it rejects as "not general enough" are generalised or moved back to `AreaLaw/`.
- `Arealaw/`: the pre-existing region library. Decide per file: what Physlib covers is replaced and deleted; what is specific to lattice regions and used by the statements stays, moved into `AreaLawForMathlib/` or `AreaLaw/S01_Setting` according to its generality. `Arealaw/` is empty at the end, and `OpenAI/Statements.lean` imports only Mathlib, Physlib and `AreaLawForMathlib`. (The frozen file's import lines are the one exception to "never edited"; the declarations in it do not change.)

Delete `docs/oai265/`, `HISTORY.md`, `OpenAI/Audit*.lean` (replace by one `scripts/audit.lean` that prints axioms for the frozen statements), and the root `OpenAI.lean` import list. Rewrite `README.md`: what is proved, the file tree, how to build, the comparator, the blueprint; no provenance narrative.


# Step 3: blueprint

Write the blueprint with [verso-blueprint](https://github.com/leanprover/verso-blueprint); the project template is at `project_template/` of the tag matching `lean-toolchain` (`v4.33.0`). Use the `mathlib-quality:blueprint` skill.

- One chapter per digest file, in paper order, with the digest's "Section in one paragraph" as the chapter introduction.
- One `:::theorem`/`:::lemma`/`:::definition` block per anchor, labelled by the anchor id, with `(lean := AreaLaw.<declaration>)`. The statement is the digest's **Statement**; the proof is the digest's numbered steps; `{uses}` lists the digest's **Used from** anchors. Where Step 1 kept a formal route that differs from the paper (the recorded exceptions), the blueprint proof says so in one sentence and gives the formal route.
- The dependency graph the blueprint renders must agree with the DAG in `digest/00-overview.md`. A discrepancy is a bug in one of them; find which.
- Build the blueprint in CI next to `lake build`.


# `RefactoringResult.md`

Sections, in this order, each a table unless noted:

1. Starting point: the baseline table above, recomputed by you.
2. Decisions: scalar field, encoding, anything else decided once in Step 0. One line each, with the reason.
3. Replacements by Mathlib/Physlib: Lean declaration removed | Mathlib/Physlib declaration | notes on hypotheses.
4. Failed searches: what was needed | names and queries tried | where it ended up (`AreaLawForMathlib/…`).
5. Route differences from the paper: anchor | paper route | formal route | reason. This is the list the blueprint cites.
6. Constants changed: anchor | paper constant | previous Lean constant | now.
7. Digest corrections: anchor | what was wrong | fix. (You will find some. The digest was checked against the LaTeX, not against a formal proof.)
8. Cuts: file or declaration | reason (`dead`, `scaffold`, `foreign`, `inlined into <anchor>`) | lines.
9. Per-section line counts: section | lines before (from `Map.md`) | lines after Step 1 | after Step 2.
10. Final numbers: the baseline table again, final state.

Write it as you go, not at the end.


# What "done" means

- Every one of the 238 anchors has a declaration in `AreaLaw/` or a `have` inside its parent's proof, and `Map.md` says which.
- Every declaration in `AreaLaw/` is in `Map.md`.
- The frozen statements are proved with standard axioms; the comparator accepts `Solution/`.
- `AreaLaw/` + `AreaLawForMathlib/` ≤ 90 000 lines.
- The blueprint builds and its graph matches the digest's DAG.
- A reader with the paper open can find any lemma of the paper by its number, and any step of its proof by the digest step id in the Lean proof.
