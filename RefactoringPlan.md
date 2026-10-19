You are going to refactor the Lean formalization in `OpenAI/` and `Arealaw/` into a one-to-one translation of the paper.

References:

- The paper: `paper/paper.pdf`, LaTeX in `paper/sections/*.tex`.
- The digest: `digest/00-overview.md`, then `digest/01-introduction.md` … `digest/11-geometry.md`, one per paper section. Every result, definition and load-bearing step has an anchor `D<section>.<n>` of kind Theorem, Proposition, Lemma, Corollary, Def or Step, with **Statement**, **Used from**, numbered proof steps `D<section>.<n>.<k>`, **Output**, **Standard?** and, where there is one, **Pitfall**. It was checked line by line against the LaTeX. When digest and Lean disagree about what a proof does, the digest wins; when digest and paper disagree, the paper wins and you fix the digest.
- Do not read `docs/oai265/`, `HISTORY.md`, or Lean docstrings that narrate how the current code was produced. Delete them in Step 2.

Log your work in `RefactoringResult.md` as you go, in the format fixed at the end of this file.

Frozen:

- `OpenAI/Statements.lean`. Every paper result is a `def … : Prop` there: `AreaLaw`, `AreaLawCorollary`, `PositiveReplacement`, `CollarBound`, `Amplification`, `TwoFamilyCancellation`, `TwoFamilyDecomposition`, `ConditionalContinuity`, `MarginalTails`, `BufferDiscount`, `InitialBoxEstimate`. The refactored code proves exactly these. Local notation and abbreviations on top of them are allowed; changing them is not. Its import lines may change in Step 2, nothing else.
- `Challenge/Basic.lean`, `Comparator/`. `Solution/Basic.lean` proves `AreaLaw 𝕜` for every `RCLike 𝕜` by applying `OpenAI.area_law`; it may be re-pointed at the new name, nothing else, and the comparator run recorded in `Comparator/` must still accept it.

Baseline (audit files `OpenAI/Audit*.lean` are `#print axioms` scripts; they are excluded from every count):

| Quantity | Value |
|---|---|
| Paper | 7 069 LaTeX lines; 1 theorem, 1 corollary, 10 propositions, 24 lemmas; 238 digest anchors |
| `OpenAI/` | 916 files, 181 500 lines. `Arealaw/` 35 files, 5 700 lines |
| Declarations in `OpenAI/` | 7 784, of which 1 083 `def`, 6 423 `theorem`/`lemma` |
| Declarations whose name occurs nowhere else | 1 398; exactly once elsewhere: 2 543 |
| Files under 80 lines | 136. Files in `OpenAI/` with no subdirectory: 575, of which 94 named `Replica*` |
| Files outside the import closure of `OpenAI.AreaLaw` | 46 (6 342 lines) |
| Lean lines per paper line | 26 |

Target: ≤ 90 000 lines proving the frozen statements (−50 %), with the paper's structure visible in the file tree, the names and the proof bodies.


# Step 0: the map

Before changing a proof, write `Map.md`: one table per digest file, one row per anchor.

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|

Status:

- `faithful`: one declaration states the anchor; its proof follows steps D*.n.1 … D*.n.k in order.
- `drift`: the conclusion is reached by another route. One line for each route.
- `smeared`: the anchor exists only as the sum of several declarations, none stating it.
- `missing`: nothing states it; downstream code worked around it.
- `overbuilt`: stated with generality, hypotheses or auxiliary theory the paper lacks (a parameter the paper fixes, a class it never varies, "for all `k`" where the paper needs `k = 2`).
- `none`: Step anchors with no proof of their own (remarks, history, the roadmap D1.13–D1.18). No declaration is expected.

Action: `keep`, `golf`, `merge into <anchor>`, `inline into <anchor>`, `restate`, `prove`, `cut`.

Two digest fields feed the map directly. **Standard?** = textbook: the declaration is a Mathlib/Physlib lemma or goes to the library tree of Step 2, never into the paper tree. **Pitfall** on quantifier order or constant dependence: check the Lean statement against it and record the result in the row.

Reverse pass: every declaration in `OpenAI/` and `Arealaw/` in no row is listed under "Unmapped" as one of:

- `standard`: a fact the paper uses in one line. Search Mathlib and Physlib (`lean_leansearch`, `lean_loogle`, grep in `.lake/packages/mathlib` and `.lake/packages/Physlib`). Found → `replace-by <name>`. Not found → library tree, stated once in Mathlib's generality and naming.
- `scaffold`: bridges between two encodings of one object, typecasts, wrappers that rename a hypothesis, restatements with one argument specialised. `cut` once the encodings are unified.
- `dead`: not reachable from the proof of any frozen statement and not a Mathlib candidate. `cut`. The 46 files outside the import closure are the first candidates; confirm each by name search, not by import alone.
- `foreign`: proved for another paper (headers citing a tensor-network or PEPS paper, or "ported from" another repository, with no anchor). `cut` unless the reverse pass finds it on the path to a frozen statement.

The 1 398 never-referenced and 2 543 once-referenced declarations are the first candidates for `inline`, `scaffold` and `dead`. Confirm by search before cutting.

Decide these two before anything else and record them in `RefactoringResult.md` §2:

1. Scalar field. The paper works over $\mathbb C$; the frozen statements and `Solution/` quantify over `[RCLike 𝕜]`. Develop over `ℂ` and prove each frozen `𝕜`-generic statement by one transfer theorem at the top, unless a specific anchor makes that impossible. Delete every piecewise transfer the choice makes unnecessary.
2. Encoding of regions, partial traces, entropy. The statements use `Reg`, `pureState`, `SubState.regionEntropy`, `mutualInfo` from `Arealaw/`. Any second encoding of these inside `OpenAI/`, and any bridge between the two, is scaffolding: keep the statement encoding, re-prove what the other carried, delete the bridge.


# Step 1: the golfed draft

Write `AreaLawRefactored/`, one file per paper section, in the dependency order of `digest/00-overview.md` §2: `S02_Preliminaries`, `S03_InitialBox`, `S04_Quasilocal`, `S05_Conditional`, `S06_Replicas`, `S07_Transport`, `S08_Comparators`, `S09_Scanner`, `S10_Amplification`, `S11_Geometry`, `S01_AreaLaw` (Theorem 1.1 and Corollary 1.2, last). A file imports only the sections its digest lists under **Dependencies**, the library tree, and `OpenAI.Statements`. One file per section rather than one file in all, as in the Cohn–Elkies refactor, because 180 000 lines do not elaborate as one module.

Rules:

- One declaration per anchor of kind Theorem, Proposition, Lemma, Corollary or Def, and per Step anchor that has its own proof steps. Name = paper label: `lemma_6_4`, `prop_9_6`, `eq_replicas_leaf_metric` for a labelled equation, `step_11_26_3` for an anchored step. Docstring = anchor id + the digest's **Statement**, nothing else. Mathlib naming does not apply; this code is not going to Mathlib and the reader has the paper open.
- The proof follows the digest steps in order. Each `D*.n.k` is a `have` or `calc` line carrying the inequality the digest states, commented `-- D*.n.k`. A step that is another anchor is an application of that anchor's declaration. A step needing more than ~15 lines is wrong: either the step is a lemma the paper names (add the anchor to the digest and the declaration to the file) or you are proving something the paper does not.
- Definitions use the paper's symbols and parameters. `ε`, `β`, `α`, `ℓ`, `δ₀`, `ζ`, `ρ₀`, `D₀`, `C_tpl`, `n_*` are named once with the values of the digest's "Parameters and constants" tables and used by name; a numeral like `1/100000` appears once, inside that definition. Constants are introduced in the order of `digest/00-overview.md` §2.3 item 11; a declaration taking a later constant as hypothesis of an earlier one is drift. The copy number `k → ∞` is taken after the finite system, schedule, `n`, `a`, `τ` are fixed; statements quantify in that order.
- Variables carry the paper's letters: `Λ`, `A`, `Ω`, `H`, `Δ`, `T`, `S₀`, `X`, `Y`, `k_i`, `W_{P,k}`. Rename every project name to the paper's. `open` and `open scoped` so that `π`, `‖·‖`, `⊗ₖ`, `∑`, `⨂` read as in the paper; no `Real.pi`, no qualified names in proof bodies.
- One type per quantity, the paper's: ambient distances real, `d_Λ` in `ℕ∞`, exponents real. Remove casts that only move between `ℕ`, `ℝ`, `ℕ∞`, `ENNReal`.
- A declaration used once is inlined unless it is an anchor; used twice inside one anchor's proof, inlined.
- Generality: a lemma stated for arbitrary finite types, `k`, normed fields or graphs where the paper uses `ℤ²`, `k = 2`, `ℂ` is restated at the paper's generality, unless the general form is what Mathlib would want, in which case it goes to the library tree.
- Drift is rewritten along the digest steps. Exception: the paper's route needs a fact Lean cannot get at reasonable cost (a compactness argument, an analytic identity without Mathlib support). Then keep the formal route and record anchor, paper route, formal route, reason in `RefactoringResult.md` §5, as the Cohn–Elkies refactor did for the Phragmén–Lindelöf substitution. This exception is for mathematics, not convenience.
- Mathlib and Physlib first. Search before keeping any `standard` declaration. Record each replacement (§3) and each failed search with the queries tried (§4).
- The paper's explicit constants (`512 e ϑ 𝓑`, `C_h = 1 + 2/e`, `4` in Lemma 2.1, `B_M = 4(C_pad+2)M`, the exponent tables of D9.22, D9.26) are the ones in the code; a different constant is changed or recorded (§6). The exponents `10⁻⁵`, `2·10⁻⁶`, `10⁻⁶`, `2·10⁻⁷` are interlocked (`digest/00-overview.md` §4): never adjust one to close a proof; a proof that does not close with the paper's exponent is wrong, not the exponent.
- `missing` and `smeared` anchors get a declaration and a proof. No `sorry` anywhere.
- Finish each section with `mathlib-quality:cleanup`, then `lean4:golf`. Expect at most half the lines of the code it replaces.

Inside a section: definitions and notation, anchors in paper order, the exported proposition last, stated as its frozen `def … : Prop`. Build after every anchor. Commit after every section, line count before and after in the message.

Gate: `lake build` clean; `#print axioms` on each frozen statement gives `propext`, `Classical.choice`, `Quot.sound` only; `Solution/Basic.lean` builds and the comparator accepts it; `OpenAI/` contains only `Statements.lean`.


# Step 2: separation

- `AreaLaw/`: the paper. Keep the section files; split one only past 1 500 lines, along the paper's subsections (`S09_Scanner/MovingPartitions`, `S09_Scanner/CollarInformation`). Nothing here is more general than the paper states it.
- `AreaLawForMathlib/`: the `standard` declarations Mathlib and Physlib lack, in Mathlib's generality, naming and directory layout (`Analysis/Matrix/…`, `LinearAlgebra/Matrix/…`, `RepresentationTheory/…`, `InformationTheory/…`, `Combinatorics/SimpleGraph/…`). Each file's docstring names the Mathlib file it extends. Run `mathlib-quality:mathlibable` on each declaration; "mathlib has it" → replace, "not general enough" → generalise or move to `AreaLaw/`.
- `Arealaw/`: per file, what Physlib covers is replaced; what is lattice-specific and used by the statements moves to `AreaLawForMathlib/` or `AreaLaw/S01_Setting` by generality. `Arealaw/` ends empty; `OpenAI/Statements.lean` imports only Mathlib, Physlib and `AreaLawForMathlib`.
- Delete `docs/oai265/`, `HISTORY.md`, `OpenAI/Audit*.lean` (replace by one `scripts/audit.lean` printing axioms of the frozen statements), the root `OpenAI.lean`. Rewrite `README.md`: what is proved, the tree, how to build, the comparator, the blueprint. No provenance narrative.


# Step 3: blueprint

[verso-blueprint](https://github.com/leanprover/verso-blueprint), template at `project_template/` of the tag matching `lean-toolchain` (`v4.33.0`); use `mathlib-quality:blueprint`.

- One chapter per digest file, in paper order; the digest's opening paragraph is the chapter introduction.
- One `:::theorem` / `:::lemma` / `:::definition` block per anchor that has a declaration, labelled by anchor id, with `(lean := AreaLaw.<declaration>)`. Statement = digest **Statement**; proof = digest steps; `{uses}` = digest **Used from**. For the recorded route exceptions, one sentence naming the formal route.
- The rendered dependency graph must agree with the DAG of `digest/00-overview.md` §2.1. A discrepancy is a bug in one of them; find which.
- The blueprint builds in CI next to `lake build`.


# `RefactoringResult.md`

Sections in this order, tables unless noted:

1. Starting point: the baseline table, recomputed.
2. Decisions: scalar field, encoding, anything else decided once. One line each with the reason.
3. Replacements: Lean declaration removed | Mathlib/Physlib declaration | hypothesis notes.
4. Failed searches: what was needed | queries tried | where it ended up.
5. Route differences: anchor | paper route | formal route | reason. The blueprint cites this list.
6. Constants changed: anchor | paper | previous Lean | now.
7. Digest corrections: anchor | what was wrong | fix.
8. Cuts: file or declaration | `dead` / `scaffold` / `foreign` / `inlined into <anchor>` | lines.
9. Per-section lines: section | before (from `Map.md`) | after Step 1 | after Step 2.
10. Final numbers: the baseline table, final state.


# Done

- Every anchor with a declaration expected by Step 1 has one in `AreaLaw/`, and `Map.md` names it; every other anchor has status `none` or a `have` inside its parent.
- Every declaration in `AreaLaw/` and `AreaLawForMathlib/` is in `Map.md`.
- The frozen statements are proved with standard axioms; the comparator accepts `Solution/`.
- `AreaLaw/` + `AreaLawForMathlib/` ≤ 90 000 lines.
- The blueprint builds; its graph matches the digest DAG.
- With the paper open, any lemma is found by its number and any proof step by its digest id in the Lean proof.
