# RefactoringResult.md

Log of the refactor fixed by `RefactoringPlan.md`. Sections in the plan's order.

## 1. Starting point

Recomputed at commit `a0b7d58` (branch `refactoring-plan`). Audit scripts `OpenAI/Audit*.lean` (3 files, 6 245 lines) and `Arealaw/Audit.lean` (358 lines, also a `#print axioms` script) are excluded from every count except where the row says otherwise. Line counts are `wc -l`.

| Quantity | Plan | Recomputed | Note |
|---|---|---|---|
| Paper | 7 069 LaTeX lines; 1 theorem, 1 corollary, 10 propositions, 24 lemmas; 238 digest anchors | 7 069 LaTeX lines (6 993 in `paper/sections/*.tex` + 76 in `paper/main.tex`); 1 theorem, 1 corollary, 10 propositions, 24 lemmas (`\begin{…}` counts); 238 anchors (`#### D<s>.<n>` headings in `digest/01`–`11`) | agrees |
| `OpenAI/` | 916 files, 181 500 lines | 916 files, 182 511 lines | line count differs by 1 011 |
| `Arealaw/` | 35 files, 5 700 lines | 35 files, 5 685 lines (5 327 without `Arealaw/Audit.lean`) | |
| Declarations in `OpenAI/` | 7 784, of which 1 083 `def`, 6 423 `theorem`/`lemma` | 7 806, of which 1 083 `def`, 6 592 `theorem`/`lemma` (6 433 + 159); also 50 `abbrev`, 43 `instance`, 32 `structure`, 5 `inductive`, 1 `class` | counted by a line regex on declaration keywords at column 0 (after attributes and modifiers) |
| Declarations whose name occurs nowhere else | 1 398; exactly once elsewhere: 2 543 | 435; exactly once elsewhere: 2 461 | the plan's counting rule is not stated and was not reproduced. Rule used: occurrences of the declaration's last name component as an identifier or dotted component in `OpenAI/`, `Arealaw/`, `Solution/`, `Challenge/` (comments stripped, audit files excluded), minus the declaration itself. Counting only whole-identifier matches of the short or full name gives 1 103 / 2 383 |
| Files under 80 lines | 136 | 135 in `OpenAI/` (+ 14 in `Arealaw/`) | |
| Files in `OpenAI/` with no subdirectory | 575, of which 94 named `Replica*` | 572 (575 with the 3 audit files), of which 94 `Replica*` | agrees |
| Files outside the import closure of `OpenAI.AreaLaw` | 46 (6 342 lines) | `OpenAI/`: 45 non-audit files (6 309 lines) + `AuditAmplification.lean` (33) = 46 (6 342); `Arealaw/`: 20 files (incl. `Audit.lean`) | 2 of the 45 are NOT dead: `OpenAI/PositiveReplacement.lean` (`OpenAI.positive_replacement`, line 16) and `OpenAI/ComplexWitnessTransfer.lean` (`OpenAI.positiveReplacement_of_complex`, line 215) prove the frozen `PositiveReplacement`, which `OpenAI.AreaLaw` does not import |
| Lean lines per paper line | 26 | 26.6 (187 838 / 7 069, audit files excluded) | |

Mapping (Map.md): 238 anchors — faithful 107, drift 41, smeared 63, missing 3, overbuilt 5, none 19. Lines attributed to rows: 170 657; `## Unmapped`: 17 181 lines (1 005 declarations: standard 322, scaffold 93, dead 269, foreign 321). Inside rows, 729 declarations (14 360 lines) are unreachable from the frozen proofs by name search.

## 2. Decisions

| Decision | Choice | Reason |
|---|---|---|
| Scalar field | Develop over `ℂ`. One transfer file at the top proves each `[RCLike 𝕜]` frozen statement (`AreaLaw`, `AreaLawCorollary`, `PositiveReplacement`, `CollarBound`, `Amplification`, `BufferDiscount`, `InitialBoxEstimate`, `TwoFamilyCancellation`, `ConditionalContinuity`, `MarginalTails`) from its `ℂ` instance with two tools: the entrywise star-embedding `𝕜 →⋆ ℂ` (today `OpenAI.toComplex`, `OpenAI/Embedding.lean`), which preserves hermiticity, spectrum and gap, partial traces and entropies, for the hypotheses; and the real part of a `ℂ` witness for the existential operator outputs (`k_X` of `PositiveReplacement`, as `OpenAI/ComplexWitnessTransfer.lean:215` does now), since every constraint on them is convex/linear and invariant under entrywise conjugation when `H`, `Ω` are real. All piecewise transfers go: `OpenAI.bufferDiscount_of_complex` (OpenAI/BufferDiscount.lean:456), the reindex-and-transfer inside `OpenAI.marginal_tails` (OpenAI/MarginalTails.lean:135), `OpenAI.positiveReplacement_of_complex` (OpenAI/ComplexWitnessTransfer.lean:215), the `toComplex` step of `OpenAI.amplification` (OpenAI/Amplification.lean:54), the ℂ→𝕜 step of `collarInformationBound` (OpenAI/CollarInformation.lean:439), `regionEntropy_pureState_toComplex` (OpenAI/BufferDiscount.lean:445), and the use of `OpenAI/Embedding.lean` (505 lines) to carry Physlib's ℂ-only SSA/subadditivity/Araki–Lieb to `𝕜` | The paper works over `ℂ`; the only other `RCLike` field is `ℝ`, which embeds. No anchor needs `𝕜`: the analytic cores of §4–§10 are already ℂ-only (Map.md rows), and the 𝕜-generic pieces (D2.4, D3.15–D3.16, D8.36/D9.28, D10.4, D11.1, D11.26) exist only to feed the frozen statements. No anchor makes the transfer impossible: the one existential-witness statement (`PositiveReplacement`) already has a working real-part transfer. Physlib's entropy inequalities are ℂ-only, so `ℂ` also removes the SSA transfer |
| Encoding of regions, partial traces, entropy | The statement encoding: `Arealaw.Reg`, `pureState`, `SubState.regionEntropy`, `mutualInfo` (Arealaw/), used everywhere. Second encodings re-proved in it, bridges cut (`scaffold`): `FiniteProduct.entropy` / `mutualInformation` / `reducedPure` / `conditionalMutualInformation` over `EuclideanSpace ℂ ((v : V) → β v)` (OpenAI/FiniteProductEntropy.lean:63, :158; FiniteProductChannel.lean:219; FiniteProductConditional.lean:30; `namespace FiniteProduct` opened in 34 files; `FiniteProduct.` or `QuantumSSA.` names occur in 92 files) with bridge `mutualInfo_pureState_eq_finiteProduct` (OpenAI/AmplificationProof.lean:87); `ConditionalMovement.QuantumSSA` (coefficient-matrix partial traces, SSA, conditional entropy; OpenAI/ConditionalMovement/PartialTrace.lean:38, EntropyBounds.lean:38, and a second Lemma 2.1 `QuantumSSA.conditional_continuity`, EntropyContinuity.lean:95); `Entropy.MarginalPhase.condMutualInfo` (OpenAI/MarginalPhaseQuadratic.lean:31); `Entropy.SiteConfig` / `FourPartition` (OpenAI/ConditionalMovementRegional.lean:41) with bridge OpenAI/ReplicaRegionUnion.lean; the §10 ancilla copies `AncillaSites`; the bipartite `PureState`/`rhoA`/`EE` of §2 | Plan, decision 2. The frozen statements are written in Arealaw's encoding, so it is the one that must stay; every other encoding needs a bridge to reach a frozen statement, and Map.md shows the same anchor (Lemma 2.1, SSA, the pure-θ marginals of §5) proved once per encoding |
| Line attribution in Map.md | Each declaration owns its lines up to the next declaration; file headers go to the first declaration; each declaration counted once (individually-named claim over whole-file claim, anchor row over section infra, else earlier section) | Makes the per-section "before" column of §9 sum to the 187 838 lines of `OpenAI/` + `Arealaw/` |
| Dead | Reachability by short-name search from the 20 theorems whose statements mention a frozen `def … : Prop`, through imported files only | Plan: "confirm by name search, not by import alone"; this search found the 2 frozen-statement proofs outside the `OpenAI.AreaLaw` closure |
| Unmapped helpers | 99 proof helpers no mapper claimed (and the 9 helper defs of `OpenAI/Statements.lean`) go into a `(section infra, reverse pass)` row of their section, not into `## Unmapped` | They serve an anchor's proof and fit none of standard/scaffold/dead/foreign |

## 3. Replacements

| Lean declaration removed | Mathlib/Physlib declaration | Hypothesis notes |
|---|---|---|
| `Arealaw.vonNeumann_strong_subadditivity`, `…_complex` (OpenAI/ConditionalEntropy.lean:284-405, §2) | Physlib `Sᵥₙ_strong_subadditivity` (through `Arealaw.MState.regionEntropy_strong_subadditivity`, AreaLawForMathlib/QuantumInfo/Region.lean:177) | ℂ only; normalized states (decision 1) |
| D2.2 item 4 lower bound (purification) | Araki–Lieb `Arealaw.abs_regionEntropy_sub_regionEntropy_le` (Arealaw/Subadditivity.lean, from Physlib `Sᵥₙ_triangle_subaddivity`) | normalized, ℂ |
| D2.3 binary entropy | Mathlib `Real.binEntropy` | already used by the frozen statement |
| D2.4 Jordan parts (`exists_posSemidef_sub_eq`, OpenAI/ConditionalContinuity.lean:134) | Physlib `HermitianMat.posPart`/`negPart`, `posPart_add_negPart` (in `MState.exists_sub_eq_sub`, AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean:248) | |
| D2.4 mixing entropy of the coin | Physlib `ProbDistribution.coin`, `Hₛ_coin`, `Sᵥₙ_ofClassical` | |
| D2.5 pure-state complement (`regionEntropy_pureState_sdiff`, OpenAI/RegionEntropy.lean:263 via `coeffMatrix`/`EE`) | Physlib `Sᵥₙ_pure_complement` (AreaLawForMathlib/QuantumInfo/Region.lean:226) | |
| D2.9 path crossing the cut | Mathlib `SimpleGraph.Walk.exists_boundary_dart`, `exists_walk_of_edist_ne_top`, `Walk.edist_le` | |
| `OpenAI.harmonic_cost_le` (OpenAI/HarmonicWeights.lean:93, D3.6.1 minimality) | Mathlib `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan form of Cauchy–Schwarz), in `AreaLaw.eq_initial_harmonic_weights` (AreaLawRefactored/S03_InitialBox.lean:124) | weights `1/(r+d_j) > 0` |
| `OpenAI.log_add_sub_log_le_div` (OpenAI/HarmonicWeights.lean:113, D3.6.2) | Mathlib `Real.log_le_sub_one_of_pos` | ratio of consecutive terms |
| `OpenAI.card_filter_not_interior_le` / colour machinery (OpenAI/ChildColoring.lean) | none needed: paper route of D3.16 (random order) counts orders with `Fintype.card_perm`, `Finset.card_nbij'`, `Finset.exists_max_image` (`AreaLaw.step_3_16_3_count`) | |

## 4. Failed searches

| What was needed | Queries tried | Where it ended up |
|---|---|---|
| concavity of `Sᵥₙ`; mixing bound `S(Σpτ) ≤ Σ pS(τ) + H(p)`; entropy of a classical–quantum (block-diagonal) state | grep Physlib `concav`, `Sᵥₙ.*mix`, `Holevo`, `cq`, `blockDiag`, `cfc_kron`; loogle `cfc, Matrix.blockDiagonal` (0 hits) | AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean (`MState.cq`, `Sᵥₙ_cq`, `Sᵥₙ_cq_traceRight_le`, `sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight`) |
| charpoly / eigenvalues / PSD of `Matrix.blockDiagonal` | loogle `Matrix.charpoly (Matrix.blockDiagonal _)` (0 hits), `Matrix.PosSemidef (Matrix.blockDiagonal _)` (HTTP 503), grep Mathlib | ClassicalQuantum.lean:23-49 |
| trace of the positive part, `Tr A⁺ = (‖A‖₁ + Tr A)/2` | grep Physlib `trace_posPart` (Arealaw/TraceDist.lean has a private one) | ClassicalQuantum.lean:232 |
| trace distance contracts under partial trace | grep Physlib `TrDistance`, `traceNorm` with `traceLeft`/`traceRight`; Arealaw `D₁.*restrict` | `Arealaw.SubState.D₁_restrict_le`, AreaLawForMathlib/QuantumInfo/Region.lean:260 |
| trace distance of two pure states | grep Physlib TraceDistance.lean `pure`, Arealaw `vecMulVec`/`traceNorm` | `Matrix.traceNorm_vecMulVec_sub_vecMulVec_div_two`, Region.lean:39 |
| eigenvalues of a Hermitian idempotent are 0/1; a projection has zero entropy | loogle `IsIdempotentElem, Matrix.IsHermitian.eigenvalues` (0 hits); atlas "The eigenvalues of a Hermitian idempotent matrix are zero or one." | `Arealaw.SubState.entropy_eq_zero_of_isIdempotentElem`, Region.lean:295 |
| `#{z ∈ ℤ² : \|z\|₁ ≤ r} ≤ 1 + 2r(r+1)` | grep Mathlib | `Finset.card_le_of_forall_natAbs_add_natAbs_le`, AreaLawForMathlib/Data/Int/L1Ball.lean:15 |

## 5. Route differences

| Anchor | Paper route | Formal route | Reason |
|---|---|---|---|
| D2.12 (Lemma 2.2), steps D2.12.3–6 | H = tensor sum over all components, ground space ⊗_c ker(H_c − E₀^c), Ω = ⊗_c Ω_c | two blocks A, Λ∖A only: on the coefficient matrix N(x,z) = v(glue x z), H acts as N ↦ PN + NG; uniqueness (from the gap, its size unused) gives PM = aM, MG = (E₀−a)M, so a column of M times a row of M is again a ground vector, M has rank one, ρ_A = MMᴴ is a rank-one projection, S = 0 (`AreaLaw.exists_hamiltonian_coeff`, `regionEntropy_eq_zero_of_split`, S02_Preliminaries.lean:626, :659) | tensor sums over an arbitrary family of components are costly in Lean; the two-block version is the same mathematics |
| D2.11.2 (R = 0) | Ω = ⊗_x ω_x through on-site ground spaces | the core lemma `regionEntropy_eq_zero_of_split`: for R = 0 every support is a singleton, which lies in A or Λ∖A | one argument serves D2.11.2 and D2.12 |
| D2.7.2 | sphere \|z\|₁ = k has 4k points; equality | ℓ¹-ball covered by two rotated squares of (r+1)² and r² points (parity of a+b+r); proves ≤ only | the anchor needs ≤; far shorter |
| D2.2 item 4, lower bound | purify, S(D\|E) = −S(D\|F) ≥ −S(D) | Araki–Lieb S(E) − S(D) ≤ S(DE) | Araki–Lieb already on regions; no purification |
| D2.5.1 | eigenvalues ±λ of the rank-two difference | X³ = (1−\|⟨ξ,η⟩\|²)X, so \|X\| = c^{−1/2}X² | avoids a spectral computation |
| D3.6.2 | integral comparison `1/(2r+jD) ≥ ∫_j^{j+1} dx/(2r+Dx)` | `log((2r+(j+1)D)/(2r+jD)) ≤ D/(2r+jD)` from `log x ≤ x − 1`, telescoped (`eq_initial_harmonic_weights`) | same inequality, no integrals |
| D3.15 | sup over instances at a fixed `D₀ > 2R+10` | sup also over `D₀ > 2R+10` (`AreaLaw.F_box`, S03_InitialBox.lean:682) | the frozen `InitialBoxEstimate` puts `∃ C e₀` before `∀ D₀`, and `D₀` is real |
| D3.16 (old code, now fixed) | uniform random order of the children | (Step 1) the paper route, `AreaLaw.step_3_16_4` (S03_InitialBox.lean:868); the old deterministic colour rotations (OpenAI/RotatedChainRule.lean, ChildColoring.lean) are not used | old route was drift |

## 6. Constants changed

| Anchor | Paper | Previous Lean | Now |
|---|---|---|---|
| D2.4 (Lemma 2.1), second inequality | C = 2(1 + 2/e) (D2.4.4) | 4 (frozen `ConditionalContinuity`, old `winterModulus_le_sqrt`) | 2·C_h proved in `AreaLaw.step_2_4_4` (S02_Preliminaries.lean:97); weakened once to the frozen 4 at the end of `lemma_2_1` (the frozen statement may not change) |
| D3.16 (Prop 3.3) | p₀ = (2C_pad+5)⁻², B_M = 4(C_pad+2)M, M ≥ max{2, 16(C_pad+2)}, λ = (1−p₀/4)M² | old `initial_box_estimate_of_bufferDiscount` (OpenAI/InitialBoxEstimate.lean:294): p = 1/(2(2C_pad+1)²), M = 8(C_pad+1), λ = (1−p/2)M², noninterior ≤ 2(2C_pad+1)M | paper's: `AreaLaw.p₀` = (2C_pad+5)⁻², `B_M` = 4(C_pad+2)M, M = 16(C_pad+2), λ = (1−p₀/4)M² (`prop_3_3`, S03_InitialBox.lean:1109) |
| D3.5(e) | `C(r+d_j)`, `C = C(q,R)` | — | `16 v_R μ_R (r+d_j)` for the count, `C₂ = 1 + 16 v_R μ_R (1+v_R log q)²` for `𝓑_j` (`step_3_5_5`) |
| D3.2.3 | `C₁ = max{1, 2v_Rμ_R(1+v_R log q)²}` | `cutLogBudget_le_card_diamond` (OpenAI/TailParameter.lean) | paper's `AreaLaw.C₁` (S03_InitialBox.lean:16) |

## 7. Digest corrections

| Anchor | What was wrong | Fix |
|---|---|---|
| §2 | none found by the §2 part agents | — |
| §3 | none found by the §3 worker | — |

## 8. Cuts

| File or declaration | Category | Lines |
|---|---|---|
| §2 old code (Map.md §2 rows) | not yet deleted: later sections still import it; cut at the Step 1 gate | — |
| §3 old code (Map.md §3 rows) | not yet deleted (instruction: keep OpenAI/ until the Step 1 gate) | — |

## 9. Per-section lines

| Section | Before (from Map.md) | After Step 1 | After Step 2 |
|---|---|---|---|
| 02 Preliminaries | 4865 | 786 (`AreaLawRefactored/S02_Preliminaries.lean`) + 607 library (`AreaLawForMathlib/QuantumInfo/Region.lean` 314, `…/Entropy/ClassicalQuantum.lean` 259, `Data/Int/L1Ball.lean` 34) = 1393 | |
| 03 InitialBox | 10096 | 1162 (`AreaLawRefactored/S03_InitialBox.lean`), PARTIAL: D3.1 (Lemma 3.1), D3.2.4, D3.4 (Lemma 3.2), D3.7–D3.13, D3.14.5 open; `prop_3_3` takes Lemma 3.2 as hypothesis | |

## 10. Final numbers

| Quantity | Value |
|---|---|
