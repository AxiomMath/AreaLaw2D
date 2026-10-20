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
| `OpenAI.harmonic_cost_le` (OpenAI/HarmonicWeights.lean:93, D3.6.1 minimality) | Mathlib `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan form of Cauchy–Schwarz), in `AreaLaw.eq_initial_harmonic_weights` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:80) | weights `1/(r+d_j) > 0` |
| `OpenAI.log_add_sub_log_le_div` (OpenAI/HarmonicWeights.lean:113, D3.6.2) | Mathlib `Real.log_le_sub_one_of_pos` | ratio of consecutive terms |
| `OpenAI.card_filter_not_interior_le` / colour machinery (OpenAI/ChildColoring.lean) | none needed: paper route of D3.16 (random order) counts orders with `Fintype.card_perm`, `Finset.card_nbij'`, `Finset.exists_max_image` (`AreaLaw.step_3_16_3_count`) | |
| `OpenAI.abs_re_sub_le_of_norm_le_closedBall` (OpenAI/StripQuadratic.lean, D3.1.8 Cauchy coefficient estimate via dslope + maximum modulus) | Mathlib `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO` (higher-order Schwarz lemma, n = 1), in `AreaLaw.step_3_1_8` (AreaLawRefactored/S03_InitialBox/MarginalTails.lean:162) | applied to k(z) = f(z) + f(−z) − 2f(0) |
| three-lines in D3.1.7 | Mathlib `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (`step_3_1_7`, AreaLawRefactored/S03_InitialBox/MarginalTails.lean:127) | already the old route |
| weighted AM–GM of D3.1.6 | Mathlib `Real.geom_mean_le_arith_mean2_weighted` | |
| `OpenAI.norm_toEuclideanLin_le` | Mathlib `Matrix.l2_opNorm_mulVec` | |
| `OpenAI.neg_log_one_sub_le` (D3.1.11) | Mathlib `Real.one_sub_inv_le_log_of_pos` | |
| Bessel for Schmidt vectors (D3.1.6) | Mathlib `Orthonormal.sum_inner_products_le` | |
| gap transport under reindexing/conjugation (D3.1.1) | Mathlib `Matrix.posSemidef_submatrix_equiv`, `PosSemidef.mul_mul_conjTranspose_same` (`hasGlobalGap_submatrix`, `hasGlobalGap_conj`, AreaLawRefactored/S03_InitialBox/MarginalTails.lean:796, :803) | |
| `OpenAI.commute_of_isHermitian_inv_mul_mul` (OpenAI/FilterStationarity.lean:111, ρL² = L²ρ ⇒ ρL = Lρ by an entrywise computation in the eigenbasis of L) | Mathlib `Commute.cfc_nnreal` with `CFC.sqrt_eq_cfc`, `CFC.sqrt_mul_self` (L = (L²)^{1/2}), in `AreaLaw.step_3_7_4` (AreaLawRefactored/S03_InitialBox/Filters.lean:89) | L ≥ 0 via `PosDef.posSemidef.nonneg` |
| concavity of entropy (D3.13.2, `Arealaw.sum_vonNeumann_sub_negMulLog_le`, OpenAI/RegionSSA.lean:198) | `MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight` (AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean, already in the library tree) | to be used when D3.13 is written |

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
| Cauchy coefficient bound `|a_n| ≤ M R⁻ⁿ` for a holomorphic function bounded on a disk (D3.1.8) | atlas_search "If a holomorphic function on a disk of radius R is bounded by M, then its n-th Taylor coefficient at the center is bounded by M divided by R to the n." (only `cauchyPowerSeries` norm bounds); "If an entire function vanishes to second order at zero and is bounded by M on the closed disk of radius r, then its norm at z is at most M times norm z squared over r squared." (found the Schwarz lemma) | Schwarz-lemma route, §5 |
| ℓ² norm of a matrix column/row ≤ its L2 operator norm; contraction conjugation does not increase the norm (D3.1.6) | atlas_search "The Euclidean norm of a row of a matrix is at most its L2 operator norm."; grep Mathlib `Analysis/CStarAlgebra/Matrix.lean`, `Analysis/Matrix/*` | AreaLawForMathlib/Analysis/CStarAlgebra/Matrix.lean (`Matrix.sum_norm_apply_sq_le_l2_opNorm_sq` :16, `Matrix.l2_opNorm_mul_mul_le_of_le_one` :25) |
| Schatten–Hölder `Tr(ρ L²) ≤ (Tr ρ^{1/(1−a)})^{1−a} (Tr L^{2/a})^{a}` for PSD matrices (D3.11.3); simultaneous diagonalization of commuting Hermitian matrices (D3.8, D3.9.3) | grep QuantumInfo/Physlib/Mathlib `holder`, `Holder`, `trace_mul_le`, `trace_rpow`; Physlib has `Commute.exists_unitary` (used) but no trace Hölder | AreaLawForMathlib/Analysis/Matrix/TraceHolder.lean (`Matrix.PosSemidef.re_trace_mul_le` :128, `Matrix.exists_unitary_diagonal_of_commute` :150; moved from OpenAI/TraceHolder.lean), used in `AreaLaw.step_3_11_3` (AreaLawRefactored/S03_InitialBox/Filters.lean:167) |
| compactness of the unitary matrices (D3.7.1) | loogle `IsCompact, Matrix.unitaryGroup` (0 hits), `IsCompact (unitary _)` (no matrix hit) | `Matrix.isCompact_setOf_conjTranspose_mul_self_eq_one`, AreaLawForMathlib/Analysis/CStarAlgebra/Matrix.lean:34 (from Mathlib `entry_norm_bound_of_unitary`) |
| `extendId` multiplicative; `⟨φ, (A ⊗ 1) φ⟩ = Tr(ρ_{φ,S} A)` (D3.7.3, D3.11.3) | grep Arealaw/PTrace.lean (`trace_ptrace_mul` only; `extendId_mul` exists only in OpenAI/Bridges.lean:407) | AreaLawForMathlib/QuantumInfo/Region.lean (`Arealaw.extendId_mul` :321, `Arealaw.dotProduct_extendId_mulVec` :327) |
| `Re Tr(ρB) = 0` for Hermitian `ρ`, anti-Hermitian `B` (D3.7.4); `extendId` transitivity for `S ⊆ T ⊆ V` (D3.7.3) | atlas semantic "trace of the product of a Hermitian matrix and a skew-Hermitian matrix has zero real part" (no Mathlib hit; nearest `Matrix.IsHermitian.im_star_dotProduct_mulVec_self`); grep Arealaw/ for `extendId` (no transitivity lemma) | `AreaLaw.re_trace_mul_eq_zero`, `AreaLaw.extendId_extendId` (AreaLawRefactored/S03_InitialBox/Filters.lean:294, :422) |

## 5. Route differences

| Anchor | Paper route | Formal route | Reason |
|---|---|---|---|
| D2.12 (Lemma 2.2), steps D2.12.3–6 | H = tensor sum over all components, ground space ⊗_c ker(H_c − E₀^c), Ω = ⊗_c Ω_c | two blocks A, Λ∖A only: on the coefficient matrix N(x,z) = v(glue x z), H acts as N ↦ PN + NG; uniqueness (from the gap, its size unused) gives PM = aM, MG = (E₀−a)M, so a column of M times a row of M is again a ground vector, M has rank one, ρ_A = MMᴴ is a rank-one projection, S = 0 (`AreaLaw.exists_hamiltonian_coeff`, `regionEntropy_eq_zero_of_split`, S02_Preliminaries.lean:626, :659) | tensor sums over an arbitrary family of components are costly in Lean; the two-block version is the same mathematics |
| D2.11.2 (R = 0) | Ω = ⊗_x ω_x through on-site ground spaces | the core lemma `regionEntropy_eq_zero_of_split`: for R = 0 every support is a singleton, which lies in A or Λ∖A | one argument serves D2.11.2 and D2.12 |
| D2.7.2 | sphere \|z\|₁ = k has 4k points; equality | ℓ¹-ball covered by two rotated squares of (r+1)² and r² points (parity of a+b+r); proves ≤ only | the anchor needs ≤; far shorter |
| D2.2 item 4, lower bound | purify, S(D\|E) = −S(D\|F) ≥ −S(D) | Araki–Lieb S(E) − S(D) ≤ S(DE) | Araki–Lieb already on regions; no purification |
| D2.5.1 | eigenvalues ±λ of the rank-two difference | X³ = (1−\|⟨ξ,η⟩\|²)X, so \|X\| = c^{−1/2}X² | avoids a spectral computation |
| D3.6.2 | integral comparison `1/(2r+jD) ≥ ∫_j^{j+1} dx/(2r+Dx)` | `log((2r+(j+1)D)/(2r+jD)) ≤ D/(2r+jD)` from `log x ≤ x − 1`, telescoped (`eq_initial_harmonic_weights`) | same inequality, no integrals |
| D3.15 | sup over instances at a fixed `D₀ > 2R+10` | sup also over `D₀ > 2R+10` (`AreaLaw.F_box`, S03_InitialBox.lean:165) | the frozen `InitialBoxEstimate` puts `∃ C e₀` before `∀ D₀`, and `D₀` is real |
| D3.16 (old code, now fixed) | uniform random order of the children | (Step 1) the paper route, `AreaLaw.step_3_16_4` (S03_InitialBox.lean:351); the old deterministic colour rotations (OpenAI/RotatedChainRule.lean, ChildColoring.lean) are not used | old route was drift |
| D3.1.8 | power series of f_i, Cauchy estimate `|a_n| ≤ e c₀ δ_i⁻ⁿ`, sum over even n ≥ 2: `≤ (4/3) e c₀ x² δ_i⁻² ≤ 2 e c₀ x² δ_i⁻²` | Mathlib's higher-order Schwarz lemma on k(z) = f_i(z) + f_i(−z) − 2f_i(0), which vanishes to second order at 0 and is bounded by 4ec₀ on the disk of radius δ_i: `|Re(f_i(x) − f_i(0))| = |Re k(x)|/2 ≤ 2 e c₀ x² δ_i⁻²` (`AreaLaw.step_3_1_8`, AreaLawRefactored/S03_InitialBox/MarginalTails.lean:162) | no Mathlib Taylor-coefficient bound; same constant 128 e c₀ ℓ_i² x² |
| D3.1.3 | commutation of F with h_i (D_i ⊆ B^c), cyclicity and [F, σ] = 0 (D_i ⊆ B) | f_i is constant for terms A ⊗ 1 and 1 ⊗ A (`modF_kronecker_one`, `modF_one_kronecker`, AreaLawRefactored/S03_InitialBox/MarginalTails.lean:352, :360), so every term enters through the D3.1.4 identity and the one-sided ones contribute 0 | same content in the Schmidt coordinates already used for D3.1.4 |
| D3.1.1 | basis-free Schmidt form at B ∣ B^c | explicit unitary (V* ⊗ 1) ∘ glue⁻¹, V the eigenvector unitary of ρ (`step_3_1_1`, `isSchmidt_cut`, AreaLawRefactored/S03_InitialBox/MarginalTails.lean:900, :865) | encoding only |

## 6. Constants changed

| Anchor | Paper | Previous Lean | Now |
|---|---|---|---|
| D2.4 (Lemma 2.1), second inequality | C = 2(1 + 2/e) (D2.4.4) | 4 (frozen `ConditionalContinuity`, old `winterModulus_le_sqrt`) | 2·C_h proved in `AreaLaw.step_2_4_4` (S02_Preliminaries.lean:97); weakened once to the frozen 4 at the end of `lemma_2_1` (the frozen statement may not change) |
| D3.16 (Prop 3.3) | p₀ = (2C_pad+5)⁻², B_M = 4(C_pad+2)M, M ≥ max{2, 16(C_pad+2)}, λ = (1−p₀/4)M² | old `initial_box_estimate_of_bufferDiscount` (OpenAI/InitialBoxEstimate.lean:294): p = 1/(2(2C_pad+1)²), M = 8(C_pad+1), λ = (1−p/2)M², noninterior ≤ 2(2C_pad+1)M | paper's: `AreaLaw.p₀` = (2C_pad+5)⁻², `B_M` = 4(C_pad+2)M, M = 16(C_pad+2), λ = (1−p₀/4)M² (`prop_3_3`, S03_InitialBox.lean:592) |
| D3.5(e) | `C(r+d_j)`, `C = C(q,R)` | — | `16 v_R μ_R (r+d_j)` for the count, `C₂ = 1 + 16 v_R μ_R (1+v_R log q)²` for `𝓑_j` (`step_3_5_5`) |
| D3.2.3 | `C₁ = max{1, 2v_Rμ_R(1+v_R log q)²}` | `cutLogBudget_le_card_diamond` (OpenAI/TailParameter.lean) | paper's `AreaLaw.C₁` (S03_InitialBox/MarginalTails.lean:1090) |
| D3.2.4 | C_M = C_M(q,R,J,Δ,M) (digest expansion 32(M+2)√((1+ϑ)C₁)) | `concentrationWidth` (OpenAI/TailParameter.lean) | digest's `AreaLaw.C_M` (AreaLawRefactored/S03_InitialBox/MarginalTails.lean:1133) |
| D3.9.4 | `C a_j²(p_i+p_k)`, sup z²cosh(z/2)/cosh z ≤ 32/e² < 4.4 | old sharper a²/2 by another route | explicit `8/e²` on the paper's route (`step_3_9_4`, AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:528) |
| D3.10 | C_pad "large enough" | packaged through Z_min (old `bufferDiscount_complex`) | C_pad = ⌈(2+D)e^{L₀}⌉ + D + 2, L₀ = max{4, 16CD/Δ, 128D√((1+J/Δ)C₂)} (`eq_initial_weight_range`, AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:600) |
| D3.14.5 | C_buf unspecified | (1024e(J/Δ)K' + C_pad)/2 | C(C_pad/D+1)·2D/log((C_pad+1)/(2+D)) (`step_3_14_5`, AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:769) |

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
| 03 InitialBox | 10096 | 3209 (`AreaLawRefactored/S03_InitialBox/MarginalTails.lean` 1184, `AreaLawRefactored/S03_InitialBox/BufferDiscount.lean` 790, `AreaLawRefactored/S03_InitialBox/Filters.lean` 589, `AreaLawRefactored/S03_InitialBox.lean` 645) + 243 library (`AreaLawForMathlib/Analysis/CStarAlgebra/Matrix.lean` 43, `AreaLawForMathlib/Analysis/Matrix/TraceHolder.lean` 178, `AreaLawForMathlib/QuantumInfo/Region.lean` +22) = 3452, PARTIAL: Lemma 3.1 (`lemma_3_1`) and D3.2 done; Lemma 3.2 (`lemma_3_2`) open: written D3.7.1–4 (no chain assembly), D3.9.1, D3.9.3, D3.9.5, D3.11.2–4, D3.12.4, D3.13 (scalar averaging); not written: chain assembly of D3.7, D3.8.1, D3.9.2, D3.9.6, D3.11.1, D3.12.1–3/5–6, D3.13.2 on regions, `lemma_3_2` itself; `prop_3_3` still takes Lemma 3.2 as hypothesis | |

## 10. Final numbers

| Quantity | Value |
|---|---|

## Next steps for whoever continues

State at the last commit of branch `agents/18b3b627-b93d-5732-9c67-7919d1fb0eea`: §2 done; §3 done except Lemma 3.2. Since then (commits 310256a, 09bf520, daf601e): D3.9.3 `step_3_9_3` and D3.9.5 `step_3_9_5` (Filters.lean:342, :365), D3.7.1 `step_3_7_1` with `IsFilter`/`filterProd` (Filters.lean:29–141), `IsFilter.exp_conj` (:85); then the D3.7.2 maximality step `step_3_7_2_filter` (Filters.lean:312) with the `prodDesc` split `prodDesc_add` (:285). `AreaLaw.prop_3_3` (AreaLawRefactored/S03_InitialBox.lean:592) proves `InitialBoxEstimate ℂ q R J Δ` from the hypothesis `lemma_3_2 : BufferDiscount ℂ q R J Δ`. Everything compiles on the hosted Axile `workspace-2` (`check_module AreaLawRefactored.S03_InitialBox`: passed); `#print axioms` of every new declaration: `[propext, Classical.choice, Quot.sound]`.

What remains in §3, in paper order (old faithful proofs to translate are cited in Map.md rows D3.7–D3.13; `AreaLawRefactored/S03_InitialBox/Filters.lean` is where they go):

1. D3.7 chain: done. `step_3_7` (AreaLawRefactored/S03_InitialBox/Filters.lean:494): for nested regions `hnest : ∀ j, X j ⊆ X (j+1)` (a hypothesis of `step_3_7`; `step_3_7_1` is unchanged), floors `f j > 0`, feasible `L` maximal at `n` (exactly the second conjunct of `step_3_7_1` with `k = n`), every `j < n` has `L j * ρ = ρ * L j` with `ρ = ptrace (hX j) (vecMulVec φ (star φ))`, `φ = filterProd hX L n *ᵥ ofLp Ω`. Proof: strong induction on `k = n − 1 − j`; `step_3_7_2_pairing`, then the peel through `K_{>j}` `step_3_7_3_prodDesc` (Filters.lean:451: `⟨φ, K (W⊗1) K⁻¹ φ⟩ = ⟨φ, (W⊗1) φ⟩` when `L_{j+1..j+m}` commute with their marginals; the conjugate is again an extension from `X_{j+1+m}` via `extendId_extendId`), `dotProduct_extendId_mulVec`, `re_trace_mul_eq_zero`, cyclicity, `step_3_7_4` with `IsFilter.posDef`. `#print axioms` of both: `[propext, Classical.choice, Quot.sound]`; `check_module AreaLawRefactored.S03_InitialBox` on hosted Axile `workspace-2`: passed. D3.8.1 can use `step_3_7` for the commutation.
2. D3.8.1: the diagonal variation (old OpenAI/FilterClipping.lean:164) giving the hypotheses of `step_3_8_2`/`step_3_8_3` (BufferDiscount.lean:454, :481) in the common eigenbasis `Matrix.exists_unitary_diagonal_of_commute`.
3. D3.9.2, D3.9.6: split-index reduction on regions (old OpenAI/FilterChainEnergy.lean) and the sum over supports; `step_3_9_1`, `step_3_9_3`, `step_3_9_4`, `step_3_9_5` (product-type coordinates `α × β` = Schmidt coordinates at `X_j | X_j^c`; transport to regions as in `isSchmidt_cut`, MarginalTails.lean) and `gap_le` (MarginalTails.lean:625) are ready.
4. D3.11.1: prefix problems `N_j` (old OpenAI/FilterPrefix.lean:144–305); then `step_3_11_2`, `step_3_11_4_region` (Lemma 3.1 via `lemma_3_1` gives its `hM` at `u = −a/(1−a)`, admissible by `eq_initial_weight_range` (iii)) and `step_3_11_5` assemble D3.11.
5. D3.12.1–3, D3.12.5–6: zero-floor limit (old OpenAI/FilterZeroFloor.lean), Schmidt pinning (OpenAI/SchmidtPinning.lean:204), vector three-lines and its derivative (OpenAI/FilterPower.lean:415; Mathlib `Complex.HadamardThreeLines`), trial filters (OpenAI/BufferDiscountCore.lean:79); `step_3_12_4` is ready.
6. D3.13.2 on regions: `∑ p_i S_{w_i}(T_j) ≤ S(T_j)` for the Schmidt decomposition at `X | X^c` (`isSchmidt_cut`, MarginalTails.lean:865; concavity `MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight`); then `step_3_13` gives D3.13.
7. `lemma_3_2 (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) : BufferDiscount ℂ q R J Δ` from D3.5, D3.6, D3.10, D3.11, D3.13 and `step_3_14`, `step_3_14_5` (BufferDiscount.lean:744, :769). The frozen statement does not carry these hypotheses; the old `OpenAI.buffer_discount` (OpenAI/BufferDiscount.lean:508) and `initial_box_estimate` (OpenAI/InitialBoxEstimate.lean:356) take the same three, so `prop_3_3` becomes `(hq) (hJ) (hΔ) : InitialBoxEstimate ℂ q R J Δ`, and the transfer to `𝕜` (decision 1) passes them on.

§4 onward (S04_Quasilocal … S01_AreaLaw), Step 2, Step 3 and the final gate are untouched.
