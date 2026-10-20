# Map.md — Step 0 of RefactoringPlan.md

One table per digest file, one row per anchor (238 anchors), then the reverse pass (`## Unmapped`).

## How the columns were filled

- **Lean declaration(s) now**: the declaration stating the anchor first, then the helpers/files that exist only to prove it. Full names with `file:line`.
- **Lines now**: computed by script (`.axiomcode/scratch/step0/` was the working directory; scripts not kept in the repo). Each declaration owns the lines from its first line to the line before the next declaration in its file; the lines above a file's first declaration (imports, module doc) go to that first declaration. Every declaration of `OpenAI/` and `Arealaw/` (audit files `*/Audit*.lean` excluded) is attributed to exactly one row or to `## Unmapped`; a declaration claimed by two rows is counted in the row that names it individually (over a whole-file claim), anchor rows over `(section infra)` rows, and otherwise in the earlier section. So the columns, the section totals and `## Unmapped` sum to the 187 838 lines of `OpenAI/` + `Arealaw/`.
- `(section infra)`: code serving the section but no single anchor. `(section infra, reverse pass)`: proof helpers that no mapper claimed and the reverse pass assigned to the section (all `inline into` their consumer).
- **Status**, **Action** per the plan. **Standard?** rows say `library tree` or `replace-by <name>`; "search pending" means no Mathlib/Physlib search was run for that row in Step 0. **Pitfall** checks are written into the Action cell as `Pitfall: OK/VIOLATED — … file:line` or `Pitfall: n/a`.
- 𝕜 vs ℂ: rows note whether the declaration is `RCLike 𝕜`-generic or ℂ-only (decision 1 in RefactoringResult.md §2).
- Reachability (used for `dead`): a declaration is reachable if its short name occurs in the body of a reachable declaration of an imported file, starting from the 20 theorems whose statements mention a frozen `def … : Prop` of `OpenAI/Statements.lean`. Over-approximate (short-name collisions), so `dead` is safe; some reachable ones are dead too.

## Summary

| Section | Anchors | faithful | drift | smeared | missing | overbuilt | none | Lines now |
|---|---|---|---|---|---|---|---|---|
| 01 Introduction | 18 | 6 | 1 | 0 | 0 | 0 | 11 | 1915 |
| 02 Entropy and induced-graph locality | 13 | 3 | 4 | 3 | 1 | 1 | 1 | 4865 |
| 03 Marginal tails, initial box estimate | 17 | 12 | 1 | 3 | 0 | 0 | 1 | 10096 |
| 04 Positive constraints and truncation | 15 | 3 | 5 | 5 | 0 | 1 | 1 | 8021 |
| 05 Two conditional operator estimates | 21 | 3 | 9 | 8 | 0 | 0 | 1 | 15729 |
| 06 Symmetric replicas and entropy metrics | 17 | 6 | 1 | 7 | 1 | 1 | 1 | 25889 |
| 07 Transport through finite trees of metrics | 27 | 13 | 5 | 7 | 0 | 1 | 1 | 13047 |
| 08 Norm comparisons from an auxiliary pair | 37 | 20 | 6 | 10 | 0 | 0 | 1 | 29293 |
| 09 Scanning collars | 30 | 18 | 4 | 7 | 0 | 1 | 0 | 32191 |
| 10 Amplifying the collar estimate | 17 | 9 | 3 | 3 | 1 | 0 | 1 | 13740 |
| 11 Two families of regions, area bound | 26 | 14 | 2 | 10 | 0 | 0 | 0 | 15871 |
| **total** | 238 | 107 | 41 | 63 | 3 | 5 | 19 | 170657 |
| Unmapped | — | | | | | | | 17181 (1005 declarations) |
| **all of OpenAI/ + Arealaw/** | | | | | | | | 187838 |

Inside the rows, 729 declarations are not reachable from any frozen proof by the name search above (Appendix C lists them by file): Step 1 cuts them with their rows' code rather than porting them.

## 01-introduction.md

Lines now (section total): 1915

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D1.1 | Def (domain, d_Λ, ℋ_Λ) | `OpenAI.domainEDist` (OpenAI/Statements.lean:107); `OpenAI.instDecidableRelAdjSquareLattice` (Statements.lean:99); `OpenAI.Qudits` (Statements.lean:160); `Arealaw.Reg` (Arealaw/Region.lean:42); helpers: OpenAI/Basic.lean:26-83 (`domainEDist_*`, `squareLattice_adj_*`), Arealaw/Region.lean (whole file: glue/split/union/sdiff equivalences, the encoding of ⨂ₓ) | 448 | faithful | golf: keep `Reg`/`domainEDist`, trim the equivalence API of Region.lean to what the proofs use. Pitfall: OK — d_Λ is `SimpleGraph.edist` of the induced graph, `⊤` across components and outside Λ (Statements.lean:107), never the ambient metric. Qudits is scalar-free (`Fin q`); scalars are 𝕜-generic (`RCLike`) in every matrix declaration |
| D1.2 | Def (admissible H, eq:hamiltonian) | `OpenAI.supports` (Statements.lean:164); `OpenAI.domainEDiam` (Statements.lean:114); `OpenAI.hamiltonian` (Statements.lean:171); `OpenAI.IsAdmissible` (Statements.lean:179); `OpenAI.IsSupportedOn` (Statements.lean:246); helpers: OpenAI/Basic.lean:139-178 (`mem_supports_iff`, `isHermitian_hamiltonian`, `IsAdmissible.exists_eq_singleton`), `OpenAI.mem_supports_iff_walk` (OpenAI/Bridges.lean:254), `Arealaw.extendId` and its API (Arealaw/PTrace.lean:216-323) | 218 | faithful | keep (golf the extendId API). 𝕜-generic. Pitfall: OK — interaction is a total family Φ X over X ⊆ Λ, one summand per support, `IsAdmissible` forces Φ X = 0 off `supports Λ R` (nonempty, `domainEDiam ≤ R`, `⊤` excluded), so μ_R depends on R only (Statements.lean:164-183) |
| D1.3 | Def (∂_Λ, ρ_A, S_Ω) | `OpenAI.edgeBoundary` (Statements.lean:135); `OpenAI.pureState` (Statements.lean:191); `Arealaw.SubState.regionEntropy` (Arealaw/Mixed.lean:231); `Arealaw.vonNeumann` (Arealaw/VonNeumann.lean:29); helpers: Arealaw/Mixed.lean:1-229 (`SubState`, `MState`, `restrict`, `entropy`), Arealaw/PTrace.lean:1-215 (`ptrace`), Arealaw/VonNeumann.lean, Arealaw/Entropy.lean:1-66 (`Arealaw.H`), Arealaw/EntropyBounds.lean, OpenAI/Basic.lean:95-138 and `pureState_M` (:180), `Arealaw.MState.regionEntropy_le_card_mul_log` (OpenAI/BoxEntropy.lean:55; S(A) ≤ card A · log q) | 801 | faithful | golf. Edge boundary stored as ordered pairs (x∈A, y∈Λ∖A); card equals the paper's #∂_Λ A. Region encoding (`Reg`, `ptrace`, `pureState`, `SubState.regionEntropy`) is the statement encoding; second encodings of S (`Arealaw.PureState`/`rhoA`/`EE` in Arealaw/State.lean, Physlib `Sᵥₙ` bridges in Arealaw/Bridge/) are mapped at D2.2. S(A)=S(Λ∖A) is D2.2 item 5; S(∅)=0 is `regionEntropy_empty`. Pitfall: OK — `interedges` of the ambient lattice between A and Λ∖A, both ends in Λ, so ∂_Λ Λ = ∅ (Statements.lean:135) |
| D1.4 | Theorem 1.1 (area law, statement) | `OpenAI.AreaLaw` (Statements.lean:202, frozen def); `OpenAI.area_law` (OpenAI/AreaLaw.lean:94); `OpenAI.HasGlobalGap` (Statements.lean:185); helpers: OpenAI/Basic.lean:185-237 (`HasGlobalGap.eq_smul_of_mulVec_eq` etc.: gap ⇒ uniqueness). Proof of the theorem is D11.26 (other agent); `OpenAI.exists_mutualInfo_exterior_union_le` (AreaLaw.lean:37) is the D11.26 assembly step and is NOT counted here | 106 | faithful | keep. Statement level only; 𝕜-generic over `[RCLike 𝕜]` (paper: ℂ). Pitfall: OK — `AreaLaw 𝕜 q R J Δ := ∃ C, ∀ Λ Φ (admissible) Ω E₀ (eigenvector and Loewner gap) A, S ≤ C · card ∂_Λ A` with (q,R,J,Δ) fixed before C and C before Λ, Φ, Ω, A (Statements.lean:202-212); gap is the operator inequality (`HasGlobalGap`, Statements.lean:185) and uniqueness is derived (Basic.lean:214), as the digest says |
| D1.5 | Step (remarks) | — | 0 | none | — |
| D1.6 | Def (∂_in, Z_A) | `OpenAI.innerBoundary` (Statements.lean:140); `OpenAI.cutEndpoints` (Statements.lean:144) | 9 | faithful | keep. ∂_in = image of `Prod.fst`; Z_A = image fst ∪ image snd of the ordered edge set |
| D1.7 | Corollary 1.2 | `OpenAI.AreaLawCorollary` (Statements.lean:228, frozen); `OpenAI.VertexAreaLaw` (Statements.lean:214, frozen); `OpenAI.area_law_corollary` (OpenAI/AreaLaw.lean:129); `OpenAI.vertexAreaLaw_of_areaLaw`, `OpenAI.areaLawCorollary_of_areaLaw`, counting lemmas `card_le_four_mul_card_image_fst/snd`, `card_innerBoundary_le`, `card_edgeBoundary_le_four_mul_innerBoundary`, `card_cutEndpoints_le`, `card_edgeBoundary_le_two_mul_cutEndpoints` (OpenAI/Corollary.lean, whole file); `OpenAI.card_neighbors_le_four` (OpenAI/Basic.lean:84) | 143 | drift | keep (golf). Route D1.7.5: paper: c(v) = number of crossing edges at v∈Z_A, Σ c(v) = 2·#∂_Λ A, c(v)≤4; Lean: #∂ ≤ 4·#∂_in and #∂ ≤ 4·#(image snd), Z_A = (image fst) ⊔ (image snd) disjoint, so 2#∂ ≤ 4#Z (Corollary.lean:79-90). D1.7.1 (rectangle, merge terms on equal supports so R=1 admissible) has no declaration: `AreaLawCorollary` states `AreaLaw 𝕜 q 1 J Δ` for every finite Λ, so rectangles are an implicit special case and "merge terms" is built into the total family Φ. Constant C replaced by `max C 0` (Corollary.lean:96). 𝕜-generic. Pitfall: OK — factor 2 in the Z_A form comes from the double count (`card_edgeBoundary_le_two_mul_cutEndpoints`, Corollary.lean:79), not 4 |
| D1.8 | Step (history) | — | 0 | none | — |
| D1.9 | Def (PEPS, bond dimension) | — | 0 | none | — (not formalized; correct, only D1.10 uses it and D1.10 is external) |
| D1.10 | Step (tensor-network consequence) | — | 0 | none | — (companion-paper theorem; by-products are Prop 4.3, 9.6, 10.2, 11.2, mapped in their sections) |
| D1.11 | Def (mutual information) | `Arealaw.SubState.mutualInfo` (Arealaw/Mixed.lean:236); `Arealaw.SubState.mutualInfo_def` (Mixed.lean:249), `mutualInfo_comm` (Mixed.lean:301); `Arealaw.SubState.mutualInfo_congr` (OpenAI/RegionEntropy.lean:122); `Arealaw.MState.mutualInfo_nonneg` (RegionEntropy.lean:179) | 37 | faithful | keep. Defined as S(X)+S(Y)−S(X∪Y) on regions of a `SubState`; disjointness is an unchecked convention (docstring Mixed.lean:233-235), hypotheses `Disjoint X Y` appear in the lemmas. SSA consequences I≥0 and monotonicity are at D2.2. Duplicate in base 2 (`mutualInfo₂`, Mixed.lean:285) is unmapped |
| D1.12 | Step (reduction to collar information) | = D11.1: frozen `OpenAI.TwoFamilyCancellation` (Statements.lean:388), `OpenAI.two_family_cancellation` (OpenAI/TwoFamily.lean:106); chain-rule helpers `Arealaw.SubState.regionEntropy_union_biUnion`, `Arealaw.MState.regionEntropy_union_biUnion_le` (OpenAI/RegionEntropy.lean:131,185) listed under (section infra) of 02-preliminaries | 0 | none | merge into D11.1 (lines counted there) |
| D1.13 | Step (ambient vs graph locality) | — (ambient notions `OpenAI.ambientEDist`, `ambientDilation` are mapped at D2.6; the bridge `OpenAI.exterior_union_subset_graphNeighborhood_compl_of_lt_ambientEDist`, OpenAI/GraphNeighborhoodCutClearance.lean:136, is D11.26.3) | 0 | none | — |
| D1.14 | Step (stage 1, roadmap) | — (stated at D3.16: frozen `OpenAI.InitialBoxEstimate`) | 0 | none | — |
| D1.15 | Step (stage 2, roadmap) | — (D4.6, D4.11, D7.14) | 0 | none | — |
| D1.16 | Step (stage 3, roadmap) | — (D8.8, D9.9, D9.19, D9.25: frozen `OpenAI.CollarBound`) | 0 | none | — |
| D1.17 | Step (stage 4, roadmap) | — (D10.4: frozen `OpenAI.Amplification`) | 0 | none | — |
| D1.18 | Step (stage 5, roadmap) | — (D11.4: frozen `OpenAI.TwoFamilyDecomposition`; D11.26) | 0 | none | — |
| (section infra) | — | none (all §1 infrastructure is attributed to a row above) | 0 | — | — |
| (section infra, reverse pass) | — | (whole file, 9 decls) (OpenAI/Statements.lean:283-410) | 153 | — | frozen helper definitions of OpenAI/Statements.lean: keep |

## 02-preliminaries.md

Lines now (section total): 4865

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D2.1 | Def (S(D∣E), I(D:E), I(D:F∣E)) | I(D:E): `Arealaw.SubState.mutualInfo` (counted at D1.11). S(D∣E) and region-level I(D:F∣E): no declaration, written as explicit differences `regionEntropy (X∪Y) − regionEntropy Y` (e.g. `OpenAI.ConditionalContinuity`, Statements.lean:436; `regionEntropy_strong_subadditivity`, OpenAI/RegionSSA.lean:108). A second, matrix-level, ℂ-only CMI: `Entropy.MarginalPhase.condMutualInfo` (OpenAI/MarginalPhaseQuadratic.lean:31, QICLean port, I(X:F∣U) on X×(U×F)) | 38 | missing | prove: add `condEntropy` / `condMutualInfo` on regions once (Mathlib-style notation over `Reg`), state SSA and D2.4 with it; merge `condMutualInfo` (§5/§6 user) into it. **Step 1 done:** `AreaLaw.condEntropy` (AreaLawRefactored/S02_Preliminaries.lean:26), `AreaLaw.condMutualInfo` (:31); I(D:E) stays `Arealaw.SubState.mutualInfo` |
| D2.2 | Step (entropy facts without proof) | item 1 SSA: `Arealaw.vonNeumann_strong_subadditivity` (OpenAI/ConditionalEntropy.lean:364, unnormalized PSD, 𝕜 via `OpenAI.toComplex` from ℂ-only `…_complex` :284 which uses Physlib `Sᵥₙ_strong_subadditivity`); region form `Arealaw.SubState.regionEntropy_strong_subadditivity` (OpenAI/RegionSSA.lean:108). item 2: `…regionEntropy_union_sub_le_of_subset` (RegionSSA.lean:163). item 3: `…mutualInfo_le_mutualInfo_union` (RegionSSA.lean:178). item 4: matrix form `Arealaw.abs_vonNeumann_sub_traceLeft_le` (ConditionalEntropy.lean:515, counted at D2.4; no region form). item 5: `OpenAI.regionEntropy_pureState_sdiff` (OpenAI/RegionEntropy.lean:263) via `coeffMatrix`, `Arealaw.EE` (Arealaw/State.lean). item 6: `regionEntropy_empty` (D1.3). Subadditivity/Araki–Lieb: `Arealaw.MState.regionEntropy_union_le` (RegionEntropy.lean:170, 𝕜), `Arealaw.regionEntropy_union_le` (Arealaw/Subadditivity.lean:50, ℂ-only via `unionState`, Physlib `Sᵥₙ_subadditivity`); Physlib bridges Arealaw/Bridge/{Entropy,MState,VonNeumann}.lean; files: ConditionalEntropy.lean:233-405, RegionSSA.lean:1-197, RegionEntropy.lean:1-121 and 170, Subadditivity.lean, State.lean | 884 | smeared | replace-by Physlib `Sᵥₙ_strong_subadditivity`, `Sᵥₙ_subadditivity`, `Sᵥₙ_triangle_subaddivity` (ℂ, normalized states) + ONE ℂ→𝕜 transfer at top (decision 1); the items 2, 3, 5 are one-line corollaries to state once in the library tree (Standard?). Delete the unnormalized-PSD re-proofs (ConditionalEntropy.lean:233-405), the ℂ/𝕜 duplicate subadditivity (Subadditivity.lean vs RegionEntropy.lean:170), the Bridge/ files and the bipartite `PureState/rhoA/EE` second encoding once purity is proved on `Reg`. Pitfall: OK — item 4 bounds by log dim of the first argument only, `abs_vonNeumann_sub_traceLeft_le` has `log (card m)` for the traced-out-left factor (ConditionalEntropy.lean:515). **Step 1 done:** `AreaLaw.step_2_2` (AreaLawRefactored/S02_Preliminaries.lean:56), from library `Arealaw.MState.regionEntropy_strong_subadditivity`, `regionEntropy_union_sub_le`, `mutualInfo_le_mutualInfo_union`, `abs_regionEntropy_union_sub_le_log_card`, `regionEntropy_pureState_sdiff` (AreaLawForMathlib/QuantumInfo/Region.lean:177-246) on Physlib SSA |
| D2.3 | Def (binary entropy h, trace distance δ) | h: Mathlib `Real.binEntropy` (used by Statements.lean:436 `ConditionalContinuity`); δ: `Arealaw.SubState.D₁` (Arealaw/TraceDist.lean:134), `Matrix.traceNorm` (Physlib), `Arealaw.MState.D₁_eq_traceNorm_div_two` (TraceDist.lean:221); files Arealaw/TraceDist.lean, Arealaw/TraceNorm.lean | 304 | overbuilt | golf: replace-by `Real.binEntropy` (already) and Physlib `TrDistance` / `(ρ-σ).traceNorm/2` on normalized states; drop the subnormalized correction term `\|tr ρ − tr σ\|` of `D₁` and the effect-variational API unless D2.5.3 needs it (it does: `D₁_restrict_le`). **Step 1 done:** `AreaLaw.traceDist` (AreaLawRefactored/S02_Preliminaries.lean:80, = `D₁`); h = Mathlib `Real.binEntropy`; `AreaLaw.C_h` (:84) |
| D2.4 | Lemma 2.1 | `OpenAI.ConditionalContinuity` (Statements.lean:436, frozen); `OpenAI.conditional_continuity` (OpenAI/ConditionalContinuity.lean:270); bipartite bounds `Arealaw.abs_vonNeumann_sub_traceLeft_sub_le` (:176, sharp) and `…_sqrt` (:216, 4√δ log(e d)); mixture bounds `Arealaw.vonNeumann_sub_traceLeft_add_le` (OpenAI/ConditionalEntropy.lean:461) and `…_add_le_add` (:497), block-diagonal/cq machinery ConditionalEntropy.lean:86-232, dimension bound `Arealaw.abs_vonNeumann_sub_traceLeft_le` (:515); scaling `Arealaw.vonNeumann_smul` (OpenAI/EntropyMixing.lean:85, whole file); concavity RegionSSA.lean:198-246; I-continuity `OpenAI.abs_mutualInfo_sub_le` (OpenAI/CollarEntropyIdentity.lean:117, constant 8); usage variants for pure states on other encodings: `FiniteProduct.abs_entropy_sub_le_sqrt_traceDistance` (OpenAI/FiniteProductContinuity.lean:75), `OpenAI.abs_regionalEntropy_sub_le_sqrt_traceDistance` (OpenAI/RegionalEntropyContinuity.lean:42) | 1087 | drift | keep statement; merge the two usage variants into D2.4 (specialise `conditional_continuity` at Y=∅ and pure states). Routes: paper: D2.4.1 mixture bound via cq register and SSA/concavity, D2.4.2 Jordan decomposition with δ>0 case split, constant C=2(1+2/e); Lean: unnormalized PSD superadditivity + upper bound (`vonNeumann_sub_traceLeft_add_le(_add_le_add)`, block-diagonal entropy from charpoly), Jordan parts from Physlib `posPart/negPart` with traces (`exists_posSemidef_sub_eq`, ConditionalContinuity.lean:134), no δ=0 split, constant C=4 (`winterModulus_le_sqrt`, :114) and 8 for I (D2.4.6 route via two applications, CollarEntropyIdentity.lean:117). 𝕜-generic (SSA through `toComplex`). Pitfall: OK — controlled system is the first argument, bounds use `Fintype.card (Reg loc X)` of X only, not of Y (Statements.lean:436-466). **Step 1 done:** `AreaLaw.lemma_2_1 : ConditionalContinuity σ loc ℂ` (AreaLawRefactored/S02_Preliminaries.lean:238), steps `AreaLaw.step_2_4_4` (:97), `AreaLaw.step_2_4_3` (:151, D2.4.1-D2.4.3, D2.4.5), library AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean (cq states, mixture bound, Jordan decomposition); paper route, constant 2C_h weakened once to the frozen 4. D2.4.6 (I(D:E)) not stated |
| D2.5 | Step (pure-state trace distance; usage rule) | `OpenAI.traceDistance_vecMulVec_le_norm_sub` (OpenAI/Amplification/EntropyComparison.lean:147, ℂ, `EuclideanSpace ℂ n`); D2.5.1 `Matrix.traceNorm_div_two_vecMulVec_eq` (OpenAI/PureStateTraceDistance.lean:69, whole file, QICLean port); D2.5.3 `Arealaw.SubState.D₁_restrict_le` (OpenAI/CollarEntropyIdentity.lean:30, regions) and duplicate `Matrix.traceNorm_traceRight_le` (EntropyComparison.lean:86, bipartite) | 360 | faithful | keep; merge `traceNorm_traceRight_le` into `D₁_restrict_le` (one contractivity statement). ℂ-only (no 𝕜 version); D2.5.1 proven via X³=cX and \|X\|=c^{-1/2}X² instead of "eigenvalues ±λ", same content. Pitfall: n/a (no quantifier-order claim). **Step 1 done:** `AreaLaw.step_2_5` (AreaLawRefactored/S02_Preliminaries.lean:283); library `Matrix.traceNorm_vecMulVec_sub_vecMulVec_div_two`, `Arealaw.SubState.D₁_restrict_le` (AreaLawForMathlib/QuantumInfo/Region.lean:39, :260) |
| D2.6 | Def (balls, neighborhoods, dilations) | `OpenAI.graphNbhd` (Statements.lean:119; B_Λ(x,r) = `graphNbhd Λ {x} r`); `OpenAI.graphNbhd_subset` (:122); `OpenAI.ambientDilation` (Statements.lean:153; T_j); `OpenAI.ambientEDist` (Statements.lean:149; dist_∞); helpers `OpenAI.mem_graphNbhd_iff_walk` (OpenAI/Bridges.lean:274), `OpenAI.mem_graphNbhd_singleton_iff` (OpenAI/FiniteSetTruncation.lean:48) | 49 | faithful | keep. No separate B_Λ definition (singleton neighbourhood). Pitfall: OK — T_j is the Minkowski sum with `Icc (-j,-j) (j,j)` in ℤ×ℤ, not cut to Λ (Statements.lean:153); `graphNbhd` filters `Λ` by `⨅ domainEDist ≤ r`, empty set gives ∅. **Step 1 done:** `AreaLaw.ball` (AreaLawRefactored/S02_Preliminaries.lean:311); N_r = `OpenAI.graphNbhd`, T_j = `OpenAI.ambientDilation` (frozen) |
| D2.7 | Step eq:ball-count | exact v_r bound only generically: `OpenAI.card_latticeDiamond` (OpenAI/GraphLatticeDiamond.lean:148), `OpenAI.card_le_diamond_of_walks` (:175), `OpenAI.card_le_diamond_of_edist_le` (:187), `OpenAI.latticeL1Distance` (OpenAI/GraphLatticeDistance.lean:32); on the induced domain graph only the weaker `OpenAI.card_graphBall_domainGraph_le` (OpenAI/LatticeCounts.lean:49, ≤ 2(d+1)²); coarser duplicates `OpenAI.card_graphNbhd_singleton_le` (FiniteSetTruncation.lean:66, (2d+1)²), `…_le_four` (:72), `…_le_two_mul` (OpenAI/Amplification/ConstraintWordTruncation.lean:244), `OpenAI.Scan.card_domainGraph_ball_le` (OpenAI/Scan/SubsystemSize.lean:52); files GraphLatticeDiamond.lean, GraphLatticeDistance.lean (whole) | 403 | smeared | restate: one `card_graphNbhd_le : card (graphNbhd Λ {x} r) ≤ 1 + 2r(r+1)` on the induced graph (D2.7.1 = ambient l1 containment via `latticeL1Distance_le_walk_length`, D2.7.2 = `card_latticeDiamond`); inline the four coarser duplicates. 𝕜-free. **Step 1 done:** `AreaLaw.eq_ball_count` (AreaLawRefactored/S02_Preliminaries.lean:358), `AreaLaw.v` (:315); library `Finset.card_le_of_forall_natAbs_add_natAbs_le` (AreaLawForMathlib/Data/Int/L1Ball.lean:15) |
| D2.8 | Step (term multiplicity and norm budget) | supports through a site: `OpenAI.card_admissibleSupport_containing_le` (OpenAI/BufferedRectangles.lean:132) with `subset_latticeDiamond_of_mem_supports` (:121) and generic `OpenAI.card_supports_containing_le_diamond` (OpenAI/GraphInteractionDiamondCounting.lean:52), `card_supportFamily_le_pow` (OpenAI/GraphInteractionBudget.lean:66) and `_erase` (:42); \|X\| ≤ v_R: `OpenAI.card_le_diamond_of_mem_supports` (OpenAI/TailParameter.lean:72), `OpenAI.card_support_le_diamond` (GraphInteractionDiamondCounting.lean:37); anchors: `OpenAI.card_anchor_fiber_le_diamond` (OpenAI/LatticeCounts.lean:68), duplicates `OpenAI.card_anchor_fiber_le` (FiniteSetTruncation.lean:82, coarse 2^((2R+1)²)), `OpenAI.card_anchor_fiber_le_two_pow` (ConstraintWordTruncation.lean:324), `OpenAI.card_filter_mem_supports_le` (OpenAI/SupportCounting.lean:96, coarse); norm budget J μ_R: `OpenAI.sum_supportWeights_containing_le_diamond` (GraphInteractionDiamondCounting.lean:83), `…sum_supportNorms_containing_le_diamond` (:102) | 355 | smeared | restate as one declaration on `supports Λ R` (card through a site ≤ μ_R, \|X\| ≤ v_R, anchor fibre ≤ μ_R, Σ_{X∋x} ‖Φ X‖ ≤ J μ_R); inline the coarse duplicates and the abstract-graph (`coord`, `hstep`) generality of GraphInteractionDiamondCounting.lean. Pitfall: OK — terms are indexed by the support set X ⊆ Λ (Φ X total family, zero or scalar term keeps its support), μ_R counts index sets (Statements.lean:164-183, BufferedRectangles.lean:132). **Step 1 done:** `AreaLaw.step_2_8` (AreaLawRefactored/S02_Preliminaries.lean:385), `AreaLaw.μ` (:318) |
| D2.9 | Step eq:crossing-count | `OpenAI.card_crossingTerms_le_edgeBoundary` (OpenAI/TailParameter.lean:82; ≤ #∂_Λ A · v_R μ_R); `OpenAI.crossingTerms` (OpenAI/RegionLift.lean:102, with `mem_crossingTerms`, `notMem_crossingTerms_iff`); `OpenAI.exists_edgeBoundary_of_walk` (OpenAI/Rectangles.lean:280). Radius-r₀ variant `OpenAI.card_crossingLabels_le` (CrossingBudget.lean:88) is §4 | 76 | drift | restate to the paper's form or record. Routes: paper: anchor a of each split support, y on the other side with d_Λ(a,y)≤R, shortest path crosses an edge z z', a∈B(z,R), ≤ 2#∂ endpoints z, ≤ v_R anchors each, ≤ μ_R terms per anchor (constant 2 v_R μ_R); Lean: no anchors — a split support X contains v∈A and w∉A, a walk gives edge (u,u')∈∂ with u∈A and l1-distance(u,v) ≤ R, so X contains a site of the ambient diamond of u; bound = #∂ · v_R · μ_R (constant v_R μ_R: the oriented edge set has one endpoint per edge, ambient diamond instead of graph ball) (TailParameter.lean:82-117). Also used only through TailParameter (§3). Pitfall: OK — count is in `edgeBoundary Λ A` (induced-graph edge boundary). **Step 1 done:** `AreaLaw.eq_crossing_count` (AreaLawRefactored/S02_Preliminaries.lean:446), paper anchor route and constant 2 v_R μ_R |
| D2.10 | Step (product decomposition across a bipartition) | `OpenAI.HasProductDecomposition` (OpenAI/CutTerms.lean:49); `OpenAI.IsSupportedOn.hasProductDecomposition_submatrix_glueEquiv` (OpenAI/CutTransport.lean:200; N = (dim D)², ‖c‖‖d‖ ≤ ‖X‖); duplicate `…hasProductDecomposition_inter_submatrix_glueEquiv` (OpenAI/FilterChainEnergy.lean:97; N = (dim (S∩B))²) | 92 | faithful | keep the first; merge the `inter` variant into it (specialise D := S∩B or prove once with the finer count). Matrix-unit expansion c_{ijkl} E_ij ⊗ E_kl, as the digest. 𝕜-generic. Pitfall: n/a (the modified-support caveat concerns §4). **Step 1 done:** `AreaLaw.step_2_10` (AreaLawRefactored/S02_Preliminaries.lean:506), `AreaLaw.cutEquiv` (:498) |
| D2.11 | Step (degenerate cases) | `OpenAI.regionEntropy_eq_zero_of_range_zero` (OpenAI/ZeroBoundary.lean:398), `…_of_q_eq_one` (:424), `…_of_eq_empty` (:431), `…_of_unique` (:417) | 41 | drift | cut (or prove as the paper's standing-assumption lemma if §3–§11 are written under q≥2, R≥1, Λ≠∅). Paper: reduce to q≥2, R≥1, Λ≠∅ and carry these as standing assumptions; Lean: no reduction — `area_law` (AreaLaw.lean:94) holds for q≥1 and every R uniformly, and these four theorems are referenced only from OpenAI/Audit.lean (not used by `area_law`). R=0 case goes through the split-interaction lemma (`regionEntropy_pureState_eq_zero_of_split`, ZeroBoundary.lean:328) rather than a tensor product of site vectors. Pitfall: OK — R=0 proof uses uniqueness via the gap hypothesis, no gap quantity (hΔ only gives uniqueness). **Step 1 done:** `AreaLaw.step_2_11` (AreaLawRefactored/S02_Preliminaries.lean:753), via `AreaLaw.regionEntropy_eq_zero_of_split` (:659) |
| D2.12 | Lemma 2.2 | `OpenAI.regionEntropy_eq_zero_of_edgeBoundary_eq_empty` (OpenAI/ZeroBoundary.lean:387); `OpenAI.subset_or_subset_sdiff_of_edgeBoundary_eq_empty` (:367); `OpenAI.regionEntropy_pureState_eq_zero_of_split` (:328) and its helpers (`commute_extendId_extendId`, `exists_eq_vecMulVec_of_forall_commute`, `HasGlobalGap.mul_coeffMatrix_eq_smul`, …; ZeroBoundary.lean:1-397) | 397 | drift | restate along the digest or record in RefactoringResult §5. Routes: paper: A is a union of components (D2.12.1), H = ⊕ H_c, ground eigenspace ⊗ ker(H_c−E_c), unique ⇒ each factor 1-dim, Ω = ⊗Ω_c (D2.12.3-6); Lean: no component decomposition — every operator K on A commuting with H_A extends (identity off A) to an operator commuting with H, hence maps Ω to a multiple of itself (via the gap/uniqueness), forcing the coefficient matrix across the cut A versus Λ∖A to have rank one, so ρ_A is a rank-one projection (idempotent ⇒ S=0). Paper route needs Lean-costly tensor sums of Hamiltonians; Lean route is a legitimate exception candidate. 𝕜-generic. Pitfall: OK — only uniqueness is used (gap enters through `HasGlobalGap.mul_coeffMatrix_eq_smul`, ZeroBoundary.lean:173). **Step 1 done:** `AreaLaw.lemma_2_2` (AreaLawRefactored/S02_Preliminaries.lean:725); formal route for D2.12.3-6 (RefactoringResult §5) |
| D2.13 | Def (convention for constants C, c) | — (realised as the quantifier order of `AreaLaw`/`CollarBound`/… in Statements.lean) | 0 | none | — |
| (section infra) | — | OpenAI/Embedding.lean (whole file, 505: 𝕜→ℂ entrywise embedding `OpenAI.toComplex` used to carry Physlib's ℂ-only SSA, subadditivity, Araki–Lieb to 𝕜); `Arealaw.kronUnion` and API (Arealaw/PTrace.lean:324-396); chain rule `Arealaw.SubState.regionEntropy_union_biUnion`, `Arealaw.MState.regionEntropy_union_biUnion_le` (OpenAI/RegionEntropy.lean:131,185; consumed by D11.1/D1.12) | 664 | — | cut Embedding.lean once the development is over ℂ with one top-level transfer (decision 1); kronUnion: check users; chain rule: move to D11.1 |
| (section infra, reverse pass) | — | (whole file, 8 decls) (OpenAI/SupportCounting.lean:61-130) | 115 | — | inline into S02 Hamiltonian setup (supports Λ R enumeration, term-size count; paper-anchored by D1/D2 Hamiltonian); owner anchor to be assigned |

## 03-initial-box.md

Lines now (section total): 10096

Scalar field: the frozen `MarginalTails` / `BufferDiscount` / `InitialBoxEstimate` are `[RCLike 𝕜]`. The Lean proof is ℂ-only for the analytic core (D3.1 bipartite bound, D3.4 filter argument) and goes through two piecewise `toComplex` transfers: `OpenAI.marginal_tails` (OpenAI/MarginalTails.lean:135, 29 `toComplex` uses) and `OpenAI.bufferDiscount_of_complex` (OpenAI/BufferDiscount.lean:456). D3.16 is natively 𝕜-generic (no transfer). The filter-algebra files (FilterMaximizer, FilterStationarity, FilterChain, FilterOptimizer, FilterClipping, RegionLift, BufferDiscountCore halves) are stated over `RCLike 𝕜` although only used at ℂ.

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D3.1 | Lemma 3.1 (lem:tail) | `OpenAI.MarginalTails` (OpenAI/Statements.lean:469, frozen); proved by `OpenAI.marginal_tails` (OpenAI/MarginalTails.lean:135, 𝕜-generic statement, reindexes along `glueEquiv` then transfers to ℂ); helpers: OpenAI/MarginalTails.lean, EigenbasisTails.lean (`log_surprisalMoment_eigenvalues_le`:229, `surprisalTail_eigenvalues_le`:249; conjugates into the marginal's eigenbasis), GapSurprisal.lean (`re_inner_tilt_sub_le`:85 = D3.1.9, `gap_surprisalMoment`:166 = D3.1.10, `log_surprisalMoment_le_of_schmidtRow`:248, `surprisalTail_le_of_schmidtRow`:273), SurprisalMoment.lean (`le_mul_of_halving`:109 = D3.1.11-12, `surprisalTail_le`:190 = D3.1.13), SchmidtTilt.lean (tilt = D3.1.1-4), ModularExpectation.lean (f_i(z) = D3.1.4-6), StripQuadratic.lean (D3.1.7-8, Mathlib `HadamardThreeLines`), CutTerms.lean, CutTransport.lean (product decomposition across the cut) (all whole files) | 2343 | faithful | golf; Standard?: three-lines already Mathlib (`Complex.HadamardThreeLines`, used in StripQuadratic.lean:77); Cauchy coefficient estimate (StripQuadratic.lean:125, 70 lines) replace-by Mathlib Cauchy estimate: search pending. Pitfall: OK — 𝓑 = 1 + Σ log²(e·card Reg(D i)) over crossing terms, u-range (32√((1+c₀/g₀)𝓑))⁻¹ keeps the (1+ϑ) factor, complement dimension never appears, OpenAI/Statements.lean:469-491. Proof follows D3.1.1-13 in order (ℂ-only core; SurprisalMoment and SchmidtTilt are also consumed by §4/§10) **Step 1 done:** `AreaLaw.lemma_3_1 : MarginalTails σ loc ℂ` (AreaLawRefactored/S03_InitialBox/MarginalTails.lean:999), steps D3.1.1–D3.1.13 in order as `have`s and anchored lemmas: `M` (:28, M(u), with `hasDerivAt_log_M` L′(0)=S), `step_3_1_12` (:55), `step_3_1_13` (:87), `step_3_1_7` (:127, Mathlib `HadamardThreeLines`), `step_3_1_8` (:162, route difference, RefactoringResult §5), Schmidt coordinates `row`/`IsSchmidt`/`modF` = f_i (:203-219), `modF_neg` (:298), `sum_add_mul_le` (:369, row/column Cauchy–Schwarz, reused by D3.9.5), `step_3_1_6` (:451), `tilt` (:523), `gap_le` (:625), `step_3_1_8_term` (:654), `step_3_1_10` (:695, D3.1.1–D3.1.10), `step_3_1_1` (:900, cut transport); library: `Matrix.sum_norm_apply_sq_le_l2_opNorm_sq`, `Matrix.l2_opNorm_mul_mul_le_of_le_one` (AreaLawForMathlib/Analysis/CStarAlgebra/Matrix.lean:16, :25). Standard axioms only |
| D3.2 | Step eq:initial-local-tail-parameter | `OpenAI.cutLogBudget_le_edgeBoundary` (OpenAI/TailParameter.lean:168) states 𝓑 ≤ C(1+b'); `OpenAI.concentrationWidth_le` (:197) + `OpenAI.IsAdmissible.one_sub_rpow_le_typicalMass_edgeBoundary` (:253) state the tail (as typical mass ≥ 1−(n+2)^−M, via `concentrationWidth`/`one_sub_rpow_le_typicalMass_reducedState` in OpenAI/Scan/MarginalTailsBridge.lean, not mapped here); helpers: OpenAI/TailParameter.lean (whole file) | 152 | smeared | restate as one lemma (𝓑 ≤ C(1+b') then Pr{∣K−S∣>C_M√(1+b')log(n+2)} ≤ (n+2)^−M); merge into D3.2: second crossing-count/𝓑 bound `OpenAI.cutLogBudget_le_card` (OpenAI/BufferDiscount.lean:90, constant (2R+1)²) vs `cutLogBudget_le_card_diamond` here (v_R=1+2R(R+1)). Pitfall: OK — n a free natural, no relation to b', OpenAI/TailParameter.lean:197. Only consumed by §10 (`Amplification/TypicalProjectors`); Lemma 3.2's proof does not use it **Step 1 done:** D3.2.1–D3.2.3 `AreaLaw.step_3_2_3` (AreaLawRefactored/S03_InitialBox/MarginalTails.lean:1120), sharper `step_3_2_3'`, `AreaLaw.C₁` (:1090); D3.2.4 `AreaLaw.step_3_2_4` (:1137) with `C_M` = 32(M+2)√((1+ϑ)C₁) (:1133), stated as the arithmetic step taking Lemma 3.1's tail at w = C_M√(1+b')log(n+2) |
| D3.3 | Def (safe rectangles) | `OpenAI.IsIntRect` (OpenAI/Statements.lean:495), `OpenAI.boxSize` (:500), `OpenAI.IsSafe` (:505), `OpenAI.ambientDilation` (:153), `OpenAI.cutEndpoints` (:144) (all frozen, not counted); helpers: OpenAI/Rectangles.lean lines 1-237 and 309-363 (rectangle/size/dilation algebra, ambient distance, `IsSafe` API; the dilation part is D2.6 material) | 311 | faithful | keep (defs frozen); golf the Rectangles API. Pitfall: OK — `IsSafe` is relative to `cutEndpoints Λ A` (Z_A) and distance to ∅ is ⊤ via `ambientEDist` (OpenAI/Statements.lean:505); only R<D₀ is used downstream (OpenAI/BufferDiscount.lean:498). 𝕜-independent **Step 1 done:** frozen defs kept; rectangle API `AreaLaw.boxSize_Icc`, `boxSize_mono`, `card_le_boxSize_sq`, `mem_ambientDilation`, `IsSafe.subset'` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:24-57) |
| D3.4 | Lemma 3.2 (lem:initial-buffer) | `OpenAI.BufferDiscount` (OpenAI/Statements.lean:514, frozen); `OpenAI.buffer_discount` (OpenAI/BufferDiscount.lean:508) = `bufferDiscount_of_complex` (:456) ∘ `bufferDiscount_complex` (:482, ℂ; explicit Z_min, C_pad, C_buf) ∘ `condEntropy_le_initialBuffer_of_constants` (:177) ∘ `OpenAI.two_mul_condEntropy_le` (OpenAI/BufferDiscountCore.lean:447); helpers: OpenAI/BufferDiscount.lean lines 1-68 and 438-512 (ℂ→𝕜 transfer `regionEntropy_pureState_toComplex`:445, `bufferDiscount_complex`, `buffer_discount`) | 93 | faithful | keep; restate the 268-line proof of :177 as steps D3.4.1-7 (each step a `have` calling the anchor's declaration); remove the 𝕜→ℂ transfer if developed over ℂ. Pitfall: OK — ∃ C_pad,C_buf placed before ∀ D₀,Λ,Φ,… (OpenAI/Statements.lean:514); built as Z_min(q,R,J,Δ) → C_pad = ⌈(R+3)e^{(R+1)Z_min}⌉+R+3 → C_buf=(1024e(J/Δ)K'+C_pad)/2, K,K' depend on q,R only (OpenAI/BufferDiscount.lean:482-506) **Step 1 open:** `lemma_3_2` not written (needs the D3.7 chain assembly, D3.8.1, D3.9.2/6, D3.11.1, D3.12.1–3/5–6, D3.13.2 on regions). Its frozen `BufferDiscount ℂ q R J Δ` needs `1 ≤ q`, `0 < J`, `0 < Δ` as hypotheses (old `OpenAI.buffer_discount`, OpenAI/BufferDiscount.lean:508, takes the same). Available: D3.5, D3.6, D3.8.2–3, D3.9.4, D3.10, D3.11.4–5, D3.14 (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean); D3.7.1–4 (no chain), D3.9.1, D3.9.3, D3.9.5, D3.11.2–4, D3.12.4, D3.13 (AreaLawRefactored/S03_InitialBox/Filters.lean) |
| D3.5 | Step (nested regions, locality, single split, contour budget) | no declaration states (a)-(e): the `have`s `hXT`, `hdle`, `hT`, `hdisj`, `hsingle`, `hcross`, `hB` inside `OpenAI.condEntropy_le_initialBuffer_of_constants` (OpenAI/BufferDiscount.lean:177); helpers: OpenAI/BufferDiscount.lean lines 69-113 and 169-437; OpenAI/Rectangles.lean lines 238-308 and 364-413 (`exists_edgeBoundary_of_walk`:280, `exists_mem_cutEndpoints_dist_le_of_walk`:293, `subset_of_isSafe`:364, `not_splits_two_contours`:393 = D3.5.2-4); OpenAI/SupportCounting.lean lines 168-268 (`IsIntRect.card_crossingTerms_le_of_isSafe`:200, `eq_of_splits_of_isSafe`:250 = D3.5(d)-(e)); OpenAI/BufferedRectangles.lean `exists_of_splits_rectRegion`:107, `card_crossingTerms_rectRegion_le`:150 (unused second proof of (e)) | 637 | smeared | restate as one lemma stating (a)-(e) with D=R+1 replaced by the paper's D; cut BufferedRectangles:107,150 (second encoding of the crossing count, 0 uses outside Audit) and keep only one of the two counts (K=8R·2^{(2R+1)²} here vs 8(R+1)μ_R there vs 2v_Rμ_R in D3.2). Pitfall: OK — X_0=A∩Q₀ kept apart, margin X_0→X_1 is r+D: X∪T_j = A∩ambientDilation Q₀ (r+(j+1)D) (OpenAI/BufferDiscount.lean:223,256). Deviation: Lean takes D=R+1 and uses only R<D₀ (single split needs D>R), not D>2R+2; T_j is padded to j ≥ m by Λ\X to index by ℕ **Step 1 done:** `AreaLaw.step_3_5` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:418), steps `step_3_5_1`…`step_3_5_5`, `X_j` (:150), `C₂` (:377); paper's D (hyp. D > 2R+2), uses only R < D₀ |
| D3.6 | Step eq:initial-harmonic-weights | `OpenAI.harmonicWeight` (OpenAI/HarmonicWeights.lean:61), `sum_harmonicWeight`:69, `sum_mul_harmonicWeight_sq`:78 (ℰ=4/Z), `harmonic_cost_le`:93 (min property, D3.6.1), `log_div_le_sum_inv_contour_of_le`:149 (Z_r lower bound, D3.6.2); a_j ≤ 1/2 is `harmonic_weight_le_half` (counted in D3.10); helpers: OpenAI/HarmonicWeights.lean lines 1-172 | 172 | faithful | keep; golf. Standard?: weighted Cauchy–Schwarz, no library name needed. Pitfall: OK — ℰ→0 only logarithmically, and the O(m·ℰ) error is absorbed into C_buf·r via 4/Z ≤ 1 and m ≤ C_pad r (OpenAI/BufferDiscount.lean:297,413) **Step 1 done:** `AreaLaw.eq_initial_harmonic_weights` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:80) with `m`, `d`, `Z_r`, `a`, `ℰ` (:61-73); paper route (log(1+t) ≤ t in place of the integral). The last sentence (C_pad so a_j ≤ ½) is in `eq_initial_weight_range` (D3.10) |
| D3.7 | Step eq:initial-filter-commutation | `OpenAI.exists_max_feasible_chain` (OpenAI/FilterMaximizer.lean:175, existence, N>0 via `toEuclideanLin_liftProd_chainList_ne_zero`), `OpenAI.commute_regionState_of_unitary_max` (OpenAI/FilterStationarity.lean:375, one filter), `OpenAI.forall_clipped_of_max` (OpenAI/FilterChain.lean:146, all filters, by descending induction via `isDescendingChain_map`:120); helpers: OpenAI/FilterStationarity.lean, FilterMaximizer.lean, FilterChain.lean (whole files) | 876 | faithful | golf; specialise the RCLike algebra to ℂ. Pitfall: n/a (no quantifier-order pitfall; descending order is used: `IsDescendingChain`, FilterStationarity.lean) **Step 1 partial:** D3.7.1 `AreaLaw.step_3_7_1` (AreaLawRefactored/S03_InitialBox/Filters.lean:141: for floors f_j > 0 with dim·f_j ≤ 1 a maximizer of N = ‖K Ω‖ over feasible families exists and N > 0), feasible filters `IsFilter` (:29, spectral form L = V diag(x^{a/2}) V*, x ≥ f = ε^{2/a}, ∑x = 1), `isCompact_setOf_isFilter` (:34), `IsFilter.isUnit_det` (:59), `isFilter_uniform` (:69), product `filterProd` (:114, K = (L_{k−1}⊗1)⋯(L_0⊗1) via `prodDesc` :19), `continuous_extendId` (:106), `continuous_filterProd` (:120), `isUnit_det_filterProd` (:129); library `Matrix.isCompact_setOf_conjTranspose_mul_self_eq_one` (AreaLawForMathlib/Analysis/CStarAlgebra/Matrix.lean:34); D3.7.2 feasibility of the curve `IsFilter.conj` (:77), `IsFilter.exp_conj` (:85, e^{tB}Le^{−tB} feasible for anti-Hermitian B), D3.7.2 `AreaLaw.step_3_7_2` (:191, first-order condition Re⟨AΦ(L)w, AΦ(BL−LB)w⟩ = 0 at a local max of t ↦ ‖AΦ(e^{tB}Le^{−tB})w‖², helper `hasDerivAt_exp_conj` :180), D3.7.3 `step_3_7_3` (:232, one peel: ⟨φ, (LWL⁻¹)⊗1 φ⟩ = ⟨φ, W⊗1 φ⟩ when [L, ρ_{φ,X}] = 0), D3.7.4 `step_3_7_4` (:246, [L, ρ] = 0 from Re Tr(L⁻¹ρLB) = 0 for all anti-Hermitian B; L = (L²)^{1/2} by Mathlib's `Commute.cfc_nnreal`, replacing the old eigenbasis computation); chain assembly `step_3_7` (:494, [L_j, ρ_{φ,X_j}] = 0 for all j < n at a maximizer, nested X_j as hypothesis) with the peel `step_3_7_3_prodDesc` (:451) |
| D3.8 | Step eq:initial-filter-clipping | `OpenAI.abs_log_clipped_sub_le` (OpenAI/LogClipping.lean:130) with `eq_max_div_of_floor_optimal`:75 (D3.8.2-3), `OpenAI.exists_clipped_of_max_feasible` (OpenAI/FilterOptimizer.lean:178, commutation + clipping of a maximizer), `OpenAI.ratio_le_of_diagonal_max` (OpenAI/FilterClipping.lean:164, D3.8.1); helpers: OpenAI/FilterClipping.lean, FilterOptimizer.lean (whole; also holds `IsFeasibleFilter` and `isFeasibleFilter_union_kronecker`:247 = D3.12.2), OpenAI/LogClipping.lean lines 1-144 | 701 | faithful | golf; specialise to ℂ. Standard?: KKT with floor is hand-proved by a one-sided variation (no library); search pending. Pitfall: n/a **Step 1 partial:** D3.8.2 `AreaLaw.step_3_8_2` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:454, floor KKT: x_i = max(ε^{2/a}, p_i/λ), λ > 0), D3.8.3 `step_3_8_3` (:481); D3.8.1 `step_3_8_1` (AreaLawRefactored/S03_InitialBox/Filters.lean:600: at a maximizer on nested regions, j < n, with L_j = V diag(x^{a_j/2}) V* (V unitary, x ≥ f_j, ∑x = 1) and ρ_{φ,X_j} = V diag(p) V*, p_k/x_k ≤ p_i/x_i whenever x_i > f_j: exactly `hopt` of `step_3_8_2`; mass moved from i to k, peel of K_{>j} by `step_3_7_3_prodDesc` with the commutation from `step_3_7`), helpers `step_3_8_1_curve` (:543, one-sided first-order condition Re⟨c 0, c'⟩ ≤ 0 in any complex inner product space), `hasDerivAt_conj_diagonal_rpow` (:564); open: producing such V, x, p from `IsFilter` + `step_3_7` (the eigenvalues l of L in the common eigenbasis are x0^{a/2} up to permutation) and normalising ∑p = 1 for `step_3_8_2`; common eigenbasis available as `Matrix.exists_unitary_diagonal_of_commute` (AreaLawForMathlib/Analysis/Matrix/TraceHolder.lean:150, with `Matrix.sum_norm_sq_row_of_mul_conjTranspose` :28, `trace_mul_eq_sum_mul_norm_sq` :37, `re_trace_mul_le_of_spectral` :60 used by D3.11.3) |
| D3.9 | Step eq:initial-product-energy | `OpenAI.re_inner_sub_le_of_max` (OpenAI/FilterExcitation.lean:206): Re⟨φ,Hφ⟩−E₀ ≤ Σ_j 4a_j² Σ_{crossing} d_i²c₀ (D3.9.1, .6); `abs_re_inner_sub_chain_conj_le_sharp` (OpenAI/FilterChainEnergy.lean, D3.9.2); `abs_re_inner_sub_conj_le_of_common_basis_sharp` (OpenAI/FilterEnergy.lean, D3.9.3); `abs_re_inner_sub_inner_conj_le_sharp` (OpenAI/FilterMoment.lean:281, D3.9.3-5); `sqrt_mul_cosh_sub_one_le_sharp` (OpenAI/LogClipping.lean:282, D3.9.4); helpers: OpenAI/FilterEnergy.lean, FilterChainEnergy.lean, FilterExcitation.lean (whole), OpenAI/FilterMoment.lean lines 230-374, OpenAI/LogClipping.lean lines 145-321 | 1191 | faithful | golf: cut the unused constant-2 / non-sharp duplicates `LogClipping.sqrt_mul_cosh_sub_one_le` (+`sinh_le_mul_cosh`, `cosh_sub_one_le`, `sq_le_mul_exp_half`, lines 145-265, ≈121 lines), `FilterMoment.abs_re_inner_sub_inner_conj_le`:357, `FilterEnergy.abs_re_inner_sub_conj_le_of_common_basis`:141, `FilterChainEnergy.abs_re_inner_sub_chain_conj_le`:475 (0 uses outside Audit); the surviving `re_inner_sub_le_of_chain` (FilterExcitation.lean:161) is a weaker-constant wrapper of `_sharp` (scaffold). Pitfall: OK — RHS involves only a_j, card of supports and c₀: no m, C_pad, floor or dim of X_j (OpenAI/FilterExcitation.lean:206-214). Lean bounds a crossing term by d_i²·c₀ (product decomposition) instead of D2.10's q^{2v_R}J, same dependence **Step 1 partial:** D3.9.1 `AreaLaw.step_3_9_1` (AreaLawRefactored/S03_InitialBox/Filters.lean:133, KHK⁻¹φ = E₀φ so ⟨φ,(H−E₀)φ⟩ = ⟨φ,(H−KHK⁻¹)φ⟩), D3.9.4 `AreaLaw.step_3_9_4` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:528, paper route, C = 8/e², helper `cosh_sub_one_le` :508); D3.9 Output (1−|⟨Ω,φ⟩|² ≤ ⟨φ,(H−E₀)φ⟩/Δ) is `AreaLaw.gap_le` (MarginalTails.lean:625); D3.9.3 `AreaLaw.step_3_9_3` (AreaLawRefactored/S03_InitialBox/Filters.lean:342, Re⟨φ,(h−LhL⁻¹)φ⟩ = −Σ_{ik}(cosh log(l_i/l_k)−1) Re H_ik with H_ik = `pair` φ h i k = √(p_ip_k)⟨g_i,h_ik g_k⟩; helpers `re_sum_pairing` :307 (pairing (i,k) with (k,i)), `pair_sum` :331), D3.9.5 `AreaLaw.step_3_9_5` (:365, split term ≤ (16/e²)a²Σ_α‖c_α‖‖d_α‖ for h = Σ_α c_α⊗d_α Hermitian, Schmidt φ, clipping hypothesis of D3.8; uses `step_3_9_4` and `sum_add_mul_unitRow_le`, MarginalTails.lean:451, the row/column block of D3.1.6 now shared with `step_3_1_6` :478); D3.9.2 (split-index reduction/peeling on regions) and D3.9.6 (sum over supports) open |
| D3.10 | Step eq:initial-weight-range | no declaration states (i)-(iii): `have`s `hE`, `ha2`, `hu` inside `OpenAI.condEntropy_le_initialBuffer_of_constants` (OpenAI/BufferDiscount.lean:177); helpers: OpenAI/BufferDiscount.lean lines 114-168 (`harmonic_weight_le_half`:117, `harmonic_weight_ratio_le`:122, `le_tailRadius_of_le`:133, `bufferCrossConst`:152, `bufferBudgetConst`:157); final choice of C_pad is in `bufferDiscount_complex` (:482, counted in D3.4) | 60 | smeared | restate as a lemma "C_pad exists with (i)-(iii)"; inline the scalar helpers. Lean's route differs in constants: paper (i) Cℰ/Δ ≤ 1/4 (overlap ≥ 3/4); Lean E ≤ Δ/2 (overlap ≥ 1/2, error m·log 2 instead of C(m+1)ℰ), thresholds packaged as Z_min instead of C_pad. Pitfall: OK — uniform in r because 𝓑_j ≤ K'(r+d_j) is matched by a_j = 2/(Z(r+d_j)) (OpenAI/BufferDiscount.lean:344-392, `le_tailRadius_of_le`:133) **Step 1 done:** `AreaLaw.eq_initial_weight_range` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:600): an integer C_pad > D+1 (explicit, ⌈(2+D)e^{L₀}⌉+D+2) with (i) Cℰ/Δ ≤ ¼, (ii) a_j ≤ ½ (D3.6 last sentence), (iii) a_j/(1−a_j) ≤ [32√((1+J/Δ)𝓑_j)]⁻¹ for all r ≥ 1, 1 ≤ j ≤ m, with D3.9's C as parameter fixed before C_pad |
| D3.11 | Step eq:initial-norm-lower | `OpenAI.pow_sqrt_mul_chainOptimum_le` (OpenAI/FilterPrefix.lean:305, telescoped form √(1−E/Δ)^m N_m ≤ ∏x_k, multiplicative instead of −2log N form), `sqrt_mul_chainOptimum_succ_le`:246 (D3.11.2), `chainOptimum`:144 (prefix problems, D3.11.1), `norm_extendId_sq_le_exp`:370 and `OpenAI.norm_kronecker_one_apply_sq_le_exp` (OpenAI/FilterMoment.lean:191) (D3.11.3-4, Hölder + Lemma 3.1 at u=−a/(1−a)), `Matrix.PosSemidef.re_trace_mul_le` (OpenAI/TraceHolder.lean:151); helpers: OpenAI/FilterPrefix.lean, TraceHolder.lean (whole), OpenAI/FilterMoment.lean lines 1-229 | 859 | faithful | golf. Standard?: Schatten–Hölder for PSD matrices (TraceHolder.lean, 201 lines incl. simultaneous diagonalization of commuting Hermitian matrices, used by D3.8): replace-by: search pending (Mathlib has `LinearMap.IsSymmetric` joint eigenspaces but no matrix trace-Hölder found; Lean-QuantumInfo `HermitianMat.trace_rpow_conj_le` is a related, already-imported candidate). Pitfall: OK — prefix optima are separate problems (`chainOptimum` at each k, FilterPrefix.lean:144) and Lemma 3.1 is applied in Ω at the cut D_k ∣ U∖D_k (FilterPrefix.lean:370) **Step 1 partial:** D3.11.2 `AreaLaw.step_3_11_2` (AreaLawRefactored/S03_InitialBox/Filters.lean:152, s N_j ≤ ‖L_jΩ‖ ‖K_{<j}Ω‖ from the overlap), D3.11.3 `step_3_11_3` (:167, Schatten–Hölder with exponents 1/(1−a), 1/a, from `Matrix.PosSemidef.re_trace_mul_le`, AreaLawForMathlib/Analysis/Matrix/TraceHolder.lean:128) and on a region `step_3_11_3_region` (:194, ‖(L⊗1)Ω‖² ≤ (Tr ρ_{Ω,X}^{1/(1−a)})^{1−a}), D3.11.3–4 on a region `step_3_11_4_region` (:211, log ‖(L⊗1)Ω‖² ≤ −a S(X) + 1024eϑ𝓑a² from the Lemma 3.1 bound at u = −a/(1−a); helper `sum_rpow_eq_sum_exp` :177), D3.11.4 scalar `AreaLaw.step_3_11_4` (BufferDiscount.lean:674), D3.11.5 `step_3_11_5` (:698), helper `neg_two_mul_le_log_one_sub` (:688); open: D3.11.1 (prefix problems N_j, each prefix maximizer's overlap via D3.9–D3.10) |
| D3.12 | Step eq:initial-trial-norm | (a) `OpenAI.norm_le_of_forall_floor` (OpenAI/FilterZeroFloor.lean:67), `pow_sqrt_mul_norm_le_of_zero_floor`:108; (b) `OpenAI.norm_liftProd_trial_ge` (OpenAI/SchmidtPinning.lean:204) with `isFeasibleFilter_union_kronecker` (OpenAI/FilterOptimizer.lean:247, counted in D3.8); (c) `OpenAI.neg_sum_le_log_of_trial` (OpenAI/BufferDiscountCore.lean:207) via `exists_trial_filter`:79 (D3.12.6) and `OpenAI.sum_re_inner_log_le` (OpenAI/FilterPower.lean:415, D3.12.3-5, Mathlib three-lines); helpers: OpenAI/FilterPower.lean, FilterZeroFloor.lean, SchmidtPinning.lean (whole), OpenAI/BufferDiscountCore.lean lines 1-156 and 207-256 | 1084 | faithful | golf; specialise to ℂ. Standard?: three-lines is Mathlib (`HadamardThreeLines`, FilterPower.lean:408); unitary-commutation identity `chainPow_one_add`:314 specific. Pitfall: OK — pinned filters ∣u_i⟩⟨u_i∣⊗M_j are feasible only at floor 0 and hence (a) is separate (FilterZeroFloor.lean; FilterOptimizer `isFeasibleFilter_union_kronecker`) **Step 1 partial:** D3.12.4 `AreaLaw.step_3_12_4` (AreaLawRefactored/S03_InitialBox/Filters.lean:259, (U_mM_m)⋯(U_1M_1) = (U_m⋯U_1)∏(V_{j−1}*M_jV_{j−1}), ordered products `prodDesc` :253); open: D3.12.1 (zero-floor limit), D3.12.2 (Schmidt pinning), D3.12.3, D3.12.5 (vector three-lines, derivative at 0⁺), D3.12.6 (trial filters) |
| D3.13 | Step eq:initial-norm-upper | `OpenAI.neg_two_mul_log_le_entropy` (OpenAI/BufferDiscountCore.lean:257): −2 log B ≤ S(X) + Σ a_j S(T_j) (B an upper bound of all zero-floor chains); `OpenAI.sum_norm_sq_mul_regionEntropy_le` (:157, concavity, D3.13.2) with `Arealaw.sum_vonNeumann_sub_negMulLog_le` (OpenAI/RegionSSA.lean:198, mapped as infra); helpers: OpenAI/BufferDiscountCore.lean lines 157-206 and 257-361 | 155 | faithful | keep. Standard?: concavity of entropy: library tree (RegionSSA.lean:198-246 is the project's own proof; Mathlib/Physlib replacement: search pending). Pitfall: n/a **Step 1 partial:** D3.13 `AreaLaw.step_3_13` (AreaLawRefactored/S03_InitialBox/Filters.lean:286, Schmidt averaging: from the per-i bounds D3.13.1 and the concavity inequalities D3.13.2 as hypotheses); open: D3.13.2 on regions (∑ p_i S_{w_i}(T_j) ≤ S(T_j) for the Schmidt decomposition of Ω at X ∣ X^c; concavity available as `MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight`, AreaLawForMathlib/QuantumInfo/Entropy/ClassicalQuantum.lean:190) |
| D3.14 | Step (conclusion of Lemma 3.2) | `OpenAI.two_mul_condEntropy_le` (OpenAI/BufferDiscountCore.lean:447): 2S(X∣T) ≤ S(X) + error; `OpenAI.sum_mul_condEntropy_le`:362 (D3.14.1-2, combines D3.11-D3.13); SSA via `Arealaw.SubState.regionEntropy_union_sub_le_of_subset` (OpenAI/RegionSSA.lean:163, infra); the final O(r) bound (D3.14.5) is in `condEntropy_le_initialBuffer_of_constants` (OpenAI/BufferDiscount.lean:393-435, counted in D3.5); helpers: OpenAI/BufferDiscountCore.lean lines 362-480 | 119 | faithful | keep. Standard?: SSA (Lieb–Ruskai): D2.2 item 2, library tree. Pitfall: OK — Σ a_j = 2 (`hmass`) gives the factor ½ (OpenAI/BufferDiscountCore.lean:447-480) **Step 1 done:** D3.14.1–D3.14.4 `AreaLaw.step_3_14` (AreaLawRefactored/S03_InitialBox/BufferDiscount.lean:744), SSA helper `condEntropy_anti` (:733); D3.14.5 `step_3_14_5` (:769, error C(m+1)ℰ ≤ C_buf r with C_buf = C(C_pad/D+1)·2D/log((C_pad+1)/(2+D))) |
| D3.15 | Def F_box(r) | `OpenAI.boxEntropy` (OpenAI/BoxEntropy.lean:87) = sSup of `OpenAI.boxEntropyValues`:74; `boxEntropy_mono`:129, `boxEntropy_nonneg`:108, `boxEntropy_le_sq_mul_log`:112, `regionEntropy_le_boxEntropy`:117; helpers: OpenAI/BoxEntropy.lean (whole) | 62 | faithful | keep. Pitfall: OK — sup ranges over all D₀>2R+10, Λ, Φ, Ω, A, Q (uniform over instances), OpenAI/BoxEntropy.lean:74-87; D₀ is also swept (paper fixes D₀) **Step 1 done:** `AreaLaw.F_box` (AreaLawRefactored/S03_InitialBox.lean:165, over ℂ, sup also over D₀ > 2R+10), `le_F_box`, `F_box_nonneg`, `F_box_mono`, `le_of_mem_boxEntropies` |
| D3.16 | Proposition 3.3 (prop:initial-box) | `OpenAI.InitialBoxEstimate` (OpenAI/Statements.lean:539, frozen); `OpenAI.initial_box_estimate` (OpenAI/InitialBoxEstimate.lean:355) = `initial_box_estimate_of_bufferDiscount`:294 (D3.16.5-8) ∘ `boxEntropy_le_of_scale`:250 (recursion, D3.16.4) ∘ `regionEntropy_inter_le_of_children`:74 (D3.16.1-3); helpers: OpenAI/InitialBoxEstimate.lean, SafeBoxChildren.lean (children, D3.16.1; `IsSafe.rectChild`:231), RotatedChainRule.lean (chain rule over rotations), ChildColoring.lean (whole files), OpenAI/HarmonicWeights.lean lines 173-256 (`exists_le_mul_rpow_of_scale_recurrence`:194, `one_lt_log_div_log_lt_two`:245 = D3.16.6-8) | 967 | drift | restate; paper: uniform random order of the ≤M² children, Pr(E_i) ≥ p₀=(2C_pad+5)^−2, ≥16(C_pad+2) ≤ M, λ=(1−p₀/4)M², noninterior ≤ 4(C_pad+2)M; Lean: deterministic colouring of chunk positions mod P=2C_pad+1 (N=P² colours) and averaging the chain rule over the N cyclic colour rotations, p=1/(2N), M=8(C_pad+1), λ=(1−p/2)M², noninterior ≤ 2(2C_pad+1)M. Pitfall: OK — M fixed after C_pad (`M = 8(Cpad+1)`, OpenAI/InitialBoxEstimate.lean:300), exponent e₀=log λ/log M −1 depends on M and only e₀<1 is claimed (:344), discount used only for interior children, children safe w.r.t. same A (`IsSafe.rectChild`, SafeBoxChildren.lean:231) and F_box a sup over instances (`boxEntropy_le_of_scale`, :250). 𝕜-generic natively **Step 1 done modulo D3.4:** `AreaLaw.prop_3_3 (lemma_3_2 : BufferDiscount ℂ q R J Δ) : InitialBoxEstimate ℂ q R J Δ` (AreaLawRefactored/S03_InitialBox.lean:592); paper route: uniform random order (`step_3_16_4` :351, `step_3_16_3_chain`, `step_3_16_3_count`), parent recursion `step_3_16_3` (:449), children `child`/`nChunks₁`/`nChunks₂`, p₀=(2C_pad+5)⁻² (`p₀` :269), B_M=4(C_pad+2)M (`B_M` :272), M=16(C_pad+2), λ=(1−p₀/4)M², `step_3_16_6`, `step_3_16_8` (:223) |
| D3.17 | Step (remarks closing §3) | — | 0 | none | cut (no declaration expected). Pitfall: n/a (no declaration) **Step 1:** none (no declaration expected) |
| (section infra) | — | OpenAI/RegionLift.lean (whole: `extendId`/`ptrace` expectation algebra, descending trace argument `inner_toEuclideanLin_extendId_conj`:240, `crossingTerms`:102; shared with §5/§9/§10), OpenAI/RegionSSA.lean (whole: SSA `regionEntropy_strong_subadditivity`:108, conditional-entropy monotonicity, concavity; D2.2 item 2, also claimable by §2) | 314 | none | library tree (RegionSSA, standard); RegionLift: golf with the filter files; **Step 1:** `Arealaw.extendId_mul`, `Arealaw.dotProduct_extendId_mulVec` (⟨φ,(A⊗1)φ⟩ = Tr(ρ_{φ,S}A)) in AreaLawForMathlib/QuantumInfo/Region.lean:321, :327 |

## 04-quasilocal.md

Lines now (section total): 8021

All files are under `OpenAI/`. Unless noted everything is over `ℂ` (matrices `Matrix _ _ ℂ`, `EuclideanSpace ℂ _`); the only 𝕜-generic items are the frozen defs in `Statements.lean` (`condExpect`, `PositiveReplacement`) and the transfer `ComplexWitnessTransfer.lean`. Split files are attributed by line range. "Standard" searches: atlas semantic search over Mathlib found no operator Hölder-1/2, no Weyl/min-max perturbation, no Lieb–Robinson, no Gevrey-bump Fourier decay (only `CFC.sqrt_le_sqrt`, eigenvalue sorting, `HasCompactSupport.hasTemperateGrowth`).

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D4.1 | Def (anchored decomposition, graph balls) | `OpenAI.graphNbhd` (OpenAI/Statements.lean:119), `graphNbhd_subset` (:122), `domainComponent` (:126), `domainComponent_subset` (:129); helpers: OpenAI/LiebRobinson/GraphBallStabilization.lean (whole file; ball = component for large radius, used only by §10 `Amplification/ComponentChannelOscillation`) | 89 | faithful (ball `N_l(a)` is `graphNbhd Λ {a} l`, graph metric `domainEDist`; frozen, 𝕜-free) | keep (Statements part frozen); GraphBallStabilization: move to §10 row or cut if §10 does not need it |
| D4.2 | Def (conditional expectation `E_{i,l}`; Standard) | `OpenAI.condExpect` (OpenAI/Statements.lean:240, normalized `ptrace` then `extendId`, 𝕜-generic, built on Arealaw `ptrace`/`extendId`); API+norm: OpenAI/ConditionalExpectation.lean (whole file; positivity, unital, support, `norm_condExpect_le` :193 and `norm_sub_condExpect_le_of_forall_commutator` :206 are ℂ-only; `condExpect_map_toComplex` :142 is a 𝕜→ℂ bridge); OpenAI/ComplementaryWeylTwirl.lean (whole file) | 540 | drift — paper: `E = ∏_y T_y`, product of single-site Haar twirls, contractivity from each `T_y`; Lean: one Weyl-clock/shift twirl over the whole complement `T∖S` (`condExpect_submatrix_glueEquiv_eq_complementaryWeylTwirl` :170), contractivity `Matrix.norm_complementaryWeylTwirl_le`; the telescoping D4.4.9 is replaced by the `∀ B supported on T∖S, ‖[A,B]‖ ≤ ε ⇒ ‖A−E A‖ ≤ ε` lemma (:206). No site-wise `T_y` exists | replace-by library tree (normalized partial trace + `condExpect` as complementary twirl); Mathlib has no partial trace (search pending beyond atlas semantic hits); golf ComplementaryWeylTwirl (288 lines) |
| D4.3 | Step (counting budget) | Clauses are separate: `b₀` bound `OpenAI.IsAdmissible.sum_norm_extendId_containing_le` (OpenAI/SupportCounting.lean:136; bound `2^((2R+1)^2) J`); anchor multiplicity `OpenAI.card_anchor_fiber_le` (OpenAI/FiniteSetTruncation.lean:82; bound `2^((2R+1)^2)`); ball bounds `card_graphNbhd_singleton_le` (:66), `card_graphNbhd_singleton_le_four` (:72, `4(d+1)^2`), `mem_graphNbhd_singleton_iff` (:48), `graphNbhd_singleton_subset_Icc` (:53); `\|X_i\| ≤ v_R` is `OpenAI.card_le_of_mem_supports` (SupportCounting.lean:81, claimed by the §2 map, not here). Second, paper-exact encoding (box replaced by diamond `v_R=1+2R(R+1)`, `μ_R=2^(v_R-1)`): `OpenAI.card_anchor_fiber_le_diamond` (OpenAI/LatticeCounts.lean:68), OpenAI/GraphInteractionDiamondCounting.lean (whole file, outside the import closure of `OpenAI.AreaLaw`) | 79 | smeared (three clauses in three declarations, none states `b₀ , | X_i\| ≤ v_R , μ_R` together) and drift in constants (paper `v_R, μ_R` diamond counts; live Lean uses sup-norm box `(2R+1)^2`, two encodings of the same count; the diamond one is live only in §9/§10 via LatticeCounts) \| restate: one declaration with `v_R, μ_R, b₀=Jμ_R`; delete box variants and `GraphInteractionDiamondCounting.lean` (dead) once the diamond count is the only one. Pitfall: n/a (no quantifier-order claim) |
| D4.4 | Lemma 4.1 | `eq:quasilocal-lr`: `OpenAI.LiebRobinson.norm_heisenberg_commutator_le_graphDistance` (OpenAI/LiebRobinson/GraphPropagation.lean:262; abstract finite graph `G : SimpleGraph ι`, abstract family `X k, h k`, `S k` support submodules, ℂ; constants `C=2e^{μR}`, `v=2v_R b₀ e^{2μR}`, `μ ≥ 0` free; plus set-version `…_graphDistance_finset` :302). `eq:quasilocal-lr-ce`: `OpenAI.LiebRobinson.norm_heisenberg_sub_condExpect_graphNbhd_le` (OpenAI/LiebRobinson/HamiltonianLocalization.lean:95; square-lattice only, `c = 1` fixed, `localizationVelocity R J = 2(2R+1)^2·2^{(2R+1)^2}J e^{2R}`, box counts). Helpers: OpenAI/LiebRobinson/CommutatorRecursion.lean (D4.4.2–3 ODE/Duhamel), OpenAI/LiebRobinson/Volterra.lean (Gronwall/Volterra bound replacing D4.4.5), HamiltonianLocalization.lean :31–94 (support-in-domain scaffolding) | 1460 | drift — paper: iterate recursion `m` times, simplex volume `t^m/m!`, chain sum, `1_{d≤(m+1)R}≤e^{μ((m+1)R−d)}` (D4.4.5–7), then twirl telescoping `B−T_1…T_nB=Σ T_1…T_{k-1}(B−T_kB)` and sum over sites at distance `d>l` with `Σ 3(d+1)²e^{−cd}` (D4.4.9–10); Lean: finite Volterra inequality (`finite_volterra_le_weight_mul_exp`) with `Σ_{j meeting X}‖h_j‖ ≤ | X\|b₀`, and for the ball version a single bound `‖A−E A‖ ≤ sup_{B on complement, ‖B‖≤1}‖[A,B]‖` applied with `Y = Λ∖N_l(a)` as one set (`…_graphDistance_finset`, no site sum, no `(d+1)²`). The statement is also split: line 1 (generic) and line 2 (lattice, `c=1`) live in different files and neither states both. Infinite distance: covered by `n ≤ edist` (ℕ∞), not a separate clause. Pitfall: OK — `μ` free and `v` an explicit function of it (GraphPropagation.lean:262); lattice version fixes `c=1` first and exposes `v` (HamiltonianLocalization.lean:77), which is what `exists_norm_filterIntegral_sub_map_le` (FilterLocality.lean:212) consumes as `(C,v,c)` simultaneously \| restate as one `lemma_4_1` (graph-generic, both lines, `C,v,c` per paper) and re-prove along D4.4.5–6 or keep Volterra and drop chain sum explicitly; golf (1460 lines for a standard Lieb–Robinson); library tree (Standard: Nachtergaele–Ogata–Sims; no Mathlib/Physlib Lieb–Robinson found in atlas search, search pending for Physlib) |
| D4.5 | Lemma 4.2 (Standard) | `OpenAI.SpectralFilter.quasilocal_filter` (OpenAI/SpectralFilter/Inversion.lean:90; χ smooth, compact support, `χ(0)=1`, even, `f` even, `χ=∫f e^{itω}`, `\|f(t)\|≤Ce^{-c\|t\|^α}`); `spectralCutoff` (Cutoff.lean:201), `spectralKernel` (Kernel.lean:91). Helpers (whole files): OpenAI/SpectralFilter/Profile.lean (Cauchy estimates, D4.5.2–3), Cutoff.lean (smoothness, Gevrey `abs_iteratedDeriv_spectralCutoff_le` :286, D4.5.4–6), Kernel.lean (integration by parts, D4.5.7), Decay.lean (choice of `m`, D4.5.8), Inversion.lean (D4.5.9) | 1108 | faithful (one declaration states the anchor; file order matches D4.5.1–9; real-valued `χ,f`, no 𝕜) Pitfall: OK — `∃ C c` after `p δ` only, Inversion.lean:90 | library tree (Gevrey bump + stretched-exponential Fourier decay; no Mathlib analogue found); golf (1108 lines) |
| D4.6 | Proposition 4.3 | Frozen statement `OpenAI.PositiveReplacement` (OpenAI/Statements.lean:259); 𝕜-generic proof `OpenAI.positive_replacement` (OpenAI/PositiveReplacement.lean:16) ← `OpenAI.positiveReplacement_of_complex` (OpenAI/ComplexWitnessTransfer.lean:215, entrywise real-part projection `Matrix.realProjection`, whole file) ← `OpenAI.positive_replacement_complex` (OpenAI/PositiveConstraints.lean:145) ← `SpectralFilter.positive_replacement` (OpenAI/SpectralFilter/PositiveReplacement.lean:313; abstract `Matrix n n ℂ`, `k=\|M\|/c_*`). Second statement of the same anchor, the one used downstream: `OpenAI.exists_latticePositiveConstraints` (OpenAI/LatticeConstraints.lean:126; ℂ, `EuclideanSpace`, explicit `k` via `positiveConstraint`, `α=kernelExponent p`, also states `Σk ≥ g(I−P)` directly). Helpers: SpectralFilter/PositiveReplacement.lean :260–354, SpectralFilter/FilterLocality.lean :257–348 (`norm_abs_sub_map_abs_le` :257, `exists_norm_positiveConstraint_sub_map_le` :285 = D4.6.6–7 for an abstract localizing map `L`), PositiveConstraints.lean (whole: `positiveConstraint_isSupportedOn_domainComponent` :58 = D4.6.9, `Commute.cfcAbs_of_isHermitian`, `commute_filterIntegral_of_forall_commute`), OpenAI/LiebRobinson/ComponentLocality.lean (whole, D4.6.9), LatticeConstraints.lean :114–211 | 1035 | drift — two routes: paper: ℂ throughout, one statement; Lean: (a) frozen 𝕜-statement obtained from the ℂ statement by a per-statement real-projection transfer (365 lines, `positive_replacement`/`ComplexWitnessTransfer` are outside the import closure of `OpenAI.AreaLaw`); (b) the live path uses a re-stated ℂ-only lattice theorem `exists_latticePositiveConstraints` with `∃ C c` before `∀ q`. Proof steps D4.6.1–4 and D4.6.6–7 follow the digest (`k= | M\|/c_*`, `‖\|M\|−\|E M\|‖` via D4.9, `E\|E M\|=\|E M\|`), D4.6.5 (uniqueness) is not stated (only the three order inequalities). Pitfall: OK — `∃ cstar C c` after `(q R J Δ p)` and before `Λ, Φ, Ω, anchor`; `k` is chosen after anchors; `cstar = positiveNormalization p (Δ/2) J` depends on `p` only through `‖f‖₁`, Statements.lean:259 \| merge `exists_latticePositiveConstraints` into the frozen statement (prove `PositiveReplacement ℂ`, derive lattice form), delete `positive_replacement`/transfer once the single ℂ→𝕜 transfer at the top exists; restate; cut ComplexWitnessTransfer (piecewise transfer) |
| D4.7 | Step (centered filtered terms `M_i`) | `SpectralFilter.centeredFilter` (OpenAI/SpectralFilter/PositiveReplacement.lean:203), `isHermitian_centeredFilter` (:208), `centeredFilter_mulVec_eq_zero` (:219), `sum_centeredFilter` (:233), `norm_centeredFilter_le` (:245); integral `SpectralFilter.filterIntegral` (OpenAI/SpectralFilter/MatrixFilter.lean:122); gap/eigenbasis step `filterIntegral_mulVec_of_gap` (MatrixFilter.lean:268), `filterIntegral_mulVec_of_posSemidef_gap` (PositiveReplacement.lean:110); helpers: MatrixFilter.lean (whole), PositiveReplacement.lean :1–259 (`filterL1` etc.) | 571 | smeared (the five properties are four separate lemmas; none states them together) | restate as one `step_4_7`; `hermitianUnitaryPath`/`filterIntegral` is a second encoding of `τ_t` next to `LiebRobinson.heisenbergEvolution` (see notes); golf |
| D4.8 | Step (locality of `M_i`) | `SpectralFilter.exists_norm_filterIntegral_sub_map_le` (OpenAI/SpectralFilter/FilterLocality.lean:212), explicit two-term form `…_le'` (:134); helpers FilterLocality.lean :1–256 (`kernelExponent` :51, `abs_spectralKernel_le_tail` :64, `neg_mul_le_sub_mul_rpow` :113) | 256 | overbuilt — states it for an arbitrary linear localizing map `L` with the hypothesis `‖τ_t(h)−L τ_t(h)‖ ≤ ‖h‖min{2,Ce^{v | t\|−cl}}` and real `l`, over any `Matrix n n ℂ`, where the paper only uses `L=E_{i,l}`, `l∈ℕ`; also route drift in D4.8.3: tail bounded by `K₀(1+\|t\|)^{-2}e^{-(c/2)T^α}` (integrable), not the incomplete-gamma integral. Pitfall: OK — rate `l^α` with `c₂ = min(c/2, cf/2·(c/(2v))^α)`, depends only on `p,δ,C,v,c`, FilterLocality.lean:212 \| inline into D4.6 or restate with `L := condExpect`; golf |
| D4.9 | Step (operator Hölder-1/2; Standard) | `CFC.norm_sqrt_sub_sqrt_le` (OpenAI/SqrtHolder.lean:154; any unital C⋆-algebra `A`, `0≤a,b`); helpers `CFC.sqrt_add_algebraMap_le` (:121), `CFC.sqrt_le_sqrt_add_sqrt_norm_sub` (:144), and for D4.6.6 `CFC.norm_abs_sub_abs_le` (:176, ≈28 lines); scaffolding `CFC.norm_posPart_mono`, `norm_le_max_of_le_of_le` … | 193 | drift — paper: resolvent-integral representation and monotonicity (D4.9.1–2); Lean: Mathlib `CFC.sqrt_le_sqrt` for monotonicity, then D4.9.3–4 as in the digest (`√(b+ε) ≤ √b+√ε`, swap, norm from two-sided scalar bound). Generality: C⋆-algebra rather than matrices (harmless). Pitfall: OK — no dimension factor, SqrtHolder.lean:154 | replace-by `CFC.sqrt_le_sqrt` for D4.9.1–2 (already) ; the Hölder estimate itself is not in Mathlib (search pending beyond atlas semantic) — library tree; golf |
| D4.10 | Lemma 4.4 | Statement-form: `OpenAI.quasilocal_roots` (OpenAI/QuasilocalRoots.lean:45; ℂ; bound `4√ε` via `ε:=‖k−E k‖`, cb-norm as `⊗ₖ 1_κ` for all `κ`; outside the import closure — only `Audit.lean` imports it). Live pieces: `Matrix.rootChannel` (OpenAI/RootChannel.lean:69) with `norm_rootChannel_kronecker_le` (:95), `norm_rootChannel_kronecker_sub_le` (:149), `rootChannel_sqrt_eq_self_of_commute` (:200), `sqrt_one_sub_mulVec_eq_self` (:194); spectator form `OpenAI.spectatorRootChannel` (OpenAI/Amplification/LocalRootChannels.lean:61), `localRootChannel` (:111), `norm_spectatorRootChannel_sub_localRootChannel_le` (:134), `localRootChannel_eq_self_of_forall_commute` (:152, commutant form); `IsSupportedOn.cfcSqrt` (OpenAI/SiteExpectationOrder.lean:54). Whole files: QuasilocalRoots.lean, RootChannel.lean, SiteExpectationOrder.lean; LocalRootChannels.lean :1–234 (shells :235–297 are §10 `eq 10.7`, not counted) | 637 | smeared — the declaration that states the lemma (`quasilocal_roots`) is dead and weaker (fixed-point only for operators supported outside the ball `T∖S`, not the commutant); the live code states the pieces separately over `Aux` spectator instead of `⊗ 1_κ` (two encodings of the same channel: `Matrix.rootChannel (G ⊗ₖ 1)` vs `spectatorRootChannel`). Proof follows D4.10.1–7 (root monotone, `V:v↦Gv⊕Kv` replaced by Kraus-contraction lemma `norm_sum_conjTranspose_mul_mul_le`, perturbation `(‖A‖+‖A'‖)‖A−A'‖`). Pitfall: VIOLATED in `quasilocal_roots` — fixed-point clause only for `IsSupportedOn (T∖S) B` (QuasilocalRoots.lean:68), not the commutant; OK in the live `localRootChannel_eq_self_of_forall_commute` (LocalRootChannels.lean:152) | restate (one `lemma_4_4`, commutant fixed-point, cb-norm as `∀ κ` or `Aux`) and re-point §10 to it; merge `spectatorRootChannel` into one encoding; cut `quasilocal_roots` if not re-pointed |
| D4.11 | Proposition 4.5 | No single declaration. Ground-state part: `OpenAI.exists_latticeFiniteSetTruncation` (OpenAI/LatticeConstraints.lean:226; ℂ, `p=1`, `∃ C₁` after `C₀`, before `q Λ Φ Ω n S₀`); assembly `OpenAI.exists_finiteSetTruncation` (OpenAI/FiniteSetTruncationGap.lean:41, abstract family `k`), `truncatedConstraint_mem_Icc` (:28) = D4.11.1; defs `OpenAI.setDist` (OpenAI/FiniteSetTruncation.lean:28), `truncationRadius` (:100), `truncatedConstraint` (:103); crossing/cut clause is in D4.14. Dead second statement: `OpenAI.exists_finiteSetTruncation_of_gap` (OpenAI/FiniteSetTruncationOfGap.lean:27, outside closure, ∃ anchors, ℂ; imports 𝕜-version `positive_replacement`). Whole files: FiniteSetTruncationGap.lean, FiniteSetTruncationOfGap.lean; LatticeConstraints.lean :1–81 (header, imports) and :212–283; FiniteSetTruncation.lean :28–47, :100–110 | 354 | smeared — Prop 4.5 as stated in the paper is three declarations (`exists_latticeFiniteSetTruncation`, `exists_latticeCrossingBudget`, `exists_latticeCutBudget_le_log`), and a fourth dead variant; ground-state clause says `HasGlobalGap Ht Ω₀ e (g/2)` and gives `Ω₀`, phase `θ`, trace distance (uniqueness version `…_eigenspace_eq_span` omitted). `S₀` nonempty not needed (matches D4.15 ii). Pitfall: OK — order `C₀` first, then `C₁` (`∃ C₁ ∀ {q}…`, depends on `R,J,Δ,C₀` only, even independent of `q`), then `n`, `S₀`, LatticeConstraints.lean:226–236 | merge the three lattice statements into one `prop_4_5`; cut `exists_finiteSetTruncation_of_gap` (dead duplicate); the abstract `exists_finiteSetTruncation` can be inlined |
| D4.12 | Step (volume-free summation) | `OpenAI.norm_sum_truncatedConstraint_sub_le` (OpenAI/FiniteSetTruncation.lean:154; abstract `Kb μ A` and series hypothesis `hA`); `OpenAI.card_label_shell_le` (:111) = D4.12.2; `OpenAI.exists_sum_shell_le` (OpenAI/TruncationSeries.lean:67) = series bound D4.12.4–6, `exists_one_add_pow_mul_exp_neg_rpow_le` (:23); `OpenAI.exists_truncationConstant` (OpenAI/TruncationRadius.lean:31) = D4.12.7; helper `half_le_two_rpow`. Whole files TruncationSeries.lean, TruncationRadius.lean; FiniteSetTruncation.lean :1–27, :111–217 | 355 | smeared (error sum, series estimate and numerics for `C₁` are three declarations, each with free abstract constants) and drift in D4.12.4–6: paper bounds tail by `∫(x+1)²e^{−c(x/3)^α}` (incomplete gamma); Lean sums `(d+1)²e^{-c·max(r₀,⌊d/2⌋)^α} ≤ A e^{-(c/2)r₀^α}` using `Σ1/(d+1)²` and `(u+1)^k e^{-bu^α} ≤ M`. Pitfall: OK — `A` is chosen before `r₀`, `N` (TruncationSeries.lean:67) and `C₁` after `B,C₀,c,g` with `ε_n ≤ g/4` built in (TruncationRadius.lean:31) | restate as one `step_4_12`; golf |
| D4.13 | Step (ground energy, gap, ground vector of `H̃`) | `Matrix.exists_posSemidef_gap_of_norm_sub_le` (OpenAI/GapPerturbation.lean:272; `e∈[0,ε]`, gap `g/2`, `∃θ ‖Ω₀−e^{iθ}Ω‖≤2√(ε/g)`, `½‖\|Ω₀⟩⟨Ω₀\|−P‖₁ ≤ √(2ε/g)`), operator form `exists_gap_of_norm_sub_le` (:131); helpers whole files GapPerturbation.lean, PhaseError.lean (minimizing phase) | 419 | drift — paper: Weyl/min–max `λ₂(H̃) ≥ λ₂(H_F)−ε`, then phase `⟨Ω,Ω̃⟩≥0` (D4.13.2–6); Lean: Rayleigh–Ritz — take a unit eigenvector minimizing `Re⟨ψ,Bψ⟩` (`exists_unit_eigenvector_re_inner_le`), express the gap as a quadratic-form inequality `g(‖ψ‖²− | ⟨Ω,ψ⟩\|²) ≤ Re⟨ψ,Aψ⟩`, minimizing phase `θ` instead of a sign convention; no eigenvalue ordering. Same conclusions. ℂ only; relies on `PureStateTraceDistance`, `SchmidtTilt` (not mapped here) \| keep statement; replace-by Weyl/min–max if a Mathlib/Physlib `λ₂` perturbation lemma appears (none found, search pending); golf |
| D4.14 | Step (crossing supports and cut budget) | `OpenAI.exists_latticeCrossingBudget` (OpenAI/LatticeConstraints.lean:284; radius clause, `\|C_X\| ≤ C b_X (r₀+1)²`, `log d_i ≤ C(r₀+1)²`, `ℬ_X ≤ C(1+b_X)(r₀+1)⁶`), `OpenAI.exists_latticeCutBudget_le_log` (:326, D4.14.7, `≤ C n D (log n)¹²`); core `OpenAI.truncationRadius_eq_of_mem_crossingLabels` (OpenAI/CrossingBudget.lean:50) = D4.14.1–2, `card_crossingLabels_le` (:88) = D4.14.3–4 (walk to a crossing edge, `cutEndpoints`), `log_dim_le_of_mem_crossingLabels` (:180), `cutBudget_le` (:198), `le_of_cutBudget_le` (:270); defs `designatedSupport`, `crossingLabels`, `cutBudget`. Whole CrossingBudget.lean; LatticeConstraints.lean :82–113 (`cutBudget_eq_cutLogBudget`, `cutBudget_sdiff`) and :284–338 | 491 | faithful (proof follows D4.14.1–7; only the ball/multiplicity constants differ: `Kb=4`, `μ=2^{(2R+1)^2}` box instead of `3(d+1)²`, `μ_R`). Pitfall: OK — `∃ C` depends on `q,R` only and is chosen before `Λ,a,S₀,r₀,X`; only `X ⊆ S₀` covered, `b_X = (edgeBoundary Λ X).card` of the induced graph, LatticeConstraints.lean:284 | keep; re-point to diamond constants from D4.3; `cutBudget_eq_cutLogBudget`/`cutBudget_sdiff` (:82, :97) are scaffolding, cut if unused |
| D4.15 | Step (remarks, degenerate cases) | — (no declaration; (ii) `S₀=∅` is covered because `exists_latticeFiniteSetTruncation` does not assume `S₀` nonempty, (iv) exponent 1000 is hard-wired at `n^(-1000)` in `ε`) | 0 | none | keep (no declaration expected) |
| (section infra) | — | OpenAI/GraphInteractionBudget.lean (whole file: abstract support-family counting, `interactionChainWeightSum`; imported by `BufferedRectangles` (§11) and the dead diamond file, shared with §2/§11) | 106 | — | move to the §2/§11 map or keep in library tree |
| (section infra, reverse pass) | — | (whole file, 11 decls) (OpenAI/SiteWeylAverage.lean:49-269) | 328 | — | inline into S04 quasilocal Weyl twirl / S10 anchor (ported from TNLean; paper-anchored: digest mentions oscillation/spectator/twirl); owner anchor to be assigned |

## 05-conditional.md

Lines now (section total): 15729

All code is over `ℂ` only (no `[RCLike 𝕜]` anywhere in this section's files; any ℂ→𝕜 transfer lives elsewhere). Constants: the paper's "universal c, C" appear as explicit numerals (`200000`, `1/8`, `skewConst`, ...) inside ∃ or `def`.

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D5.1 | Def (spectral powers, hat, norms; F1, F2) | no single def. Four encodings of ρ^[z] / ρ̂^{iu}: `ConditionalMovement.SupportedCurve.power` (OpenAI/ConditionalMovement/SpectralPowers.lean:69), `Matrix.kernelCompletion` (OpenAI/KernelCompletion.lean:50), `Matrix.hatPhase` (OpenAI/MarginalPhaseSupport.lean:24; whole file: kerProj/suppProj/sqrtSpec), `Entropy.ConditionalSkew.suppPowFun` (OpenAI/ConditionalSkewSetup.lean:33) and `Entropy.ConditionalSkew.hatFun` (OpenAI/ConditionalSkewPhaseCore.lean:25–87). F1 (‖Tθ‖=‖T√ρ‖₂) is `Entropy.MarginalPhase.norm_kronecker_one_mulVec` (MarginalPhaseSingular.lean:448, counted in D5.12); F2 (Schmidt mirroring) is `Entropy.ConditionalSkew.imag_vector_eq` (ConditionalSkewGeometry.lean:105, counted in D5.17) | 559 | smeared | merge (one `ρ^[z]` / `ρ̂^{iu}` pair in the library tree, via Mathlib `CFC.rpow`/`cfc`; the brackets-vs-hats split of the digest Pitfall is then one definition). Pitfall: OK — brackets (`suppPowFun`, `SupportedCurve.power`) are used for the entire function f of Lemma 5.3 and hats (`hatPhase`, `hatFun`) for the unitary phases of Lemmas 5.1/5.2, ConditionalSkewSetup.lean:33, MarginalPhaseSupport.lean:24. Standard?: notation → library tree |
| D5.2 | Step eq:conditional-log-moments (three moments of L) | no declaration states it. Pieces: E e^{L} ≤ d as `ConditionalMovement.ConditionalCollision.collision_le` (ConditionalCollision.lean:71), density `density`/`density_pos`/`density_marginal` (ConditionalCollision.lean:130–144); E L = −S(x\|U) as `...ConditionalCollision.spectral_mean_eq_neg_entropy` (FilterEntropy.lean:144) with `spectral_marginal` (:94), `spectral_support` (:119); E e^{−L} ≤ d enters as hypothesis `htr : Σ r ≤ D` of `RelativeLogMoment.spectral_mgf` (LogMoments.lean:210). Domination ρ ≤ d(I⊗ρ_U) (D5.2.1) is not stated: collision_le proves the entrywise Cauchy–Schwarz form Σ‖ρ_{xp,yq}‖²/r_q ≤ d Σ r directly. Files OpenAI/ConditionalMovement/ConditionalCollision.lean (lines 1–144), FilterEntropy.lean (lines 94–180) | 231 | smeared | restate (one lemma: three moments of L over the statement encoding; ρ ≤ d(I_x⊗ρ_U) as its own library lemma — search pending for Mathlib/Physlib `PosSemidef` partial-trace domination). Pitfall: n/a (no quantifier-order hazard; constants free of dim U: OK, d = card X only, collision_le :71) |
| D5.3 | Step eq:conditional-log-mgf | `ConditionalMovement.ConditionalCollision.conditional_spectral_mgf` (ConditionalCollision.lean:145), `ConditionalMovement.RelativeLogMoment.spectral_mgf` (LogMoments.lean:210), `...tilted_second_moment` (LogMoments.lean:118); whole file LogMoments.lean (also `square_le_cutoff`, `second_moment`, `exp_linear_remainder`, `mgf_bound`) | 378 | drift (paper: Markov tails Pr(\|L\|>v) ≤ 2d e^{−v}, then layer-cake integration of s²e^{\|b\|s}, then Taylor; Lean: no tail statement, `tilted_second_moment` takes the two exponential-moment hypotheses ΣwE e^{±z} ≤ e^l and cuts off at a threshold (`square_le_cutoff`); only b ≥ 0 treated, explicit constant 3b²(16e ℓ²+32)) | golf (tails step is missing from Lean; either add D5.3.1 as a lemma or fold; keep b ≥ 0 only). Pitfall: OK — hypothesis is `b * log D ≤ 1` with `b ≤ 1/2` (so \|b\|ℓ-type, not \|b\|≤c), ConditionalCollision.lean:145, LogMoments.lean:210 |
| D5.4 | Step eq:conditional-schatten (Schatten estimate) | `ConditionalMovement.ConditionalCollision.one_filter_entropy_bound` (FilterEntropy.lean:181), `...petz_diagonal_mgf` (FilterEntropy.lean:42), `ConditionalMovement.MatrixInterpolation.trace_power_gram_le` (EntropyHolder.lean:192), `one_filter_petz_bound` (EntropyHolder.lean:237), `...ConditionalCollision.one_filter_purification_bound` (Purification.lean:223); files EntropyHolder.lean (whole), FilterEntropy.lean (lines 1–93, 181–235), Purification.lean (lines 223–252) | 446 | drift (paper: analytic family T(z)=ρ^{[z/2]}Q^{−az}, Stein interpolation between L^∞ and L² to get Z=‖K‖_r, then Hölder with τ_u in D5.6.2; Lean: no ‖K‖_r and no interpolation. Bounds Tr(S^β AA*) for arbitrary S directly by Hölder on eigenvalue sums (`trace_power_gram_le`) and Petz's diagonal identity `petz_diagonal_mgf` + D5.3 with b=β/(1−β), β=2a) | restate (Schatten step as Hölder-on-Gram, i.e. keep Lean's route, then D5.4+D5.6.2 become one statement `Tr τ^{2a}K ≤ e^{…}`); Hölder on eigenvalue sums: replace-by `Real.inner_le_Lp_mul_Lq_of_nonneg` (already used, EntropyHolder.lean). Pitfall: OK — a<1/4 appears as β=2a ≤ 1/4 (`hβfourth`) in the interpolation and β ≤ 1/3 here; 2a≤1/2 as b ≤ 1/2, FilterEntropy.lean:181 |
| D5.5 | Lemma 5.1 (conditional movement estimate) | `Entropy.conditionalMovement_norm_le` (OpenAI/ConditionalMovementEstimate.lean:262); chain: `ConditionalMovement.LocalMove.one_copy_move_cfc` (ConditionalMovement/UnitaryCovariance.lean:352) → `one_copy_move_unitary_image` (:230) → `one_copy_move_schmidt` (SingularInterpolation.lean:161) → `one_copy_interpolation` (SingularInterpolation.lean:104, regularisation = D5.5.11) → `one_copy_interpolation_fullrank` (DoubleCurve.lean:205); scalar absorption `entropy_remainder_bound` (MoveBounds.lean:117) = D5.5.10; files ConditionalMovementEstimate.lean, ConditionalMovement/{UnitaryCovariance,DoubleCurve,Interpolation,MoveBounds,SingularInterpolation}.lean (whole) | 1904 | drift (statement matches the paper: ∃ C c universal, σ τ PSD trace ≤ 1, word σ^{a/2}ρ̂_P^{−a/2}τ^{a/2}ρ̂_U^{−a/2}θ, a·log(e·card X) ≤ c, η = S(x\|P)+S(x\|U), ℂ only. Route: paper: G(z) on a strip, left/right boundaries via slack λ(u), Hellinger and harmonic-measure integral; Lean: θ turned into a coefficient matrix C∈Matrix(X×U)(P×F), rotated to Schmidt form by unitaries, then `doubleCurve` strip product with *paired* three-lines in ‖G(z)‖²‖G(z+1)‖² and explicit constants 200000, a·ℓ ≤ 1/8, free parameter `l ≥ max(1, log card X)`) | golf + restate the internals onto D5.6–D5.11 as separate declarations (the paper's order); keep the frozen-quantifier statement. Pitfall: OK — constants C, c chosen before the dimensions (`∃ C c` precedes ∀ types), threshold uses only `Fintype.card X` (dim x); dims of P,U,F never enter, ConditionalMovementEstimate.lean:262 |
| D5.6 | Step eq:conditional-slack, eq:conditional-overlap (left boundary, slack) | `ConditionalMovement.ConditionalCollision.left_boundary_trace` (BoundaryEnergy.lean:302), `...conditional_optimizer_deficit` (FilterSlack.lean:163), `...optimizer_deficit_bound` (FilterSlack.lean:121), `ConditionalMovement.MatrixInterpolation.optimizerWeights` (Optimizer.lean:280) + `optimizer_attains`, `optimizer_root_bound`; files NormalizedRows.lean (whole), Optimizer.lean (lines 1–422), BoundaryEnergy.lean (302–340), FilterSlack.lean (121–209) | 878 | drift (paper: ξ=K^r/Tr K^r and log-slack λ(u) with Tr τ_u^{2a}ξ^{1−2a} ≥ e^{−2λ}; Lean: ξ-spectrum = `optimizerWeights A β` (normalised (AA*)^{1/(1−β)}) built through Hölder duality in NormalizedRows/Optimizer, and slack is the *linear* deficit 1 − Tr(…) ≤ ε, not λ) | restate onto D5.6 as one declaration (λ as log-slack or 1−Tr, choose one) and golf (≈1/3 of Optimizer/NormalizedRows is optimizer machinery with no digest counterpart). Pitfall: n/a (no constant-dependence hazard; deficit ε is dim-U-free: FilterSlack.lean:163) |
| D5.7 | Step eq:conditional-hellinger | `ConditionalMovement.ConditionalCollision.conditional_optimizer_root_stability` (Optimizer.lean:423), `ConditionalMovement.OptimizerStability.weighted_root_stability` (OptimizerStability.lean:70), `refined_young` (OptimizerStability.lean:43), `root_hs_le_deficit` (Optimizer.lean:130, counted in D5.6); files OptimizerStability.lean (whole), Optimizer.lean (423–469) | 164 | drift (paper: concavity of φ(b)=1−Tr ρ^{[b]}ξ^{[1−b]} and Hölder, divide by 4a; Lean: `weighted_root_stability` b·ΣΣu(√p−√q)² ≤ 1−ΣΣu p^{1−b}q^{b} via a refined Young inequality) | keep (the scalar lemma is the right shape; golf); Standard? concavity argument → search pending. Pitfall: OK — β·‖√ρ−√ξ‖² ≤ ε=O(β²ℓ²) so H = O(√β ℓ), not O(β ℓ), Optimizer.lean:423 |
| D5.8 | Step eq:conditional-phase-hellinger | `ConditionalMovement.MatrixInterpolation.phase_root_deficit` (PhaseTransfer.lean:104), `ConditionalMovement.RenyiSlack.phase_le_gap` (RenyiSlack.lean:124), `SpectralPhase.spectral_difference_energy` (SpectralPhase.lean:41); files RenyiSlack.lean, SpectralPhase.lean (whole), PhaseTransfer.lean (104–163) | 476 | drift (paper: termwise β\|α̂^{ib}−β̂^{ib}\|² ≤ C(1+\|b\|)²(√α−√β)² by cases on v=α/β; Lean: termwise \|e^{itz}−1\|² ≤ 36(1+\|t\|/b+t²/b)·gap_b(z) in terms of the Rényi gap 1−(…)^{1−b}(…)^{b}, i.e. phase controlled by the Rényi deficit, not by √-distance) | restate (to the paper's Hellinger form, or merge into D5.9 together with D5.7 since Lean only ever uses the Rényi form). Pitfall: OK — √B (the weight) on the right: `phase_root_deficit` has `power U p (1/2)` on the right so kernel of the weight contributes 0, PhaseTransfer.lean:104 |
| D5.9 | Step eq:conditional-state-movement | `ConditionalMovement.MatrixInterpolation.modular_state_distance` (ModularDistance.lean:100), `...phase_transfer` (PhaseTransfer.lean:207), `ConditionalMovement.ConditionalCollision.conditional_modular_distance` (FilterSlack.lean:223), `...conditional_phase_continuity` (ConditionalPhase.lean:206; = D5.9.2, E L² ≤ ℓ²-bound with t²(2ℓ²+8)), `ConditionalMovement.PhaseContinuity.renyi_phase_continuity` (PhaseContinuity.lean:67); files ConditionalPhase, ModularDistance, PhaseContinuity (whole), PhaseTransfer.lean (1–103, 164–241), FilterSlack.lean (210–300) | 832 | drift (paper: ‖θ_u−θ‖ ≤ C(1+\|u\|)(√λ+√a ℓ) from first-term/second-term split with E\|1−e^{−iauv}\|² computed on {v≤0}, {v>0}; Lean: bounds the squared HS distance of the phase words by 24·\|\|√U−√V\|\|² + 216(1+\|t\|/b+t²/b)·(Rényi deficits) + 2·‖(phaseU−phase1)C‖², no λ(u), no v-split) | restate; merge D5.7–D5.9 into one deficit-based step (Lean's own route). Pitfall: n/a (θ_u is never a declaration: the two forms of θ_u are absorbed in `power`/`phase` identities, ModularDistance.lean:100) |
| D5.10 | Step — Right boundary | `ConditionalMovement.ConditionalCollision.right_boundary_entropy` (BoundaryEnergy.lean:341), `...boundary_pair_energy` (BoundaryEnergy.lean:379), `...paired_entropy_boundary` (BoundaryEnergy.lean:139), `...opposite_entropy_absorbed` (Purification.lean:79), `ConditionalMovement.QuantumSSA.conditional_continuity` (EntropyContinuity.lean:95: a second proof of Lemma 2.1/D2.4 in the coefficient-matrix encoding); files BoundaryEnergy.lean (1–301, 341–431), EntropyContinuity.lean (whole), Purification.lean (1–222) | 944 | drift (paper: D5.4 with U→P then Lemma 2.1 with D=x,E=P, δ ≤ ‖θ_u−θ‖, √‖θ_u−θ‖ from D5.9; Lean: continuity is not applied to S(x\|P)_{θ_u}; `opposite_entropy_absorbed` absorbs the *other* entropy into the deficit and `boundary_pair_energy` pairs the two boundaries at the same t. `conditional_continuity` is a duplicate of OpenAI.conditional_continuity (§2) used only through this chain) | restate (right boundary as the paper); cut the duplicate `conditional_continuity` in favour of the §2 declaration. Pitfall: OK — continuity is for S(x\|P), log card of the *first* factor m (=X), `conditional_continuity` EntropyContinuity.lean:95 |
| D5.11 | Step — Log-interpolation with harmonic measure | `ConditionalMovement.LocalMove.paired_three_lines` (ThreeLines.lean:48), `paired_three_lines_vector_sq` (ThreeLines.lean:146); file ThreeLines.lean | 179 | drift (paper: Poisson kernel du/(2cosh πu) and sub-mean-value of log\|φ\|; Lean: ‖G(z)‖²‖G(z+1)‖² ≤ e^{A+B·Im z²} on the line Re z=0 ⇒ bound at z=1/2, via Hadamard/Phragmén–Lindelöf, no log-integral) | replace-by `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (Mathlib.Analysis.Complex.Hadamard) if the paired Gaussian form can be dropped; otherwise keep as a library-tree lemma. Pitfall: OK — pairing at the same Im z is exactly what the statement does, ThreeLines.lean:48 |
| D5.12 | Lemma 5.2 (marginal-phase comparison) | `Entropy.MarginalPhase.norm_phaseDifference_mulVec_le` (OpenAI/MarginalPhaseSingular.lean:471; θ on (X×(U×F))×P, constant 2\|sinh πu\|·`Matrix.phaseRate (card X) η`, `Matrix.phaseRate` ResolventPhaseRate.lean:25) ← `Entropy.MarginalPhase.norm_phaseDifference_le` (MarginalPhaseSingular.lean:215; √ρ_f HS-form, = D5.12.10+11); helpers: `Matrix.ResolventCompression.norm_phaseGap_le_phaseRate` (ResolventPhaseBound.lean:332, D5.12.7–9), `Complex.integral_cpow_imag_mul_inv_sub` (ResolventMellin.lean:276, D5.12.6), `Entropy.MarginalPhase.linMatrix_isoMap_compress` (MarginalPhaseCompression.lean:176, D5.12.2–3); files MarginalPhase{Setup,Powers,Compression,Faithful,Comparison,Approx,Limit,Singular}.lean, ResolventMellin, ResolventPhaseGap, ResolventPhaseRate, ResolventPhaseBound (whole) | 2615 | faithful (statement is the θ-form; proof follows D5.12.1–11 in order: faithful setup with A=L_σR_{ρ⁻¹}, isometry V, resolvent integral, split at y/d² and 1/y, regularisation (1−ε)ρ+εI/dim. ℂ only) | golf (2615 lines for ~3 pages: ~1/3 is a hand-rolled spectral-function calculus `spectralFun`/`cpowSpec`/`rpowSpec`; replace by `cfc`). Standard?: Mellin integral ∫v^z/(x+v)dv — Mathlib search found nothing; library tree. Pitfall: OK — R_η uses d = card X only, `phaseRate (Fintype.card X)`, MarginalPhaseSingular.lean:471 |
| D5.13 | Step eq:conditional-resolvent-square, eq:conditional-resolvent-entropy | no single declaration: h(v) ≥ 0 is `Matrix.ResolventCompression.defect_nonneg` (ResolventDefect.lean:221) with `discrepancy_quadratic` (:165, compression identity D5.13.1); ∫h = log-gap is `...integrableOn_defect_and_integral` (ResolventDefectIntegral.lean:125); log-gap = I(x:F\|U) is `Entropy.MarginalPhase.compression_logGap` (MarginalPhaseLogGap.lean:128, D5.13.3–4, with `re_logForm`); files MarginalPhaseLogGap.lean (whole), ResolventDefect.lean (1–212, 221–232), ResolventDefectIntegral.lean (1–77, 120–163) | 519 | smeared (steps D5.13.1–4 each a separate declaration across 3 files; the abstract `ResolventCompression` structure is the shared set-up) | merge (one statement of h≥0 and ∫h=η; keep the abstract `ResolventCompression` interface only if D5.12/13/14 all use it). Standard?: Carlen–Vershynina Lemma 2.1; integral log formula — search pending |
| D5.14 | Step eq:conditional-resolvent-tail | `Matrix.ResolventCompression.defect_le_invQuadA` (ResolventDefectIntegral.lean:78), `defect_le_quadB_div_sq` (ResolventDefectIntegral.lean:92), `mul_norm_discrepancy_sq_le` (ResolventDefect.lean:213), `Entropy.MarginalPhase.compression_invQuadA_le` (MarginalPhaseQuadratic.lean:125, D5.14.1–2 = D5.2.1 in Hilbert–Schmidt form), `compression_quadB` (:70); files MarginalPhaseQuadratic.lean (whole), ResolventDefectIntegral.lean (78–119), ResolventDefect.lean (213–220) | 211 | smeared (h ≤ d², h ≤ v⁻², ‖δ_v‖ ≤ √(h/v) are three declarations in three files) | merge (one lemma `0 ≤ h ≤ min(d², v⁻²)`, ‖δ‖ ≤ √(h/v)); the d² bound re-proves ρ ≤ d(I⊗ρ_{UF}) (D5.2.1) a second time — merge with D5.2 |
| D5.15 | Lemma 5.3 (conditional skew estimate) | `Entropy.ConditionalSkew.conditionalSkew_le` (OpenAI/ConditionalSkewBound.lean:44; θ : (P₀×P₁)×((X×U)×F)→ℂ, 0≤h≤1 on P₀×X, a·log(e·card(P₀×X)) ≤ 1/8, ‖f(a/2)‖−Re f(a/2) ≤ `skewConst`·a²ℓ_h⁴η^{1/8}), `Entropy.ConditionalSkew.skewFun` (ConditionalSkewSetup.lean:86, the entire f), `Entropy.ConditionalSkew.skewEta` (ConditionalSkewPhaseComparison.lean:226); files ConditionalSkewBound.lean (whole), ConditionalSkewSetup.lean (lines 1–32, 36–141: marginals `margP`/`margW`/`margY`, lifts) | 286 | faithful (proof follows the roadmap: D5.16 strip bound → D5.17 imaginary-axis phase comparison → D5.18 → D5.19 (`OpenAI.norm_sub_re_le_of_phase_bounds`) → D5.20 rate bookkeeping; ℂ only; P₁ unconstrained as in the paper) | golf. Pitfall: OK — R_η uses `Fintype.card X` (d = dim x) while ℓ_h uses `Fintype.card (P₀ × X)` (d_h); η = `skewEta θ` is I(x:F\|U) of θ's marginal, involves X only, ConditionalSkewBound.lean:44 |
| D5.16 | Step eq:conditional-narrow-strip | smeared over: `OpenAI.norm_le_exp_one_mul_of_strip` (OpenAI/StripQuadratic.lean:103, D5.16.6 three-lines on a general entire f), `Entropy.ConditionalSkew.norm_skewFun_le_of_strip` (ConditionalSkewStrip.lean:92, ‖f‖ ≤ d_h² on \|Re z\|≤1/2, D5.16.1–3), `norm_skewFun_imag_le` (ConditionalSkewValues.lean:116, D5.16.5), `skewFun_neg_conj` (ConditionalSkewValues.lean:149, D5.16.4); files ConditionalSkewValues, ConditionalSkewStrip, ConditionalSkewStripCore, StripQuadratic (whole) | 551 | smeared | merge (the narrow-strip statement does not exist; Lean's strip is 1/(8ℓ) inside the generic lemma, cf. D5.19); StripQuadratic's `abs_re_sub_le_of_strip` is a second route to D5.19.4 used by another section (ModularExpectation) — ask the integrator. Standard?: Hadamard three-lines → replace-by `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (Mathlib, already used in StripQuadratic). Pitfall: OK — strip half-width 1/(8ℓ) ∝ 1/ℓ, StripQuadratic.lean:103 |
| D5.17 | Step eq:conditional-phase-discrepancy | smeared: f(iu)=⟨w,hw⟩ is `Entropy.ConditionalSkew.imag_vector_eq` (ConditionalSkewGeometry.lean:105), ‖w_u−w_u⁰‖-form is `imag_vector_sub_eq` (ConditionalSkewPhaseComparison.lean:131), the Lemma 5.2 application is `norm_liftR_phaseDiffW_le` (ConditionalSkewPhaseComparison.lean:230, ρ_Y version via `thetaR`, `relUnitary`); also contains the D5.18.1 inequality as `norm_skewFun_imag_sub_le` (:243); files ConditionalSkewPhaseComparison, ConditionalSkewGeometry, ConditionalSkewSupport (whole), ConditionalSkewPhaseCore.lean (1–24, 88–235) | 702 | smeared | merge (state D5.17 once; drop the `thetaR`/`reindexE`/`regroup`/`liftR` re-encodings once θ lives on one `Reg`-indexed space). Pitfall: n/a (the ρ_{YF}-vs-ρ_{UF} point is inside `imag_vector_sub_eq`; not verified line by line) |
| D5.18 | Step eq:conditional-first-derivative | smeared: \|f(iu)−p\| bound is `norm_skewFun_imag_sub_le` (ConditionalSkewPhaseComparison.lean:243, counted in D5.17); \|f'(0)\| ≤ C√p R is `OpenAI.norm_deriv_le_of_phase` (SkewFromPhases.lean:152); f'(0)∈iℝ is `OpenAI.re_deriv_eq_zero_of_symm` (SkewFromPhases.lean:196); file SkewFromPhases.lean (lines 1–111, 139–225) | 198 | smeared | keep (these two are already abstract-in-f; golf) ; Standard?: elementary |
| D5.19 | Step — Gaussian-weighted three-lines and second-order remainder | `OpenAI.norm_sub_re_le_of_phase_bounds` (SkewFromPhases.lean:226; abstract entire f with symmetry, \|f\|≤1 on iℝ, ≤m on \|Re\|≤1/4, phase hypothesis; conclusion t²(8π²R²+C ℓ²√min(1,R))), `OpenAI.phaseError_mul_exp_le` (SkewFromPhases.lean:112), `OpenAI.norm_sub_sub_deriv_le` (SkewFromPhases.lean:44, counted in D5.18 range); file SkewFromPhases.lean (112–138, 226–441) | 243 | faithful (F=(f−p)e^{z²}, outer-line and imaginary-axis bounds, three lines on half-strips via Mathlib `HadamardThreeLines`, Cauchy second-order remainder: same steps as D5.19.1–4) | keep; Standard?: Cauchy estimate → replace-by Mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` family (search pending for the second-order form) |
| D5.20 | Step — Parameter bookkeeping | `Entropy.ConditionalSkew.phaseRate_le` (ConditionalSkewRate.lean:41: R ≤ 3ℓ(min(1,η))^{1/4} given η ≤ 2ℓ), `Entropy.ConditionalSkew.condMutualInfo_le_two_log` (ConditionalSkewEta.lean:44, η ≤ 2 log d), `condMutualInfo_nonneg` (:30); final combination inside `conditionalSkew_le` (ConditionalSkewBound.lean:44, counted in D5.15); files ConditionalSkewRate.lean, ConditionalSkewEta.lean | 161 | smeared (statement `ℓ_h²m^{1/2}+R² ≤ Cℓ_h⁴η^{1/8}` itself is not a declaration; case η ≥ 1 uses η ≤ 2ℓ through the hypothesis `hη`) | inline into D5.15. Pitfall: OK — η ≥ 1 case needs η ≤ 2ℓ, provided as hypothesis `hη : η ≤ 2*ℓ` and discharged by `condMutualInfo_le_two_log`, ConditionalSkewRate.lean:41 |
| D5.21 | Step — Closing remark | — | 0 | none | cut (remark) |
| (section infra) | — | Second encoding of states/entropy for the movement chain: `ConditionalMovement.QuantumSSA.*` (own strong subadditivity, partial traces `ptrL`/`ptrR`, `traceEntropy`, coefficient/`reshuffle`, pure-state entropies): ConditionalMovement/{EntropyBounds,LogCompression,PartialTrace,PureEntropy,StrongSubadditivity}.lean, FilterSlack.lean (1–120); lattice adapters of Lemma 5.1: `Entropy.regionalMovement_norm_le` (OpenAI/ConditionalMovementRegional.lean:376, `FourPartition`, `frameEquiv`) and the η-identities `Entropy.regionalMovementEta_eq_cmi_left` (OpenAI/MovementEtaRegional.lean:300, `IsRegionSplit`) | 2277 | overbuilt (SSA, partial trace and conditional entropy re-proved on `Matrix (X×Y)(P×F)` although `Arealaw.vonNeumann_strong_subadditivity`, `Matrix.traceLeft/traceRight` exist; the regional files exist only to move Lemma 5.1 between three state encodings) | cut after unifying the encoding: re-prove D5.5 on the statement encoding (`Reg`, `pureState`, `SubState.regionEntropy`); SSA/entropy → use §2's; LogCompression (459) is also imported by `OpenAI.PositiveProjectionCompression` and `OpenAI.SpectralProjectionIntertwiner`, so check before cutting |
| (section infra, reverse pass) | — | `Matrix.PosSemidef.leftKroneckerEmbed_supportProj_mul_self` (OpenAI/MarginalSupportAbsorption.lean:79); `Matrix.PosSemidef.mul_leftKroneckerEmbed_supportProj_self` (OpenAI/MarginalSupportAbsorption.lean:117); `Matrix.PosSemidef.rightKroneckerEmbed_supportProj_mul_self` (OpenAI/MarginalSupportAbsorption.lean:168); `Matrix.PosSemidef.mul_rightKroneckerEmbed_supportProj_self` (OpenAI/MarginalSupportAbsorption.lean:206); `Matrix.PosSemidef.productMarginals_kernel_le` (OpenAI/MarginalSupportAbsorption.lean:229); (whole file, 3 decls) (OpenAI/MaximalOverlap.lean:43-60); `quantumRelativeEntropy_product_marginals` (OpenAI/ProductMarginals.lean:160); 11 decls: `exists_isometry_norm_sub_le_of_purification`, `exists_isometry_norm_sub_padPurification_le`, `tensorPurification`, `partialTraceRight_vecMulVec_tensorPurification`, `canonicalPurification`, `partialTraceRight_vecMulVec_canonicalPurification`, `exists_isometry_purification_norm_sub_tensorPurification_le`, `exists_isometry_norm_sub_tensorPurification_le`, `exists_isometry_norm_sub_tensorPurification_le_mutualInformation`, `exists_isometry_norm_sub_tensorPurification_le_sqrt`, `exists_isometry_norm_sub_tensorPurification_le_zpow` (OpenAI/PurificationSplitting.lean:117-362); `Matrix.IsHermitian.trace_cfc_mul_cfc_eq_double_sum` (OpenAI/RootFidelityRelativeEntropy.lean:91); `Matrix.exp_neg_quantumRelativeEntropy_div_two_le_rootFidelity` (OpenAI/RootFidelityRelativeEntropy.lean:148); `Matrix.PosSemidef.re_dotProduct_cfc_log_mulVec_le_log` (OpenAI/SupportLogJensen.lean:62); `Matrix.supportCPow` (OpenAI/SupportPower.lean:30); `Matrix.differentiable_spectralFun_apply` (OpenAI/SupportPower.lean:58); `Matrix.differentiable_supportCPow_apply` (OpenAI/SupportPower.lean:65); `Matrix.re_diag_conj_le_one` (OpenAI/SupportPower.lean:86); `Matrix.normSq_supportCPow_entry` (OpenAI/SupportPower.lean:121); `Matrix.re_trace_supportCPow_sandwich_le` (OpenAI/SupportPower.lean:133) | 975 | — | inline into S05 UhlmannIsometry/PurificationSplitting chain (partial trace of a pure vector / overlap); inline into S05 conditional support-power (Hadamard three-lines style) anchor; owner anchor to be assigned; inline into S05 marginal-support absorption (owner anchor: ProductMarginals/relative-entropy chain); inline into S05 purification-splitting anchor (Uhlmann-isometry corollaries); inline into S05 relative-entropy product-marginal anchor; inline into S05 root-fidelity vs relative-entropy anchor; inline into S05/S07 log-Jensen anchor (Jensen in digest 05, 07) |

## 06-replicas.md

Lines now (section total): 25889

All §6 code is ℂ-only (matrices over `ℂ`; `RCLike` occurs only as `RCLike.re_le_norm`); no 𝕜-generic declaration and no ℂ→𝕜 transfer exists in this section. Line counts are whole-file (≈ where a declaration was split out of a file).

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D6.1 | Def (systems, symmetric subspaces, subsystems) | `TensorPower.copyPerm` (OpenAI/TensorPowerAction.lean:114), `TensorPower.Config` (:126), `TensorPower.subsystemPerm` (:131), `TensorPower.symmetricSubspace` (:180), `PermutationRepresentation.symProj` (:57), `permOp` (OpenAI/PermutationRepresentation.lean:86), `groupAlgebraRep` (:121), `IrrepLabel.exists_centralIdem_eq_averagingElement` (OpenAI/TrivialLabel.lean:121, Π_k = trivial label); helpers: SymmetricProjection, SymmetricProjectionCoordinates, SubsystemTransport, ReplicaSupport, ReplicaSiteOp (whole files) | 1095 | faithful (ℂ-only) | keep; golf. V is encoded three ways (`Config k ι` with a family `ι : F → Type`, `Entropy.SiteConfig n`/`RegionConfig n`, and bare `Fin q`/`Ω`): unify to one. `D_k` is never stated; only `Tr Π_k` and cruder bounds are used (fine). Pitfall: n/a (no Pitfall in digest) |
| D6.2 | Step eq:schur-decomposition (Schur–Weyl, Weyl character) | no single statement; proved from scratch: `TensorPower.alternant_mul_glChar` (OpenAI/WeylCharacter.lean:477, Weyl character formula), commutant results in SchurWeylCommutant/UnitaryCommutant/CommutantDimension (`sum_multiplicity_le_finrank_commutant`, OpenAI/CommutantDimension.lean:138); labels of S_k = partitions: SchurWeylLabels; `IrrepLabels`/`IrrepLabelCount`/`RegularTrace`/`IsotypicDimension` (Artin–Wedderburn labels, #labels = #conj. classes); highest-weight/Pieri machinery: HighestWeight, ColumnAntisymmetrizer, ExteriorPieri, SplitCopies, Alternant, SchurWeylLift, PartitionCount (all whole files, OpenAI/) | 5259 | overbuilt (paper: cited textbook theorem; Lean re-proves Schur–Weyl and Weyl characters, ℂ-only) | library tree. Standard? yes. Mathlib search done (atlas glob/semantic, corpus mathlib): no Schur–Weyl, Specht, Weyl character, hook formula; only `FDRep` characters and `Complex.betaIntegral`; `#irreps = #conj classes`: search pending (`IrrepLabelCount.lean`). Restate once in Mathlib's `FDRep`/`Representation` generality, or axiom-cite per paper |
| D6.3 | Def eq:F-definition (label projectors, F_{Q,k}) | `PermutationRepresentation.labelProj` (OpenAI/LabelProjectors.lean:42), `labelObservable` (:74), `labelEntropy` (:79, F = Σ log d_λ π^λ) | 99 | faithful (ℂ-only) | keep. Pitfall: n/a |
| D6.4 | Lemma 6.1 (Schur-label estimates, parts 1–6) | no declaration states the lemma; per part: (1) `TensorPower.schur_dim_eq_hookFormula` (OpenAI/SchurLabelEstimates.lean:60), `schur_abs_log_dim_sub_le` (:67), `TensorPower.schur_multiplicity_eq_weylFormula` (OpenAI/WeylDimension.lean:287), `card_labelProj_ne_zero_le` (OpenAI/CommutantDimension.lean:341), `sum_multiplicity_le` (:334); (2) `TensorPower.labelProj_mul_symProj_compl` (OpenAI/SchurLabelCommutation.lean:117), `commute_subgroup_labelObservables_of_subset_or_disjoint` (OpenAI/SubsystemLabelCommutation.lean:37); (3) `PermutationRepresentation.dim_le_mul_dim_of_compatible` (OpenAI/MergeDimensions.lean:45, `'` :147), `TensorPower.merge_moment_le` (OpenAI/MergeMoment.lean:434); (4) `PermutationRepresentation.mul_dim_le_dim_of_compatible` (OpenAI/GroupedCopies.lean:163), `dim_le_index_mul_of_compatible` (:180), `TensorPower.groupedCopies_labelEntropy_bounds` (OpenAI/GroupedLabelEntropy.lean:72); (5) `TensorPower.schurSurprisal` (OpenAI/SchurSurprisal.lean:353); (6) `TensorPower.schur_branch_probability` (OpenAI/SchurLabelEstimates.lean:95), `schur_starOp_eigenvalue` (:124); helpers: HookDimension, HookFormula, HookRecursion, WeylDimension, WeylRecursion, JucysRecursion, JointIsotypic, BranchProbability, Branching, BranchingPieri, StarOperator, Casimir (whole files) | 5371 | smeared (also drift on part 1 and 3) | Part 1 drift: paper: coefficient extraction from (Σx_i)^k·alternant + Vandermonde of falling factorials (D6.4.2–4); Lean: Pieri/branching recursion on Weyl formula (WeylRecursion, HookRecursion, JucysRecursion). Part 3 drift: paper: exact `Pr(ν\|λ,μ)=g d_ν/(d_λ d_μ)` for *product* states with g ≤ poly (D6.4.11–12); Lean: general ρ invariant under Q- and E-copy permutations, bound `(k+1)^{q²}`, via `sum_multiplicity_le` (MergeMoment.lean:404,434). Action: restate as one `Lemma 6.1` with six conjuncts (or six named parts) and merge the helper recursions (HookDimension/HookRecursion/WeylRecursion/JucysRecursion are four routes to the dimension formula: keep one); parts (1),(2),(6) are standard (Keyl–Werner, branching rule, Vershik–Okounkov): library tree. Pitfall: OK — complement equality only on `S_k` (`labelProj … * symProj` form, SchurLabelCommutation.lean:117); (6) stated on `(ℂ^q)^{⊗k}` with `q` the factor's own dimension, padded `l_i` is used only in D6.6 (SchurLabelEstimates.lean:95); (3) only invariance under the two copy groups is assumed, which is weaker than the product hypothesis (OK, more general, MergeMoment.lean:404) |
| D6.5 | Def eq:w-definition (w_k, W_{Q,k}) | `Partition.replicaConst` (OpenAI/ReplicaWeight.lean:147), `Partition.replicaWeight` (:152), `TensorPower.replicaLabelWeight` (OpenAI/ReplicaMetric.lean:79), `TensorPower.replicaMetric` (:85) | 21 | faithful (ℂ-only) | keep. Pitfall: OK — labels padded to the full dimension `replicaDim ι` for every `Q`, not `d_Q` (ReplicaMetric.lean:79–83); the Gamma-offset `c` is `replicaConst`, distinct from the §5 constant `c` (RelativePin.lean:151 uses a separate `c`) |
| D6.6 | Lemma 6.2 (integral formula, marked ratios) | no single statement; positivity `TensorPower.posDef_replicaMetric` (OpenAI/ReplicaMetric.lean:108), centrality `commute_replicaMetric_of_subset` (:150), complement `replicaMetric_mul_symProj_compl` (:166), `W-comparison` `exists_replicaMetric_comparison` (:225), `W-integral` `exists_replicaMetric_integral` (OpenAI/ReplicaIntegral.lean:173), full-dim law `integral_specSample_tensorPow` (OpenAI/ReplicaSpectralLaw.lean:419), Gamma integral `Partition.replicaWeight_eq_gammaIntegral` (OpenAI/ReplicaGammaIntegral.lean:553), `R-forward` `exists_l2_opNorm_markedRatio_sub_le` (OpenAI/ReplicaMarkedRatio.lean:286), `‖R‖` (:306), `R-inverse` `exists_norm_markedRatio_inv_mulVec_le` (OpenAI/ReplicaMarkedRatioInverse.lean:366) and `exists_norm_markedRatio_inv_sub_clipped_le` (:604); helpers: ReplicaMetric/ReplicaWeight/ReplicaRatio (asymptotics), GammaRatio (Wendel), BetaHalfLine, TraceCompression, UnitaryTwirl, UnitaryHaar, CentralLabelFunction (whole files) | 4088 | smeared (plus drift on D6.6.2/D6.6.8) | Drift: paper: measure on the simplex with density ∝ Δ(s)Δ(s^t), Haar U independent; Lean: orthant `x∈ℝ^d_+` with density a_δ(x)a_δ(x^t)e^{-Σx}, s = x/Σx (equal law by homogeneity; ReplicaSpectralLaw.lean:10–17, a second route). Drift: paper: `Tr τ ≤ 1` by min–max eigenvalue comparison (D6.6.8); Lean: `Tr (A\|_m)^p ≤ Tr A^p` with p=1/t (`Matrix.re_trace_rpow_submatrix_le`, TraceCompression.lean:85). Drift: integral stated for 0<t≤1 (ReplicaIntegral.lean:173), ratios for 0<t<1/2, paper 0<t<1/4 (generalisation only). Action: restate as one Lemma 6.2 (items: pos/central, comparison, complement, integral, R-forward, R-inverse); merge ReplicaMetric/ReplicaWeight/ReplicaRatio asymptotics; GammaRatio/BetaHalfLine/Wendel: replace-by Mathlib `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma` and `Complex.betaIntegral` where possible (search partial). Pitfall: n/a |
| D6.7 | Step eq:fixed-factor (fixed pure factor restriction) | — (no declaration states `W_{BQ,k}(φ^{⊗k}⊗z)=φ^{⊗k}⊗W_{Q,k}z`; downstream worked around by Bell-specific insertion identities `TensorPower.labelObservable_mul_bellInsertion_*` (OpenAI/BellInsertionCoordinates.lean:234,255), `replicaMetric_factor_mul_bellInsertion_symProj` (OpenAI/BellPinnedMetricCoordinates.lean:148), parked in infra) | 0 | missing | prove (one lemma from `W=(1/k!)Σ f_k(π)U(π)`; then cut the Bell insertion layer). Pitfall: n/a (no Pitfall in digest) |
| D6.8 | Def eq:leaf-metric (A_k(P,Y,F)) | `TensorPower.leafRoot` (OpenAI/ReplicaSimilarity.lean:94), `TensorPower.leafMetric` (:101), `leafRoot_comm` (OpenAI/ReplicaEtaForms.lean:38), `leafMetric_comm` (:48, P↔F symmetry); commutation/positivity of the factors: OpenAI/ReplicaDisjointMetricPositivity.lean (whole file) | 148 | faithful (ℂ-only) | keep. Pitfall: n/a |
| D6.9 | Step eq:leaf-floor (floor, commutation with copy averages) | no declaration states `log A_k = a(F_P+F_F−F_Y)+O(log k)`; pieces: `TensorPower.exists_replicaMetric_inv_square_le_exp` (OpenAI/ReplicaWholeInverse.lean:56), `exists_replicaMetric_inv_square_le_grouped_exp` (OpenAI/ReplicaGroupedInverse.lean:157), `subgroup_signedLabelEntropy_symProj_nonneg` (OpenAI/GroupedLabelSymmetricSupport.lean:110, F_P+F_F−F_Y ≥ 0 on S_k), `exists_replicaMetric_symProj_inverse_bound_and_floor` (OpenAI/ReplicaSymmetricMetricFloor.lean:53) and `…_isometric_floor` (:106); commutation of `h̄` with `A_k`: `commute_labelObservable_siteOp_of_disjoint` (OpenAI/ReplicaSimilarity.lean:264, counted in D6.13) | 694 | smeared | Lean cites §8 (`07-comparators.tex` 454–480, 603–615) for the floor, not §6; the floor is proved only for covers `P∪Y∪F=univ`, one-sided (inverse ≤ poly·e^{…}); restate once as D6.9 and merge the whole/grouped/symmetric variants. Pitfall: n/a |
| D6.10 | Lemma 6.3 (relative coherent pin) | `TensorPower.relativePin` (OpenAI/RelativePin.lean:151), regional/exchanged forms `relativePin_regionalMovementEta` (OpenAI/ReplicaEtaForms.lean:62), `relativePin_toF` (:83); helpers: RelativePin (frame/marginal lemmas), RelativePinAlgebra (Cauchy–Schwarz, `moveWord`, `relativeMetric`), RelativePinCommute, RelativePinCompensator (`T_R`), ReplicaLift (integral in lifted form), TensorPowerRpow (whole files); uses `Entropy.regionalMovement_norm_le` (OpenAI/ConditionalMovementRegional.lean:376, = Lemma 5.1, mapped by §5) | 1240 | faithful (ℂ-only; statement is the quadratic-form form ` | ⟨θ^{⊗k},w⟩\|² e^{…} ≤ K(k+2)^N ⟨w,Cw⟩`, i.e. D6.10.1 inlined; t range 0<t≤1 rather than <1/4) \| keep; golf (ReplicaEtaForms re-states the same lemma twice more, merge). Pitfall: OK — hypothesis is on `a·log(e·\|RegionConfig n x\|)` i.e. `dim x`, not `dim V` (RelativePin.lean:~160); `a^{1/4}` after the `ka` prefactor (RelativePin.lean:~160); no commutation of `W_{Px}`,`W_{xY₀}` is used (integral + triangle inequality, RelativePin.lean:151). η_θ is a second region-entropy encoding (`Entropy.movementEta`/`regionalMovementEta`), see notes |
| D6.11 | Def eq:resolution, eq:husimi (coherent probability measure) | `TensorPower.coherentIntegral` (OpenAI/CoherentMeasure.lean:23, functional `φ ↦ D_k∫Tr(σP_{Ue_a,k})φ(Ue_a)dHaar(U)`), `TensorPower.unitaryTwirl_coherentProj` (OpenAI/CoherentResolution.lean:69, resolution); second encoding `TensorPower.coherentMeasure` on `CoherentSphere` (OpenAI/ReplicaTransportCoherentMeasure.lean:146, in infra) | 308 | drift (paper: unitarily-invariant probability measure dθ on the unit sphere, dμ_σ = D_k Tr(σP)dθ; Lean: Haar on U(Ω) pushed through `U ↦ U e_a`, a functional not a measure; the sphere measure appears separately in §7 code) | restate once as a measure on the sphere (`coherentMeasure`) and derive `coherentIntegral` from it; Standard? yes (CKMR 2007): library tree. Pitfall: n/a |
| D6.12 | Lemma 6.4 (marked-copy scalar symbols, items 1–4) | no single statement; (1) `exists_norm_markedSimilarity_mulVec_le` (OpenAI/ReplicaSimilarity.lean:513, counted in D6.13); (2),(3) `hasCoherentSymbol_markedSimilarity` (OpenAI/MarkedSimilaritySymbol.lean:413), `eventually_norm_trace_freeAlgebra_markedSimilarity_sub_le` (:572), `eventually_norm_trace_skewOperator_markedSimilarity_sub_le` (:590); (4) `TensorPower.…eventually_re_trace_skewOperator_le` (OpenAI/SkewSymbolBound.lean:466), region-entropy form `SkewPartition.eventually_re_trace_skewOperator_le_regionalMovementEta` (OpenAI/ReplicaEtaForms.lean:284) and outer-exchanged `…_le_swap` (:306); helpers: OpenAI/MarkedSimilaritySymbol.lean, SkewSymbolBound.lean, ReplicaEtaForms.lean (rest of file) | 1352 | smeared | Lean: 0<t<1/2 (paper <1/4, generalisation); item 4 with `h = lift K`, `0≤K≤1`, `a log(e d_h) ≤ 1/8` (paper: `≤ c`); item 4 is stated four times (SkewSymbolBound:466, EtaForms:284, EtaForms:306, and the §7 copy `ReplicaTransportSplitSkewBound.lean:322`). Action: restate as one Lemma 6.4 with four items; merge EtaForms variants into the one with `η_θ` in region form; Pitfall: OK — limit order ε then eventually-in-k then sup over σ is correct (`∀ᶠ k, ∀ σ`, MarkedSimilaritySymbol.lean:572,590, SkewSymbolBound.lean:466); item 4 requires `0≤h≤I` via `K` (OK); `\|O_k\|` is handled via polynomial approximation of √ (CoherentSymbolFunction.lean:156), not by expectations of `O_k` on product vectors (OK) |
| D6.13 | Step (bounded approximation on symmetric inputs) | (a) `TensorPower.markedSimilarity_succ_eq` (OpenAI/ReplicaSimilarity.lean:409, compression of the marked word), `exists_norm_markedSimilarity_mulVec_le` (:513); (b) polynomial/clip approximation: not a declaration — inlined in the proof of `hasCoherentSymbol_markedSimilarity` (OpenAI/MarkedSimilaritySymbol.lean:413–~560), polynomials of `J`: `TensorPower.l2_opNorm_starOp_le` (OpenAI/StarFunction.lean:70); helpers: OpenAI/ReplicaSimilarity.lean (rest), StarFunction.lean | 735 | smeared (part (a) stated, part (b) only inside D6.12's proof) | golf ReplicaSimilarity (601 lines for D6.13.1–5); prove/extract (b) as its own lemma or merge into D6.12 as a step. Pitfall: OK — `R^{-1}` only applied to symmetric vectors, `z ∈ symmetricSubspace` in `hCI` (ReplicaSimilarity.lean:513–~535) |
| D6.14 | Step eq:finite-husimi, eq:uniform-husimi | identity `TensorPower.integral_coherent_pairing` (OpenAI/HusimiIdentity.lean:66, `D_k` absorbed into `coherentIntegral`), uniform bound `TensorPower.norm_trace_mul_injectionAverage_sub_coherentIntegral_le` (OpenAI/UniformHusimi.lean:412, constant `4m²(1+d^m)²`); helpers: OpenAI/UniformHusimi.lean, HusimiIdentity.lean, InjectionAverage.lean (injection averages `T_{k,m}`) | 832 | faithful (ℂ-only; follows D6.14.1–5: good permutations, normal form via exchange traces) | keep; golf (`Equiv.Perm.card_filter_apply_eq_mul` UniformHusimi.lean:69 duplicates `Function.Embedding.card_filter_apply_eq_mul` InjectionProduct.lean:48). Standard? yes (Chiribella/CKMR/LNR): library tree, search pending. Pitfall: n/a |
| D6.15 | Step eq:injection-product (products after compression) | `TensorPower.norm_injectionAverage_mul_sub_le` (OpenAI/InjectionProduct.lean:285), `IsInjectionPoly.exists_mul` (OpenAI/InjectionPoly.lean:370), `HasMarkedSymbol.mul` (OpenAI/MarkedSymbol.lean:480), `hasMarkedSymbol_starOp` (OpenAI/MarkedStar.lean:293), donor contraction `sum_expect_regionUnit_smul` (:187), `HasCoherentSymbol.mul` (OpenAI/CoherentSymbol.lean:258); helpers: OpenAI/InjectionProduct.lean, InjectionPoly.lean, MarkedSymbol.lean, MarkedStar.lean, CoherentSymbol.lean (whole files) | 2153 | smeared (three layered symbol calculi: `IsInjectionPoly` → `IsMarkedPoly`/`HasMarkedSymbol` → `HasCoherentSymbol`) | merge the three symbol calculi into one; golf (2153 lines for ≈50 digest lines). Pitfall: OK — each word is averaged with its own centre before words are multiplied (`IsInjectionPoly.exists_mul`, InjectionPoly.lean:370; `HasMarkedSymbol.mul`, MarkedSymbol.lean:480); not line-checked beyond the statements |
| D6.16 | Step (removing clipping; absolute values; closing the lemma) | no statement; `TensorPower.markedScalarSymbol` (OpenAI/RegionPowerSymbol.lean:273, f_θ), clipping `norm_regionPow_sandwich_sub_le` (:435), `HasCoherentSymbol.of_approx` (OpenAI/CoherentSymbolLimit.lean:95), `HasCoherentSymbol.abs` (OpenAI/CoherentSymbolFunction.lean:156), `.skew` (:210), `.freeAlgebra` (OpenAI/CoherentSymbol.lean:377, counted D6.15); helpers: RegionPowerSymbol, CoherentSymbolFunction, CoherentSymbolLimit (whole files) | 858 | smeared | merge into D6.12 (steps, not statements). Pitfall: n/a |
| D6.17 | Step (closing remark: gain and cost on the same states) | — (bookkeeping; the Lean counterpart is the §7 packaging `RelativePinBound`/`SplitSkewBound` in OpenAI/ReplicaTransportPrerequisites.lean, parked in infra) | 0 | none | cut (no declaration expected) |
| (section infra) | — | §6-serving: OpenAI/ReplicaRegionUnion.lean (regional lift for `Entropy.SiteConfig`, ≈322, bridge between the `Config k ι` and `SiteConfig n` encodings, scaffold). Parked, apparently serving §7–§9 or §8 (cite `06-transport`/`07-comparators`/`08-scanner`; ≈19635 total): Replica*Transport* (≈4410), ReplicaGood*/ReplicaJoint*/ReplicaComponent*/ReplicaExcitation*/ReplicaLowDefect*/ReplicaPinned*/ReplicaPrevector*/ReplicaSymmetric{Band*,MeanTreeProduct}/ReplicaLaminarBandMetrics/ReplicaMetricCutoffNorm/ReplicaDefect/…, Bell* (≈1781, the D6.7 workaround), CoherentLog* (≈826, §7 log passage), SchurLabel{Tails,Cutoff,Moments,MomentBounds,SectorMass}, MergeExponential, PairMerge*, PhysicalMergeHolder, CompatiblePhysicalLabel, MatchedSchurCutoffs, SupportedSubsystemLabelDimension, UniformBellLabel, GlobalSchmidtBellPrevector, GoodAuxiliaryLabelCompression, AddedSiteTensorInsertionSymmetry, GroupAlgebraProductCoordinates, SubsystemLabelCoordinates, TensorPowerPartialTrace, RegionalReplicaMetric (full list in mapped.txt) | 1393 | none | classify in the reverse pass after the §7/§8/§9 maps; none is used by D6.1–D6.17 except `ReplicaRegionUnion` (scaffold: cut once the encodings of V are unified) |
| (section infra, reverse pass) | — | 5 decls: `normalizePosSemidef`, `normalizePosSemidef_posSemidef`, `normalizePosSemidef_trace`, `trace_re_smul_normalizePosSemidef`, `commute_normalizePosSemidef` (OpenAI/PositiveSemidefiniteNormalization.lean:50-119); 7 decls: `taggedInterleavings`, `filters_eq_nil_left`, `filters_eq_nil_right`, `mem_taggedInterleavings_iff`, `nodup_taggedInterleavings`, `length_taggedInterleavings`, `length_filterMap_add` (OpenAI/TaggedInterleavings.lean:27-105) | 243 | — | inline into S06 PairMergeMoment user (normalizePosSemidef: ρ/tr ρ); owner anchor to be assigned; inline into S06/S09 PoissonWordThinning anchor (digest 06, 09 mention interleavings); consider Mathlib List.Sublist/shuffle |

## 07-transport.md

Lines now (section total): 13047

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D7.1 | Def (`transport:mean-def`) | `Matrix.geomMean` (OpenAI/WeightedGeometricMean.lean:29); positivity helpers `Matrix.PosDef.whiten`, `Matrix.PosDef.geomMean` (lines 42, 47) | 51 | faithful (ℂ-only: `Matrix n n ℂ`; p is a bare ℝ, restricted to [0,1] at use sites) | keep; Standard? (Kubo–Ando): library tree, no Mathlib match found by atlas search (only scalar AM-GM), Physlib search pending |
| D7.2 | Def (`transport:tree`) | `Matrix.MeanTree` (OpenAI/FiniteMeanTree.lean:72), `.eval` (:87), `.weight` (:100), `weight_nonneg`, `sum_weight` (:125), `posDef_eval` (:146); file lines 1–154 | 154 | faithful (leaf labels may repeat, weight = sum over leaves with that label; parameter in `unitInterval`; edge-weight-0 contraction is not built in, positivity of weights is the hypothesis `IsAdmissible`) | keep |
| D7.3 | Lemma 7.1 (`transport:means`) | No single statement. Items: 1 `Matrix.MeanTree.eval_star_conj` (FiniteMeanTree.lean:171) over vertex `Matrix.geomMean_star_conj` (WeightedGeometricMean.lean:69); 2 `eval_mono` (:184) over `geomMean_mono_right/left` (WGM:181/193); 3 `eval_smul` (:204) over `geomMean_smul` (WGM:126); 4 `re_dotProduct_eval_le` (:246) over `re_dotProduct_geomMean_le` (WGM:258), `re_dotProduct_rpow_mulVec_le` (WGM:209); 5 `smul_le_eval` (:306); 6 `eval_listProd_ofFn` (:428), `commute_eval_band` (:450), vertex `geomMean_mul_of_commute` (WGM:297); symmetry `geomMean_comm` (WGM:150); idempotence `geomMean_self` (:277), `eval_const` (:290). Helpers: WeightedGeometricMean.lean (lines 52–346), FiniteMeanTree.lean (lines 155–459), PosSemidefCommute.lean (whole), DiagonalJensen.lean (whole; `Matrix.diagonal_jensen_of_convexOn`) | 730 | smeared (items 1–6 are six separate theorems; route faithful except D7.3.3–D7.3.4: monotonicity of C ↦ C^p comes from Mathlib `CFC.rpow_le_rpow` (WGM:181), not from the integral formula; the integral formula is proved separately in PowerDerivative.lean for D7.5) | restate as one Lemma 7.1 with six numbered parts (or six named lemmas `lemma_7_1_i`); items 1–4: Standard, library tree (Kubo–Ando), replace-by `CFC.rpow_le_rpow` for D7.3.4. Pitfall: OK — item 6 takes `hcomm j j' g g'` for g≠g' over all pairs of leaves (FiniteMeanTree.lean:428); p in [0,1] enforced via `Icc` hypotheses at vertex lemmas |
| D7.4 | Def | `IsNPositiveMap` (OpenAI/NPositiveMap.lean:52), `nPositiveAmpliation` (:32); positive-map layer `IsPositiveMap` (OpenAI/PositiveMap.lean:32), `IsPositiveMap.traceAdjoint` (:148); whole files NPositiveMap.lean, PositiveMap.lean | 438 | overbuilt (k-indexed family `IsNPositiveMap k` and a separate `IsPositiveMap` layer where the paper has one notion CP = all k; no `IsCompletelyPositive`/unital def; only k=1,2 are consumed: Kadison–Schwarz needs k=2) | replace-by Mathlib `CompletelyPositiveMap` (Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap, found by atlas search; applicability to `Matrix n n ℂ` not verified, search pending); else library tree. Standard. |
| D7.5 | Lemma 7.2 (`transport:cp`) | No single statement. `Matrix.normalizedDerivMap` (MeanDerivative.lean:248), `MeanTree.leafMap` (TreeDerivative.lean:236), `MeanTree.isNPositiveMap_leafMap` (:255, CP, ∀ k), `leafMap_one` (:264, unital), `sandwich_derivLabel_eq_smul_leafMap` (:244), `hasFDerivWithinAt_eval_update` (:157), chain rule `leafMap_node_left/right` (:322/:335) with `edgeMapLeft/Right` (:285/:291); vertex: `isNPositiveMap_geomMeanDerivRight/Left` (MeanDerivative.lean:226/237); power derivative `Matrix.rpowFDeriv` (PowerDerivative.lean:249), `rpow_eq_integral` (:122), `hasFDerivWithinAt_rpow` (:403), `isNPositiveMap_rpowFDeriv` (:436); block clause `MeanTree.isBlockDiagonalMap_leafMap` (BlockDiagonal.lean:461). Files: MeanDerivative.lean, TreeDerivative.lean, PowerDerivative.lean, ResolventFunctionalCalculus.lean, BlockDiagonal.lean (whole) | 1697 | smeared (statement split over CP / unital / leaf identity / block clause; proof follows D7.5.1–D7.5.7: integral formula and Fréchet derivative of the power, CP of sandwich integrals, symmetry for the first child via `geomMeanDerivLeft`, unitality by homogeneity, chain rule by `normalizedDerivMap_comp`, block case; ℂ-only) | restate as one Lemma 7.2; golf (BlockDiagonal.lean 472 lines and PowerDerivative.lean 480 lines are the bulk). Pitfall: OK — edge maps divide by the edge weight (`edgeMapLeft`: `1-p`, `edgeMapRight`: `p`, TreeDerivative.lean:285-291), `leafMap` divides by terminal weight `T.weight j` (:236), `leafMap_node_*` composes them. Standard? Daleckii–Krein part: standard, search pending for Mathlib/Physlib Fréchet derivative of matrix rpow |
| D7.6 | Def (`transport:fourier-density`) | `Real.sinhRatio` (OpenAI/SinhRatioDensity.lean:65), `Real.sinhRatioDensity` (:70), `Transport.fourierWeight` = m_{1/4} (OpenAI/Transport/Defs.lean:149); SinhRatioDensity.lean lines 1–78, Transport/Defs.lean lines 149–153 | 83 | faithful (g_s with value 2s at 0 via `if z = 0`; m_s explicit; real argument only, a separate `Complex.sinhRatioDensity` is counted in D7.7) | keep; Standard? (rescaled Bhatia–Parthasarathy kernel): library tree |
| D7.7 | Lemma 7.3 (`transport:fourier`) | No single statement. Item 1: `Complex.integral_exp_mul_sinhRatioDensity` (OpenAI/SinhRatioFourier.lean:505), positivity `Real.sinhRatioDensity_pos` (SinhRatioDensity.lean:117), total mass `Real.integral_sinhRatioDensity` (:208). Item 2: `Complex.integral_exp_mul_qPlus` / `qMinus` (SinhRatioShift.lean:241/254), bound `Complex.norm_sinhRatioDensity_shift_le` (SinhRatioDensity.lean:256), shifted-contour core `integral_exp_mul_sinhRatioDensity_shift` (SinhRatioShift.lean:122); contour `rectBoundaryIntegral_fourierIntegrand` (SinhRatioFourier.lean:265). Files: SinhRatioFourier.lean, SinhRatioShift.lean (whole), SinhRatioDensity.lean lines 79–294 | 1069 | smeared (item 2 is three declarations; q_± defined only inside `ErrorFourier.qDensity` (counted in D7.23); proof follows D7.7.1–D7.7.7: poles and residues, rectangle contour, shift, explicit bound; ℝ/ℂ native) | restate as one Lemma 7.3 with `q_±` defined once; golf (1 069 lines for a classical contour computation). Standard? item 1 classical: library tree (no Mathlib match for Fourier transform of 1/cosh found, search pending). Pitfall: OK — bound is stated at s=1/4 against m_{1/4} (not m_{1/8}): `norm_sinhRatioDensity_shift_le` SinhRatioDensity.lean:256 |
| D7.8 | Def (`transport:band-metric`) | `TensorPower.ReplicaTransport.bandMetric` (OpenAI/ReplicaTransportSetup.lean:108, a one-line alias of §6 `leafMetric`, OpenAI/ReplicaSimilarity.lean:101), `symBandMetric` (:119, bandMetric extended by identity off `symProj`); lemmas ReplicaTransportSymmetricMetric.lean lines 1–189 (positivity `posDef_bandMetric` :90, `posDef_symBandMetric` :98, commutation, `crossBandCommute_iff` :288) | 206 | drift (paper: A=(W_P^{-1}W_F^{-1}W_Y)^2 an operator on S_k=Sym^k V; Lean: operator on the full tensor space `Config k …` with S_k as the range of `symProj`, so every metric is padded by `Π A + (1-Π)`) | restate: define on a Sym^k type once; cut `symBandMetric` and its padding lemmas after the encoding is unified; `bandMetric` alias merge into D6.8 `leafMetric` |
| D7.9 | Def (`transport:terminal-weights`, `transport:tree-figure`) | `TransportData` (OpenAI/ReplicaTransportSetup.lean:159), `PYF` (:70), `Move` (:84), `TransportData.IsAdmissible` (:185), `CrossBandCommute` (:195), `oldMetric`/`newMetric` (:202/:208), `tree` (:213), `input` (:217), `rootPath` (:223); `MeanTree.interpTree` (OpenAI/Transport/Defs.lean:82), `interpInput`, `interpRoot`, `choiceRoot`; terminal weights `MeanTree.weight_interpTree_old/new` (Transport/Derivative.lean:94/105); `isPartition_leafPart`, `posDef_input`, `weight_tree_pos` (ReplicaTransportStates.lean:95/103/131). Files: Transport/Defs.lean lines 1–114, Transport/Derivative.lean lines 45–151, ReplicaTransportSetup.lean lines 1–50, 70–107, 159–228, ReplicaTransportStates.lean lines 1–142 | 516 | faithful (history tree, choice trees, moves stay/toP/toF, cross-band commutation and π_j match; inherits the padded S_k encoding of D7.8; ℂ-only). Pitfall (π_old=(1-p)w_h) checked in D7.14/D7.15 | keep. Pitfall: OK — `weight_interpTree_old` gives (1-p)·w_h, `weight_interpTree_new` gives p·w_h·q_{c given h} (Transport/Derivative.lean:94,105); cross-band commutation covers all pairs of leaves j,j' (ReplicaTransportSetup.lean:195) |
| D7.10 | Def (`transport:move-eta`) | `logDim` (OpenAI/ReplicaTransportSetup.lean:125, log(e·∏ dim)), `moveEta` (:130, η = I(x:F given P) or I(x:P given F) via `FiniteProduct.conditionalMutualInformation`, OpenAI/FiniteProductConditional.lean:30) | 12 | drift (paper: η = S(x given P)+S(x given Y0)=I(x:F given P), entropy of Arealaw `SubState`; Lean: η is defined directly as a conditional mutual information of `FiniteProduct.entropy` on `EuclideanSpace ℂ (∀ v, Fin (n v))` with regions `Finset V` — a second encoding of regions and entropy, not Arealaw `Reg`/`SubState.regionEntropy`/`mutualInfo`) | restate in Arealaw vocabulary (`mutualInfo`, `Reg`); cut `FiniteProduct` bridge afterwards. The smallness constants (t<1/4, aℓ≤c₀) enter as hypotheses of D7.14 |
| D7.11 | Def | `EnergyTerms` (OpenAI/ReplicaTransportSetup.lean:267), `PYF.Contains` (:137), `SplitsToP/F` (:140/:144), `splitBandEta` (:151), `TransportData.SupportCompatible` (:280), `splitLeaves` (:287), `splitEta` (:294); file lines 137–158 and 267–300 | 56 | faithful (contractions with designated supports; exceptional band encoded by `SupportCompatible`; η_{i,j} summed over the unique exceptional band; again the second entropy encoding of D7.10) | keep |
| D7.12 | Step (`transport:replica-energy`) | `EnergyTerms.replicaEnergy` (OpenAI/ReplicaTransportSetup.lean:301), `copyMean` (OpenAI/ReplicaSimilarity.lean, §6); commutation `commute_bandMetric_copyMean_of_contains` (ReplicaTransportEnergy.lean:179), `commute_replicaMetric_copyMean` (:165), `commute_permOp_subsystemPerm_copyMean_of_subset` (:137), `TransportData.commute_input_copyMean_of_not_mem_splitLeaves` (:320). Files: ReplicaTransportEnergy.lean lines 137–198 and 307–352; ReplicaTransportSetup.lean lines 301–306 | 114 | faithful (D7.12.1: invariance of Σ_r h_{i,r} under permutations of the copies of Q⊇D and commutation with permutations of the complement; D7.12.2: metric is a function of Schur labels; Lean covers D⊆Q or D disjoint from Q) | keep |
| D7.13 | Def (`transport:coherent-measure`) | `realCoherentIntegral` (OpenAI/ReplicaTransportSetup.lean:58, real-valued, via Haar on `unitaryHaar Ω` and θ=U·e), `symDim` (:51); second and third encodings: `TensorPower.coherentIntegral` (OpenAI/CoherentMeasure.lean:23, complex-valued), `TensorPower.coherentMeasure` (OpenAI/ReplicaTransportCoherentMeasure.lean:146, measure on `CoherentSphere`, used by §9). Files: CoherentMeasure.lean, ReplicaTransportCoherentMeasure.lean (whole), ReplicaTransportSetup.lean lines 51–69 | 280 | drift (paper: dμ_σ=D_k Tr(σ P_θ)dθ with dθ Haar probability on the unit sphere; Lean: three parallel encodings, all via image of Haar measure on the unitary group under U ↦ U e_a, and `coherentMeasure` re-proves the sphere measure; D_k = `symDim` as a finrank, no binomial formula) | restate with the sphere measure once (`coherentMeasure`) and derive `realCoherentIntegral`/`coherentIntegral` from it, or delete them; Standard: library tree (de Finetti / coherent-state measure) |
| D7.14 | Proposition 7.4 (`prop:transport`) | `TensorPower.ReplicaTransport.transport` (OpenAI/ReplicaTransport.lean:53, parts (a),(b),(c) and integrated (b)); duplicates of the same statement: `transport_of_relativePin_of_splitSkewBound` (OpenAI/ReplicaTransportProposition.lean:54, without integrated clause), `transport_of_splitSkewBound` (OpenAI/ReplicaTransportRelativePinBound.lean:251), `transport_finite_family` (ReplicaTransportFiniteFamily.lean:43, counted in D7.26). Defining data: `filteredNormSq`, `filteredVector`, `transportState` (OpenAI/Transport/Defs.lean:121/126/136), `TransportData.state` (ReplicaTransportSetup.lean:229), `exactDerivative` (:243), `entropyGain` (:256), `energyError` (:317); `hasDerivAt_exactDerivative` (ReplicaTransportStates.lean:174). Files: ReplicaTransport.lean, ReplicaTransportProposition.lean (whole), Transport/Defs.lean lines 115–143, ReplicaTransportSetup.lean 229–266 and 307–330, ReplicaTransportRelativePinBound.lean 251–277, ReplicaTransportStates.lean 174–186 | 319 | faithful (one theorem states (a),(b),(c) and the integrated form; proof is assembly of D7.15–D7.26; stated four times in slightly different forms; ℂ-only, over `Config k … → ℂ` with S_k as `symmetricSubspace`) | keep `ReplicaTransport.transport`; cut `transport_of_relativePin_of_splitSkewBound` and ReplicaTransportProposition.lean (superseded, refcount 2), inline `transport_of_splitSkewBound`. Pitfall: OK — constants `c₀ Cent eent Cen een` are ∃ before the data; `β r` are ∃ after the data and before `k pre p`, so they depend on the fixed data but not on p, pre or the replica state; energy error has W_i(p)·Σπ_j via `energyError` (ReplicaTransportSetup.lean:317); ℓ bounds log(e dim D_i) only when `splitLeaves` nonempty (ReplicaTransport.lean:53) |
| D7.15 | Step (`transport:node-p-derivative`, `transport:root-p-derivative`) | `Transport.exists_hasDerivAt_interpPath` (OpenAI/Transport/Derivative.lean:208), `hasDerivAt_eval_bind` (:152), `hasDerivAt_geomMean_param` (Transport/PathDerivative.lean:190), `geomMeanDerivLeft_sandwich_log` (PathDerivative.lean:210). Files: PathDerivative.lean (whole), Derivative.lean lines 1–44 and 152–240 | 347 | faithful (V unitary is not introduced; instead ∂_pM=A^{1/2}C^p log C A^{1/2} and the old-child derivative is (1-p)·that, as in D7.15.2–D7.15.3; root via `hasDerivAt_eval_bind` and path leaf maps D7.15.4) | keep. Pitfall: OK — coefficient is `T.weight h` = w_h, not (1-p)w_h (Transport/Derivative.lean:208; the (1-p) is divided out in `geomMeanDerivLeft_sandwich_log`, PathDerivative.lean:210) |
| D7.16 | Step (`transport:norm-derivative`, `transport:exact-derivative`) | `Transport.hasDerivAt_neg_log_filteredNormSq` (OpenAI/Transport/Derivative.lean:252), `hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt` (Transport/NormDerivative.lean:390), `relation_eigen` (:339), `coeff_identity` (:274), `integral_fourierWeight_mul_re_sum` (:85); density matrices `posSemidef_transportState`, `trace_transportState` (Derivative.lean:301/306), `posSemidef_traceAdjoint_leafMap`, `trace_traceAdjoint_leafMap` (OpenAI/LeafStates.lean:43/51), `posSemidef_state`, `trace_state` (ReplicaTransportStates.lean:143/149). Files: NormDerivative.lean, LeafStates.lean (whole), Derivative.lean lines 241–314, ReplicaTransportStates.lean lines 143–173 | 663 | faithful (eigenbasis Daleckii–Krein, bracket = g_{1/4}(log x_r - log x_t), Fourier formula of Lemma 7.3(1), σ ≥ 0 by CP, Tr σ = 1 by unitality; g_s(ad) is not a separate object — expanded in eigenbasis; fixed s=1/4) | keep (golf: NormDerivative.lean 499 lines) |
| D7.17 | Step (`transport:relative-factorization`) | `TransportData.cfc_log_relRatio_eq_sum` (OpenAI/ReplicaTransportEntropyGain.lean:295), `bandRelRatio` (:169), `bandRelRatio_eq_eval` (:179), `listProd_whiten` (:76), `Matrix.MeanTree.eval_listProd_ofFn` (FiniteMeanTree.lean:428, counted in D7.3), `Matrix.cfc_log_listProd_ofFn` (OpenAI/CfcLogListProduct.lean:37), `Matrix.PosDef.cfc_log_mul` (OpenAI/CfcLogAdditive.lean:50). Files: CfcLogAdditive.lean, CfcLogListProduct.lean (whole), ReplicaTransportEntropyGain.lean lines 1–112, 169–217, 295–342 | 324 | smeared (D7.17.1–D7.17.3 are spread over `eval_listProd_ofFn`, `bandRelRatio_eq_eval` (congruence, 17.3) and `cfc_log_relRatio_eq_sum` (17.2); no declaration states both C_h=∏C_{h,g} and log C_h=Σ log C_{h,g} plus the choice-tree form) | golf; merge `commute_rpow_of_commute`, `commute_eval_of_commute` (ReplicaTransportEntropyGain.lean:57/64) into library tree (commutation lemmas); keep `cfc_log_relRatio_eq_sum` as `step_7_17` |
| D7.18 | Step (`transport:conditional-pin`) | `TransportData.smul_coherentProj_le_bandRelRatio` (OpenAI/ReplicaTransportEntropyGain.lean:218, D7.18.3 via `smul_le_eval`); common b_k over moves is taken inside `exists_entropyGain_le_exactDerivative_of_relativePin` (:343, D7.18.2); bridge to Lemma 6.3: `RelativePinBound` (OpenAI/ReplicaTransportPrerequisites.lean:48, a Prop restating Lemma 6.3) and its proof `TensorPower.ReplicaTransport.relativePinBound` (OpenAI/ReplicaTransportRelativePinBound.lean:166). Files: ReplicaTransportPrerequisites.lean lines 1–67, ReplicaTransportRelativePinBound.lean lines 1–250, ReplicaTransportEntropyGain.lean lines 218–257 | 357 | smeared (C_{h,g}≥b_k exp(ka[Σqη − Ca^{1/4}ℓ^C])P_θ is never stated as one inequality: per-move pin is the hypothesis, the common b_k and common error are chosen inside the D7.20 theorem; `RelativePinBound` is a second statement of Lemma 6.3 (D6.10)) | restate as one lemma, derive from D6.10 directly; cut `RelativePinBound` Prop and the bridge file once D6.10 is stated in the needed form (≈250 lines of translation). Standard? no. Pitfall: n/a |
| D7.19 | Step (`transport:log-jensen`) | `TensorPower.coherentAverage` (OpenAI/CoherentLogBasic.lean:128, the map 𝒬_k), `coherentAverage_log_le_of_pos` (OpenAI/CoherentLogJensen.lean:198), `coherentAverage_log_le` (OpenAI/ReplicaTransportCoherentLog.lean:35), `le_coherentAverage_inv` (OpenAI/CoherentLogAverage.lean:134), `logKernel`/`cfc_logKernel` (OpenAI/CoherentLogKernel.lean:33/154). Files: CoherentLogAverage.lean, CoherentLogBasic.lean, CoherentLogJensen.lean, CoherentLogKernel.lean (whole), ReplicaTransportCoherentLog.lean lines 1–46 | 872 | faithful (𝒬_k as `coherentAverage`; unitality, positivity; inverse inequality by the pointwise sandwich g(X−g^{-1})P_θ(X−g^{-1}) ≥ 0 instead of the 2×2 Schur complement in D7.19.2, with filler c on the complement of S_k; log via resolvent integral D7.19.4; the "logarithm operator monotone" clause is not separately stated) | keep; golf (826 lines); Standard (operator Jensen, Choi–Davis): library tree, no Mathlib match found, search pending |
| D7.20 | Step (`transport:log-relative`, `transport:entropy-gain`) | `TransportData.exists_entropyGain_le_exactDerivative_of_relativePin` (OpenAI/ReplicaTransportEntropyGain.lean:343), `realCoherentIntegral_sub_log_le_re_trace_mul_log` (OpenAI/ReplicaTransportCoherentLog.lean:47), `log_symDim_isBigO` (:132), `integrable_fourierWeight_mul_trace_state` (EntropyGain:258), `continuous_entropy`, `continuous_moveEta` (:122/147). Files: ReplicaTransportEntropyGain.lean lines 113–168, 258–294, 343–582; ReplicaTransportCoherentLog.lean lines 47–146 | 433 | drift (paper: operator inequality log C_{h,g} ≥ ka·𝒬_k(Σqη − Ca^{1/4}ℓ^C) + (log b_k − log D_k)I, then expectation in σ; Lean: the pin is turned directly into the scalar trace inequality ∫φ dμ_ρ − log D_k ≤ Tr(ρ log X) for each band, never forming 𝒬_k(…) as an operator; common b_k from a sum of −log b over all (h,c,g) instead of a minimum; β_k is O(log(k+1)) not the explicit K/2(log D_k − log b_k)) | restate as the operator inequality of D7.20 then take traces (prove); Pitfall: OK — D_k enters once additively as −log D_k in `realCoherentIntegral_sub_log_le_re_trace_mul_log` (ReplicaTransportCoherentLog.lean:47) and b_k is common over finitely many moves (EntropyGain:343) |
| D7.21 | Step (`transport:unsplit-block`, `transport:rank-deficient-B`, `transport:skew-square`) | `Matrix.Transport.exists_auxBlock` (OpenAI/Transport/EnergyBlock.lean:181), `auxY`, `auxZ` (:53/58), `kerProj` (:65), `skewSquare` (OpenAI/Transport/Defs.lean:144), `posSemidef_copyMean` (ReplicaTransportEnergy.lean:219, T^*T=h̄). Files: EnergyBlock.lean lines 1–297, Transport/Defs.lean lines 144–148 | 302 | drift (paper: T:S_k→D=ran T_i the last-copy reduction, B on D, polar decomposition on commuting leaves, SVD identity; Lean: T=√h̄ as a square matrix on the whole space, B=… built with a kernel projector `kerProj`, Y,Z defined by formulas on the whole space; the commuting case is a case split `by_cases Commute A h` with B=A) | restate on T=h̄^{1/2} without kerProj if possible; keep result `exists_auxBlock`; no Pitfall check needed for the exceptional band (that is D7.24.1) |
| D7.22 | Step (`transport:block-rotation`) | `Transport.sum_weight_smul_leafMap_rotation` (OpenAI/Transport/EnergyBlock.lean:410, 2 sinh(ad/2)L = Σπ_jΦ_j(K_j) in the form M^{1/2}LM^{-1/2}−M^{-1/2}LM^{1/2}), `sum_derivLabel_commutator` (:394), `sum_derivLabel_congr` (:381), `geomMeanDeriv_congr` (:314), `hasDerivAt_star_exp_mul_mul_exp` (:298); block structure of M_{i,j}, K_{i,j} inside `norm_sq_errorVec_le` (:467) using `eval_fromBlocks_diag` (BlockDiagonal.lean:149). File: EnergyBlock.lean lines 298–452 | 155 | smeared (rotation identity is one declaration; K_{i,j}, block diag(𝓜,𝓑_i), lower-left Y−Z and K^*K are not stated, only used inside D7.23; proof by rotation covariance e^{itL}, as D7.22.2–D7.22.3) | golf; restate K_{i,j} and the block facts as a declaration of their own |
| D7.23 | Step (`transport:E-def`, `transport:cp-schwarz`, `transport:block-bound`) | `Matrix.Transport.norm_sq_errorVec_le` (OpenAI/Transport/EnergyBlock.lean:467, ‖E_±v‖² ≤ ¼ W Σπ_j∫m_s Tr(σ_{j,u}𝖣_{j})), `errorOp` (:453); Fourier machinery `nsq_conj_sub_le` (OpenAI/Transport/ErrorFourier.lean:452), `qDensity` (:131), `norm_qDensity_le` (:135), `integral_qDensity_mul_inner` (:237), eigen-decomposition `eigConj`, `imagPow_eq_eigConj`; Kadison–Schwarz `kadison_schwarz_twoPositive` (OpenAI/TwoPositiveSchwarz.lean:95). Files: EnergyBlock.lean lines 453–560, ErrorFourier.lean, TwoPositiveSchwarz.lean (whole) | 868 | faithful (D7.23.1–D7.23.6: h_±(ad) applied to the rotation identity, density q_± , Cauchy–Schwarz over (j,u), Schwarz for the unital 2-positive leaf map, constants ¼; Schwarz stated for 2-positive maps only, which is weaker hypothesis than CP) | keep; golf ErrorFourier.lean (598 lines). Standard (Schwarz for unital CP): library tree; no Mathlib match found (Mathlib has Cauchy–Schwarz for positive linear maps in `PositiveLinearMap.cauchy_schwarz_mul_star` only), search pending. Pitfall: OK — bound has (Σ_{j∈S}π_j)·Σ_{j∈S}π_j∫…, i.e. W_i twice (EnergyBlock.lean:467) |
| D7.24 | Step (`transport:symbol-cost`) | `TransportData.exists_trace_skewSquare_le_of_splitSkewBound` (OpenAI/ReplicaTransportEnergy.lean:386), `skewSquare_input_eq_symBandMetric` (:353, D7.24.1), `splitEta_eq_splitBandEta` (:372); bridge to Lemma 6.4: `SplitSkewBound` (OpenAI/ReplicaTransportPrerequisites.lean:68, a Prop restating Lemma 6.4), proof `splitSkewBound` (OpenAI/ReplicaTransportSplitSkewBound.lean:325) via `eventually_re_trace_skewSquare_le` (:202); padded-space extension lemmas `proj_mul_skewSquare_extension`, `mul_skewSquare_symBandMetric` (OpenAI/ReplicaTransportSymmetricMetric.lean:199/271). Files: ReplicaTransportSplitSkewBound.lean (whole), ReplicaTransportEnergy.lean lines 54–136 and 353–464, ReplicaTransportSymmetricMetric.lean lines 190–296, ReplicaTransportPrerequisites.lean lines 68–83 | 728 | faithful (D7.24.1 cancellation of the non-exceptional bands, D7.24.2–D7.24.3 apply Lemma 6.4 with ℓ, D7.24.4 uniformity in σ; one common r_k = Σ abs r over split pairs). `SplitSkewBound` is a second statement of D6.12 | keep the theorem; cut `SplitSkewBound` Prop and the 123-line `eventually_re_trace_skewSquare_le` bridge once D6.12 is stated as needed; the 107-line extension block disappears with the padded encoding (D7.8). Pitfall: n/a |
| D7.25 | Step (`transport:energy-similarity`) | `Transport.re_star_dotProduct_mulVec_le_energy` (OpenAI/Transport/EnergyBlock.lean:603, one term), `re_inner_errorVec_eq` (:561), `re_inner_add_add_ge` (:588); sum over i and assembly with D7.23–D7.24: `TransportData.exists_energy_le_of_splitSkewBound` (OpenAI/ReplicaTransportEnergy.lean:477), `re_star_filteredVector_dotProduct` (:231). Files: EnergyBlock.lean lines 561–626, ReplicaTransportEnergy.lean lines 1–53, 199–306, 465–640 | 350 | faithful (D7.25.1 cancellation of B^{±s}, D7.25.2 the ½/3/2 inequality, D7.25.3 eigenvector hypothesis used only at the sum, D7.25.4 W_i²·r_k remainder) | keep. Pitfall: OK — eigenvector hypothesis `E.replicaEnergy k *ᵥ pre = E₀ • pre` is used only in the final sum (ReplicaTransportEnergy.lean:477) |
| D7.26 | Step | Smoothness/continuity: `Transport.continuous_filteredNormSq_interpPath` (OpenAI/Transport/Derivative.lean:351), `exists_abs_exactDerivative_le` (:387), `log_filteredNormSq_sub_eq_integral` (:427), `TransportData.integral_le_log_filteredNormSq_sub` (OpenAI/ReplicaTransportIntegrated.lean:37), `intervalIntegrable_entropyGain` (OpenAI/ReplicaTransportIntegratedEntropy.lean:193), `Transport.hasDerivAt_neg_log_filteredNormSq_leafPerturbation` (Transport/LeafDerivative.lean:113, used to prove integrability of the gain in p); finite sequences of rounds: `transport_finite_family` (OpenAI/ReplicaTransportFiniteFamily.lean:43). Files: ReplicaTransportIntegrated.lean, ReplicaTransportIntegratedEntropy.lean, ReplicaTransportFiniteFamily.lean, Transport/LeafDerivative.lean (whole), Transport/Derivative.lean lines 315–469 | 718 | smeared (integrated form is the last clause of `ReplicaTransport.transport`, endpoint continuity and boundedness in four theorems; Lean adds an integrability-in-p argument the paper does not need, via LeafDerivative; finite-family theorem is a fifth statement of Prop 7.4) | golf; inline `transport_finite_family` into D7.14 or into §9 where it is used (OpenAI/Scan/ActualRoundTransport.lean); LeafDerivative.lean + IntegratedEntropy.lean (382 lines) likely cut if integrability of the entropy term in p is not required by D9 |
| D7.27 | Step | — (the state σ_{h,u} of leaf (h,old) is the single definition `TransportData.state` (OpenAI/ReplicaTransportSetup.lean:229), used in both `exactDerivative` (:243) and `energyError` (:317)) | 0 | none | keep; no declaration expected |
| (section infra) | — | Transport/Commutant.lean (175; mul-by-commutant lemmas for the padded S_k encoding: `mul_transportState`, `leafMap_mul_right`), Transport/FilteringIntertwine.lean (67), GeometricMeanIntertwine.lean (82), MeanTreeIntertwine.lean (62), MatrixSandwichIntertwine.lean (54) — rectangular-intertwiner transport used for the compressed-coordinate statements of §8/§9 (`ReplicaTransportRootCompression`); outside the import closure of `OpenAI.AreaLaw`: Transport/Intertwine.lean (75), GeometricMeanDerivativeIntertwine.lean (115), MeanTreeDerivativeIntertwine.lean (115), PowerDerivativeIntertwine.lean (111), LeafStateIntertwine.lean (60), SingleKraus.lean (59) | 975 | — | scaffold: cut the six dead files now; the closure ones go with the §8/§9 compression bridge once encodings are unified; Commutant cut with padded encoding |
| (section infra, reverse pass) | — | (whole file, 11 decls) (OpenAI/ProjectionCompressionCfc.lean:44-205) | 230 | — | inline into S07 ReplicaTransportSymmetricMetric user (cfc of P·A·P + (1-P)); owner anchor to be assigned |

## 08-comparators.md

Lines now (section total): 29293

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D8.1 | Def comparator:nesting | no declaration; nesting hypothesis `∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h` is repeated verbatim in every theorem (e.g. `FiniteProduct.eventually_suppliedReplicaPrevector_rough_upper` OpenAI/ReplicaPrevectorRoughUpper.lean:88, OpenAI/SchmidtBellSharpUpper.lean, OpenAI/RegionalRoughLowerNorm.lean:90, OpenAI/BellPinnedProductAction.lean:64, ≥10 sites); consequences (iii)/(ii) commutation: `TensorPower.replicaBandRegions_subset_or_disjoint` (OpenAI/ReplicaLaminarBandMetrics.lean:53), `commute_labelObservables_subsystemPerm_of_laminar` (:94), `replicaPinnedBands_posDef_commute` (:203); helpers: ReplicaLaminarBandMetrics.lean (whole file) | 311 | smeared | restate (one `Status`/`ComparatorData` structure with the two-status nesting field, inlined into D8.8); golf ReplicaLaminarBandMetrics. Pitfall: OK — nesting is quantified over two leaves `j j'` with `g < h` (OpenAI/ReplicaPrevectorRoughUpper.lean:88). 𝕜: ℂ-only. |
| D8.2 | Def comparator:typical-set | `Entropy.typicalSet` (OpenAI/TypicalSet.lean:40) and `Entropy.typicalMass` (:45), `Entropy.exp_le_of_mem_typicalSet` (:86) on a probability vector; matrix side `Matrix.IsHermitian.spectralSelection` (OpenAI/TypicalDensity.lean:180, counted in D8.3), `spectralRestrictionMass` (=z), `Matrix.PosSemidef.typicalSet_normalizedSpectralRestriction_bounds` (OpenAI/TypicalStateFromTail.lean:86), `Matrix.typicalPureState_typicalSet_bounds` (:127); in the upper/lower theorems E is an arbitrary `Finset (Configuration β X)` with only `0 < z` (no window hypothesis); helpers: TypicalSet.lean, TypicalStateFromTail.lean | 241 | smeared | restate (one Def: E, w, z, d_*, p', S'); the Specific data stays in the paper tree. 𝕜: ℂ-only on matrix side (EuclideanSpace ℂ). |
| D8.3 | Step comparator:typical-entropies | `Entropy.typicalSpectrum_entropy_bounds` (OpenAI/TypicalDensity.lean:140) and matrix form `Matrix.PosSemidef.typicalSpectralRestriction_entropy_bounds` (:323); instance `OpenAI.abs_log_card_and_selectedSchmidtEntropy_sub_le` (OpenAI/SelectedSchmidtEntropyBounds.lean:45, specialised to a `Finset (ℤ × ℤ)` lattice with `Fin q` sites); helpers: TypicalDensity.lean (spectral-restriction defs), SelectedSchmidtEntropy.lean (entropy of selected auxiliary marginal) | 495 | faithful | keep `typicalSpectrum_entropy_bounds` (centered window + triangle inequality, as D8.3.1-2); inline the lattice-specialised instance into D8.20/D8.22 uses (golf). Standard?: direct computation. |
| D8.4 | Def comparator:prefix-data | no declaration; hypotheses `regions`, `hnested`, `hdisjoint`, `∀ D ∈ regions, entropy β Ω D ≤ Bsh`, `hmatch` (`1 + log \|Configuration β (D ∆ Q)\| ≤ Bexc`) inline in `FiniteProduct.eventually_suppliedReplicaPrevector_rough_upper` (OpenAI/ReplicaPrevectorRoughUpper.lean:66-100), `eventually_suppliedSchmidtBell_rough_upper` (OpenAI/BellPhysicalRoughUpper.lean:69), `eventually_exists_suppliedSchmidtBell_physicalWitness` (OpenAI/SchmidtBellPhysicalWitness.lean:73) | 0 | smeared | restate (one `PrefixData` structure, inlined into D8.18-D8.20). |
| D8.5 | Def comparator:mgf-data | no declaration; hypothesis `∀ v, \|v\| ≤ r → log (surprisalMoment eigs v) ≤ v * S + K * v^2` repeated inline, with (C₀𝓑, c₀/√𝓑) merged into `(K, r)`: `TensorPower.eventually_suppliedSchmidtBell_sharp_upper` (OpenAI/SchmidtBellSharpUpper.lean:56), `Matrix.exists_replicaExcitationComponent_inverse_sharp_le` (OpenAI/ReplicaComponentInverseSharp.lean:55), `Matrix.exists_replicaMetric_symProj_bandProduct_sharp_lower_norm` (OpenAI/RegionalSharpLowerNorm.lean:69); `OpenAI.surprisalMoment` (eigenvalue form of log Tr ρ^{1-u}) | 0 | smeared | restate (one `MomentData` structure with `𝓑`, `C₀`, `c₀`); regions list `{XU_g, V_g, Y_g, U_g, U_gY_g}` appears as `Fin 3`/`Q = U ∨ U∪Y ∨ Y` cases, not as one list. Pitfall: n/a (no declaration). |
| D8.6 | Def comparator:metrics | no declaration of `Bell_CR`, `𝒱`, `𝒮_k`, `P,F,Y` or `A_{j,g}`: C,R are the sites `some none`/`none` of `addedSiteSpace (addedSiteSpace β E) (Fin E.card)` (OpenAI/AddedSiteSpace.lean:34); `A_{j,g} = ((W Q)⁻¹ * (W F)⁻¹ * W Y)^2` is a `let H := …` written out in each theorem (OpenAI/ReplicaPrevectorRoughUpper.lean:103, OpenAI/RegionalRoughLowerNorm.lean:~100, OpenAI/SchmidtBellSharpUpper.lean:~118); `TensorPower.posDef_bellMetric_factors` (OpenAI/BellMetricFactorPositivity.lean:57); `posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq` (OpenAI/ReplicaDisjointMetricPositivity.lean:75); helpers: AddedSite*.lean (4 files: tensor-power insertion of the auxiliary site and its symmetry/norm) | 581 | smeared | restate (one `leafMetric P Y F` and `meanOfBands`); cut the second site-family encodings (`compressedSiteSpace`, exterior/regional five-factor `ι : Fin 5 → Type`). Note the small-`a` hypotheses differ per theorem (`4t ≤ 1`, `20t ≤ 1`, `6a ≤ 1`), not one `a₀`. Pitfall n/a. 𝕜: ℂ-only. |
| D8.7 | Def (mean tree, ⟨·⟩_av) | `Matrix.MeanTree` (§7) used; `M = ∏_g T.eval …` written inline as `(List.ofFn fun g ↦ T.eval …).prod`; commutation of band roots `TensorPower.replicaMetric_symProj_meanTree_roots_commute` (OpenAI/ReplicaSymmetricBandCommute.lean:97), `replicaMetric_symProj_compressions_posDef_commute` (:60); `M = ∏ M_g` `replicaMetric_symProj_meanTree_eq_product` (OpenAI/ReplicaSymmetricMeanTreeProduct.lean:47); ⟨f⟩_av has no definition (inline `∑ g, ∑ j, T.weight j * …` in OpenAI/SchmidtBellSharpUpper.lean); helpers: the two files | 197 | smeared | restate (def of `M`, `M_g`, `avg`); merge into D8.8. Uses Lemma 7.1 item 6 hypotheses derived in D8.1. 𝕜: ℂ-only. |
| D8.8 | Prop 8.1 | nothing states Prop 8.1; four separately-hypothesised bounds + entropy identity, each repeating the whole hypothesis block: rough upper `FiniteProduct.eventually_suppliedReplicaPrevector_rough_upper` (OpenAI/ReplicaPrevectorRoughUpper.lean:66) [same statement again in `eventually_suppliedSchmidtBell_rough_upper` BellPhysicalRoughUpper.lean:69 and `…suppliedGlobalSchmidtBellPrevector_rough_upper` GlobalSchmidtBellRoughUpper.lean:45]; sharp upper `FiniteProduct.eventually_suppliedReplicaPrevector_sharp_upper` (OpenAI/ReplicaPrevectorSharpUpper.lean:59) [and `TensorPower.eventually_suppliedSchmidtBell_sharp_upper` SchmidtBellSharpUpper.lean:56]; rough lower `Matrix.exists_replicaMetric_symProj_bandProduct_rough_lower_norm` (OpenAI/RegionalRoughLowerNorm.lean:68) [+ `…_three` RegionalRoughLowerThree.lean:118, + `exists_global_schmidtBellPrevector_rough_lower` GlobalSchmidtBellRoughLower.lean:61]; sharp lower `Matrix.exists_replicaMetric_symProj_bandProduct_sharp_lower_norm` (OpenAI/RegionalSharpLowerNorm.lean:69); identity `OpenAI.collarLeaf_entropy_identity` (D8.36); prevector `TensorPower.exists_label_sequence_replicaPrevector` (OpenAI/ReplicaPrevector.lean:331); lines here: GlobalSchmidtBellRoughUpper.lean, GlobalSchmidtBellRoughLower.lean | 348 | smeared | restate (one `prop_8_1` with rough/sharp, upper/lower, identity, quantifiers fixed as in the digest); prove from D8.20, D8.22, D8.35, D8.36; cut GlobalSchmidtBellRoughUpper.lean (outside import closure). Pitfall (i): OK — `δ` (E_def) is a `let` over `v` hence depends on tree and k, never bounded in the statement, OpenAI/RegionalRoughLowerNorm.lean:~118; (ii) OK — `(1-τ)` on g_pre only in lower (RegionalSharpLowerNorm.lean:~127), upper uses full g_post (SchmidtBellSharpUpper.lean:~125); (iii) OK — `gmax` enters only `max 0 (2*S + gmax)` (RegionalSharpLowerNorm.lean:129). Quantifiers: upper `∃ c, ∀ᶠ k, ∀ n Z K U Y T …` constant/threshold before tree and band families — OK; lower is explicit-remainder `∃ c Cf, ∀ k …` (no o_k(1) statement; limit taken later, D8.37). 𝕜: all of it ℂ-only (`Matrix … ℂ`, `EuclideanSpace ℂ`); no ℂ→𝕜 transfer here. |
| D8.9 | Step comparator:label-remainder | `TensorPower.schurSurprisal` (OpenAI/SchurSurprisal.lean:353) — this is Lemma 6.1(5) itself (file belongs to §6/D6.4); lines not counted here; D8.12 uses it via `re_trace_exp_remainder_joint` (OpenAI/HighLabelWindow.lean:110) | 14 | none | replace-by D6.4(5) (`TensorPower.schurSurprisal`); no §8 declaration needed. Standard?: proof in §6. |
| D8.10 | Step comparator:signed-label-moments | `Matrix.PosSemidef.log_re_trace_finKronecker_signed_label_moments_le` (OpenAI/IidSchurSignedMoments.lean:64); general-ρ layer `TensorPower.log_centered_labelEntropy_moments_le` (OpenAI/SchurLabelMomentBounds.lean:122), `PermutationRepresentation.re_trace_mul_exp_centered_labelEntropy_le` (OpenAI/SchurLabelMoments.lean:84, + sign: F≤L), `re_trace_mul_exp_neg_centered_labelEntropy_le` (:130, − sign by weighted Cauchy–Schwarz at 2u); helpers: SchurLabelMoments, SchurLabelMomentBounds, IidSchurExponentialMoments, IidSurprisalMomentExponential, SurprisalProductMoment | 747 | faithful | golf (three layers general ρ → uniform → iid; the paper needs only the iid statement; Standard?: Chernoff-type, − sign trick specific so keep in paper tree). Proof matches D8.10.1-3: + sign via F_Q ≤ L (D8.9), − sign via CS with `2u ≤ r`, `2u ≤ 1`, remainder `(card n)²/2·log(k+1)`. 𝕜: ℂ-only (matrices over ℂ). |
| D8.11 | Def (Schmidt vectors, ψ, B_XC, post_k, 𝖯) | `Matrix.compressedTypicalPureState` (OpenAI/TypicalPureCompression.lean:106) = ψ; `Matrix.selectedBellVector` (OpenAI/TypicalBellPin.lean:77) = B_XC; `Matrix.selectedBellProjection` (:107) = 𝖯; `Matrix.bellPinPostvector` (:130); further encodings of post_k: `TensorPower.selectedBellPost` (OpenAI/ReplicaPinnedSharpTree.lean:103), `FiniteProduct.schmidtBellSitePrevector` (OpenAI/SchmidtBellPrevectorOverlap.lean:62); helpers: TypicalPureCompression.lean, TypicalBellPin.lean | 325 | smeared | merge (one `post_k`, `ψ`, `B_XC`, `𝖯` def; at least four coordinate encodings now: bellPin*, schmidtBellSite*, selectedBellPost, compressedTypical*) then restate. |
| D8.12 | Step comparator:high-label | `TensorPower.exists_label_sequence_mass_entropy_asymptotic` (OpenAI/HighLabelWindow.lean:368), `…pure_norm_entropy_asymptotic` (:431); Chebyshev `surprisalTail_pi_le_variance` (OpenAI/IidSurprisal.lean:151) with `k^{3/4}` window (`…three_quarters_le` :253); exp-Markov via `re_trace_exp_remainder_joint` (HighLabelWindow.lean:110); pigeonhole `exists_labelProj_trace_mass_ge` (OpenAI/SchurSectorMass.lean:59); helpers: HighLabelWindow, IidSurprisal, IidTailThreshold, SchurSectorMass, PureTensorPower | 1031 | faithful | keep; golf (statement is generic ρ with explicit `(k+1)^{\|E\|²}` count; proof follows D8.12.1-4). Standard?: Schur-label typicality — library tree candidate for the iid-concentration part (IidSurprisal, IidTailThreshold). ℂ-only. |
| D8.13 | Step | `TensorPower.replicaPrevector` (OpenAI/ReplicaPrevector.lean:48) = pre_k with only the R label inserted; (a)(b)(c) `replicaPrevector_properties` (:273, private) and `exists_label_sequence_replicaPrevector` (:331); C-label = R-label via `UniformBellLabel.lean`; further prevector encodings `SchmidtBellPrevector.lean:266`, `GlobalSchmidtBellPrevector.lean:48`, `SchmidtBellEnumeratedPrevector.lean:49`; (d) `replicaMetric_normalized_symProj_bandProduct_mem_original_labels` (OpenAI/ReplicaSymmetricBandLabelPreservation.lean:45); helpers: the six files | 1298 | drift | restate; merge the four prevector encodings. (d) paper: D8.13.4 — central label function commutes with every leaf ⇒ V = 1−2π unitary, congruence (Lemma 7.1(1)) ⇒ π commutes with M, M^r; Lean: leaves compressed by one isometry Z onto the symmetric subspace (`Zᴴ * A * Z`), labels shown preserved on the compressed band product directly (ReplicaSymmetricBandLabelPreservation.lean). (a)-(c) faithful (copy symmetry, energy eigenvector, both labels). |
| D8.14 | Step comparator:bell-pin | one copy `Matrix.selectedBellProjection_bellPinPrevector` (OpenAI/TypicalBellPin.lean:136); k copies `Matrix.finKronecker_selectedBellProjection_bellPinPrevector` (OpenAI/TypicalBellPinPowers.lean:98); the same identity again in other coordinates: `FiniteProduct.selectedBellProjection_replicaPrevector_site` (OpenAI/SchmidtBellSitePin.lean:163), `TensorPower.bellPin_schmidtBellPrevector_eq_selectedBellPost` (OpenAI/SelectedBellPostPin.lean:120); helpers: TypicalBellPinPowers, SchmidtBellSitePin, SelectedBellPostPin, SelectedBellPostMass | 731 | faithful | merge (the identity is stated and proved three times, once per coordinate system; keep TypicalBellPinPowers:98, inline the others). Proof = D8.14.1-2 (collapse m=i=l, tensor power). |
| D8.15 | Step comparator:pin-norm | `TensorPower.selectedBellPost_inverse_norm_le_physical` (OpenAI/SelectedBellPostInverseTransport.lean:47) (N² ≥ (z/\|E\|²)^k ‖M̃^{-s} π post‖²); tree/pin action `replicaMetric_meanTree_bellPin` (OpenAI/BellPinnedTreeAction.lean:164), `replicaMetric_bandProduct_bellPin` (OpenAI/BellPinnedProductAction.lean:60); `isStarProjection_bellInsertion_symProj` (OpenAI/BellSymmetricPinProjection.lean:58); helpers: the four files | 541 | drift | golf. paper: P commutes with each A_{j,g} (central label on P ⊇ XC), V = 1−2P unitary, congruence (Lemma 7.1(1)) ⇒ P commutes with M, M^{-s}, N ≥ ‖M^{-s}P pre‖; Lean: literal insertion isometry J (exterior coordinates → original), each leaf intertwines through J, weighted mean and real power transported by intertwining (`replicaMetric_meanTree_bellPin`), contraction. Same conclusion. |
| D8.16 | Step comparator:pinned-metric | `TensorPower.exists_replicaPinnedFactor_le_exp` (OpenAI/ReplicaPinnedMetricUpper.lean:53), `exists_replicaPinnedTree_inverse_norm_bound` (OpenAI/ReplicaPinnedTreeExpectation.lean:73), `exists_replicaPinnedLeaf_expectation_le` (OpenAI/ReplicaPinnedLeafExpectation.lean:100), `replicaMetric_factor_mul_bellInsertion_symProj` (OpenAI/BellPinnedMetricCoordinates.lean:148), `replicaMetric_compressed_bandProduct_bellPin_rpow` (OpenAI/BellPinnedCompressedPowers.lean:62); helpers: BellPinned{MetricCoordinates,CompressedPowers}, ReplicaPinned{MetricUpper,TreeExpectation,LeafExpectation}, BellInsertion{Coordinates,RegisterCoordinates,Symmetry} | 1374 | drift | golf/merge. paper: A_{j,g} restricted to ran 𝖯 equals Ã_{j,g}=(W_U^{-1}W_{UY}^{-1}W_Y)² on the restricted system UYVR (fixed-factor identity D6.7); Lean: never restricts A; defines Ã on a second ('exterior') site family without C,R and relates the two by the insertion J (BellInsertion*), so the 'restricted tree' is an exterior-family tree pulled back. Log formula via leaf-floor (D6.9) as in D8.16.3. |
| D8.17 | Step comparator:post-marginal | `Matrix.partialTraceLeft_typicalPureState_decomposition` (OpenAI/TypicalPureState.lean:281), `Matrix.partialTraceLeft_typicalPureState_le` (:292), `Matrix.entropy_partialTraceLeft_typicalPureState_le` (:302); duplicate on physical regions `FiniteProduct.reducedPure_typicalPureState_le` (OpenAI/FiniteProductTypicalState.lean:183), `entropy_typicalPureState_le` (:197); in compressed coordinates `CompressedTypicalRegionalMarginal.lean:50`, `CompressedTypicalSiteEntropy.lean:46`; helpers: the four files | 776 | faithful | merge (three encodings of ρ_ψ ≤ z⁻¹ρ, S(ρ_ψ) ≤ S/z). Standard?: Standard — concavity of entropy, positivity of remainder; `entropy` concavity is Mathlib/Arealaw candidate: search pending. |
| D8.18 | Step comparator:rough-overlap | `TensorPower.exists_commonLabelCutoff_vector` (OpenAI/CommonSchurCutoffs.lean:200), bell form `exists_commonLabelCutoff_bell_vector` (OpenAI/CommonSchurBellCutoffs.lean:104), compressed `FiniteProduct.eventually_exists_commonLabelCutoff_compressedTypical_bell_vector` (OpenAI/CompressedTypicalCommonBellVector.lean:65), `eventually_commonLabelCutoff_compressedTypicalSite_retains_mass` (CompressedTypicalCommonRetainedMass.lean:67), `eventually_exists_suppliedSchmidtBell_physicalWitness` (OpenAI/SchmidtBellPhysicalWitness.lean:73); exp tails `Matrix.PosSemidef.exists_re_trace_one_sub_labelCutoff_finKronecker_le_exp` (IidSchurLabelExponential.lean:46), `exists_surprisal_upper_tail_pi_le_exp` (IidSurprisalExponential.lean:49); union bound `Matrix.projection_union_bound` (CommonSchurCutoffs.lean:76); helpers: 17 files (cutoff/witness/compressed-typical coordinates) | 2311 | faithful | golf hard (17 files, ≈2300 lines for a 19-line step: the cutoff statement is re-proved in four coordinate systems — generic, Bell, compressed-typical, physical-witness). Proof follows D8.18.1-4 (commuting cutoffs, exp-Markov, finite union bound, normalise). Standard?: standard concentration. |
| D8.19 | Step comparator:actual-cutoffs | `TensorPower.log_dim_bounds_of_subset` (OpenAI/MatchedSchurCutoffs.lean:54), `labelCutoff_subsystemPerm_mul_of_nested` (:104), `toEuclideanLin_labelCutoff_of_matched` (:174); `PermutationRepresentation.dim_le_card_of_labelProj_ne_zero` (OpenAI/SupportedSubsystemLabelDimension.lean:48) (Specht dim ≤ D^k); physical form `FiniteProduct.toEuclideanLin_compressedPhysicalCutoff_of_matched` (OpenAI/CompressedPhysicalMatchedCutoffs.lean:92); helpers: the three files | 433 | faithful | keep; merge the compressed-physical copy. Pitfall: OK — only the matched pair's cutoffs are required to commute (`labelCutoff_subsystemPerm_mul_of_nested` is for one nested pair), OpenAI/MatchedSchurCutoffs.lean:104. Uses Lemma 6.1(2)(3). |
| D8.20 | Step comparator:rough-upper | stated in `FiniteProduct.eventually_suppliedSchmidtBell_rough_upper` (OpenAI/BellPhysicalRoughUpper.lean:69) → coordinate copy `…suppliedReplicaPrevector_rough_upper` (OpenAI/ReplicaPrevectorRoughUpper.lean:66, D8.8); pieces `TensorPower.exists_replicaMetric_compressed_bell_inverse_norm_bound` (OpenAI/BellCompressedInverseNorm.lean:61) (D8.15/16/20.4), `Matrix.MeanTree.re_inner_eval_le_of_forall` (OpenAI/MeanTreeUniformExpectation.lean:87) + `norm_inner_sq_le_rpow_mul_inverse_norm_sq` (:132) (D8.20.2-4), `Real.neg_log_div_le_of_bell_overlap_bound` (OpenAI/BellOverlapLogBound.lean:51) (D8.20.5); helpers: BellPhysicalRoughUpper, BellOverlapLogBound, ReplicaPrevectorRoughUpper, MeanTreeUniformExpectation, BellCompressedInverseNorm | 663 | faithful | merge the two coordinate copies of the statement (ReplicaPrevectorRoughUpper is a wrapper by an enumeration equivalence). Bound `8 s t K (Bsh/z + Bexc)` = 2sW(2Bsh/z+2Bexc) with W=aK, a=2t, as D8.20.5. Uniform-leaf vector Jensen replaces D8.20.2's product form (leaf bounds are the same for every j). 𝕜: ℂ-only. |
| D8.21 | Step comparator:sharp-jensen | `Matrix.MeanTree.re_inner_log_eval_prod_le_of_projection` (OpenAI/MeanTreeProjectionMultibandUpper.lean:46), `re_inner_log_eval_le_of_projection` (OpenAI/MeanTreeProjectionUpper.lean:88), `Matrix.cfc_log_listProd_ofFn` (OpenAI/CfcLogListProduct.lean:37), `Matrix.PosDef.norm_sq_mul_exp_le_norm_rpow_neg_sq_of_normalized_log_le` (OpenAI/InversePowerLogJensen.lean:81), `TensorPower.exists_selectedBellPost_sharp_tree_bounds` (OpenAI/ReplicaPinnedSharpTree.lean:139); helpers: the five files | 710 | faithful | keep; golf. Proof: log of commuting product = Σ logs, concavity, vector Jensen through tree, conditioning cost `-log q_k` as D8.21.1-4. Standard?: Jensen thrice — library tree candidate for the three Jensen lemmas (search pending). |
| D8.22 | Step comparator:sharp-upper | `TensorPower.eventually_suppliedSchmidtBell_sharp_upper` (OpenAI/SchmidtBellSharpUpper.lean:56) (coordinate copy `FiniteProduct.eventually_suppliedReplicaPrevector_sharp_upper` OpenAI/ReplicaPrevectorSharpUpper.lean:59, D8.8); leaf `TensorPower.exists_log_re_inner_replicaPinnedFactor_post_le` (OpenAI/ReplicaPinnedSharpLeaf.lean:305) with Hölder-3 `three_rpow_exp_bound` (:281); operator domination `re_inner_exp_labelEntropy_compressedTypicalSiteState_prod_le` (OpenAI/CompressedTypicalExponentialDomination.lean:48); `Real.neg_log_div_le_of_sharp_bell_bound` (OpenAI/SharpBellOverlapLogBound.lean:70); helpers: SchmidtBellSharpUpper, ReplicaPrevectorSharpUpper, SharpBellOverlapLogBound, ReplicaPinnedSharpLeaf, CompressedTypicalExponential(+Domination), SubsystemLabelExponential, FiniteKroneckerOrder | 1300 | faithful | merge the coordinate copies; golf ReplicaPinnedSharpLeaf (450 lines). Proof = D8.22.1-5 (Hölder 3,3,3; ρ_ψ ≤ z⁻¹ρ giving `-2sG log z`; D8.10 at 3a; assemble). Pitfall: OK — z enters via the operator bound `ρ_ψ ≤ z⁻¹ρ` (`FiniteKroneckerOrder` Kronecker monotonicity), giving `\|log z\|/a`, OpenAI/SchmidtBellSharpUpper.lean:~125 (`- 2*s*G*log z`). Moment hypothesis uses `6a ≤ r` (digest: 3a and shrink c). ℂ-only. |
| D8.23 | Step comparator:defect-mass | `Matrix.PosSemidef.replica_gap` (OpenAI/ReplicaDefect.lean:169), `Matrix.spectralCutoff_replica_gap_mass_ge` (:203), `Matrix.globalReplicaLowDefectProjection_gap_mass_ge` (OpenAI/RegionalLowDefectMass.lean:73), `replicaMetric_normalized_symProj_bandProduct_lowDefect_mass_ge` (OpenAI/RegionalLowDefectProductMass.lean:61), `replicaLowDefectProjection_gap_mass_ge` (OpenAI/ReplicaLowDefectProjection.lean:257); helpers: ReplicaDefect, RegionalLowDefectMass, RegionalLowDefectProductMass, SpectralCutoffMass, ReplicaLowDefectProjection, RegionalLowDefectProjection, ReplicaLowDefectCoordinateCovariance, ReplicaLowDefectSymmetricCoordinates, ReplicaPermutationCovariance, ReplicaMeanIdentityExtension, RegionalAuxiliaryLabels | 1671 | faithful | merge (low-defect projection built three times: replica, regional, global coordinates); proof = D8.23.1-3 (gap per copy, count projection, Markov). Standard?: Markov on the excited-copy count. ℂ-only; H given as matrix with `H - E₀ - gap·(1-\|Ω⟩⟨Ω\|) ≥ 0` (unique-ground-vector form). |
| D8.24 | Step | `Matrix.replicaExcitationProjection` (OpenAI/ReplicaExcitationDecomposition.lean:51), `sum_replicaExcitationProjection` (:126), `replicaDefectCutoff_decomposition` (:242), `permOp_mul_replicaExcitationProjection` (OpenAI/ReplicaExcitationSymmetry.lean:59), `replicaGoodCopy_factorization_of_fixed` (OpenAI/ReplicaGoodCopyFactorization.lean:120), `commute_partialTraceLeft_replicaExcitationComponent` (OpenAI/ReplicaMarginalSymmetry.lean:124); helpers: four files | 677 | faithful | keep; golf ReplicaMarginalSymmetry. Proof = D8.24.1-2 (Π_B product of Q_i/(1−Q_i), invariance under S_{k'}×S_r, ground-state factor). Standard?: standard. |
| D8.25 | Step comparator:restriction-dimensions | `TensorPower.groupedCopies_labelEntropy_bounds` (OpenAI/GroupedLabelEntropy.lean:72) (operator form of Lemma 6.1(4)); `commute_grouped_labelObservables` (OpenAI/GroupedLabelSymmetricSupport.lean:145); `TensorPower.commute_subgroup_labelObservables_of_subset_or_disjoint` (OpenAI/SubsystemLabelCommutation.lean:37); `Real.log_choose_le_mul_binEntropy` (OpenAI/ExcitationSubsetCounts.lean:75, counted D8.31); helpers: GroupedLabelEntropy, GroupedConfigurationTransport, SubsystemLabelCommutation, CommutingExponentialOrder, GroupAlgebraProductCoordinates | 244 | faithful | merge into D6.4(4) (`replicas:group-dimensions`; dimension form lives in OpenAI/GroupedCopies.lean, §6); keep only the operator statement here. Standard?: Standard — library tree. |
| D8.26 | Step comparator:whole-inverse | `TensorPower.exists_replicaMetric_inv_square_le_exp` (OpenAI/ReplicaWholeInverse.lean:56), `exists_replicaMetric_inv_square_le_grouped_exp` (OpenAI/ReplicaGroupedInverse.lean:157), `exp_neg_whole_labelEntropy_le_exp_grouped` (:78), `Matrix.IsHermitian.re_dotProduct_exp_add_le_of_compressed_exp_le` (OpenAI/InvariantExponentialComparison.lean:78); helpers: the three files | 146 | faithful | keep; golf. Pitfall: OK — binomial exponent is exactly `2t = a` (`(k.choose r) ^ (2*t)`, OpenAI/ReplicaGroupedInverse.lean:~170), not the paper's weaker `Ca`; no single-site projector commuted through A (operator inequality evaluated on u_B afterwards). |
| D8.27 | Step comparator:good-auxiliary | `Matrix.replicaExcitationComponent_goodAuxiliary_labelEntropy_lower` (OpenAI/ReplicaGoodAuxiliaryLabelBound.lean:72); `subgroup_signedLabelEntropy_symProj_nonneg` (OpenAI/GroupedLabelSymmetricSupport.lean:110) (G^bad ≥ 0); `groupHom₂_labelProj_dim_le` (OpenAI/BadCopyLabelDimension.lean:76) (F^bad ≤ r log d_*); joint form `Matrix.replicaExcitationComponent_exp_good_le_without_auxiliary` (OpenAI/ReplicaJointAuxiliaryExponential.lean:241), `copyPerm_groupedGood_auxiliaryPair_exp_compression` (OpenAI/GoodAuxiliaryPairCompression.lean:103), `replicaExcitationComponent_exp_grouped_le_good` (OpenAI/ReplicaBadCopyExponential.lean:215); helpers: ten files | 1249 | drift | golf/merge. paper: lower bounds F_C^{good},F_R^{good} ≥ kS'−r log d_*−log C(k,r)−o(k) used inside the D8.30 expectation; Lean: additionally proves an operator-level removal of the joint (C,R) exponential from the good-copy expectation (GoodAuxiliaryPairCompression, ReplicaJointAuxiliaryExponential) — an extra layer, same net output `-2kaS'+2ar log d_*+2a log C(k,r)`. |
| D8.28 | Step comparator:merge-decomposition | `PermutationRepresentation.physicalMergeDeficit` (OpenAI/CompatiblePhysicalLabel.lean:85), `posSemidef_qvMergeDeficit` (:102), 𝖩 `spectralProjectionGE_physicalMergeDeficit_mul_symProj` (:152), `commute_labelObservables_of_subset_or_disjoint` (:54), `TensorPower.pairMergeDeficit` (OpenAI/PairMergeDeficit.lean:48), `posSemidef_mergeDeficit` (OpenAI/MergeExponential.lean:191), `exp_mergeDeficit_eq_sum` (:130); the identity G^good = G_phys+F_C+F_R−D_C−D_R is not a declaration (assembled inside the D8.30 proofs); helpers: three files | 578 | smeared | restate (one lemma `step_8_28` for the identity, D_C,D_R ≥ 0, 𝖩); merge MergeExponential (spectral expansion of the merge deficit, also used for D6.4(3)). Standard?: specific. |
| D8.29 | Step comparator:merge-moments | individual moments `Matrix.replicaGoodConfigurationMarginal_exp_mergeDeficits_le` (OpenAI/ReplicaGoodConfigurationIndividualMergeMoment.lean:85), AM-form `replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le` (OpenAI/ReplicaGoodConfigurationMergeMoment.lean:76), `replicaGoodPairMarginal_exp_mergeDeficits_le` (OpenAI/ReplicaTwoMergeMoment.lean:174), `replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le` (OpenAI/ReplicaComponentMergeMoment.lean:133); input Lemma 6.1(3) `TensorPower.pair_merge_moment_le` (OpenAI/PairMergeMoment.lean:158); helpers: 17 files (good-copy densities, pair/regional/five-factor marginals, transport) | 2925 | drift | golf hard (≈2900 lines: marginal of u_B on good copies is rebuilt in five-factor, pair-marginal, regional and component coordinates). paper: E[e^{bD_C}\|γ,β] = Σ_ν m^ν (d_ν/(d_γd_β))^{1-b} ≤ poly via Schur–Weyl independence (D8.29.1-4); Lean: applies the generic positive-matrix merge-moment `pair_merge_moment_le` (Lemma 6.1(3) for non-iid marginals) to the actual good-pair density, and combines the two deficits by an arithmetic-mean bound (ReplicaTwoMergeMoment, ReplicaGoodConfigurationMergeMoment), not the Cauchy–Schwarz geometric mean of D8.30.3. |
| D8.30 | Step comparator:component-inverse | sharp `Matrix.exists_replicaExcitationComponent_inverse_sharp_le` (OpenAI/ReplicaComponentInverseSharp.lean:55), rough `exists_replicaExcitationComponent_inverse_rough_le` (OpenAI/ReplicaComponentInverseRough.lean:48), common `exists_replicaExcitationComponent_inverse_le_good_expectation` (OpenAI/ReplicaComponentInverseGoodExpectation.lean:54); Hölder-5 `Real.prod_five_rpow_le_common_exp` (OpenAI/FiveMomentExponentialBound.lean:33), `re_trace_mul_exp_mergeDeficits_sub_physicalMergeDeficit_le` (OpenAI/PhysicalMergeHolder.lean:111), `replicaGoodConfigurationMarginal_exp_merge_sub_physical_sharp_le` (OpenAI/ReplicaGoodConfigurationSharpMoment.lean:53); g^pre ≥ 0 `Matrix.physicalSingletonEntropy_outer_sub_middle_nonneg` (OpenAI/PhysicalSingletonEntropy.lean:105); helpers: 13 files | 1864 | drift | golf. rough: paper — drop e^{-aG_phys} ≤ 1 via 𝖩, then Cauchy–Schwarz on e^{aD_C+aD_R}; Lean — arithmetic-mean bound on the two merge exponentials (ReplicaTwoMergeMoment), bound `…inverse_rough_le` rather than the CS form. sharp: faithful (scalar Hölder-5 on e^{aD_C},e^{aD_R},e^{-aF_Q},e^{-aF_V},e^{aF_Y}, D8.10 at 5a, needs `20t ≤ r`, `20t ≤ 1`, constant `25 K a²`). Pitfall: OK — `(k-r)` multiplies g^pre (`m = Bᶜ.card`, L = −m·2t·(S0+S2−S1)…, OpenAI/ReplicaComponentInverseSharp.lean:~103) and bad copies cost `r log d_*` (b term :~98). Three marginal encodings (`Fin 5 → Type` five-factor family) duplicate Arealaw's `Reg`. |
| D8.31 | Step comparator:inverse-compression, lower-pin | compression `Matrix.compression_le_of_replicaExcitationComponent_bounds` (OpenAI/ReplicaExcitationCompression.lean:144), subset count `Finset.card_filter_powerset_le_mul_exp_binEntropy` (OpenAI/ExcitationSubsetCounts.lean:130), uniform rate `Real.replica_component_prefactor_le_uniform` (OpenAI/ReplicaComponentUniformRate.lean:33), `exists_replicaExcitationComponent_inverse_{rough,sharp}_uniform_le` (ReplicaComponentInverse{Rough,Sharp}Uniform.lean:52/:57), compression statements `exists_replicaLowDefectProjection_inverse_{rough,sharp}_compression_le` (ReplicaInverseRoughCompression.lean:53, ReplicaLowDefectSharpCompression.lean:57), lower pin `Matrix.PosDef.inv_smul_projection_le_of_compression_inv_le` (OpenAI/InverseCompressionLowerPin.lean:51), `exists_replicaLowDefectProjection_{rough,sharp}_lower_pin` (ReplicaLowDefect{Rough,Sharp}LowerPin.lean:51/:47), global form `exists_globalReplicaLowDefectProjection_{rough,sharp}_lower_pin` (OpenAI/RegionalLowDefectLowerPin.lean:130/:189); helpers: 13 files | 1642 | faithful | merge (compression + lower pin proved three times: replica, symmetric-coordinate, regional/global coordinates). Proof = D8.31.1-4. Standard?: specific; subset count `binEntropy` bounds are library-tree candidates (search pending). |
| D8.32 | Step | `Matrix.floor_pin_le` (OpenAI/FloorPin.lean:40) (A ≥ b(1−P)+(b+c/2)P from floor 2b and pin c); floor input `TensorPower.exists_replicaMetric_symProj_isometric_floor` (OpenAI/ReplicaSymmetricMetricFloor.lean:106) (leaf floor D6.9, `b = (k+2)^{-Cf}/2` appears inside RegionalRoughLowerNorm.lean:~108); `Matrix.identity_extension_floor` (FloorPin.lean:55); `Matrix.compressed_square_floor_of_inv_le` (OpenAI/CompressedInverseFloor.lean:33, outside import closure); helpers: FloorPin, ReplicaSymmetricMetricFloor, CompressedInverseFloor | 120 | faithful | keep `floor_pin_le`; cut CompressedInverseFloor.lean (dead: outside closure). Standard?: elementary. |
| D8.33 | Step | `Matrix.MeanTree.smul_one_sub_add_smul_projection_le_eval` (OpenAI/MeanTreeProjectionSectors.lean:102), `eval_smul_one_sub_add_smul_projection` (:69), `Matrix.MeanTree.weighted_log_add_half_exp_bounds` (OpenAI/MeanTreeLogFloorExp.lean:68), `weighted_log_floor_deficit_lower` (OpenAI/MeanTreeLogFloorDeficit.lean:36), `Matrix.cfc_affine_of_isSelfAdjoint_isIdempotentElem` (OpenAI/ProjectionCalculus.lean:37); helpers: four files | 345 | faithful | keep; golf. Pitfall (errors uniform in w_j via max_j, Σw_j=1): OK — `weighted_…_bounds` bound by the max over leaves, OpenAI/MeanTreeLogFloorExp.lean:68. Standard?: elementary. |
| D8.34 | Step comparator:tree-log-lower | `Matrix.MeanTree.re_dotProduct_log_eval_ge_of_projection_mass` (OpenAI/MeanTreeProjectionMassBound.lean:46), `log_projection_sectors_le_log_eval` (OpenAI/MeanTreeProjectionLogBound.lean:46); helpers: the two files | 154 | faithful | keep. Operator monotonicity of log + min(1,E_def/τ) step as D8.34.1-3. Standard?: elementary. |
| D8.35 | Step | `Matrix.MeanTree.mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound` (OpenAI/MeanTreeMultibandLowerNorm.lean:47), `explicit_lower_norm_of_exponential_projection_lower_bound` (OpenAI/MeanTreeExponentialLowerNorm.lean:44), `Matrix.PosDef.mul_re_inner_cfc_log_normalized_inverse_le_neg_log_norm_sq` (OpenAI/NormalizedInversePowerLogBound.lean:62); final statements `Matrix.exists_replicaMetric_symProj_bandProduct_rough_lower_norm` (OpenAI/RegionalRoughLowerNorm.lean:68), `…_rough_lower_norm_three` (RegionalRoughLowerThree.lean:118), `…_sharp_lower_norm` (RegionalSharpLowerNorm.lean:69), `Real.rough_lower_coefficient_three` (OpenAI/RoughLowerCoefficient.lean:34); helpers: seven files | 989 | faithful | merge the rough-lower variants (`…_norm` and `…_norm_three`, the latter fixing total band weight and the coefficient 3); proof = D8.35.1-4 (convexity of exp, Σ over g, divide by k). Standard?: Jensen; specific assembly. ℂ-only. |
| D8.36 | Step comparator:entropy-identity | `OpenAI.collarLeaf_entropy_identity` (OpenAI/CollarEntropyIdentity.lean:63) — stated in terms of Arealaw's `pureState`, `regionEntropy`, `mutualInfo`; proof by purity complements as D8.36.1-3; docstring cites §9 eq. (9.20), the rest of the file (`D₁_restrict_le`, `two_mutualInfo_le_collarLeaf`, `abs_mutualInfo_sub_le`) belongs to §9/§2 | 29 | faithful | keep (move to the §8 file). 𝕜-generic (`[RCLike 𝕜]`), Arealaw encoding — the only §8 statement not over ℂ. Standard?: Standard. |
| D8.37 | Step | no declaration; encoded in the quantifier order of the D8.8 theorems (`∃ c, ∀ᶠ k, ∀ n Z K U Y T …`) and `Real.bellOverlapRemainder` / `Real.tendsto_bellOverlapRemainder` (OpenAI/BellOverlapLogBound.lean:43/:83); `Matrix.MeanTree.tendsto_rough_lower_remainder_div_nat` (OpenAI/MeanTreeSublinearRemainder.lean:54), `tendsto_shifted_log_div_nat` (:41) | 92 | smeared | restate (one uniformity lemma: remainders vanish uniformly in terminal probabilities); inline into D8.8. |
| (section infra) | — | coordinate/isometry scaffolding serving several anchors, none stating one: CompressedSiteCoordinates.lean; CompressedTypicalAuxiliaryCoordinates.lean; CompressedTypicalLabelMass.lean; CompressedTypicalSiteCoordinates.lean; CompressedTypicalSiteNorm.lean; FiveFactorAuxiliaryCoordinates.lean; IsometricDomainExtension.lean; IsometricIntertwiningCommute.lean; MatrixProductIntertwine.lean; Transport/MetricFloor.lean; PositiveProjectionCompression.lean; ProjectionIntertwiningNorm.lean; ProjectionRangeIsometry.lean; RegionalFiveFactorCoordinates.lean; RegionalPhysicalMarginals.lean; RegionalPhysicalVector.lean; RegionalReplicaMetric.lean; RegionalReplicaMetricRegions.lean; ReplicaMetricCutoffNorm.lean; ReplicaTransportRootCompression.lean; ReplicaTransportRootMetricFloor.lean; ReplicaTransportSymmetricMetricFloor.lean; SchmidtBellEnumeratedCompression.lean; SpectralProjectionIntertwiner.lean; SurprisalFunctionalCalculus.lean; SymmetricProjectionCoordinates.lean; TensorPowerPartialTrace.lean; TrivialLabel.lean; TypicalTailScales.lean | 2093 | — | cut once the compressed/regional/five-factor/exterior encodings are unified (see notes) |
| (section infra, reverse pass) | — | `Matrix.omegaVec` (OpenAI/MaximallyEntangled.lean:31); `MaximallyEntangled.omegaCoeff_eq_inv` (OpenAI/MaximallyEntangled.lean:44) | 48 | — | inline into S08 Bell-label users (omegaVec: maximally entangled vector); owner anchor to be assigned |

## 09-scanner.md

Lines now (section total): 32191

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D9.1 | Def | `OpenAI.Scan.ambientDepth` (OpenAI/Scan/AmbientDepth.lean:51), `ambientSupDistance` (:46), `ambientDepth_le_iff_mem_dilation` (:98); d_Λ ≥ dist_∞: `OpenAI.Scan.mem_ambientDilation_singleton_of_domainGraph_edist_le` (OpenAI/Scan/SubsystemSize.lean:40, counted in D9.8) | 196 | faithful | golf; replace-by search pending (sup-norm infDist on ℤ×ℤ; `Metric.infDist`/`ambientDilation` already in Arealaw/OpenAI). ℂ/𝕜: scalar-free. |
| D9.2 | Def | `OpenAI.Scan.ScannerExponents` (OpenAI/Scan/Defs.lean:77) with `.L .m .K .D .a .eps .rounds .delta` (:103–:125), `chargeRounds` (:137); helper: OpenAI/Scan/BandCountGrowth.lean (whole file; K ≥ 1 for large n, not in import closure) | 198 | faithful | keep (the structure also carries e, ν of Prop 9.2; W is passed separately). Pitfall: OK — safe-rectangle n is a free parameter `n` of `sourceScan` (SourceScan.lean:66), fixed to 8·s₀ only in OpenAI/Scan/BoxImprovementStep.lean:81. BandCountGrowth.lean is outside the closure (dead). |
| D9.3 | Step | No single declaration: hypotheses `\|T\| ≤ C_T n²`, row bound `\|T_d∖T_{d−1}\| ≤ n`, clearance `2L+10r₀ < ambientSupDistance` are repeated inline in every theorem (e.g. `OpenAI.Scan.exists_sourceScan_selection`, OpenAI/Scan/ScannerSelection.lean:46); scan object `OpenAI.Scan.sourceScan` (OpenAI/Scan/SourceScan.lean:66, also holds `finalExponents` :100, `bootstrapExponents` :124, `IsSchmidtBellLabels` :162); truncated terms `CollarScan.truncatedEnergyTerm`/`actualEnergyTerms` (OpenAI/Scan/ActualEnergyTerms.lean); O(n) cut of ∂X: `CollarScan.source_target_geometry` (OpenAI/Scan/TargetGeometry.lean); scale order r₀≪D≪m≪L: `eventually_sourceScan_scales` (OpenAI/Scan/SourceScanScales.lean:41), `eventually_status_scale_separation` (StatusScaleSeparation.lean), RadiusAsymptotics.lean; OriginalTruncation.lean | 1013 | smeared | restate (one `TestGeometry` structure/def used by name). Pitfall: OK — row size only enters through the hypothesis `(ambientDilation T d \ ambientDilation T (d-1)).card ≤ n` (ScannerSelection.lean:46+). Scan side is ℂ-only. SourceScan.lean also hosts the D9.20/D9.26 exponent tuples and `IsSchmidtBellLabels` (a §8 object). |
| D9.4 | Def | `OpenAI.Scan.initialPartition` (OpenAI/Scan/PhysicalPartition.lean:89), `nominalFront` (:107), `augmentedPartition` (OpenAI/Scan/AugmentedPartition.lean:35), `sourceScan_terminal_regions` (OpenAI/Scan/SourceScanTerminalRegions.lean:114); helpers: ReceivingRegions.lean, AugmentedReceivingRegions.lean (outside closure), BandMargins.lean | 847 | faithful | golf (rows padded via fixed lists; C,R added by `augmentedPartition`; coordinate bridges for C,R sit in (section infra)). |
| D9.5 | Def | `OpenAI.Scan.CollarScan.state` (OpenAI/Scan/ActualHistory.lean:113), `chargeStep` (:93), `fillCount`/`nominalFront` (PhysicalPartition.lean:101/107); helpers: FillCoverage.lean, FrontThresholds.lean | 353 | faithful | keep. Fronts j_P, j_F = `nominalFront` (lo+1+⌊fills/n⌋ near, −hi+⌊·/n⌋ far) match the digest. |
| D9.6 | Def | `OpenAI.Scan.chargeCandidates` (OpenAI/Scan/ChargeSlots.lean:44), `chargeSlotCount` (:96), `paddedChargeSlot`; `CollarScan.selected` (ActualHistory.lean) | 205 | faithful | keep. Pitfall: OK — list length constant is the field `C₁ := 3 * anchorMultiplicityBound R` of `CollarScan` (SourceScan.lean:66–81), a name separate from Prop 4.5 constants; capacity `⌈C₁ n D⌉` dominates `μ_R n (D+r₀+1)` via `card_chargeCandidates_le_chargeSlotCount` (ChargeSlots.lean:100, needs r₀ ≤ D). |
| D9.7 | Def | `OpenAI.Scan.historyMeanTree` (OpenAI/Scan/HistoryMeanTree.lean:110), `historyWeight` (HistoryWeights.lean), `CollarScan.chargeTransportData` (PhysicalBandCommutation.lean:95), `actualFillData` (FillTransport.lean), `CollarScan.actualRoundData` (ActualRoundTransport.lean:96), `ActualTerminals.terminalPartition` (ActualTerminalPartitions.lean), `quantumHistoryMetric` (FillTransportEndpoints.lean), `IsSchmidtBellLabels.augmentedPrevector` (SchmidtBellAugmentedPrevector.lean:25); helpers: HistoryWeights, HistoryPrefixes, ActualChargeData, FillTransportEndpoints, AugmentedRootCompression, AugmentedReplicaPrevectorProperties, SupportCompatibility, FillSupportCompatibility | 2019 | smeared | restate (one round-data constructor feeding §7 `TransportData`; fill and charge are built by two parallel constructions). ℂ-only. |
| D9.8 | Lemma 9.1 | Stated twice, neither consumed downstream: structure `OpenAI.Scan.CollarScan.HistoryProperties` (OpenAI/Scan/ScanHistories.lean:520) proved by `eventually_historyProperties` (:809); abstract `HistoryFacts` (OpenAI/Scan/Defs.lean:275, counted in D9.9) proved by `exists_historyFacts_actualScanRound` (OpenAI/Scan/ActualHistoryFacts.lean:440, outside closure). Downstream uses the pieces: item 1 `SupportLocalization`, `SideSeparation`, `BandUniqueness`, `SplitSupportSize`, `SupportClassification`, `TerminalSplits`, `NestedBandMetric`, `BandNesting`; item 2 `AssignedLead`, `PrefixComparison/Approximation/Cardinality/FiniteFamily`, `FrontPrefixFamily`, `StatusCutBounds`, `SplitIntervals`, `SplitCounting`, `ActualRoundSplits`; item 3 `OffsetDilution`, `DesignatedDilution` (`old_designated_split_dilution_domainGraph`, DesignatedDilution.lean:81); item 4 `ChargeAncestry`, `PhysicalChargeAncestry`, `Ancestry*`, `ChargePathCounting`, `TimedChargePaths`, `ChargeBinomialBound`, `SelectedChainProbability`, `BadHistory*`, `BadChargeRatioBound`, `BadOldHistoryDecay`, `PhysicalBadHistoryDecay`, `GoodSampling` (`good_split_sampling_domainGraph` :220), `CompactCollarCounting`, `SubsystemSize` (all OpenAI/Scan/) | 7514 | smeared | restate (four named items, one declaration each, then delete both record encodings) + golf heavily (≈7.5k lines vs ≈150 digest lines). Lean constants are explicit (`10D/m`, `10μKnD`, `40nD`) vs paper C. Item 4 uses the paper route D9.8.12–15 (ancestry paths, binomial) with ratio nr₀(1+r₀²)μ/M instead of C r₀⁵/D (drift in constants only). Pitfall: OK (a) — `eventually_sourceScan_scales` gives 2r₀ ≤ D, 4(D+2r₀) ≤ m, 8Km ≤ L strictly (SourceScanScales.lean:41); (b) — `IsGoodOldHistory` is a property of the old history (GoodSampling.lean:99) and availability is claimed only on good histories (:220), bad ones paid by `exists_badOldHistory_threshold` (BadOldHistoryDecay.lean). ℂ-only except none. Note: `ChargeBinomialBound` ≈ Mathlib `Nat.choose_le_pow_div` + exp bound (search partial). |
| D9.9 | Proposition 9.2 | `OpenAI.Scan.exists_sourceScan_selection` (OpenAI/Scan/ScannerSelection.lean:46; ℂ-only); transfer Ω→Ω̃ and typical window: `exists_sourceScan_truncation` (SourceScanTruncation.lean:61), `CollarScan.exists_scanTruncation` (ScanTruncationInputs.lean:157), `exists_budgets` (Budgets.lean:271), `exists_truncated_target_typical_window` (TargetTypicalWindow.lean), status moments (StatusMarginalBudget/Moments, SourceStatusMarginalMoments), Lemma 3.1 bridges (MarginalTailsBridge, ActualMarginalTails, 𝕜-generic), `DomainFiniteProduct`; second route via abstract `ScanData` (OpenAI/Scan/Defs.lean:379 and rest of Defs.lean) with `scanner_estimate` (Scanner.lean:64, outside closure, dead) | 3164 | drift | restate. paper: hypotheses on S_Ω(X), S_Ω(Q_j) for Ω; builds typical set, labels and prevector inside the proof; conclusion E_def ≤ … for the selected (round, p_k). Lean: hypotheses are entropies of the truncated vector Ωt (`FiniteProduct.entropy`), a supplied typical set `E` and supplied `IsSchmidtBellLabels` (§8 data lifted to hypotheses); transfer and typical-window existence are separate theorems; conclusion is the energy half only, `∀η>0 ∀ᶠ k` instead of o_k(1). Pitfall: OK — ε = n^{−ν} is `X.eps` (Defs.lean:118), separate from the literal 10⁻⁵ and ε_n; selection (∃ s p) comes after `∀ᶠ k` with n, W, scan fixed before (ScannerSelection.lean:46+). Second encoding: `FiniteProduct.entropy/reducedPure` vs Arealaw `pureState`/`regionEntropy` bridged by DomainFiniteProduct.lean. |
| D9.10 | Def | `OpenAI.Scan.CollarScan.actualChargeEntropyDefect` (OpenAI/Scan/ActualEntropySampling.lean:52) and, in parallel, abstract `OpenAI.Scan.ScanRound.chargeDefect` (OpenAI/Scan/Defs.lean:214, counted in D9.9) joined by `transportScanRound_chargeDefect` (TransportRound.lean); η: `moveEta` (RegionalMoveEntropy.lean), `chargeEntropyCost` (ChargeEntropyCost.lean:68), `splitEta` (SplitEntropyBound, SplitEntropyCost); integrals: OldStateIntegral, OldStateParameterIntegral, ActualParameterIntegral, ActualRoundParameterIntegral (outside closure), TransportRoundParameterIntegral (outside closure), TransportRound, ActualScanMeasures | 1956 | overbuilt | merge into D9.9 (delete `ScanRound`/`ScanData` layer; keep one Q definition). Pitfall: OK — Q uses old weights `historyWeight` (ActualEntropySampling.lean:52), energy uses terminal weights (1−p), p (TransportRoundEnergy.lean). |
| D9.11 | Step | No declaration states the displayed inequality for −∂ₚ log N²; it is assembled from `CollarScan.actualCharge_transport_domainGraph` (OpenAI/Scan/ActualTransportEstimates.lean:152), sampling `good_split_sampling_domainGraph`, move-cost sums (ExpectedMoveCost.lean, DesignatedMoveCost.lean, DesignatedSampling.lean), dimension caps (SubsystemDimension/Scale, TransportDimension), `ScanData.chargeDefect_le_choiceGainSum` (EntropyBalance.lean), `actualCharge_integral_bound_domainGraph` (ActualChargeParameterBound.lean, outside closure) | 1839 | smeared | restate (state D9.11 once; inline the three cost/dimension families). |
| D9.12 | Step | `OpenAI.Scan.exists_sourceScan_selected_density` (OpenAI/Scan/SourceScanSelectedDensity.lean:155); steps: telescoping `actualRounds_entropy_integral_le_domainGraph` (ActualRoundEntropy.lean:185), initial `exists_actualFillData_initial_log_filteredNormSq_bound` (ActualInitialRootNorm.lean), final rough upper `eventually_actualScan_suppliedPrevector_rough_upper` (ActualRoughUpper.lean:58), restriction `actualCharges_integral_bound_domainGraph` (ActualChargeEntropySum.lean:188), averaging `exists_selected_density` (Selection.lean:107), `actualCharges_selection_domainGraph` (ActualChargeSelectionBound.lean) | 1622 | faithful | keep/golf. Steps D9.12.1–6 each have a file; ℂ-only. Pitfall: OK — selected (s,p) in the statement follows `∀ᶠ k` with W, n, scan fixed (SourceScanSelectedDensity.lean:155). |
| D9.13 | Step | `OpenAI.Scan.exists_sourceScan_energy_le` (OpenAI/Scan/SourceScanSelectedEnergy.lean:129); steps: Hölder + split counts `actualCharge_energyError_le_domainGraph` (ActualChargeEnergyBound.lean:65), coefficients (ActualChargeEnergyCoefficients), threshold `exists_actualCharge_energy_threshold` (ActualChargeEnergyDecay.lean:53), generic `ScanData.energySum_le` (EnergyBalance.lean), gap defect (ActualReplicaDefect), mean energy (ActualGlobalReplicaEnergy, TransportRoundEnergy) | 1812 | faithful | golf (EnergyBalance.lean works over abstract `ScanRound`, duplicated by Actual* versions). Pitfall: OK — three factors D/m, KnD, a² kept separate in `charge_energy_coefficient_identity` (ActualChargeEnergyCoefficients.lean). |
| D9.14 | Def 9.3 | `OpenAI.IsTemplate` (OpenAI/Statements.lean:304), `IsTemplatePiece` (:293), `HasTemplateSlope` (:287), `IsSeparatedFromCut` (:314) — frozen, not counted; piece = four strips: OpenAI/Geometry/TemplatePieceStrips.lean (counted in D9.16) | 0 | faithful | keep (frozen). Pitfall: n/a (no declaration; digest pitfall is notation). |
| D9.15 | Lemma 9.4 | Geometry half: `OpenAI.Scan.isTemplate_test_geometry` (OpenAI/Scan/TemplateTestGeometry.lean:224; \|T\| ≤ 4n², rows ≤ n, clearance), `OpenAI.IsTemplate.collar_cut_card_le` (OpenAI/Geometry/TemplateCollar.lean:458; cuts ≤ 4n, 8n, \|S₀\| ≤ 10n²), `IsTemplate.two_mul_sum_card_filter_le` (:339); entropy half: `OpenAI.templateEntropy_le_of_boxEntropy_le` (OpenAI/TemplateEntropy.lean:82, counted in D9.18; 𝕜-generic) | 282 | smeared | restate. Lean specialises the geometry to L = collarWidth n (and j ∈ {0,L}); the paper’s general `\|T\|≤Cns₀`, `\|T_j∖T_{j−1}\|≤n (j≤s₀)`, `\|∂T_j\|≤Cn (j≤s₀)` and the prefix/partial-row clause (“extra Cn”) are not stated for templates (partial row handled in Budgets/ScanTruncationInputs). Pitfall: OK — safety at own size: `IsSeparatedFromCut.isSafe` (TemplateEntropy.lean:45) uses clearance 4D₀s₀. |
| D9.16 | Step | No row-formula lemma; replaced by octagonal convexity: `OpenAI.IsOctagonallyConvex` (OpenAI/Geometry/TemplateCollar.lean:52), `IsTemplatePiece.isOctagonallyConvex` (:320), `IsOctagonallyConvex.card_ambientDilation_succ_sdiff_le` (OpenAI/Scan/TemplateTestGeometry.lean:103), `IsTemplate.card_ambientDilation_sdiff_le` (:180); piece = four strips: OpenAI/Geometry/TemplatePieceStrips.lean (shared with §11 fans) | 808 | drift | restate. paper: rows are max/min of affine functions with slopes in {−1,0,1}, endpoints 1-Lipschitz, layer and boundary ≤ C(s₀+j+1); Lean: piece is the intersection of four strips x, y, x±y, “octagonal convexity” and layer counts are derived from `injOn_snd_filter`/`injOn_fst_filter` counting (no explicit row interval lemma). TemplatePieceStrips (315 lines) exists to prove piece = strips. |
| D9.17 | Step | `OpenAI.card_mixedDyadicIndices_le` (OpenAI/Geometry/TemplateMixedSquares.lean:101), `IsTemplate.card_mixedDyadicIndices_ambientDilation_le` (:278; ≤ 16(3+2a)n/u for u ≤ a(s₀+1), j ≤ s₀); helper: OpenAI/Geometry/QuotientIntervals.lean | 366 | faithful | golf; library tree (elementary lattice geometry, search pending). Variant bound form (per piece sum over N₀, via `ambientDilation_biUnion` :239); T and T_j∖T cases are in CappedDyadicPartition (D9.18). Uses “Lipschitz rows” in place of endpoint-movement ≤1. |
| D9.18 | Step | `OpenAI.templateEntropy_le_of_boxEntropy_le` (OpenAI/TemplateEntropy.lean:82; 185 lines, steps D9.18.1–5 inline), `regionEntropy_inter_le_sum_cappedDyadicPartition` (:58), `OpenAI.IsSeparatedFromCut.isSafe` (:45); cover: OpenAI/Geometry/CappedDyadicPartition.lean (`cappedDyadicPartition`, four-per-mixed-parent, `sum_rpow_cappedDyadicPartition_le`) | 621 | faithful | library tree (maximal dyadic cover; searched: Mathlib/analysis-ci only have the real-cube Whitney version, not a lattice capped cover); golf (split the 185-line proof into D9.18.1–5 steps). Standard: maximal dyadic cover. |
| D9.19 | Proposition 9.5 | `OpenAI.improved_box_estimate` (OpenAI/ImprovedBoxEstimate.lean:84; ℂ-only via `boxEntropy ℂ`); `boxEntropy_eventually_improves` (:28) | 110 | faithful | keep. Pitfall: OK — bootstrap uses only rough comparisons (`ActualRoughUpper/Lower`, OpenAI/Scan/RectangleBootstrap.lean:147 hypotheses carry no a√B bound). |
| D9.20 | Step | `OpenAI.Scan.BootstrapParameters.{g0,mu,nu,ell,kappa}` (OpenAI/Scan/BootstrapParameters.lean:42–56), `parameter_bounds` (:60), `density_exponents` (:68), `energy_exponents` (:80), `comparison_exponents` (:91); assembled in `bootstrapExponents` (OpenAI/Scan/SourceScan.lean:124, counted in D9.3) | 101 | faithful | keep. Pitfall: OK — parameters take only e₀ (BootstrapParameters.lean:42–56) so iteration count and constants are uniform; W = 4 is fixed in ActualRoughLower (D9.23). `bootstrapExponents` sets scan exponent e := e₀ while the hypothesis exponent is the current e ≤ e₀ (handled in RectangleBootstrap.lean:147). |
| D9.21 | Step | `OpenAI.Scan.isSafe_test_geometry` (OpenAI/Scan/RectangleTestGeometry.lean:43), `OpenAI.Scan.isSafe_shell_regionEntropy_le` (OpenAI/Scan/RectangleShellEntropy.lean:59; 𝕜-generic), `IsSafe.isSafe_cappedDyadicPartition_shell` (OpenAI/WeakRectangleShellSafety.lean), `IsSafe.of_subset_dilate` (OpenAI/SafeRectangleDilation.lean), rounded scales (RoundedClearance, RoundedScalePower, BootstrapRoundedClearance) | 728 | drift | merge into D9.18 (rectangle = template with N₀=1). paper: rectangle case reuses D9.18 with cap ≈ L; Lean: second covering/mixed-square argument for `IsIntRect` (RectangleShellEntropy.lean, with its own `isOctagonallyConvex`/`card_mixedDyadicIndices` for rectangles) next to the template one. n = ⌈C₂ s₀⌉ specialised to n = 8 s₀ in BoxImprovementStep.lean:81. |
| D9.22 | Step | `OpenAI.Scan.exists_bootstrap_principal_energy_bound` (OpenAI/Scan/BootstrapPrincipalEnergyBounds.lean:47), `exists_bootstrap_energy_expression_bound` (:243); exponent facts in `BootstrapParameters.density_exponents/energy_exponents` (D9.20 file) | 279 | faithful | golf (arithmetic; consider `grind`/`norm_num` over exponent table). |
| D9.23 | Step | `OpenAI.Scan.exists_bootstrap_comparison_cost_le` (OpenAI/Scan/RectangleBootstrap.lean:68), `sourceScan_bootstrap_entropy_le` (:147; merges D9.23 with D9.24.1–3), `entropy_le_of_replica_comparisons` (BootstrapReplicaAbsorption.lean:46), `exists_actualScan_suppliedPrevector_rough_lower` (ActualRoughLower.lean:72), `regionalEntropy_le_of_rough_typical_comparisons` (TypicalReplicaAbsorption.lean:58), budgets (BootstrapComparisonBudget, BootstrapBinaryEntropyCost) | 1108 | drift | restate. paper: intermediate bound S_X ≤ C_e(nL^e+nD+w+h(τ)/a+1) then exponent arithmetic D9.24.1–3; Lean: no declaration states the intermediate, `sourceScan_bootstrap_entropy_le` goes straight to `C n^{1+(1−ℓ)e}`. Order of limits (k→∞, then n large) is respected via `entropy_le_of_replica_comparisons`. ℂ-only. |
| D9.24 | Step | one step `OpenAI.Scan.isSafe_regionEntropy_le_of_boxEntropy_le` (OpenAI/Scan/BoxImprovementStep.lean:81), sup over boxes `OpenAI.boxEntropy_eventually_improves` (OpenAI/ImprovedBoxEstimate.lean:28), iteration `OpenAI.exists_boxEntropy_le_rpow_of_eventual_improvement` (OpenAI/ExponentBootstrap.lean:127) over generic `exists_uniform_rpow_bound_of_eventual_improvement` (:88) | 403 | smeared | restate; golf. ExponentBootstrap.lean is stated for an abstract family F i (more general than the paper’s single F_box). |
| D9.25 | Proposition 9.6 | statement frozen: `OpenAI.CollarBound` (OpenAI/Statements.lean:323); `OpenAI.collar_bound` (OpenAI/CollarBound.lean:16) = `collarBound_of_collarInformationBound` (OpenAI/CollarReduction.lean:48) applied to `collarInformationBound` (OpenAI/CollarInformation.lean:439; the single ℂ→𝕜 transfer) from `collarInformationBound_complex` (:324) and `exists_truncated_collar_leaf_family` (:73); size/cut claims: D9.15 | 550 | faithful | keep/golf. 𝕜: development over ℂ with one top-level transfer (CollarInformation.lean:439) — as planned. Pitfall: OK — ε = 10⁻⁵ appears in both `collarWidth` and the bound (frozen, Statements.lean:283/336); L ≤ s₀ is the hypothesis `collarWidth n ≤ s₀`; constants ordered D₀ → C_tpl₀ → C, n₀. |
| D9.26 | Step | `OpenAI.Exponents.scannerMu/scannerEll/scannerKappa` (OpenAI/Scan/ScannerExponents.lean), `scannerNu/scannerOmega` (OpenAI/Scan/SharpMomentScale.lean:43/46), `finalExponents` (OpenAI/Scan/SourceScan.lean:100, counted in D9.3), `exists_final_a_le_moment_radius` (SharpMomentScale.lean:246) | 330 | faithful | keep. E_def ≤ n^{−0.0005}: `eventually_final_energy_le` (FinalCollarScales.lean:80, counted in D9.29). Rational exponents with coercion. |
| D9.27 | Step | `OpenAI.Scan.sourceScan_collar_leaf_bound` (OpenAI/Scan/CollarComparison.lean:158; merges (a),(b) and part of D9.29), (a) `CollarScan.terminalPartition_entropyGap_le` (TerminalEntropyGapBound.lean:73), (b) `two_mul_add_inv_mul_sum_sub_le_of_sharp_comparisons` (SharpComparisonSubtraction.lean:27), `two_mul_add_le_of_subtracted_comparison` (CollarErrorAbsorption.lean:28); sharp comparisons instantiated on the actual scan: ActualSharpUpper (`actualScan_sharpUpper_of_compressed` :533), ActualSharpLower, ActualSharpLowerPrevector, ActualSharpLowerRemainder, ActualSharpPrevector, SourceTargetSharpUpper (`exists_truncated_target_actualSharpUpper` :75) | 3090 | smeared | restate (state (a), (b) once). The ≈2.7k lines of ActualSharp* re-instantiate §8 Prop 8.1 (sharp upper/lower) on the Actual* data — candidates for §8 or for deletion once D9.7 is unified. Pitfall: OK — S(·) are entropies of Ωt (`pureState Ωt`) and transfer to Ω is only in `collarInformationBound_complex` (D9.30). |
| D9.28 | Step | `OpenAI.collarLeaf_entropy_identity` (OpenAI/CollarEntropyIdentity.lean:63), `OpenAI.two_mutualInfo_le_collarLeaf` (:92; I(X:W) ≤ … for W ⊆ V) | 25 | faithful | keep. Standard parts (purity S(AB)=S(C), mutual-info monotonicity) via Arealaw `regionEntropy_pureState_sdiff`, `SubState.mutualInfo_def`; 𝕜-generic (no ℂ-only). |
| D9.29 | Step | `OpenAI.Scan.eventually_final_collar_errors_le` (OpenAI/Scan/FinalCollarScales.lean:190; six-term sum ≤ n^{1−10⁻⁵}), `eventually_final_collar_scales`/`eventually_final_energy_le` (:80); chain assembled inside `exists_truncated_collar_leaf_family` (OpenAI/CollarInformation.lean:73) | 287 | faithful | golf (table is one aggregate inequality, per-row powers are internal). Pitfall: n/a (arithmetic). |
| D9.30 | Step | `OpenAI.abs_mutualInfo_sub_le` (OpenAI/CollarEntropyIdentity.lean:117; 𝕜-generic, dimension of X only), `Arealaw.SubState.D₁_restrict_le` (:30); used in `collarInformationBound_complex` (OpenAI/CollarInformation.lean:324); size/cut claims: D9.15 (`collar_cut_card_le`) | 0 | faithful | merge into D2.4’s consumer if possible: check against frozen `ConditionalContinuity` (Lemma 2.1) and delete `abs_mutualInfo_sub_le` if it re-proves it (search pending). |
| (section infra) | — | OpenAI/Scan/AugmentedEnergyCoordinates.lean, AugmentedReplicaMetricCoordinates.lean, GlobalReplicaEnergyCoordinates.lean (whole files: Option vs Sum descriptions of the augmented sites P∪{C,R}; scaffold) | 365 | none | cut once D9.7/D9.13 use one encoding of C,R |

## 10-amplification.md

Lines now (section total): 13740

All declarations below are over `ℂ` unless stated; the only 𝕜-generic declarations are `OpenAI.amplificationOutput` and `OpenAI.amplification` (one ℂ→𝕜 transfer at the top, via `toComplex`, OpenAI/Amplification.lean:28). Files are under `OpenAI/` (`Amp/` = `OpenAI/Amplification/`). "span a–b" = the declarations of that file between those lines (a file is split over rows only where it serves several anchors).

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D10.1 | Def (ε, β, α = p/(p+1), positive system) | — (no declaration). Used as numerals `1/100000`, `2/1000000`, `1/1000000` in OpenAI/Statements.lean:355 and AmplificationCutClearance.lean; α is `OpenAI.kernelExponent p` (OpenAI/SpectralFilter/FilterLocality.lean:51, §4); the system `k_i, g` is `exists_latticePositiveConstraints` / `positiveConstraint` (§4 files, not counted here); hypothesis `hp : 1 - 1/10^6 < p/(p+1)` stands for p ≥ 10^6 | 0 | missing | restate (name ε, β once; `hp` as `p ≥ 10^6`); Pitfall: OK — p-dependence of C, c, g fixed before Λ (`exists_latticePositiveConstraints hp R hJ hΔ` gives C c before Λ, OpenAI/Amplification/ConstraintWordTruncation.lean:442), `hp` explicit in `amplification` (OpenAI/Amplification.lean:54) |
| D10.2 | Lemma 10.1 | Statement split in two: (A)+support `OpenAI.exists_domainConstraintWord_truncation` (Amp/ConstraintWordTruncation.lean:381, abstract k_i) and lattice specialization `OpenAI.exists_latticeConstraintWord_truncation` (:442); (B) `OpenAI.exists_domainConstraintWord_omission` (Amp/LatticeChannelSpatialOmission.lean:150) and `OpenAI.exists_latticeConstraintWord_omission` (:206). Channels/shells D10.2.1–6: Amp/LocalRootChannels.lean (`spectatorRootChannel` :61, `localRootChannel` :111, `localRootChannelShell` :235), Amp/ChannelGroundVectors.lean, Amp/ChannelShellOscillation.lean, Amp/LocalChannelOscillation.lean, Amp/ExponentialChannelShells.lean, Amp/ComponentChannelOscillation.lean (D10.2.4). Kernel/propagation D10.2.7–9: Amp/GraphChannelEventError.lean, Amp/GraphChannelEventKernel.lean, Amp/GraphChannelOscillation.lean, Amp/GraphChannelWeightedRow.lean, Amp/GraphChannelPoissonGrowth.lean (`integrable_and_integral_siteOscillation_le_of_graph_kernel` :73), OpenAI/PoissonWordWeightedGrowth.lean, OpenAI/PoissonWordSpatialGrowth.lean. Omitted event/coupling D10.2.10–12: Amp/GraphOmittedAnchorTail.lean, Amp/GraphChannelSpatialOmission.lean, Amp/ChannelWordObservables.lean, Amp/ChannelWordOmission.lean, Amp/ChannelWordThinning.lean. Distance/profile helpers: OpenAI/GraphExtendedMetric.lean, OpenAI/ExponentialDistanceProfile.lean, OpenAI/StretchedExponentialSummability.lean. (Poisson-word measure theory is in `(section infra)`.) | 3908 | smeared | merge lattice versions into abstract ones, then prove as one `lemma_10_1` with (A), (B), support; keep route notes. Routes — paper D10.2.9: ODE `d/du E d_y(B_u) ≤ Σ A_yz E d_z`, sup-weighted `f_u`, Gronwall; Lean: Poisson-word recursion, weighted supersolution `Σ_{words of length m} f ≤ (card ι+v)^m C r(y)` summed against Poisson weights (OpenAI/PoissonWordWeightedGrowth.lean:69, :109). Paper D10.2.11: Campbell formula on coupled clocks; Lean: `channelWordOmissionDefect` with prefix sums and Poisson occupation integrals (Amp/ChannelWordOmission.lean:66–143). Paper: abstract k_i anchored in Λ; Lean: abstract version over `Finset (ℤ×ℤ)` domains plus a second copy for the lattice constraints. Statement over ℂ only. Pitfall: OK — unital channels and `k_i Ω = 0` used (Amp/ChannelGroundVectors.lean:54–83); (B) has `exp(v t − γ r^α)`, (A) has none; constants `A v γ` chosen before Λ, spectator `Aux`, S, r, t (Amp/LatticeChannelSpatialOmission.lean:206) |
| D10.3 | Step (excited-state decay) | `OpenAI.latticeConstraintWord_excitedProjection_decay` (Amp/LatticeExcitedDecay.lean:53) and abstract `Matrix.poissonContractionWord_excitedProjection_decay` (OpenAI/PoissonContractionDecay.lean:72); helpers: OpenAI/ContractionWordDecay.lean (`contractionWord` :37, `contractionWordSum_le_pow` :172), OpenAI/ContractionWordDecaySpectator.lean (whole file) | 535 | drift | restate as one lemma; prove along D10.3.1–3 (paper: ODE `d/du E‖ψ_u‖² = −E⟨ψ_u,H_Fψ_u⟩ ≤ −g E‖ψ_u‖²`, Gronwall; Lean: `Σ_i ‖G_iψ‖² ≤ (card ι−g)‖ψ‖²` on every ground-orthogonal vector, word sums `contractionWordSum k m v ≤ (card ι−g)^m‖v‖²`, then Poisson series `Σ_m e^{-t}t^m/m!·(card ι−g)^m = e^{−gt}` (PoissonWord.lean:193); spectator handled by slicing `ζ = Σ_r ζ_r⊗e_r`, 176 extra lines, where the paper writes `P_Ω ⊗ I`). ℂ-only; gap is `Δ/cs` with `cs = positiveNormalization p (Δ/2) J` |
| D10.4 | Proposition 10.2 | `OpenAI.amplification` (OpenAI/Amplification.lean:54, 𝕜-generic, = frozen `Amplification`); `OpenAI.amplificationOutput` (:28, ℂ→𝕜 transfer); `OpenAI.amplificationOutput_complex` (OpenAI/AmplificationProof.lean:149, one 329-line proof of D10.5–D10.15); `OpenAI.AmplificationOutput` def (OpenAI/AmplificationCutClearance.lean:186, second statement of Prop 10.2 without clearance clause); `OpenAI.amplification_of_amplificationOutput` (:213); helpers in AmplificationProof.lean: `mutualInfo_pureState_eq_finiteProduct` (:87, bridge `Reg/pureState` ↔ `FiniteProduct`), `sqrt_inv_pow_eq_rpow`, `sqrt_rpow_neg_two_mul'` (duplicate of `sqrt_rpow_neg_two_mul`, Amp/LatticeRestoring.lean:712), `unitary_error_le`, `one_le_of_lt_div`, `norm_toLp_single_eq_one` | 573 | drift | golf (split into the digest steps; delete `AmplificationOutput` and the bridge once the encoding is unified); Pitfall: OK — quantifiers `C₀ M ∃ C_M n₀ ∀ Λ Φ Ω A T n ∃ r`, r after `𝓘` (OpenAI/Statements.lean:355); `K` fixed from `M`, then thresholds, then `C'` (AmplificationProof.lean:149ff). Drift: paper `K = ⌈4(M+3)⌉`, `n^{2−K/4} ≤ n^{−M−1}`; Lean `K = 4(M+2)` (AmplificationProof.lean `set K := 4*(M+2)`) with constants 9 `n^{−K/2}` and `n^{2−K/4}=n^{−M}`, absorbed in `C_M`. No separate `X=∅` case (D10.4.1; blank vectors make it vacuous). Clause `L+2r = o(n^β)` is not in the frozen statement (follows from `r ≤ C_M n^{(1−ε)/α}`) |
| D10.5 | Step (typical projections) | `OpenAI.exists_typicalProjectors_three_cuts` (Amp/TypicalProjectors.lean:267); `OpenAI.typicalProjection` (:86), `typicalProjection_failure_le_surprisalTail` (:114), `exists_typicalProjection_failure_le_stretchedExp` (:152), `exists_typicalProjection_failure_le_inv_pow` (:236) | 301 | faithful | keep (𝕜 n/a: ℂ-only; stated on the `FiniteProduct` encoding over `↥Λ` with `Fin q`, not on `Reg`/`pureState`). Lemma 3.1 enters through `hΦ.surprisalTail_reducedState_le` (§3). Pitfall: OK — `w = n^(3/5)`, failure `C exp(−c n^{1/10}) ≤ n^{−2K}` (:152, :205) |
| D10.6 | Def (φ, η, R_X) | `OpenAI.Entropy.restoringCopy` (OpenAI/RestoringVectors.lean:53 = φ), `restoringRestored` (:68 = η), `restoringInitial` (:60); coordinates `OpenAI.restoringVector` (Amp/LatticeRestoring.lean:291), `OpenAI.restoringSplit` (:283); relabelling/isometry `R_X` replaced by unitary transport `OpenAI.restoringTransport` (Amp/LatticeAncillaTransport.lean:216), `restoringTransport_estimates` (:323), and the ancilla swap/rotation `OpenAI.ancillaTransport` (Amp/AncillaTransport.lean:78); files Amp/AncillaTransport.lean, Amp/LatticeAncillaTransport.lean, Amp/LatticeRestoring.lean span 262–332 | 966 | smeared | restate (φ, η, R_X as three definitions with D10.6.1–2 as lemmas); unify with D10.15's ancilla-site encoding; the paper's one-line isometry costs ≈ 900 lines here (rotation of eigenbasis, swap, transport of every earlier estimate) |
| D10.7 | Def (R₀, B₀) | `OpenAI.Entropy.restoringOperator` (OpenAI/RestoringOperators.lean:94), `restoringOperatorWithAncilla` (:103), `columnOperator` (:113), global versions `restoringGlobal` (OpenAI/RestoringVectors.lean:97), `restoringColumnGlobal` (:105); column identity `R₀φ = B₀(Ω⊗ket 00)`: `restoringGlobal_mulVec_copy` (:194), `column_operator_apply` (:169), transported as `hcol` in `restoringTransport_estimates` (Amp/LatticeAncillaTransport.lean:323); files OpenAI/RestoringOperators.lean, OpenAI/RestoringVectors.lean span 1–260 | 591 | faithful | keep (generic over index types, eigenbasis `U`, blank vectors; ℂ-only); golf |
| D10.8 | Step (norms ≤ M₀) | `OpenAI.Entropy.restoringOperators_norm_le_exp` (OpenAI/RestoringNorm.lean:200) with `restoringGram_le` (:84), `restoringOperator_norm_le` (:147), `columnOperator_norm_le` (:171); Gram identities `Entropy.restoringOperator_gram` / `columnOperator_gram` (OpenAI/RestoringOperators.lean:237, :286, counted in D10.7); lattice input `OpenAI.restoringOperator_estimates` (Amp/LatticeRestoring.lean:663), `exists_restoringOperator_estimates` (:729), spectral inequalities `restoringCutProjection_le_and_typicalProjection_le` (:609), `Matrix.IsHermitian.spectralSelection_mul_mul_le_smul` (:217), purity identity `mutualInformation_compl_eq` (:587); files OpenAI/RestoringNorm.lean, Amp/LatticeRestoring.lean spans 1–261, 333–400, 587–775 | 751 | faithful | keep; golf (D10.8.2–3 are 4 generic lemmas plus lattice repackaging; ℂ-only, `FiniteProduct` encoding) |
| D10.9 | Step (adjoint identity, no M₀) | `OpenAI.Entropy.restoringGlobal_adjoint_identity` (OpenAI/RestoringVectors.lean:314), `restoringGlobal_adjoint_error_le` (:426), `three_contractions_error` (:402); failure-probability pieces `OpenAI.norm_selectedProjection_restoringVector_sub_le` (Amp/LatticeRestoring.lean:449), `norm_typicalProjection_restoringVector_sub_le` (:479), `norm_restoringCutProjection_restoringVector_sub_le` (:557); files OpenAI/RestoringVectors.lean span 261–469, Amp/LatticeRestoring.lean span 401–586 | 395 | faithful | keep; golf |
| D10.10 | Step (ground component ≤ 1) | `OpenAI.Entropy.restoringGroundComponent_norm_le_one` (OpenAI/RestoringGroundComponent.lean:329), `restoringGroundComponent_trace_chain` (:296), `restoringMarginal_le` (OpenAI/RestoringMarginal.lean:139), `Matrix.PosSemidef.selected_sum_sq_div_le_trace` (OpenAI/RestoringCoefficientBound.lean:119), `PosSemidef.mul_supportInv_mul_le` (OpenAI/SupportInverseSandwich.lean:107); files OpenAI/RestoringGroundComponent.lean, OpenAI/RestoringMarginal.lean, OpenAI/RestoringCoefficientBound.lean, OpenAI/SupportInverseSandwich.lean | 740 | faithful | golf (follows D10.10.1–4: coefficients `c_xy`, `0 ≤ M_X ≤ ρ_X`, `M_X ρ_X⁺ M_X ≤ M_X`, trace; 740 lines for a half-page argument — the `supportInv` sandwich lemmas are `standard`: search pending for Mathlib/Physlib replacements) |
| D10.11 | Def (t*, r) | `OpenAI.amplificationTime` (Amp/GoodRealization.lean:106, C = 6/g), `OpenAI.amplificationRadius` (:111); requirement proofs `OpenAI.amplification_scale_bounds` (:181, C' = (g/2+2v+12)/c), `exists_one_add_sq_mul_exp_neg_rpow_le` (:116), `prefactor_le` (:157); D10.11.1 radius bound `OpenAI.exists_amplificationRadius_le` (Amp/RadiusBound.lean:42); files Amp/RadiusBound.lean, Amp/GoodRealization.lean span 106–294 | 286 | faithful | keep; Pitfall: OK — C fixed before C' (C' depends only on g, v, c; threshold N on K, C, C₀), Amp/GoodRealization.lean:181. Constants: paper `C ≥ max{6/g, 2}`, Lean `C = 6/g` and the `g/2` term in C' replaces D10.11.3 (`log M₀ ≤ t*`), which is not used |
| D10.12 | Step (good trajectory) | `OpenAI.exists_good_realization` (Amp/GoodRealization.lean:295, abstract random variables X, Y, Z with the three expectation bounds), `OpenAI.exists_le_of_integral_sq_le_of_integral_le` (:65, Markov + union bound); application inside `amplificationOutput_complex` (AmplificationProof.lean:149ff); file Amp/GoodRealization.lean spans 1–105, 295–338 | 149 | faithful | keep (D10.12.1 squared Markov, .2–.3 first moments, .4 union bound) |
| D10.13 | Step (estimates before polar, direct error) | `OpenAI.norm_truncated_restoring_le` (Amp/GoodRealizationUnitary.lean:74 = D10.13.2), `norm_truncated_adjoint_sub_le` (:99 = D10.13.3), `norm_sub_sq_le_of_adjoint_error` (:120 = D10.13.5–6, `‖R'φ−η‖² ≤ 2a+2b+b²`); D10.13.1 word facts `Matrix.contractionWord_eq_prod_reverse`, `conjTranspose_contractionWord_mulVec_self` etc. (Amp/ConstraintWordLists.lean:56–95); files Amp/ConstraintWordLists.lean, Amp/GoodRealizationUnitary.lean span 1–156 | 262 | faithful | keep |
| D10.14 | Step (local unitary via polar) | `OpenAI.exists_unitary_kronecker_sub_le_of_good_realization` (Amp/GoodRealizationUnitary.lean:181), `exists_unitary_kronecker_sub_le` (:157); polar factor `Matrix.exists_unitary_polar_correction` (OpenAI/PolarUnitaryCorrection.lean:126), `unitary_polar_correction_kronecker_one` (OpenAI/PolarUnitaryCorrectionKronecker.lean:53); support `OpenAI.exists_supported_unitary_of_good_realization` (Amp/SupportedPolarCorrection.lean:175), `exists_ancilla_unitary_of_good_realization` (OpenAI/AmplificationProofSteps.lean:136); files OpenAI/PolarUnitaryCorrection.lean, OpenAI/PolarUnitaryCorrectionKronecker.lean, Amp/SupportedPolarCorrection.lean span 1–301, OpenAI/AmplificationProofSteps.lean span 1–214, Amp/GoodRealizationUnitary.lean span 157–206 | 814 | drift | restate; paper: `ξ=U†η`, `(I+H₊)(ξ−φ) = (H₊ξ−φ) − (H₊φ−ξ)`, `‖(I+H₊)^{-1}‖ ≤ 1`, so `‖U'φ−η‖ ≤ 4n^{−K}+Cn^{−K/2}`; Lean: same expansiveness of `1+P` packaged as `‖Ux−y‖ ≤ ‖Dx−y‖+‖D†y−x‖` (PolarUnitaryCorrection.lean:95/126) applied with `x=φ, y=η`, giving `a+√(2a+2b+b²)`; extra: support of the polar unitary on `s'∪N_{2r}(S₀)` proved by an `∃ K, U = 1 ⊗ K` factorisation over the ancilla-site encoding (SupportedPolarCorrection.lean:132–262) |
| D10.15 | Step (mutual information bound) | `OpenAI.mutualInformation_le_of_ancilla_unitary` (OpenAI/AmplificationProofSteps.lean:247), `OpenAI.mutualInformation_le_inv_pow_of_supported_unitary` (Amp/SupportedPolarCorrection.lean:325), `FiniteProduct.mutualInformation_le_inv_pow_of_unitary_sub_le` (Amp/EntropyComparison.lean:388); D10.15.1–2 `OpenAI.mutualInformation_ancillaCopy_eq` (Amp/LatticeAncillaSites.lean:300), `mutualInformation_ancillaProduct_copy_eq_zero` (:277); enlarged-site encoding `OpenAI.AncillaSites` (:131), `FiniteProduct.relabelSites`, `sumSitesProduct` (Amp/AncillaSiteEntropy.lean:114, :185); `FiniteProduct.traceDistance_reducedPure_le` (Amp/EntropyComparison.lean:185); `hdim` (`log dim e' ≤ C n²`) inline in AmplificationProof.lean; files Amp/EntropyComparison.lean, Amp/AncillaSiteEntropy.lean, Amp/LatticeAncillaSites.lean, Amp/SupportedPolarCorrection.lean span 302–346, OpenAI/AmplificationProofSteps.lean span 215–325 | 1122 | smeared | restate as one step lemma; paper: Lemma 2.1 on `e'` + `log dim e' ≤ C n²`, three lines; Lean: builds the disjoint-sum site type `AncillaSites Λ X` and proves relabel/sum invariance of entropy and mutual information for it (≈ 700 lines of encoding). Standard?: continuity (Lemma 2.1, `FiniteProductContinuity`, §2). Pitfall: OK — `dim e'` enters, `dim J` does not (Amp/EntropyComparison.lean:263–388). D10.15.7 (subsets X' ⊆ X) is `hX''X` in `mutualInformation_le_of_ancilla_unitary` |
| D10.16 | Step (radius bounds, containment in A) | `OpenAI.Exponents.radiusExponent_lt_beta` (OpenAI/AmplificationCutClearance.lean:74), `radius_exponent_gaps` (:82), `exists_collar_radius_threshold` (:115), `collar_add_radius_isLittleO` (:137), `OpenAI.exists_threshold_graphNeighborhood_collar_subset` (:164), `OpenAI.graphNeighborhood_subset_of_lt_ambientEDist` (OpenAI/GraphNeighborhoodCutClearance.lean:100); files OpenAI/AmplificationCutClearance.lean span 1–185, OpenAI/GraphNeighborhoodCutClearance.lean | 330 | faithful | keep (D10.16.2 exponent arithmetic, D10.16.3 path argument); Pitfall: OK — `(1−ε)/α < β` for `α > 1−10⁻⁶` (:74); numerals repeated rather than named once |
| D10.17 | Step (closing remark) | — | 0 | none | cut (no declaration expected) |
| (section infra) | — | Poisson-word probability space (`PoissonWord.Word/weight/measure`, partition/thinning/occupation/jump integrals) used by D10.2 and D10.3: OpenAI/PoissonWord.lean, PoissonWordAppend.lean, PoissonWordInsertion.lean, PoissonWordInsertionWeight.lean, PoissonWordMarked.lean, PoissonWordRelabel.lean, PoissonWordThinning.lean, PoissonWordPartition.lean, PoissonWordOccupation.lean, PoissonWordRealOccupation.lean, PoissonWordJump.lean (whole files) | 1568 | overbuilt | replace-by Mathlib/Physlib Poisson process if one exists (search pending; Mathlib has none for a discrete word law); otherwise reduce to one file: the paper only needs `E Σ_{events of i} f = ∫₀ᵗ E f(B_u) du` and `E‖·‖` on coupled clocks, which a finite-time Poisson clock model gives directly |
| (section infra, reverse pass) | — | 11 decls: `siteOscillation`, `norm_siteUnitary_commutator_le`, `siteOscillation_bddAbove`, `zero_mem_siteOscillation_values`, `norm_commutator_le_siteOscillation`, `norm_commutator_le_siteOscillation_right`, `siteOscillation_nonneg`, `siteOscillation_le`, `siteOscillation_le_two_mul_norm`, `siteOscillation_add_le`, `siteOscillation_eq_zero_of_commute` (OpenAI/SiteOscillation.lean:58-155); `OpenAI.siteOscillation_of_notMem` (OpenAI/SiteOscillation.lean:182); (whole file, 3 decls) (OpenAI/SpectatorOscillationSupport.lean:37-73); `OpenAI.spectatorCondExpect` (OpenAI/SpectatorSiteExpectation.lean:64); `OpenAI.spectatorCondExpect_apply` (OpenAI/SpectatorSiteExpectation.lean:70); 4 decls: `mul_kronecker_one_apply`, `kronecker_one_mul_apply`, `spectatorCondExpect_commute`, `spectatorGlueEquiv` (OpenAI/SpectatorSiteExpectation.lean:98-130); 4 decls: `spectatorCondExpect_submatrix_eq`, `extendId_sdiff_kronecker_one_submatrix`, `smul_spectatorCondExpect_eq_sum_conj`, `norm_sub_spectatorCondExpect_le` (OpenAI/SpectatorSiteExpectation.lean:166-240) | 449 | — | inline into S10 amplification / S04 spectator conditional expectation anchor (ported from TNLean; paper-anchored: digest mentions oscillation/spectator/twirl); owner anchor to be assigned; inline into S10 amplification anchor (ported from TNLean; paper-anchored: digest mentions oscillation/spectator/twirl); owner anchor to be assigned |

## 11-geometry.md

Lines now (section total): 15871

Conventions in the rows. `G/` = `OpenAI/Geometry/`. `TFD` = `OpenAI/TwoFamilyDecomposition.lean`. §11 is purely geometric except D11.1 and D11.26, so every Geometry declaration is scalar-free; only `two_family_cancellation` and `area_law` carry `[RCLike 𝕜]` (both 𝕜-generic natively; the ℂ-only subadditivity is transferred inside `Arealaw.MState.regionEntropy_union_biUnion_le` via `OpenAI.Embedding`, not in this section). Almost all of the geometry is stated in `ℝ × ℝ` with Mathlib's sup metric and then bridged to `ℤ × ℤ` by `integerPoint`.

| Anchor | Kind | Lean declaration(s) now | Lines now | Status | Action |
|---|---|---|---|---|---|
| D11.1 | Lemma 11.1 | `OpenAI.two_family_cancellation` (OpenAI/TwoFamily.lean:106, states frozen `TwoFamilyCancellation`, Statements.lean:388); helpers `OpenAI.regionEntropy_add_sum_le_of_mutualInfo_le` (TwoFamily.lean:74, the one-family bound = D11.1.1–5), `OpenAI.sdiff_sdiff_union_biUnion_filter` (:39); whole file `OpenAI/TwoFamily.lean`; plus the unused second algebraic encoding `Entropy.OrderedSetFunction.{union_biUnion_le_sum, chain_lower, two_family_le_half_sum_defect, two_family_le_half_sum}` (OpenAI/OrderedEntropyAlgebra.lean:66,164,178,191) | 273 | faithful | keep; golf (the one-family bound for general `p` replaces the paper's `f=0,1` pair; D11.1.6 is the final `linarith`). Cut the four `OrderedSetFunction` decls (nothing uses them; `past`/`defect`/`sum_defect` of the same file are used by `FiniteProductConditional` and belong to another row). Standard: chain rule, subadditivity, purity are already library (`Arealaw.MState.regionEntropy_union_biUnion[_le]`, `regionEntropy_pureState_sdiff`); no Mathlib replacement exists (search pending). Pitfall: OK — hypothesis conditions on the whole union `Λ \ A ∪ ⋃_{j<i, f j = f i} X_j` as one set (TwoFamily.lean:71–73; Statements.lean:395–398). 𝕜-generic. |
| D11.2 | Def (`geometry:exponents`, `geometry:exponent-gaps`) | `OpenAI.Exponents.{boxError, beta, geometryDelta, zeta, rho, geometryEll}` (G/Exponents.lean:22–37), `OpenAI.Exponents.geometry_gaps` (:40); whole file | 46 | faithful | keep; golf (values are `ℚ` and re-cast to `ℝ` at ≈ 100 use sites; `2/1000000` is also written as a numeral 45 times in Geometry/TFD/AreaLaw because the frozen statements spell `1 - 2/1000000`; `1/100000` for `ℓ` likewise). Standard: no (paper-specific). Pitfall: n/a (no declaration for gap roles; all six gaps in one `norm_num`, Exponents.lean:40). |
| D11.3 | Def (birth region, actual region, template of a tile) | `OpenAI.Geometry.RepairSetup.birthRegion` (G/RepairRegions.lean:85), `.currentRegion` (:92), `.finalRegion` (:98); `OpenAI.Geometry.latticeTemplate` (G/TwoFamilyTemplates.lean:38) with `mem_latticeTemplate`, `latticeTemplate_mono`, `coe_latticeTemplate`; `TwoFamilyAssembly.Data.template` (TFD:345), `isBounded_birthRegion`, `mem_template`, `mem_template_of_mem_finalRegion` (TFD:347–365) | 112 | drift | restate or record. paper: closed squares are removed and the open interior is the actual region; Lean: open sup-balls are removed so birth/current/final regions are closed (RepairRegions.lean docstring), and the two agree only on lattice points via `dist_integerPoint_ne_natCast` (G/Octants.lean:611). Decide at restatement: keep the closed convention and record in RefactoringResult §5, or switch to the paper's. Pitfall: n/a |
| D11.4 | Proposition 11.2 | `OpenAI.two_family_decomposition` (TFD:1012, states frozen `TwoFamilyDecomposition`, Statements.lean:410); `TwoFamilyAssembly.beltCells` (TFD:213), `.Data` (:221), `.exists_data` (:249), accessors `Data.{Z, I, R, Z_nonempty, latticeHyp, mem_fineLayerIndices_zOf, mem_M_of_mem_beltCellMarks}` (:266–296) | 92 | faithful | keep the statement (frozen); the `Data` structure (cut-dependent belt shifts, marks, assigned cells) is the paper's "layer by layer choices" — restate with the paper's names. `Data.decomposition` states the same conclusion again, see D11.25. Pitfall: OK — `∀ D₀ Ctpl, nStar ≥ 1 → ∃ C, ∀ Λ A` (Statements.lean:410–412; proof builds `κ : Consts D₀ Ctpl nStar` first, TFD:1015–1017) and separation (3) is `ambientEDist (T i) (⋃_{j<i, f j = f i} X j)` with `T i` the birth template and `X j` actual (Statements.lean:427–429). |
| D11.5 | Def (origin, dyadic cells) | `OpenAI.Geometry.dyadicOrigin` (G/DyadicOrigin.lean:24 = `(√2, √3)`), `dyadicOrigin_nonintegral` (:36), `dyadicOrigin_supporting_lines_avoid_lattice` (:56); `closure_dyadicCell` etc. (G/DyadicClosure.lean, whole file); half-open cells `dyadicCell`/`dyadicCellIndex`/`dyadicParent` are in G/DyadicLayers.lean:23–35 (counted in D11.6) | 113 | faithful | keep; golf. `C₀` is not defined here but in `Consts` (D11.24) with `2 ≤ C₀`, `4 D₀ + 2 ≤ C₀` — the weaker conditions actually used, not the digest's `C₀ > 100(D₀+1)`. Standard: generic dyadic grid (search pending). Pitfall: n/a |
| D11.6 | Step (neighbourhoods `N_k`, layers `D_k`, dummy tile) | `OpenAI.Geometry.dyadicNeighborhood` (G/DyadicLayers.lean:79), `dyadicLayer` (:122), `dyadicNeighborhood_subset_succ` (:92, nested), `exists_mem_dyadicNeighborhood` (G/DyadicExhaustion.lean:20, exhaustion), `card_dyadicLayerIndices_boundary_le` (G/DyadicLayers.lean:150, count ≤ Cb), `dyadicLayer_dist_lower` (G/DistanceLayers.lean:114) and `dyadicLayer_exists_dist_le` (:63, the two distance bounds); files G/DyadicLayers.lean, G/CellCounting.lean, G/DyadicExhaustion.lean, G/DistanceLayers.lean (all but the two D11.7 decls), G/LayerPartition.lean, G/FineCellPartition.lean (unique layer/fine cell of a point outside `N_{k₀}`; bridges to D11.8/D11.11) | 600 | smeared | merge into one `step_11_6` with the three bullets; keep each distance bound as a `have`. Dead inside: `dyadicLayer_infDist_bounds`, `iUnion_dyadicNeighborhood_eq_univ`, `dyadicNeighborhood_union_iUnion_layers_eq_univ`, `dyadicNeighborhood_union_iUnion_fineCells_eq_univ` (refcount 0) — cut. Standard: Whitney-type layering (search pending; no Mathlib). Pitfall: n/a |
| D11.7 | Step (`geometry:nonadjacent`) | `OpenAI.Geometry.dyadicLayer_dist_nonadjacent` (G/DistanceLayers.lean:163, bound `(C-1)/2 · 2^h`), `dyadicLayer_dist_separation` (:148, = D11.7.1) | 26 | faithful | keep. Elementary. Fine-scale variant `dyadicLayer_dist_nonadjacent_fineScale` is in G/LocalLayers.lean (counted in D11.13). Pitfall: n/a |
| D11.8 | Def (scales `s_k, t_k`, belt cells, pitch interiors, primary tiles) | `OpenAI.Geometry.fineScaleIndex` (G/DyadicScales.lean:25, `⌊ζk⌋`), `pitchScaleIndex` (:28, `⌊(1+δ₀)k⌋`), `fineScaleIndex_succ` (G/AdjacentScales.lean:29), `dyadicScale_side_ratios` (G/ScaleSeparation.lean:44, `t ≪ r ≪ s` above threshold `10⁷d`), fine cells `dyadicRefinement`/`fineLayerIndices` (G/DyadicRefinement.lean:38,98); files G/DyadicScales.lean, G/AdjacentScales.lean, G/ScaleSeparation.lean, G/DyadicRefinement.lean. Belt cells: `beltCellIndices` (D11.9); pitch interiors and primaries: `pitchInterior`, `primaryBirthRegion` (D11.10) | 334 | faithful | keep; golf. Dead: `fineScale_dvd_layerScale`, `layerScale_dvd_pitchScale`, `fineScale_side_succ`, `card_fineLayerIndices_le`, `exists_dyadicScale_side_ratios` (refcount 0). Standard: no. Pitfall: OK — exponents are floors so divisibility is `pow_dvd_pow` (DyadicScales.lean:46,50) and mesh ratio `≤ 2` is `fineScaleIndex_succ` (AdjacentScales.lean:29). |
| D11.9 | Step (`geometry:belt-count`) | `OpenAI.Geometry.exists_sparse_dyadic_belt_shift` (G/FineBelts.lean:75), via `exists_fine_belt_shift` (:56) and `exists_sparse_belt_shift` (G/SparseBelts.lean:23, pigeonhole form of the averaging), `dyadicScale_ratio_le` (FineBelts.lean:35, D11.9.4); files G/SparseBelts.lean, G/FineBelts.lean | 153 | faithful | keep; inline `exists_fine_belt_shift` and `dyadic_scale_ratio` into it (each used once). Standard: averaging over residue classes — Mathlib pigeonhole `Finset.exists_card_fiber_lt_of_card_lt_mul` is already used. Pitfall: n/a |
| D11.10 | Step (`geometry:primary-pieces`) | `OpenAI.Geometry.primaryBirthRegion` (G/PrimaryRegions.lean:61), `primaryBirthRegion_dist_le` (:91, diameter), `primaryBirthRegion_dist_separation` (:130, ≥ `t_k` apart), `card_primaryPitchIndices_boundary_le` (G/PrimaryCounting.lean:142, ≤ Cb per layer), `card_primaryFragmentIndices_le` (PrimaryRegions.lean:168, ≤ C(s/r+2)² pieces), `primaryBirthRegion_eq_iUnion_primaryFragment` (G/PrimaryFragments.lean:48), parity separation `primary_contact_parities_ne` (G/InitialRegionInterfaces.lean:54, counted in D11.11); files G/PrimaryRegions.lean, G/PrimaryFragments.lean, G/PrimaryCounting.lean, G/PrimaryFineCellCover.lean, G/NonbeltPrimaries.lean | 724 | smeared | merge into one `step_11_10`. Second description of the same set: rectangular fragments (PrimaryFragments) and unions of non-belt fine cells (PrimaryFineCellCover, NonbeltPrimaries, 254 lines, bridging the two); keep one, cut the bridge. Dead: `primaryBirthRegion_diam_le`, `primaryFragment_diam_le`. Standard: elementary counting (search pending). Pitfall: n/a |
| D11.11 | Step (fans, labels, point-contact property) | no declaration states "positive-length interface ⇒ opposite labels ⇒ same-label contact is a point at a belt cell"; the interface half is `OpenAI.Geometry.initialRegionColor_ne_of_segment_subset_inter` (G/InitialRegionInterfaces.lean:104); colours `beltCellFanColor` (G/BeltFanColors.lean:83), fans `cellFanPolygon` (G/CellFans.lean:337), runs `cellFanRunRegion` (G/FanRuns.lean:140), identifiers `InitialRegionIndex`, `initialBirthRegion`, `initialRegionColor` (G/InitialRegions.lean:54,71,95), side subdivision `fineLayerSplitMask` (G/SideSubdivisionMask.lean:40); 29 files (list in mapped.txt): CellFans, CellFanCycle, CellFanSlopes, FanRegularity, FanRuns, FanRunContacts, FanSideContacts, BeltFanColors, BeltRunInterfaces, ElementarySideOpponents, ElementarySideOpponentUniqueness, ElementarySideReciprocity, SideSubdivision, SideSubdivisionMask, SideEndpoints, ActualSideMatching, CellContacts, CellSides, DummyContacts, DummyCorners, DummyRunInterfaces, FinCyclicInduction, InitialRegions, InitialRegionInterfaces, InitialRegionInteriors, InitialRegionRegularity | 5506 | smeared | restate as one `step_11_11` (interfaces joining opposite labels, then the point-contact corollary D11.11.6) proved along D11.11.1–5. Overbuilt in practice: ≈ 1 700 lines (ActualSideMatching 464, ElementarySideOpponents 452, …Uniqueness 320, …Reciprocity 144, CellContacts 498) classify contacts between actual rectangles to recover "each belt side has ≤ 2 elementary segments, opposing region is one cell" (paper: one paragraph D11.11.1); `elementarySideOpponent_reciprocal_iff` is dead. Route differences: paper chooses "any opposite pair" on a shared belt side (D11.11.3); Lean fixes it by a lexicographic cell key (BeltFanColors.lean:42 `cellKey`, `beltCellFanColor`). Dead: `FinCyclicInduction` has 3 unused lemmas. Standard: no. Pitfall: n/a |
| D11.12 | Def (initial marks) | `OpenAI.Geometry.beltCellMarks` (G/BeltMarks.lean:39), `beltMarks` (:47), `card_beltMarks_le` (:88, ≤ 9·cells); scale `S_v` = smallest incident side: `exists_least_incident_scales` (G/InitialMarkFamily.lean:160, private); files G/BeltMarks.lean, G/InitialMarkFamily.lean (also holds `exists_uniform_separated_initial_marks` :188 = D11.13(1), and `finite_support_of_summable_nat_counts` :49 = D11.19.4's "finite sum") | 350 | faithful | keep; split `InitialMarkFamily` by anchor (marks → here, separation → D11.13, finiteness → D11.19). Dead: `exists_sparse_dyadic_belt_marks_shift`. Standard: notation. Pitfall: n/a |
| D11.13 | Lemma 11.3 (`geometry:initial-stars`) | no declaration states it as a theorem; packaged as `OpenAI.Geometry.initialRepairSetup_latticeHyp` (G/InitialRepairSetup.lean:152: separation `sep₀`, star `star₀`, opposite labels `label₀_ne`, with `a₀ := 1/64` in `initialRepairSetup` :138); separation of marks `exists_uniform_separated_initial_marks` (G/InitialMarkFamily.lean:188, in D11.12's files); local geometry in 11 files: InitialRepairSetup, InitialSectorAssignment, InitialSectorColors, InitialStarFrontiers, NearMarkGeometry, MeshGeometry, FineMarkSeparation, AllowedSlopeAffineLine, FiniteUnionFrontier, ConcentricFans, CellFanSectors, LocalLayers | 1816 | smeared | restate as `lemma_11_3`. Route: paper picks `a₀` small against the finite quarter-mesh patterns (D11.13.4); Lean fixes `a₀ = 1/64` and proves explicit clearances (`affineMesh_dist_ge` G/MeshGeometry.lean:65, `fineLayer_marks_dist_ge` G/FineMarkSeparation.lean:77, `fine_fan_frontier_near_allowed` G/InitialStarFrontiers.lean:128) — equivalent but not a "finite pattern" argument. Standard: no. Pitfall: OK — `a₀ = 1/64` is a literal in `RepairSetup.a₀` (InitialRepairSetup.lean:146), so it cannot depend on `k` or the shifts; star radius `t/64` via the cell scale. |
| D11.14 | Def (stopping scale, trim radius, repair rule) | `OpenAI.Geometry.repairHalfSide` (G/SimultaneousRepair.lean:54, `2^⌊ρ₀ log₂ S⌋`), margins `half_rpow_le_repairHalfSide` (:77), `repairHalfSide_le_rpow` (:70), `eventually_repairHalfSide_le` (:97, existence of `S_*`); repair rule itself in `RepairSetup.markOct`/`birthRegion`/`finalRegion` and `IsNonterminal` (G/RepairRegions.lean:80,85,98; G/RepairTree.lean:140, counted in D11.15); whole file G/SimultaneousRepair.lean | 171 | smeared | merge into D11.15's file; restate with `d(S)` named. Second encoding of the removal rule: `repairSquare`, `repairRemovalSet`, `simultaneousRepairRemnants`, `repairChildLocation`, `repairChildScale` (SimultaneousRepair.lean:122–167, refcount 0/1) are unused (the live rule is `finalRegion`'s `Metric.ball`) — cut. `eventually_repairHalfSide_margins` dead. Standard: no. Pitfall: OK — old identifiers lose the ball of generation `g` before replacements born at `g+1` exist: `RepairId.birthGen (repl m _) = m.gen + 1` and `finalRegion` subtracts only marks with `birthGen ≤ m.gen` (RepairRegions.lean:56–62, 98–101). |
| D11.15 | Lemma 11.4 (`geometry:repair-induction`) | no single statement; star at every mark: `OpenAI.Geometry.RepairSetup.Hyp.currentRegion_inter_closedBall` (G/RepairRegions.lean:379) via `currentRegion_child_inter_closedBall` (:282); disjointness/separation `TreeHyp.dist_markPos_of_gen_eq` (G/RepairTree.lean:235); descendant bound `TreeHyp.dist_markPos_descendant_add_markRadius_le` (:308); termination `TreeHyp.exists_gen_le` (:338), `finite_isMark` (:375); labels `Hyp.label_markOct_ne` (RepairRegions.lean:407); octant calculus for children `childOctant`, `mem_octantConeAt_child_iff` (G/Octants.lean:81,415); files G/RepairRegions.lean, G/RepairTree.lean, G/Octants.lean | 1464 | smeared | restate as one `lemma_11_4` (induction on generation, steps D11.15.1–7 as `have`s). Octants.lean is shared with D11.18 (`half_le_dist_of_mem_octantTriangle_succ/pred`). Dead: `iUnion_octantCone`, `mem_octantConeAt_lineMap`, `RepairMark.gen_descend`. Standard: no. Pitfall: OK — `a₀` is one field of `RepairSetup` (RepairTree.lean:113–115) and `TreeHyp` requires only `margin` with `a₀/1000` (:157–162); the induction `currentRegion_inter_closedBall` has the same radius `a₀ · scale` at every generation. |
| D11.16 | Step (edges avoid lattice sites) | `OpenAI.Geometry.initialBirthRegion_frontier_avoid_lattice` (G/InitialRegionBoundaries.lean:207), `initialBirthRegion_lattice_mem_iff_initialOpenRegion` (:239), `exists_unique_initialOpenRegion_integerPoint` (G/InitialLatticePartition.lean:35), `dyadicOrigin_supporting_lines_avoid_lattice` (D11.5's file), partition after repair `RepairSetup.LatticeHyp.eq_of_mem_finalRegion` (G/RepairPartition.lean:79) and `exists_mem_finalRegion_or_terminal` (:139); files G/RepairPartition.lean, G/InitialRegionBoundaries.lean, G/InitialLatticePartition.lean, G/FanFrontiers.lean | 617 | smeared | merge into `step_11_16`. Route: paper shows every edge lies on one of four line families with `m ∈ ℤ`; Lean proves it for initial regions (`*_onSupportingLine`) but for removal squares uses integer half-sides (`dist_integerPoint_ne_natCast`, Octants.lean:611). Dead: `initialOpenRegion_frontier_avoid_lattice`. Standard: elementary. Pitfall: n/a |
| D11.17 | Def (order of tile identifiers) | `TwoFamilyAssembly.Data.rank` (TFD:315: 0 primaries, 1 runs, `g+2` replacements), `OpenAI.Geometry.exists_equiv_fin_rank_monotone` (TFD:44); dummy excluded in `Data.IsTile` (TFD:297, counted in D11.25) | 65 | faithful | keep. Pitfall: n/a |
| D11.18 | Lemma 11.5 (`geometry:birth-separation`) | two declarations, no single statement: belts `OpenAI.Geometry.half_le_dist_of_mem_initialBirthRegion_beltRun` (G/BeltSeparation.lean:745: `≥ r₀/2`, `r₀ ≤ t/4096`), replacements `RepairSetup.Hyp.half_le_dist_of_mem_birthRegion_repl` (G/RepairSeparation.lean:35: `≥ d(u)/2`); combined as `TwoFamilyAssembly.Data.clearance_le_dist` (TFD:510, in D11.25); files G/BeltSeparation.lean (1 050), G/RepairSeparation.lean | 1194 | drift | restate along D11.18.1–7. paper: finite patterns + compactness giving `c₁ u^{ρ₀}`, angular gap at contacts (D11.18.5); Lean: explicit constants (`t/4096`, `d(u)/2`), 3-case mesh analysis by hand (BeltSeparation: cellFanOctantSlot… `ball_diff_closure_subset_closure_of_mem_segment`, 700+ lines of segment/rectangle geometry), angular gap by octants. Same conclusion, no compactness; belts and replacements are two lemmas not one. Standard: compactness + pattern argument (search pending). Pitfall: OK — rate comes from the trim (`d(u)/2`, RepairSeparation.lean:35), and the comparison is birth template vs *final* region of earlier tiles (TFD:510 `clearance_le_dist … hy : integerPoint y ∈ finalRegion b`). |
| D11.19 | Step (`geometry:descendant-count`, `geometry:total-repairs`) | depth `OpenAI.Geometry.exists_repair_depth_bound` (G/RepairDepth.lean:121), descendants `exists_repair_descendant_count_bound` (:160), layer form `exists_repair_descendant_count_layer_bound` (:220), total `exists_ncard_isMark_le` (G/TwoFamilyCounting.lean:153) and its instance `TwoFamilyAssembly.Data.card_marks_le` (TFD:595); series `summable_rpow_mul_two_rpow_neg` (TwoFamilyCounting.lean:125); files G/RepairDepth.lean (minus `eventually_fine_clearance`), G/PolynomialBudget.lean, and `Data.{marks, mem_marks, card_marks_le}` | 512 | smeared | merge into `step_11_19` (D11.19.1–4). Standard: bookkeeping (geometric series: Mathlib `tsum_geometric`-type lemmas partly used; search pending). Pitfall: n/a |
| D11.20 | Step (`geometry:bad-sites`) | `TwoFamilyAssembly.Data.card_le_of_subset_exceptional` (TFD:627: any `D` inside the closed dummy neighbourhood or terminal squares has `\|D\| ≤ C b`), `OpenAI.Geometry.card_latticeTemplate_closure_dyadicNeighborhood_le` (G/TwoFamilyCounting.lean:93), `card_latticeTemplate_closedBall_le` (:47) and 3 helpers (lines 34–124) | 182 | faithful | keep. Lean states it for any subset of exceptional sites; `D := A \ ⋃ X_i` is shown inside it in `Data.decomposition` (TFD:971). Standard: bookkeeping. Pitfall: n/a |
| D11.21 | Step (`geometry:primary-scale`, `geometry:primary-limits`) | `OpenAI.Geometry.primaryScanScale` (G/TwoFamilyScales.lean:94, `⌈C_P (2^k)^{1+2δ₀}⌉`), `primaryScanScale_bounds` (:153), `isTemplate_primary` (G/TwoFamilyTemplates.lean:142, `N₀ ≤ (2^{p-k}+2)²`, template of Def 9.3), helpers `two_pow_pitchScaleIndex_sub_le` (TwoFamilyScales.lean:83), `eventually_mul_rpow_lt_rpow` (:43), `isTemplate_latticeTemplate_of_eq_biUnion` (TwoFamilyTemplates.lean:105); the `o(r)`, `o(t_k)` limits are folded into `exists_twoFamily_constants` (D11.24) as eventual inequalities | 269 | smeared | merge into `step_11_21`; replace the explicit `18 M + 1` by `C_P` with the digest's `C_P ≥ 18 C C_tpl`. Pitfall: n/a |
| D11.22 | Step (belt tiles and replacements) | `OpenAI.Geometry.tileScanScale` (G/TwoFamilyScales.lean:99, `⌈C_B u⌉`), `tileScanScale_bounds` (:104), `isTemplate_beltRun` (G/TwoFamilyTemplates.lean:168), `isTemplate_repl` (:199) | 118 | smeared | merge into `step_11_22` with D11.21. Pitfall: n/a |
| D11.23 | Step (cut clearance of belt/replacement templates; hypotheses of Lemma 9.4) | `TwoFamilyAssembly.Data.tileSpec` (TFD:375, 135 lines; `TileSpec` TFD:366 = `nStar ≤ n`, `IsTemplate`, `IsSeparatedFromCut D₀`, `collarWidth n ≤ s`, cut clearance `2 n^β < …`, and `2 n^β < clearance`), `RepairSetup.TreeHyp.markRadius_le_two_mul_root` (TFD:128, the D11.15.6 `2d(S)` bound) | 160 | faithful | keep; golf. The Lemma 9.4 hypotheses are the frozen predicates `IsTemplate`/`IsSeparatedFromCut`, so no separate verification appears. Pitfall: n/a |
| D11.24 | Step (`geometry:fine-clearance`, order of thresholds) | `OpenAI.Geometry.exists_twoFamily_constants` (G/TwoFamilyScales.lean:228, `∃ C₀ C_P C_B S_* k₀` with all inequalities), repeated as structure `TwoFamilyAssembly.Consts` (TFD:144, plus `K`, `B₀`), `nonempty_consts` (:196), `Consts.C` (:208); `OpenAI.Geometry.eventually_fine_clearance` (G/RepairDepth.lean:266, `c₁` form), `repairHalfSide_le_repairHalfSide` (TwoFamilyScales.lean:306) | 192 | faithful | keep; merge the duplicate statement (`exists_twoFamily_constants` and `Consts` say the same, so state once). `c₁` of D11.18 is replaced by the explicit `d(u/2)/2`; `eventually_fine_clearance` is then the `ρ₀ > β` step. Pitfall: OK — `S_* := max S₀ (max 2 n_*)` before `k₀ := max K 5·10⁷` (TwoFamilyScales.lean:264, 284), `a₀ = 1/64` literal, `C₀` first, so constants precede thresholds (statement order TwoFamilyScales.lean:228–231). |
| D11.25 | Step (conclusion of Prop 11.2) | `TwoFamilyAssembly.Data.decomposition` (TFD:936, same conclusion as D11.4); `Data.clearance_le_dist` (TFD:510, = D11.25.3), `sum_primary_le`, `card_run_le`, `card_repl_le`, `sum_le` (TFD:724–935, = D11.25.4), `Data.{IsTile, finite_isTile, tiles, mem_tiles, scanScale, pieceScale, clearance, IsPrimary, IsRun, layer, pitchIndex, cell, markOf, one_le_scanScale, inv_scanScale_pow_le_one}` (TFD:297–345, 685–723) | 448 | faithful | inline into D11.4 (the conclusion is stated twice: `Data.decomposition` and `two_family_decomposition`); keep the proof along D11.25.1–4. Pitfall: n/a |
| D11.26 | Theorem 1.1 | `OpenAI.area_law` (OpenAI/AreaLaw.lean:94, proves frozen `AreaLaw`), step D11.26.2–4 as `OpenAI.exists_mutualInfo_exterior_union_le` (AreaLaw.lean:37, used once); D11.26.3 in `OpenAI.exterior_union_subset_graphNeighborhood_compl_of_lt_ambientEDist` (OpenAI/GraphNeighborhoodCutClearance.lean:136, whole file 145 lines); `n_*` threshold `OpenAI.Exponents.exists_collar_radius_threshold` (OpenAI/AmplificationCutClearance.lean:115, counted in §10) | 93 | faithful | keep `area_law`; inline `exists_mutualInfo_exterior_union_le` or name it `step_11_26_4`. Differences from the digest: D11.26.1 handles only `b = 0` (via Lemma 2.2, `regionEntropy_eq_zero_of_edgeBoundary_eq_empty`), not `Λ=∅`, `A∈{∅,Λ}`, `q=1`, `R=0` separately (they are all `b = 0` or covered by `log q ≥ 0`; `q = 1` needs no case); `Ctpl` is obtained from `collar_bound` (an ∃), not fixed first; `D₀ := 2R + 11`. 𝕜-generic natively (`variable [RCLike 𝕜]`, AreaLaw.lean:33). Pitfall: OK — `n₀ := max (max n₁ n₂) N` is fixed before any `n`, `r` (AreaLaw.lean:62, `∀ n ≥ n₀`, `r` obtained inside), `two_family_decomposition (2R+11) Ctpl n₀` is called after `n₀` (:96–97) and `C := C·(log q + CM/2)` is chosen before `∀ Λ Φ Ω A` (:97); `AreaLaw` fixes `∀ q R J Δ ∃ C ∀ Λ Φ A` (Statements.lean). |
| (section infra) | — | G/AmbientDistanceBridge.lean (whole, 59 lines; `integerPoint` ↔ `ambientEDist` conversion, two decls dead); G/TemplatePolygons.lean (56, `TemplatePolygon`, `IsAllowedSlope` abbreviation); TFD generic helpers `ofReal_lt_ambientEDist_of_le_dist`, `repairHalfSide_le_self`, `sum_half_pow_le_two`, `isBounded_closure_dyadicCell`, `isBounded_closure_dyadicNeighborhood`, `cellFanRunRegion_subset_closure_dyadicCell`, `closure_dyadicCell_subset_closure_dyadicLayer`, `mem_closure_dyadicLayer_of_mem_beltCellMarks`, `fineScale_le_two_mul_of_mem_beltCellMarks` (TFD:60–127) | 183 | none | golf; cast bridges (`integerPoint`, `ambientEDist` ↔ `dist`) disappear once the planar/lattice encodings are unified; `IsAllowedSlope` is a one-line abbreviation of frozen `HasTemplateSlope` — inline. |
| (section infra, reverse pass) | — | `OpenAI.Geometry.sum_weighted_dyadic_rpow_le` (OpenAI/Geometry/DyadicWeightedSum.lean:23) | 58 | — | inline into S11 CappedDyadicPartition user (one caller); weighted dyadic rpow sum bound |
## Unmapped

| Category | Declarations | Lines |
|---|---|---|
| standard | 322 | 5854 |
| scaffold | 93 | 1463 |
| dead | 269 | 4598 |
| foreign | 321 | 5266 |
| total | 1005 | 17181 |

### Arealaw/Bell.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 7 decls) | Arealaw/Bell.lean:21-47 | 49 | foreign | cut (BH12 Bell-pair/dimer example, arXiv:1309.3789; no anchor in digest) |

### Arealaw/Chain.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 13 decls) | Arealaw/Chain.lean:23-99 | 104 | foreign | cut (BH12 dimer-chain area-law example, arXiv:1309.3789) |

### Arealaw/Cor.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 28 decls) | Arealaw/Cor.lean:32-212 | 226 | foreign | cut (BH12 correlation function / area-law corollary) |

### Arealaw/DataHiding.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | Arealaw/DataHiding.lean:38-48 | 68 | foreign | cut (BH12 data-hiding step; no anchor in digest) |

### Arealaw/EDC.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 3 decls) | Arealaw/EDC.lean:22-40 | 47 | foreign | cut (BH12 exponential decay of correlations hypothesis) |

### Arealaw/Entropy.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Arealaw.H₂` | Arealaw/Entropy.lean:68 | 2 | dead | cut (reachable only by name collision with hypothesis names `H₂`; only real user is Mixed.entropy₂_eq_H₂, itself unreachable) |
| `Arealaw.H₂_def` | Arealaw/Entropy.lean:70 | 3 | dead | cut |

### Arealaw/Equipartition.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 36 decls) | Arealaw/Equipartition.lean:72-632 | 663 | foreign | cut (BH12 Lemma 19 quantum equipartition) |

### Arealaw/Fidelity.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Arealaw.conjTranspose_cfcSqrt` | Arealaw/Fidelity.lean:46 | 52 | standard | replace-by CFC.sqrt_nonneg (self-adjointness from `.isSelfAdjoint`) |
| `Arealaw.cfcSqrt_eq_cfc_real_sqrt` | Arealaw/Fidelity.lean:53 | 5 | standard | library tree (Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow; `CFC.sqrt_eq_real_sqrt` is the cfcₙ form) |
| `Arealaw.cfcSqrt_diagonal` | Arealaw/Fidelity.lean:58 | 7 | dead | cut |
| `Arealaw.re_trace_cfc` | Arealaw/Fidelity.lean:65 | 4 | standard | replace-by HermitianMat.trace_cfc_eq (Physlib QuantumInfo; ℂ) / Matrix.IsHermitian.trace_eq_sum_eigenvalues |
| `Arealaw.re_trace_cfcSqrt` | Arealaw/Fidelity.lean:69 | 7 | standard | replace-by HermitianMat.trace_cfc_eq (Physlib QuantumInfo; ℂ) / Matrix.IsHermitian.trace_eq_sum_eigenvalues |
| `Arealaw.conjTranspose_cfcSqrt_mul_mul_cfcSqrt_mul` | Arealaw/Fidelity.lean:76 | 9 | dead | cut |
| `Arealaw.traceNorm_conjTranspose_square` | Arealaw/Fidelity.lean:85 | 9 | standard | replace-by Matrix.traceNorm_conjTranspose (Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm; ℂ only) |
| `Arealaw.traceNorm_conjTranspose` | Arealaw/Fidelity.lean:94 | 14 | standard | replace-by Matrix.traceNorm_conjTranspose (Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm; ℂ only) |
| 6 decls: `trace_fromBlocks`, `posSemidef_fromBlocks_zero`, `cfcSqrt_fromBlocks_zero`, `traceNorm_fromBlocks_zero`, `posSemidef_fromBlocks_one`, `traceNorm_fromBlocks_zero_diag` | Arealaw/Fidelity.lean:108-150 | 50 | standard | library tree (LinearAlgebra/Matrix/Block; block trick for re_trace_le_traceNorm, droppable if Physlib SVD route is used) |
| `Arealaw.re_trace_le_traceNorm` | Arealaw/Fidelity.lean:158 | 20 | standard | library tree (Analysis/Matrix, cf. Physlib QuantumInfo/ForMathlib/MatrixNorm/TraceNorm) |
| `Arealaw.norm_trace_le_traceNorm` | Arealaw/Fidelity.lean:178 | 11 | standard | library tree (Analysis/Matrix, cf. Physlib QuantumInfo/ForMathlib/MatrixNorm/TraceNorm) |
| `Arealaw.fidelity` | Arealaw/Fidelity.lean:189 | 3 | standard | library tree (Physlib QuantumInfo/States/Mixed/Fidelity; 𝕜-generic ‖√A√B‖₁ form) |
| `Arealaw.fidelity_def` | Arealaw/Fidelity.lean:192 | 3 | standard | library tree (Physlib QuantumInfo/States/Mixed/Fidelity; 𝕜-generic ‖√A√B‖₁ form) |
| 4 decls: `fidelity_nonneg`, `fidelity_comm`, `fidelity_eq_re_trace_sqrt`, `fidelity_self` | Arealaw/Fidelity.lean:195-209 | 23 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Arealaw.re_trace_mul_nonneg` | Arealaw/Fidelity.lean:218 | 5 | standard | replace-by Matrix.PosSemidef.trace_mul_nonneg (Physlib QuantumInfo.Channels.Dual) |
| `Arealaw.projLT_zero_mul_self` | Arealaw/Fidelity.lean:223 | 5 | dead | cut |
| `Arealaw.self_mul_projLT_zero` | Arealaw/Fidelity.lean:228 | 6 | dead | cut |
| 4 decls: `trace_mul_sub_eq_trace_mul_add`, `re_trace_sq_sqrt_sub_le_traceNorm_sub`, `re_trace_sq_sqrt_sub`, `trace_add_trace_sub_two_mul_fidelity_le_traceNorm_sub` | Arealaw/Fidelity.lean:234-286 | 59 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### Arealaw/Geometry.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 29 decls) | Arealaw/Geometry.lean:30-149 | 154 | foreign | cut (BH12 site-metric geometry) |

### Arealaw/Kronecker.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 4 decls) | Arealaw/Kronecker.lean:23-54 | 59 | dead | cut (entropy additivity over tensor products; unused; Physlib has Sᵥₙ_of_prod-type results; Mathlib candidate no) |

### Arealaw/Ladder.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 25 decls) | Arealaw/Ladder.lean:50-243 | 263 | foreign | cut (BH12 ladder/quartering lemmas) |

### Arealaw/Mixed.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Arealaw.SubState.regionEntropy₂` | Arealaw/Mixed.lean:273 | 4 | dead | cut [name also occurs in A/Subadditivity: user is itself unreachable or a name collision; confirm] |
| 5 decls: `regionEntropy₂_def`, `regionEntropy₂_nonneg`, `mutualInfo₂`, `mutualInfo₂_def`, `mutualInfo₂_eq` | Arealaw/Mixed.lean:277-295 | 24 | dead | cut |
| `Arealaw.Qubits` | Arealaw/Mixed.lean:320 | 22 | dead | cut (`Qubits n`: only user is out-of-closure Ladder/Saturation) |

### Arealaw/OpNorm.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Arealaw.euclidean_norm_comp_le` | Arealaw/OpNorm.lean:34 | 41 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.euclidean_norm_sq_prod` | Arealaw/OpNorm.lean:42 | 5 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.kronecker_one_mulVec_apply` | Arealaw/OpNorm.lean:47 | 7 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.kronecker_comm_submatrix` | Arealaw/OpNorm.lean:54 | 12 | standard | library tree (LinearAlgebra/Matrix/Kronecker) |
| `Arealaw.l2_opNorm_le_bound` | Arealaw/OpNorm.lean:66 | 6 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.norm_entry_le_l2_opNorm` | Arealaw/OpNorm.lean:72 | 5 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.l2_opNorm_submatrix_id_le` | Arealaw/OpNorm.lean:77 | 7 | standard | library tree (Analysis/CStarAlgebra/Matrix; equiv case: Physlib Matrix.opNorm_reindex_proven, Mathlib Matrix.permMatrix_l2_opNorm_le) |
| `Arealaw.l2_opNorm_submatrix_le` | Arealaw/OpNorm.lean:84 | 8 | standard | library tree (Analysis/CStarAlgebra/Matrix; equiv case: Physlib Matrix.opNorm_reindex_proven, Mathlib Matrix.permMatrix_l2_opNorm_le) |
| `Arealaw.l2_opNorm_submatrix` | Arealaw/OpNorm.lean:92 | 7 | standard | library tree (Analysis/CStarAlgebra/Matrix; equiv case: Physlib Matrix.opNorm_reindex_proven, Mathlib Matrix.permMatrix_l2_opNorm_le) |
| `Arealaw.l2_opNorm_kronecker_one_le` | Arealaw/OpNorm.lean:99 | 10 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.l2_opNorm_one_kronecker_le` | Arealaw/OpNorm.lean:109 | 5 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.l2_opNorm_kronecker_le` | Arealaw/OpNorm.lean:114 | 6 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/MatrixKroneckerContraction: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Arealaw.l2_opNorm_kronecker_le_one` | Arealaw/OpNorm.lean:120 | 5 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/MatrixKroneckerContraction: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Arealaw.l2_opNorm_one_le` | Arealaw/OpNorm.lean:125 | 5 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.l2_opNorm_le_one_of_conjTranspose_mul_self` | Arealaw/OpNorm.lean:130 | 6 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| `Arealaw.l2_opNorm_le_one_of_mem_unitaryGroup` | Arealaw/OpNorm.lean:136 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Arealaw.l2_opNorm_single` | Arealaw/OpNorm.lean:147 | 7 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Arealaw.l2_opNorm_le_one_of_nonneg_of_le_one` | Arealaw/OpNorm.lean:154 | 12 | standard | library tree (Analysis/CStarAlgebra/Matrix) |

### Arealaw/Postselection.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 4 decls) | Arealaw/Postselection.lean:23-66 | 75 | foreign | cut (BH12 Lemma 9 postselection) |

### Arealaw/PurifiedDist.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 31 decls) | Arealaw/PurifiedDist.lean:47-183 | 187 | foreign | cut (BH12/Renner purified distance) |

### Arealaw/Purify.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 16 decls) | Arealaw/Purify.lean:36-126 | 131 | dead | cut (explicit purification; unused; Physlib MState.purify exists) |

### Arealaw/PurifyChain.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 32 decls) | Arealaw/PurifyChain.lean:37-241 | 248 | foreign | cut (BH12 ancilla-as-extra-site chain) |

### Arealaw/SVD.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Arealaw.exists_mem_unitaryGroup_eq_mul_diagonal` | Arealaw/SVD.lean:26 | 48 | standard | replace-by Matrix.exists_svd_sqrt_eigenvalues (Physlib QuantumInfo; ℂ only) |
| `Arealaw.exists_mem_unitaryGroup_trace_mul_eq_traceNorm` | Arealaw/SVD.lean:49 | 13 | standard | library tree (Analysis/Matrix, cf. Physlib QuantumInfo/ForMathlib/MatrixNorm/TraceNorm) |

### Arealaw/Sanity/FannesPurifiedDistance.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 17 decls) | Arealaw/Sanity/FannesPurifiedDistance.lean:43-140 | 151 | foreign | cut (BH12 Fannes–Audenaert sanity check) |

### Arealaw/Saturation.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 6 decls) | Arealaw/Saturation.lean:35-84 | 102 | foreign | cut (BH12 Lemma 16 saturation) |

### Arealaw/SmoothEntropy.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 36 decls) | Arealaw/SmoothEntropy.lean:70-304 | 309 | foreign | cut (BH12 smooth entropy) |

### Arealaw/Spectrum.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 4 decls) | Arealaw/Spectrum.lean:25-43 | 47 | dead | cut (sorted eigenvalues; unused; Mathlib candidate: Matrix.IsHermitian.eigenvalues₀ ordering API) |

### Arealaw/Uhlmann.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 6 decls) | Arealaw/Uhlmann.lean:45-97 | 105 | dead | cut (Uhlmann theorem, Renner05; unused in closure; Physlib has fidelity/Uhlmann; Mathlib candidate no) |

### OpenAI/Bridges.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.regEquivPiSubtype` | OpenAI/Bridges.lean:62 | 69 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.regEquivPiSubtype_apply` | OpenAI/Bridges.lean:70 | 4 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.regEquivPiSubtype_symm_apply` | OpenAI/Bridges.lean:74 | 6 | dead | cut (@[simp]/instance: may fire implicitly; check by deleting) |
| `OpenAI.regSdiffEquivPiSubtype` | OpenAI/Bridges.lean:80 | 8 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.regSdiffEquivPiSubtype_apply` | OpenAI/Bridges.lean:88 | 5 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.regSdiffEquivPiSubtype_symm_apply` | OpenAI/Bridges.lean:93 | 7 | dead | cut (@[simp]/instance: may fire implicitly; check by deleting) |
| `OpenAI.piEquivPiSubtypeProd_symm_regEquivPiSubtype` | OpenAI/Bridges.lean:100 | 23 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.ptrace_eq_traceRight_piEquivPiSubtypeProd` | OpenAI/Bridges.lean:123 | 18 | dead | cut |
| `OpenAI.regionEntropy_pureState_eq_sum_negMulLog` | OpenAI/Bridges.lean:141 | 16 | dead | cut |
| `OpenAI.map_embeddingSubtype_subset` | OpenAI/Bridges.lean:157 | 8 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.mem_map_embeddingSubtype_iff` | OpenAI/Bridges.lean:165 | 10 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.regionEntropy_pureState_map_embeddingSubtype` | OpenAI/Bridges.lean:175 | 14 | dead | cut |
| `OpenAI.regionEntropy_pureState_eq_sum_negMulLog_subtype` | OpenAI/Bridges.lean:189 | 20 | dead | cut |
| `OpenAI.norm_toLp_eq_one_iff` | OpenAI/Bridges.lean:209 | 12 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.normalized_eigen_hasGlobalGap_iff_euclidean` | OpenAI/Bridges.lean:221 | 20 | scaffold | cut once encodings unified (Reg ↔ Pi-subtype / Euclidean / Walk encodings) |
| `OpenAI.exists_walk_length_le_iff_edist_le` | OpenAI/Bridges.lean:241 | 13 | standard | replace-by SimpleGraph.exists_walk_of_edist_ne_top + SimpleGraph.edist_le (Mathlib Combinatorics/SimpleGraph/Metric) |
| 8 decls: `piProd_one`, `single_eq_piProd`, `extendId_piProd`, `isSupportedOn_extendId`, `isSupportedOn_zero`, `isSupportedOn_one`, `add`, `smul` | OpenAI/Bridges.lean:300-364 | 74 | scaffold | cut once encodings unified (state IsSupportedOn as a Subalgebra / AlgHom.range of extendId; closure lemmas are then free) |
| `OpenAI.isSupportedOn_iff_mem_span` | OpenAI/Bridges.lean:374 | 33 | dead | cut |
| `OpenAI.extendId_mul` | OpenAI/Bridges.lean:407 | 5 | scaffold | cut once encodings unified (state IsSupportedOn as a Subalgebra / AlgHom.range of extendId; closure lemmas are then free) |
| `OpenAI.IsSupportedOn.mul` | OpenAI/Bridges.lean:412 | 9 | scaffold | cut once encodings unified (state IsSupportedOn as a Subalgebra / AlgHom.range of extendId; closure lemmas are then free) |

### OpenAI/BufferedRectangles.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.latticeL1Distance_le_one_of_adj` | OpenAI/BufferedRectangles.lean:68 | 75 | scaffold | cut once encodings unified (ℓ¹ lattice distance vs graph/metric distance on ℤ²) |
| `OpenAI.dist_le_latticeL1Distance` | OpenAI/BufferedRectangles.lean:76 | 11 | dead | cut |
| `OpenAI.width_le_boxSize_Icc` | OpenAI/BufferedRectangles.lean:87 | 7 | dead | cut |
| `OpenAI.height_le_boxSize_Icc` | OpenAI/BufferedRectangles.lean:94 | 13 | dead | cut |

### OpenAI/CeilScaling.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `name` | OpenAI/CeilScaling.lean:8 | 30 | dead | n/a (indexer artifact: docstring word, not a declaration) |
| `Nat.ceil_le_add_one_mul_of_le_mul` | OpenAI/CeilScaling.lean:31 | 10 | standard | library tree (Algebra/Order/Floor/Semifield; cf. Nat.ceil_le_mul) |

### OpenAI/CfcComplex.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.cfcC` | OpenAI/CfcComplex.lean:26 | 28 | standard | replace-by cfc (ℂ→ℂ functional calculus of Mathlib; Hermitian ⇒ IsStarNormal) |
| `Matrix.cfcC_eq_spectralFun` | OpenAI/CfcComplex.lean:29 | 4 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with the corresponding star-algebra map |
| `Matrix.cfcC_mul` | OpenAI/CfcComplex.lean:33 | 6 | standard | replace-by cfc_mul / cfc_add / cfc_const / cfc_id (Mathlib, ℂ-valued cfc; only cfc_mul checked) |
| `Matrix.conjTranspose_cfcC` | OpenAI/CfcComplex.lean:39 | 5 | standard | replace-by cfc_star (Mathlib) |
| `Matrix.cfcC_transpose` | OpenAI/CfcComplex.lean:44 | 4 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with the corresponding star-algebra map |
| `Matrix.cfcC_kronecker_one` | OpenAI/CfcComplex.lean:48 | 5 | dead | cut |
| `Matrix.cfcC_one_kronecker` | OpenAI/CfcComplex.lean:53 | 5 | dead | cut |
| `Matrix.cfcC_submatrix_equiv` | OpenAI/CfcComplex.lean:58 | 6 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with the corresponding star-algebra map |
| `Matrix.cfcC_mul_intertwine` | OpenAI/CfcComplex.lean:64 | 7 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with the corresponding star-algebra map |
| `Matrix.supportCPow_eq_cfcC` | OpenAI/CfcComplex.lean:71 | 5 | scaffold | cut once encodings unified (supportCPow vs cfcC) |
| `Matrix.cfcC_add` | OpenAI/CfcComplex.lean:76 | 6 | standard | replace-by cfc_mul / cfc_add / cfc_const / cfc_id (Mathlib, ℂ-valued cfc; only cfc_mul checked) |
| `Matrix.cfcC_one` | OpenAI/CfcComplex.lean:82 | 5 | standard | replace-by cfc_mul / cfc_add / cfc_const / cfc_id (Mathlib, ℂ-valued cfc; only cfc_mul checked) |
| `Matrix.cfcC_id` | OpenAI/CfcComplex.lean:87 | 5 | standard | replace-by cfc_mul / cfc_add / cfc_const / cfc_id (Mathlib, ℂ-valued cfc; only cfc_mul checked) |
| `Matrix.cfcC_congr_of_nonneg` | OpenAI/CfcComplex.lean:92 | 10 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with the corresponding star-algebra map |

### OpenAI/CfcConjugation.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.reindexStarAlgHom` | OpenAI/CfcConjugation.lean:29 | 43 | standard | library tree (LinearAlgebra/Matrix/Reindex; star version of Matrix.reindexAlgEquiv) |
| `Matrix.reindexStarAlgHom_apply` | OpenAI/CfcConjugation.lean:44 | 4 | standard | library tree (LinearAlgebra/Matrix/Reindex; star version of Matrix.reindexAlgEquiv) |
| `Matrix.cfc_submatrix_equiv` | OpenAI/CfcConjugation.lean:48 | 20 | standard | replace-by Matrix.cfc_reindex (Physlib QuantumInfo.ForMathlib.Isometry; 𝕜-generic) |
| `Matrix.rpow_conj_unitary` | OpenAI/CfcConjugation.lean:68 | 14 | standard | replace-by Matrix.cfc_conj_unitary (Physlib QuantumInfo.ForMathlib.Isometry) with CFC.rpow = cfc |

### OpenAI/CfcKronecker.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| 4 decls: `leftKroneckerEmbed`, `leftKroneckerEmbed_apply`, `rightKroneckerEmbed`, `rightKroneckerEmbed_apply` | OpenAI/CfcKronecker.lean:30-65 | 68 | standard | library tree (LinearAlgebra/Matrix/Kronecker; star-alg hom A ↦ A ⊗ 1, from Matrix.kroneckerStarAlgEquiv) |
| `Matrix.cfc_kronecker_one` | OpenAI/CfcKronecker.lean:69 | 15 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with leftKroneckerEmbed |
| `Matrix.cfc_one_kronecker` | OpenAI/CfcKronecker.lean:84 | 18 | dead | cut [name also occurs in O/CfcComplex, O/MatrixSqrt: user is itself unreachable or a name collision; confirm] |

### OpenAI/CfcTranspose.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 4 decls) | OpenAI/CfcTranspose.lean:22-47 | 63 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; cfc commutes with transpose) |

### OpenAI/ConditionalTwoFamilies.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `FiniteProduct.disjoint_exterior_past` | OpenAI/ConditionalTwoFamilies.lean:55 | 70 | dead | cut |
| `FiniteProduct.conditionalMutualInformation_union_left` | OpenAI/ConditionalTwoFamilies.lean:71 | 10 | dead | cut |
| `FiniteProduct.mutualInformation_le_two_entropy` | OpenAI/ConditionalTwoFamilies.lean:81 | 19 | scaffold | cut once encodings unified (FiniteProduct entropy encoding) |
| `FiniteProduct.conditionalMutualInformation_le_two_entropy` | OpenAI/ConditionalTwoFamilies.lean:100 | 10 | scaffold | cut once encodings unified (FiniteProduct entropy encoding) |
| 4 decls: `conditionalMutualInformation_biUnion_le_sum`, `target_union_complement_eq_exterior`, `conditionalMutualInformation_le_two_family_mutualInformation`, `conditionalMutualInformation_le_two_family_sum` | OpenAI/ConditionalTwoFamilies.lean:110-230 | 145 | dead | cut |

### OpenAI/EntropyContinuity.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.vonNeumann_eq_re_trace_cfc` | OpenAI/EntropyContinuity.lean:32 | 40 | standard | replace-by Sᵥₙ_eq_trace_cfc_negMulLog (Physlib QuantumInfo.Entropy.VonNeumann; MState encoding) |
| `Matrix.continuousOn_vonNeumann` | OpenAI/EntropyContinuity.lean:41 | 14 | standard | replace-by Sᵥₙ_continuous (Physlib QuantumInfo.Entropy.VonNeumann; MState encoding) |

### OpenAI/FinSum.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.submatrix_sum` | OpenAI/FinSum.lean:29 | 41 | standard | library tree (Algebra/BigOperators/Basic; Matrix.submatrix of a finite sum) |
| 6 decls: `sum_mul_mul_eq_mul_sum_mul`, `sum_finSigmaFinEquiv`, `sum_piFin_castLE_extend_zero`, `sum_fiber_smul`, `sum_castLE_extend_zero`, `coefficient_eq_zero_of_sum_eq_of_complement_smul` | OpenAI/FinSum.lean:42-168 | 193 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/FiniteProductChannel.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `FiniteProduct.Configuration` | OpenAI/FiniteProductChannel.lean:35 | 38 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |
| `FiniteProduct.complementEquiv` | OpenAI/FiniteProductChannel.lean:39 | 8 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |
| `FiniteProduct.splitEquiv` | OpenAI/FiniteProductChannel.lean:47 | 5 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |
| `FiniteProduct.splitEquiv_apply_fst` | OpenAI/FiniteProductChannel.lean:52 | 4 | dead | cut (@[simp]/instance: may fire implicitly; check by deleting) |
| `FiniteProduct.splitEquiv_apply_snd` | OpenAI/FiniteProductChannel.lean:56 | 4 | dead | cut (@[simp]/instance: may fire implicitly; check by deleting) |
| 18 decls: `splitEquiv_symm_apply_of_mem`, `splitEquiv_symm_apply_of_notMem`, `unionEquiv`, `complementUnionEquiv`, `configurationCongr`, `configurationCongr_apply`, `split_union_symm`, `reducedMatrix`, `reducedMatrix_apply`, `reducedMatrix_posSemidef`, `trace_reducedMatrix`, `traceRight_reducedMatrix_union`, `unionEquiv_symm_swap`, `reducedMatrix_congr_region`, `traceLeft_reducedMatrix_union`, `reducedPure`, `reducedPure_posSemidef`, `trace_reducedPure` | OpenAI/FiniteProductChannel.lean:60-229 | 176 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |

### OpenAI/FiniteProductConditional.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `FiniteProduct.conditionalMutualInformation` | OpenAI/FiniteProductConditional.lean:30 | 36 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |
| `FiniteProduct.conditionalMutualInformation_eq_sub` | OpenAI/FiniteProductConditional.lean:37 | 10 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |
| `FiniteProduct.conditionalMutualInformation_le_mutualInformation_union` | OpenAI/FiniteProductConditional.lean:47 | 9 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |
| `FiniteProduct.sum_conditionalMutualInformation_past` | OpenAI/FiniteProductConditional.lean:56 | 23 | dead | cut [name also occurs in O/ConditionalTwoFamilies: user is itself unreachable or a name collision; confirm] |
| `FiniteProduct.conditionalMutualInformation_pure_duality` | OpenAI/FiniteProductConditional.lean:79 | 44 | dead | cut [name also occurs in O/ConditionalTwoFamilies: user is itself unreachable or a name collision; confirm] |

### OpenAI/FiniteProductEntropy.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Arealaw.vonNeumann_traceLeft_vecMulVec_eq_traceRight` | OpenAI/FiniteProductEntropy.lean:38 | 62 | standard | replace-by Sᵥₙ_of_partial_eq (Physlib QuantumInfo.Entropy.VonNeumann; MState/Ket encoding) |
| 6 decls: `entropy`, `reducedPure_eq_traceRight`, `split_compl_symm`, `reducedPure_compl_eq_traceLeft`, `entropy_compl`, `entropy_empty` | OpenAI/FiniteProductEntropy.lean:63-119 | 63 | scaffold | cut once encodings unified (FiniteProduct entropy vs SubState.regionEntropy / Reg encoding) |
| `FiniteProduct.entropy_univ` | OpenAI/FiniteProductEntropy.lean:126 | 5 | dead | cut (@[simp]/instance: may fire implicitly; check by deleting) |
| `FiniteProduct.entropy_union_le` | OpenAI/FiniteProductEntropy.lean:131 | 27 | scaffold | cut once encodings unified (FiniteProduct entropy vs SubState.regionEntropy / Reg encoding) |
| `FiniteProduct.mutualInformation` | OpenAI/FiniteProductEntropy.lean:158 | 5 | scaffold | cut once encodings unified (FiniteProduct entropy vs SubState.regionEntropy / Reg encoding) |
| `FiniteProduct.mutualInformation_nonneg` | OpenAI/FiniteProductEntropy.lean:163 | 6 | scaffold | cut once encodings unified (FiniteProduct entropy vs SubState.regionEntropy / Reg encoding) |

### OpenAI/FiniteProductEntropyBounds.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 5 decls) | OpenAI/FiniteProductEntropyBounds.lean:22-68 | 75 | scaffold | cut once encodings unified (FiniteProduct encoding of regions/partial traces/entropy vs Reg/pureState/SubState.regionEntropy/mutualInfo) |

### OpenAI/FiniteProductInformation.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 5 decls) | OpenAI/FiniteProductInformation.lean:42-159 | 173 | scaffold | cut once encodings unified (FiniteProduct SSA/submodularity; content is Physlib QuantumInfo.Entropy.SSA) |

### OpenAI/GaussianFilterReindex.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.reindex_exp` | OpenAI/GaussianFilterReindex.lean:29 | 35 | standard | replace-by NormedSpace.map_exp (Mathlib; name from memory, not searched) with Matrix.reindexAlgEquiv |

### OpenAI/Geometry/CellFanRadialIncidence.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/Geometry/CellFanRadialIncidence.lean:39-78 | 103 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/CellFanRays.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 7 decls) | OpenAI/Geometry/CellFanRays.lean:44-128 | 135 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/FanAffineCoordinates.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/Geometry/FanAffineCoordinates.lean:40-64 | 73 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/FanInactiveSeams.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 5 decls) | OpenAI/Geometry/FanInactiveSeams.lean:49-162 | 172 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/FanRadialConvexity.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 9 decls) | OpenAI/Geometry/FanRadialConvexity.lean:46-211 | 221 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/FanRadialPieces.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/Geometry/FanRadialPieces.lean:43-84 | 98 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/FanRunComponents.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 3 decls) | OpenAI/Geometry/FanRunComponents.lean:48-201 | 224 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/FanRunConnectedness.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 3 decls) | OpenAI/Geometry/FanRunConnectedness.lean:44-120 | 152 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/FanRunDisjointness.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.Geometry.cellFanRunRegion_sdiff_radials_pairwise_disjoint` | OpenAI/Geometry/FanRunDisjointness.lean:39 | 111 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/InitialActiveRayCount.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/Geometry/InitialActiveRayCount.lean:44-79 | 105 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/InitialActiveRays.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 5 decls) | OpenAI/Geometry/InitialActiveRays.lean:52-317 | 359 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/InitialComponentRegions.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.Geometry.exists_unique_initialRegion_of_closedHalf_component` | OpenAI/Geometry/InitialComponentRegions.lean:41 | 95 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/InitialSectorComponents.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 3 decls) | OpenAI/Geometry/InitialSectorComponents.lean:55-221 | 294 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/InitialSectorCycle.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/Geometry/InitialSectorCycle.lean:43-68 | 94 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/InitialSectorRuns.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 3 decls) | OpenAI/Geometry/InitialSectorRuns.lean:46-149 | 257 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/MeshSegmentClearance.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.Geometry.affineMesh_segment_dist_ge_of_not_mem` | OpenAI/Geometry/MeshSegmentClearance.lean:44 | 76 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/Geometry/SegmentBallClipping.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.Geometry.segment_inter_closedBall_of_dist_eq_one` | OpenAI/Geometry/SegmentBallClipping.lean:34 | 51 | foreign | cut (TNLean PEPS geometry port; no anchor in digest, nothing in the closure references it) |

### OpenAI/HermitianCfcSpectral.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.IsHermitian.spectral_form` | OpenAI/HermitianCfcSpectral.lean:19 | 27 | standard | replace-by Matrix.IsHermitian.spectral_theorem (Mathlib; ℂ) |
| `Matrix.IsHermitian.cfc_form` | OpenAI/HermitianCfcSpectral.lean:28 | 8 | standard | replace-by Matrix.IsHermitian.cfc_eq (Mathlib) + spectral_theorem |
| `Matrix.IsHermitian.cfc_mul` | OpenAI/HermitianCfcSpectral.lean:36 | 10 | standard | replace-by cfc_mul (Mathlib) |
| `Matrix.IsHermitian.cfc_id` | OpenAI/HermitianCfcSpectral.lean:46 | 7 | standard | replace-by cfc_id' (Mathlib; name from memory) |
| `Matrix.IsHermitian.self_mul_cfc` | OpenAI/HermitianCfcSpectral.lean:53 | 6 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus) |
| `Matrix.IsHermitian.trace_cfc_eq_sum` | OpenAI/HermitianCfcSpectral.lean:59 | 8 | standard | replace-by HermitianMat.trace_cfc_eq (Physlib) / Matrix.IsHermitian.trace_eq_sum_eigenvalues |
| `Matrix.IsHermitian.trace_cfc_eq_sum_re` | OpenAI/HermitianCfcSpectral.lean:67 | 7 | standard | replace-by HermitianMat.trace_cfc_eq (Physlib) / Matrix.IsHermitian.trace_eq_sum_eigenvalues |

### OpenAI/HermitianHelpers.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/HermitianHelpers.lean:30-46 | 91 | standard | library tree (Analysis/Matrix/Order) |

### OpenAI/HermitianUnitaryPath.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.hermitianUnitaryPath` | OpenAI/HermitianUnitaryPath.lean:34 | 36 | standard | library tree (Analysis/Normed/Algebra/MatrixExponential; one-parameter unitary group exp(itH)) |
| `Matrix.hermitianUnitaryPath_zero` | OpenAI/HermitianUnitaryPath.lean:37 | 4 | standard | library tree (Analysis/Normed/Algebra/MatrixExponential; one-parameter unitary group exp(itH)) |
| `Matrix.continuous_hermitianUnitaryPath` | OpenAI/HermitianUnitaryPath.lean:41 | 6 | standard | library tree (Analysis/Normed/Algebra/MatrixExponential; one-parameter unitary group exp(itH)) |
| `Matrix.hermitianUnitaryPath_add` | OpenAI/HermitianUnitaryPath.lean:47 | 8 | standard | replace-by Matrix.exp_add_of_commute (Mathlib) |
| `Matrix.hermitianUnitaryPath_mul_conjTranspose` | OpenAI/HermitianUnitaryPath.lean:55 | 12 | standard | library tree (Analysis/Normed/Algebra/MatrixExponential; one-parameter unitary group exp(itH)) |
| `Matrix.hermitianUnitaryRepresentation` | OpenAI/HermitianUnitaryPath.lean:67 | 12 | dead | cut |
| `Matrix.eventually_ne_zero_of_hasDerivAt` | OpenAI/HermitianUnitaryPath.lean:79 | 13 | dead | cut |
| `Matrix.eventually_hermitianUnitaryPath_nonscalar` | OpenAI/HermitianUnitaryPath.lean:92 | 31 | dead | cut |

### OpenAI/IsometricCompression.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 5 decls) | OpenAI/IsometricCompression.lean:41-102 | 110 | dead | cut (QICLean port, unused; Mathlib candidate: isometry conjugation as nonunital star-hom) |

### OpenAI/KleinInequality.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 4 decls) | OpenAI/KleinInequality.lean:36-96 | 107 | standard | library tree (Analysis/Matrix; eigen-expansion tr(ρ f(σ)) = Σ pᵢ f(qⱼ) |

### OpenAI/KroneckerExponential.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.exp_kronecker_one` | OpenAI/KroneckerExponential.lean:28 | 43 | standard | replace-by NormedSpace.map_exp (Mathlib; name from memory, not searched) with the Kronecker star-alg hom |
| `Matrix.exp_one_kronecker` | OpenAI/KroneckerExponential.lean:44 | 16 | standard | replace-by NormedSpace.map_exp (Mathlib; name from memory, not searched) with the Kronecker star-alg hom |
| `Matrix.exp_kronecker_sum` | OpenAI/KroneckerExponential.lean:60 | 12 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/PairMergeDeficit: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Matrix.exp_map_conjugate` | OpenAI/KroneckerExponential.lean:72 | 7 | dead | cut |
| `Matrix.exp_rowCommutator` | OpenAI/KroneckerExponential.lean:79 | 15 | dead | cut |

### OpenAI/KroneckerFactorPositivity.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `applies` | OpenAI/KroneckerFactorPositivity.lean:66 | 76 | dead | n/a (indexer artifact: docstring word) |
| 4 decls: `eq_zero_of_forall_star_dotProduct_mulVec_eq_zero`, `exists_star_dotProduct_mulVec_ne_zero`, `posSemidef_of_forall_star_dotProduct_mulVec_nonneg`, `star_dotProduct_kronecker_mulVec_prod` | OpenAI/KroneckerFactorPositivity.lean:77-139 | 84 | standard | library tree (Analysis/Matrix/Order; star-dotProduct characterisation of PSD / zero matrix) |
| `Matrix.smul_kronecker_smul_inv_eq` | OpenAI/KroneckerFactorPositivity.lean:161 | 11 | standard | library tree (Analysis/Matrix/Order; A⊗B PSD ⇒ A,B scalar multiples of PSD) |
| `Matrix.exists_smul_posSemidef_of_kronecker_posSemidef` | OpenAI/KroneckerFactorPositivity.lean:172 | 47 | standard | library tree (Analysis/Matrix/Order; A⊗B PSD ⇒ A,B scalar multiples of PSD) |
| `Matrix.PosSemidef.eq_zero_of_neg_posSemidef` | OpenAI/KroneckerFactorPositivity.lean:219 | 14 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.exists_pos_real_smul_eq_of_smul_posSemidef` | OpenAI/KroneckerFactorPositivity.lean:233 | 76 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.finKronecker` | OpenAI/KroneckerFactorPositivity.lean:309 | 4 | standard | library tree (Analysis/Matrix/Order; A⊗B PSD ⇒ A,B scalar multiples of PSD) |
| `Matrix.finKronecker_apply` | OpenAI/KroneckerFactorPositivity.lean:313 | 7 | standard | library tree (Analysis/Matrix/Order; A⊗B PSD ⇒ A,B scalar multiples of PSD) |
| `Matrix.finKronecker_posSemidef` | OpenAI/KroneckerFactorPositivity.lean:320 | 8 | standard | library tree (Analysis/Matrix/Order; A⊗B PSD ⇒ A,B scalar multiples of PSD) |
| `Matrix.finKronecker_ne_zero` | OpenAI/KroneckerFactorPositivity.lean:328 | 19 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.finKronecker_update_smul` | OpenAI/KroneckerFactorPositivity.lean:347 | 25 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.exists_pi_smul_posSemidef_of_finKronecker_posSemidef` | OpenAI/KroneckerFactorPositivity.lean:372 | 103 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/L2OpNormReindex.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 3 decls) | OpenAI/L2OpNormReindex.lean:30-72 | 84 | standard | library tree (Analysis/CStarAlgebra/Matrix; Physlib Matrix.opNorm_reindex_proven uses Physlib’s own opNorm) |

### OpenAI/LogarithmicEnvelope.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Asymptotics.IsBigO.exists_nonneg_abs_le_mul_log_add_two` | OpenAI/LogarithmicEnvelope.lean:30 | 47 | standard | library tree (Analysis/Asymptotics/Defs; O(n) ⇒ ≤ C·log(n+2)) |

### OpenAI/MarginalSupport.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.PosSemidef.proj_mul_eq_zero_of_trace_eq_zero` | OpenAI/MarginalSupport.lean:38 | 62 | standard | library tree (LinearAlgebra/Matrix/PosDef; P·ρ=0 when tr(Pρ)=0) |

### OpenAI/MarginalSupportAbsorption.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.trace_leftKroneckerEmbed_mul` | OpenAI/MarginalSupportAbsorption.lean:54 | 78 | standard | library tree (LinearAlgebra/Matrix/Kronecker; trace of (A⊗1)ρ) |
| `Matrix.trace_rightKroneckerEmbed_mul` | OpenAI/MarginalSupportAbsorption.lean:141 | 27 | standard | library tree (LinearAlgebra/Matrix/Kronecker; trace of (A⊗1)ρ) |

### OpenAI/MatrixFramePerturbation.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one` | OpenAI/MatrixFramePerturbation.lean:52 | 59 | standard | library tree (Analysis/CStarAlgebra/Matrix; ‖V‖≤1 for V†V=1) |
| `Matrix.norm_sub_isometry_sq_le` | OpenAI/MatrixFramePerturbation.lean:60 | 23 | dead | cut |
| `Matrix.l2_opNorm_kronecker_one_mulVec_le` | OpenAI/MatrixFramePerturbation.lean:83 | 30 | dead | cut |
| `Matrix.norm_encoder_conversion_reference_le` | OpenAI/MatrixFramePerturbation.lean:113 | 20 | dead | cut |

### OpenAI/MatrixGramUnitary.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq` | OpenAI/MatrixGramUnitary.lean:44 | 130 | standard | library tree (Analysis/Matrix/Order; polar decomposition: V†V=W†W ⇒ W=UV) |
| `Matrix.exists_unitary_zero_extension_eq` | OpenAI/MatrixGramUnitary.lean:131 | 59 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.inv_sqrt_star_eq_and_mul_self_of_pos` | OpenAI/MatrixGramUnitary.lean:190 | 19 | dead | cut |
| `Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one` | OpenAI/MatrixGramUnitary.lean:209 | 20 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.normalized_conj_eq_conj_inv_of_gram_eq_smul_one` | OpenAI/MatrixGramUnitary.lean:229 | 36 | dead | cut |

### OpenAI/MatrixIntertwine.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.cfc_intertwine` | OpenAI/MatrixIntertwine.lean:32 | 89 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; cfc intertwined by V A = B V) |
| `Matrix.PosSemidef.rpow_intertwine` | OpenAI/MatrixIntertwine.lean:90 | 10 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; cfc intertwined by V A = B V) |
| `Matrix.star_dotProduct_mulVec` | OpenAI/MatrixIntertwine.lean:100 | 6 | standard | library tree (LinearAlgebra/Matrix/DotProduct; duplicate of MatrixProjectionAux.star_dotProduct_mulVec) |
| `Matrix.re_star_dotProduct_self_eq_norm_sq` | OpenAI/MatrixIntertwine.lean:106 | 6 | standard | replace-by EuclideanSpace.norm_sq_eq / inner_self_eq_norm_sq (Mathlib; names from memory) on `toLp` |
| `Matrix.mul_exp_eq_exp_mul_of_mul_eq` | OpenAI/MatrixIntertwine.lean:112 | 41 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/MatrixIsometryKronecker.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.Isometry.kronecker` | OpenAI/MatrixIsometryKronecker.lean:25 | 37 | standard | library tree (LinearAlgebra/UnitaryGroup; Isometry (A ⊗ B)) |

### OpenAI/MatrixKroneckerContraction.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.kronecker_kronecker_eq_submatrix` | OpenAI/MatrixKroneckerContraction.lean:41 | 58 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.l2_opNorm_one_kronecker_rect_le` | OpenAI/MatrixKroneckerContraction.lean:59 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.l2_opNorm_kronecker_le` | OpenAI/MatrixKroneckerContraction.lean:70 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in A/OpNorm: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Matrix.l2_opNorm_kronecker_le_one` | OpenAI/MatrixKroneckerContraction.lean:81 | 6 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in A/OpNorm: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Matrix.l2_opNorm_toMatrix_toPEquiv_le` | OpenAI/MatrixKroneckerContraction.lean:87 | 10 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.norm_submatrix_equiv_le` | OpenAI/MatrixKroneckerContraction.lean:97 | 10 | standard | library tree (Analysis/CStarAlgebra/Matrix; opNorm of submatrix/Kronecker) |
| `Matrix.toMatrix_toPEquiv_prodCongr` | OpenAI/MatrixKroneckerContraction.lean:107 | 10 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.toMatrix_toPEquiv_submatrix` | OpenAI/MatrixKroneckerContraction.lean:117 | 9 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.submatrix_symm_submatrix` | OpenAI/MatrixKroneckerContraction.lean:126 | 9 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Commute.submatrix_equiv` | OpenAI/MatrixKroneckerContraction.lean:135 | 10 | dead | cut |
| `EuclideanSpace.norm_toLp_comp_equiv` | OpenAI/MatrixKroneckerContraction.lean:145 | 7 | scaffold | cut once encodings unified (Euclidean-space Kronecker vector vs matrix encoding) |
| `EuclideanSpace.vecKron` | OpenAI/MatrixKroneckerContraction.lean:152 | 4 | scaffold | cut once encodings unified (Euclidean-space Kronecker vector vs matrix encoding) |
| `EuclideanSpace.vecKron_sub_left` | OpenAI/MatrixKroneckerContraction.lean:156 | 5 | dead | cut |
| `EuclideanSpace.vecKron_sub_right` | OpenAI/MatrixKroneckerContraction.lean:161 | 8 | dead | cut |
| `EuclideanSpace.norm_vecKron` | OpenAI/MatrixKroneckerContraction.lean:169 | 8 | scaffold | cut once encodings unified (Euclidean-space Kronecker vector vs matrix encoding) |
| `EuclideanSpace.norm_vecKron_self_sub_le` | OpenAI/MatrixKroneckerContraction.lean:177 | 11 | dead | cut |

### OpenAI/MatrixL2Contraction.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.l2_opNorm_reindex_le` | OpenAI/MatrixL2Contraction.lean:47 | 69 | standard | library tree (Analysis/CStarAlgebra/Matrix) |
| 6 decls: `l2_opNorm_le_one_of_conjTranspose_mul_self_le_one`, `l2_opNorm_le_one`, `l2_opNorm_mul_le_one`, `l2_opNorm_conjTranspose_mul_mul_le_one`, `l2_opNorm_list_prod_le_one`, `l2_opNorm_le_of_blocks` | OpenAI/MatrixL2Contraction.lean:70-102 | 81 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.kronecker_one_mul_apply` | OpenAI/MatrixL2Contraction.lean:151 | 5 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/SpectatorSiteExpectation: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |

### OpenAI/MatrixPowers.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.PosDef.rpow` | OpenAI/MatrixPowers.lean:31 | 34 | standard | replace-by IsStrictlyPositive.rpow (Mathlib) via Matrix.isStrictlyPositive_iff_posDef |
| `Matrix.PosDef.rpow_isHermitian` | OpenAI/MatrixPowers.lean:35 | 4 | standard | replace-by CFC.rpow_* API (Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic; Matrix.PosDef restatements) |
| `Matrix.PosDef.star_rpow` | OpenAI/MatrixPowers.lean:39 | 4 | standard | replace-by CFC.rpow_* API (Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic; Matrix.PosDef restatements) |
| `Matrix.PosDef.rpow_mul_rpow` | OpenAI/MatrixPowers.lean:43 | 4 | standard | replace-by CFC.rpow_add (Mathlib) |
| `Matrix.PosDef.rpow_zero` | OpenAI/MatrixPowers.lean:47 | 4 | standard | replace-by CFC.rpow_zero (Mathlib) |
| `Matrix.PosDef.rpow_one` | OpenAI/MatrixPowers.lean:51 | 4 | standard | replace-by CFC.rpow_one (Mathlib) |
| 9 decls: `rpow_mul_rpow_neg`, `rpow_neg_mul_rpow`, `rpow_half_mul_rpow_half`, `rpow_rpow`, `smul_rpow`, `commute_rpow`, `commute_rpow_left`, `mul_of_commute`, `mul_rpow_of_commute` | OpenAI/MatrixPowers.lean:55-107 | 67 | standard | replace-by CFC.rpow_* API (Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic; Matrix.PosDef restatements) |

### OpenAI/MatrixProjectionAux.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.star_dotProduct_mulVec` | OpenAI/MatrixProjectionAux.lean:23 | 31 | standard | library tree (LinearAlgebra/Matrix/DotProduct, Matrix.Isometry sums) |
| `Matrix.sum_star_mul_eq_ite_of_conjTranspose_mul_eq_one` | OpenAI/MatrixProjectionAux.lean:32 | 6 | standard | library tree (LinearAlgebra/Matrix/DotProduct, Matrix.Isometry sums) |
| 4 decls: `sum_mul_star_eq_ite_of_conjTranspose_mul_eq_one`, `sum_mul_star_eq_ite_of_mul_conjTranspose_eq_one`, `sum_star_mul_eq_ite_of_mul_conjTranspose_eq_one`, `eq_zero_of_sum_mul_conjTranspose_eq_zero` | OpenAI/MatrixProjectionAux.lean:38-68 | 51 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.eq_zero_of_sum_conjTranspose_mul_self_eq_zero` | OpenAI/MatrixProjectionAux.lean:89 | 14 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/OrthogonalProjection: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |

### OpenAI/MatrixReindexGap.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.toEuclideanLin_reindex_piLpCongrLeft` | OpenAI/MatrixReindexGap.lean:27 | 37 | scaffold | cut once encodings unified (spectral gap under reindexing of the Euclidean encoding) |
| `Matrix.ker_toEuclideanLin_reindex_map` | OpenAI/MatrixReindexGap.lean:38 | 21 | dead | cut |
| `Matrix.norm_gap_toEuclideanLin_reindex` | OpenAI/MatrixReindexGap.lean:59 | 18 | dead | cut |

### OpenAI/MatrixReindexUnitary.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.reindex_mem_unitaryGroup` | OpenAI/MatrixReindexUnitary.lean:27 | 34 | dead | cut (QICLean port, unused; subsumed by Physlib Matrix.reindex_one_mem_unitaryGroup) |

### OpenAI/MatrixScalarFloor.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/MatrixScalarFloor.lean:26-34 | 49 | standard | library tree (Analysis/Matrix/Order; A ≤ B ⇒ scalar floor ⇒ B^r ≤ c·1) |

### OpenAI/MatrixSqrt.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.IsHermitian.star_mulVec_dotProduct` | OpenAI/MatrixSqrt.lean:66 | 74 | standard | library tree (Analysis/Matrix/Order; CFC.sqrt of Kronecker / PSD) |
| `Matrix.cfc_kronecker_of_mul_posSemidef` | OpenAI/MatrixSqrt.lean:75 | 64 | standard | library tree (Analysis/Matrix/Order; CFC.sqrt of Kronecker / PSD) |
| `Matrix.PosSemidef.sqrt_smul` | OpenAI/MatrixSqrt.lean:139 | 20 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.sqrt_kronecker` | OpenAI/MatrixSqrt.lean:159 | 12 | standard | library tree (Analysis/Matrix/Order; CFC.sqrt of Kronecker / PSD) |
| `Matrix.conjTranspose_cfc_sqrt` | OpenAI/MatrixSqrt.lean:171 | 7 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosDef.isUnit_det_cfc_sqrt` | OpenAI/MatrixSqrt.lean:178 | 10 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.cfc_sqrt_isHermitian` | OpenAI/MatrixSqrt.lean:188 | 15 | standard | library tree (Analysis/Matrix/Order; CFC.sqrt of Kronecker / PSD) |
| `Matrix.PosSemidef.cfc_sqrt_mul_supportProj` | OpenAI/MatrixSqrt.lean:203 | 27 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportProj_mul_cfc_sqrt` | OpenAI/MatrixSqrt.lean:230 | 9 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportProj_cfc_sqrt` | OpenAI/MatrixSqrt.lean:239 | 27 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.cfc_sqrt_mul_self` | OpenAI/MatrixSqrt.lean:266 | 17 | standard | library tree (Analysis/Matrix/Order; CFC.sqrt of Kronecker / PSD) |
| `Matrix.PosSemidef.cfc_log_sqrt` | OpenAI/MatrixSqrt.lean:283 | 19 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosDef.rpow_neg_quarter_eq_inv_sqrt_sqrt` | OpenAI/MatrixSqrt.lean:302 | 17 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportInvSqrt` | OpenAI/MatrixSqrt.lean:319 | 10 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInvFourthRoot` | OpenAI/MatrixSqrt.lean:329 | 6 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportInvSqrt_mul_supportProj` | OpenAI/MatrixSqrt.lean:335 | 27 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInvSqrt_submatrix_equiv` | OpenAI/MatrixSqrt.lean:362 | 16 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportInv` | OpenAI/MatrixSqrt.lean:378 | 5 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInvSqrt_isHermitian` | OpenAI/MatrixSqrt.lean:383 | 8 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportProj_mul_supportInvSqrt` | OpenAI/MatrixSqrt.lean:391 | 11 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInvSqrt_posSemidef` | OpenAI/MatrixSqrt.lean:402 | 18 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosDef.supportInvSqrt_eq_inv_sqrt` | OpenAI/MatrixSqrt.lean:420 | 25 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInvSqrt_smul` | OpenAI/MatrixSqrt.lean:445 | 30 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportInvSqrt_kronecker` | OpenAI/MatrixSqrt.lean:475 | 22 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInvSqrt_kronecker_one` | OpenAI/MatrixSqrt.lean:497 | 15 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportInvSqrt_one_kronecker` | OpenAI/MatrixSqrt.lean:512 | 13 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.cfc_sqrt_mul_supportInvSqrt` | OpenAI/MatrixSqrt.lean:525 | 26 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInvSqrt_mul_cfc_sqrt` | OpenAI/MatrixSqrt.lean:551 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| 4 decls: `supportInvSqrt_mul_self_mul_supportInvSqrt`, `supportProj_kronecker`, `supportProj_eq_one`, `supportInvSqrt_sq_mul_self` | OpenAI/MatrixSqrt.lean:562-636 | 110 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.self_mul_supportInvSqrt_sq` | OpenAI/MatrixSqrt.lean:672 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportInv_mul_self` | OpenAI/MatrixSqrt.lean:683 | 7 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.self_mul_supportInv` | OpenAI/MatrixSqrt.lean:690 | 6 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportInv_isHermitian` | OpenAI/MatrixSqrt.lean:696 | 6 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportInv_posSemidef` | OpenAI/MatrixSqrt.lean:702 | 9 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportProj_mul_supportInv` | OpenAI/MatrixSqrt.lean:711 | 5 | standard | library tree (LinearAlgebra/Matrix/PosDef; support-inverse API; cf. Physlib HermitianMat.supportProj) |
| 15 decls: `supportInv_mul_supportProj`, `supportInvExtension`, `supportInvExtensionInverse`, `supportInvExtension_mul_self`, `self_mul_supportInvExtension`, `supportInvExtension_mul_inverse`, `supportInvExtension_inverse_mul`, `supportInvExtensionUnit`, `isUnit_supportInvExtension`, `isUnit_det_supportInvExtension`, `star_dotProduct_supportInv_mulVec_eq_of_mulVec_eq`, `supportProj_posSemidef`, `one_sub_supportProj_posSemidef`, `sub_smul_posSemidef_iff`, `blockDiagonal'` | OpenAI/MatrixSqrt.lean:716-959 | 265 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/MatrixSqrtKernel.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 2 decls) | OpenAI/MatrixSqrtKernel.lean:19-61 | 70 | standard | library tree (Analysis/Matrix/Order; ker √k = ker k) |

### OpenAI/MatrixTracePairing.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| 6 decls: `linearMap_trace_eq_sum_apply_single`, `entry_mul_single_mul`, `vec_one_dotProduct_vec_eq_trace`, `span_range_mul_nonzero_mul_eq_top`, `submodule_sup_ne_top_of_mul_eq_zero`, `traceBilinForm` | OpenAI/MatrixTracePairing.lean:70-192 | 199 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.traceBilinForm_apply` | OpenAI/MatrixTracePairing.lean:200 | 6 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (@[simp]/instance: may fire implicitly; check by deleting) (Mathlib candidate, unused) |
| 4 decls: `trace_mul_right_eq_zero_iff`, `traceBilinForm_nondegenerate`, `exists_identity_traceless_basis`, `tracelessPart` | OpenAI/MatrixTracePairing.lean:206-260 | 58 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.trace_tracelessPart` | OpenAI/MatrixTracePairing.lean:264 | 17 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (@[simp]/instance: may fire implicitly; check by deleting) (Mathlib candidate, unused) |
| `Matrix.traceAdjointMap` | OpenAI/MatrixTracePairing.lean:281 | 20 | standard | library tree (cf. Physlib QuantumInfo/Channels/Dual `MatrixMap.dual`; trace-pairing adjoint map) |
| `Matrix.trace_traceAdjointMap_mul` | OpenAI/MatrixTracePairing.lean:301 | 18 | standard | library tree (cf. Physlib QuantumInfo/Channels/Dual `MatrixMap.dual`; trace-pairing adjoint map) |
| 8 decls: `traceAdjointMap_apply_apply`, `traceAdjointMap_add`, `traceAdjointMap_sub`, `traceAdjointMap_toMatrix_transpose`, `traceAdjointMap_charpoly`, `traceAdjointMap_hasEigenvalue_iff`, `traceAdjointMap_traceAdjointMap`, `traceAdjointMap_comp` | OpenAI/MatrixTracePairing.lean:319-427 | 125 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/MatrixUnitaryBetween.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.IsCoisometry` | OpenAI/MatrixUnitaryBetween.lean:76 | 80 | standard | library tree (LinearAlgebra/UnitaryGroup; Coisometry/UnitaryBetween API, Physlib has only Matrix.Isometry) |
| `Matrix.IsUnitaryBetween` | OpenAI/MatrixUnitaryBetween.lean:81 | 4 | standard | library tree (LinearAlgebra/UnitaryGroup; Coisometry/UnitaryBetween API, Physlib has only Matrix.Isometry) |
| `Matrix.isCoisometry_iff_isometry_conjTranspose` | OpenAI/MatrixUnitaryBetween.lean:85 | 4 | standard | library tree (LinearAlgebra/UnitaryGroup; extends Physlib Matrix.Isometry) |
| `Matrix.isUnitaryBetween_iff_isometry` | OpenAI/MatrixUnitaryBetween.lean:89 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.conjTranspose_mul_mul_eq_conjTranspose_mul_iff_of_mul_eq_one` | OpenAI/MatrixUnitaryBetween.lean:100 | 28 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| 4 decls: `rank_eq_card`, `card_le`, `conjTranspose`, `reindex` | OpenAI/MatrixUnitaryBetween.lean:128-157 | 39 | standard | library tree (LinearAlgebra/UnitaryGroup; extends Physlib Matrix.Isometry) |
| `Matrix.Isometry.mul` | OpenAI/MatrixUnitaryBetween.lean:167 | 14 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.Isometry.isUnitaryBetween_of_card_eq` | OpenAI/MatrixUnitaryBetween.lean:181 | 38 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| 4 decls: `rank_eq_card`, `card_le`, `conjTranspose`, `reindex` | OpenAI/MatrixUnitaryBetween.lean:219-248 | 39 | standard | library tree (LinearAlgebra/UnitaryGroup; Coisometry/UnitaryBetween API, Physlib has only Matrix.Isometry) |
| `Matrix.IsCoisometry.mul` | OpenAI/MatrixUnitaryBetween.lean:258 | 14 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.IsCoisometry.isUnitaryBetween_of_card_eq` | OpenAI/MatrixUnitaryBetween.lean:272 | 14 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.IsUnitaryBetween.conjTranspose` | OpenAI/MatrixUnitaryBetween.lean:286 | 5 | standard | library tree (LinearAlgebra/UnitaryGroup; Coisometry/UnitaryBetween API, Physlib has only Matrix.Isometry) |
| `Matrix.IsUnitaryBetween.reindex` | OpenAI/MatrixUnitaryBetween.lean:291 | 7 | standard | library tree (LinearAlgebra/UnitaryGroup; Coisometry/UnitaryBetween API, Physlib has only Matrix.Isometry) |
| 4 decls: `mul`, `of_mul_left`, `of_mul_right`, `isUnitaryBetween_iff_mem_unitaryGroup` | OpenAI/MatrixUnitaryBetween.lean:298-330 | 38 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/MaximallyEntangled.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.omegaVec_apply` | OpenAI/MaximallyEntangled.lean:34 | 10 | dead | cut |

### OpenAI/NeumannInverse.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `NormedRing.inverse_tendsto_of_tendsto_of_isUnit` | OpenAI/NeumannInverse.lean:25 | 37 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| 4 decls: `norm_inverse_one_sub_le`, `perturbation_setup`, `isUnit_and_norm_inverse_le_of_norm_inverse_mul_sub_le`, `isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le` | OpenAI/NeumannInverse.lean:38-99 | 69 | standard | library tree (Analysis/Normed/Ring/Units; cf. NormedRing.inverse_one_sub, Units.ofNearby) |
| `NormedRing.norm_inverse_sub_inverse_le_of_norm_inverse_mul_sub_le` | OpenAI/NeumannInverse.lean:107 | 44 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `NormedRing.norm_inverse_sub_inverse_le_of_norm_mul_norm_sub_le` | OpenAI/NeumannInverse.lean:151 | 9 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/OperatorConvexity.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.IsHermitian.sum_dotProduct_eigenvectorBasis_eq_trace` | OpenAI/OperatorConvexity.lean:84 | 134 | standard | library tree (Analysis/Matrix; Σᵢ ⟨eᵢ, M eᵢ⟩ over an eigenvector basis = trace; the file’s own trace_rpow_concave/convex are unreachable) |
| `TNLean.rpow_eq_cfc_power` | OpenAI/OperatorConvexity.lean:135 | 5 | dead | cut |
| `TNLean.hermitian_cfc_neg` | OpenAI/OperatorConvexity.lean:140 | 12 | dead | cut |
| `TNLean.trace_cfc_convex_bound` | OpenAI/OperatorConvexity.lean:152 | 105 | dead | cut |
| `TNLean.trace_rpow_concave` | OpenAI/OperatorConvexity.lean:257 | 34 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `TNLean.trace_rpow_convex` | OpenAI/OperatorConvexity.lean:291 | 21 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/OrderedEntropyAlgebra.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Entropy.OrderedSetFunction.past` | OpenAI/OrderedEntropyAlgebra.lean:105 | 5 | scaffold | cut once encodings unified (ordered set-function entropy algebra over Finset V, FiniteProduct encoding) |
| `Entropy.OrderedSetFunction.defect` | OpenAI/OrderedEntropyAlgebra.lean:110 | 7 | scaffold | cut once encodings unified (ordered set-function entropy algebra over Finset V, FiniteProduct encoding) |
| `Entropy.OrderedSetFunction.sum_defect` | OpenAI/OrderedEntropyAlgebra.lean:117 | 47 | dead | cut |

### OpenAI/OrthogonalProjection.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `IsOrthogonalProjection` | OpenAI/OrthogonalProjection.lean:39 | 42 | standard | replace-by isStarProjection_iff' (Mathlib; IsOrthogonalProjection is a Fin D-specialised IsStarProjection) |
| `IsOrthogonalProjection.isStarProjection` | OpenAI/OrthogonalProjection.lean:43 | 6 | standard | replace-by isStarProjection_iff' (Mathlib; IsOrthogonalProjection is a Fin D-specialised IsStarProjection) |
| `IsStarProjection.isOrthogonalProjection` | OpenAI/OrthogonalProjection.lean:49 | 12 | standard | replace-by isStarProjection_iff' (Mathlib; IsOrthogonalProjection is a Fin D-specialised IsStarProjection) |
| `Matrix.isStarProjection_conjTranspose_mul_mul_of_mul_range_eq` | OpenAI/OrthogonalProjection.lean:61 | 20 | standard | library tree (Analysis/InnerProductSpace/Projection; matrix star projections) |
| `IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one` | OpenAI/OrthogonalProjection.lean:81 | 19 | standard | library tree (Analysis/InnerProductSpace/Projection; matrix star projections) |
| `IsOrthogonalProjection.one_sub` | OpenAI/OrthogonalProjection.lean:100 | 5 | standard | library tree (Analysis/InnerProductSpace/Projection; matrix star projections) |
| `isOrthogonalProjection_posSemidef` | OpenAI/OrthogonalProjection.lean:105 | 7 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `IsOrthogonalProjection.exists_range_isometry` | OpenAI/OrthogonalProjection.lean:112 | 99 | standard | library tree (Analysis/InnerProductSpace/Projection; matrix star projections) |
| `IsOrthogonalProjection.exists_support_isometry` | OpenAI/OrthogonalProjection.lean:211 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `isOrthogonalProjection_sum_of_pairwise_mul_eq_zero` | OpenAI/OrthogonalProjection.lean:222 | 26 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `orthogonalProjection_mul_eq_zero_of_sum_eq_one` | OpenAI/OrthogonalProjection.lean:248 | 55 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/OrthogonalResolution.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 25 decls) | OpenAI/OrthogonalResolution.lean:38-221 | 228 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; spectral resolution of identity, cf. Mathlib CompleteOrthogonalIdempotents) |

### OpenAI/OrthogonalResolutionCfc.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| 7 decls: `hom_const`, `aeval_hom`, `spectrum_hom_subset`, `cfc_hom`, `conjTranspose_hom`, `l2_opNorm_hom_le`, `weight` | OpenAI/OrthogonalResolutionCfc.lean:30-119 | 121 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; cfc over a resolution of identity) |
| `Matrix.IsOrthogonalResolution.weight_eq` | OpenAI/OrthogonalResolutionCfc.lean:122 | 4 | dead | cut |
| `Matrix.IsOrthogonalResolution.re_star_dotProduct_hom_mulVec_self` | OpenAI/OrthogonalResolutionCfc.lean:126 | 15 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; cfc over a resolution of identity) |
| `Matrix.IsOrthogonalResolution.weight_nonneg` | OpenAI/OrthogonalResolutionCfc.lean:141 | 6 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; cfc over a resolution of identity) |
| `Matrix.IsOrthogonalResolution.sum_weight` | OpenAI/OrthogonalResolutionCfc.lean:147 | 4 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; cfc over a resolution of identity) |

### OpenAI/PartialTraceDomination.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 4 decls) | OpenAI/PartialTraceDomination.lean:26-56 | 135 | standard | library tree (Analysis/Matrix/Order; ρ ≤ |

### OpenAI/PiProductTrace.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.trace_piProduct` | OpenAI/PiProductTrace.lean:28 | 35 | standard | library tree (LinearAlgebra/Matrix/Trace; trace of a Pi-product of matrices) |

### OpenAI/PosDefInverseOrder.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.PosDef.inv_le_inv_of_le` | OpenAI/PosDefInverseOrder.lean:23 | 49 | standard | replace-by HermitianMat.inv_antitone (Physlib QuantumInfo.ForMathlib.HermitianMat.LogExp; HermitianMat form) |

### OpenAI/PosSemidefSupport.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.IsHermitian.eigenvectorUnitary_indicator_isHermitian` | OpenAI/PosSemidefSupport.lean:46 | 60 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.eigenvectorUnitary_indicator_idem` | OpenAI/PosSemidefSupport.lean:61 | 22 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.eigenvectorUnitary_indicator_trace` | OpenAI/PosSemidefSupport.lean:83 | 15 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| 4 decls: `supportProj`, `supportProj_eq`, `supportProj_isHermitian`, `supportProj_idem` | OpenAI/PosSemidefSupport.lean:98-119 | 27 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.supportProj_trace` | OpenAI/PosSemidefSupport.lean:125 | 6 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.IsHermitian.supportProj_mul_self` | OpenAI/PosSemidefSupport.lean:131 | 21 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.mul_supportProj_self` | OpenAI/PosSemidefSupport.lean:152 | 7 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/MatrixSqrt: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Matrix.IsHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le` | OpenAI/PosSemidefSupport.lean:159 | 18 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/MatrixSqrt, O/SupportInverseSandwich: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Matrix.IsHermitian.one_sub_supportProj_isHermitian` | OpenAI/PosSemidefSupport.lean:177 | 6 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.one_sub_supportProj_idem` | OpenAI/PosSemidefSupport.lean:183 | 10 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.one_sub_supportProj_mul_self` | OpenAI/PosSemidefSupport.lean:193 | 8 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.eigenvalues_sq_eq_self_of_idem` | OpenAI/PosSemidefSupport.lean:201 | 30 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.IsHermitian.eigenvalues_idem_eq_zero_or_one` | OpenAI/PosSemidefSupport.lean:231 | 11 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.IsHermitian.rank_eq_trace_re_of_idem` | OpenAI/PosSemidefSupport.lean:242 | 12 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.IsHermitian.exists_supportProj_eq_mul` | OpenAI/PosSemidefSupport.lean:254 | 23 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.IsHermitian.supportProj_mulVec_eq_zero_of_mulVec_eq_zero` | OpenAI/PosSemidefSupport.lean:277 | 15 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportProj` | OpenAI/PosSemidefSupport.lean:292 | 4 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportProj_congr` | OpenAI/PosSemidefSupport.lean:296 | 9 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportProj_isHermitian` | OpenAI/PosSemidefSupport.lean:305 | 4 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportProj_idem` | OpenAI/PosSemidefSupport.lean:309 | 5 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportProj_trace` | OpenAI/PosSemidefSupport.lean:314 | 5 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.PosSemidef.supportProj_mul_self` | OpenAI/PosSemidefSupport.lean:319 | 4 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.mul_supportProj_self` | OpenAI/PosSemidefSupport.lean:323 | 4 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) [name also occurs in O/MatrixSqrt: user is itself unreachable or a name collision; confirm] (Mathlib candidate, unused) |
| `Matrix.PosSemidef.exists_supportProj_eq_mul` | OpenAI/PosSemidefSupport.lean:327 | 5 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| `Matrix.PosSemidef.supportProj_mulVec_eq_zero_of_mulVec_eq_zero` | OpenAI/PosSemidefSupport.lean:332 | 5 | standard | library tree (LinearAlgebra/Matrix/PosDef; support projection API, cf. Physlib HermitianMat.supportProj) |
| 7 decls: `supportProj_sq_eq_supportProj`, `posDef_of_supportProj_eq_one`, `supportProj_ne_zero_of_ne_zero`, `supportProj_ne_one_of_not_posDef`, `isOrthogonalProjection_supportProj`, `supportProj_mul_conjTranspose_mul_self`, `one_sub_supportProj_mul_mul_supportProj_eq_zero` | OpenAI/PosSemidefSupport.lean:337-427 | 109 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/PositiveSemidefiniteNormalization.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.kronecker_eq_trace_re_mul_normalized` | OpenAI/PositiveSemidefiniteNormalization.lean:130 | 19 | dead | cut |

### OpenAI/ProductMarginals.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Arealaw.vonNeumann_eq_neg_trace_mul_log` | OpenAI/ProductMarginals.lean:40 | 51 | standard | replace-by Sᵥₙ_eq_neg_trace_log (Physlib QuantumInfo.Entropy.VonNeumann; MState encoding) |
| `Matrix.quantumRelativeEntropy_eq_neg_entropy_sub_trace_mul_log` | OpenAI/ProductMarginals.lean:52 | 16 | standard | replace-by qRelativeEnt_eq_neg_Sᵥₙ_add (Physlib QuantumInfo.Entropy.Relative; MState encoding) |
| `Matrix.log_kronecker_posSemidef` | OpenAI/ProductMarginals.lean:68 | 92 | standard | library tree (Analysis/Matrix/Order; CFC.log of Kronecker) |

### OpenAI/PurificationSplitting.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `supplies` | OpenAI/PurificationSplitting.lean:33 | 72 | dead | n/a (indexer artifact: docstring word) |
| `Real.sqrt_two_mul_one_sub_exp_neg_half_le_sqrt` | OpenAI/PurificationSplitting.lean:73 | 16 | standard | library tree (Analysis/SpecialFunctions/Exponential; elementary real inequality) |
| `Matrix.trace_partialTraceRight_vecMulVec` | OpenAI/PurificationSplitting.lean:89 | 5 | standard | library tree (LinearAlgebra/Matrix; partial trace of vecMulVec / norm of toLp; cf. Physlib traceRight_vecMulVec) |
| `Matrix.norm_toLp_sq` | OpenAI/PurificationSplitting.lean:94 | 6 | standard | library tree (LinearAlgebra/Matrix; partial trace of vecMulVec / norm of toLp; cf. Physlib traceRight_vecMulVec) |
| `Matrix.star_mulVec_dotProduct_mulVec_of_conjTranspose_mul_eq_one` | OpenAI/PurificationSplitting.lean:100 | 17 | standard | library tree (LinearAlgebra/Matrix; partial trace of vecMulVec / norm of toLp; cf. Physlib traceRight_vecMulVec) |

### OpenAI/RectangleSimplePoles.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 15 decls) | OpenAI/RectangleSimplePoles.lean:40-207 | 256 | standard | library tree (Analysis/Complex/CauchyIntegral; rectangle boundary integral with simple poles, cf. Complex.integral_boundary_rect_eq_zero_of_differentiableOn) |

### OpenAI/RegionSplit.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 5 decls) | OpenAI/RegionSplit.lean:33-89 | 104 | scaffold | cut once encodings unified (IsRegionSplit/SiteConfig encoding vs Reg) |

### OpenAI/RootFidelityRelativeEntropy.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.quantumRelativeEntropy` | OpenAI/RootFidelityRelativeEntropy.lean:80 | 83 | standard | replace-by qRelativeEnt (Physlib QuantumInfo.Entropy.Relative; MState encoding) |
| `Matrix.quantumRelativeEntropy_eq_trace_mul_log_sub` | OpenAI/RootFidelityRelativeEntropy.lean:84 | 7 | standard | replace-by qRelativeEnt_rank (Physlib; MState encoding) |
| `Matrix.mul_exp_half_log_sub_le` | OpenAI/RootFidelityRelativeEntropy.lean:118 | 19 | standard | library tree (Analysis/SpecialFunctions/Log; elementary real inequality) |
| `Matrix.PosSemidef.sqrt_eq_cfc_real_sqrt` | OpenAI/RootFidelityRelativeEntropy.lean:137 | 11 | standard | library tree (Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow; duplicate of Arealaw.cfcSqrt_eq_cfc_real_sqrt) |

### OpenAI/Scan/Defs.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.Scan.<anon>` | OpenAI/Scan/Defs.lean:134 | 3 | dead | cut (@[simp]/instance: may fire implicitly; check by deleting) |

### OpenAI/SchmidtRank.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.schmidtCoeffMatrix` | OpenAI/SchmidtRank.lean:65 | 68 | scaffold | cut once encodings unified (bipartite vector ψ : m×n→ℂ as coefficient matrix) |
| `Matrix.schmidtCoeffMatrix_apply` | OpenAI/SchmidtRank.lean:69 | 7 | scaffold | cut once encodings unified (bipartite vector ψ : m×n→ℂ as coefficient matrix) |
| `Matrix.exists_mul_eq_of_rank_le` | OpenAI/SchmidtRank.lean:76 | 24 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.schmidtRank` | OpenAI/SchmidtRank.lean:100 | 4 | standard | library tree (LinearAlgebra/Matrix/Rank; Schmidt rank = rank of coefficient matrix, cf. Physlib MState.Ket.IsProd_iff_rank_eq_one) |
| `Matrix.HasSchmidtRankLE` | OpenAI/SchmidtRank.lean:104 | 3 | standard | library tree (LinearAlgebra/Matrix/Rank; Schmidt rank = rank of coefficient matrix, cf. Physlib MState.Ket.IsProd_iff_rank_eq_one) |
| 5 decls: `hasSchmidtRankLE_iff`, `schmidtRank_zero`, `schmidtRank_le_left`, `schmidtRank_le_right`, `schmidtRank_le_min` | OpenAI/SchmidtRank.lean:107-133 | 32 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.HasSchmidtRankLE.mono` | OpenAI/SchmidtRank.lean:139 | 5 | standard | library tree (LinearAlgebra/Matrix/Rank; Schmidt rank = rank of coefficient matrix, cf. Physlib MState.Ket.IsProd_iff_rank_eq_one) |
| `Matrix.schmidtRank_product_le_one` | OpenAI/SchmidtRank.lean:144 | 25 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.hasSchmidtRankLE_one_product` | OpenAI/SchmidtRank.lean:169 | 8 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.schmidtSingularValues` | OpenAI/SchmidtRank.lean:177 | 8 | dead | cut |
| `Matrix.schmidtRank_eq_finrank_range_toEuclideanLin` | OpenAI/SchmidtRank.lean:185 | 16 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |
| `Matrix.support_schmidtSingularValues` | OpenAI/SchmidtRank.lean:201 | 8 | dead | cut |
| `Matrix.schmidtSingularValues_eq_zero_iff` | OpenAI/SchmidtRank.lean:209 | 8 | dead | cut |
| `Matrix.schmidtSingularValues_pos_iff_lt_schmidtRank` | OpenAI/SchmidtRank.lean:217 | 9 | dead | cut |
| `Matrix.hasSchmidtRankLE_iff_schmidtSingularValues_eq_zero` | OpenAI/SchmidtRank.lean:226 | 6 | dead | cut here; upstream to library tree if kept (general fact not in Mathlib/Physlib) (Mathlib candidate, unused) |

### OpenAI/ShiftedDensityTruncation.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 3 decls) | OpenAI/ShiftedDensityTruncation.lean:37-46 | 56 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; spectral projection 1[A ≥ b]) |

### OpenAI/SiteOscillation.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.isSupportedOn_singleton_inter_iff` | OpenAI/SiteOscillation.lean:47 | 57 | dead | cut |
| `OpenAI.siteOscillation_zero` | OpenAI/SiteOscillation.lean:167 | 6 | dead | cut |
| `OpenAI.siteOscillation_one_kronecker` | OpenAI/SiteOscillation.lean:173 | 9 | dead | cut |
| 5 decls: `siteOscillation_smul_le`, `siteOscillation_smul`, `siteOscillation_neg`, `siteOscillation_sub_le`, `siteOscillation_sum_le` | OpenAI/SiteOscillation.lean:198-230 | 42 | dead | cut |

### OpenAI/SpectatorSiteExpectation.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.spectatorCondExpect_kronecker` | OpenAI/SpectatorSiteExpectation.lean:79 | 12 | dead | cut |
| `OpenAI.spectatorCondExpect_one_kronecker` | OpenAI/SpectatorSiteExpectation.lean:91 | 7 | dead | cut (@[simp]/instance: may fire implicitly; check by deleting) |
| `OpenAI.norm_spectatorCondExpect_le` | OpenAI/SpectatorSiteExpectation.lean:138 | 28 | dead | cut |

### OpenAI/SpectralFun.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.spectralFun` | OpenAI/SpectralFun.lean:30 | 32 | standard | replace-by cfc (ℂ→ℂ, Mathlib) on Hermitian A, with spectralFun = U·diag·U* a conjugated-diagonal |
| 12 decls: `spectralFun_mul`, `spectralFun_add`, `spectralFun_const`, `spectralFun_one`, `conjTranspose_spectralFun`, `spectralFun_smul`, `spectralFun_apply`, `spectralFun_eigenvectorUnitary`, `cfc_eq_spectralFun`, `spectralFun_eq_cfc_re_add_im`, `spectralFun_cfc_comp`, `cfc_affine` | OpenAI/SpectralFun.lean:33-119 | 101 | standard | replace-by cfc_mul / cfc_add / cfc_const / cfc_star (Mathlib; cfc_mul, cfc_star checked) or Matrix.IsHermitian.cfc_eq; spectralFun is a U-conjugated diagonal, so add Matrix.IsHermitian.spectral_theorem |

### OpenAI/SpectralKronecker.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| 6 decls: `kroneckerUnitary`, `conjUnitary`, `coe_kroneckerUnitary`, `spectralFun_kronecker`, `transpose_spectralFun`, `trace_spectralFun` | OpenAI/SpectralKronecker.lean:27-63 | 67 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with kroneckerUnitary/conjUnitary star-alg maps; library tree otherwise |
| `Matrix.spectralFun_congr` | OpenAI/SpectralKronecker.lean:68 | 5 | dead | cut |
| 4 decls: `linMatrix`, `linMatrix_mulVec_vec`, `ext_star_dotProduct_mulVec`, `ext_star_vec_dotProduct_mulVec_vec` | OpenAI/SpectralKronecker.lean:73-99 | 36 | scaffold | cut once encodings unified (vectorised linear map encoding) |
| `Matrix.spectralFun_leftRight_mul` | OpenAI/SpectralKronecker.lean:109 | 13 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with kroneckerUnitary/conjUnitary star-alg maps; library tree otherwise |
| `Matrix.spectralFun_leftRight_add` | OpenAI/SpectralKronecker.lean:122 | 22 | standard | replace-by StarAlgHom.map_cfc (Mathlib) with kroneckerUnitary/conjUnitary star-alg maps; library tree otherwise |

### OpenAI/SpectralQuadraticForm.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 5 decls) | OpenAI/SpectralQuadraticForm.lean:24-95 | 106 | standard | library tree (Analysis/Matrix/HermitianFunctionalCalculus; ⟨v,f(A)v⟩ = Σ f(λᵢ) |

### OpenAI/SupportPower.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.supportCPow_mul_supportCPow` | OpenAI/SupportPower.lean:34 | 10 | dead | cut |
| `Matrix.conjTranspose_supportCPow` | OpenAI/SupportPower.lean:44 | 14 | dead | cut |
| `Matrix.differentiable_mul_apply` | OpenAI/SupportPower.lean:74 | 7 | standard | library tree (Analysis/Complex; Analysis/Matrix; elementary) |
| `Matrix.norm_ofReal_cpow_of_pos` | OpenAI/SupportPower.lean:81 | 5 | standard | library tree (Analysis/Complex; Analysis/Matrix; elementary) |
| `Matrix.re_trace_conjTranspose_mul_self_eq_sum` | OpenAI/SupportPower.lean:107 | 8 | standard | library tree (Analysis/Complex; Analysis/Matrix; elementary) |
| `Matrix.sum_normSq_row_eq` | OpenAI/SupportPower.lean:115 | 6 | standard | library tree (Analysis/Complex; Analysis/Matrix; elementary) |

### OpenAI/SupportedMatrixElements.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `OpenAI.IsSupportedOn.apply_eq_zero` | OpenAI/SupportedMatrixElements.lean:41 | 52 | scaffold | cut once encodings unified (IsSupportedOn matrix-element lemma, Reg encoding) |
| `OpenAI.IsSupportedOn.mul_apply_self_of_disjoint` | OpenAI/SupportedMatrixElements.lean:53 | 10 | dead | cut |

### OpenAI/TaggedInterleavings.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `TaggedInterleavings.length_of_mem_taggedInterleavings` | OpenAI/TaggedInterleavings.lean:115 | 6 | dead | cut |

### OpenAI/TraceDistance.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.trace_partialTraceRight_mul` | OpenAI/TraceDistance.lean:34 | 39 | standard | library tree (cf. Physlib traceRight_kron; tr((X⊗1)·Y) = tr(X·tr_B Y)) |

### OpenAI/TraceMulBound.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.norm_star_dotProduct_mulVec_le` | OpenAI/TraceMulBound.lean:22 | 39 | standard | library tree (Analysis/Matrix, cf. Physlib QuantumInfo/ForMathlib/MatrixNorm/TraceNorm; |
| `Matrix.PosSemidef.norm_trace_mul_le` | OpenAI/TraceMulBound.lean:40 | 29 | standard | library tree (Analysis/Matrix, cf. Physlib QuantumInfo/ForMathlib/MatrixNorm/TraceNorm; |
| `Matrix.l2_opNorm_one_kronecker_le` | OpenAI/TraceMulBound.lean:69 | 12 | standard | library tree (Analysis/CStarAlgebra/Matrix) |

### OpenAI/TraceRightAlong.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 4 decls) | OpenAI/TraceRightAlong.lean:32-54 | 66 | scaffold | cut once encodings unified (partial trace along an equivalence β ≃ β′×γ; Reg/pureState traceRight) |

### OpenAI/TraceRightSubmatrix.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.traceRight_submatrix_prodCongr` | OpenAI/TraceRightSubmatrix.lean:23 | 32 | scaffold | cut once encodings unified (traceRight under submatrix of prodCongr) |

### OpenAI/UhlmannIsometry.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| `Matrix.exists_mem_unitaryGroup_trace_eq_fidelity` | OpenAI/UhlmannIsometry.lean:76 | 87 | standard | library tree (Physlib QuantumInfo/States/Mixed/Fidelity; Uhlmann via isometries) |
| `Matrix.exists_isometry_mul_eq_of_conjTranspose_mul_eq` | OpenAI/UhlmannIsometry.lean:88 | 24 | standard | library tree (Physlib QuantumInfo/States/Mixed/Fidelity; Uhlmann via isometries) |
| `Matrix.exists_isometry_eq_mul_conjTranspose_of_mul_conjTranspose_eq` | OpenAI/UhlmannIsometry.lean:112 | 13 | standard | library tree (Physlib QuantumInfo/States/Mixed/Fidelity; Uhlmann via isometries) |
| `Matrix.schmidtCoeffMatrix_one_kronecker_mulVec` | OpenAI/UhlmannIsometry.lean:125 | 9 | scaffold | cut once encodings unified (padded purification / coefficient-matrix encodings) |
| `Matrix.isometry_map_star` | OpenAI/UhlmannIsometry.lean:134 | 15 | scaffold | cut once encodings unified (padded purification / coefficient-matrix encodings) |
| `Matrix.exists_isometry_star_dotProduct_eq_fidelity` | OpenAI/UhlmannIsometry.lean:149 | 52 | standard | library tree (Physlib QuantumInfo/States/Mixed/Fidelity; Uhlmann via isometries) |
| `Matrix.padPurification` | OpenAI/UhlmannIsometry.lean:201 | 4 | scaffold | cut once encodings unified (padded purification / coefficient-matrix encodings) |
| `Matrix.padPurification_inl` | OpenAI/UhlmannIsometry.lean:205 | 5 | dead | cut |
| `Matrix.padPurification_inr` | OpenAI/UhlmannIsometry.lean:210 | 5 | dead | cut |
| `Matrix.partialTraceRight_vecMulVec_padPurification` | OpenAI/UhlmannIsometry.lean:215 | 15 | scaffold | cut once encodings unified (padded purification / coefficient-matrix encodings) |
| `Matrix.exists_isometry_star_dotProduct_padPurification_eq_fidelity` | OpenAI/UhlmannIsometry.lean:230 | 14 | dead | cut |

### OpenAI/WeylTwirl.lean

| Declaration | file:line | Lines | Category | Action |
|---|---|---|---|---|
| (whole file, 16 decls) | OpenAI/WeylTwirl.lean:31-183 | 211 | standard | library tree (LinearAlgebra/Matrix; Weyl clock-shift operators and their unitary-1-design twirl; used by S04 twirl anchor) |
## Appendix A: mapper notes per section

Unreviewed notes of the per-section mapping (duplicates, second encodings, 𝕜/ℂ transfers, judgement calls). Step 1 should re-check before acting on them.

### Notes, §01-02

#### Notes for the integrator (s01-02: digest 01-introduction, 02-preliminaries)

Line attribution: spans computed by `span.py`/`drv.py` (this directory) from decls.tsv; ranges of files are exact line counts including docstrings/comments. Section totals: §1 = 1524, §2 = 4290 (incl. 665 section infra); sum 5814 = every Lean line I attributed. `spec.txt` is the exact item list per row.

##### Anchors I was unsure about
- D1.4: I mapped only statement-level declarations (frozen `AreaLaw`, `area_law`, `HasGlobalGap`, gap-uniqueness lemmas). `OpenAI.exists_mutualInfo_exterior_union_le` (OpenAI/AreaLaw.lean:37, 59 lines) is the D11.26 assembly step; I left it to the D11.26 agent. Same for the 35-line body of `area_law` (counted here per instructions; the D11.26 agent may also list it).
- D1.12 / D11.1: status `none`, merge into D11.1; I did not count `two_family_cancellation`. The chain-rule lemmas (`regionEntropy_union_biUnion`, `…_biUnion_le`, RegionEntropy.lean:131,185) are in my section infra but belong to D11.1.
- D2.1 `missing`: S(D|E) and I(D:F|E) have no region-level definition; everything inlines differences. `Entropy.MarginalPhase.condMutualInfo` (OpenAI/MarginalPhaseQuadratic.lean:31) is a matrix-level, ℂ-only second definition (QICLean port) used by the §5/§6 files (ConditionalSkew*, MarginalPhase*, SkewSymbolBound, ReplicaEtaForms); the §5/§6 agents will claim its users. I counted only its 8-line definition.
- D2.11: `drift` + action `cut` because none of the four degenerate-case theorems is used by `area_law` (referenced only in OpenAI/Audit.lean). If the refactor keeps the paper's standing assumptions (q≥2, R≥1, Λ≠∅) these must instead be proved and used.
- D2.9: the Lean bound has constant v_R μ_R (paper 2 v_R μ_R) because the oriented `edgeBoundary` and the ambient diamond around the A-side endpoint replace "≤ 2·#∂ endpoints, graph ball, anchors". It lives in TailParameter.lean (a §3 file, 269 lines); I counted only the declarations for D2.9/D2.8, the rest of TailParameter.lean (tail parameter, concentration width, typical mass) is §3 for the other agent.

##### Digest vs paper / digest vs Lean notes (not fixed)
- D2.4 constants: digest says "C=2(1+2/e) works" (D2.4.4); Lean (frozen statement) uses C=4 and 8 for I. Frozen, so only a note. The paper's eq:conditional-continuity has an unspecified absolute C.
- D2.4.6: digest says |I−I'| ≤ 2 f(δ) ≤ 2C√δ log(e d_D); Lean has `abs_mutualInfo_sub_le` with 8√δ log(e d_X) (= 2·4), consistent.
- D2.5: Lean's statement is for ℂ (`EuclideanSpace ℂ n`) only; there is no 𝕜 version.
- D1.7: Corollary.lean proves the vertex forms with `max C 0` (paper silently assumes C ≥ 0).

##### Lean declarations stating the same anchor several times
- Ball cardinality (D2.7): `card_latticeDiamond` (exact, abstract graph), `card_graphBall_domainGraph_le` (2(d+1)²), `card_graphNbhd_singleton_le` ((2d+1)²), `…_le_four`, `…_le_two_mul`, `Scan.card_domainGraph_ball_le`, `Scan.CollarScan.card_ball_le_domainGraph` (not mapped by me; scan-specific).
- Multiplicity (D2.8): `card_admissibleSupport_containing_le`, `card_supports_containing_le_diamond`, `card_supportFamily_le_pow(_card_erase)`, `card_filter_mem_supports_le` (coarse); anchor fibre: `card_anchor_fiber_le_diamond`, `card_anchor_fiber_le`, `card_anchor_fiber_le_two_pow`, plus `card_anchor_fiber_subtype_le` (OpenAI/Amplification/GraphChannelWeightedRow.lean:77, §10, unmapped).
- Product decomposition (D2.10): two `…hasProductDecomposition…` theorems (CutTransport.lean:200, FilterChainEnergy.lean:97).
- Subadditivity: `Arealaw.regionEntropy_union_le` (ℂ, Subadditivity.lean:50) and `Arealaw.MState.regionEntropy_union_le` (𝕜, RegionEntropy.lean:170).
- Contractivity of trace distance under partial trace (D2.5.3): `D₁_restrict_le` and `Matrix.traceNorm_traceRight_le`.
- S(D) continuity: `conditional_continuity` at Y=∅ vs `FiniteProduct.abs_entropy_sub_le_sqrt_traceDistance` vs `abs_regionalEntropy_sub_le_sqrt_traceDistance`.
- Crossing-term counts: `card_crossingTerms_le_edgeBoundary` (TailParameter), `card_crossingTerms_rectRegion_le` (BufferedRectangles:150), `card_crossingTerms_le_of_isSafe` (SupportCounting), `card_crossingLabels_le` (CrossingBudget:88): four versions of the D2.9 argument in §3/§4 files.

##### Second encodings of regions / partial traces / entropy (plan decision 2)
- Region encoding in use: `Arealaw.Reg`, `Arealaw.ptrace`, `Arealaw.extendId`, `OpenAI.pureState`, `Arealaw.SubState.regionEntropy`, `mutualInfo` (note: `pureState` is defined in OpenAI/Statements.lean:191, not in Arealaw/).
- Second encodings:
  1. `FiniteProduct.*` (Configuration/`reducedPure`/`entropy β Ω R`, `FiniteProduct.splitEquiv`, `unionEquiv`; files OpenAI/FiniteProduct*.lean, OpenAI/Amplification/EntropyComparison.lean, AncillaSiteEntropy.lean, OpenAI/Scan/DomainFiniteProduct.lean, OpenAI/Bridges.lean `regionalEntropy_eq_finiteProduct`), ℂ-only, `EuclideanSpace ℂ`.
  2. Bipartite matrix encoding: `Arealaw.PureState`, `rhoA`, `EE` (Arealaw/State.lean), `Arealaw.vonNeumann` with `traceLeft/traceRight` (Physlib) used throughout ConditionalEntropy/ConditionalContinuity, plus `unionState` and Physlib `Sᵥₙ`/`MState` bridges (Arealaw/Subadditivity.lean, Arealaw/Bridge/*.lean).
  3. `Entropy.MarginalPhase.*` / `TensorPower.*` / `Entropy.FourPartition` (X×(U×F) triple products with `assocE`), QICLean ports, ℂ-only.
  4. `Arealaw.regionEntropy₂`, `mutualInfo₂` base-2 duplicates (Mixed.lean:273-300), `Arealaw.Qubits` (Mixed.lean:320): BH12/qubit tree, unmapped (foreign).
- Bridges between them: OpenAI/Bridges.lean (420 lines: walk/neighbourhood bridges, `regionEntropy_pureState_eq_sum_negMulLog…`, `IsSupportedOn` closure); I mapped only `mem_supports_iff_walk` and `mem_graphNbhd_iff_walk` from it. The rest is scaffold candidates for the reverse pass.

##### Piecewise 𝕜/ℂ transfers noticed
- `OpenAI.toComplex` and OpenAI/Embedding.lean (505 lines): SSA, subadditivity, Araki–Lieb are proved over ℂ (Physlib) in `vonNeumann_*_complex` (ConditionalEntropy.lean:284,310,331) and carried to 𝕜 entry-wise (ConditionalEntropy.lean:364-404, RegionEntropy.lean:170 `MState.regionEntropy_union_le`). Also `OpenAI.vonNeumann_of_eq_map_toComplex` (ConditionalEntropy.lean:253), `OpenAI.BufferDiscount.regionEntropy_pureState_toComplex` (BufferDiscount.lean:445, §3, unmapped).
- Separately ℂ-only with no 𝕜 transfer: `traceDistance_vecMulVec_le_norm_sub` and `Matrix.traceNorm_div_two_vecMulVec_eq` (D2.5), `Arealaw.regionEntropy_union_le`, FiniteProduct.* continuity; Lemma 2.1 itself is 𝕜-generic.

##### Provenance flags (Step 2 deletions)
- Files headed "Ported from LionSR/QICLean|TNLean" within my rows: PureStateTraceDistance.lean (D2.5), LatticeCounts.lean, GraphInteractionDiamondCounting.lean, GraphInteractionBudget.lean, GraphLatticeDiamond.lean, TailParameter.lean, CutTerms.lean, FiniteProductContinuity.lean, RegionalEntropyContinuity.lean, MarginalPhaseQuadratic.lean. Their `[OAI265]`-citing docstrings are fine; the provenance headers and implementation-note narration (ConditionalEntropy.lean:1-85, ConditionalContinuity.lean:1-62, RegionSSA.lean:1-57, TailParameter.lean:1-60) go in Step 2.
- Foreign-looking citations found while grepping (not mapped, for the reverse pass): OpenAI/RootFidelityRelativeEntropy.lean, PurificationSplitting.lean, UhlmannIsometry.lean cite "Polynomial-PEPS manuscript Lemma 2.2 lem:fidelity" (a different paper's Lemma 2.2) — foreign.
- Arealaw files outside the closure of OpenAI.AreaLaw (closure.json): Bell, Chain, Cor, DataHiding, EDC, Equipartition, Geometry, Kronecker, Ladder, Postselection, PurifiedDist, Purify, PurifyChain, Saturation, SmoothEntropy, Spectrum, Uhlmann (BH12 tree; `dead`/`foreign` candidates). Arealaw/Fidelity.lean (292) and OpNorm.lean/SVD.lean are in the closure but belong to later sections (not mapped here).

##### Standard-library searches (D2.2, D2.3, D2.4, D2.5)
- Mathlib: `Real.binEntropy` found and already used (D2.3). Physlib: `Sᵥₙ_strong_subadditivity`, `Sᵥₙ_subadditivity`, `Sᵥₙ_triangle_subaddivity` (ℂ, normalized; cited in ConditionalEntropy.lean), `TrDistance` (ℂ). No AFW/Winter continuity bound and no pure-state trace-distance formula found (two atlas semantic searches returned only unrelated github repos); local grep of `.lake/packages` not possible (no .lake). Loogle/leansearch not run: search pending for D2.4/D2.5/D2.7/D2.8.

### Notes, §03

#### Notes for the integrator: s03 (digest/03-initial-box.md)

Counts: faithful 12 (D3.1, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 15), smeared 3 (D3.2, 3.5, 3.10), drift 1 (D3.16), none 1 (D3.17), missing 0, overbuilt 0. Total 10581 lines (≈15.7 Lean lines per LaTeX line of the 676-line source).

##### Unsure / judgement calls
- D3.6 and D3.12 are conjunctions of facts, each its own declaration (Z_r bound, mass 2, cost 4/Z, min; zero-floor, pinning, trial bound). Marked faithful; a stricter reading gives smeared.
- D3.9 is marked faithful even though it carries duplicate non-sharp coefficient chains; D3.11 is faithful although stated multiplicatively (√(1−E/Δ)^m N_m ≤ ∏x_k) rather than as −2 log N ≥ …; the log form is taken inside `sum_mul_condEntropy_le` (BufferDiscountCore.lean:362).
- Attribution is by file or by declaration range (BufferDiscount, BufferDiscountCore, Rectangles, FilterMoment, LogClipping, HarmonicWeights, SupportCounting, BufferedRectangles are split; ranges are in mapped.txt through the declaration names). The 268-line proof `OpenAI.condEntropy_le_initialBuffer_of_constants` (BufferDiscount.lean:177-437) contains D3.5, D3.6/D3.10 choices and D3.14.5 inline; all counted in D3.5.

##### Digest vs paper / Lean differences (not fixed)
- D3.5: digest says D>2R+2 "is the paper's choice"; Lean uses D=R+1 and only R<D₀ (single split needs only D>R).
- D3.10/D3.11: Lean makes the energy budget E ≤ Δ/2 (overlap ≥ 1/2, prefix error m·log 2 ≤ C_pad r) instead of Cℰ/Δ ≤ 1/4 with error C(m+1)ℰ; C_pad is given in closed form from Z_min (BufferDiscount.lean:482).
- D3.15: Lean's F_box also takes the sup over D₀ > 2R+10 (frozen statement quantifies ∀ D₀ too).
- D3.2.4: Lean states the tail as typical mass ≥ 1−(n+2)^−M (`Entropy.typicalMass`, `concentrationWidth` in Scan/MarginalTailsBridge.lean) for n ≥ 0, M ≥ 0; digest/paper: n ≥ 1, Pr ≤ (n+2)^−M.
- D3.16: random order replaced by cyclic colour rotations (RotatedChainRule.lean, ChildColoring.lean); constants M=8(C_pad+1), p=1/(2(2C_pad+1)²) differ from the digest's M ≥ 16(C_pad+2), p₀=(2C_pad+5)^−2.

##### Duplicated statements / second encodings
- Crossing-term count for a safe contour (D3.5(e)) is proved three times: `IsIntRect.card_crossingTerms_le_of_isSafe` (SupportCounting.lean:200, K=8R·2^{(2R+1)²}, used by BufferDiscount), `card_crossingTerms_rectRegion_le` (BufferedRectangles.lean:150, 8(R+1)μ_R, unused outside Audit), and `card_crossingTerms_le_edgeBoundary` (TailParameter.lean:82, general cut, v_Rμ_R) for D3.2. The 𝓑 ≤ K'(…) bound also appears twice: `cutLogBudget_le_card` (BufferDiscount.lean:90, (2R+1)²) and `cutLogBudget_le_card_diamond` (TailParameter.lean:118, v_R=1+2R(R+1)). `latticeCutLogBudget` (Scan/MarginalTailsBridge.lean:113) is a lattice copy of the general `cutLogBudget` (CutTerms.lean:76).
- Non-sharp duplicates of the D3.9.3-4 coefficient bound (constant 2 vs sharp a²/2): dead `LogClipping.sqrt_mul_cosh_sub_one_le` (+ `sinh_le_mul_cosh`, `cosh_sub_one_le`, private `sq_le_mul_exp_half`, lines 145-265), `FilterMoment.abs_re_inner_sub_inner_conj_le`:357, `FilterEnergy.abs_re_inner_sub_conj_le_of_common_basis`:141, `FilterChainEnergy.abs_re_inner_sub_chain_conj_le`:475 (no uses outside OpenAI/Audit.lean). `FilterExcitation.re_inner_sub_le_of_chain`:161 is a live weaker-constant wrapper around `_sharp`.
- Two parallel fragments for zero/positive floor: `IsFeasibleFilter` is parameterised by a floor f; the paper only needs f>0 then the limit (D3.12(a)).
- No second encoding of `Reg`, `pureState`, `SubState.regionEntropy`, `mutualInfo` seen in these files: they all use `Reg loc U`, `Arealaw.extendId`/`ptrace`, `pureState`, `regionEntropy`. But the filter files work with `EuclideanSpace ℂ (Reg loc U)` vectors and `vonNeumann (isHermitian_ptrace_vecMulVec_star …)` (BufferDiscountCore.lean) with bridge lemmas `regionEntropy_pureState_eq_vonNeumann` (RegionLift.lean:265) and `regionEntropy_pureState_toComplex` (BufferDiscount.lean:445): a second spelling of region entropy (`vonNeumann ∘ ptrace ∘ vecMulVec`) to unify in Step 2.
- `OpenAI.MarginalTails` frozen statement uses `Fintype.card (Reg loc (D i))` as d_i and a general `σ`/`loc` site type, while D3.2 and §4 specialise to `Qudits q`; the glue `marginal_tails` ↔ lattice use goes through `Scan/MarginalTailsBridge` and `TailParameter` (§9/§10 files).

##### Piecewise 𝕜/ℂ transfers
- `marginal_tails` (MarginalTails.lean:135 plus lemmas 60-135: `toComplex` bridges, `hasGlobalGap_submatrix_equiv`, `surprisalMoment_eigenvalues_map_toComplex`, `surprisalTail_eigenvalues_map_toComplex`) and `bufferDiscount_of_complex` (BufferDiscount.lean:456, with `regionEntropy_pureState_toComplex`:445). Everything between (EigenbasisTails, GapSurprisal, ModularExpectation, StripQuadratic, FilterPower, FilterPrefix, FilterExcitation, FilterChainEnergy, FilterEnergy, FilterMoment, BufferDiscountCore:207-446) is ℂ-only. D3.15/D3.16 (BoxEntropy, InitialBoxEstimate, RotatedChainRule) are 𝕜-generic with no transfer. The algebra in FilterMaximizer, FilterStationarity (algebra half), FilterChain, FilterOptimizer (feasibility), FilterClipping (algebra), RegionLift, BufferDiscountCore (`mono_floor`, `exists_trial_filter`, `sum_norm_sq_mul_regionEntropy_le`) is stated for `RCLike 𝕜` but used at ℂ only.

##### Files shared with other sections or not claimed
- Claimed here but also used elsewhere: SurprisalMoment.lean (§10 IidSurprisal, TypicalSet), SchmidtTilt.lean (§4 SpectralFilter, GapPerturbation), Rectangles.lean (§9, §11; its ambient dilation part, lines 111-236, is D2.6), RegionLift.lean (widely), CutTransport.lean (ConditionalExpectation), BoxEntropy.lean (§9, §11), HarmonicWeights scale recurrence (reusable for §9).
- NOT claimed (belong to §2 or other digests): SupportCounting.lean lines 1-167 (supports, `card_filter_mem_supports_le`, `hamiltonian_eq_sum_supports`, `norm_extendId_le`, `sum_norm_extendId_containing_le`, D2.7-D2.10, but used directly by BufferDiscount), BufferedRectangles.lean lines 1-106 and 122-149 (`card_admissibleSupport_containing_le`, diamond counts, used by TailParameter/LatticeCounts), SchmidtRank.lean and MaximalOverlap.lean (only used by UhlmannIsometry/MarginalSupportAbsorption), TypicalSet.lean/TailParameter consumers in Scan/ and Amplification/, ImprovedBoxEstimate.lean (§9, Prop 9.5). RegionSSA.lean (SSA, D2.2) is listed under (section infra) here in case §2 does not claim it.
- decls.tsv name artefacts: docstring "namespace `Entropy`" / "namespace is" produce names like `` `Entropy`.OpenAI.exists_trial_filter `` and `is.OpenAI.buffer_discount`; the real names are `OpenAI.…` (mapped.txt uses the real names). `` `Entropy`.Matrix.* `` entries in FilterMaximizer etc. are `Matrix.*`.

##### Provenance prose to delete in Step 2 (not read for the mapping)
Docstrings and file headers of TailParameter, BufferDiscount, BufferDiscountCore, FilterZeroFloor, FilterMaximizer, FilterStationarity, FilterClipping, FilterOptimizer, LogClipping, HarmonicWeights, RotatedChainRule, ChildColoring, InitialBoxEstimate, SupportCounting, RegionLift cite "Ported from QICLean/TNLean at commit …" (foreign provenance); the code is on the path of Lemma 3.2/Prop 3.3, so none is `foreign` in the reverse pass, only the narration.

### Notes, §04

#### Notes (digest 04-quasilocal.md)

##### Anchors I was unsure about
- D4.11/D4.14: Prop 4.5 is split into three lattice declarations; I gave `exists_latticeFiniteSetTruncation` to D4.11 and the two crossing/cut declarations to D4.14 (D4.14's statement is the crossing clause of D4.11).
- D4.7 and D4.8 do not have a declaration per anchor; lines are cut by line range inside `SpectralFilter/PositiveReplacement.lean` (1–259 D4.7, 260–354 D4.6) and `FilterLocality.lean` (1–256 D4.8, 257–348 D4.6) and `LatticeConstraints.lean` (1–81 header→D4.11, 82–113 D4.14, 114–211 D4.6, 212–283 D4.11, 284–338 D4.14). The split points are my judgement.
- `Amplification/LocalRootChannels.lean` serves both D4.10 (lines 1–234) and §10 (shells, 235–297). The §10 mapper may also claim lines 1–234; the integrator should dedupe.
- Counting lemmas overlap with the §2 map: `SupportCounting.lean` (`card_le_of_mem_supports`, `card_filter_mem_supports_le`), `LatticeCounts.card_graphBall_domainGraph_le` (D2.7) are NOT claimed here; I claimed only `sum_norm_extendId_containing_le`, `card_anchor_fiber_le`, `card_anchor_fiber_le_diamond`, the four ball/box lemmas in `FiniteSetTruncation.lean`, and the dead `GraphInteractionDiamondCounting.lean`. `GraphInteractionBudget.lean` is parked in (section infra).
- Digest vs paper: none found. D4.4 digest says `v = 2 v_R J μ_R e^{cR}` (c=μ); the Lean generic lemma has `e^{2μR}` (different constant, same shape).

##### Lean declarations stating one anchor more than once
- Prop 4.3 (D4.6): `PositiveReplacement` (frozen, Statements.lean:259) proved by `positive_replacement_complex` (PositiveConstraints.lean:145) and `positive_replacement` (𝕜); restated as `exists_latticePositiveConstraints` (LatticeConstraints.lean:126) which is what §9/§10 use; abstract version `SpectralFilter.positive_replacement` (PositiveReplacement.lean:313).
- Prop 4.5 ground-state part: `exists_latticeFiniteSetTruncation` (live), `exists_finiteSetTruncation` (abstract), `exists_finiteSetTruncation_of_gap` (dead, FiniteSetTruncationOfGap.lean:27).
- Lemma 4.4: `quasilocal_roots` (dead, weaker fixed-point) vs live `Matrix.rootChannel` + `localRootChannel` (spectator form). `exists_latticeQuasilocalRoots` was explicitly not ported (LatticeConstraints.lean header).
- Lemma 4.1: two statements in two files (generic graph, lattice with c=1).
- Counting (D4.3/D2.7/D2.8): at least four encodings of ball/multiplicity counts: box `(2R+1)^2` (`card_anchor_fiber_le`), diamond (`card_anchor_fiber_le_diamond`), `card_anchor_fiber_le_two_pow` and `card_graphNbhd_singleton_le_two_mul` in `Amplification/ConstraintWordTruncation.lean`, `card_graphBall_domainGraph_le` (2(d+1)^2) and `card_graphNbhd_singleton_le_four` (4(d+1)^2).

##### Second encodings noticed (relative to Arealaw `Reg`, `ptrace`, `extendId`, `mutualInfo`)
- `condExpect` is built on Arealaw `ptrace`/`extendId` (good), but `ConditionalExpectation.condExpectₗ` (linear-map version, never referenced) and `RegionLift.extendIdₗ` exist, `FilterPower.extendIdCLM` (§10), `SpectatorSiteExpectation.spectatorCondExpect` (§10) and `Entropy.IsSupportedOn` (ReplicaSupport.lean:31) next to `OpenAI.IsSupportedOn` (Statements.lean:246): second encodings of "supported on".
- `ComplexWitnessTransfer.lean` re-proves that `ptrace`, `extendId`, `condExpect`, `IsSupportedOn` commute with `realProjection` (bridges).
- Two encodings of `τ_t`: `LiebRobinson.heisenbergEvolution` (`exp(t•(I•H)) A exp(-t•(I•H))`) used in GraphPropagation/CommutatorRecursion, `Matrix.hermitianUnitaryPath` (HermitianUnitaryPath.lean, also used in §7 Transport) used in MatrixFilter/FilterLocality; bridged inside HamiltonianLocalization.lean (`convert … using 1`) and mentioned as `heisenbergEvolution_eq_hermitianUnitaryPath` in SiteExpectationOrder.lean's docstring (no declaration of that name found by grep).
- Two encodings of the graph: abstract `SimpleGraph ι` in the Lieb–Robinson file vs `domainEDist`/`graphNbhd` on `Finset (ℤ×ℤ)`; scaffolding `supportInDomain`, `supportedOnSubmodule`, `mem_supportInDomain`, `card_supportInDomain`, `disjoint_of_disjoint_supportInDomain` (HamiltonianLocalization.lean:31–66) converts between them. Two encodings of the root channel (`rootChannel (G ⊗ₖ 1)` vs `spectatorRootChannel`).
- Entropy/mutual information do not occur in §4.

##### Piecewise 𝕜/ℂ transfers
- `ComplexWitnessTransfer.lean` (365 lines, outside the closure of `OpenAI.AreaLaw`): transfers `PositiveReplacement ℂ` to `PositiveReplacement 𝕜`; a per-statement transfer, to be deleted when the single top-level transfer exists.
- `ConditionalExpectation.condExpect_map_toComplex` (:142) transfers `condExpect` along `toComplex`; `condExpect` itself and its algebra lemmas are 𝕜-generic but `norm_condExpect_le`, everything in `LatticeConstraints`, `FiniteSetTruncation*`, `GapPerturbation`, `SqrtHolder` (C⋆), `RootChannel` are ℂ-only. `Statements.lean` §4 items: only `condExpect`, `IsSupportedOn`, `PositiveReplacement` are 𝕜-generic.
- Consequence: the frozen `PositiveReplacement 𝕜` is not on the path of `OpenAI.AreaLaw` (neither `positive_replacement` nor `ComplexWitnessTransfer` are in `closure.json`); the main path uses the ℂ lattice theorem directly.

##### Outside the import closure of `OpenAI.AreaLaw`
`GraphInteractionDiamondCounting.lean`, `QuasilocalRoots.lean`, `FiniteSetTruncationOfGap.lean`, `ComplexWitnessTransfer.lean`, `PositiveReplacement.lean` (all mapped above; all candidates for `cut` unless re-pointed). `SpatialExpectation` not examined.

##### Not determined
- Mathlib/Physlib availability: only the atlas semantic search was run (no Physlib, no loogle structural pass); statements "not found" mean "not found by atlas semantic search".
- Exact per-line attribution inside split files is by declaration boundaries (±header lines).

### Notes, §05

#### notes (s05, 05-conditional.md)

Attribution is by file or declaration range; every line of the listed files is counted exactly once (checked by gen.py coverage). Section total 15002 = 12725 on anchors + 2277 section infra.

##### Digest vs Lean
- Lemma 5.1 (D5.5–D5.11) is the largest drift: Lean never forms ‖K‖_r, λ(u), ξ-overlap-in-log, the Hellinger inequality D5.8, or the harmonic-measure integral. It works with coefficient matrices C (Matrix (X×U)(P×F)), a Hölder "optimizer" (`optimizerWeights`) and a *linear* Rényi deficit 1−Tr(...), paired three-lines with Gaussian weight, β = 2a (the interpolation lemma has `β ≤ 1/4`, exponent β/4 = a/2). The statement D5.5 matches; the integrator must decide whether to keep Lean's route and rewrite the digest's D5.6–D5.11, or re-prove along the digest (the digest wins).
- D5.3 paper has Markov tail step D5.3.1; Lean has none (only b ≥ 0, cutoff-based second moment).
- D5.16: the paper's narrow-strip statement does not exist as a declaration; `OpenAI.StripQuadratic` has a generic version (strip 1/(8ℓ)), plus `abs_re_sub_le_of_strip` (a second route to D5.19.4). `OpenAI.StripQuadratic` is also imported by `OpenAI.ModularExpectation`, which is outside D5 (used by `OpenAI.SchmidtTilt`): another digest's file.
- Lean's D5.15 hypothesis is `a*log(e*card(P₀×X)) ≤ 1/8` and its constant is the explicit `skewConst`; Lean's D5.19 abstract lemma needs `|t| ≤ 1/(16ℓ)`.
- D5.12: statement is stated for √ρ_f in HS form (`norm_phaseDifference_le`) and for θ (`norm_phaseDifference_mulVec_le`); both in the same row. D5.17 re-derives the θ-form through `thetaR`/`relUnitary`.

##### Same anchor stated twice / duplicates of other sections
- `ConditionalMovement.QuantumSSA.conditional_continuity` (EntropyContinuity.lean:95) duplicates Lemma 2.1 (`OpenAI.conditional_continuity`, ConditionalContinuity.lean:270, which says it was ported from this one). `ConditionalMovement.QuantumSSA` also has its own SSA (StrongSubadditivity.lean), partial traces `ptrL/ptrR`, `traceEntropy`, `conditionalEntropy` (EntropyBounds, PartialTrace, PureEntropy): a second encoding of entropy on coefficient matrices, none using `Arealaw.Reg`/`SubState.regionEntropy`/`mutualInfo`.
- The D5.2.1 domination ρ ≤ d(I⊗ρ_U) is proved three times: `collision_le` (ConditionalCollision.lean:71, entrywise), `compression_invQuadA_le` (MarginalPhaseQuadratic.lean:125, HS form with ρ_{UF}), and implicitly in `skewFun` strip bounds (d_h²).
- Four encodings of marginals of a pure θ: movement (`movementMarginalXU/XP`, coefficient matrices; ConditionalMovementEstimate.lean:154–176), marginal phase (`marginalXU/U/UF`, MarginalPhaseSetup.lean:35–44), skew (`margP/margW/margY`, ConditionalSkewSetup.lean:36–45; θ as a function on `(P₀×P₁)×((X×U)×F)`), regional (`frameMarginalP/Y`, ConditionalMovementRegional.lean:333–338, on `SiteConfig n` with `FourPartition`). Plus `rhoW`, `thetaR`, `reindexE`, `regroup` bridges in ConditionalSkew*. All ℂ-only matrices over product types; none is `Arealaw.Reg`.
- Hat/bracket powers: four encodings (see D5.1 row), plus `Matrix.spectralFun`, `cpowSpec`, `rpowSpec`, `Matrix.cfcC` (CfcComplex.lean:26) in the shared Spectral*/Cfc* files that I did not map (general spectral calculus, closure members; likely claimed by §2 or reverse pass).

##### Not mapped by me (outside D5 or other digest; reverse pass should assign)
- `OpenAI/ModularExpectation.lean`, `OpenAI/SchmidtTilt.lean`-related (Schmidt tilt: other section); `OpenAI/ResolventFunctionalCalculus.lean` (its header says it serves Section 7); `OpenAI/MarginalSupport.lean`, `MarginalSupportAbsorption.lean` (used by `ProductMarginals`), `MarginalTails.lean` (Lemma 3.1), `PhaseError.lean` (Prop 4.5), `RelativePin.lean` (Lemma 6.3, consumer of `regionalMovement_norm_le`), `SkewSymbolBound.lean` (Lemma 6.4, consumer of `conditionalSkew_le`), `ReplicaTransportSplitSkewBound.lean` (Prop 7.4), `RegionSplit.lean`/`ReplicaEtaForms.lean` (consumers of `MovementEtaRegional`).
- `ConditionalMovement/LogCompression.lean` is imported also by `PositiveProjectionCompression`, `SpectralProjectionIntertwiner`; I put it in section infra for D5 because its in-section importer is `PartialTrace`.

##### 𝕜 / ℂ
Everything in D5 is ℂ-only; transfer to 𝕜 happens above this section (e.g. `Arealaw.vonNeumann_*_complex` vs 𝕜 versions in ConditionalEntropy.lean; `OpenAI.traceLeft_map_toComplex`). No piecewise transfer found inside these files.

##### Unsure
- D5.17 pitfall (first mirroring gives ρ_{YF}) not verified line by line.
- Standard?-items: Mathlib has `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (three lines); no Mathlib hit for the resolvent/Mellin integral ∫v^z/(x+v), the concavity Hellinger inequality, or the Nussbaum–Szkoła variable ("search pending" for the last two).
- Line counts of split files are by declaration range (headers/imports fall into the range they precede); regional/Marginal files whole.

### Notes, §06

#### Notes for the integrator (digest 06-replicas.md)

Status counts (17 anchors): faithful 6 (D6.1, 3, 5, 8, 10, 14), smeared 7 (D6.4, 6, 9, 12, 13, 15, 16), overbuilt 1 (D6.2), drift 1 (D6.11), missing 1 (D6.7), none 1 (D6.17).

##### Scope and attribution choices
- The digest covers only §6, but the Replica*/Bell*/Pinned*/Coherent*/Schur* files in OpenAI/ mostly cite `06-transport.tex`, `07-comparators.tex` or `08-scanner.tex`. I attributed to D6.x only files whose docstrings cite `05-replicas.tex` lines belonging to that anchor; the rest (111 files, ≈19.6k lines, list in mapped.txt tagged `(section infra)`) are parked in the infra row. The §7/§8/§9 mappers should claim them; the integrator must de-duplicate so no file is counted twice. Excluded from my rows and from mapped.txt on purpose: OpenAI/ConditionalMovementRegional.lean (Lemma 5.1, §5), OpenAI/Scan/* (§9), OpenAI/WeylTwirl.lean (feeds `condExpect`, not §6), OpenAI/LeafStates.lean, OpenAI/LeafStateIntertwine.lean (not in closure.json; §7 tree states), generic matrix/cfc infrastructure (OrthogonalResolution(Cfc), MatrixIntertwine, L2OpNormReindex, MatrixPowers, ...) which the reverse pass should classify as `standard`/`scaffold`.
- `OpenAI/PurificationSplitting.lean` cites "Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`": a different paper's Lemma 6.4. Classify `foreign` (not mapped by me).
- Declaration-level overrides inside files that are otherwise mapped whole to another row (in mapped.txt the declaration lines win): `Partition.replicaConst`, `Partition.replicaWeight` (ReplicaWeight.lean, file is D6.6), `TensorPower.replicaLabelWeight`, `TensorPower.replicaMetric` (ReplicaMetric.lean, file is D6.6) → D6.5; `TensorPower.leafRoot`, `TensorPower.leafMetric` (ReplicaSimilarity.lean, file is D6.13), `leafRoot_comm`, `leafMetric_comm` (ReplicaEtaForms.lean, file is D6.12) → D6.8; `relativePin_regionalMovementEta`, `relativePin_toF` (ReplicaEtaForms.lean) → D6.10. Line counts in map.md already subtract these (D6.5 21, D6.8 28 from the decls + 83 file, D6.10 +57).
- D6.12 item (1) (`exists_norm_markedSimilarity_mulVec_le`) and the commutation `commute_labelObservable_siteOp_of_disjoint` for D6.9.3 live inside ReplicaSimilarity.lean, counted under D6.13.

##### Digest vs Lean / paper
- No digest/paper disagreement found in the parts I read.
- Lean works with `0<t<1/2` (ratios, inverse, symbols; ReplicaMarkedRatioInverse.lean, MarkedSimilaritySymbol.lean) and `0<t≤1` (integral, relative pin; ReplicaIntegral.lean:173, RelativePin.lean:151); the paper fixes `0<t<1/4`. Pure generalisation, no extra proof cost known.
- D6.9: the floor is not proved in a §6 file in the paper's form; Lean cites `07-comparators.tex` and proves one-sided inverse bounds for covers `P∪Y∪F=univ`. `log A_k = a(F_P+F_F−F_Y)+O(log k)` is never stated.
- D6.6 route differs (orthant/exponential weight instead of simplex; `Tr(A|_m)^p` instead of min–max), see map row.
- D6.2 (standard, cited in the paper) is ≈5.3k lines and D6.4 part (1) has four overlapping routes to the dimension formula (HookDimension, HookRecursion, WeylRecursion, JucysRecursion/WeylDimension); the biggest line saving in this section.

##### Same statement more than once
- Lemma 6.3: `relativePin` (RelativePin.lean:151), `relativePin_regionalMovementEta`, `relativePin_toF` (ReplicaEtaForms.lean), and the §7 form `relativePinBound` (ReplicaTransportRelativePinBound.lean).
- Lemma 6.4 item 4: SkewSymbolBound.lean:466, ReplicaEtaForms.lean:284 and :306, ReplicaTransportSplitSkewBound.lean:322.
- Lemma 6.1(3) merge moment: `merge_moment_le` (MergeMoment.lean:434) and the pairwise/five-factor variants PairMergeMoment, PhysicalMergeHolder, MergeExponential (parked, §8).
- Floor/inverse bound: ReplicaWholeInverse, ReplicaGroupedInverse, ReplicaSymmetricMetricFloor, ReplicaTransportSymmetricMetricFloor, ReplicaTransportRootMetricFloor, ReplicaTransportSymmetricMetric.
- Counting lemma `card_filter_apply_eq_mul` twice (UniformHusimi.lean:69, InjectionProduct.lean:48).
- Three symbol calculi: `IsInjectionPoly` (InjectionPoly.lean:295), `IsMarkedPoly`/`HasMarkedSymbol` (MarkedSymbol.lean:266,275), `HasCoherentSymbol` (CoherentSymbol.lean:130).

##### Second encodings (relevant to Plan Step 0 item 2)
- Nothing in the §6 files imports `Arealaw/` or uses `Reg`, `pureState`, `SubState.regionEntropy`, `mutualInfo`. Instead OpenAI/ has its own region/entropy encoding used by D6.10/D6.12: `Entropy.SiteConfig`, `RegionConfig`, `FourPartition`, `Entropy.movementEta`, `regionalMovementEta`, `skewEta`, `localLift`, `frameVector` (ConditionalMovementRegional.lean, RegionLift, RegionEntropy) and the bridge `ReplicaRegionUnion.lean`. These are second encodings of regions, marginals and conditional entropy (η_θ = S(x|P)+S(x|Y₀)). `ReplicaEtaForms.lean` exists only to convert between `movementEta` and `regionalMovementEta`.
- V (the tensor-factorised system) has three encodings in §6 code: family `ι : F → Type` (`Config k ι`, ReplicaMetric etc.), `n : V → ℕ` (`SiteConfig n`, ReplicaSimilarity etc.) and plain `Ω`/`Fin q` (Schur estimates, coherent symbols); `splitEquiv`, `subsystemSplitEquiv`, `SubConfig/ComplConfig` bridge them.
- Two encodings of the coherent measure: `coherentIntegral` via Haar on U(Ω) (CoherentMeasure.lean:23) and `coherentMeasure` on `CoherentSphere` (ReplicaTransportCoherentMeasure.lean:146); plus `coherentExpect`.

##### 𝕜 / ℂ
- All §6 declarations are ℂ-only (matrices over `ℂ`). No `[RCLike 𝕜]` and no ℂ→𝕜 transfer in these files (`RCLike` appears only via `RCLike.re_le_norm`). Nothing to delete here for the scalar-field decision.

##### Unsure
- D6.15 Pitfall (separate centres) judged from statements only.
- D6.1 `D_k` polynomial/`D_k/D_{k+m}=1+O(1/k)` (D6.14.5) is folded into UniformHusimi.lean; not located separately.
- Mathlib search for D6.14 (Chiribella/coherent resolution) and `#irreps = #conjugacy classes` is pending; no Mathlib Schur–Weyl/Weyl-character/hook/Specht found (atlas glob on names returned nothing).
- Line counts are whole-file; ReplicaSimilarity.lean (614) mixes D6.8 defs, D6.9.3 commutations, D6.12(1) and D6.13.

### Notes, §07

#### s07 notes (digest/07-transport.md)

##### Unsure / judgement calls
- Attribution of mixed files is by line range (alloc.py in this directory reproduces it; mapped.txt lists declarations for split files, file paths for whole files). Header/import/module-doc lines go with the neighbouring range, so per-row line counts are approximate (each file is fully covered, no line counted twice; total 13 006).
- D7.4: Lean has no definition of "completely positive" or "unital"; only `IsNPositiveMap k` and `IsPositiveMap`. Marked overbuilt. Mathlib has `CompletelyPositiveMap` (Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap); fit to `Matrix n n ℂ` not checked.
- D7.21 vs paper: Lean takes T = sqrt(h̄_i) on the whole space and builds B with a kernel projector; the paper's T : S_k -> D = ran T_i is a different construction. Both give Y^*Z = O, (Y−Z)^*(Y−Z) = 𝖣, Y = Z on commuting leaves, so the result is the same.
- D7.20: Lean never states the operator inequality log C_{h,g} ≥ ka·𝒬_k(…) + (log b_k − log D_k)I; it goes straight to the trace inequality.
- D7.27 is a remark; the single definition `TransportData.state` makes it automatic. Status none.

##### Digest vs paper
- Nothing found that disagrees. Minor: D7.9 digest says edges of weight 0 are omitted and trees contracted; Lean instead assumes positive weights (`IsAdmissible.histWeight_pos`, `choiceWeight_pos`).

##### Same anchor stated more than once
- D7.14 (Proposition 7.4): `ReplicaTransport.transport` (OpenAI/ReplicaTransport.lean:53); `transport_of_relativePin_of_splitSkewBound` (OpenAI/ReplicaTransportProposition.lean:54); `transport_of_splitSkewBound` (OpenAI/ReplicaTransportRelativePinBound.lean:251); `transport_finite_family` (OpenAI/ReplicaTransportFiniteFamily.lean:43).
- Lemma 6.3 restated inside §7 as `RelativePinBound` (OpenAI/ReplicaTransportPrerequisites.lean:48), Lemma 6.4 as `SplitSkewBound` (:68), each with a bridge proof (ReplicaTransportRelativePinBound.lean, ReplicaTransportSplitSkewBound.lean). This is a second statement of D6.10 and D6.12; the §6 agent should map the originals.
- The band metric: `bandMetric` (ReplicaTransportSetup.lean:108) is a one-line alias of `leafMetric` (§6, OpenAI/ReplicaSimilarity.lean:101).

##### Second encodings (for the reverse pass and for plan decisions 1 and 2)
- Entropy and regions: `moveEta`/`splitBandEta` use `FiniteProduct.conditionalMutualInformation` (OpenAI/FiniteProductConditional.lean:30), regions as `Finset V` on `EuclideanSpace ℂ (∀ v, Fin (n v))`. This is not Arealaw `Reg`, `pureState`, `SubState.regionEntropy` or `mutualInfo`. No bridge to Arealaw was seen inside the §7 files.
- Sym^k: S_k is `symmetricSubspace`/`symProj` inside the full tensor space `Config k …`; all band metrics are padded by `Π A + (1−Π)` (`symBandMetric`), which forces Commutant.lean, the extension lemmas (ReplicaTransportSymmetricMetric.lean lines 190–296) and the `symProj_mul_*` lemmas.
- Coherent measure: three encodings, `realCoherentIntegral` (ReplicaTransportSetup.lean:58), `coherentIntegral` (OpenAI/CoherentMeasure.lean:23), `coherentMeasure` on `CoherentSphere` (OpenAI/ReplicaTransportCoherentMeasure.lean:146); all via Haar on the unitary group, U ↦ U e_a.

##### 𝕜/ℂ
- Every §7 declaration is ℂ-only (`Matrix n n ℂ`, vectors `→ ℂ`). The RCLike hits in these files are incidental (`RCLike.re` etc.). No piecewise 𝕜→ℂ transfer found in §7. `OpenAI/Scan/ActualRoundTransport.lean` consumes `transport_finite_family`.

##### Files I did not map (probably other sections; flag for the reverse pass)
- §9 initial floor: OpenAI/Transport/MetricFloor.lean, OpenAI/ReplicaTransportRootMetricFloor.lean, OpenAI/ReplicaTransportSymmetricMetricFloor.lean (used by Scan/ActualInitialRootNorm.lean); OpenAI/ReplicaTransportRootCompression.lean (used by Scan/AugmentedRootCompression.lean); OpenAI/ReplicaTransportLeafMeasure.lean (transportLeafMeasure, used by Scan/TransportRound*.lean for `scanner:Q-definition`).
- §8 consumers of Lemma 7.1: OpenAI/MeanTree{ProjectionLogBound,ProjectionMassBound,ProjectionMultibandUpper,ProjectionSectors,ProjectionUpper,SublinearRemainder,LogFloorDeficit,LogFloorExp,MultibandLowerNorm,ExponentialLowerNorm,UniformExpectation}.lean, OpenAI/InversePowerLogJensen.lean, NormalizedInversePowerLogBound.lean, ReplicaSymmetricMeanTreeProduct.lean, ReplicaMeanIdentityExtension.lean (all in the import closure).
- §6: CoherentResolution.lean (D6.11), CoherentSymbol*.lean, RelativePin*.lean (D6.10), SkewSymbolBound.lean (D6.12), ReplicaSimilarity.lean (`leafMetric`, `copyMean`).
- Dead (outside closure) files I placed under (section infra): Transport/Intertwine.lean, GeometricMeanDerivativeIntertwine.lean, MeanTreeDerivativeIntertwine.lean, PowerDerivativeIntertwine.lean, LeafStateIntertwine.lean, SingleKraus.lean (484 lines in total).

##### Mathlib/Physlib search
- Done with atlas only (Physlib not checked). No match for matrix weighted geometric mean (Kubo–Ando), Kadison–Schwarz for CP maps, operator Jensen, Fréchet derivative of matrix rpow, Fourier transform of sech. Match: `CompletelyPositiveMap` (D7.4); `CFC.rpow_le_rpow` already used for operator monotonicity.

### Notes, §08

#### Notes for the integrator (digest 08-comparators)

##### Scope decisions
- `OpenAI/Scan/` was NOT mapped (6 868 lines in 28 files cite comparator labels or Proposition 8.1). They instantiate §8 at the scan's actual charge roots and belong to §9 (D9.7, D9.21-D9.30): ActualRoughUpper/Lower, ActualSharpUpper/Lower/LowerPrevector/LowerRemainder/Prevector, SourceTargetSharpUpper, SourceScan (`IsSchmidtBellLabels`, label selection), SchmidtBellAugmentedPrevector, Augmented* (4 files), ActualReplicaDefect, GlobalReplicaEnergyCoordinates, TypicalReplicaAbsorption, SharpComparisonSubtraction (D9.27), TerminalEntropyGapBound, CollarComparison, Defs, Scanner, ScanTruncationInputs, StatusMarginal*, TargetTypicalWindow, SharpMomentScale, SourceStatusMarginalMoments. If §9's mapper does not claim them, they fall to the reverse pass. `Scan/Scanner.lean`, `Scan/SourceStatusMarginalMoments.lean`, `Scan/SourceTargetSharpUpper.lean` are outside the import closure.
- Also not mapped (they cite comparator labels but serve §3/§7): `OpenAI/TypicalTailScales.lean` (width n^{3/5}, Lemma 3.1 numerics) is in my infra row; `ReplicaTransportRootCompression`, `ReplicaTransportRootMetricFloor`, `ReplicaTransportSymmetricMetricFloor`, `Transport/MetricFloor` are the §7-transport/§8 interface and are in the infra row.
- Files in closure-external: `CompressedInverseFloor.lean`, `GlobalSchmidtBellRoughUpper.lean` (outside the import closure of OpenAI.AreaLaw): dead candidates (mapped to D8.32 / D8.8 so the reverse pass will not list them as unmapped, but they should be cut).
- Attribution is by whole file (file length via `wc -l`); a few files serve two anchors (TypicalDensity: D8.2 data + D8.3 bounds; ReplicaLaminarBandMetrics: D8.1 commutation + D8.6 positivity of pinned leaves; ReplicaLowDefect*/Regional*: same statement in two coordinates). Numbers are therefore ≈ per row. D8.9 and D8.25 point at §6 declarations (`TensorPower.schurSurprisal`, `groupedCopies_labelEntropy_bounds`/GroupedCopies.lean): the §6 map may also count them. D8.36 counts only the 29-line declaration `OpenAI.collarLeaf_entropy_identity`, not its file.

##### Digest/paper observations (not fixed)
- D8.36 (entropy identity, `comparator:entropy-identity`) is stated in §8 of the paper/digest, but the Lean docstring cites it as §9 eq. (9.20) (`OpenAI/CollarEntropyIdentity.lean`). Same for `abs_mutualInfo_sub_le` etc. (§9/§2).
- D8.26 Pitfall: Lean has exactly the exponent `2t = a` on the binomial (the digest's derivation), not the paper's `Ca`.
- D8.12: Lean's inverse-polynomial mass is `1/(2 (k+1)^{|E|²})` (label count `(k+1)^{q²}`), the digest says at most `(k+1)^{d_*}` labels; harmless.
- Moment-hypothesis constants differ per theorem (`6a ≤ r` in sharp upper, `20t ≤ r` = `10a ≤ r` in lower/component, rough lower `4t ≤ 1`); digest has one `a₀`, `c`, `c₀`, `𝓑`. Lean merges `C₀𝓑 → K`, `c₀/√𝓑 → r`.
- The digest's `ŵ`/`o_k(1)` upper bounds appear as `Real.bellOverlapRemainder E.card c K k` (vanishes, with explicit polynomial constant), the lower bounds as explicit-remainder statements; the limit statement is only taken in §9 and `MeanTreeSublinearRemainder`.

##### Same anchor stated several times (merge candidates)
- Rough upper (D8.20): `BellPhysicalRoughUpper` → `ReplicaPrevectorRoughUpper` (wrapper by enumeration) → `GlobalSchmidtBellRoughUpper` (dead) → `Scan/ActualRoughUpper`.
- Sharp upper (D8.22): `SchmidtBellSharpUpper` → `ReplicaPrevectorSharpUpper` → `Scan/ActualSharpUpper` (1 063 lines) → `Scan/SourceTargetSharpUpper` (dead).
- Rough lower (D8.35): `RegionalRoughLowerNorm`, `RegionalRoughLowerThree`, `GlobalSchmidtBellRoughLower`, `ReplicaLowDefectRoughLowerPin`, `RegionalLowDefectLowerPin`, `Scan/ActualRoughLower`; sharp lower likewise (`RegionalSharpLowerNorm`, `ReplicaLowDefectSharpLowerPin`, `Scan/ActualSharpLower`, `Scan/ActualSharpLowerPrevector`).
- Bell pin identity (D8.14) proved in three coordinate systems; ρ_ψ ≤ z⁻¹ρ (D8.17) three times (`TypicalPureState`, `FiniteProductTypicalState`, `CompressedTypicalRegionalMarginal`); low-defect projection (D8.23) in replica/regional/global coordinates; compression + lower pin (D8.31) three times; cutoff vector (D8.18) four times.

##### Second encodings (reverse-pass / Step 2 targets)
- Regions: `Finset V` with `FiniteProduct.entropy β Ω D`, `reducedPure`, `Configuration β X`, `splitEquiv` — a second encoding of `Reg`/`pureState`/`SubState.regionEntropy` (Arealaw). Also the site-family encodings `addedSiteSpace`, `compressedSiteSpace`, `exteriorRegion`, `regionalPhysicalRegion`, five-factor `ι : Fin 5 → Type`, `Option (Option V)` sites. Entropy: `Arealaw.vonNeumann` of `reducedPure_posSemidef` (sharp upper) vs `regionEntropy` (D8.36); the bridge sits in §9 (not mapped).
- Partial traces: `Matrix.partialTraceLeft/Right`, `traceLeft`, `partialTraceLeft_typicalPureState*`, many `partialTraceRight_*_reindex` identities (`FiniteProductTypicalState`, `TensorPowerPartialTrace`, `ReplicaGoodPairMarginal`).
- `abs_log_card_and_selectedSchmidtEntropy_sub_le` (D8.3 instance) is specialised to `Finset (ℤ × ℤ)` with `Fin q` — a lattice specialisation inside §8.

##### 𝕜 / ℂ
- Everything in §8 is ℂ-only (`Matrix … ℂ`, `EuclideanSpace ℂ`, `toEuclideanLin`) except `OpenAI.collarLeaf_entropy_identity` (D8.36, `[RCLike 𝕜]`, Arealaw encoding). No ℂ→𝕜 transfer was seen in my files; the transfer for the frozen `𝕜` statements must therefore live in §9/§10 or in `Bridges`/`ComplexWitnessTransfer`/`ComplexWitnessTransfer`-style files (not checked here).

##### Unsure
- D8.13 (d) route and D8.27 "drift" labels are based on file headers/statements and the proof outline, not a line-by-line read of the 130-300-line proofs.
- D8.28: I could not locate a declaration of the identity G^good = G_phys + F_C + F_R − D_C − D_R; I assume it is assembled inside `ReplicaGoodConfigurationExpectation.lean` / `…SharpMoment.lean` / `ReplicaComponentInverseGoodExpectation.lean` (counted under D8.29/D8.30).
- Library-tree/Mathlib replacement searches (D8.17 entropy concavity, D8.21 Jensen, D8.31 `binEntropy` counts, D8.12 iid concentration) are "search pending"; no atlas query was run.

### Notes, §09

#### s09 notes (digest/09-scanner.md)

Attribution is by whole file except four split files (OpenAI/Scan/Defs.lean at line 144; OpenAI/Geometry/TemplateCollar.lean at 229/298/338; OpenAI/Scan/TemplateTestGeometry.lean at 223/224; OpenAI/CollarEntropyIdentity.lean at 29/62/116). Split ones are listed in mapped.txt by declaration name. Section total 32 329 lines (OpenAI/Scan = 29 464 of it, all 159 files placed). Frozen Statements.lean template defs (D9.14) not counted.

##### Uncertain or judgement calls
- D9.8 (Lemma 9.1): about 7.5k lines. Status smeared (not missing): statement exists as `CollarScan.HistoryProperties` (ScanHistories.lean:520) + `eventually_historyProperties`, but nothing downstream consumes it (only Audit.lean); downstream uses the pieces. A second record `HistoryFacts` (Defs.lean:275) is proved only in ActualHistoryFacts.lean (outside the closure).
- D9.9: I counted `ScanData`/`ScanRound`/`HistoryFacts`/`ScanTruncation` records (Defs.lean 145–487), Budgets, Selection, EnergyBalance, EntropyBalance here or in D9.10–13. `Scanner.lean` (`scanner_estimate`) is outside the closure and its own docstring says it is not Prop 9.2: dead. Others of this layer (Defs, Budgets, Selection, EnergyBalance, EntropyBalance) ARE imported by the Actual* files, so they are live.
- D9.27/D9.29: `sourceScan_collar_leaf_bound` (CollarComparison.lean:158) and `exists_truncated_collar_leaf_family` (CollarInformation.lean:73) merge (a),(b) of D9.27, the D9.26 numerics and the D9.29 chain; I assigned CollarComparison to D9.27 and FinalCollarScales to D9.29.
- ActualSharpUpper/Lower/*, ActualRoughUpper/Lower, SourceTargetSharpUpper (≈3.9k lines incl. D9.12's rough upper) instantiate §8 Prop 8.1 comparisons on the Actual* round data. They could equally belong to the §8 map (D8.8 rows); the integrator should avoid double counting. ActualRoughUpper is counted in D9.12, ActualRoughLower in D9.23, ActualSharp* in D9.27.
- D9.14: no Lean lines of its own except the frozen defs; OpenAI/Geometry/TemplatePolygons.lean (56 lines, extracted from TNLean; consumers CellFans, Octants, CellFanSlopes = §11) and TwoFamilyTemplates.lean (§11) are left unmapped on purpose (reverse pass: §11 or foreign). TemplatePieceStrips.lean is also imported by §11 files (Octants, CellFans*); I attributed it to D9.16 only.
- ChargeBinomialBound (choose ≤ (e v/j)^j): Mathlib has `Nat.choose_le_pow_div` + exp bound; not verified as an exact replacement.

##### Digest vs paper / Lean oddities (digest not fixed)
- Digest D9.2 lists exponents ℓ,κ,μ,W only; Lean `ScannerExponents` also carries ν and e (Prop 9.2 data) with `kappa_le_e`. Not a disagreement.
- Digest D9.8.14 gets ratio C r₀⁵/D; Lean counts labelled anchor paths only and gets n r₀(1+r₀²)μ/M (BadHistoryGeometricTail.lean docstring). Constants only.
- Lean constants in Lemma 9.1 are explicit: 10D/m split dilution, 10μKnD split count, 40nD cuts (`HistoryProperties`), digest says C.
- Lean `bootstrapExponents` sets the scan entropy exponent e := e₀, while the hypothesis exponent is the current e ≤ e₀ (RectangleBootstrap.lean:147 takes both); the paper uses the current e in δ_n. Harmless (D9.22.1 bounds δ_n by e₀ anyway) but worth a look when restating D9.9.
- Lean applies the bootstrap at n = 8 s₀ (BoxImprovementStep.lean:81) instead of n = ⌈C₂ s₀⌉.
- Lean's template geometry (isTemplate_test_geometry) gives |T| ≤ 4n² and cuts only at j ∈ {0, L}; the paper’s Lemma 9.4 states |T| ≤ Cns₀ and |∂T_j| ≤ Cn for all j ≤ s₀ plus the prefix/partial-row clause; those general forms exist nowhere.

##### Anchors stated twice / duplicated encodings
- Lemma 9.1 twice (HistoryProperties, HistoryFacts). Q(p) twice: `ScanRound.chargeDefect` (Defs.lean:214) and `CollarScan.actualChargeEntropyDefect` (ActualEntropySampling.lean:52), bridged by `transportScanRound_chargeDefect`. Energy sum: `ScanRound.energySum`/EnergyBalance vs Actual*/TransportRoundEnergy.
- Fill transport and charge transport are two parallel constructions of `TransportData` (FillTransport/FillTransportEndpoints vs PhysicalBandCommutation/ActualChargeData).
- Covering argument twice: TemplateEntropy + CappedDyadicPartition (templates) vs RectangleShellEntropy (rectangles, own `IsIntRect.isOctagonallyConvex` and mixed-square lemma). `IsOctagonallyConvex` itself is defined in TemplateCollar.lean:52 and re-derived for rectangles.
- Safe-box entropy transfers: PositivePrefixEntropyTransfer (outside closure) vs ScanTruncationInputs.

##### Second encodings of regions / entropy (vs Arealaw `Reg`, `pureState`, `SubState.regionEntropy`, `mutualInfo`)
- `FiniteProduct.entropy`, `FiniteProduct.reducedPure`, `FiniteProduct.Configuration β Xs` appear in the hypotheses of `exists_sourceScan_selection` (ScannerSelection.lean:46), `sourceScan_bootstrap_entropy_le`, `isSafe_regionEntropy_le_of_boxEntropy_le`; bridge theorems `OpenAI.reducedState_eq_finiteProduct`, `regionalEntropy_eq_finiteProduct` (DomainFiniteProduct.lean), `finiteProduct_entropy_eq_regionEntropy` (BoxImprovementStep.lean), `regionEntropy_eq_finiteProduct_of_map_eq` (CollarInformation.lean:45), `surprisalMoment_restrict_pureState_eq_finiteProduct` (ActualSharpUpper.lean), `surprisalTail_restrict_pureState_eq_finiteProduct` (TargetTypicalWindow.lean). All scaffold once one encoding is chosen.
- Regions as `Finset (ℤ × ℤ)` subsets of Λ coerced to `↥(Λ : Set (ℤ×ℤ))` (scan side) vs `Finset (ℤ × ℤ)` (statement side): `map_subtype_subset`, `map_subtype_compl`, `map_embeddingSubtype_compl` and `Scan.map_embeddingSubtype_subset` bridges (ScanHistories.lean:240/247, CollarInformation.lean:56). Augmented sites have two descriptions (Option vs Sum): the three *Coordinates files (infra row).
- Truncated pure state is an `EuclideanSpace ℂ` vector in the scan theorems and a `Reg → ℂ` function in the statement-side theorems (`pureState Ωt.ofLp ...`): conversions `star_dotProduct_self_eq_one_of_norm_eq_one` everywhere.

##### 𝕜 / ℂ
- Entire scan chain (D9.3–D9.13, D9.19–D9.24, D9.26, D9.27) is ℂ-only; the top transfer for Prop 9.6 is the single `collarInformationBound` (CollarInformation.lean:439), via `toComplex` map lemmas. Prop 9.5 `improved_box_estimate` is ℂ-only and feeds `InitialBoxEstimate` machinery with `𝕜 := ℂ`.
- Piecewise 𝕜-generic pieces that the ℂ choice makes unnecessary: TemplateEntropy.lean (`templateEntropy_le_of_boxEntropy_le`, 𝕜), RectangleShellEntropy.lean (`isSafe_shell_regionEntropy_le`, 𝕜), MarginalTailsBridge.lean (𝕜), CollarEntropyIdentity.lean (𝕜 for the identity and `abs_mutualInfo_sub_le`), CollarReduction.lean (𝕜), WeakRectangleShellSafety/SafeRectangleDilation (scalar-free).

##### Out-of-closure files in my section (dead candidates, confirm by name search)
Scan: BandCountGrowth, ActualRoundParameterIntegral, RoundedClearance (live? listed outside closure), TransportRoundParameterIntegral, SourceStatusMarginalMoments, SourceTargetSharpUpper, RoundedScalePower, OriginalTruncation, PositivePrefixEntropyTransfer, ActualChargeParameterBound, Scanner, AugmentedReceivingRegions, ActualHistoryFacts. (closure.json is the authority; note SourceTargetSharpUpper/SourceStatusMarginalMoments being outside is surprising since their topic is used on the main path: likely superseded by StatusMarginalMoments/ActualSharp* versions — worth a check.)

##### Foreign provenance
Many headers cite `TNLean/PEPS/AreaLaw/...` (Apache 2.0) ports: ActualHistoryFacts, TemplatePolygons, QuotientIntervals and others. Those carrying an anchor are mapped; TemplatePolygons is not.

### Notes, §10

#### Notes for the integrator, digest/10-amplification.md

Anchors: D10.1–D10.17 (17 headings; D10.2.1–13 etc. are bullets, not anchors, so all of Lemma 10.1's code sits in the D10.2 row, 4177 lines).

##### Attribution choices (rough where marked)
- Files serving several anchors are split by line span (`mapped.txt` lists the declarations per span): LatticeRestoring (D10.6/8/9), RestoringVectors (D10.7/9), GoodRealization (D10.11/12), GoodRealizationUnitary (D10.13/14), SupportedPolarCorrection (D10.14/15), AmplificationProofSteps (D10.14/15), AmplificationCutClearance (D10.4/16). Span boundaries are by declaration, ≈.
- `(section infra)` = the 11 Poisson-word measure-theory files (1568 lines), importers are only Amplification files, so they are on no other section's path.
- Not counted here, used by this section, probably belong to other digest rows: `OpenAI/Scan/DomainFiniteProduct`, `FiniteProductEntropy/Continuity/Channel/Information` (FiniteProductInformation is also imported by `Scan/RegionalMoveEntropy`), `TypicalDensity`, `RootChannel`, `SiteExpectationOrder`, `LatticeConstraints`/`SpectralFilter/*` (D4.6 positive system, `kernelExponent`), `EntropyContinuity` (Lemma 2.1), `RegionLift`, `MatrixKroneckerContraction`, `Embedding` (`toComplex`).
- `OpenAI/AuditAmplification.lean` excluded (audit script).

##### Unsure / flags
- D10.1: no declaration exists; marked `missing` (not `none`) because it is a Def whose content (ε, β, α numerals, p ≥ 10^6) is spread as literals. ε = `1/100000` and β = `2/1000000` are repeated in Statements.lean:355 (frozen) and AmplificationCutClearance.lean, AmplificationProof.lean, RadiusBound hypotheses; the refactor must name them once outside the frozen file.
- D10.4: classified `drift` because of `K = 4(M+2)` vs the paper's `K ≥ 4(M+3)` (Lean's constants 9 n^{−K/2}, n^{2−K/4} = n^{−M}) and the missing `X = ∅` case; otherwise the 329-line proof follows the skeleton D10.4.2–10 in order. Could equally be called `faithful`.
- D10.14 is `drift` only in packaging (same expansiveness of `1+P`).
- D10.3, D10.2 (propagation, coupling) differ from the digest in route: the paper integrates a differential inequality along the Poisson clocks (Gronwall / Campbell); Lean sums over words of length m and uses the Poisson series. Same estimate, different technique. Both are generic over `[Fintype ι]` index sets and over matrices.

##### Statements stated twice
- Lemma 10.1: abstract domain versions (`exists_domainConstraintWord_truncation`, `…_omission`) and lattice versions (`exists_latticeConstraintWord_truncation`, `…_omission`); the lattice ones only instantiate the abstract ones with Prop 4.3's constraints.
- Prop 10.2: frozen `Amplification` (Statements.lean) and `AmplificationOutput` (CutClearance:186, the same minus the clearance clause).
- D10.3: generic `Matrix.poissonContractionWord_excitedProjection_decay` and `latticeConstraintWord_excitedProjection_decay`.
- `sqrt_rpow_neg_two_mul` (Amp/LatticeRestoring.lean:712) and `sqrt_rpow_neg_two_mul'` (AmplificationProof.lean:112).
- Restoring estimates: proved on the original coordinates (`restoringOperator_estimates`, LatticeRestoring:663) and again after transport (`restoringTransport_estimates`, LatticeAncillaTransport:323, 172 lines).

##### Second encodings / bridges (scaffold candidates)
- The whole section is proved on the `FiniteProduct` encoding (`Configuration (fun _ : ↥Λ => Fin q)`, `FiniteProduct.mutualInformation/entropy/reducedPure`) rather than Arealaw's `Reg`/`pureState`/`SubState.mutualInfo`; the only bridge is `OpenAI.mutualInfo_pureState_eq_finiteProduct` (AmplificationProof.lean:87), used for the hypothesis and conclusion. Regions are `Finset ↥(Λ : Set (ℤ×ℤ))` (subtype of sites) inside the proof, `Finset (ℤ×ℤ)` in the statement; `Finset.subtype`/`map` conversions (`hXmap`, `hS₀map`, `hcompl`) fill ≈ 40 lines of the main proof.
- The ancilla copies s', e' are a third encoding: `AncillaSites Λ X` (disjoint sum of sites, LatticeAncillaSites.lean:131), `ancillaSplit`, `restoringSplit`, `RegionalConfiguration`, plus `Entropy.restoringCoordinates` of the generic restoring algebra. Entropy/mutual-information invariance under these relabellings (`FiniteProduct.relabelSites`, `sumSitesProduct`, AncillaSiteEntropy.lean) is scaffolding for the paper's "append s', e'".
- ℂ vs 𝕜: everything inside is ℂ-only (`EuclideanSpace ℂ`, `toEuclideanLin`, `CFC.sqrt` over `ℂ`); the single transfer is `amplificationOutput` (Amplification.lean:28) through `toComplex` (`hamiltonian_map_toComplex`, `hasGlobalGap_map_toComplex_iff`, `SubState.mutualInfo_toComplex`, `pureState_toComplex`, in other files). This already matches the plan's decision; no piecewise transfers found in this section.

##### Digest vs paper / digest vs Lean
- Digest D10.11 asks `C ≥ max{6/g, 2}` and uses `log M₀ ≤ t*`; Lean uses `C = 6/g` and absorbs `M₀` through the `g/2` summand in `C'`. Digest consistent with paper; flagged only as a constant difference.
- Digest D10.12.1 expects `M₀² e^{−g t*} ≤ n^{−6K}`; Lean proves exactly this (`amplification_scale_bounds`, first conjunct).
- No contradiction found between digest and paper.

##### Dead/foreign candidates seen
- `Exponents.collar_add_radius_isLittleO` (CutClearance:137, 0 references), `domainDistanceProfile_empty`, `…_eq_zero_of_*` variants with 0 references in the files listed (see decls.tsv refcount 0): `Amp/ComponentChannelOscillation` has 4 declarations with refcount 0; `Amp/ChannelWordObservables.siteOscillation_spectatorRootChannelWord_bounds` and `…append_sub_le_graphChannelEventKernel` refcount 0; `Amp/ChannelWordOmission.norm_spectatorRootChannelWord_sub_le`, `Amp/ChannelWordThinning.integrable_and_integral_siteOscillation_filter_le`, `Amp/LocalChannelOscillation.localRootChannelShellBound_zero/_succ`: candidates for the reverse pass (inline/cut), not confirmed by name search beyond refcount.
- Headers of PolarUnitaryCorrection*.lean cite a "Polynomial-PEPS" paper (`info-reset-polar-errors`) alongside Area-law §9; the code is generic and used only by D10.14, so kept in the D10.14 row, not `foreign`. Files `Amp/ConstraintWordTruncation.lean`, `AmplificationProof.lean`, `PolarUnitaryCorrectionKronecker.lean` have provenance headers (TNLean/QICLean "ported") to delete in Step 2.

### Notes, §11

#### Notes for s11 (digest/11-geometry.md)

Counts (26 anchors): faithful 14 (D11.1, 2, 4, 5, 7, 8, 9, 12, 17, 20, 23, 24, 25, 26), drift 2 (D11.3, D11.18), smeared 10 (D11.6, 10, 11, 13, 14, 15, 16, 19, 21, 22), missing 0, overbuilt 0, none 0. The (section infra) row has Status `none`. The "89 files" figure under Provenance counts files with a port header.

##### Scope decisions the integrator must know
- `OpenAI/Geometry/` is not all §11. Six files are §9 (Def 9.3 / Lemma 9.4 / eq. (9.11)) and I did NOT map them: `CappedDyadicPartition` (356, Lemma 9.4, used by `WeakRectangleShellSafety`), `TemplateCollar` (512, Lemma 9.4 + last sentence of Prop 9.6, used by `CollarReduction`, `Scan/*`), `TemplateMixedSquares` (321, eq. (9.11), used by `TemplateEntropy`), `TemplatePieceStrips` (315, Def 9.3), `QuotientIntervals` (45), `DyadicWeightedSum` (58). They sit in the §11 directory but belong to the §9 digest's map.
- Seventeen Geometry files are outside the import closure of `OpenAI.AreaLaw` (2 620 lines) and are in no row, not in mapped.txt: `CellFanRadialIncidence, CellFanRays, FanAffineCoordinates, FanInactiveSeams, FanRadialConvexity, FanRadialPieces, FanRunComponents, FanRunConnectedness, FanRunDisjointness, InitialActiveRayCount, InitialActiveRays, InitialComponentRegions, InitialSectorComponents, InitialSectorCycle, InitialSectorRuns, MeshSegmentClearance, SegmentBallClipping`. Candidates `dead`.
- Outside `OpenAI/Geometry/`, rows also use `OpenAI/TwoFamily.lean`, `OpenAI/TwoFamilyDecomposition.lean`, `OpenAI/AreaLaw.lean` (two decls; `area_law_corollary` is D1.7), `OpenAI/GraphNeighborhoodCutClearance.lean` (D11.26.3; but `OpenAI/AmplificationCutClearance.lean:164 exists_threshold_graphNeighborhood_collar_subset` also imports it, so §10's mapper may want to cite it). `OpenAI.Exponents.exists_collar_radius_threshold` (AmplificationCutClearance.lean:115) supplies D11.26.2's `L + 2r < n^β` and is left to the §10 map. Of `OpenAI/OrderedEntropyAlgebra.lean` I mapped only the four unused decls to D11.1; `past`, `defect`, `sum_defect` (used by `FiniteProductConditional`) are unmapped here.
- mapped.txt has overlap that is intentional: files `DistanceLayers.lean` (D11.6) and `RepairDepth.lean` (D11.19) are listed whole, while `dyadicLayer_dist_nonadjacent`, `dyadicLayer_dist_separation` (D11.7) and `eventually_fine_clearance` (D11.24) are listed under their own anchors; the line counts already exclude them from the file rows.

##### Places where the digest and Lean differ in route (no digest edits proposed)
- D11.3: closed vs open removal squares (Lean deletes open sup-balls, so birth/final regions are closed; equivalent on lattice points only).
- D11.5: `C₀` in Lean is `≥ 2` and `≥ 4D₀+2`; digest says `> 100(D₀+1)` (and notes only `≥ 2`, `> 4D₀` are needed). Not a conflict.
- D11.11: label choice on a shared belt side is a lexicographic cell key (`BeltFanColors.lean:42`), digest says "any opposite pair".
- D11.13: `a₀ = 1/64` is a literal; the digest picks `a₀` small abstractly. Mark separation in Lean is `max(scale)/4` (stronger than `a₀ max`). Also `k₀ ≥ 5·10⁷` and `10⁷·d` appear as unnamed numerals (78 occurrences of `50000000` in Geometry/TFD) where the paper says "k₀ large".
- D11.18: two lemmas (belt, replacement) with explicit constants (`r₀ ≤ t/4096`, `d(u)/2`), no compactness, vs one lemma with `c₁ u^{ρ₀}` in the paper. `c₁` never appears; `clearance`/`TileSpec` use `d(u/2)/2` directly, so D11.24's `c₁u^{ρ₀} > 2⌈C_B u⌉^β` is `eventually_fine_clearance` plus the explicit comparison inside `exists_twoFamily_constants`.
- D11.26: Lean never treats `Λ = ∅`, `A ∈ {∅, Λ}`, `q = 1`, `R = 0` as separate cases: all reduce to `b = 0` via Lemma 2.2 or are covered by the general estimate. `Ctpl` is existentially produced by `collar_bound`, not a fixed input.

##### Statements stated twice
- D11.4 / D11.25: `two_family_decomposition` and `TwoFamilyAssembly.Data.decomposition` (same conclusion).
- D11.24: `exists_twoFamily_constants` (G/TwoFamilyScales.lean:228) and structure `TwoFamilyAssembly.Consts` (TFD:144) restate the same inequalities.
- D11.1: `TwoFamilyCancellation` is also proved algebraically for set functions in `OrderedEntropyAlgebra.two_family_le_half_sum[_defect]` (unused).
- D11.14: removal rule is encoded twice: `repairSquare`/`repairRemovalSet`/`simultaneousRepairRemnants` (SimultaneousRepair.lean:122–143, unused) and `finalRegion` (RepairRegions.lean:98).
- D11.10: primaries described both as rectangular fragments (`PrimaryFragments`) and as unions of non-belt fine cells (`PrimaryFineCellCover`, `NonbeltPrimaries`).

##### Second encodings of regions / entropy / scalars
- Nothing in §11 duplicates `Reg`, `pureState`, `SubState.regionEntropy`, `mutualInfo`: `TwoFamily.lean` uses them directly (`pureState ψ hψ`, `.mutualInfo`, `.regionEntropy`). The only entropy-like second encoding is `OrderedEntropyAlgebra` (arbitrary `Finset V → ℝ` set function, `entropy β ψ` in `FiniteProductConditional`) — outside this section's rows.
- Planar vs lattice: geometry lives in `ℝ × ℝ` with `integerPoint : ℤ×ℤ → ℝ×ℝ` and is bridged to the frozen `ambientEDist` (`ℤ×ℤ`, `ℕ∞`) by `AmbientDistanceBridge` and `ofReal_lt_ambientEDist_of_le_dist` (TFD:60); these casts are scaffold. Exponents are `ℚ` (`Exponents.*`) cast to `ℝ` everywhere.
- 𝕜/ℂ: only D11.1 and D11.26 touch scalars. `two_family_cancellation` is native over 𝕜 except subadditivity, transferred through `OpenAI.Embedding` (TwoFamily.lean docstring). The geometry (D11.2–D11.25) is scalar-free. If the refactor develops over ℂ, D11.1's transfer is the one place that matters.

##### Anchors I was unsure about
- D11.11 and D11.13: no declaration states them; status `smeared` rests on `initialRegionColor_ne_of_segment_subset_inter` (interfaces only) and `initialRepairSetup_latticeHyp` (a structure `LatticeHyp`, not a theorem). Files assigned between these two (e.g. `InitialRegionInteriors`, `InitialRegionRegularity`, `FanFrontiers`, `ConcentricFans`, `CellFanSectors`) are judgement calls; moving any of them changes only the split of line counts, not the total.
- D11.12/D11.13: `InitialMarkFamily.lean` (232) contains parts of D11.12 (scales), D11.13(1) (separation) and D11.19.4 (finite support); it is attributed whole to D11.12.
- D11.15 file attribution: `Octants.lean` (624) is shared with D11.18; attributed to D11.15. `RepairTree.lean` contains the `RepairSetup` structure (the repair data) that D11.14 also uses.
- D11.21/22/23 line spans for decls come from decls.tsv (docstring-to-next-decl), so ±10 lines.
- Standard? items: Mathlib searches were not run (search pending) for D11.5, 6, 7, 10, 16, 19; D11.9 already uses Mathlib's pigeonhole and D11.1's chain rule/subadditivity/purity already exist in `Arealaw`.

##### Dead declarations inside mapped files (refcount 0 in decls.tsv)
`fineScale_side_succ`, `ofReal_lt_ambientEDist_of_subset_dyadicLayer`, `ofReal_lt_ambientEDist_of_nonadjacent_dyadicLayers`, `exists_sparse_dyadic_belt_marks_shift`, `dyadicLayer_infDist_bounds`, `iUnion_dyadicNeighborhood_eq_univ`, `card_fineLayerIndices_le`, `fineScale_dvd_layerScale`, `layerScale_dvd_pitchScale`, `elementarySideOpponent_reciprocal_iff`, `coe_finRotate_mod`, `Fin.forall_sub_one_iff`, `Fin.finRotate_succ_castSucc`, `dyadicNeighborhood_union_iUnion_fineCells_eq_univ`, `initialOpenRegion_frontier_avoid_lattice`, `dyadicNeighborhood_union_iUnion_layers_eq_univ`, `iUnion_octantCone`, `mem_octantConeAt_lineMap`, `primaryFragment_diam_le`, `primaryBirthRegion_diam_le`, `RepairMark.gen_descend`, `exists_dyadicScale_side_ratios`, `eventually_repairHalfSide_margins`, `simultaneousRepairRemnants`, `repairChildLocation`, `repairChildScale`.

##### Provenance
89 of the Geometry/OrderedEntropyAlgebra/GraphNeighborhoodCutClearance files carry "Ported from / Adapted from LionSR/TNLean (or QICLean)" headers. They are anchored to §11 so I treated them as not `foreign`, but the integrator may want to delete these headers (Step 2).

## Appendix B: Mathlib/Physlib searches of the reverse pass

# Searches (reverse pass)

Tool: `atlas_search` (semantic unless noted) over corpora `mathlib` + `physlib` pinned to `v4_33_0`; Physlib hits under module `QuantumInfo.*` are the Lean-QuantumInfo part of Physlib (the project already imports `QuantumInfo.ForMathlib.Matrix`, `QuantumInfo.Channels.Dual`, ...). "glob" = `atlas_search mode=glob` (dotted-name match, needs the exact namespace prefix, so empty results there mean "not under that name", not "absent"). `loogle_search` was tried once and failed on the notation query.

| what was needed | queries tried | result |
|---|---|---|
| trace norm of conjTranspose (Fidelity.traceNorm_conjTranspose*) | "trace norm of a matrix equals tr √(A*A), invariant under conjugate transpose" | FOUND `Matrix.traceNorm_conjTranspose` (Physlib QuantumInfo.ForMathlib.MatrixNorm.TraceNorm), ℂ only; also `traceNorm_unitary_conj`, `traceNorm_isometry_left/right`, `traceNorm_mul_le_traceNorm_opNorm` |
| trace norm via blocks / ≤ bounds (fromBlocks, re_trace_le_traceNorm, norm_trace_le_traceNorm) | globs `Matrix.trace_fromBlocks`, `posSemidef_fromBlocks`, `traceNorm_fromBlocks`, `norm_trace_le_traceNorm` | NOT FOUND under those names; Physlib proves trace-norm facts through SVD (`Matrix.exists_svd_sqrt_eigenvalues`) instead of block trick -> library tree |
| ‖A⊗B‖ = ‖A‖‖B‖ / ≤ (OpNorm.l2_opNorm_kronecker_le, MatrixKroneckerContraction) | "operator norm of Kronecker product is product of norms"; glob `l2_opNorm_kronecker`; loogle `‖_ ⊗ₖ _‖` (parse error) | NOT FOUND (only `Matrix.l2_opNorm_mul`, `TensorProduct.norm_tmul`) -> library tree Analysis/CStarAlgebra/Matrix |
| l2 operator norm invariant under reindex/submatrix by equiv | "l2 operator norm unchanged by reindexing rows and columns by equivalences"; glob `opNorm_reindex` | PARTIAL: `Matrix.permMatrix_l2_opNorm_le` (Mathlib, permutation matrices), `Matrix.opNorm_reindex_proven` (Physlib, but about Physlib's own `Matrix.opNorm`, not Mathlib's l2 norm) -> library tree |
| ‖V‖ ≤ 1 for isometry | "matrix with V*V=1 is an isometry, operator norm ≤ 1" | PARTIAL: `Matrix.opNorm_isometry`, `isometry_mul_conjTranspose_le_one` (Physlib QuantumInfo.Entropy.SSA, Physlib's `Matrix.opNorm`) -> library tree |
| cfc and unitary conjugation (CfcConjugation.rpow_conj_unitary) | "cfc of Hermitian matrix commutes with conjugation by a unitary" | FOUND `Matrix.cfc_conj_unitary`, `Matrix.cfc_conj_unitary'` (Physlib QuantumInfo.ForMathlib.Isometry), `HermitianMat.cfc_conj_unitary` |
| cfc and reindexing (CfcConjugation.cfc_submatrix_equiv) | glob `Matrix.cfc_reindex` | FOUND `Matrix.cfc_reindex` (Physlib QuantumInfo.ForMathlib.Isometry), `HermitianMat.cfc_reindex` |
| cfc under a star-algebra hom (CfcKronecker, CfcComplex, SpectralKronecker) | "cfc commutes with a star algebra homomorphism"; "Kronecker with identity is a star algebra hom"; "reindexing is a star algebra equivalence preserving cfc" | FOUND `StarAlgHom.map_cfc` / `StarAlgHomClass.map_cfc` (Mathlib CFC/Unique); `Matrix.kroneckerStarAlgEquiv` (Mathlib RingTheory/MatrixAlgebra); NOT FOUND: a ready star-hom `A ↦ A ⊗ 1` (glob `kroneckerStarAlgHom` empty), star version of `Matrix.reindexAlgEquiv` (only `CStarMatrix.reindexₐ`) |
| ℂ-valued functional calculus (CfcComplex.cfcC, SpectralFun) | semantic queries above; Mathlib `cfc` works for ℂ-valued f on `IsStarNormal` elements | FOUND route: `cfc_mul`, `cfc_star` (Mathlib CFC Unital); not type-checked that `g ∘ re` restriction closes the cfcC statements |
| cfc transpose (CfcTranspose) | "transpose of Hermitian matrix equals entrywise conjugate; cfc commutes with transpose" | NOT FOUND (only `Matrix.isHermitian_transpose_iff`, `IsHermitian.transpose`) -> library tree |
| spectral theorem (HermitianCfcSpectral.spectral_form/cfc_form) | "A = U diag(eigenvalues) U*" | FOUND `Matrix.IsHermitian.spectral_theorem` (Mathlib Analysis/Matrix/Spectrum), `Matrix.IsHermitian.cfc_eq` (used by the project already) |
| trace of cfc = Σ f(eigenvalues) | "trace of a function of a Hermitian matrix equals sum over eigenvalues" | FOUND `HermitianMat.trace_cfc_eq` (Physlib), `Matrix.IsHermitian.trace_eq_sum_eigenvalues` (Mathlib) |
| tr(PSD·PSD) ≥ 0 (Fidelity.re_trace_mul_nonneg) | "trace of product of PSD with Hermitian bounded by ..." | FOUND `Matrix.PosSemidef.trace_mul_nonneg` (Physlib QuantumInfo.Channels.Dual) |
| support projection (PosSemidefSupport, MatrixSqrt supportInv*) | "support projection of a PSD matrix is the orthogonal projection onto its range"; glob `Matrix.PosSemidef.supportProj` | PARTIAL: `HermitianMat.supportProj`, `supportProj_mul_self`, `supportProj_ker`, `kerProj_add_supportProj` (Physlib, HermitianMat wrapper, not Matrix); no Matrix-level `supportProj`/`supportInv` -> library tree Mathlib LinearAlgebra/Matrix/PosDef |
| √(A⊗B), support inverse sqrt | "square root of Kronecker product of PSD matrices" | NOT FOUND (only `Matrix.PosSemidef.kronecker`, `HermitianMat.sqrt_sq`) -> library tree |
| rpow of PosDef matrices (MatrixPowers) | "PosDef matrix raised to real power r is PosDef, rpow_add rpow_zero rpow_one" | FOUND Mathlib CFC API (`CFC.rpow_add`, `CFC.rpow_zero`, `CFC.rpow_one`, `IsStrictlyPositive.rpow`); the project's `Matrix.PosDef.*` restatements add nothing |
| inverse order (PosDefInverseOrder) | "A ≤ B PosDef ⇒ B⁻¹ ≤ A⁻¹" | FOUND `HermitianMat.inv_antitone` (Physlib QuantumInfo.ForMathlib.HermitianMat.LogExp), HermitianMat form |
| Neumann / perturbation of inverse (NeumannInverse) | "inverse of 1 - t has norm ≤ 1/(1-a)"; "K invertible, K' close to K ⇒ invertible, inverse norm bounded" | PARTIAL: `NormedRing.inverse_one_sub`, `Units.oneSub`, `Units.ofNearby`, `NormedRing.inverse_add_norm` (Mathlib Analysis/Normed/Ring/Units) give invertibility, not the explicit norm bounds -> library tree |
| partial trace of Kronecker (TraceDistance, TraceRight*) | "partial trace of A ⊗ B = tr(B)·A" | PARTIAL: `HermitianMat.traceRight_kron`, `Matrix.trace_mul_kron_one_right`, `Matrix.trace_mul_one_kron_right` (Physlib) |
| exp of Kronecker (KroneckerExponential, GaussianFilterReindex) | "exp(X⊗1)=exp X⊗1"; glob `exp_kronecker` | NOT FOUND as such; route via `NormedSpace.map_exp` for a continuous algebra hom (name from memory, not found by search); `Matrix.exp_add_of_commute` FOUND |
| isometry API (MatrixUnitaryBetween) | "V*V=1 isometry; isometry iff conjTranspose coisometry"; globs `IsCoisometry`, `Matrix.Isometry.kronecker`, `Matrix.Isometry.mul` | PARTIAL: `Matrix.Isometry` (Physlib QuantumInfo.ForMathlib.Isometry) exists; `IsCoisometry`/`IsUnitaryBetween` NOT FOUND -> library tree |
| polar / Gram unitary (MatrixGramUnitary) | "V*V=W*W ⇒ W=UV" | NOT FOUND -> library tree |
| IsStarProjection (OrthogonalProjection) | "P*=P and PP=P" | FOUND `isStarProjection_iff'` (Mathlib Algebra/Star/StarProjection) |
| orthogonal resolution of identity (OrthogonalResolution) | "pairwise orthogonal projections summing to one" | PARTIAL: `CompleteOrthogonalIdempotents`, `OrthogonalIdempotents` (Mathlib, ring-level); no Hermitian spectral-projection API -> library tree |
| idempotent Hermitian: eigenvalues 0/1, rank = trace | "Hermitian idempotent has eigenvalues 0 or 1 and rank equals trace" | NOT FOUND (only `Matrix.IsHermitian.rank_eq_rank_diagonal`) |
| PSD ⇒ nonzero Kronecker factors (KroneckerFactorPositivity) | not searched separately | no hit expected; library tree |
| Schmidt rank (SchmidtRank) | "Schmidt rank equals rank of coefficient matrix" | NOT FOUND (only `Matrix.rank_vecMulVec_le`, `MState.Ket.IsProd_iff_rank_eq_one`) -> library tree LinearAlgebra/Matrix/Rank |
| von Neumann entropy facts (EntropyContinuity, ProductMarginals, FiniteProductEntropy) | "von Neumann entropy continuous"; "S = -tr ρ log ρ"; "entropies of a pure state's marginals coincide" | FOUND `Sᵥₙ_continuous`, `Sᵥₙ_eq_neg_trace_log`, `Sᵥₙ_eq_trace_cfc_negMulLog`, `Sᵥₙ_of_partial_eq`, `Sᵥₙ_pure_tripartite_triangle` (Physlib QuantumInfo.Entropy.VonNeumann/SSA), all stated for `MState`/`Ket`, i.e. a third encoding |
| relative entropy / Klein (RootFidelityRelativeEntropy, KleinInequality) | "relative entropy nonneg (Klein) via spectral decomposition"; "relative entropy = tr ρ(log ρ - log σ)" | FOUND `inner_log_sub_log_nonneg`, `qRelativeEnt`, `qRelativeEnt_rank`, `qRelativeEnt_eq_neg_Sᵥₙ_add` (Physlib QuantumInfo.Entropy.Relative), MState encoding |
| SSA / submodularity (FiniteProductInformation) | via entropy queries | FOUND module `QuantumInfo.Entropy.SSA` (`Sᵥₙ_pure_tripartite_triangle`; SSA statement itself not name-checked) |
| fidelity (Fidelity.fidelity) | glob `Matrix.fidelity` | NOT FOUND as Matrix-level; Physlib has `QuantumInfo/States/Mixed/Fidelity` for `MState` (imported by the project) |
| graph distance / walks (Bridges.exists_walk_length_le_iff_edist_le) | "walk of given length"; globs `SimpleGraph.edist_le`, `exists_walk_of_edist` | FOUND `SimpleGraph.edist_le`, `SimpleGraph.exists_walk_of_edist_ne_top`, `exists_walk_of_edist_eq_coe` (Mathlib Combinatorics/SimpleGraph/Metric) |
| ceiling scaling (CeilScaling) | "x ≤ A s, s ≥ 1 ⇒ ⌈x⌉ ≤ (A+1) s" | NOT FOUND (only `Nat.ceil_le_mul` with hypotheses on b, a) -> library tree Algebra/Order/Floor |
| big-O log envelope (LogarithmicEnvelope) | "big O of n bounded by C log(n+2)" | NOT FOUND (only `IsBigO.of_abs_right`-type API) |
| rectangle contour integral with simple poles (RectangleSimplePoles) | "∮ of 1/(z-p) over rectangle = 2πi" | NOT FOUND for rectangles (only `circleIntegral.integral_sub_inv_of_mem_ball`); Mathlib has the zero-integral rectangle theorem -> library tree Analysis/Complex/CauchyIntegral |
| interleavings of two lists (TaggedInterleavings) | "all ways of merging two lists preserving order" | NOT FOUND (only `List.sublists`, `permutations` API) |
| Weyl twirl / unitary 1-design (WeylTwirl, SiteWeylAverage) | "clock and shift matrices twirl gives trace times identity" | NOT FOUND for Weyl operators (only `twirling_average_eq` in Physlib QuantumInfo.Entropy.DPI, a general twirl for a unitary family satisfying a design hypothesis) |
| finite-sum reindexing (FinSum) | "finite sum over Pi/Sigma type reindexed by equivalence" | PARTIAL: `Equiv.sum_comp`, `Fintype.sum_equiv`; the Sigma/castLE/fiber lemmas not found |
| trace-pairing adjoint map (MatrixTracePairing) | not found by name in semantic queries; Physlib has `MatrixMap.dual` (module QuantumInfo.Channels.Dual, imported by project, name not search-verified) | PARTIAL/UNVERIFIED |

## Appendix C: declarations in rows that are unreachable from the frozen proofs

| File | Declarations |
|---|---|
| Arealaw/Bridge/Entropy.lean | 1 |
| Arealaw/Bridge/MState.lean | 7 |
| Arealaw/Bridge/VonNeumann.lean | 3 |
| Arealaw/Entropy.lean | 1 |
| Arealaw/Mixed.lean | 12 |
| Arealaw/PTrace.lean | 18 |
| Arealaw/Region.lean | 16 |
| Arealaw/State.lean | 8 |
| Arealaw/Subadditivity.lean | 7 |
| Arealaw/TraceDist.lean | 4 |
| Arealaw/TraceNorm.lean | 6 |
| OpenAI/AddedSiteSpace.lean | 2 |
| OpenAI/AddedSiteTensorInsertionSymmetry.lean | 2 |
| OpenAI/Amplification/ChannelWordObservables.lean | 2 |
| OpenAI/Amplification/ChannelWordOmission.lean | 2 |
| OpenAI/Amplification/ChannelWordThinning.lean | 3 |
| OpenAI/Amplification/ComponentChannelOscillation.lean | 5 |
| OpenAI/Amplification/ConstraintWordTruncation.lean | 1 |
| OpenAI/Amplification/GraphOmittedAnchorTail.lean | 3 |
| OpenAI/Amplification/LatticeAncillaSites.lean | 2 |
| OpenAI/Amplification/LatticeExcitedDecay.lean | 1 |
| OpenAI/Amplification/LatticeRestoring.lean | 4 |
| OpenAI/Amplification/LocalChannelOscillation.lean | 2 |
| OpenAI/Amplification/SupportedPolarCorrection.lean | 1 |
| OpenAI/AmplificationCutClearance.lean | 2 |
| OpenAI/Basic.lean | 11 |
| OpenAI/BellInsertionRegisterCoordinates.lean | 1 |
| OpenAI/BellPinnedTreeAction.lean | 1 |
| OpenAI/BlockDiagonal.lean | 1 |
| OpenAI/BranchingPieri.lean | 2 |
| OpenAI/BufferedRectangles.lean | 2 |
| OpenAI/CoherentSymbol.lean | 2 |
| OpenAI/CommutantDimension.lean | 1 |
| OpenAI/CompatiblePhysicalLabel.lean | 1 |
| OpenAI/ComplexWitnessTransfer.lean | 2 |
| OpenAI/CompressedInverseFloor.lean | 1 |
| OpenAI/CompressedSiteCoordinates.lean | 2 |
| OpenAI/ConditionalEntropy.lean | 3 |
| OpenAI/ConditionalExpectation.lean | 5 |
| OpenAI/ConditionalMovement/BoundaryEnergy.lean | 1 |
| OpenAI/ConditionalMovement/EntropyBounds.lean | 1 |
| OpenAI/ConditionalMovement/EntropyHolder.lean | 3 |
| OpenAI/ConditionalMovement/NormalizedRows.lean | 1 |
| OpenAI/ConditionalMovement/PartialTrace.lean | 1 |
| OpenAI/ConditionalMovement/PhaseContinuity.lean | 2 |
| OpenAI/ConditionalMovement/PhaseTransfer.lean | 1 |
| OpenAI/ConditionalMovement/Purification.lean | 1 |
| OpenAI/ConditionalMovement/RenyiSlack.lean | 1 |
| OpenAI/ConditionalMovementEstimate.lean | 1 |
| OpenAI/ConditionalSkewSupport.lean | 2 |
| OpenAI/ContractionWordDecay.lean | 1 |
| OpenAI/ContractionWordDecaySpectator.lean | 5 |
| OpenAI/Corollary.lean | 1 |
| OpenAI/Embedding.lean | 12 |
| OpenAI/ExponentialDistanceProfile.lean | 1 |
| OpenAI/ExteriorPieri.lean | 1 |
| OpenAI/FilterChainEnergy.lean | 2 |
| OpenAI/FilterClipping.lean | 1 |
| OpenAI/FilterEnergy.lean | 1 |
| OpenAI/FilterMoment.lean | 1 |
| OpenAI/FilterPower.lean | 1 |
| OpenAI/FilterStationarity.lean | 5 |
| OpenAI/FiniteMeanTree.lean | 4 |
| OpenAI/FiniteProductTypicalState.lean | 2 |
| OpenAI/FiniteSetTruncationOfGap.lean | 1 |
| OpenAI/FiveFactorAuxiliaryCoordinates.lean | 1 |
| OpenAI/GapPerturbation.lean | 1 |
| OpenAI/GeometricMeanDerivativeIntertwine.lean | 4 |
| OpenAI/Geometry/AdjacentScales.lean | 1 |
| OpenAI/Geometry/AmbientDistanceBridge.lean | 2 |
| OpenAI/Geometry/BeltMarks.lean | 1 |
| OpenAI/Geometry/CappedDyadicPartition.lean | 1 |
| OpenAI/Geometry/CellFanCycle.lean | 2 |
| OpenAI/Geometry/DistanceLayers.lean | 1 |
| OpenAI/Geometry/DyadicExhaustion.lean | 1 |
| OpenAI/Geometry/DyadicRefinement.lean | 1 |
| OpenAI/Geometry/DyadicScales.lean | 2 |
| OpenAI/Geometry/ElementarySideReciprocity.lean | 1 |
| OpenAI/Geometry/FanRuns.lean | 8 |
| OpenAI/Geometry/FinCyclicInduction.lean | 4 |
| OpenAI/Geometry/FineCellPartition.lean | 1 |
| OpenAI/Geometry/InitialRegionBoundaries.lean | 1 |
| OpenAI/Geometry/LayerPartition.lean | 1 |
| OpenAI/Geometry/Octants.lean | 2 |
| OpenAI/Geometry/PrimaryFragments.lean | 1 |
| OpenAI/Geometry/PrimaryRegions.lean | 1 |
| OpenAI/Geometry/RepairDepth.lean | 1 |
| OpenAI/Geometry/RepairTree.lean | 1 |
| OpenAI/Geometry/ScaleSeparation.lean | 1 |
| OpenAI/Geometry/SimultaneousRepair.lean | 7 |
| OpenAI/GlobalSchmidtBellRoughLower.lean | 1 |
| OpenAI/GlobalSchmidtBellRoughUpper.lean | 1 |
| OpenAI/GoodAuxiliaryPairCompression.lean | 1 |
| OpenAI/GraphExtendedMetric.lean | 3 |
| OpenAI/GraphInteractionBudget.lean | 5 |
| OpenAI/GraphInteractionDiamondCounting.lean | 6 |
| OpenAI/GraphLatticeDiamond.lean | 1 |
| OpenAI/GraphLatticeDistance.lean | 1 |
| OpenAI/HarmonicWeights.lean | 1 |
| OpenAI/HighestWeight.lean | 3 |
| OpenAI/HookFormula.lean | 1 |
| OpenAI/HookRecursion.lean | 1 |
| OpenAI/InjectionAverage.lean | 2 |
| OpenAI/InjectionPoly.lean | 3 |
| OpenAI/InvariantExponentialComparison.lean | 2 |
| OpenAI/IrrepLabelCount.lean | 1 |
| OpenAI/IrrepLabels.lean | 3 |
| OpenAI/LatticeCounts.lean | 1 |
| OpenAI/LeafStateIntertwine.lean | 1 |
| OpenAI/LiebRobinson/CommutatorRecursion.lean | 2 |
| OpenAI/LiebRobinson/GraphBallStabilization.lean | 2 |
| OpenAI/LiebRobinson/GraphPropagation.lean | 2 |
| OpenAI/LiebRobinson/Volterra.lean | 3 |
| OpenAI/LogClipping.lean | 4 |
| OpenAI/MarginalPhaseSetup.lean | 1 |
| OpenAI/MarginalPhaseSingular.lean | 2 |
| OpenAI/MarginalPhaseSupport.lean | 1 |
| OpenAI/MarkedSimilaritySymbol.lean | 1 |
| OpenAI/MatrixSandwichIntertwine.lean | 1 |
| OpenAI/MeanDerivative.lean | 4 |
| OpenAI/MeanTreeDerivativeIntertwine.lean | 4 |
| OpenAI/MeanTreeProjectionUpper.lean | 1 |
| OpenAI/MergeMoment.lean | 1 |
| OpenAI/MovementEtaRegional.lean | 1 |
| OpenAI/NPositiveMap.lean | 1 |
| OpenAI/OrderedEntropyAlgebra.lean | 4 |
| OpenAI/PairMergeDeficit.lean | 2 |
| OpenAI/PairMergeMoment.lean | 2 |
| OpenAI/PermutationRepresentation.lean | 3 |
| OpenAI/PhaseError.lean | 1 |
| OpenAI/PoissonWord.lean | 9 |
| OpenAI/PoissonWordAppend.lean | 14 |
| OpenAI/PoissonWordJump.lean | 7 |
| OpenAI/PoissonWordMarked.lean | 2 |
| OpenAI/PoissonWordOccupation.lean | 2 |
| OpenAI/PoissonWordPartition.lean | 5 |
| OpenAI/PoissonWordRealOccupation.lean | 1 |
| OpenAI/PoissonWordRelabel.lean | 4 |
| OpenAI/PoissonWordThinning.lean | 7 |
| OpenAI/PositiveMap.lean | 1 |
| OpenAI/PowerDerivativeIntertwine.lean | 2 |
| OpenAI/ProjectionCfcUpperBound.lean | 1 |
| OpenAI/QuasilocalRoots.lean | 2 |
| OpenAI/Rectangles.lean | 7 |
| OpenAI/RegionEntropy.lean | 1 |
| OpenAI/RegionLift.lean | 4 |
| OpenAI/RegionSSA.lean | 2 |
| OpenAI/RegionalFiveFactorCoordinates.lean | 1 |
| OpenAI/ReplicaEtaForms.lean | 1 |
| OpenAI/ReplicaExcitationDecomposition.lean | 1 |
| OpenAI/ReplicaGammaIntegral.lean | 2 |
| OpenAI/ReplicaGoodAuxiliaryLabelBound.lean | 1 |
| OpenAI/ReplicaGoodConfigurationPairMarginal.lean | 1 |
| OpenAI/ReplicaGoodCopyFactorization.lean | 2 |
| OpenAI/ReplicaGoodPairMarginal.lean | 2 |
| OpenAI/ReplicaLift.lean | 1 |
| OpenAI/ReplicaMarginalSymmetry.lean | 1 |
| OpenAI/ReplicaMarkedRatio.lean | 4 |
| OpenAI/ReplicaMarkedRatioInverse.lean | 1 |
| OpenAI/ReplicaMetric.lean | 8 |
| OpenAI/ReplicaPermutationCovariance.lean | 1 |
| OpenAI/ReplicaRegionUnion.lean | 2 |
| OpenAI/ReplicaSimilarity.lean | 1 |
| OpenAI/ReplicaSymmetricMeanTreeProduct.lean | 1 |
| OpenAI/ReplicaTransportCoherentLog.lean | 1 |
| OpenAI/ReplicaTransportCoherentMeasure.lean | 11 |
| OpenAI/ReplicaTransportLeafMeasure.lean | 8 |
| OpenAI/ReplicaTransportSymmetricMetric.lean | 2 |
| OpenAI/ReplicaTransportSymmetricMetricFloor.lean | 1 |
| OpenAI/ReplicaWeight.lean | 1 |
| OpenAI/ResolventDefect.lean | 2 |
| OpenAI/ResolventFunctionalCalculus.lean | 1 |
| OpenAI/RestoringGroundComponent.lean | 2 |
| OpenAI/RestoringOperators.lean | 1 |
| OpenAI/RootChannel.lean | 4 |
| OpenAI/SafeBoxChildren.lean | 2 |
| OpenAI/Scan/ActualChargeEnergyCoefficients.lean | 2 |
| OpenAI/Scan/ActualChargeEnergyDecay.lean | 1 |
| OpenAI/Scan/ActualChargeParameterBound.lean | 2 |
| OpenAI/Scan/ActualEnergyTerms.lean | 1 |
| OpenAI/Scan/ActualHistory.lean | 1 |
| OpenAI/Scan/ActualHistoryFacts.lean | 10 |
| OpenAI/Scan/ActualParameterIntegral.lean | 4 |
| OpenAI/Scan/ActualReplicaDefect.lean | 2 |
| OpenAI/Scan/ActualRoundEntropy.lean | 2 |
| OpenAI/Scan/ActualRoundParameterIntegral.lean | 8 |
| OpenAI/Scan/ActualRoundSplits.lean | 5 |
| OpenAI/Scan/ActualRoundTransport.lean | 2 |
| OpenAI/Scan/ActualScanMeasures.lean | 8 |
| OpenAI/Scan/ActualSharpPrevector.lean | 1 |
| OpenAI/Scan/ActualTransportEstimates.lean | 1 |
| OpenAI/Scan/AugmentedReceivingRegions.lean | 2 |
| OpenAI/Scan/AugmentedReplicaPrevectorProperties.lean | 1 |
| OpenAI/Scan/BadHistoryUnion.lean | 1 |
| OpenAI/Scan/BadOldHistoryDecay.lean | 1 |
| OpenAI/Scan/BandCountGrowth.lean | 1 |
| OpenAI/Scan/BootstrapParameters.lean | 2 |
| OpenAI/Scan/BootstrapRoundedClearance.lean | 2 |
| OpenAI/Scan/Budgets.lean | 5 |
| OpenAI/Scan/ChargeEntropyCost.lean | 1 |
| OpenAI/Scan/ChargePathCounting.lean | 1 |
| OpenAI/Scan/ChargeSlots.lean | 1 |
| OpenAI/Scan/CompactCollarCounting.lean | 1 |
| OpenAI/Scan/Defs.lean | 5 |
| OpenAI/Scan/DesignatedDilution.lean | 1 |
| OpenAI/Scan/DesignatedSampling.lean | 1 |
| OpenAI/Scan/EnergyBalance.lean | 7 |
| OpenAI/Scan/EntropyBalance.lean | 7 |
| OpenAI/Scan/FillTransport.lean | 1 |
| OpenAI/Scan/HistoryMeanTree.lean | 3 |
| OpenAI/Scan/HistoryPrefixes.lean | 1 |
| OpenAI/Scan/HistoryWeights.lean | 2 |
| OpenAI/Scan/MarginalTailsBridge.lean | 3 |
| OpenAI/Scan/OffsetDilution.lean | 1 |
| OpenAI/Scan/OldStateIntegral.lean | 1 |
| OpenAI/Scan/OldStateParameterIntegral.lean | 3 |
| OpenAI/Scan/OriginalTruncation.lean | 1 |
| OpenAI/Scan/PhysicalChargeAncestry.lean | 1 |
| OpenAI/Scan/PhysicalPartition.lean | 4 |
| OpenAI/Scan/PositivePrefixEntropyTransfer.lean | 1 |
| OpenAI/Scan/PrefixComparison.lean | 1 |
| OpenAI/Scan/RegionalMoveEntropy.lean | 4 |
| OpenAI/Scan/RoundedClearance.lean | 4 |
| OpenAI/Scan/RoundedScalePower.lean | 2 |
| OpenAI/Scan/ScanHistories.lean | 5 |
| OpenAI/Scan/ScanTruncationInputs.lean | 3 |
| OpenAI/Scan/Scanner.lean | 1 |
| OpenAI/Scan/SelectedChainProbability.lean | 1 |
| OpenAI/Scan/Selection.lean | 3 |
| OpenAI/Scan/SharpMomentScale.lean | 1 |
| OpenAI/Scan/SourceStatusMarginalMoments.lean | 1 |
| OpenAI/Scan/SourceTargetSharpUpper.lean | 1 |
| OpenAI/Scan/StatusMarginalMoments.lean | 1 |
| OpenAI/Scan/StatusScaleSeparation.lean | 1 |
| OpenAI/Scan/SubsystemDimension.lean | 3 |
| OpenAI/Scan/SubsystemDimensionScale.lean | 5 |
| OpenAI/Scan/SubsystemSize.lean | 2 |
| OpenAI/Scan/TransportDimension.lean | 1 |
| OpenAI/Scan/TransportRound.lean | 6 |
| OpenAI/Scan/TransportRoundParameterIntegral.lean | 5 |
| OpenAI/SchmidtBellPrevector.lean | 3 |
| OpenAI/SchurLabelEstimates.lean | 5 |
| OpenAI/SchurLabelMomentBounds.lean | 1 |
| OpenAI/SchurSectorMass.lean | 1 |
| OpenAI/SchurWeylCommutant.lean | 1 |
| OpenAI/SchurWeylLift.lean | 1 |
| OpenAI/SingleKraus.lean | 2 |
| OpenAI/SinhRatioDensity.lean | 2 |
| OpenAI/SpectralFilter/Cutoff.lean | 1 |
| OpenAI/SpectralFilter/Decay.lean | 1 |
| OpenAI/SpectralFilter/Inversion.lean | 1 |
| OpenAI/SpectralFilter/Kernel.lean | 1 |
| OpenAI/SpectralFilter/MatrixFilter.lean | 4 |
| OpenAI/SplitCopies.lean | 8 |
| OpenAI/SqrtHolder.lean | 1 |
| OpenAI/StarFunction.lean | 1 |
| OpenAI/Statements.lean | 1 |
| OpenAI/StretchedExponentialSummability.lean | 2 |
| OpenAI/SupportInverseSandwich.lean | 5 |
| OpenAI/SurprisalMoment.lean | 1 |
| OpenAI/TailParameter.lean | 4 |
| OpenAI/TraceCompression.lean | 1 |
| OpenAI/TraceHolder.lean | 1 |
| OpenAI/Transport/Intertwine.lean | 2 |
| OpenAI/TreeDerivative.lean | 10 |
| OpenAI/TwoPositiveSchwarz.lean | 4 |
| OpenAI/TypicalBellPin.lean | 1 |
| OpenAI/TypicalPureState.lean | 7 |
| OpenAI/TypicalSet.lean | 2 |
| OpenAI/TypicalStateFromTail.lean | 1 |
| OpenAI/TypicalTailScales.lean | 2 |
| OpenAI/UnitaryHaar.lean | 5 |
| OpenAI/WeightedGeometricMean.lean | 2 |
| OpenAI/WeylDimension.lean | 4 |
| OpenAI/WeylRecursion.lean | 2 |
| OpenAI/ZeroBoundary.lean | 4 |

