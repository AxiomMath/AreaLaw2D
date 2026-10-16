# OAI 265 inventory: what exists, where, verified

Phase 0 item (2) of the OAI 265 plan, plus raw material for items (3) and (4).
Target: OpenAI, *A two-dimensional area law from a global spectral gap*, 24 Sept 2026,
`openai/math` `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/paper.pdf`
(90 PDF pages; proof ends p. 88). The preprint directory has one commit, `adc7f1241b42`
(2026-10-06), so `main` and the revision TNLean cites are the same text. PDF sha256
`91e272a2245ad0bd922be670e023ee76d9afa2564c8e309915070a2f42479153`. The LaTeX source is in
the same directory (`build/sections/*.tex`); equation labels below are from it.

## 0. Method and legend

Every name in the tables carries one tag saying how it was checked.

| Tag | Meaning |
|---|---|
| **E** | Elaborated with `#check` through the hosted Lean session (`mcp__axile__diagnostics` on a gitignored `Arealaw/Probe.lean` in this worktree): Lean 4.33.0, Mathlib v4.33.0 (`db584cd`), Physlib `a50684a1`, this repo at `014e4d9`. |
| **A** | Also `#print axioms` in the same session: `[propext, Classical.choice, Quot.sound]`. |
| **U** | Elaborated and rejected (`Unknown constant` / `Unknown identifier`). Counts as absent. |
| **G** | Found verbatim, `path:line`, in a read-only clone. Not elaborated: TNLean and QICLean need Lean v4.35.0-rc3, which this machine does not have built. |
| **absent** | No name could be produced. Per the rules of this inventory, that means absent. |

Clones (all read-only, in `.axiomcode/scratch/oai265-inventory/`, not committed):

- **TNLean** `LionSR/TNLean` at `f4c2d204ab64a9635c15f709170971bdf8d18d24` (2026-10-12). Toolchain
  `leanprover/lean4:v4.35.0-rc3`; Mathlib `v4.35.0-rc3` (`c55e6e78`); QICLean
  `32a5a1a83f787e28b24ad4da57208d1971d73b28`; Gametheory (`LionSR/Brouwer`) `ec93e4da`;
  checkdecls `3d425859`.
- **QICLean** `LionSR/QICLean` checked out at the TNLean pin `32a5a1a8` (2026-10-12), same toolchain.
- **openai/math Lean** (see Section 3): `lean/OAI/MathematicalPhysics/{PEPSFilters,PEPSMove,PEPSSubvolume,TensorNetwork}`
  at `adc7f12`, fetched file by file through the GitHub API. Toolchain `v4.34.1`.

Whole-tree token scans (comments included, so these are upper bounds):

| Tree | `sorry` | `axiom` decl | `admit` (tactic) | `native_decide` | `unsafe`/`implemented_by`/`extern` |
|---|---|---|---|---|---|
| `TNLean/` (4120 `.lean` files repo-wide) | 0 code (1 hit, a comment, `MPS/RFP/Decorrelation.lean:23`) | 0 | 0 (9 hits, all the English verb) | 0 | 0 |
| `TNLean/PEPS/AreaLaw/` (280 files, 42,572 lines) | 0 | 0 | 0 | 0 | 0 |
| `QICLean/` | 0 code (2 comment hits) | 0 | 0 | 0 | 0 |
| openai `PEPS*`/`TensorNetwork` (109 files, 24,561 lines) | 0 | 0 | 0 | 0 | 0 |

A token scan is not `#print axioms`. Because every TNLean declaration cited below sits in a tree
with no `sorry` or `axiom` token at all, its direct dependencies are clean at grep level; that is
the strongest statement available without building TNLean.

## 1. Per-item status

Items are quoted as note 05 (`ruiz/oai265-notes`, `docs/oai265/reading/05_formalization_map.md`,
section 4) names them. "Repo" means this repository (`Arealaw/`).

### Tier 1

**T1.1 "square-lattice domains via `hasse ℤ □ hasse ℤ` and `induce`"** (paper §1.1, before (1.1))

| Source | Status | Names |
|---|---|---|
| Repo | absent | none (`Arealaw/Geometry.lean` is 1D: `ringDist`, `interval` on `Fin n`) |
| Mathlib | present | `SimpleGraph.hasse` E, `SimpleGraph.hasse_adj` E (`a ⋖ b ∨ b ⋖ a`), `SimpleGraph.boxProd` E (notation `□`), `SimpleGraph.boxProd_adj` E, `SimpleGraph.induce` E. The composite `(SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ).induce (Λ : Set (ℤ × ℤ)) : SimpleGraph ↑↑Λ` elaborates E. No lemma identifying its adjacency with `‖x - y‖₁ = 1` was found (absent). |
| Physlib | absent | `Physlib/CondensedMatter/LatticeModels/Basic.lean` is an 18-line stub (line count checked), no declarations. |
| TNLean | present, own encoding | `TNLean.PEPS.AreaLaw.Site` (`abbrev Site Λ := ↥Λ`) `FiniteDomain.lean:39` G; `domainGraph` `FiniteDomain.lean:47` G, hand-written adjacency, not Mathlib's `hasse`/`boxProd`/`induce`; `rectangularDomain` `RectangularDomain.lean:42` G and `rectangleGraphIso` `:59` G for open rectangles. |

**T1.2 "an ℕ∞ diameter through `edist`"** (paper §1.1, `diam_{dΛ} X ≤ R` in (1.1); "+∞ between different components")

| Source | Status | Names |
|---|---|---|
| Repo | wrong type | `Arealaw.regionDist : (σ → σ → ℕ) → Finset σ → Finset σ → ℕ` E, `Arealaw.separation` E, `Arealaw.regionDist_empty_left : regionDist d ∅ Y = 0` E, `Arealaw.regionDist_empty_right` E. ℕ-valued, empty set at distance 0. |
| Mathlib | present | `SimpleGraph.edist : V → V → ℕ∞` E, `SimpleGraph.edist_eq_top_of_not_reachable` E, `SimpleGraph.exists_walk_of_edist_ne_top` E, `SimpleGraph.Walk.edist_le` E, `SimpleGraph.edist_le_one_iff_adj_or_eq` E, `SimpleGraph.ediam : ℕ∞` E (whole graph), `SimpleGraph.edist_le_ediam` E, `SimpleGraph.ediam_eq_top_of_not_preconnected` E, `SimpleGraph.ediam_eq_top_of_not_connected` E. Trap: `SimpleGraph.dist : ℕ` E with `SimpleGraph.dist_eq_zero_of_not_reachable` E. `SimpleGraph.edist_eq_top_iff` U, `SimpleGraph.Subgraph.ediam` U. No diameter of a vertex *subset* measured in the ambient graph (absent): `ediam` is a graph invariant, so `diam_{dΛ} X` has to be written as `⨆ x ∈ X, ⨆ y ∈ X, G.edist x y` or as a pairwise bound. |
| Physlib | absent | none |
| TNLean | present | `IsAdmissibleSupport` `FiniteDomain.lean:61` G (pairwise walk of length `≤ R` inside `domainGraph Λ`); `exists_walk_length_le_iff_edist_le` `:131` G (equivalent to `edist ≤ R`); `graphPseudoEMetricSpace` `GraphExtendedMetric.lean:42` G. |

**T1.3 "admissible Hamiltonians built with `extendId`"** (paper (1.1): one term `h_X = h_X*`, `‖h_X‖ ≤ J` per nonempty `X ⊆ Λ` with `diam_{dΛ} X ≤ R`)

| Source | Status | Names |
|---|---|---|
| Repo | building blocks present, Hamiltonian absent | `Arealaw.extendId` E (over `RCLike 𝕜`), `Arealaw.extendId_eq_kronecker` E A, `Arealaw.extendId_one` E, `Arealaw.isHermitian_extendId` E, `Arealaw.posSemidef_extendId` E A, `Arealaw.trace_extendId` E, `Arealaw.ptrace_mul_extendId` E A, `Arealaw.extendId_mul_ptrace` E, `Arealaw.trace_ptrace_mul` E. Instantiation at `σ := ℤ × ℤ`, `loc := fun _ => Fin q`, `X ⊆ Λ` elaborates E. `Arealaw.extendId_mul` U. No norm identity `‖extendId A‖ = ‖A‖`, no commutation for disjoint supports, no nested-extension lemma (absent). |
| Mathlib | partial | `Matrix.kroneckerMap` (appears in `extendId_eq_kronecker` E); L2 operator norm instance under `Matrix.Norms.L2Operator` (used by the repo lemmas `Arealaw.l2_opNorm_kronecker_le` E etc.). No local Hamiltonian notion (absent). |
| Physlib | absent | none |
| TNLean | present, own encoding | `LocalHamiltonian` `LocalHamiltonian.lean:45` G (fields `term`, `supported`, `hermitian`, `norm_le`), `LocalHamiltonian.operator` `:57` G, `AdmissibleSupport` `FiniteDomain.lean:66` G (subtype of `Finset (Site Λ)`, one term per support), `localLift` `LocalHamiltonian.lean:80` G. Support is membership in `QuantumCircuit.supportedOperators q X` (`TNLean/Circuit/LocalCircuit.lean:90` G: span of Kronecker products equal to `1` off `X`), not a placement map. |

**T1.4 "the Loewner-form gap"** (paper Thm 1.1: `H − E₀ id ≥ Δ(id − |Ω⟩⟨Ω|)`; Prop 4.3 adds `HΩ = E₀Ω, ‖Ω‖ = 1`)

| Source | Status | Names |
|---|---|---|
| Repo | absent as a notion | `Arealaw.vecMulVec_self_star_eq_rhoA` E, `Arealaw.rhoA` E, `Arealaw.fidelity_vecMulVec` E (pure-state projector facts). |
| Mathlib | order present, gap absent | `Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef` E, `Matrix.PosSemidef` E, `Matrix.vecMulVec` E, `Matrix.posSemidef_vecMulVec_self_star` E, `Matrix.toEuclideanCLM` E, `Matrix.IsHermitian.eigenvalues` E, `Matrix.IsHermitian.trace_eq_sum_eigenvalues` E. No min-max / Courant-Fischer and no Weyl perturbation inequality found (absent). |
| Physlib | absent | none |
| TNLean | present | `Matrix.IsGappedGroundState` `TNLean/Algebra/GappedGroundState.lean:45` G: `‖Ω‖ = 1 ∧ toEuclideanCLM H Ω = E₀ • Ω ∧ PosSemidef (H - E₀ • 1 - Δ • (1 - vecMulVec Ω (star Ω)))`; `Matrix.isGappedGroundState_iff` `:53` G; `Matrix.IsGappedGroundState.eigenspace_eq_span` `:63` G (for `Δ > 0` the `E₀`-eigenspace is `span {Ω}`); domain wrapper `TNLean.PEPS.AreaLaw.IsGappedGroundState` `LocalHamiltonian.lean:98` G. |

**T1.5 "the edge boundary"** (paper §1.1, `∂_Λ A = {{x,y} : x ∈ A, y ∈ Λ∖A, |x−y|₁ = 1}`)

| Source | Status | Names |
|---|---|---|
| Repo | absent | none |
| Mathlib | absent | `SimpleGraph.edgeBoundary` U, `SimpleGraph.cutSet` U. Ingredients: `SimpleGraph.edgeFinset : Finset (Sym2 V)` E, `SimpleGraph.Walk.exists_boundary_dart` E. |
| Physlib | absent | none |
| TNLean | present | `edgeBoundary : Finset (Sym2 (Site Λ))` `FiniteDomain.lean:81` G, `edgeBoundary_empty` `:109` G, `edgeBoundary_univ` `:115` G, `exists_edgeBoundary_of_walk` `:165` G; vertex forms `innerBoundary` `BoundaryConventions.lean:32` G, `endpointBoundary` `:39` G. |

**T1.6 "templates"** (paper Def 9.3, §9.3)

| Source | Status | Names |
|---|---|---|
| Repo / Mathlib / Physlib | absent | none |
| TNLean | present | `TNLean.PEPS.AreaLaw.Geometry.Template (Ctpl : ℝ) (n s₀ : ℕ)` `Geometry/Templates.lean:72` G (polygons with slopes `0, ∞, ±1` via `IsAllowedSlope` `:35`, exact lattice sampling, nonempty, `Ctpl * N₀ * (s₀+1) ≤ n`, sup-diameter `≤ n`); `Template.IsSeparated` `:105` G; `Template.core` `:111`, `Template.collar` `:117` G; `ambientDilation` `FiniteDomain.lean:89` G (the `T_j` of §2.2). |

**T1.7 "Theorem 1.1 and Corollary 1.2 stated as Props, with the constant quantified as ∃C ∀Λ ∀H ∀Ω ∀A"** (paper Thm 1.1, (1.2); Cor 1.2)

| Source | Status | Names |
|---|---|---|
| Repo / Mathlib / Physlib | absent | none |
| TNLean | Thm 1.1 stated, open; Cor 1.2 proved conditionally | `UniformAreaLaw : Prop` `TheoremStatements.lean:70` G, verbatim: `∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ → ∀ A : Finset (Site Λ), regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card`. No theorem proves it (its only use is the next line). `UniformAreaLaw.vertex_boundary_bounds (h : UniformAreaLaw) : …` `VertexBoundaryCorollaries.lean:63` G gives `4C|∂_in A|` and `2C|Z_A|` from the hypothesis. The "rectangular lattice" first sentence of Cor 1.2 rests on `rectangleGraphIso` `RectangularDomain.lean:59` G; the Hamiltonian transport is listed as open in TNLean's own `docs/formalization/openai-area-law-peps.md`. |

**T1.8 "Interface Props for exactly what the paper says it exports in §1.3, and what the PEPS companion's Appendix A imports: Proposition 4.3, Definition 9.3 with Proposition 9.6, Proposition 10.2, Lemma 11.1, and Proposition 11.2"**

§1.3 itself names Prop 4.3, Props 9.6 and 10.2, and Prop 11.2. It does not name Lemma 11.1 (see Section 6).

| Result | Repo / Mathlib / Physlib | TNLean |
|---|---|---|
| Prop 4.3 (`prop:positive`) | absent | **Proved** (G): `TNLean.PEPS.AreaLaw.exists_positiveQuasilocalConstraints` `PositiveConstraints.lean:133`, on a general finite graph with ball/sphere growth, support-size and site-budget hypotheses; `LatticeConstraints.lean` discharges those for `domainGraph` (its docstring, lines 18-24). Spectral part `SpectralFilter.positive_replacement` `QICLean/Analysis/SpectralFilter/PositiveReplacement.lean:308` G. |
| Def 9.3 | absent | Defined (T1.6). |
| Prop 9.6 (`prop:collar`) | absent | **Absent.** No file cites `prop:collar`. Prop 9.2 exists only conditionally: `Scan.scanner_estimate` `Scan/Scanner.lean:53` G takes `S : ScanData …` (`Scan/Defs.lean:256` G), a structure whose fields are the conclusions of Lemma 9.1, Prop 7.4, Prop 8.1, Lemma 2.1 and Lemma 3.1 (module docstring, "Scope restriction (inputs as hypotheses)"). No `ScanData` is ever constructed (grep). Prop 9.5: only the bootstrap arithmetic with the improvement as a hypothesis, `exists_uniform_boxError_bound_of_eventual_improvement` `Scan/ExponentBootstrap.lean:112` G. |
| Prop 10.2 (`prop:amplification`) | absent | **Absent.** No file cites `prop:amplification`; `Amplification/` (17 files) holds channel-oscillation and radius-scale lemmas (`RadiusScales.lean` cites `eq:amplification-radius`). |
| Lemma 11.1 (`geometry:cancellation`) | absent | **Proved** (G): `Geometry.OrderedTwoFamilyPartition.entropy_le_residual_add_half_sum` `TwoFamilies.lean:94`, lattice form `regionalEntropy_le_residual_add_half_sum` `TwoFamilies.lean:143`; partition structure `Geometry.OrderedTwoFamilyPartition` `Geometry/Templates.lean:124`, `earlierSameFamily` `:142`. |
| Prop 11.2 (`prop:two-families`) | absent | **Open.** 108 files under `Geometry/` prove parts (layers, belts, cell fans, initial regions); TNLean's own coverage table lists "simultaneous repairs, birth separation, and the full partition" as remaining. No theorem with the conclusion of Prop 11.2 was found. |

**T1.9 "Proved in full: the region SSA bridge"** (paper §2.1, `I(D:F|E) ≥ 0` [27])

| Source | Status | Names |
|---|---|---|
| Repo | two-region only | `Arealaw.unionState` E (ℂ only), `Arealaw.regionEntropy_union_le` E A, `Arealaw.mutualInfo_nonneg` E A, `Arealaw.abs_regionEntropy_sub_regionEntropy_le` E A (Araki-Lieb), `Arealaw.mutualInfo_le_two_mul_regionEntropy` E, `Arealaw.MState.Sᵥₙ_physlibEquiv` E, `Arealaw.traceRight_physlibEquiv_submatrix` E, `Arealaw.traceLeft_physlibEquiv_submatrix` E. No three-region state, no region SSA, no region conditional entropy or CMI (absent). |
| Mathlib | absent | none |
| Physlib | present on product types | `Sᵥₙ_strong_subadditivity` E A, `qConditionalEnt_strong_subadditivity` E A, `qMutualInfo_strong_subadditivity` E A, `Sᵥₙ_weak_monotonicity` E A, `Sᵥₙ_subadditivity` E, `Sᵥₙ_pure_tripartite_triangle` E, `qcmi` E, `qcmi_nonneg` E A, `qcmi_le_2_log_dim` E A, `qConditionalEnt` E, `qMutualInfo` E. `qcmi_chain_rule` U: it is commented out in `QuantumInfo/Entropy/SSA.lean:1295-1302`. |
| TNLean / QICLean | present | `QICLean` `regionEntropy_ssa` `QICLean/Entropy/RegionEntropy.lean:173` G (`S(A∪(B∪C)) + S(B) ≤ S(A∪B) + S(B∪C)`, pairwise disjoint regions); `SSAPosDef.strong_subadditivity_general` `QICLean/Channel/Schwarz/StrongSubadditivityPosDef.lean:811` G; `FiniteProduct.entropy_compl` `QICLean/Entropy/FiniteProduct.lean:81` G (purity on regions); `FiniteProduct.mutualInformation_nonneg` `:174` G; conditional MI lemmas in `QICLean/Entropy/FiniteProductConditional.lean:48,58,67,90` G. |

**T1.10 "Lemma 11.1"** (proved in full): see T1.8. Repo, Mathlib, Physlib absent; TNLean/QICLean proved (G).

**T1.11 "Corollary 1.2 from Theorem 1.1"**: see T1.7. TNLean `UniformAreaLaw.vertex_boundary_bounds` (G) is exactly this implication. Repo, Mathlib, Physlib absent.

**T1.12 "`areaLaw_of_interfaces`, which derives Theorem 1.1 from Propositions 9.6, 10.2 and 11.2 plus Lemma 2.2"** (paper §11.8)

Absent everywhere, including TNLean. §11.8 also uses Lemma 11.1, monotonicity of mutual information
under discarding part of the first system, and `S(D) ≤ |D| log q`; any interface theorem needs them
as inputs too. Available pieces: TNLean Lemma 2.2 (T1.13), Lemma 11.1 (T1.8);
`Arealaw.MState.entropy_le_log_card` E A and Physlib `Sᵥₙ_le_log_d` E for the `|D| log q` step;
Physlib `qMutualInfo_strong_subadditivity` E A for monotonicity.

**T1.13 "Guards: the cases q = 1, R = 0 (product ground state), b = 0, and the `dist` versus `edist` trap"** (paper §2.2 last paragraph; Lemma 2.2)

| Source | Status | Names |
|---|---|---|
| Repo / Physlib | absent | none |
| Mathlib | trap documented | `SimpleGraph.dist_eq_zero_of_not_reachable` E vs `SimpleGraph.edist_eq_top_of_not_reachable` E. |
| TNLean | proved | Lemma 2.2: `regionalEntropy_eq_zero_of_edgeBoundary_eq_empty` `ZeroBoundary.lean:321` G; `R = 0`: `regionalEntropy_eq_zero_of_range_eq_zero` `:331` G; `q = 1`: `regionalEntropy_eq_zero_of_q_eq_one` `:362` G; empty domain: `regionalEntropy_eq_zero_of_domain_eq_empty` `:368` G; product step `exists_eq_mul_of_gap` `ProductGroundState.lean:55` G, `vonNeumannEntropy_partialTraceRight_eq_zero_of_gap` `:145` G; range zero is one-site supports `isAdmissibleSupport_zero_iff` `FiniteDomain.lean:145` G. |

### Tier 2

**T2.1 "Lemma 2.1"** (Alicki-Fannes-Winter, (2.1) `eq:conditional-continuity`)

| Source | Status | Names |
|---|---|---|
| Repo | absent | Only `Arealaw.FannesAudenaert.repaired_of_audenaert` E, which takes Audenaert's inequality as a hypothesis (`Arealaw/Sanity/FannesPurifiedDistance.lean`). `Arealaw.repaired_of_audenaert` U (namespaced). |
| Mathlib | ingredients | `Real.binEntropy` E, `Real.negMulLog` E, `Real.concaveOn_negMulLog` E, `CFC.posPart_sub_negPart` E (Jordan decomposition). |
| Physlib | absent | no Fannes/Alicki/Winter declaration (grep of `QuantumInfo/`). |
| QICLean | proved | `Entropy.abs_conditionalEntropy_sub_le` `QICLean/Entropy/ControlledContinuity.lean:231` G, verbatim first inequality of (2.1) with `binEntropy`; `Entropy.abs_conditionalEntropy_sub_le_sqrt` `:273` G (second inequality, `C = 4`); `Entropy.conditionalEntropy` `QICLean/Entropy/ConditionalEntropy.lean:134` G. TNLean lattice corollary `abs_regionalEntropy_sub_le_sqrt_traceDistance` `RegionalEntropyContinuity.lean:33` G (pure states, factor `1 + |A| log q`). |
| openai/math | proved | `OAI.PolynomialPEPS.PhysicalMove.QuantumSSA.conditional_continuity` `PEPSMove/EntropyContinuity.lean:70` G (`2δ log d + negMulLog δ − negMulLog (1+δ)`, the same bound). |

**T2.2 "Lemma 3.1"** (marginal moment and tail bounds, (3.1) `eq:initial-tail-mgf`, (3.2) `eq:initial-tail-probability`)

| Source | Status | Names |
|---|---|---|
| Repo | absent | none |
| Mathlib | ingredients | `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` E (for `f : ℂ → E`, so the vector form is covered); `norm_cauchyPowerSeries_le` E; `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` E; `ProbabilityTheory.mgf` E; `ProbabilityTheory.measure_ge_le_exp_mul_mgf` E (exponential Markov). `Complex.norm_le_interp_of_mem_verticalClosedStrip'` U (note 05's spelling). |
| Physlib | absent | none |
| TNLean / QICLean | proved | General: `Entropy.log_surprisalMoment_le_of_schmidtRow` `QICLean/Entropy/GapSurprisal.lean:295` G, `Entropy.surprisalTail_le_of_schmidtRow` `:322` G, `Entropy.cutLogBudget` `:188` G (`1 + ∑ log (e·d_i)^2`), `Entropy.tailRadius` `:206` G, `Entropy.log_surprisalMoment_eigenvalues_le` `QICLean/Entropy/MarginalTails.lean:228` G. Lattice: `LocalHamiltonian.log_surprisalMoment_reducedState_le` `MarginalTails.lean:98` G, `LocalHamiltonian.surprisalTail_reducedState_le` `:119` G, `cutLogBudget` `:88` G. |

**T2.3 "Lemma 3.2"** (buffered conditional entropy, (3.9) `eq:initial-buffer-discount`)

| Source | Status | Names |
|---|---|---|
| Repo | absent | none |
| Mathlib | ingredients | `IsCompact.exists_isMaxOn` E, `NormedSpace.exp` E, `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` E, `Real.concaveOn_negMulLog` E. |
| Physlib | ingredients | `schattenNorm` E, `schattenNorm_mul_le` E (Hölder), `HermitianMat.trace_young` E. No concavity of `Sᵥₙ` found (absent). |
| TNLean / QICLean | proved | `exists_condEntropy_le_initialBuffer` `InitialBuffer.lean:424` G (∃ `Cpad ≥ 1`, `Cbuf ≥ 0`, uniform in `D₀ > 2R+10`); finite-dimensional core `Entropy.two_mul_condEntropy_le` `QICLean/Entropy/BufferDiscount.lean:397` G; `IsSafe` `BufferedRectangles.lean:195` G; `IntRect` `:83` G; `rectRegion` `:200` G. |

**T2.4 "Proposition 3.3"** (initial safe-box estimate, (3.21))

| Source | Status | Names |
|---|---|---|
| Repo | absent | `Arealaw.Ladder.descend_add` E and `Arealaw.Ladder.rescale_step` E are scalar recursions on `ℕ → ℝ` (not pinned to `Qubits`, contrary to note 05). |
| Mathlib / Physlib | absent | none |
| TNLean | proved | `boxEntropy` (`F_box`) `InitialBoxEstimate.lean:63` G with `bddAbove_boxEntropyValues` proved in the same file (so the `sSup` is not the junk value 0); `exists_boxEntropy_le_rpow` `:437` G: `∃ C e₀, 0 < e₀ ∧ e₀ < 1 ∧ ∀ D₀, 2R+10 < D₀ → ∀ r ≥ 1, boxEntropy q R J Δ D₀ r ≤ C * r ^ (1 + e₀)`. Deterministic colour rotations replace the paper's random order (module docstring). |
| openai/math | proved, different setting | `OAI.PolynomialPEPS.Subvolume.RectangleTiling.uniform_subvolume_square` `PEPSSubvolume/Subvolume.lean:71` G: `L × L` open grid, on-site plus nearest-neighbour terms, `q ≥ 2`, square boxes `box lo₁ lo₂ 1 n`; not induced domains, not finite range `R`, no cut `A`. |

Also verified for tools named under §§2-4 (not Tier items): `Arealaw.sum_single_kronecker_submatrix` E A (matrix-unit
decomposition across a cut, Lemma 3.1 proof); `Arealaw.MState.D₁_eq_traceNorm_div_two` E A; `Arealaw.uhlmann` E A;
`Arealaw.exists_mem_unitaryGroup_eq_mul_diagonal` E; `Matrix.traceNorm` E, `Matrix.traceNorm_eq_max_re_tr_U` E
(Physlib); `MatrixMap.IsCompletelyPositive` E, `MatrixMap.Unital` E (Physlib); `OperatorGeometricMean.operatorPowerMean` E
(Physlib, on bounded operators `LownerHeinzTheorem.L ℋ`, not matrices); `CFC.monotone_rpow` E, `CFC.rpow_le_rpow` E,
`CFC.sqrt_le_sqrt` E, `CFC.log_le_log` E, `CFC.abs` E; `norm_le_gronwallBound_of_norm_deriv_right_le` E;
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` E; `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` E;
`polynomialFunctions_closure_eq_top` E; `ContDiffBump` E; `Fourier.fourierIntegral` E, `VectorFourier.fourierIntegral` E,
`Continuous.fourierInv_fourier_eq` E (`Real.fourierIntegral` U). TNLean Lemma 4.1: `exists_quasilocal_lieb_robinson`
`GraphPropagation.lean:247` G (constants from `R, J` only; zero commutator at `edist = ⊤`). QICLean Lemma 4.2:
`SpectralFilter.spectralCutoff` `QICLean/Analysis/SpectralFilter/Cutoff.lean:196` G,
`SpectralFilter.exists_abs_spectralKernel_le_exp` `QICLean/Analysis/SpectralFilter/Decay.lean:171` G.

## 2. TNLean map

**Size and layout.** 4120 `.lean` files repo-wide: `TNLean/MPS` 2078, `TNLean/PEPS` 1324, `TNLean/Algebra`
209, `TNLean/Circuit` 107, `TNLean/QCA` 38, `TNLean/Wielandt` 28, `TNLean/Spectral` 13, plus tests. The area
law is `TNLean/PEPS/AreaLaw/` (280 files, 42,572 lines, 1095 `theorem`/`lemma`, 304 `def`/`abbrev`/`structure`
lines), aggregated by the generated `TNLean/PEPS/AreaLaw.lean`: 66 top-level modules plus `Geometry/` (108
files), `Scan/` (88), `Amplification/` (17). Generic quantum information (entropy, partial trace, SSA,
continuity, spectral filter, surprisal moments) lives in QICLean. The "~264 files" in the brief matches
neither count exactly; 280 is the area-law tree at `f4c2d204`.

**Main statements, verbatim.**

- Theorem 1.1: `TNLean.PEPS.AreaLaw.UniformAreaLaw` `TNLean/PEPS/AreaLaw/TheoremStatements.lean:70`, quoted in
  T1.7. **Open** (a `def … : Prop`, no proof anywhere).
- Corollary 1.2: `UniformAreaLaw.vertex_boundary_bounds` `VertexBoundaryCorollaries.lean:63`, **proved from
  the hypothesis `h : UniformAreaLaw`**.
- The PEPS companion's `PolynomialPEPSApproximation` is also only a target (TNLean doc
  `docs/formalization/openai-area-law-peps.md`, "Target proposition defined").

**Status by paper result** (G throughout).

| Paper | TNLean / QICLean |
|---|---|
| Lemma 2.1 | proved (QICLean `Entropy.abs_conditionalEntropy_sub_le`) |
| Lemma 2.2, degenerate cases | proved (`ZeroBoundary.lean`) |
| Lemma 3.1 | proved (`MarginalTails.lean`, QICLean `GapSurprisal.lean`) |
| Lemma 3.2 | proved (`InitialBuffer.lean:424`) |
| Prop 3.3 | proved (`InitialBoxEstimate.lean:437`) |
| Lemma 4.1 | proved (`GraphPropagation.lean:247`) |
| Lemma 4.2 | proved (QICLean `SpectralFilter`) |
| Prop 4.3 | proved (`PositiveConstraints.lean:133`) |
| Lemma 4.4, Prop 4.5 | partial (`QuasilocalRoots.lean`, `FiniteSetTruncation*.lean`; not audited here) |
| §§5-8 | partial in QICLean (`ConditionalMovement*`, `MarginalPhase*`, `IidSchur*`); not audited here |
| Prop 9.2 | conditional on `ScanData` (never constructed) |
| Props 9.5, 9.6 | open (bootstrap arithmetic only) |
| Prop 10.2 | open |
| Lemma 11.1 | proved |
| Prop 11.2 | open (parts proved) |
| Theorem 1.1 | open |

**Definitions.** Domain `Site Λ := ↥Λ` for `Λ : Finset (ℤ × ℤ)`; `domainGraph` (hand-written adjacency);
`Configuration Λ q := Site Λ → Fin q`; `StateSpace Λ q := EuclideanSpace ℂ (Configuration Λ q)`;
`LocalHamiltonian` (T1.3); `IsGappedGroundState` (T1.4); `edgeBoundary` (T1.5); `reducedState`
`TheoremStatements.lean:38` (Mathlib split `Equiv.piEquivPiSubtypeProd`, then QICLean
`Matrix.partialTraceRight` `QICLean/Channel/PartialTrace.lean:98`); `regionalEntropy` `TheoremStatements.lean:63`
= QICLean `vonNeumannEntropy` (`QICLean/Analysis/Entropy.lean:96`, `∑ negMulLog (eigenvalues)`, natural log).

**Axioms and sorries.** 0 / 0 across `TNLean/` and `QICLean/` (Section 0). TNLean's CI rule
(`docs/openai-math-provenance.md`): "contains no `sorry`, `axiom` or `native_decide`". The gate here is
grep, not `#print axioms`; TNLean was not built.

**Soundness review of the statement layer.**

- Quantifier order of `UniformAreaLaw` is the paper's: constants `q, R, J, Δ` first, then `∃ C`, then `Λ`,
  `h`, `E₀`, `Ω`, the gap hypothesis, `A`. `C ≥ 0` is a harmless strengthening.
- The gap hypothesis contains the eigen-equation `H Ω = E₀ Ω` and `‖Ω‖ = 1`. This is load-bearing: without
  it any unit `Ω` satisfies `H − E₀ ≥ Δ(1 − |Ω⟩⟨Ω|)` once `E₀ ≤ λ_min(H) − Δ`, and the conclusion fails for
  volume-law `Ω`.
- Supports are measured in the domain graph (walks inside `Λ`), not in the subgraph induced on `X`; one term
  per support (subtype index, not a multiset). Both match (1.1).
- `supportedOperators` is a span of Kronecker products with identity off `X`: a genuine "supported on `X`"
  algebra, not a trivially satisfiable predicate.
- `boxEntropy` is an `sSup` over `ℝ`, which would silently be `0` if unbounded; TNLean proves
  `bddAbove_boxEntropyValues`, so Prop 3.3 is not vacuous.
- `IsSafe` quantifies over crossing-edge endpoints, so the empty cut is safe for every rectangle: the paper's
  "distance to the empty set is infinite" (§3.2).
- Concern: `Scan/` (Prop 9.2 and helpers in `Selection.lean`, `Budgets.lean`, `EnergyBalance.lean`,
  `EntropyBalance.lean`) proves results over `ScanData`, a structure whose fields are the conclusions of
  Lemma 9.1, Prop 7.4, Prop 8.1, Lemma 2.1, Lemma 3.1. This is the "structure with the properties I need"
  pattern the owner has ruled out for this repo. None of it is on the path to anything proved unconditionally.
- Concern: `Template` takes `Ctpl : ℝ` as a free parameter; Def 9.3 fixes it as a large numerical constant.
  TNLean's docstring says every geometric estimate must assume the lower bound explicitly. Not an error,
  but a caller can instantiate `Ctpl ≤ 0`.
- Minor: `Scan/Scanner.lean` docstring calls `lem:tail` "Lemma 2.3"; it is Lemma 3.1.
- TNLean cites the LaTeX at `adc7f12`; since the preprint has one commit, citations match `main`.

## 3. Lean in openai/math (finding)

The brief says "no Lean anywhere in their repo". CONTENTS entry 265 carries no `[Lean]` link (entries 266 and
267 do), and there is no `lean/docs/265.md`. But `openai/math` at `adc7f12` contains
`lean/OAI/MathematicalPhysics/PEPSFilters` (25 files), `PEPSMove` (33), `PEPSSubvolume` (50) and
`TensorNetwork/VectorColumn.lean`: 109 files, 24,561 lines, namespace `OAI.PolynomialPEPS`, `import Mathlib`,
toolchain v4.34.1, with no `sorry`, `axiom`, `admit` or `native_decide` token. It formalizes pieces on the
`L × L` grid of the PEPS companion: `FullSystemGap` `PEPSFilters/Basic.lean:74` (quadratic-form gap),
`IsGridHamiltonian` `:57`, `vonNeumannEntropy` `:127`, `boundaryCard` `:130`, strong subadditivity
`PhysicalMove.QuantumSSA.strong_subadditivity_posDef` `PEPSMove/StrongSubadditivity.lean:66`, Lemma 2.1
`PEPSMove/EntropyContinuity.lean:70`, three-lines `PhysicalMove.LocalMove.paired_three_lines`
`PEPSMove/ThreeLines.lean:18`, and the grid subvolume law `uniform_subvolume_square`
`PEPSSubvolume/Subvolume.lean:71`. TNLean adapts `Vertex`, `ForwardAdjacent` and the PEPS contraction from
`PEPSFilters/Basic.lean` (`TNLean/docs/openai-math-provenance.md`). None of it is on induced domains or finite
range `R`, and none of it was elaborated here.

## 4. Conventions: raw material for item (3)

| Convention | Paper | TNLean | Mathlib | Physlib | Repo |
|---|---|---|---|---|---|
| Log base | natural, §1.1 "All logarithms are natural", `0 log 0 = 0`; `B` in Lemma 3.1 uses `log² (e d_i)` | natural: QICLean `vonNeumannEntropy` = `∑ negMulLog` | `Real.negMulLog`, `Real.log` | `Sᵥₙ` natural (`Sᵥₙ_eq_trace_cfc_negMulLog`, grep) | nats primitive: `Arealaw.H` (`Arealaw/Entropy.lean:16`, `∑ negMulLog`), base 2 derived `H₂ = H / log 2` (`:68`), `SubState.entropy`/`entropy₂` |
| Edge vs vertex boundary | Thm 1.1 edge boundary `∂_Λ A`, unordered edges inside `Λ`; Cor 1.2 `∂_in A` (sites of `A` on a crossing edge), `Z_A` (both endpoints); `\|∂_in A\| ≤ \|∂_Λ A\| ≤ 4\|∂_in A\|`, `\|Z_A\| ≤ 2\|∂_Λ A\| ≤ 4\|Z_A\|`; §3.2's `Z` is `Z_A` | `edgeBoundary : Finset (Sym2 (Site Λ))`, `innerBoundary`, `endpointBoundary` | none; `SimpleGraph.edgeFinset : Finset (Sym2 V)` | none | none |
| `dist` vs `edist` | `d_Λ` graph distance in the induced graph, `+∞` across components; `dist(·, ∅) = +∞` (§3.2, (11.3)-(11.4)); ambient `dist_∞` separately for safety and templates | walks / `edist`, `graphPseudoEMetricSpace`; ambient `supDist` | `edist : ℕ∞` (`⊤` unreachable); `dist : ℕ` (`0` unreachable, `dist_eq_zero_of_not_reachable`) | none | `regionDist`, `separation : ℕ`, `regionDist d ∅ Y = 0` |
| Diameter of a support | `diam_{dΛ} X`: metric diameter of `X` inside `Λ`'s graph | pairwise walk bound in `domainGraph Λ` | `ediam` is a whole-graph invariant; `ediam` of `(G.induce Λ).induce X` would measure inside `X` (wrong, and a strictly smaller Hamiltonian class) | none | none |
| Gap direction | `H − E₀ id ≥ Δ (id − \|Ω⟩⟨Ω\|)` with `Ω` a unit ground vector at energy `E₀`; Prop 4.3 states `HΩ = E₀Ω`, `‖Ω‖ = 1` explicitly | `PosSemidef (H − E₀•1 − Δ•(1 − vecMulVec Ω (star Ω)))` plus `‖Ω‖ = 1` and `H Ω = E₀ Ω` | `Matrix.le_iff : A ≤ B ↔ (B − A).PosSemidef`, so `Δ • (1 − vecMulVec Ω (star Ω)) ≤ H − E₀ • 1`; `vecMulVec Ω (star Ω)` is `\|Ω⟩⟨Ω\|` | none | none |
| Universe of site spaces | `ℂ^q` per site | `Fin q`, `Type` | universe-polymorphic | `MState (d : Type u)` | `Reg (loc : σ → Type u₂) S : Type (max u₁ u₂)`; `loc := fun _ => Fin q` gives `Type` (elaborated); `Arealaw.LocP (loc : σ → Type)` pins `Type` |
| Field | ℂ | ℂ | `RCLike` throughout | ℂ (`MState`, `Sᵥₙ`, `schattenNorm`) | `RCLike 𝕜` for Region/PTrace/Mixed; ℂ for Subadditivity (Physlib) |

## 5. Raw material for item (4): what of BH12 carries over

All declarations below elaborated (E) at `σ := ℤ × ℤ` or generic `σ` with `[DecidableEq σ]`; `A` marks those
whose axioms were printed.

**Unchanged on a 2D finite domain** (generic in the site type `σ`, the local spaces `loc`, and `RCLike 𝕜`):

- `Arealaw/Region.lean`: `Reg`, `restr`, `glue`, `glueEquiv`, `splitEquiv`, `unionEquiv`, `sdiffEquiv`,
  `univEquiv`, `card_reg`, `card_reg_union`, `card_reg_const` (`Reg (fun _ : ℤ × ℤ => Fin q) Λ : Type`
  elaborated).
- `Arealaw/PTrace.lean`: `ptrace`, `ptrace_ptrace` A, `ptraceₗ`, `ptrace_eq_traceRight`, `ptrace_eq_traceLeft`,
  `ptrace_eq_sum_conj`, `posSemidef_ptrace`, `trace_ptrace`, `extendId` and `extendId_eq_kronecker` A,
  `extendId_one`, `isHermitian_extendId`, `posSemidef_extendId` A, `trace_extendId`, `ptrace_mul_extendId` A,
  `extendId_mul_ptrace`, `trace_ptrace_mul`, `kronUnion`, `ptrace_kronUnion_left`, `ptrace_kronUnion_right`.
- `Arealaw/Mixed.lean`: `SubState`, `MState`, `SubState.restrict`, `SubState.restrict_restrict` A,
  `SubState.entropy`, `SubState.regionEntropy`, `SubState.mutualInfo`, `SubState.regionEntropy_empty`,
  `MState.restrict`, `MState.entropy_le_log_card` A.
- `Arealaw/Subadditivity.lean` (ℂ only, through Physlib): `unionState`, `regionEntropy_union_le` A (instantiated
  at `Reg (fun _ : ℤ × ℤ => Fin q) Λ`), `mutualInfo_nonneg` A, `abs_regionEntropy_sub_regionEntropy_le` A,
  `mutualInfo_le_two_mul_regionEntropy`.
- Also generic: `Arealaw.vonNeumann`, `Arealaw.trace_cfc`, `Arealaw.MState.physlibEquiv`,
  `Arealaw.MState.Sᵥₙ_physlibEquiv`, the trace-distance, fidelity, Uhlmann, SVD and `OpNorm` lemmas listed in
  Section 1, `Arealaw.sum_single_kronecker_submatrix` A, `Arealaw.Ladder.descend_add`, `Arealaw.Ladder.rescale_step`.

**Chain-, qubit- or ℕ-specific** (do not carry over as is):

- `Arealaw/Geometry.lean`: `ringDist`, `interval`, `IsInterval`, `IsArc` (on `Fin n`); `regionDist`, `separation`
  are generic in `σ` but ℕ-valued with `regionDist d ∅ Y = 0`, which contradicts the paper's `dist(·, ∅) = ∞`.
- `Arealaw/Mixed.lean` section `Qubits` (`Arealaw.Qubits n : Fin n → Type`), and the modules that use it:
  `Arealaw/Ladder.lean` (its `regionEntropy₂` on `Reg (Qubits n) univ`), `Arealaw/Saturation.lean`. `Arealaw/EDC.lean`
  uses the 1D `Geometry.lean` notions.
- `Arealaw.PureState` (`Arealaw/State.lean:24`) is a bipartite coefficient matrix `A × B`, not a region-indexed ket.

**Missing for a 2D statement layer that this repo would own:** a three-region bridge (SSA, conditional
entropy, CMI on regions), region purity `S(A) = S(Λ∖A)`, `extendId_mul`, `‖extendId A‖ = ‖A‖`, an ℕ∞ region
distance.

## 6. Paper versus notes

1. **Lemma 3.1, the parameter `B`.** Notes 01 and 02 read `B = 1 + ∑ log₂(e d_i)` and note 02 reports this as
   "one real error", needing the fix `B := 1 + ∑ ℓ_i²`. The paper already has the squared natural log: the
   LaTeX is `\mathcal B=1+\sum_{i\in\mathcal I_\times}\log^2(\mathrm e d_i)` (`02-initial.tex:48`), and in the PDF
   the `2` after `log` is raised (baseline 694.5 against 699.0, PyMuPDF span origins, page 9). Note 02 also
   quotes "Since ℓ_i ≤ B"; the paper has `\ell_i\le\sqrt{\mathcal B}` (`02-initial.tex:168`). The reported error
   is a text-extraction artifact. QICLean's `Entropy.cutLogBudget` (`GapSurprisal.lean:188`) uses the squared log.
2. **Reflection identity in Lemma 3.1.** Note 02 says "`f_i(−z) = f_i(z)` should read `f_i(−z̄) = conj f_i(z)`".
   The LaTeX already reads `f_i(-\overline z)=\overline{f_i(z)}` (`02-initial.tex:153`). Note 02's guess
   (extraction artifact) is right.
3. **What §1.3 exports.** §1.3 names Prop 4.3, Props 9.6 and 10.2, and Prop 11.2. It does not mention Lemma 11.1
   or Def 9.3 (Def 9.3 enters through the statement of Prop 9.6). The notes' README lists the PEPS companion's
   imports as "Thm 1.1, Prop 4.3, Props 9.6, 10.2, Lemma 11.1" and note 05 lists both Lemma 11.1 and Prop 11.2.
   The owner's brief also says "§1.3 … Lemma 11.1". Whether Lemma 11.1 or Prop 11.2 (or both) is meant is
   for the owner; the PEPS companion's Appendix A was not read here.
4. **`areaLaw_of_interfaces` inputs.** Note 05 lists Props 9.6, 10.2, 11.2 and Lemma 2.2. §11.8 also uses
   Lemma 11.1, monotonicity of mutual information under discarding, and `S(D) ≤ |D| log q`.
5. **Repo names in note 05 that do not elaborate:** `card_Reg_const` (actual `Arealaw.card_reg_const`; likewise
   `card_reg`, `card_reg_union`), `Sᵥₙ_physlibEquiv` (actual `Arealaw.MState.Sᵥₙ_physlibEquiv`), `descend_add` /
   `rescale_step` (actual `Arealaw.Ladder.*`), `repaired_of_audenaert` (actual `Arealaw.FannesAudenaert.repaired_of_audenaert`).
6. **"Missing algebra: … `extendId_one`".** `Arealaw.extendId_one` exists (E). `extendId_mul` is missing (U).
7. **"Ladder's `descend_add` and `rescale_step` … pinned to `Qubits`".** Both are scalar lemmas on `ℕ → ℝ` (E).
8. **Mathlib three-lines name.** Note 05's `Complex.norm_le_interp_of_mem_verticalClosedStrip'` is
   `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`.
9. **Physlib CMI chain rule.** Note 05 lists `qcmi` among Physlib's assets; the chain rule `qcmi_chain_rule` is
   commented out in this Physlib pin.
10. **"Lieb-Robinson … absent everywhere" and "no Lean".** True for Mathlib and Physlib. TNLean proves Lemma 4.1
    (`exists_quasilocal_lieb_robinson`) and Prop 4.3, and `openai/math` itself ships 24.5k lines of Lean for the
    PEPS side (Section 3). Note 05 does not mention TNLean.
11. **Repo snapshot.** Note 05 describes main at `a56d41d` (34 files, 5,275 lines). This worktree is at `014e4d9`
    (36 files, 5,709 lines, including the Lemma 19 / AEP module).
12. **Page count.** Note 05 says 88 pages; the PDF has 90 (proof ends on p. 88, references to p. 90).

## 7. Not done, or done weakly

- No TNLean, QICLean or openai/math declaration was elaborated: their toolchains (v4.35.0-rc3, v4.34.1) are not
  built here. Their status rests on verbatim grep with `path:line` and on whole-tree token scans.
- `#print axioms` was run only on the declarations marked A, not on every E name.
- TNLean's §4.4-§8 and §10 partial work was listed by module, not audited.
- The PEPS companion (its Appendix A import list) was not read.
- `mcp__plugin_axiomcode_axiomcode__lean_run_code` timed out without checking anything (no Axile environment
  for this repo; filed as a duplicate of AxiomMath/axiom#12706) and `axile_provision` refused the worktree
  (duplicate of #12587). The checks above used `mcp__axile__diagnostics` instead.
