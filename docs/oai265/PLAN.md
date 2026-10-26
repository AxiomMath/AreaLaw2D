# OAI265 Phase 0 plan

Target: OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
`openai/math`, `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
(90 pp, unrefereed), cited as [OAI265] by section and equation number. Section and equation
numbers below were checked against the LaTeX source (`build/sections/*.tex`, with
`\numberwithin{equation}{section}`, theorem counter per section) and against the PDF text.

Phase 0 deliverables:

- `OpenAI/Statements.lean`: the statement layer (Section 1 below).
- `docs/oai265/Inventory.md`: per-item status of note 05's Tier 1 and Tier 2 lists in this repo,
  Mathlib, Physlib, TNLean/QICLean and `openai/math`, with exact names and how each was checked.
- `docs/oai265/Memory.md`: the decision log.
- This file: conventions (Section 2), verdict (Section 3), open decisions (Section 4), Phase 1
  outline (Section 5).

No proof of any paper result has been started.

## 1. Statement layer

Library `OpenAI` (lakefile `[[lean_lib]]`), namespace `OpenAI`, imports `Arealaw.Mixed` and
Mathlib modules only. `lake build OpenAI` on this branch: `Build completed successfully (2806
jobs)`, six `declaration uses 'sorry'` warnings at lines 205, 229, 281, 349, 392, 416.

Definitions (all sorry-free), `OpenAI/Statements.lean`:

| Line | Declaration | Paper |
|---|---|---|
| 99 | `domainEDist` | `d_Λ`, §1.1 |
| 106 | `domainEDiam` | `diam_{d_Λ} X`, eq. (1.1) |
| 111 | `graphNbhd` | `N_r^Λ(D)`, §2.2; `N_l(a)`, §4 |
| 118 | `domainComponent` | component of an anchor, §4.2 (Prop 4.3) |
| 127 | `edgeBoundary` | `∂_Λ A`, §1.1 |
| 132 | `innerBoundary` | `∂_in A`, §1.1 |
| 136 | `cutEndpoints` | `Z_A`, §1.1 |
| 141 | `ambientEDist` | `dist_∞`, §3.2 and Def 9.3 |
| 145 | `ambientDilation` | `T_j`, §2.2 |
| 152 | `Qudits` | `ℂ^q` per site, §1.1 |
| 156 | `supports` | index set of eq. (1.1) |
| 163 | `hamiltonian` | `H = ∑ h_X`, eq. (1.1) |
| 171 | `IsAdmissible` | conditions of eq. (1.1) |
| 177 | `HasGlobalGap` | gap display of Thm 1.1 |
| 183 | `pureState` | `\|Ω⟩⟨Ω\|` |
| 194 | `AreaLaw` | Thm 1.1, eq. (1.2) |
| 211 | `VertexAreaLaw` | Cor 1.2, vertex forms |
| 225 | `AreaLawCorollary` | Cor 1.2 |
| 241 | `condExpect` | `E_{i,l}`, eq. (4.1) |
| 247 | `IsSupportedOn` | "supported on X", §1.1 |
| 260 | `PositiveReplacement` | Prop 4.3, eqs. (4.8), (4.9) |
| 288 | `collarWidth` | `L = ⌊n^{1-10⁻⁵}⌋`, Prop 9.6 |
| 292 | `HasTemplateSlope` | Def 9.3 |
| 298 | `IsTemplatePiece` | Def 9.3 |
| 309 | `IsTemplate` | Def 9.3 |
| 319 | `IsSeparatedFromCut` | Def 9.3 |
| 328 | `CollarBound` | Prop 9.6, eq. (9.16) |
| 364 | `Amplification` | Prop 10.2, eqs. (10.15)–(10.18) |
| 402 | `TwoFamilyCancellation` | Lemma 11.1 |
| 429 | `TwoFamilyDecomposition` | Prop 11.2, eqs. (11.3), (11.4); (11.1) |

Sorried theorems (intended, see Section 4): `area_law` :205, `area_law_corollary` :229,
`positive_replacement` :281, `collar_bound` :349, `amplification` :392,
`two_family_cancellation` :416. Prop 11.2 is a `def … : Prop` with no theorem.

Proved: `instDecidableRelAdjSquareLattice` :91, `graphNbhd_subset` :114,
`domainComponent_subset` :121.

Quantifier order of every Hamiltonian statement: constants first as theorem arguments
(`q R J Δ`, and `p` where present), then `∃ C, ∀ Λ, ∀ Φ, IsAdmissible → ∀ Ω hΩ E₀,
eigen-equation → gap → ∀ A hA`. Theorem 1.1 has not changed since 2b4f982.

## 2. Conventions pinned

### 2.1 Natural logarithm

- Paper: §1.1, "All logarithms are natural", `S_Ω(A) = -Tr ρ_A log ρ_A`, `0 log 0 = 0`.
  Lemma 3.1's `B = 1 + ∑ log²(e d_i)` is a squared natural log (Inventory §6.1).
- Here: `AreaLaw` (:194) bounds `(pureState Ω hΩ).regionEntropy hA`; `SubState.regionEntropy`
  (`Arealaw/Mixed.lean:231`) is `SubState.entropy` (`:84`) of the restriction, which is
  `Arealaw.vonNeumann` (`Arealaw/VonNeumann.lean:29`), natural log. Base 2 is derived
  (`SubState.entropy₂`, `Mixed.lean:88`; `Arealaw.H₂ = H / log 2`, `Arealaw/Entropy.lean:68`),
  never used by OpenAI.
- TNLean: `regionalEntropy` (`TheoremStatements.lean:63`) is QICLean `vonNeumannEntropy`,
  `∑ negMulLog`, natural. Physlib `Sᵥₙ` natural. Agreement everywhere; nothing to bridge.

### 2.2 Edge versus vertex boundary

- Paper: Thm 1.1 uses the edge boundary `∂_Λ A = {{x,y} : x ∈ A, y ∈ Λ∖A, |x−y|₁ = 1}` (§1.1).
  Cor 1.2 adds `∂_in A` and `Z_A = ⋃_{e ∈ ∂_Λ A} e`, with `S ≤ 4C|∂_in A|`, `S ≤ 2C|Z_A|`
  (proof of Cor 1.2: `|∂_in A| ≤ |∂_Λ A| ≤ 4|∂_in A|`, `|Z_A| ≤ 2|∂_Λ A| ≤ 4|Z_A|`). `Z` of §3.2
  and Def 9.3 is `Z_A`.
- Here: `edgeBoundary` :127 is `(hasse ℤ □ hasse ℤ).interedges A (Λ \ A)`, ordered pairs out of
  `A`; its cardinality is the paper's (each unordered crossing edge once). `innerBoundary` :132
  and `cutEndpoints` :136 are its images. Theorem 1.1 is stated with the edge form only;
  vertex forms only in `VertexAreaLaw` :211.
- TNLean: `edgeBoundary : Finset (Sym2 (Site Λ))` (`FiniteDomain.lean:81`), unordered;
  `innerBoundary`, `endpointBoundary` (`BoundaryConventions.lean:32, 39`). Mathlib has no edge
  boundary (`SimpleGraph.edgeBoundary`, `SimpleGraph.cutSet` unknown, Inventory T1.5). Reuse of
  TNLean boundary lemmas needs one cardinality lemma between `interedges` and the `Sym2` form.

### 2.3 `dist` versus `edist`

- Paper: `d_Λ` is graph distance in the induced graph, `+∞` between components (§1.1); the
  support condition of eq. (1.1) is `diam_{d_Λ} X ≤ R` measured in `Λ`, not in `X` ("The distance
  in (1.1) is the distance within the induced graph", §1.1). Distance to the empty set is
  infinite (§3.2). Ambient `dist_∞` for safety (§3.2), templates (Def 9.3) and clearances
  ((10.18), (11.3), (11.4)).
- Here: `domainEDist` :99 is `SimpleGraph.edist` of `(hasse ℤ □ hasse ℤ).induce Λ`, in `ℕ∞`, and
  `⊤` off `Λ`; `domainEDiam` :106 is `⨆ x ∈ X, ⨆ y ∈ X, domainEDist Λ x y`. Ambient distances:
  `ambientEDist` :141 via `Metric.infEDist` (sup metric of `ℤ × ℤ`), `⊤` to `∅`;
  `Metric.ediam` in `IsTemplate` :309.
- Trap: Mathlib `SimpleGraph.dist` is `0` across components
  (`SimpleGraph.dist_eq_zero_of_not_reachable`), so a `dist`-diameter admits disconnected
  supports and enlarges the Hamiltonian class; `SimpleGraph.ediam` is a whole-graph invariant and
  measuring inside `X` shrinks it. Neither is used. `Metric.diam` is `0` on unbounded sets; not
  used.
- This repo's `Arealaw.regionDist` (`Arealaw/Geometry.lean:59`) is `ℕ`-valued with
  `regionDist d ∅ Y = 0`, contradicting §3.2; not used.
- TNLean: walks of length `≤ R` in `domainGraph Λ` (`IsAdmissibleSupport`,
  `FiniteDomain.lean:61`), equivalent to `edist ≤ R` (`exists_walk_length_le_iff_edist_le`,
  `FiniteDomain.lean:131`). Same class.

### 2.4 Direction of the gap and the eigen-equation

- Paper: Thm 1.1 assumes a unique normalized ground vector `Ω` up to phase, ground energy `E₀`,
  and `H − E₀ id ≥ Δ(id − |Ω⟩⟨Ω|)` (unnumbered display in Thm 1.1, §1.1). Prop 4.3 states the
  hypotheses as `HΩ = E₀Ω`, `‖Ω‖ = 1`, `H − E₀I ≥ Δ(I − P_Ω)` (unnumbered display, §4.2);
  (4.8) is its conclusion `H_F ≥ c_*⁻¹(H − E₀I) ≥ g(I − P_Ω)`.
- Here: `HasGlobalGap H Ω E₀ Δ := (Δ : 𝕜) • (1 - vecMulVec Ω (star Ω)) ≤ H - (E₀ : 𝕜) • 1` (:177),
  Mathlib's `MatrixOrder` (`Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef`). Every Hamiltonian
  statement also takes `star Ω ⬝ᵥ Ω = 1` and `hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω` (:198–199).
  Uniqueness up to phase is not a hypothesis: with `Δ > 0` it follows from the three, so omitting
  it does not weaken the theorem (to be proved as a lemma; TNLean has the ℂ version,
  `Matrix.IsGappedGroundState.eigenspace_eq_span`, `Algebra/GappedGroundState.lean:63`).
- The eigen-equation is required. Without it any unit `Ω` satisfies the inequality once
  `E₀ ≤ λ_min(H) − Δ` (then `H − E₀ ≥ Δ·1 ≥ Δ(1 − P_Ω)`), and Theorem 1.1 would assert an area law
  for arbitrary unit vectors, which is false.
- Normalization is `star Ω ⬝ᵥ Ω = 1`, never `‖Ω‖` on `ι → 𝕜` (sup norm).
- TNLean: `Matrix.IsGappedGroundState` (`Algebra/GappedGroundState.lean:45`):
  `‖Ω‖ = 1 ∧ toEuclideanCLM H Ω = E₀ • Ω ∧ PosSemidef (H − E₀•1 − Δ•(1 − vecMulVec Ω (star Ω)))`,
  on `EuclideanSpace ℂ n`. Same proposition up to `Matrix.le_iff` and `WithLp.ofLp`.
- Citation defect to fix in Phase 1: the docstring of `HasGlobalGap` (:175) cites "Theorem 1.1
  and eq. (4.8)"; the hypothesis is the unnumbered display of Thm 1.1 and of Prop 4.3, not (4.8).
  `Statements.lean` is not edited in this step.

### 2.5 Universe of the site Hilbert spaces

- Paper: `ℂ^q` at each site (§1.1).
- Here: sites `ℤ × ℤ`; `Qudits q := fun _ => Fin q` (:152), so `Reg (Qudits q) Λ : Type`.
  `Arealaw.Reg (loc : σ → Type*) (S : Finset σ) := ∀ i : S, loc i` (`Arealaw/Region.lean:42`) is
  universe-polymorphic (`Type (max u_σ u_loc)`); the pin to `Type` comes from `Qudits` alone.
  `TwoFamilyCancellation` :402 keeps general `σ : Type*`, `loc : σ → Type*`. The scalar field
  `𝕜 : Type*` is any `RCLike` field in any universe. `Arealaw.SubState`/`MState`
  (`Mixed.lean:43, 52`) and Physlib `MState (d : Type*)` are polymorphic; the one `Type`-pinned
  family in this repo is `Arealaw.LocP (loc : σ → Type)` (`Arealaw/PurifyChain.lean:37`), not
  used by OpenAI.
- TNLean: `Configuration Λ q := Site Λ → Fin q`, `Type`. No universe bridge needed.

### 2.6 Field

- Paper and TNLean: `ℂ`. Here: `RCLike 𝕜` (charter criterion 3). Physlib entropy and
  `Arealaw/Subadditivity.lean` are `ℂ`-only. See Section 3 and decision 4.3.

## 3. Verdict: statement shape

**Adopt ours (`OpenAI.AreaLaw`), not TNLean's `UniformAreaLaw`; port TNLean proofs behind
bridge lemmas rather than depend on TNLean.**

TNLean `UniformAreaLaw` (`TNLean/PEPS/AreaLaw/TheoremStatements.lean:70`, clone `f4c2d204`):

```
∀ q, 1 ≤ q → ∀ R, ∀ J Δ, 0 < J → 0 < Δ → ∃ C, 0 ≤ C ∧
  ∀ Λ, ∀ h : LocalHamiltonian Λ q R J, ∀ E₀, ∀ Ω : StateSpace Λ q,
    IsGappedGroundState Λ q h.operator E₀ Ω Δ →
    ∀ A : Finset (Site Λ), regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card
```

Comparison with `OpenAI.AreaLaw` (:194) plus `area_law` (:205):

| Axis | TNLean | Ours | Consequence |
|---|---|---|---|
| Quantifiers | `∃ C` after `q R J Δ`, before `Λ h E₀ Ω A` | same | Equivalent. TNLean's `0 ≤ C` is free (replace `C` by `max C 0`; `S ≥ 0`). |
| Field | `ℂ` (`StateSpace := EuclideanSpace ℂ _`, terms `Matrix _ _ ℂ`) | `RCLike 𝕜` | Ours is the charter-required generality. The `𝕜 = ℝ` instance is a consequence of the `ℂ` one, but only through a transfer lemma we do not have yet. |
| Hamiltonian | `structure LocalHamiltonian` (`LocalHamiltonian.lean:45`): `term : AdmissibleSupport Λ R → Matrix (Configuration Λ q) …`, full-domain matrices with a membership proof in `QuantumCircuit.supportedOperators q X` | total family `Φ X : Matrix (Reg X) (Reg X) 𝕜` over every `X`, placed by `Arealaw.extendId` (`Arealaw/PTrace.lean:216`), `IsAdmissible` :171 a separate `Prop` | Same class of `H`. Ours keeps definitions total with side conditions on the theorem (charter, API shape) and reuses this repo's `extendId` algebra. TNLean's encoding needs a bridge: `supportedOperators q X = range (extendId)` after reindexing `Configuration Λ q ≃ Reg (Qudits q) Λ`. |
| Sites and cuts | `Site Λ := ↥Λ`, `A : Finset (Site Λ)` | `A : Finset (ℤ × ℤ)`, `hA : A ⊆ Λ` | Ours composes with `Arealaw`'s region API (`Finset σ` with subset proofs). Bridge: `Finset.subtype`/`map` plus the `interedges`/`Sym2` cardinality lemma (2.2). |
| Graph | hand-written `domainGraph` (`FiniteDomain.lean:47`) | Mathlib `(hasse ℤ □ hasse ℤ).induce Λ` | Ours uses Mathlib's notions (later-phase rule). Bridge: an iso `domainGraph Λ ≃g (hasse ℤ □ hasse ℤ).induce Λ`, short. |
| Gap | `IsGappedGroundState` with `‖Ω‖ = 1` on `EuclideanSpace` | `star Ω ⬝ᵥ Ω = 1`, `H *ᵥ Ω = E₀ • Ω`, `HasGlobalGap` | Same proposition (2.4). |
| Entropy | QICLean `vonNeumannEntropy` of `reducedState` (`Equiv.piEquivPiSubtypeProd` then `Matrix.partialTraceRight`) | `Arealaw.SubState.regionEntropy` via `Arealaw.ptrace` | Both natural log. Bridge: `reducedState` vs `ptrace` after reindexing, and `vonNeumannEntropy` vs `Arealaw.vonNeumann`. |
| Toolchain | Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3` (`c55e6e78`), QICLean `32a5a1a8` | Lean `v4.33.0`, Mathlib `v4.33.0`, Physlib `a50684a1` | TNLean cannot be a lake dependency without moving this repo to v4.35-rc3, and Physlib would have to follow. Reuse means porting files (Apache 2.0, attribution kept) down to v4.33, file by file. |
| Status | statement open; no theorem proves it | sorried theorem | Neither is proved. |

Reuse feasibility of TNLean's proved results (status from Inventory, grep-level `G`, not
elaborated here):

- Prop 4.3: `exists_positiveQuasilocalConstraints` (`PositiveConstraints.lean:133`) is stated on a
  general finite graph with `G.edist`, `ℂ`, terms in `supportedOperators`. Portable in shape;
  depends on QICLean `SpectralFilter` and TNLean Lieb–Robinson modules, so the port is a
  dependency cone, not one file. Needs the `extendId` bridge.
- Lemma 11.1: `OrderedTwoFamilyPartition.entropy_le_residual_add_half_sum`
  (`TwoFamilies.lean:94`) over QICLean `entropy_le_remainder_add_half_sum`
  (`QICLean/Entropy/TwoFamilies.lean:132`), on `EuclideanSpace ℂ ((v : ι) → β v)` with general
  `β`. Ours (`TwoFamilyCancellation` :402) is general in `σ`, `loc`, `𝕜`. Its proof is chain
  rule + purity + subadditivity (§11.1); with a region SSA bridge here it is shorter to prove
  natively than to port.
- Lemma 2.1, Lemma 2.2 degenerate cases, Lemma 3.1, Lemma 3.2, Prop 3.3, Lemma 4.1, Lemma 4.2:
  proved in TNLean/QICLean (Inventory §2), all `ℂ`. Candidates for porting in later phases.
- Props 9.6, 10.2, 11.2 and Theorem 1.1: open in TNLean; nothing to reuse beyond parts.
- `Scan/` results over `ScanData` (`Scan/Defs.lean:256`), whose fields are the conclusions of
  other results, are the "structure with the properties I need" pattern ruled out here; not
  reused.

What carries over unchanged from BH12 (generic in `σ`, `loc` and, except Subadditivity,
`RCLike 𝕜`; elaborated at `σ := ℤ × ℤ`, `loc := Qudits q` per Inventory §5):

- `Arealaw/Region.lean`: `Reg` :42, `restr` :48, `glue` :51, `glueEquiv` :108, `splitEquiv` :122,
  `regEquivOfEq` :155, `sdiffEquiv` :170, `unionEquiv` :183, `univEquiv` :219, `card_reg` :244,
  `card_reg_union` :248, `card_reg_const` :253.
- `Arealaw/PTrace.lean`: `ptrace` :38, `ptrace_self` :44, `ptrace_ptrace` :50, `ptraceₗ` :81,
  `ptrace_eq_traceRight` :118, `ptrace_eq_traceLeft` :127, `ptrace_eq_sum_conj` :159,
  `posSemidef_ptrace` :180, `isHermitian_ptrace` :193, `trace_ptrace` :205, `extendId` :216,
  `extendId_eq_kronecker` :252, `extendId_one` :260, `isHermitian_extendId` :270,
  `posSemidef_extendId` :278, `trace_extendId` :283, `ptrace_mul_extendId` :296,
  `extendId_mul_ptrace` :304, `trace_ptrace_mul` :311, `kronUnion` :325,
  `ptrace_kronUnion_left` :340, `ptrace_kronUnion_right` :355.
- `Arealaw/Mixed.lean`: `SubState` :43, `MState` :52, `MState.mk'` :155, `SubState.restrict` :63,
  `SubState.restrict_restrict` :70, `SubState.entropy` :84, `MState.restrict` :169,
  `MState.entropy_le_log_card` :193, `SubState.regionEntropy` :231, `SubState.mutualInfo` :236,
  `SubState.regionEntropy_empty` :268, `SubState.mutualInfo_comm` :301.
- `Arealaw/Subadditivity.lean` (`ℂ` only, through Physlib): `unionState` :24,
  `regionEntropy_union_le` :50, `mutualInfo_nonneg` :65,
  `abs_regionEntropy_sub_regionEntropy_le` :71, `mutualInfo_le_two_mul_regionEntropy` :80.

What assumes a chain, qubits or `ℕ` distances, and does not carry over:
`Arealaw/Geometry.lean` (`ringDist` :30, `interval` :115, `IsInterval` :135, `IsArc` :145 on
`Fin n`; `regionDist` :59 and `separation` :96 generic in `σ` but `ℕ`-valued with `∅` at distance
0); `Arealaw.Qubits` (`Mixed.lean:320`) and its users `Arealaw/Ladder.lean`,
`Arealaw/Saturation.lean`; `Arealaw/EDC.lean` (1D geometry); `Arealaw.PureState`
(`Arealaw/State.lean`, bipartite coefficient matrix, not a region-indexed ket).

Missing for 2D and owned by this repo if needed (none exists in Mathlib, Physlib or `Arealaw`,
Inventory §5): a three-region bridge (SSA, conditional entropy, CMI on regions, from Physlib
`Sᵥₙ_strong_subadditivity`), region purity `S(A) = S(Λ∖A)`, `extendId_mul`,
`‖extendId A‖ = ‖A‖`. `pureState`, `condExpect`, `IsSupportedOn` (:183, :241, :247) are
region-layer notions living in `OpenAI/` only because Phase 0 does not touch `Arealaw/`.

## 4. Open decisions for the owner

1. **Seventh spine theorem: Lemma 11.1 or Prop 11.2.** §1.3 ("A tensor-network consequence")
   names Prop 4.3, Props 9.6 and 10.2, and Prop 11.2 as the exported results; it does not name
   Lemma 11.1 or Def 9.3 (Def 9.3 enters through Prop 9.6). The brief listed Lemma 11.1. Both are
   stated: `two_family_cancellation` :416 is sorried; `TwoFamilyDecomposition` :429 is a `Prop`
   with no theorem. Choose: keep as is, add `two_family_decomposition` as a seventh sorried
   theorem, or both. §11.8 (proof of Thm 1.1) consumes Props 9.6, 10.2, 11.2, Lemma 11.1 and
   Lemma 2.2.
   (no the project configuration file; an internal tool issue). In this session the tool configuration reports
   process reports `charter   defaults` and `sorried statements   not allowed`, and no
3. **Field generality of proofs.** Statements are over `RCLike 𝕜`. Physlib entropy, this repo's
   Subadditivity and all TNLean/QICLean proofs are `ℂ`. Either prove over `𝕜` (new `RCLike`
   versions of SSA etc.), or prove over `ℂ` and transfer through a reusable embedding lemma set
   (`𝕜 → ℂ` preserves Hermitian, operator norm, Loewner order, the eigen-equation and entropy).
   Recommendation: the transfer, named as a deviation where it is used.
4. **TNLean reuse mode.** Port at v4.33 with attribution versus moving this repo to v4.35-rc3.
   Recommendation: port, file by file, only along the cone a spine theorem needs.

## 5. Phase 1 outline (not started)

Rules carried from the brief: Mathlib and Physlib first, never re-define a notion they have; no
"structure with the properties I need" plus a sorried existence lemma (a hard definition stops
work and goes to the owner); at most 3 workers until `Statements.lean` builds (it does), one
writer per file; commit and push after every step; decisions in `Memory.md`.

1. Owner review of Sections 1–4; resolve 4.1–4.4. Fix the `HasGlobalGap` citation (2.4).
2. Enrol the three proved declarations in an `OpenAI` audit file (`Arealaw/Audit.lean` is BH12
   and stays untouched), so CI gates them.
3. Sanity lemmas on the statement layer, each a named lemma: `domainEDist` agrees with
   `SimpleGraph.edist` on `Λ`; uniqueness of the ground vector from the three hypotheses (2.4);
   `card (edgeBoundary Λ A)` equals the paper's unordered count; `hamiltonian` Hermitian;
   `IsAdmissible` at `R = 0` gives single-site supports.
4. Bridges to TNLean's encoding (2.2, 3): `domainGraph` iso, `supportedOperators` versus
   `extendId`, `reducedState` versus `ptrace`. These decide whether any TNLean proof is portable;
   write them before porting anything.
5. First spine targets by dependency depth: Cor 1.2 from Thm 1.1 (`AreaLaw → VertexAreaLaw`,
   counting only), Lemma 2.2 degenerate cases, Lemma 11.1 natively over a region SSA bridge. Then
   Prop 4.3 by port or native proof, per 4.4.
