# Proposition 10.2 (amplification): plan

Status 2026-10-16: proved, `OpenAI.amplification` (OpenAI/Amplification.lean); see Memory.md.
The "State at freeze" column below records the first copy, not the end state.

Target: `OpenAI.amplification` (OpenAI/Statements.lean:391 at `2413cff`), the frozen
`OpenAI.Amplification 𝕜 q R J Δ p` for every `RCLike 𝕜`, `1 ≤ q`, `0 < J`, `0 < Δ` and every
`p` with `1 - 10⁻⁶ < p / (p + 1)`.  `Amplification` is not changed.  As for Propositions 4.3,
9.6 and 11.2, the sorried theorem leaves Statements.lean and is proved, with the same name and
signature, in its own file (`OpenAI/Amplification.lean`), then enrolled in `OpenAI/Audit.lean`.

## Sources

- Paper: `openai/math@adc7f1241b42`, `09-amplification.tex` (Section 10): Lemma 10.1
  (`lem:amplification-local-products`, lines 42–72), the excited decay
  (`eq:amplification-excited-decay`, 237–253), Proposition 10.2 (261–296, proof 298–576).
- TNLean `LionSR/TNLean@834d8da300df` (2026-10-16) proves Proposition 10.2:
  `TNLean.PEPS.AreaLaw.amplificationBound` (`TNLean/PEPS/AreaLaw/AmplificationProof.lean:103`),
  no `sorry`/`axiom`/`native_decide` in its cone.  Its pin of QICLean is
  `LionSR/QICLean@ed700e7b45ff`.  Clones (read-only, not committed) in
  a scratch directory.
- Route: port the cone file by file at v4.33 (charter: "Port TNLean file by file at v4.33 with
  attribution, only along a spine theorem's cone"), then restate the final theorem for the frozen
  `Amplification ℂ` and transfer to `RCLike 𝕜` through `OpenAI.toComplex`, as
  `OpenAI.collarInformationBound` does.

## Statement comparison

TNLean `AmplificationBound q R J Δ` (`BoundaryTheorem.lean:96`) has the quantifiers of the frozen
statement (`∀ C₀ > 0, ∀ M ≥ 1, ∃ C N, ∀ n ≥ 2, N ≤ n → ∀ Λ h E₀ Ω, gapped → ∀ A T, …`), with
`X = A ∩ T`, `S₀ = A ∩ T_L` as `Finset (Site Λ)` filters, its unordered `edgeBoundary`,
`FiniteProduct.mutualInformation`, `graphNeighborhood Λ (2r) S₀` and the pointwise cut
clearance `∀ t ∈ T, ∀ z ∈ Z_A, L + n^β < dist_∞(t, z)`.  Differences, each to be bridged in the
final file:

- `p`: TNLean fixes `p = 10⁶` (`Exponents.amplificationPower`); its proof uses only `1 ≤ p` and
  `α = p/(p+1)`, plus `α > 1 - 10⁻⁶` for the cut clearance.  The port takes `p` and `hp` as in
  the frozen statement.
- Field: TNLean is over `ℂ`; the frozen statement is over `RCLike 𝕜` (transfer, deviation named
  in place).
- Encodings: `Site Λ`, `LocalHamiltonian`, `IsGappedGroundState`, `edgeBoundary`,
  `boundaryEndpoints`, `graphNeighborhood`, `ambientSupDistance` as in the existing ports
  (`docs/oai265/ports/PortMap.txt` NOTE lines; OpenAI/LatticeConstraints.lean header);
  `FiniteProduct.mutualInformation` versus `SubState.mutualInfo` through
  `OpenAI.Scan.DomainFiniteProduct`.

## The cone

Import closure of `AmplificationProof` minus what the repository already ports (PortMap.txt and
the `Ported from` headers), cut at `BoundaryTheorem` (only the `def AmplificationBound` and the
conditional Theorem 1.1 are used from it), `ZeroBoundary` (one lemma, `trace_reducedState`,
already `FiniteProduct.trace_reducedPure`) and `PEPS/Approximation/SheetSplitting` (four
declarations).  `RectangularTraceNorm`, `SchattenNorm`, `TraceNormAbs`, `TraceNormVariational`
and `Geometry/TemplateRows` are imported but no declaration of theirs is reachable from
`amplificationBound` by name; they are not ported (a porter that needs one ports only that
declaration into the consuming file).  Level = longest import chain within the cone.

Kind `pure`: no TNLean lattice or circuit encoding; copied with header, import and namespace
changes only (`stub.py keep`).  Kind `encoding`: uses `QuantumCircuit.supportedOperators`,
`siteExpectation`, `Configuration`, `Site`, `LocalHamiltonian`, `graphBall`, … and is translated.

| Level | Source module | Lines | Target | Kind | State at freeze |
| --- | --- | --- | --- | --- | --- |
| 0 | `QICLean.Algebra.TaggedInterleavings` | 117 | `OpenAI.TaggedInterleavings` | pure | copied, compiles |
| 0 | `QICLean.Analysis.ContractionWordDecay` | 184 | `OpenAI.ContractionWordDecay` | pure | copied, compiles |
| 0 | `QICLean.Analysis.EntropyDecomposition` | 492 | `OpenAI.EntropyDecomposition` | encoding | to port |
| 0 | `QICLean.Analysis.ExponentialDistanceProfile` | 135 | `OpenAI.ExponentialDistanceProfile` | pure | copied, compiles |
| 0 | `QICLean.Analysis.PolarUnitaryCorrection` | 148 | `OpenAI.PolarUnitaryCorrection` | pure | copied, compiles |
| 0 | `QICLean.Analysis.StretchedExponentialSummability` | 100 | `OpenAI.StretchedExponentialSummability` | pure | copied, compiles |
| 0 | `QICLean.Analysis.SupportInverseSandwich` | 108 | `OpenAI.SupportInverseSandwich` | pure | copied, compiles |
| 0 | `QICLean.Entropy.RestoringMarginal` | 149 | `OpenAI.RestoringMarginal` | pure | copied, errors |
| 0 | `QICLean.Entropy.RestoringOperators` | 328 | `OpenAI.RestoringOperators` | pure | copied, compiles |
| 0 | `QICLean.Probability.PoissonWord` | 200 | `OpenAI.PoissonWord` | pure | copied, compiles |
| 0 | `TNLean.Circuit.SiteEmbedding` | 361 | `OpenAI.SiteEmbedding` | encoding | to port |
| 0 | `TNLean.Circuit.SiteOscillation` | 220 | `OpenAI.SiteOscillation` | encoding | to port |
| 0 | `TNLean.PEPS.AreaLaw.Amplification.EntropyComparison` | 303 | `OpenAI.Amplification.EntropyComparison` | pure | copied, errors |
| 0 | `TNLean.PEPS.AreaLaw.Amplification.GoodRealization` | 335 | `OpenAI.Amplification.GoodRealization` | pure | copied, compiles |
| 0 | `TNLean.PEPS.AreaLaw.GraphExtendedMetric` | 80 | `OpenAI.GraphExtendedMetric` | pure | copied, compiles |
| 0 | `TNLean.PEPS.AreaLaw.GraphNeighborhoodCutClearance` | 97 | `OpenAI.GraphNeighborhoodCutClearance` | encoding | to port |
| 0 | `TNLean.PEPS.AreaLaw.TailParameter` | 220 | `OpenAI.TailParameter` | encoding | to port |
| 0 | `TNLean.PEPS.AreaLaw.ZeroBoundary` | 390 | `OpenAI.ZeroBoundary` | partial | to port |
| 1 | `QICLean.Analysis.ContractionWordDecaySpectator` | 173 | `OpenAI.ContractionWordDecaySpectator` | pure | copied, compiles |
| 1 | `QICLean.Analysis.PolarUnitaryCorrectionKronecker` | 95 | `OpenAI.PolarUnitaryCorrectionKronecker` | pure | copied, compiles |
| 1 | `QICLean.Analysis.RestoringCoefficientBound` | 124 | `OpenAI.RestoringCoefficientBound` | pure | copied, compiles |
| 1 | `QICLean.Entropy.RestoringNorm` | 225 | `OpenAI.RestoringNorm` | pure | copied, errors |
| 1 | `QICLean.Entropy.RestoringVectors` | 467 | `OpenAI.RestoringVectors` | pure | copied, compiles |
| 1 | `QICLean.Probability.PoissonWordAppend` | 145 | `OpenAI.PoissonWordAppend` | pure | copied, compiles |
| 1 | `QICLean.Probability.PoissonWordInsertionWeight` | 129 | `OpenAI.PoissonWordInsertionWeight` | pure | copied, compiles |
| 1 | `QICLean.Probability.PoissonWordRelabel` | 56 | `OpenAI.PoissonWordRelabel` | pure | copied, compiles |
| 1 | `QICLean.Probability.PoissonWordThinning` | 188 | `OpenAI.PoissonWordThinning` | pure | copied, compiles |
| 1 | `TNLean.Circuit.SiteExpectation` | 551 | `OpenAI.SiteExpectation` | encoding | to port |
| 1 | `TNLean.PEPS.AreaLaw.Amplification.AncillaSiteEntropy` | 246 | `OpenAI.Amplification.AncillaSiteEntropy` | encoding | to port |
| 1 | `TNLean.PEPS.AreaLaw.Amplification.RadiusBound` | 94 | `OpenAI.Amplification.RadiusBound` | pure | copied, compiles |
| 1 | `TNLean.PEPS.AreaLaw.Amplification.TypicalProjectors` | 258 | `OpenAI.Amplification.TypicalProjectors` | encoding | to port |
| 1 | `TNLean.PEPS.AreaLaw.AmplificationCutClearance` | 116 | `OpenAI.AmplificationCutClearance` | encoding | to port |
| 2 | `QICLean.Analysis.PoissonContractionDecay` | 82 | `OpenAI.PoissonContractionDecay` | pure | copied, compiles |
| 2 | `QICLean.Entropy.RestoringGroundComponent` | 330 | `OpenAI.RestoringGroundComponent` | pure | copied, errors |
| 2 | `QICLean.Probability.PoissonWordMarked` | 106 | `OpenAI.PoissonWordMarked` | pure | copied, compiles |
| 2 | `QICLean.Probability.PoissonWordPartition` | 114 | `OpenAI.PoissonWordPartition` | pure | copied, compiles |
| 2 | `TNLean.Circuit.LiebRobinson.GraphLocalization` | 250 | `OpenAI.LiebRobinson.GraphLocalization` | encoding | to port |
| 2 | `TNLean.Circuit.SiteExpectationOrder` | 151 | `OpenAI.SiteExpectationOrder` | encoding | to port |
| 2 | `TNLean.Circuit.SpectatorSiteExpectation` | 220 | `OpenAI.SpectatorSiteExpectation` | encoding | to port |
| 2 | `TNLean.PEPS.AreaLaw.Amplification.AncillaTransport` | 399 | `OpenAI.Amplification.AncillaTransport` | pure | copied, compiles |
| 2 | `TNLean.PEPS.AreaLaw.Amplification.GoodRealizationUnitary` | 203 | `OpenAI.Amplification.GoodRealizationUnitary` | pure | copied, compiles |
| 3 | `QICLean.Probability.PoissonWordInsertion` | 114 | `OpenAI.PoissonWordInsertion` | pure | copied, compiles |
| 3 | `QICLean.Probability.PoissonWordWeightedGrowth` | 143 | `OpenAI.PoissonWordWeightedGrowth` | pure | copied, compiles |
| 3 | `TNLean.Circuit.LiebRobinson.GraphBallStabilization` | 73 | `OpenAI.LiebRobinson.GraphBallStabilization` | encoding | to port |
| 3 | `TNLean.Circuit.SpectatorOscillationSupport` | 90 | `OpenAI.SpectatorOscillationSupport` | encoding | to port |
| 3 | `TNLean.PEPS.AreaLaw.Amplification.ConstraintWordLists` | 103 | `OpenAI.Amplification.ConstraintWordLists` | encoding | to port |
| 3 | `TNLean.PEPS.AreaLaw.Amplification.LatticeExcitedDecay` | 67 | `OpenAI.Amplification.LatticeExcitedDecay` | encoding | to port |
| 3 | `TNLean.PEPS.AreaLaw.Amplification.LatticeRestoring` | 735 | `OpenAI.Amplification.LatticeRestoring` | encoding | to port |
| 3 | `TNLean.PEPS.AreaLaw.Amplification.LocalRootChannels` | 267 | `OpenAI.Amplification.LocalRootChannels` | encoding | to port |
| 4 | `QICLean.Probability.PoissonWordOccupation` | 81 | `OpenAI.PoissonWordOccupation` | pure | copied, compiles |
| 4 | `QICLean.Probability.PoissonWordSpatialGrowth` | 79 | `OpenAI.PoissonWordSpatialGrowth` | pure | copied, compiles |
| 4 | `TNLean.Algebra.MatrixL2Contraction` | 144 | `OpenAI.MatrixL2Contraction` | pure | copied, errors |
| 4 | `TNLean.PEPS.AreaLaw.Amplification.ChannelShellOscillation` | 111 | `OpenAI.Amplification.ChannelShellOscillation` | encoding | to port |
| 5 | `QICLean.Probability.PoissonWordRealOccupation` | 209 | `OpenAI.PoissonWordRealOccupation` | pure | copied, compiles |
| 5 | `TNLean.Algebra.MatrixKroneckerContraction` | 184 | `OpenAI.MatrixKroneckerContraction` | pure | copied, errors |
| 5 | `TNLean.PEPS.AreaLaw.Amplification.LocalChannelOscillation` | 148 | `OpenAI.Amplification.LocalChannelOscillation` | encoding | to port |
| 6 | `QICLean.Probability.PoissonWordJump` | 186 | `OpenAI.PoissonWordJump` | pure | copied, compiles |
| 6 | `TNLean.PEPS.Approximation.SheetSplitting` | 427 | `OpenAI.SheetSplitting` | partial | to port |
| 6 | `TNLean.PEPS.AreaLaw.Amplification.ComponentChannelOscillation` | 131 | `OpenAI.Amplification.ComponentChannelOscillation` | encoding | to port |
| 6 | `TNLean.PEPS.AreaLaw.Amplification.ConstraintWordTruncation` | 410 | `OpenAI.Amplification.ConstraintWordTruncation` | encoding | to port |
| 6 | `TNLean.PEPS.AreaLaw.Amplification.ExponentialChannelShells` | 129 | `OpenAI.Amplification.ExponentialChannelShells` | encoding | to port |
| 6 | `TNLean.PEPS.AreaLaw.Amplification.LatticeAncillaTransport` | 450 | `OpenAI.Amplification.LatticeAncillaTransport` | encoding | to port |
| 7 | `TNLean.PEPS.AreaLaw.Amplification.GraphChannelEventError` | 91 | `OpenAI.Amplification.GraphChannelEventError` | encoding | to port |
| 7 | `TNLean.PEPS.AreaLaw.Amplification.GraphChannelOscillation` | 58 | `OpenAI.Amplification.GraphChannelOscillation` | encoding | to port |
| 7 | `TNLean.PEPS.AreaLaw.Amplification.LatticeAncillaSites` | 326 | `OpenAI.Amplification.LatticeAncillaSites` | encoding | to port |
| 7 | `TNLean.PEPS.AreaLaw.Amplification.SupportedPolarCorrection` | 282 | `OpenAI.Amplification.SupportedPolarCorrection` | encoding | to port |
| 8 | `TNLean.PEPS.AreaLaw.Amplification.GraphChannelEventKernel` | 124 | `OpenAI.Amplification.GraphChannelEventKernel` | encoding | to port |
| 8 | `TNLean.PEPS.AreaLaw.AmplificationProofSteps` | 290 | `OpenAI.AmplificationProofSteps` | encoding | to port |
| 9 | `TNLean.PEPS.AreaLaw.Amplification.GraphChannelWeightedRow` | 345 | `OpenAI.Amplification.GraphChannelWeightedRow` | encoding | to port |
| 10 | `TNLean.PEPS.AreaLaw.Amplification.ChannelWordObservables` | 123 | `OpenAI.Amplification.ChannelWordObservables` | encoding | to port |
| 10 | `TNLean.PEPS.AreaLaw.Amplification.GraphOmittedAnchorTail` | 339 | `OpenAI.Amplification.GraphOmittedAnchorTail` | encoding | to port |
| 11 | `TNLean.PEPS.AreaLaw.Amplification.ChannelGroundVectors` | 106 | `OpenAI.Amplification.ChannelGroundVectors` | encoding | to port |
| 11 | `TNLean.PEPS.AreaLaw.Amplification.ChannelWordThinning` | 130 | `OpenAI.Amplification.ChannelWordThinning` | encoding | to port |
| 11 | `TNLean.PEPS.AreaLaw.Amplification.GraphChannelPoissonGrowth` | 149 | `OpenAI.Amplification.GraphChannelPoissonGrowth` | encoding | to port |
| 12 | `TNLean.PEPS.AreaLaw.Amplification.ChannelWordOmission` | 195 | `OpenAI.Amplification.ChannelWordOmission` | encoding | to port |
| 13 | `TNLean.PEPS.AreaLaw.Amplification.GraphChannelSpatialOmission` | 215 | `OpenAI.Amplification.GraphChannelSpatialOmission` | encoding | to port |
| 14 | `TNLean.PEPS.AreaLaw.Amplification.LatticeChannelSpatialOmission` | 227 | `OpenAI.Amplification.LatticeChannelSpatialOmission` | encoding | to port |
| 15 | `TNLean.PEPS.AreaLaw.AmplificationProof` | 448 | `OpenAI.AmplificationProof` | encoding | to port |

## Encodings for the circuit layer

Fixed by the foundation pass (wave 1).  A site set is `σ` with local family `loc` and a region
`T : Finset σ`; operators with a spectator act on `Reg loc T × Aux`; `h : S ⊆ T` is always an
explicit argument.  On the lattice `σ = ℤ × ℤ`, `loc = Qudits q`, `T = Λ`.  TNLean's generic
graph is only ever `domainGraph Λ`, so graph balls are stated for the lattice.

| TNLean | Repository |
|---|---|
| `supportedOperators q K` | `IsSupportedOn (h : K ⊆ T) U` |
| `supportedOperators q Kᶜ` | `IsSupportedOn (Finset.sdiff_subset : T \ K ⊆ T) U` |
| `U ∈ supportedOperators q {y}` | `IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U` |
| `supportedOperators_mono`, `one_mem`, `sub_mem` | `IsSupportedOn.mono` (RegionLift.lean), `isSupportedOn_one`, `IsSupportedOn.sub` (SiteExpectationOrder.lean) |
| `embedOp`, `embedOp_mem_supportedOperators` | `Arealaw.extendId h`, `isSupportedOn_extendId` |
| `siteExpectation q K k` | `condExpect h k`; on balls `condExpect (graphNbhd_subset Λ {a} l) k` |
| `siteExpectation_mem_supportedOperators`, `_of_mem_supportedOperators` | `isSupportedOn_condExpect`, `condExpect_of_isSupportedOn` |
| `siteExpectation_nonneg`, `_le_one`, `_one`, `norm_siteExpectation_le` | `condExpect_nonneg`, `condExpect_le_one`, `condExpect_one`, `norm_condExpect_le` (`ℂ`) |
| `sqrt_mem_supportedOperators K hk₀ hk` | `IsSupportedOn.cfcSqrt` (SiteExpectationOrder.lean) |
| `spectatorSiteExpectation q K B` | `spectatorCondExpect (h : K ⊆ T) B` (SpectatorSiteExpectation.lean); `… q (regions l)ᶜ B` is `spectatorCondExpect (Finset.sdiff_subset : T \ regions l ⊆ T) B` |
| `norm_sub_spectatorSiteExpectation_le` | `norm_sub_spectatorCondExpect_le h B ε hε`, the sum over `T \ S` |
| `spectatorSiteExpectation_eq_self_iff` | `spectatorCondExpect_eq_self_iff` (SpectatorOscillationSupport.lean) |
| `siteOscillation q y B` | `siteOscillation y B`, defined for every `y : σ`, `0` off `T` (SiteOscillation.lean) |
| `siteOscillation_eq_zero_of_not_mem_support`, `_le_support_indicator` | same names, `h : K ⊆ T` first |
| `graphBall (domainGraph Λ) a l`, `mem_graphBall` | `graphNbhd Λ {a} l`, `mem_graphNbhd_singleton_iff_domainEDist_le` (LiebRobinson/GraphBallStabilization.lean) |
| `graphBall_mono`, `notMem_graphBall_of_edist_eq_top` | `graphNbhd_mono`, `notMem_graphNbhd_singleton_of_domainEDist_eq_top` |
| `coe_graphBall_eq_reachable_of_sup_dist_le` | `graphNbhd_singleton_eq_domainComponent_of_sup_le` |
| `spectatorRootChannel k B`, `localRootChannel K k B` | `spectatorRootChannel k B`, `localRootChannel (h : K ⊆ T) k B` (Amplification/LocalRootChannels.lean) |
| `localRootChannelShell regions k l B` | `localRootChannelShell regions (hregions : ∀ l, regions l ⊆ T) k l B` |

`SiteEmbedding`, `SiteExpectation` and `LiebRobinson/GraphLocalization` are not ported: every
declaration downstream uses from them already exists (`Arealaw.extendId_eq_kronecker`,
`OpenAI.extendId_sdiff_submatrix_glueEquiv`, OpenAI/ConditionalExpectation.lean,
`OpenAI.LiebRobinson.norm_heisenberg_sub_condExpect_graphNbhd_le`).

## Waves

1. Pure files: fix the six copied files with errors, prove the two sorried copies
   (`PoissonWord.hasSum_weight_mul_pow`, `Matrix.PosSemidef.supportInv_eq_diagonal`); one
   formalizer per file.  Circuit foundation: one agent, the nine circuit files.
2. Freeze (defs and statements, `sorry` proofs) of the encoding files, by level, once the
   foundation's statements compile.  Judge the freeze against the TNLean statements.
3. Proofs, one formalizer per file, all files in parallel against the frozen signatures.
4. Final file `OpenAI/Amplification.lean`: `amplification_complex` from the ported
   `amplificationBound`, transfer to `𝕜`, removal of the sorried copy from Statements.lean,
   Audit.lean enrolment, umbrella, `lean_check_project`, `axiom_audit`.

Step budget: at most 120 workers runs over all waves.
