# Proposition 9.6, pass 3: the statement freeze (all 13 lemmas now proved)

The remaining proof of `OpenAI.collar_bound` (OpenAI/Statements.lean), decomposed into frozen
lemmas.  `OpenAI.collarBound_of_collarInformationBound` (OpenAI/CollarReduction.lean) reduces it
to `OpenAI.CollarInformationBound`; the chain below proves that from the freeze.

TeX paths are relative to
a scratch directory.
Equation numbers are those of the compiled paper (`08-scanner.tex` numbers (9.1)–(9.20) in
order of appearance: scales (9.1), test geometry (9.2), entropy input (9.4), energy output (9.5),
density (9.6), template entropy (9.11), bootstrap parameters (9.13), bootstrap energy (9.14),
bootstrap comparison (9.15), collar output (9.16), final parameters (9.17), final energy (9.18),
final errors (9.19), entropy identity (9.20)).

## The proved chain

| Declaration | File:line | Content |
| --- | --- | --- |
| `OpenAI.collarInformationBound` | OpenAI/CollarInformation.lean:196 | `CollarInformationBound 𝕜` for every `RCLike 𝕜`, from the `ℂ` case through `OpenAI.toComplex` |
| `OpenAI.collarInformationBound_complex` | OpenAI/CollarInformation.lean:81 | `CollarInformationBound ℂ` from frozen lemma 13, eq. (9.20) (`two_mutualInfo_le_collarLeaf`), leaf averaging, `abs_mutualInfo_sub_le` and `eventually_continuityCost_le_of_fixed_coefficient` |
| `OpenAI.improved_box_estimate` | OpenAI/ImprovedBoxEstimate.lean:83 | Prop 9.5 from Prop 3.3, `exists_boxEntropy_le_rpow_of_eventual_improvement` and the line below |
| `OpenAI.boxEntropy_eventually_improves` | OpenAI/ImprovedBoxEstimate.lean:27 | the `F_box` improvement from frozen lemma 7 (sup over boxes; small boxes cost `N² log q`) |
| `OpenAI.Scan.sourceScan_anchor_card_le` | OpenAI/Scan/SourceScan.lean:87 | anchor multiplicity `≤ 2^{(2R+1)²}`, from `card_filter_mem_supports_le` |
| `OpenAI.Scan.exists_isSchmidtBellLabels` | OpenAI/Scan/SourceScan.lean:218 | `exists_global_schmidtBellPrevector` repackaged |
| `OpenAI.Scan.finalExponents_L` | OpenAI/Scan/SourceScan.lean:122 | final collar depth is `collarWidth` |

New definitions (all total, no `sorry`): `OpenAI.Scan.supportAnchor`, `anchorMultiplicityBound`,
`sourceScan` (the collar scan at the source scales, eq. (9.1)), `finalExponents` (eq. (9.17)),
`bootstrapExponents` (eq. (9.13)), `IsSchmidtBellLabels` (the conclusions of the Schmidt–Bell
selection, eqs. (8.7), (8.15)), all in OpenAI/Scan/SourceScan.lean.

## Frozen lemmas

Each frozen lemma lives in its own file (the file named in its row), except lemmas 8 and 9,
which share OpenAI/Scan/FinalCollarScales.lean, and lemma 13, which sits with the proved chain.

Sizes are Lean lines for the proof, given the existing library and the pass-3 ports.
"Ports" means the TNLean HEAD files being added to OpenAI/Scan/ in parallel
(ActualSharpLower, ActualSharpLowerPrevector, ActualSharpLowerRemainder, ActualMarginalTails,
StatusMarginalMoments, SourceStatusMarginalMoments, TargetGeometry, TargetTypicalWindow,
ScanTruncationInputs, SourceTargetSharpUpper and their deps).

| # | Lean name, file:line | Paper statement | Proof uses | New mathematics | Size |
| --- | --- | --- | --- | --- | --- |
| 1 | `OpenAI.Scan.exists_sourceScan_truncation`, OpenAI/Scan/SourceScanTruncation.lean | the truncated ground state and its scanner inputs: 08-scanner.tex 49–59, 400–414; Prop 4.5 03-quasilocal.tex 405–433; Lemma 2.1 01-preliminaries.tex 33–46; Lemma 3.1 02-initial.tex 34–69; 07-comparators.tex 37–55 | ports `CollarScan.exists_scanTruncation` (ScanTruncationInputs), `exists_truncated_reducedState_moment_tail_bounds` (ActualMarginalTails), `exists_truncated_statusMarginal_moment_bounds`, `exists_truncated_target_typical_window`, `tailRadius_antitone_budget`; repo `conditional_continuity`, `Entropy.typicalSet`, `exp_le_of_mem_typicalSet`, `surprisalMoment_restrict_pureState_eq_finiteProduct`, `regionalEntropy_eq_finiteProduct` | none: restates TNLean's `ScanTruncation` in this repository's vocabulary (D₁ for trace distance, region entropies for `regionalEntropy`, a single parameter `𝓑 = C n D log¹² n`) | 250–450 |
| 2 | `OpenAI.Scan.exists_sourceScan_selection`, OpenAI/Scan/ScannerSelection.lean | Prop 9.2, 08-scanner.tex 349–397 (proof 399–533), energy output (9.5) with density (9.6) | `actualCharges_selection_domainGraph`, `exists_actualFillData_initial_log_filteredNormSq_bound`, `eventually_actualScan_suppliedPrevector_rough_upper` (terminal bound at the charge root `s = nm - 1, p = 1`), `actualCharge_transport_domainGraph` (energy clause), `actualCharge_energyError_le_domainGraph`, `exists_badOldHistory_threshold`, `eventually_scaleFacts`, `exists_actualCharge_energy_coefficients` (final exponents only), `sourceScan_anchor_card_le`, AugmentedReplicaPrevectorProperties (eigenvector equation of `pre` in augmented coordinates) | yes: the scanner estimate for the actual vector; TNLean proves it only from a supplied `ScanData`. The energy-coefficient lemma must be redone for a general `ScannerExponents` (TNLean's is at the final exponents) | 500–800 |
| 3 | `OpenAI.Scan.exists_actualScan_suppliedPrevector_rough_lower`, OpenAI/Scan/ActualRoughLower.lean | Prop 8.1 rough lower (8.9), 07-comparators.tex 166, proof 585–651, as used in (9.15) | `exists_replicaMetric_symProj_bandProduct_rough_lower_norm_three`, the proof of `exists_global_schmidtBellPrevector_rough_lower`, `rootPath_augmented_compressed_bandProduct`, `actualChargeData_leafPart_terminalPartition`, the band-nesting lemmas `state_near_middle_subset_later_near` etc., `actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian`, `norm_filteredVector_actualChargeData`; port ActualSharpLowerPrevector as the template for supplied labels | yes (assembly): TNLean has the rough lower only for the global vector with its own label choice | 300–500 |
| 4 | `OpenAI.Scan.isSafe_test_geometry`, OpenAI/Scan/RectangleTestGeometry.lean | test geometry (9.2) for a safe rectangle, 08-scanner.tex 709–715 | `exists_bootstrap_collar_clearance`, `exists_two_mul_floor_rpow_ceil_mul_le`, SafeRectangleDilation port, `card_Icc_eq_mul`, `lt_ambientEDist_iff` | none beyond rectangle counting | 120–250 |
| 5 | `OpenAI.Scan.isSafe_shell_regionEntropy_le`, OpenAI/Scan/RectangleShellEntropy.lean | rectangle shell entropy, 08-scanner.tex 717–726 | TemplateEntropy's argument (`regionEntropy_inter_le_sum_cappedDyadicPartition`, `cappedDyadicPartition`, `regionEntropy_le_boxEntropy`) with the rectangle mixed-square count; or port TNLean `WeakRectangleShellEntropy`, `RoundedShellEntropy`, `Geometry/CappedDyadicEntropyCover`, `Geometry/RectangleShellWeightedCover` | none (TNLean proves it) | 300–500 |
| 6 | `OpenAI.Scan.sourceScan_bootstrap_entropy_le`, OpenAI/Scan/RectangleBootstrap.lean | the one-step comparison (9.14), (9.15) and lines 752–787 of the proof of Prop 9.5 | lemmas 2, 3; `eventually_actualScan_suppliedPrevector_rough_upper`; `regionalEntropy_le_of_rough_typical_comparisons`; `exists_bootstrap_energy_expression_bound`; `exists_bootstrap_comparison_budget_bound`; `BootstrapParameters.*` | yes: the one-step improvement of Prop 9.5; no reference proves it | 450–700 |
| 7 | `OpenAI.Scan.isSafe_regionEntropy_le_of_boxEntropy_le`, OpenAI/Scan/BoxImprovementStep.lean | the improvement step, 08-scanner.tex 707–790 | lemmas 1, 4, 5, 6; `sourceScan_anchor_card_le`; `exists_isSchmidtBellLabels`; `regionEntropy_le_boxEntropy`; `regionalEntropy_eq_finiteProduct`; `ambientDepth_le_iff_mem_dilation` (positive-depth prefixes are the shells `A ∩ (Q_j \ Q)`) | yes (assembly) | 300–500 |
| 8 | `OpenAI.Scan.eventually_final_energy_le`, OpenAI/Scan/FinalCollarScales.lean | final energy (9.18), 08-scanner.tex 846–859 | `eventually_scaleFacts`, `ScannerExponents.exists_eventually_rpow_le_mul_K`, the pattern of `exists_bootstrap_principal_energy_bound` | scalar arithmetic only | 100–200 |
| 9 | `OpenAI.Scan.eventually_final_collar_errors_le`, OpenAI/Scan/FinalCollarScales.lean | the error table after (9.19), 08-scanner.tex 913–930 | as 9; `Real.binEntropy` bounds as in `exists_bootstrap_binEntropy_cost_bound` | scalar arithmetic only | 150–300 |
| 10 | `OpenAI.Scan.isTemplate_test_geometry`, OpenAI/Scan/TemplateTestGeometry.lean | Lemma 9.4 layer bound (9.10) and the clearance check, 08-scanner.tex 571–621, 833–836 | `IsTemplate.card_ambientDilation_le_sq`, the octagonal-convexity lemmas of OpenAI/Geometry/TemplateCollar.lean (pattern of `IsTemplate.two_mul_sum_card_filter_le`), `lt_ambientEDist_iff`; or TNLean `Geometry/TemplateLayers` restated over `IsTemplate` | none (TNLean proves the layer bound for its `Template`) | 200–400 |
| 11 | `OpenAI.Scan.sourceScan_terminal_regions`, OpenAI/Scan/SourceScanTerminalRegions.lean | the leaf partition `X, U, Y, V`, 08-scanner.tex 83–98, 868 | `state_receiving_regions`, `oldChargeState_receiving_regions`, `state_depth_bounds`, `oldChargeState_depth_bounds`, `middle_eq_positiveNearMiddle_sdiff_positiveNear`, the initial-partition depth lemmas | none | 60–150 |
| 12 | `OpenAI.Scan.sourceScan_collar_leaf_bound`, OpenAI/Scan/CollarComparison.lean | the sharp collar comparison, proof of Prop 9.6, 08-scanner.tex 838–930 (eqs. (9.17)–(9.19), table) | lemmas 2, 8, 9; `exists_actualScan_schmidtBellPrevector_sharp_upper` / `eventually_actualScan_suppliedPrevector_sharp_upper`; port `exists_actualScan_suppliedPrevector_sharp_lower`; `exists_final_a_le_moment_radius`, `final_scanner_moment_margin`; `abs_log_card_and_selectedSchmidtEntropy_sub_le`; SSA (`Arealaw.vonNeumann_strong_subadditivity`) for `0 ≤ g_pre` and the uniform bound `g_pre ≤ C n^{1+e}` | yes: the subtraction of the sharp comparisons at a common point and the replica limit; no reference proves it | 600–800 |
| 13 | `OpenAI.exists_truncated_collar_leaf_family`, OpenAI/CollarInformation.lean | proof of Prop 9.6, 08-scanner.tex 828–944, up to the transfer of line 936 | lemmas 1, 10, 11, 12; `improved_box_estimate`; `templateEntropy_le_of_boxEntropy_le`; `exists_isSchmidtBellLabels`; `IsTemplate.collar_cut_card_le`; `regionalEntropy_eq_finiteProduct`; `finalExponents_L` | yes (assembly); translates the scan's leaves into regions of `ℤ²` | 400–700 |

## Dependency order

Leaves (no frozen prerequisite): 1 (after the ScanTruncationInputs/ActualMarginalTails ports
land), 3, 4, 5, 8, 9, 10, 11.  Then 2.  Then 6 (2, 3) and 12 (2, 8, 9; the sharp-lower
port).  Then 7 (1, 4, 5, 6), which closes `improved_box_estimate`.  Last 13 (1, 10, 11, 12 and
`improved_box_estimate`), which closes `collarInformationBound`.

## Judgment calls

* Every scanner-level lemma takes the truncated ground state, its spectral set and its label
  sequence as supplied data with the properties the paper's argument uses (TNLean's "supplied
  prevector" style); lemma 1 and `exists_isSchmidtBellLabels` supply them.  This keeps one
  label sequence and one vector across the selection and the comparisons.
* The replica remainder `o_k(1)` is "for every `η > 0`, at all large `k`" (lemma 2); the
  limit `k → ∞` is done inside lemmas 6 and 12, whose conclusions are free of `k`.
* The paper's "`C₁` large enough" for the charge capacity is `3 μ_R`, `μ_R = 2^{(2R+1)²}`.
* The trace-distance estimate keeps a fixed coefficient (`≤ C n^{-500}`), as TNLean does.
* Lemma 7 and the final constants are uniform over `D₀ > 2R + 10`: only `D₀ ≥ 10` enters.
* The scanner layer and Prop 9.5 are over `ℂ`; `collarInformationBound` transfers to `𝕜`.
