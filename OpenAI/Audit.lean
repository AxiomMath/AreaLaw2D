import Solution.Basic
import AreaLaw
import AreaLawForMathlib
import OpenAI.Cylinder3D

/-!
# Axiom audit

`lake env lean OpenAI/Audit.lean` prints the axioms of

* the solution of the challenge and the declaration proving each frozen statement of
  `OpenAI/Statements.lean` (the list of `scripts/audit.lean`);
* the two theorems about the statements of `OpenAI/Statements3D.lean`;
* every result of v1's `OpenAI/Audit.lean` (tag `v1.0`) that still exists under the same name;
* for a v1 result that `Map.md` maps to a renamed anchor, that anchor, once.

Each should depend on `propext`, `Classical.choice` and `Quot.sound` only. The v1 results whose
declaration no longer exists are dropped; `MERGE_NOTES.md` gives the counts.
-/

-- The frozen statements.
#print axioms OpenAI.Challenge.area_law
#print axioms AreaLaw.areaLaw
#print axioms AreaLaw.areaLawCorollary
#print axioms AreaLaw.positiveReplacement
#print axioms AreaLaw.collarBound_of_complex
#print axioms AreaLaw.Scanner.prop_9_6
#print axioms AreaLaw.amplification
#print axioms AreaLaw.twoFamilyCancellation
#print axioms AreaLaw.Geometry.prop_11_2
#print axioms AreaLaw.conditionalContinuity
#print axioms AreaLaw.marginalTails
#print axioms AreaLaw.bufferDiscount
#print axioms AreaLaw.initialBoxEstimate

-- The three-dimensional statements.
#print axioms OpenAI.cylinderAreaLawOfPlanar3D
#print axioms OpenAI.cylinderAreaLaw3D

-- Results of v1 renamed in the restructuring, under the anchor name of `Map.md`.
-- v1: `OpenAI.regionEntropy_eq_zero_of_edgeBoundary_eq_empty` (D2.12)
#print axioms AreaLaw.lemma_2_2
-- v1: `OpenAI.regionEntropy_eq_zero_of_range_zero` (D2.11)
#print axioms AreaLaw.step_2_11
-- v1: `OpenAI.two_family_cancellation` (D11.1)
#print axioms AreaLaw.lemma_11_1
-- v1: `OpenAI.norm_deriv_le_of_phase` (D5.18)
#print axioms AreaLaw.step_5_18
-- v1: `OpenAI.norm_sub_re_le_of_phase_bounds` (D5.19)
#print axioms AreaLaw.step_5_19
-- v1: `OpenAI.exists_max_feasible_chain` (D3.7)
#print axioms AreaLaw.step_3_7_1
-- v1: `OpenAI.pow_sqrt_mul_chainOptimum_le` (D3.11)
#print axioms AreaLaw.step_3_11_2
-- v1: `OpenAI.neg_two_mul_log_le_entropy` (D3.13)
#print axioms AreaLaw.eq_initial_norm_upper
-- v1: `OpenAI.two_mul_condEntropy_le` (D3.14)
#print axioms AreaLaw.step_3_14_1
-- v1: `OpenAI.condEntropy_le_initialBuffer_of_constants` (D3.5)
#print axioms AreaLaw.step_3_5
-- v1: `OpenAI.quasilocal_roots` (D4.10)
#print axioms AreaLaw.lemma_4_4
-- v1: `OpenAI.IsAdmissible.sum_norm_extendId_containing_le` (D4.3)
#print axioms AreaLaw.step_4_3
-- v1: `Matrix.exists_posSemidef_gap_of_norm_sub_le` (D4.13)
#print axioms AreaLaw.step_4_13
-- v1: `Matrix.MeanTree.eval_star_conj` (D7.3)
#print axioms AreaLaw.Transport.lemma_7_1
-- v1: `Matrix.MeanTree.eval_listProd_ofFn` (D7.17)
#print axioms AreaLaw.Transport.Round.step_7_17
-- v1: `Matrix.Transport.exists_auxBlock` (D7.21)
#print axioms AreaLaw.Transport.Round.step_7_21
-- v1: `Matrix.Transport.norm_sq_errorVec_le` (D7.23)
#print axioms AreaLaw.Transport.Round.step_7_23
-- v1: `TensorPower.ReplicaTransport.relativePinBound` (D7.18)
#print axioms AreaLaw.Transport.step_7_18
-- v1: `TensorPower.ReplicaTransport.transport` (D7.14)
#print axioms AreaLaw.Transport.prop_7_4
-- v1: `Real.bellOverlapRemainder` (D8.37), `TensorPower.eventually_suppliedSchmidtBell_sharp_upper` (D8.8)
#print axioms AreaLaw.Comparators.prop_8_1
-- v1: `ConditionalMovement.LocalMove.paired_three_lines` (D5.11)
#print axioms AreaLaw.step_5_11
-- v1: `ConditionalMovement.ConditionalCollision.collision_le` (D5.2)
#print axioms AreaLaw.step_5_2_1
-- v1: `ConditionalMovement.ConditionalCollision.one_filter_entropy_bound` (D5.4)
#print axioms AreaLaw.step_5_4_of
-- v1: `ConditionalMovement.ConditionalCollision.conditional_optimizer_root_stability` (D5.7)
#print axioms AreaLaw.step_5_7
-- v1: `ConditionalMovement.MatrixInterpolation.modular_state_distance` (D5.9)
#print axioms AreaLaw.step_5_9_of
-- v1: `ConditionalMovement.ConditionalCollision.left_boundary_trace` (D5.6)
#print axioms AreaLaw.step_5_6
-- v1: `ConditionalMovement.ConditionalCollision.right_boundary_entropy` (D5.10)
#print axioms AreaLaw.step_5_10_1
-- v1: `Entropy.conditionalMovement_norm_le` (D5.5)
#print axioms AreaLaw.lemma_5_1
-- v1: `Matrix.ResolventCompression.defect_nonneg` (D5.13)
#print axioms AreaLaw.step_5_13
-- v1: `Matrix.ResolventCompression.defect_le_invQuadA` (D5.14)
#print axioms AreaLaw.step_5_14
-- v1: `Entropy.MarginalPhase.norm_phaseDifference_mulVec_le` (D5.12)
#print axioms AreaLaw.lemma_5_2
-- v1: `Entropy.ConditionalSkew.imag_vector_eq` (D5.17)
#print axioms AreaLaw.step_5_17
-- v1: `Entropy.ConditionalSkew.phaseRate_le` (D5.20)
#print axioms AreaLaw.step_5_20
-- v1: `Entropy.ConditionalSkew.conditionalSkew_le` (D5.15)
#print axioms AreaLaw.lemma_5_3
-- v1: `OpenAI.collarLeaf_entropy_identity` (D8.36)
#print axioms AreaLaw.Comparators.step_8_36
-- v1: `OpenAI.abs_mutualInfo_sub_le` (D9.30)
#print axioms AreaLaw.Scanner.step_9_30
-- v1: `OpenAI.card_mixedDyadicIndices_le` (D9.17)
#print axioms AreaLaw.Scanner.step_9_17
-- v1: `OpenAI.templateEntropy_le_of_boxEntropy_le` (D9.18)
#print axioms AreaLaw.Scanner.step_9_18
-- v1: `OpenAI.card_latticeDiamond` (D2.7)
#print axioms AreaLaw.eq_ball_count
-- v1: `OpenAI.card_admissibleSupport_containing_le` (D2.8)
#print axioms AreaLaw.step_2_8
-- v1: `TensorPower.exists_commonLabelCutoff_vector` (D8.18)
#print axioms AreaLaw.Comparators.step_8_18
-- v1: `Matrix.floor_pin_le` (D8.32)
#print axioms AreaLaw.Comparators.step_8_32
-- v1: `Matrix.MeanTree.smul_one_sub_add_smul_projection_le_eval` (D8.33)
#print axioms AreaLaw.Comparators.step_8_33
-- v1: `TensorPower.exists_replicaPinnedFactor_le_exp` (D8.16)
#print axioms AreaLaw.Comparators.step_8_16
-- v1: `Entropy.typicalSpectrum_entropy_bounds` (D8.3)
#print axioms AreaLaw.Comparators.step_8_3
-- v1: `TensorPower.exists_label_sequence_mass_entropy_asymptotic` (D8.12)
#print axioms AreaLaw.Comparators.step_8_12
-- v1: `Matrix.MeanTree.re_dotProduct_log_eval_ge_of_projection_mass` (D8.34)
#print axioms AreaLaw.Comparators.step_8_34
-- v1: `Matrix.MeanTree.re_inner_log_eval_prod_le_of_projection` (D8.21)
#print axioms AreaLaw.Comparators.step_8_21
-- v1: `Matrix.PosSemidef.log_re_trace_finKronecker_signed_label_moments_le` (D8.10)
#print axioms AreaLaw.Comparators.step_8_10
-- v1: `Matrix.MeanTree.mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound` (D8.35)
#print axioms AreaLaw.Comparators.step_8_35
-- v1: `Matrix.compression_le_of_replicaExcitationComponent_bounds` (D8.31)
#print axioms AreaLaw.Comparators.step_8_31
-- v1: `Matrix.replicaExcitationComponent_goodAuxiliary_labelEntropy_lower` (D8.27)
#print axioms AreaLaw.Comparators.step_8_27
-- v1: `Matrix.partialTraceLeft_typicalPureState_decomposition` (D8.17)
#print axioms AreaLaw.Comparators.step_8_17
-- v1: `Matrix.selectedBellProjection_bellPinPrevector` (D8.14)
#print axioms AreaLaw.Comparators.step_8_14
-- v1: `TensorPower.exists_replicaMetric_compressed_bell_inverse_norm_bound` (D8.20)
#print axioms AreaLaw.Comparators.step_8_20
-- v1: `TensorPower.selectedBellPost_inverse_norm_le_physical` (D8.15)
#print axioms AreaLaw.Comparators.step_8_15
-- v1: `Matrix.exists_replicaExcitationComponent_inverse_sharp_le` (D8.30)
#print axioms AreaLaw.Comparators.step_8_30
-- v1: `Matrix.replicaGoodConfigurationMarginal_exp_mergeDeficits_le` (D8.29)
#print axioms AreaLaw.Comparators.step_8_29
-- v1: `OpenAI.Scan.exists_bootstrap_principal_energy_bound` (D9.22)
#print axioms AreaLaw.Scanner.step_9_22
-- v1: `OpenAI.exists_latticeCrossingBudget` (D4.14)
#print axioms AreaLaw.step_4_14
-- v1: `OpenAI.Scan.exists_sourceScan_selection` (D9.9)
#print axioms AreaLaw.Scanner.prop_9_2
-- v1: `OpenAI.Scan.exists_sourceScan_selected_density` (D9.12)
#print axioms AreaLaw.Scanner.step_9_12
-- v1: `OpenAI.Scan.exists_sourceScan_energy_le` (D9.13)
#print axioms AreaLaw.Scanner.step_9_13
-- v1: `OpenAI.Scan.isSafe_test_geometry` (D9.21)
#print axioms AreaLaw.Scanner.step_9_21
-- v1: `OpenAI.Scan.isTemplate_test_geometry` (D9.15)
#print axioms AreaLaw.Scanner.lemma_9_4
-- v1: `OpenAI.Scan.eventually_final_collar_errors_le` (D9.29)
#print axioms AreaLaw.Scanner.step_9_29
-- v1: `OpenAI.Scan.exists_bootstrap_comparison_cost_le` (D9.23)
#print axioms AreaLaw.Scanner.step_9_23
-- v1: `OpenAI.Scan.isSafe_regionEntropy_le_of_boxEntropy_le` (D9.24)
#print axioms AreaLaw.Scanner.step_9_24
-- v1: `OpenAI.improved_box_estimate` (D9.19)
#print axioms AreaLaw.Scanner.prop_9_5
-- v1: `OpenAI.amplification` (D10.4)
#print axioms AreaLaw.prop_10_2

-- Results of v1 kept under the same name, in the order and groups of the v1 audit.
-- Domination by a canonical marginal and inverse antitonicity.
#print axioms Matrix.PosDef.inv_le_inv_of_le
#print axioms OpenAI.instDecidableRelAdjSquareLattice
#print axioms OpenAI.graphNbhd_subset
#print axioms OpenAI.domainComponent_subset
#print axioms OpenAI.domainEDist_of_mem
#print axioms OpenAI.domainEDiam_le_iff
#print axioms OpenAI.squareLattice_adj_iff
#print axioms OpenAI.mem_edgeBoundary
#print axioms OpenAI.mem_supports_iff
#print axioms OpenAI.exists_walk_length_le_iff_edist_le
#print axioms Arealaw.SubState.entropy_toComplex
#print axioms Arealaw.SubState.regionEntropy_toComplex
#print axioms Arealaw.SubState.mutualInfo_toComplex
#print axioms OpenAI.pureState_toComplex
#print axioms Arealaw.EE_transpose
#print axioms OpenAI.regionEntropy_pureState
#print axioms Arealaw.MState.regionEntropy_union_le
-- Continuity of the canonical von Neumann entropy along spectral contractions.
#print axioms Matrix.PosSemidef.re_trace_mul_le
#print axioms Matrix.exists_unitary_diagonal_of_commute
#print axioms Arealaw.MState.regionEntropy_le_card_mul_log
#print axioms Matrix.sum_weyl_conj
#print axioms Matrix.complementaryWeylTwirl_eq_smul_traceRight_kronecker_one
#print axioms Matrix.norm_complementaryWeylTwirl_le
#print axioms Matrix.reindexedWeyl_mem_unitary
#print axioms Matrix.inv_sq_smul_sum_sum_const
#print axioms Matrix.norm_sub_complementaryWeylTwirl_le
-- Root-channel support for Lemma 4.4.
#print axioms Matrix.rootChannel_nonneg
#print axioms Matrix.norm_mul_mul_sub_mul_mul_le
#print axioms Matrix.norm_rootChannel_sub_le
#print axioms Matrix.rootChannel_eq_self_of_commute
#print axioms Matrix.sqrt_le_one
-- Lemma 4.4: quasilocal square roots and their channels.
#print axioms OpenAI.condExpect_map_toComplex
-- Proposition 4.3 spectral-filter foundation (QICLean port).
#print axioms CFC.norm_abs_sub_abs_le
-- Proposition 4.5 exact pure-state trace distance.
#print axioms Matrix.abs_eq_inv_sqrt_smul_mul_self
-- Section 7 positive-matrix power calculus.
#print axioms Matrix.PosDef.cfc_log_rpow
#print axioms Matrix.PosDef.cfc_log_mul
#print axioms Matrix.PosSemidef.mul_of_commute
#print axioms Matrix.smul_one_le_mul_of_commute
#print axioms Matrix.pow_smul_one_le_list_prod
#print axioms Matrix.PosDef.rpow
#print axioms Matrix.PosDef.rpow_isHermitian
#print axioms Matrix.PosDef.star_rpow
#print axioms Matrix.PosDef.rpow_mul_rpow
#print axioms Matrix.PosDef.rpow_zero
#print axioms Matrix.PosDef.rpow_one
#print axioms Matrix.PosDef.rpow_mul_rpow_neg
#print axioms Matrix.PosDef.rpow_neg_mul_rpow
#print axioms Matrix.PosDef.rpow_half_mul_rpow_half
#print axioms Matrix.PosDef.rpow_rpow
#print axioms Matrix.PosDef.smul_rpow
#print axioms Matrix.PosDef.commute_rpow
#print axioms Matrix.PosDef.commute_rpow_left
#print axioms Matrix.PosDef.mul_of_commute
#print axioms Matrix.PosDef.mul_rpow_of_commute
-- Section 7 spectral quadratic forms and diagonal Jensen.
#print axioms Matrix.IsHermitian.cfc_form
#print axioms Matrix.IsHermitian.cfc_mul
#print axioms Matrix.IsHermitian.cfc_id
#print axioms Matrix.IsHermitian.trace_cfc_eq_sum
#print axioms Matrix.IsHermitian.trace_cfc_eq_sum_re
#print axioms Matrix.IsHermitian.spectralWeight_nonneg
#print axioms Matrix.IsHermitian.sum_spectralWeight
#print axioms Matrix.IsHermitian.re_dotProduct_cfc_mulVec_eq_sum
#print axioms Matrix.IsHermitian.re_dotProduct_mulVec_eq_sum
#print axioms Matrix.diagonal_jensen_of_convexOn
-- Section 7 weighted geometric mean.
#print axioms Matrix.reindexStarAlgHom_apply
#print axioms Matrix.rpow_conj_unitary
#print axioms Matrix.PosDef.whiten
#print axioms Matrix.PosDef.geomMean
#print axioms Matrix.geomMean_zero
#print axioms Matrix.geomMean_one
#print axioms Matrix.one_geomMean
#print axioms Matrix.geomMean_star_conj
#print axioms Matrix.geomMean_smul
#print axioms Matrix.geomMean_comm
#print axioms Matrix.geomMean_mono_right
#print axioms Matrix.geomMean_mono_left
#print axioms Matrix.re_dotProduct_rpow_mulVec_le
#print axioms Matrix.re_dotProduct_geomMean_le
#print axioms Matrix.Commute.geomMean_right
#print axioms Matrix.geomMean_mul_of_commute
#print axioms Matrix.commute_geomMean_of_commute
-- Section 7 k-positive maps and Bochner integration.
#print axioms singleKrausMap_apply
#print axioms IsNPositiveMap.zero
#print axioms IsNPositiveMap.add
#print axioms IsNPositiveMap.smul_nonneg
#print axioms IsNPositiveMap.comp
#print axioms isNPositiveMap_singleKrausMap
#print axioms nPositiveEval_apply
#print axioms nPositiveEval_eq_ampliation
#print axioms Matrix.PosSemidef.integral_of_ae
#print axioms Matrix.PosSemidef.integral_of_ae'
#print axioms IsNPositiveMap.integral
-- Quantitative Neumann inverse bounds for the Section 7 power derivative.
#print axioms NormedRing.norm_inverse_one_sub_le
#print axioms NormedRing.isUnit_and_norm_inverse_le_of_norm_inverse_mul_sub_le
#print axioms NormedRing.isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le
-- Resolvent form of the Loewner real-power integrand.
#print axioms Matrix.cfc_rpowIntegrand₀₁_eq_resolvent
-- Fréchet derivative of a real power of a positive-definite matrix.
#print axioms Matrix.rpowConst_pos
#print axioms Matrix.integrableOn_rpowIntegrand
#print axioms Matrix.rpow_eq_integral
#print axioms Matrix.PosDef.exists_pos_smul_one_le
#print axioms Matrix.norm_ringInverse_smul_one_add_le
#print axioms Matrix.isStrictlyPositive_smul_one_add
#print axioms Matrix.isUnit_and_norm_ringInverse_le
#print axioms Matrix.rpowFDerivIntegrand_apply
#print axioms Matrix.integrableOn_rpowFDerivIntegrand
#print axioms Matrix.hasFDerivAt_integral_rpowIntegrand
#print axioms Matrix.posSemidef_of_norm_sub_lt
#print axioms Matrix.hasFDerivWithinAt_rpow
#print axioms Matrix.rpowFDeriv_apply
#print axioms Matrix.isNPositiveMap_rpowFDeriv
#print axioms Matrix.rpowFDeriv_self
-- Partial derivatives and normalized derivative maps for weighted geometric means.
#print axioms Matrix.posDef_of_norm_sub_lt
#print axioms Matrix.eventually_posDef_nhdsWithin
#print axioms Matrix.hasFDerivWithinAt_rpow_Icc
#print axioms Matrix.isNPositiveMap_id
#print axioms Matrix.isNPositiveMap_rpowDeriv
#print axioms Matrix.rpowDeriv_self
#print axioms Matrix.sandwichL_apply
#print axioms Matrix.isNPositiveMap_sandwichL
#print axioms Matrix.hasFDerivWithinAt_geomMean_right
#print axioms Matrix.hasFDerivWithinAt_geomMean_left
#print axioms Matrix.geomMeanDerivRight_self
#print axioms Matrix.geomMeanDerivLeft_self
#print axioms Matrix.isNPositiveMap_geomMeanDerivRight
#print axioms Matrix.isNPositiveMap_geomMeanDerivLeft
#print axioms Matrix.normalizedDerivMap_one
#print axioms Matrix.isNPositiveMap_normalizedDerivMap
#print axioms Matrix.normalizedDerivMap_right_one
#print axioms Matrix.normalizedDerivMap_left_one
#print axioms Matrix.isNPositiveMap_normalizedDerivMap_right
#print axioms Matrix.isNPositiveMap_normalizedDerivMap_left
-- Recursive derivatives and normalized leaf-to-root maps of finite mean trees.
#print axioms Matrix.isHermitian_rpow
#print axioms Matrix.isHermitian_geomMean
-- Section 7 hyperbolic-sine Fourier multiplier (Lemma 7.3).
#print axioms Matrix.hermitianUnitaryPath_zero
#print axioms Matrix.continuous_hermitianUnitaryPath
#print axioms Matrix.hermitianUnitaryPath_mul_conjTranspose
#print axioms Real.sinhRatio_zero
#print axioms Real.sinhRatio_of_ne_zero
#print axioms Real.sinhRatioDensity_pos
#print axioms Real.hasDerivAt_sinhRatioDensityPrimitive
#print axioms Real.sinhRatioDensity_neg
#print axioms Real.tendsto_sinhRatioDensityPrimitive_atTop
#print axioms Real.tendsto_sinhRatioDensityPrimitive_atBot
#print axioms Real.integrable_sinhRatioDensity
#print axioms Real.integral_sinhRatioDensity
#print axioms Complex.integral_boundary_rect_inv_sub
#print axioms Complex.integral_boundary_rect_eq_of_simple_poles
#print axioms Complex.cosh_ofReal_add_ofReal_mul_I
#print axioms Complex.cosh_two_pi_mul_add_cos_eq_zero
#print axioms Complex.exists_continuousAt_div_sub_inv
#print axioms Complex.fourierIntegrand_eq
#print axioms Complex.differentiable_densityDenom
#print axioms Complex.deriv_densityDenom
#print axioms Complex.densityDenom_pole₁
#print axioms Complex.densityDenom_pole₂
#print axioms Complex.pole₁_ne_pole₂
#print axioms Complex.deriv_densityDenom_pole₁
#print axioms Complex.deriv_densityDenom_pole₂
#print axioms Complex.differentiable_fourierNumer
#print axioms Complex.two_pi_I_mul_residues
#print axioms Complex.fourierIntegrand_eq_div
#print axioms Complex.densityDenom_ne_zero
#print axioms Complex.rectBoundaryIntegral_fourierIntegrand
#print axioms Complex.abs_sinh_le_norm_cosh
#print axioms Complex.densityDenom_add_I
#print axioms Complex.fourierIntegrand_add_I
#print axioms Complex.norm_fourierIntegrand_ofReal
#print axioms Complex.integrable_fourierIntegrand
#print axioms Complex.norm_fourierIntegrand_vertical_le
#print axioms Complex.tendsto_vertical_fourierIntegrand
#print axioms Complex.integral_exp_mul_sinhRatioDensity
#print axioms Complex.cos_mul_cosh_le_norm_densityDenom
#print axioms Complex.norm_sinhRatioDensity_half_le
#print axioms Complex.norm_fourierIntegrand_half_le
#print axioms Complex.densityDenom_half_ne_zero
#print axioms Complex.integral_exp_mul_sinhRatioDensity_shift
-- Trace pairing, positive maps, and normalized leaf states.
#print axioms Matrix.traceBilinForm_apply
#print axioms Matrix.trace_tracelessPart
#print axioms Matrix.trace_traceAdjointMap_mul
#print axioms Matrix.traceAdjointMap_add
#print axioms Matrix.traceAdjointMap_sub
#print axioms IsPositiveMap.map_conjTranspose
#print axioms isNPositiveMap_one_iff_isPositiveMap
#print axioms Matrix.PosSemidef.of_forall_trace_mul_nonneg
#print axioms IsPositiveMap.traceAdjointMap
-- Block-diagonal calculus and normalized leaf maps.
#print axioms Matrix.cfc_fromBlocks_diag
#print axioms Matrix.PosDef.fromBlocks_diag
#print axioms Matrix.rpow_fromBlocks_diag
#print axioms Matrix.geomMean_fromBlocks_diag
#print axioms Matrix.fromBlocks_diag_mul_blockDiagProj
#print axioms Matrix.IsBlockDiagonalMap.comp
#print axioms Matrix.IsBlockDiagonalMap.add
#print axioms Matrix.IsBlockDiagonalMap.smul
#print axioms Matrix.IsBlockDiagonalMap.zero
#print axioms Matrix.IsBlockDiagonalMap.id
#print axioms Matrix.IsBlockDiagonalMap.toBlocks₁₁
#print axioms Matrix.isBlockDiagonalMap_sandwichL
#print axioms Matrix.ringInverse_smul_one_add_fromBlocks
#print axioms Matrix.isBlockDiagonalMap_rpowFDeriv
#print axioms Matrix.isBlockDiagonalMap_rpowDeriv
#print axioms Matrix.isBlockDiagonalMap_geomMeanDerivRight
#print axioms Matrix.isBlockDiagonalMap_geomMeanDerivLeft
#print axioms Matrix.IsBlockDiagonalMap.normalizedDerivMap
-- Derivatives of weighted geometric means along paths.
#print axioms Matrix.PosDef.rpow_eq_exp_smul_log
#print axioms Matrix.PosDef.hasDerivAt_rpow_exponent
#print axioms Matrix.uniqueDiffWithinAt_hermitianSet
#print axioms Matrix.differentiableWithinAt_rpow_neg_half
#print axioms Matrix.differentiableWithinAt_geomMean
#print axioms Matrix.hasFDerivWithinAt_geomMean_prod
#print axioms Matrix.hasDerivAt_geomMean_of_hasDerivAt
#print axioms Matrix.hasDerivAt_geomMean_param
#print axioms Matrix.geomMean_rpow_self
#print axioms Matrix.geomMeanDerivLeft_sandwich_log
-- Spectral/Fourier formula for the derivative of the filtered norm.
#print axioms Matrix.Transport.sinhRatio_quarter
#print axioms Matrix.Transport.rpow_mul_sinhRatio_quarter
#print axioms Matrix.Transport.quarter_mem_Ioo
#print axioms Matrix.Transport.norm_cexp_I_mul_mul
#print axioms Matrix.Transport.integrable_cexp_mul_fourierWeight
#print axioms Matrix.Transport.integral_fourierWeight_mul_re_sum
#print axioms Matrix.Transport.star_eigU_mul
#print axioms Matrix.Transport.eigU_mul_star
#print axioms Matrix.Transport.cfc_eq_eigen
#print axioms Matrix.Transport.rpow_eq_eigen
#print axioms Matrix.Transport.log_eq_eigen
#print axioms Matrix.Transport.imagPow_eq_eigen
#print axioms Matrix.Transport.star_mulVec_dotProduct_mulVec_of_unitary
#print axioms Matrix.Transport.conj_mulVec_mulVec
#print axioms Matrix.Transport.quadForm_eigen
#print axioms Matrix.Transport.quadForm_imagPow_eq_sum
#print axioms Matrix.Transport.integrable_fourierWeight_mul_re_sum
#print axioms Matrix.Transport.integrable_fourierWeight_mul_quadForm
#print axioms Matrix.Transport.filteredNormSq_eq
#print axioms Matrix.Transport.rpow_neg_half_mul_self_mul
#print axioms Matrix.Transport.exists_hasDerivAt_rpow_neg_half
#print axioms Matrix.Transport.coeff_identity
#print axioms Matrix.Transport.filteredNormSq_pos
#print axioms Matrix.Transport.star_dotProduct_filteredRaw
#print axioms Matrix.Transport.star_dotProduct_filteredVector
#print axioms Matrix.Transport.relation_eigen
#print axioms Matrix.Transport.hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt
-- Commutant invariance of leaf maps and transport states.
#print axioms Matrix.commute_ringInverse_right
#print axioms Matrix.sandwich_mul_right
#print axioms Matrix.rpowDeriv_mul_right
#print axioms Matrix.geomMeanDerivRight_mul_right
#print axioms Matrix.geomMeanDerivLeft_mul_right
#print axioms Matrix.traceAdjointMap_mul_left
#print axioms Matrix.Transport.commute_imagPow
#print axioms Matrix.Transport.mulVec_filteredVector
-- Kadison--Schwarz for the two-positive leaf maps.
#print axioms Matrix.PosSemidef.fromBlocks_diag
#print axioms finTwoSumEquiv_apply_zero
#print axioms finTwoSumEquiv_apply_one
#print axioms finTwoSumEquiv_symm_inl
#print axioms finTwoSumEquiv_symm_inr
#print axioms IsNPositiveMap.isPositiveMap_two
#print axioms kadison_schwarz_twoPositive
-- Fourier representation and generic bound for the transported square.
#print axioms Matrix.Transport.re_star_mulVec_dotProduct_le_of_twoPositive
#print axioms Matrix.Transport.inner_imagPow_eq_sum
#print axioms Matrix.Transport.continuous_inner_imagPow
#print axioms Matrix.Transport.norm_inner_imagPow_le
#print axioms Matrix.Transport.conjTranspose_imagPow_mul_self
#print axioms Matrix.Transport.re_mul_dotProduct_le
#print axioms Matrix.Transport.imagPow_eq_cfc
#print axioms Matrix.Transport.imagPow_fromBlocks_diag
#print axioms Matrix.Transport.star_sumElim_zero_dotProduct
-- Rectangular functional-calculus and vector-pairing identities.
#print axioms Matrix.star_dotProduct_mulVec
#print axioms Matrix.re_star_dotProduct_self_eq_norm_sq
-- Compactness and Haar probability measure on the finite unitary group.
#print axioms Matrix.norm_apply_le_one_of_mem_unitaryGroup
#print axioms Matrix.isCompact_unitaryGroup
#print axioms Matrix.instIsHaarMeasureSubtypeComplexMemSubmonoidUnitaryGroupUnitaryHaar
#print axioms Matrix.instIsProbabilityMeasureSubtypeComplexMemSubmonoidUnitaryGroupUnitaryHaar
-- Functional calculus on the range of a commuting orthogonal projection.
#print axioms Matrix.mul_pow_eq_mul_pow_of_mul_eq
#print axioms Matrix.mul_cfc_eq_mul_cfc_of_mul_eq
#print axioms Matrix.cfc_proj_mul_add
#print axioms Matrix.cfc_proj_mul_add_one_sub
#print axioms Matrix.commute_proj_mul_add_one_sub
#print axioms Matrix.proj_mul_add_one_sub_mul
#print axioms Matrix.commute_proj_mul_add_one_sub_iff
#print axioms Matrix.PosDef.proj_mul_add_one_sub
#print axioms Matrix.PosDef.rpow_proj_mul_add_one_sub
#print axioms Matrix.PosDef.whiten_proj_mul_add_one_sub
#print axioms Matrix.PosDef.le_whiten_proj_mul_add_one_sub
-- Finite permutation representations and their complex group algebras.
#print axioms MonoidAlgebra.invStar_single
#print axioms MonoidAlgebra.coeff_invStar
#print axioms MonoidAlgebra.invStar_invStar
#print axioms PermutationRepresentation.permOp_apply
#print axioms PermutationRepresentation.permOp_apply_apply
#print axioms PermutationRepresentation.conjTranspose_permOp
#print axioms PermutationRepresentation.permOp_mulVec
#print axioms PermutationRepresentation.permOp_inv_mul_self
#print axioms PermutationRepresentation.permOp_mul_inv_self
#print axioms PermutationRepresentation.groupAlgebraRep_single
#print axioms PermutationRepresentation.groupAlgebraRep_eq_sum
#print axioms PermutationRepresentation.groupAlgebraRep_invStar
#print axioms PermutationRepresentation.commute_groupAlgebraRep_of_forall_commute
#print axioms PermutationRepresentation.commute_groupAlgebraRep_of_commute
-- Artin--Wedderburn labels and central idempotents of finite groups.
#print axioms MonoidAlgebra.exists_algEquiv_pi_matrix_complex
#print axioms IrrepLabel.instNeZeroNatDim
#print axioms IrrepLabel.dim_pos
#print axioms IrrepLabel.wedderburnEquiv_centralIdem
#print axioms IrrepLabel.wedderburnEquiv_matrixUnit
#print axioms IrrepLabel.centralIdem_mul_centralIdem
#print axioms IrrepLabel.centralIdem_mul_self
#print axioms IrrepLabel.centralIdem_mul_centralIdem_of_ne
#print axioms IrrepLabel.sum_centralIdem
#print axioms IrrepLabel.centralIdem_mul_comm
#print axioms IrrepLabel.centralIdem_ne_zero
#print axioms IrrepLabel.matrixUnit_mul_matrixUnit
#print axioms IrrepLabel.matrixUnit_mul_matrixUnit_of_ne
#print axioms IrrepLabel.sum_matrixUnit_diag
#print axioms IrrepLabel.centralIdem_mul_matrixUnit
#print axioms IrrepLabel.eq_sum_matrixUnit
#print axioms IrrepLabel.exists_wedderburnEquiv_eq_scalar_of_central
#print axioms IrrepLabel.groupAlgebraRep_regular_apply_one
#print axioms IrrepLabel.groupAlgebraRep_regular_injective
#print axioms IrrepLabel.invStar_centralIdem
-- Isotypic projectors and central observables of permutation representations.
#print axioms PermutationRepresentation.labelProj_mul_labelProj
#print axioms PermutationRepresentation.labelProj_mul_self
#print axioms PermutationRepresentation.labelProj_mul_labelProj_of_ne
#print axioms PermutationRepresentation.sum_labelProj
#print axioms PermutationRepresentation.isHermitian_labelProj
#print axioms PermutationRepresentation.commute_labelProj_groupAlgebraRep
#print axioms PermutationRepresentation.commute_labelProj_permOp
#print axioms PermutationRepresentation.commute_labelProj_of_forall_commute
#print axioms PermutationRepresentation.isHermitian_labelObservable
#print axioms PermutationRepresentation.labelObservable_mul_labelProj
#print axioms PermutationRepresentation.commute_labelObservable_of_forall_commute
-- Copy permutations, invariant subspaces, and subsystem actions on tensor powers.
#print axioms PermutationRepresentation.mem_invariantSubspace
#print axioms PermutationRepresentation.permOp_mul_symProj
#print axioms PermutationRepresentation.symProj_mulVec_mem
#print axioms PermutationRepresentation.symProj_mulVec_of_mem
#print axioms IrrepLabel.coeff_conj_of_mem_center
#print axioms IrrepLabel.coeff_inv_of_mem_center
#print axioms IrrepLabel.centralIdem_mem_center
#print axioms TensorPower.copyPerm_apply
#print axioms TensorPower.subsystemPerm_apply
#print axioms TensorPower.subsystemPerm_univ
#print axioms TensorPower.commute_subsystemPerm_of_disjoint
#print axioms TensorPower.subsystemPerm_union
-- The trivial label and the invariant projector of a finite permutation action.
#print axioms IrrepLabel.augmentation_add
#print axioms IrrepLabel.augmentation_smul
#print axioms IrrepLabel.augmentation_single
#print axioms IrrepLabel.augmentation_sum
#print axioms IrrepLabel.averagingElement_mul
#print axioms IrrepLabel.mul_averagingElement
#print axioms IrrepLabel.augmentation_averagingElement
#print axioms IrrepLabel.augmentation_mul
#print axioms IrrepLabel.averagingElement_ne_zero
#print axioms IrrepLabel.exists_centralIdem_eq_averagingElement
#print axioms PermutationRepresentation.groupAlgebraRep_averagingElement
#print axioms PermutationRepresentation.exists_labelProj_eq_symProj
#print axioms PermutationRepresentation.isStarProjection_symProj
-- Orthogonal resolutions and the spectral projection resolution of a Hermitian matrix.
#print axioms Matrix.IsHermitian.posSemidef_of_mul_self
#print axioms Matrix.IsOrthogonalResolution.mul_self
#print axioms Matrix.IsOrthogonalResolution.mul_of_ne
#print axioms Matrix.IsOrthogonalResolution.sum_smul_mul_sum_smul
#print axioms Matrix.IsOrthogonalResolution.hom_apply
#print axioms Matrix.IsOrthogonalResolution.trace_hom
#print axioms Matrix.IsOrthogonalResolution.continuous_hom
#print axioms Matrix.IsOrthogonalResolution.exp_hom
#print axioms Matrix.IsOrthogonalResolution.prod
#print axioms Matrix.IsOrthogonalResolution.prod_hom_fst
#print axioms Matrix.IsOrthogonalResolution.prod_hom_snd
#print axioms Matrix.IsOrthogonalResolution.isHermitian_hom
#print axioms Matrix.IsOrthogonalResolution.posSemidef_hom
#print axioms Matrix.IsOrthogonalResolution.posSemidef_hom_of_ne_zero
#print axioms Matrix.IsHermitian.mem_eigenvalueSet
#print axioms Matrix.IsHermitian.cfc_eq_sum_smul_spectralProj
#print axioms Matrix.IsHermitian.isHermitian_spectralProj
#print axioms Matrix.IsHermitian.isOrthogonalResolution_spectralProj
#print axioms Matrix.IsHermitian.cfc_eq_hom
#print axioms Matrix.IsHermitian.eq_hom
#print axioms Matrix.IsHermitian.commute_spectralProj
-- Matrix-unit operators and dimensions of isotypic components.
#print axioms PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp
#print axioms PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp_self
#print axioms PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp_of_ne_index
#print axioms PermutationRepresentation.sum_matrixUnitOp_diag
#print axioms PermutationRepresentation.labelProj_mul_matrixUnitOp
#print axioms PermutationRepresentation.groupAlgebraRep_mulVec_mem
#print axioms PermutationRepresentation.dim_le_finrank_of_invariant
#print axioms PermutationRepresentation.trace_eq_finrank_range_of_mul_self
#print axioms PermutationRepresentation.trace_labelProj
-- Commutant dimension and polynomial tensor-power multiplicity bounds.
#print axioms PermutationRepresentation.matrixUnitOp_mul_matrixUnitOp_of_ne
#print axioms PermutationRepresentation.commute_matrixUnitOp_unitAverage
#print axioms PermutationRepresentation.unitAverage_mem_commutant
#print axioms PermutationRepresentation.matrixUnitOp_zero_mul_unitAverage_mul
#print axioms PermutationRepresentation.eq_zero_of_vecMulVec_eq_zero
#print axioms PermutationRepresentation.sum_multiplicity_le_finrank_commutant
#print axioms PermutationRepresentation.apply_eq_of_mem_commutant
#print axioms PermutationRepresentation.finrank_commutant_le_card_pairOrbits
#print axioms TensorPower.pairType_copyPerm
#print axioms TensorPower.exists_copyPerm_of_pairType_eq
#print axioms TensorPower.card_pairOrbits_le
#print axioms TensorPower.sum_multiplicity_le
#print axioms TensorPower.card_labelProj_ne_zero_le
-- Central operators for a permutation representation are label functions.
#print axioms Matrix.exists_eq_smul_of_commute_corner
#print axioms PermutationRepresentation.exists_eq_sum_labelProj_of_commute
-- The copy-permutation commutant lies in the diagonal-action algebra (Schur--Weyl).
#print axioms TensorPower.partialTensor_apply
#print axioms TensorPower.partialTensor_univ_apply
#print axioms TensorPower.partialTensor_empty
#print axioms TensorPower.partialTensor_congr
#print axioms TensorPower.partialTensor_mul_partialTensor
#print axioms TensorPower.commute_partialTensor
#print axioms TensorPower.diagOp_mem_diagAlgebra
#print axioms TensorPower.siteOp_apply
#print axioms TensorPower.siteOp_mul_siteOp
#print axioms TensorPower.siteOp_one
#print axioms TensorPower.siteOp_pow
#print axioms TensorPower.commute_siteOp
#print axioms MvPolynomial.esymm_mem_adjoin_psum
#print axioms TensorPower.tensorPow_mem_diagAlgebra
#print axioms TensorPower.sum_superset_neg_one_pow
#print axioms TensorPower.sum_image_eq_univ_eq_sum_perm
#print axioms TensorPower.tensorPow_sum
#print axioms TensorPower.symTensor_eq_sum
#print axioms TensorPower.symTensor_mem_diagAlgebra
#print axioms TensorPower.eq_smul_sum_symTensor_of_mem_commutant
#print axioms TensorPower.commutant_le_diagAlgebra
-- Highest weights for commutant-invariant tensor-power subspaces.
#print axioms PermutationRepresentation.mem_commutant_of_apply_eq
#print axioms TensorPower.weight_update
#print axioms TensorPower.siteOp_mulVec_apply
#print axioms TensorPower.siteOp_add
#print axioms TensorPower.siteOp_smul
#print axioms TensorPower.siteOp_sub
#print axioms TensorPower.siteOp_zero
#print axioms TensorPower.diagOp_sub
#print axioms TensorPower.diagOp_add
#print axioms TensorPower.diagOp_smul
#print axioms TensorPower.diagOp_zero
#print axioms TensorPower.diagOp_mul_sub_mul
#print axioms TensorPower.diagOp_mem_commutant
#print axioms TensorPower.diagAlgebra_le_commutant
#print axioms TensorPower.gen_mulVec_apply
#print axioms TensorPower.gen_mem_commutant
#print axioms TensorPower.gen_mul_sub_mul
#print axioms TensorPower.isWeightVector_zero
#print axioms TensorPower.IsWeightVector.add
#print axioms TensorPower.IsWeightVector.smul
#print axioms TensorPower.IsWeightVector.gen_mulVec
#print axioms TensorPower.IsWeightVector.gen_self_mulVec
#print axioms TensorPower.toLex_add_single_sub_single_lt
#print axioms TensorPower.monomial_nil
#print axioms TensorPower.monomial_cons
#print axioms TensorPower.monomial_mem_lowerSpan
#print axioms TensorPower.self_mem_lowerSpan
#print axioms TensorPower.IsWeightVector.monomial
#print axioms TensorPower.gen_mulVec_mem_lowerSpan_of_lt
#print axioms TensorPower.IsHighestWeight.gen_mulVec_mem_lowerSpan
#print axioms TensorPower.diagOp_eq_sum_gen
#print axioms TensorPower.isInvariant_of_gen
#print axioms TensorPower.IsHighestWeight.isInvariant_lowerSpan
#print axioms TensorPower.lowerSpan_le
#print axioms TensorPower.weightProj_mulVec_apply
#print axioms TensorPower.IsWeightVector.weightProj_mulVec
#print axioms TensorPower.IsWeightVector.weightProj_mulVec_of_ne
#print axioms TensorPower.isWeightVector_weightProj_mulVec
#print axioms TensorPower.weight_comp_perm
#print axioms TensorPower.weightProj_mem_commutant
#print axioms TensorPower.IsHighestWeight.weightProj_mulVec_mem_span
#print axioms TensorPower.IsIrreducible.lowerSpan_eq
#print axioms TensorPower.IsIrreducible.mem_span_of_isWeightVector
#print axioms TensorPower.IsIrreducible.toLex_le
#print axioms TensorPower.IsIrreducible.weight_eq_of_isHighestWeight
#print axioms TensorPower.exists_isHighestWeight
#print axioms TensorPower.relabel_mulVec_apply
#print axioms TensorPower.relabel_mem_commutant
#print axioms TensorPower.IsWeightVector.relabel_mulVec
#print axioms TensorPower.IsIrreducible.antitone_of_isHighestWeight
-- Differentiated unitary tensor-power symmetries and Schur-label centrality.
#print axioms TensorPower.rotation_mem_unitaryGroup
#print axioms TensorPower.rotation_zero
#print axioms TensorPower.hasDerivAt_rotation_apply
#print axioms TensorPower.diagOp_apply
#print axioms TensorPower.tensorPow_apply
#print axioms TensorPower.hasDerivAt_tensorPow_rotation_apply
#print axioms TensorPower.commute_diagOp_of_commute_tensorPow_rotation
#print axioms TensorPower.diagOp_sum
#print axioms TensorPower.isRotationPair_real
#print axioms TensorPower.isRotationPair_imag
#print axioms TensorPower.isRotationPair_phase
#print axioms TensorPower.commute_diagOp_of_forall_unitary
#print axioms TensorPower.commute_of_mem_commutant_of_forall_unitary
#print axioms TensorPower.exists_eq_sum_labelProj_of_forall_unitary
-- Euclidean operator norm under simultaneous row/column relabelling.
#print axioms Matrix.l2_opNorm_le_of_forall
#print axioms Matrix.l2_opNorm_reindex_le_equiv
#print axioms Matrix.l2_opNorm_reindex_equiv
-- Concrete support interface for replica-site operators.
#print axioms Entropy.IsSupportedOn.apply_eq
-- One-copy operators and subsystem copy permutations.
#print axioms PermutationRepresentation.commute_permOp_of_apply_eq
#print axioms TensorPower.siteOp_eq_reindex
#print axioms TensorPower.l2_opNorm_siteOp_le
#print axioms TensorPower.siteOp_sum
#print axioms TensorPower.conjTranspose_siteOp
#print axioms TensorPower.siteOp_apply_of_isSupportedOn
#print axioms TensorPower.commute_permOp_subsystemPerm_siteOp_of_disjoint
#print axioms TensorPower.commute_permOp_subsystemPerm_siteOp_of_fix
#print axioms TensorPower.permOp_copyPerm_mul_siteOp
-- Haar-unitary twirling and its central Schur-label form.
#print axioms TensorPower.tensorPow_mul
#print axioms TensorPower.tensorPow_one
#print axioms TensorPower.conjTranspose_tensorPow
#print axioms TensorPower.commute_permOp_copyPerm_tensorPow
#print axioms TensorPower.continuous_unitary_apply
#print axioms TensorPower.continuous_twirlIntegrand
#print axioms TensorPower.integrable_twirlIntegrand
#print axioms TensorPower.integral_mul_mul_apply
#print axioms TensorPower.tensorPow_mul_unitaryTwirl
#print axioms TensorPower.commute_unitaryTwirl_tensorPow
#print axioms TensorPower.commute_permOp_unitaryTwirl
#print axioms TensorPower.trace_labelProj_mul_unitaryTwirl
#print axioms TensorPower.unitaryTwirl_eq_sum_labelProj
-- Haar-coherent resolution of the symmetric projector.
#print axioms TensorPower.tensorPow_mulVec_tensorVec
#print axioms TensorPower.tensorVec_mem_symmetricSubspace
#print axioms TensorPower.coherentProj_mulVec
#print axioms TensorPower.commute_permOp_coherentProj
#print axioms TensorPower.eq_zero_of_isHermitian_of_mul_self_of_trace
#print axioms TensorPower.unitaryTwirl_coherentProj
-- Schur-label commutation and complementary-label identities.
#print axioms PermutationRepresentation.commute_groupAlgebraRep_permOp_of_mem_center
#print axioms PermutationRepresentation.permOp_of_eq_mul
#print axioms PermutationRepresentation.commute_groupAlgebraRep_of_eq_mul
#print axioms PermutationRepresentation.groupAlgebraRep_mulVec_eq_of_eq_mul
#print axioms TensorPower.commute_groupAlgebraRep_subsystemPerm_of_disjoint
#print axioms TensorPower.commute_groupAlgebraRep_subsystemPerm_of_subset
#print axioms TensorPower.commute_labelProj_subsystemPerm_of_disjoint
-- Functional calculus and vector weights for orthogonal resolutions.
#print axioms Matrix.IsOrthogonalResolution.hom_const
#print axioms Matrix.IsOrthogonalResolution.aeval_hom
#print axioms Matrix.IsOrthogonalResolution.spectrum_hom_subset
#print axioms Matrix.IsOrthogonalResolution.cfc_hom
#print axioms Matrix.IsOrthogonalResolution.conjTranspose_hom
#print axioms Matrix.IsOrthogonalResolution.l2_opNorm_hom_le
#print axioms Matrix.IsOrthogonalResolution.re_star_dotProduct_hom_mulVec_self
#print axioms Matrix.IsOrthogonalResolution.weight_nonneg
#print axioms Matrix.IsOrthogonalResolution.sum_weight
-- Wendel inequalities for ratios of Gamma values.
#print axioms Real.Gamma_add_le_rpow_mul_Gamma
#print axioms Real.mul_Gamma_le_rpow_mul_Gamma_add
#print axioms Real.Gamma_add_div_Gamma_le_rpow
#print axioms Real.div_rpow_le_Gamma_add_div_Gamma
#print axioms Real.rpow_sub_le_Gamma_add_div_Gamma
-- Hook/Weyl formulas and entropy asymptotics.
#print axioms Real.log_factorial_sub_nonneg
#print axioms Real.log_factorial_sub_le
#print axioms Real.mul_log_add_sub_bounds
#print axioms Partition.shiftedPart_sub_ge
#print axioms Partition.shiftedPart_le
#print axioms Partition.hookFormula_pos
#print axioms Partition.entropyTerm_eq
#print axioms Partition.abs_log_hookFormula_sub_le
#print axioms Partition.abs_log_hookFormula_sub_le_mul_log
-- Common replica label weight and its scalar estimates.
#print axioms Real.abs_log_Gamma_one_add_sub_le
#print axioms Real.log_mul_add_add_two_le
#print axioms Partition.one_le_replicaConst
#print axioms Partition.replicaConst_eq_one_or_two_le
#print axioms Partition.replicaWeight_pos
#print axioms Partition.replicaWeight_zero
#print axioms Partition.replicaWeight_update_succ
#print axioms Partition.exists_abs_log_replicaWeight_add_le
-- Asymptotics and uniform convergence of the marked replica ratio.
#print axioms Real.abs_rpow_sub_rpow_le
#print axioms Partition.replicaRatio_wendel
#print axioms Partition.exists_replicaRatio_bounds
#print axioms Partition.exists_abs_replicaRatio_sub_le
-- Entrywise isometry and finite matrix sum-of-squares identities.
#print axioms Matrix.eq_zero_of_sum_mul_conjTranspose_eq_zero
#print axioms Matrix.eq_zero_of_sum_conjTranspose_mul_self_eq_zero
-- Finite-dimensional complex orthogonal projections and support isometries.
#print axioms IsOrthogonalProjection.isStarProjection
#print axioms IsStarProjection.isOrthogonalProjection
#print axioms IsOrthogonalProjection.one_sub
-- Schur-label entropy and surprisal bounds for permutation-invariant states.
#print axioms PermutationRepresentation.isOrthogonalResolution_labelProj
#print axioms PermutationRepresentation.labelObservable_eq_hom
#print axioms PermutationRepresentation.commute_spectralProj_labelProj
#print axioms PermutationRepresentation.isOrthogonalResolution_joint
#print axioms PermutationRepresentation.isHermitian_joint
#print axioms PermutationRepresentation.joint_hom_fst
#print axioms PermutationRepresentation.joint_hom_snd
#print axioms PermutationRepresentation.trace_joint
#print axioms PermutationRepresentation.eigenvalue_nonneg
#print axioms PermutationRepresentation.mul_dim_le_one_of_ne_zero
#print axioms PermutationRepresentation.supportProj_eq_joint_hom
#print axioms PermutationRepresentation.neg_log_eq_joint_hom
#print axioms PermutationRepresentation.labelEntropy_eq_joint_hom
#print axioms PermutationRepresentation.supportProj_mul_labelEntropy_mul_supportProj_le
#print axioms PermutationRepresentation.re_trace_mul_exp_le_sum_multiplicity
#print axioms TensorPower.schurSurprisal
-- Padded partitions and conjugacy-class counting.
#print axioms Partition.mem_padded
#print axioms Partition.multiset_eq_of_countP_le
#print axioms Partition.lt_card_filter_iff
#print axioms Partition.eq_of_filter_eq
#print axioms Partition.countP_le_countP_of_imp
#print axioms Partition.sum_countP_lt
#print axioms Partition.conjVec_mem_padded
#print axioms Partition.conjVec_injective
#print axioms Partition.card_padded_self
#print axioms Equiv.Perm.nat_card_conjClasses
-- Irreducible-label counting through the centre of the group algebra.
#print axioms IrrepLabel.coeff_classSum
#print axioms IrrepLabel.classSum_mul_comm
#print axioms IrrepLabel.classSum_add
#print axioms IrrepLabel.classSum_smul
#print axioms IrrepLabel.eq_zero_of_central_of_entry
#print axioms IrrepLabel.card_eq_card_conjClasses
-- Single and joint isotypic blocks for commuting finite-group actions.
#print axioms PermutationRepresentation.permOp_comp
#print axioms PermutationRepresentation.permOp_mul_matrixUnitOp
#print axioms PermutationRepresentation.matrixUnitOp_mul_permOp
#print axioms PermutationRepresentation.finrank_blockSpan_le
#print axioms PermutationRepresentation.permOp_mulVec_mem_blockSpan
#print axioms PermutationRepresentation.blockSpan_le_range_labelProj
#print axioms PermutationRepresentation.finrank_pairBlockSpan_le
#print axioms PermutationRepresentation.permOp_mulVec_mem_pairBlockSpan_left
#print axioms PermutationRepresentation.commute_matrixUnitOp_pair
#print axioms PermutationRepresentation.permOp_mulVec_mem_pairBlockSpan_right
#print axioms PermutationRepresentation.mul_dim_le_finrank_of_invariant
-- Highest-weight vectors from Young-diagram column antisymmetrization.
#print axioms Partition.le_of_mem_padded
#print axioms Partition.card_box_row
#print axioms Partition.card_box
#print axioms TensorPower.permOp_mulVec_single
#print axioms TensorPower.gen_mulVec_single
#print axioms TensorPower.sum_sign_smul_single_eq_zero
#print axioms TensorPower.weight_rowConfig
#print axioms TensorPower.isWeightVector_single
#print axioms TensorPower.isWeightVector_columnVector
#print axioms TensorPower.boxEquiv_ext
#print axioms TensorPower.columnVector_apply_rowConfig
#print axioms TensorPower.columnVector_ne_zero
#print axioms TensorPower.gen_mulVec_columnVector
#print axioms TensorPower.isHighestWeight_columnVector
-- Schur-Weyl labels as padded partitions and their multiplicity spaces.
#print axioms TensorPower.unitOp_mulVec_of_mem
#print axioms TensorPower.unitOp_mulVec_mem
#print axioms TensorPower.commute_groupAlgebraRep_of_mem_commutant
#print axioms TensorPower.isInvariant_multSpace
#print axioms TensorPower.isIrreducible_multSpace
#print axioms TensorPower.isWeightVector_iff_weightProj
#print axioms TensorPower.IsHighestWeight.groupAlgebraRep_mulVec
#print axioms TensorPower.exists_isHighestWeight_shape
#print axioms TensorPower.shape_eq_of_isHighestWeight
#print axioms TensorPower.shape_eq_of_labelProj_mulVec_ne_zero
#print axioms TensorPower.sum_weight
#print axioms TensorPower.weight_nonneg
#print axioms TensorPower.shape_props
#print axioms TensorPower.multSpace_ne_bot_of_le
#print axioms TensorPower.cast_labelShape
#print axioms TensorPower.labelShape_mem_padded
#print axioms TensorPower.exists_labelShape_eq
#print axioms TensorPower.card_irrepLabel_perm
#print axioms TensorPower.labelShape_bijective
#print axioms TensorPower.labelShape_injective
-- Finite-group restriction multiplicities and trace factorization.
#print axioms IrrepLabel.block_mul
#print axioms IrrepLabel.branchMatrix_mul_self
#print axioms IrrepLabel.trace_branchMatrix
#print axioms IrrepLabel.trace_block_centralIdem
#print axioms IrrepLabel.dim_eq_sum_branchMult
#print axioms IrrepLabel.sum_dim_sq
#print axioms PermutationRepresentation.groupAlgebraRep_comp
#print axioms PermutationRepresentation.groupAlgebraRep_mul_matrixUnitOp
#print axioms PermutationRepresentation.groupAlgebraRep_mul_labelProj
#print axioms PermutationRepresentation.trace_mul_matrixUnitOp
#print axioms PermutationRepresentation.trace_mul_groupAlgebraRep_mul_labelProj
#print axioms PermutationRepresentation.groupAlgebraRep_mul_labelProj_eq_zero_iff
-- Schur-Weyl multiplicity spaces under enlargement of the one-copy dimension.
#print axioms TensorPower.liftMat_mulVec_apply
#print axioms TensorPower.liftMat_mulVec_comp
#print axioms TensorPower.liftMat_mulVec_injective
#print axioms TensorPower.permOp_mulVec_liftMat
#print axioms TensorPower.groupAlgebraRep_mulVec_liftMat
#print axioms TensorPower.weight_castLE_comp
#print axioms TensorPower.gen_mulVec_liftMat
#print axioms TensorPower.gen_mulVec_liftMat_of_le
#print axioms TensorPower.IsHighestWeight.liftMat
#print axioms TensorPower.labelProj_mulVec_of_mem
#print axioms TensorPower.shape_lift
#print axioms TensorPower.labelShape_truncate_mem
#print axioms TensorPower.multSpace_ne_bot_iff
#print axioms TensorPower.shape_eq_labelShape
#print axioms TensorPower.multSpace_eq_bot_iff
#print axioms TensorPower.labelProj_ne_zero_iff_multSpace
#print axioms TensorPower.labelProj_ne_zero_iff
-- Joint labels for grouped copies and Young-subgroup dimension bounds.
#print axioms PermutationRepresentation.exists_mulVec_ne_zero
#print axioms PermutationRepresentation.commute_labelProj_comp
#print axioms PermutationRepresentation.groupAlgebraRep_comp_mulVec_mem'
#print axioms PermutationRepresentation.comp_commute
#print axioms PermutationRepresentation.groupImage_le
#print axioms PermutationRepresentation.permOp_mulVec_mem_groupImage₁
#print axioms PermutationRepresentation.permOp_mulVec_mem_groupImage₂
#print axioms PermutationRepresentation.labelProj_mulVec_groupImage₁
#print axioms PermutationRepresentation.labelProj_mulVec_groupImage₂
#print axioms PermutationRepresentation.exists_groupImage_ne_bot
#print axioms PermutationRepresentation.mul_dim_le_dim_of_compatible
#print axioms PermutationRepresentation.dim_le_index_mul_of_compatible
#print axioms TensorPower.groupHom_commute
#print axioms TensorPower.noncommCoprod_groupHom
#print axioms TensorPower.youngHom_injective
#print axioms TensorPower.index_range_youngHom
#print axioms TensorPower.groupedCopies_dim
#print axioms TensorPower.groupedCopies_commute
-- Multiplicity-one Pieri branching across the last tensor copy.
#print axioms TensorPower.firstCopies_castSucc
#print axioms TensorPower.firstCopies_last
#print axioms TensorPower.copyPerm_firstCopies_snoc
#print axioms TensorPower.slice_permOp
#print axioms TensorPower.slice_groupAlgebraRep
#print axioms TensorPower.slice_gen
#print axioms TensorPower.weight_snoc
#print axioms TensorPower.IsWeightVector.slice
#print axioms TensorPower.groupAlgebraRep_mulVec_mem_hwSpace
#print axioms TensorPower.slice_firstUnit
#print axioms TensorPower.exists_slice_isHighestWeight
#print axioms TensorPower.finrank_hwSpace_fixed_le_one
#print axioms TensorPower.shape_eq_labelPart
#print axioms TensorPower.branchMult_le_one_and
-- Lagrange-interpolation recursions for hook-formula dimensions.
#print axioms Partition.vand_eq
#print axioms Partition.vand_update_mul
#print axioms Partition.exists_X_sq_mul_prod
#print axioms Partition.sum_mul_prod_sub_one_div
#print axioms Partition.sum_prod_add_one_div
#print axioms Partition.hookFormula_eq_vand
#print axioms Partition.shiftedPart_update
#print axioms Partition.sum_update_sub_one
#print axioms Partition.sum_update_add_one
#print axioms Partition.hookFormula_update_sub_mul
#print axioms Partition.hookFormula_update_add_mul
#print axioms Partition.sum_shiftedPart
#print axioms Partition.shiftedPart_injective
#print axioms Partition.hookFormula_eq_sum_remove
#print axioms Partition.sum_hookFormula_add
#print axioms Partition.shiftedPart_snoc_castSucc
#print axioms Partition.shiftedPart_snoc_last
#print axioms Partition.vand_snoc
#print axioms Partition.hookFormula_snoc
#print axioms Partition.hookFormula_eq_of_le
-- Hook-formula dimensions and exact symmetric-group branching.
#print axioms Partition.hookFormula_nonneg_of_antitone
#print axioms Partition.strictAnti_shiftedPart
#print axioms Partition.hookFormula_update_sub_nonneg
#print axioms Partition.hookFormula_update_add_nonneg
#print axioms TensorPower.labelPart_of_le
#print axioms TensorPower.labelPart_antitone
#print axioms TensorPower.sum_labelPart
#print axioms TensorPower.labelPart_injective
#print axioms TensorPower.hookFormula_part_eq
#print axioms TensorPower.sum_le_sum_of_injOn
#print axioms TensorPower.sum_lt_sum_of_injOn
#print axioms TensorPower.part_eq_of_labelPart_eq
#print axioms TensorPower.part_of_branch
#print axioms TensorPower.exists_branch
#print axioms TensorPower.branchRow_spec
#print axioms TensorPower.dim_cast_eq_sum
#print axioms TensorPower.dim_le_hookFormula
#print axioms TensorPower.sum_hookFormula_mul_dim_le
#print axioms TensorPower.dim_eq_hookFormula_succ
#print axioms TensorPower.dim_eq_hookFormula
#print axioms TensorPower.dim_eq_hookFormula_of_rows
#print axioms TensorPower.branchMult_eq_one_iff
#print axioms TensorPower.branchMult_eq_zero_iff
-- Central transposition sum and the tensor-power Casimir identity.
#print axioms IrrepLabel.single_mul_transpositionSum_mul
#print axioms IrrepLabel.transpositionSum_mul_comm
#print axioms IrrepLabel.wedderburnEquiv_transpositionSum
#print axioms IrrepLabel.transpositionSum_mul_centralIdem
#print axioms TensorPower.update_update_eq_comp_swap
#print axioms TensorPower.groupAlgebraRep_transpositionSum_mulVec_apply
#print axioms TensorPower.sum_gen_mulVec_gen
#print axioms TensorPower.casimir_eq
-- Jucys--Murphy star operator and removable-row eigenvalue.
#print axioms IrrepLabel.firstCopies_swap
#print axioms IrrepLabel.transpositionSum_eq_sum
#print axioms IrrepLabel.two_smul_starElement
#print axioms IrrepLabel.starElement_mul_centralIdem_mul
#print axioms TensorPower.sum_rowPairs_sub
#print axioms TensorPower.casimir_sub_casimir
#print axioms PermutationRepresentation.starOp_eq
#print axioms PermutationRepresentation.starOp_mul_branch
-- Removable-row compatibility, probabilities, and dimension-ratio bounds.
#print axioms IrrepLabel.eq_zero_of_mul_self_of_trace_eq_zero
#print axioms PermutationRepresentation.labelProj_firstCopies
#print axioms PermutationRepresentation.block_restrict_centralIdem_eq_zero_iff
#print axioms PermutationRepresentation.labelProj_mul_labelProj_firstCopies_ne_zero_iff
#print axioms PermutationRepresentation.trace_mul_labelProj_mul_labelProj_firstCopies
#print axioms TensorPower.sum_labelPart_of_rows
#print axioms TensorPower.dim_div_dim_eq
#print axioms TensorPower.sub_one_div_le_two
#print axioms TensorPower.dim_div_dim_le
-- Assembled Schur-label dimension, branch, and star estimates.
#print axioms TensorPower.labelPart_eq_zero_of_labelProj_ne_zero
-- Transport of labels between subsystem actions and tensor powers.
#print axioms PermutationRepresentation.permOp_of_intertwine
#print axioms PermutationRepresentation.groupAlgebraRep_of_intertwine
#print axioms PermutationRepresentation.labelProj_of_intertwine
#print axioms PermutationRepresentation.prodLeft_apply
#print axioms PermutationRepresentation.permOp_prodLeft
#print axioms PermutationRepresentation.groupAlgebraRep_prodLeft
#print axioms PermutationRepresentation.labelProj_prodLeft
#print axioms TensorPower.splitEquiv_subsystemPerm
#print axioms TensorPower.labelProj_subsystemPerm_eq
#print axioms TensorPower.labelProj_copyPerm_equiv
#print axioms TensorPower.labelProj_copyPerm_ne_zero_of_subsystemPerm
#print axioms TensorPower.labelPart_eq_zero_of_subsystemPerm
#print axioms TensorPower.card_subConfig_le
-- Positive subsystem replica metrics and comparison with label entropy.
#print axioms PermutationRepresentation.labelObservable_eq_groupAlgebraRep
#print axioms PermutationRepresentation.sum_smul_centralIdem_mem_center
#print axioms TensorPower.replicaMetric_eq_hom
#print axioms TensorPower.replicaDim_pos
#print axioms TensorPower.replicaLabelWeight_pos
#print axioms TensorPower.posDef_replicaMetric
#print axioms TensorPower.replicaMetric_zero
#print axioms TensorPower.commute_replicaMetric_permOp
#print axioms TensorPower.exists_abs_log_replicaLabelWeight_add_le
#print axioms TensorPower.exists_replicaMetric_comparison
-- Forward marked replica ratio and its star-operator approximation.
#print axioms TensorPower.snocEquiv_apply
#print axioms TensorPower.replicaMetricFirst_eq
#print axioms TensorPower.isOrthogonalResolution_branch
#print axioms TensorPower.isHermitian_branch
#print axioms TensorPower.markedRow_spec
#print axioms TensorPower.starOp_subsystemPerm_eq_hom
#print axioms TensorPower.markedRatio_eq_hom
#print axioms TensorPower.exists_branch_scalars
#print axioms TensorPower.exists_l2_opNorm_markedRatio_sub_le
#print axioms TensorPower.exists_l2_opNorm_markedRatio_le
-- Dimension inequalities for compatible labels on merged disjoint subsystems.
#print axioms PermutationRepresentation.dim_le_mul_dim_of_compatible
#print axioms PermutationRepresentation.permOp_pairAction_mulVec
#print axioms PermutationRepresentation.vecOfMatrix_injective
#print axioms PermutationRepresentation.vecOfMatrix_smul
#print axioms PermutationRepresentation.vecOfMatrix_sum
#print axioms PermutationRepresentation.dim_le_mul_dim_of_compatible'
#print axioms TensorPower.merge_dim_le
-- Conditional merge probabilities and the merge moment.
#print axioms PermutationRepresentation.pairUnit_mul_pairUnit
#print axioms PermutationRepresentation.pairUnit_mul_pairUnit_self
#print axioms PermutationRepresentation.commute_pairUnit
#print axioms PermutationRepresentation.trace_mul_pairUnit
#print axioms PermutationRepresentation.pairUnit_mem_pairUnitSpan
#print axioms PermutationRepresentation.exists_trace_mul_eq
#print axioms PermutationRepresentation.labelProj_mul_labelProj_eq_sum
#print axioms PermutationRepresentation.permOp_mul_permOp_mul_pairUnit_mem
#print axioms PermutationRepresentation.trace_mul_trace_eq
#print axioms PermutationRepresentation.isHermitian_mul_of_commute
#print axioms PermutationRepresentation.re_trace_mul_nonneg
#print axioms PermutationRepresentation.merge_conditional_le
#print axioms PermutationRepresentation.re_trace_merge_nonneg
#print axioms PermutationRepresentation.merge_moment_le_sum_multiplicity
#print axioms TensorPower.copyPerm_eq_mul_compl
#print axioms TensorPower.merge_conditional_le
#print axioms TensorPower.merge_moment_le
-- Inverse marked-ratio estimates on symmetric vectors.
#print axioms TensorPower.commute_permOp_subsystemPerm_of_disjoint
#print axioms TensorPower.trace_complAverage_mul
#print axioms TensorPower.commute_complAverage
#print axioms TensorPower.commute_permOp_compl_labelProj
#print axioms TensorPower.weight_branch
#print axioms TensorPower.card_branch_le
#print axioms TensorPower.sum_le_of_branch
#print axioms TensorPower.markedRatio_inv_eq_hom
#print axioms TensorPower.re_star_dotProduct_branch_hom_mulVec_self
#print axioms TensorPower.branchWeight_nonneg
#print axioms TensorPower.labelWeight_nonneg
#print axioms TensorPower.sum_labelWeight
#print axioms TensorPower.sum_branchWeight
#print axioms TensorPower.branchWeight_eq_zero
#print axioms TensorPower.exists_branch_data
#print axioms TensorPower.exists_norm_markedRatio_inv_mulVec_le
#print axioms TensorPower.exists_markedRatio_inv_sub_clipped_sq_le
#print axioms TensorPower.exists_norm_markedRatio_inv_sub_clipped_le
-- Regional lifts and supported-product decomposition for the concrete replica model.
#print axioms Entropy.localLift_apply
#print axioms Entropy.localLift_add
#print axioms Entropy.localLift_smul
#print axioms Entropy.localLift_eq_reindex_kronecker
#print axioms Entropy.localLift_mul
#print axioms Entropy.localLift_one
#print axioms Entropy.isSupportedOn_localLift
#print axioms Entropy.IsSupportedOn.exists_localLift
#print axioms Entropy.IsSupportedOn.mono
#print axioms Entropy.regionUnionEquiv_apply_fst
#print axioms Entropy.regionUnionEquiv_apply_snd
#print axioms Entropy.localLift_union_kronecker
#print axioms Entropy.localLift_commute_of_disjoint
#print axioms Entropy.IsSupportedOn.exists_sum_mul
-- Similarity transforms of copy means by the partition metric.
#print axioms PermutationRepresentation.commute_labelObservable_of_commute
#print axioms PermutationRepresentation.labelObservable_inv_mul'
#print axioms PermutationRepresentation.labelObservable_inv
#print axioms PermutationRepresentation.labelObservable_mul_inv_self
#print axioms PermutationRepresentation.labelObservable_inv_mul_self
#print axioms TensorPower.replicaMetric_inv_eq
#print axioms TensorPower.commute_replicaMetric_of_disjoint'
#print axioms TensorPower.posDef_leafRoot
#print axioms TensorPower.sqrt_leafMetric
#print axioms TensorPower.commute_copyPerm_labelObservable
#print axioms TensorPower.commute_copyPerm_copyMean
#print axioms TensorPower.star_dotProduct_copyMean_eq
#print axioms TensorPower.norm_mulVec_le
#print axioms TensorPower.norm_star_dotProduct_le
#print axioms TensorPower.commute_labelObservable_siteOp_of_disjoint
#print axioms TensorPower.commute_labelObservable_first_siteOp_last
#print axioms TensorPower.commute_labelObservable_first
#print axioms TensorPower.commute_labelObservable_first_of_disjoint
#print axioms TensorPower.replicaMetric_conj_siteOp_mul
#print axioms TensorPower.markedSimilarity_succ_eq
#print axioms TensorPower.commute_copyPerm_markedSimilarity_succ
#print axioms TensorPower.star_dotProduct_markedSimilarity_eq_sum
#print axioms TensorPower.exists_norm_markedSimilarity_mulVec_le
-- Finite-product coordinates and regional partial traces.
#print axioms FiniteProduct.splitEquiv_apply_fst
#print axioms FiniteProduct.splitEquiv_apply_snd
#print axioms FiniteProduct.splitEquiv_symm_apply_of_mem
#print axioms FiniteProduct.splitEquiv_symm_apply_of_notMem
#print axioms FiniteProduct.configurationCongr_apply
#print axioms FiniteProduct.reducedMatrix_apply
#print axioms FiniteProduct.trace_reducedMatrix
-- Orthogonality of the copy-symmetric averaging projector.
#print axioms TensorPower.symProj_mul_symProj
#print axioms TensorPower.isHermitian_symProj
-- Functional-calculus logarithm of a finite commuting positive product.
#print axioms Matrix.cfc_log_listProd_ofFn
-- Single exceptional-band reduction and the energy estimate under the split-skew hypothesis.
#print axioms Matrix.PosDef.rpow_conj_mul_of_commute
#print axioms Matrix.posDef_list_ofFn_prod
#print axioms Matrix.list_ofFn_prod_rpow_conj
-- Lemma 6.3 in the concrete Loewner form consumed by replica transport.
#print axioms Matrix.smul_vecMulVec_le_of_forall
-- Matrix floor conversion for the sharp lower comparison of Proposition 8.1.
#print axioms Matrix.mul_conjTranspose_le_smul_one_of_conjTranspose_mul_le
#print axioms Matrix.PosDef.inv_smul_projection_le_of_compression_inv_le
#print axioms TensorPower.exists_replicaMetric_inv_square_le_exp
#print axioms TensorPower.groupedCopies_labelEntropy_bounds
#print axioms TensorPower.posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq
#print axioms Matrix.IsHermitian.exp_le_exp_of_commute
#print axioms TensorPower.exp_neg_whole_labelEntropy_le_exp_grouped
#print axioms TensorPower.exists_replicaMetric_inv_square_le_grouped_exp
#print axioms Matrix.IsHermitian.compression_cfc_le_of_lower_bound
#print axioms Matrix.IsHermitian.compression_exp_neg_smul_le_of_lower_bound
-- Spectral calculus for real powers of tensor powers and the compensator norm bound.
#print axioms TensorPower.tensorPow_diagonal
#print axioms TensorPower.tensorPow_conj
#print axioms TensorPower.eq_unitary_conj_diagonal
#print axioms TensorPower.rpow_eq_unitary_conj_diagonal
#print axioms TensorPower.posSemidef_tensorPow
#print axioms TensorPower.tensorPow_rpow
#print axioms TensorPower.trace_tensorPow
#print axioms TensorPower.l2_opNorm_labelObservable_mul_tensorPow_rpow_le
-- Algebraic factorization and inverse Cauchy--Schwarz for a replica move.
#print axioms TensorPower.norm_star_dotProduct_sq_le_inv
#print axioms TensorPower.IsLabelFunctionOn.commute_of_disjoint
#print axioms TensorPower.IsLabelFunctionOn.commute_of_subset
#print axioms TensorPower.isLabelFunctionOn_replicaMetric
#print axioms TensorPower.isLabelFunctionOn_replicaMetric_inv
#print axioms TensorPower.isUnit_det_replicaMetric
#print axioms TensorPower.leafRoot_inv_mul_leafRoot
#print axioms TensorPower.relativeMetric_eq
#print axioms TensorPower.posDef_relativeMetric_and_inv
#print axioms TensorPower.norm_star_dotProduct_sq_le_moveWord
-- Trace convexity and concavity for matrix real powers.
#print axioms Matrix.IsHermitian.sum_dotProduct_eigenvectorBasis_eq_trace
-- Coordinate compression and trace monotonicity of positive matrix real powers.
#print axioms Matrix.conjTranspose_mul_mul_embedMatrix
#print axioms Matrix.star_embedMatrix_mulVec_dotProduct
#print axioms Matrix.IsHermitian.star_eigenvectorBasis_dotProduct_self
#print axioms Matrix.re_trace_rpow_submatrix_le
-- Beta integral transported from the unit interval to the positive half-line.
#print axioms Real.integrableOn_rpow_mul_one_add_rpow
#print axioms Real.integral_rpow_mul_one_add_rpow
-- Interpolation identity and Pieri recursion for the Weyl dimension formula.
#print axioms Partition.weylFormula_eq_vand
#print axioms Partition.rowPairs_denom_pos
#print axioms Partition.weylFormula_zero
#print axioms Partition.weylFormula_eq_zero_of_shiftedPart_eq
#print axioms Partition.weylFormula_update_add_mul
-- Alternants, vertical-strip Pieri, and the dimension-form Vandermonde identity.
#print axioms Partition.indic_injective
#print axioms Partition.alternant_eq_sum
#print axioms Partition.alternant_eq_zero_of_eq
#print axioms Partition.elemSymm_eq_perm
#print axioms Partition.prod_pow_indic
#print axioms Partition.alternant_mul_elemSymm
#print axioms Partition.alternant_geom
#print axioms Partition.X_pow_sub_X_pow
#print axioms Partition.eval_one_geomPoly
#print axioms Partition.alternant_geom_eq
#print axioms Partition.eval_one_elemSymm_geom
#print axioms Partition.eval_one_geomVand
#print axioms Partition.sum_prod_add_indic
#print axioms Partition.prod_Ioi_eq_vand
#print axioms Partition.sum_vand_add_indic
#print axioms Partition.shiftedPart_add_indic
#print axioms Partition.sum_weylFormula_add_indic
-- Orthant gamma integral and its exact replica-weight normalization.
#print axioms Partition.instSigmaFiniteOrthant
#print axioms Partition.ae_orthant_pos
#print axioms Partition.integrable_monomial
#print axioms Partition.integral_monomial
#print axioms Partition.monomial_nonneg
#print axioms Partition.integrable_and_integral_monomial_mul_rpow_sum
#print axioms Partition.integrable_monomial_mul_rpow_sum
#print axioms Partition.integral_monomial_mul_rpow_sum'
#print axioms Partition.alternant_mul_alternant_rpow
#print axioms Partition.Gamma_one_add_add_nat
#print axioms Partition.delta_eq_revPerm
#print axioms Partition.alternant_delta_eq
#print axioms Partition.det_risingPoly
#print axioms Partition.alternant_mul_left
#print axioms Partition.sum_delta
#print axioms Partition.termExp_gt
#print axioms Partition.sum_termExp
#print axioms Partition.gammaIntegrand_eq
#print axioms Partition.gammaIntegral_eq_sum
#print axioms Partition.integrable_gammaIntegrand
#print axioms Partition.sum_sign_prod_Gamma
#print axioms Partition.det_Gamma
#print axioms Partition.gammaIntegral_eq
#print axioms Partition.sign_revPerm_mul_self
#print axioms Partition.alternant_delta_mul_rpow_nonneg
#print axioms Partition.alternant_delta_eq_vand
#print axioms Partition.alternant_delta_ne_zero
#print axioms Partition.cast_delta
#print axioms Partition.sum_shiftedPart_nat
#print axioms Partition.replicaWeight_eq_gammaIntegral
-- Regular-representation traces and the central character projection.
#print axioms PermutationRepresentation.trace_groupAlgebraRep
#print axioms PermutationRepresentation.groupAlgebraRep_regular_apply
#print axioms PermutationRepresentation.trace_groupAlgebraRep_regular
#print axioms PermutationRepresentation.coordEquiv_apply
#print axioms PermutationRepresentation.groupAlgebraRep_regular_mulVec
#print axioms PermutationRepresentation.multiplicity_regular
#print axioms IrrepLabel.block_centralIdem_mul
#print axioms IrrepLabel.card_mul_coeff_centralIdem
#print axioms PermutationRepresentation.characterSum_eq
-- Fixed-word character sums and the Jucys add-one-copy recursion.
#print axioms TensorPower.trace_permOp_inv
#print axioms TensorPower.fixSum_eq_characterSum
#print axioms TensorPower.decomp_last
#print axioms TensorPower.firstCopies_injective
#print axioms TensorPower.decomp_injective
#print axioms TensorPower.decomp_bijective
#print axioms TensorPower.card_filter_snoc
#print axioms TensorPower.snoc_comp_firstCopies
#print axioms TensorPower.snoc_comp_decomp_some
#print axioms TensorPower.fixCount_decomp_none
#print axioms TensorPower.fixCount_decomp_some
#print axioms TensorPower.fixSum_succ
-- Weyl formula for Schur--Weyl multiplicity spaces.
#print axioms TensorPower.fixSum_eq_sum
#print axioms TensorPower.fixSum_mul_centralIdem
#print axioms TensorPower.fixScalar_eq_of_branch
#print axioms TensorPower.multiplicity_eq_weylFormula
-- Split-copy permutation actions and the antisymmetric trace identity.
#print axioms TensorPower.leftCopies_castAdd
#print axioms TensorPower.leftCopies_natAdd
#print axioms TensorPower.rightCopies_castAdd
#print axioms TensorPower.rightCopies_natAdd
#print axioms TensorPower.leftCopies_symm_castAdd
#print axioms TensorPower.leftCopies_symm_natAdd
#print axioms TensorPower.rightCopies_symm_castAdd
#print axioms TensorPower.rightCopies_symm_natAdd
#print axioms TensorPower.leftCopies_mul_rightCopies
#print axioms TensorPower.copyPerm_leftCopies_append
#print axioms TensorPower.copyPerm_rightCopies_append
#print axioms TensorPower.splitOp_append
#print axioms TensorPower.sum_append
#print axioms TensorPower.ext_append
#print axioms TensorPower.splitOp_mul
#print axioms TensorPower.trace_splitOp
#print axioms TensorPower.append_eq_append_iff
#print axioms TensorPower.permOp_leftCopies
#print axioms TensorPower.permOp_rightCopies
#print axioms TensorPower.groupAlgebraRep_leftCopies
#print axioms TensorPower.groupAlgebraRep_rightCopies
#print axioms TensorPower.tensorPow_eq_splitOp
#print axioms TensorPower.sign_mul_sign
#print axioms TensorPower.single_mul_antisym
#print axioms TensorPower.antisym_mul_antisym
#print axioms TensorPower.sum_sign_fix
#print axioms TensorPower.trace_permOp_mul_tensorPow_diagonal
#print axioms TensorPower.card_injective_image_eq
#print axioms TensorPower.sum_injective_prod
#print axioms TensorPower.trace_antisym_mul_tensorPow
-- Exterior Pieri idempotent and rank-one block.
#print axioms TensorPower.restrictHom_left_mul_right
#print axioms TensorPower.leftUnit_mul_self
#print axioms TensorPower.rightAntisym_mul_self
#print axioms TensorPower.pieriElem_mul_self
#print axioms TensorPower.groupAlgebraRep_pieriElem
#print axioms TensorPower.sliceR_splitOp_one
#print axioms TensorPower.sliceR_permOp_rightCopies
#print axioms TensorPower.castAdd_ne_natAdd
#print axioms TensorPower.update_append_castAdd
#print axioms TensorPower.update_append_natAdd
#print axioms TensorPower.sliceR_gen
#print axioms TensorPower.weight_append
#print axioms TensorPower.IsWeightVector.sliceR
#print axioms TensorPower.single_rightCopies_mul_antisym
#print axioms TensorPower.fixed_left_right
#print axioms TensorPower.sliceR_copyPerm_of_fixed
#print axioms TensorPower.sliceR_eq_zero_of_not_injective
#print axioms TensorPower.isPieriVector_of_fixed
#print axioms TensorPower.zSum_update_lt
#print axioms TensorPower.exists_sliceR_isHighestWeight
#print axioms TensorPower.weight_pos_iff
#print axioms TensorPower.exists_copyPerm_of_weight_eq
#print axioms TensorPower.finrank_hwSpace_pieri_le_one
#print axioms TensorPower.trace_block_pieriElem
#print axioms TensorPower.pieriRank_le_one_and
-- Weyl characters and the exterior Pieri rule.
#print axioms TensorPower.multSpace_ne_bot_iff_hasRows
#print axioms TensorPower.unitOp_eq_zero_of_not_hasRows
#print axioms TensorPower.glChar_eq_zero_of_not_hasRows
#print axioms TensorPower.glChar_one
#print axioms TensorPower.multiplicity_pos
#print axioms TensorPower.multiplicity_eq_zero_of_not_hasRows
#print axioms TensorPower.trace_mul_labelProj_eq
#print axioms TensorPower.trace_labelProj_mul_tensorPow
#print axioms TensorPower.trace_mul_tensorPow_eq_sum
#print axioms TensorPower.trace_pieriElem_mul_tensorPow
#print axioms TensorPower.hasRows_iff_part
#print axioms TensorPower.antitone_part
#print axioms TensorPower.sum_part
#print axioms TensorPower.exists_part_eq
#print axioms TensorPower.exists_shiftedPart_eq_of_not_antitone
#print axioms TensorPower.mem_pieriSet
#print axioms TensorPower.sum_pieriSet
#print axioms TensorPower.pieriRank_hasRows_eq_zero_or_mem
#print axioms TensorPower.sum_pieriSet_multiplicity
#print axioms TensorPower.pieriRank_eq_one
#print axioms TensorPower.glChar_mul_elemSymm
#print axioms TensorPower.mem_rowSet
#print axioms TensorPower.mem_rowSet_of_le
#print axioms TensorPower.card_rowSet_lt
#print axioms TensorPower.glChar_of_part_eq_zero
#print axioms TensorPower.alternant_mul_glChar
-- Spectral law for the replica metrics.
#print axioms TensorPower.gammaIntegrand_zero
#print axioms TensorPower.specNorm_eq_integral
#print axioms TensorPower.specDensity_nonneg
#print axioms TensorPower.specNorm_pos
#print axioms TensorPower.measurable_specWeight
#print axioms TensorPower.coe_specWeight_ae
#print axioms TensorPower.isProbabilityMeasure_specMeasure
#print axioms TensorPower.integral_specMeasure
#print axioms TensorPower.ae_specMeasure_pos
#print axioms TensorPower.glChar_mul_left
#print axioms TensorPower.specDensity_mul_glChar
#print axioms TensorPower.specSample_rpow
#print axioms TensorPower.specSample_posDef
#print axioms TensorPower.trace_specSample
#print axioms TensorPower.tensorPow_specSample_rpow_apply
#print axioms TensorPower.measurable_sampleEntry
#print axioms TensorPower.norm_sampleEntry_le
#print axioms TensorPower.ae_prod_pos
#print axioms TensorPower.integral_unitary_sampleEntry
#print axioms TensorPower.integral_specMeasure_label
#print axioms TensorPower.integral_specSample_tensorPow
-- Integral representation of subsystem replica metrics.
#print axioms TensorPower.groupAlgebraRep_comp_embedding
#print axioms TensorPower.exists_replicaMetric_integral
-- Lifted subsystem integral and tensor-power vector estimates.
#print axioms TensorPower.splitEquiv_symm_apply_eq
#print axioms TensorPower.reindex_tensorPow_localLift
#print axioms TensorPower.exists_replicaMetric_integral_localLift
#print axioms TensorPower.norm_tensorVec
#print axioms TensorPower.norm_of_integral_mulVec_le
#print axioms TensorPower.mul_of_integral
-- Polynomial compensator bound for replica moves.
#print axioms TensorPower.reindex_labelObservable_subsystemPerm
#print axioms TensorPower.exists_l2_opNorm_compensator_le
-- Commutation of subsystem labels with local tensor powers.
#print axioms TensorPower.commute_permOp_subsystemPerm_tensorPow_of_subset
#print axioms TensorPower.commute_labelObservable_tensorPow_of_subset
#print axioms TensorPower.commute_labelObservable_tensorPow_of_disjoint
-- Finite-copy coherent-measure identity.
#print axioms TensorPower.tensorVec_split
#print axioms TensorPower.coherentProj_split
#print axioms TensorPower.trace_mul_integral
#print axioms TensorPower.integral_coherent_pairing
-- Operator-norm bounds for positive trace pairings.
#print axioms Matrix.norm_star_dotProduct_mulVec_le
#print axioms Matrix.PosSemidef.norm_trace_mul_le
#print axioms Matrix.l2_opNorm_one_kronecker_le
-- Coherent probability measure and fixed-copy expectations.
#print axioms TensorPower.trace_coherentProj
#print axioms TensorPower.dotProduct_star_unitary_mulVec_single
#print axioms TensorPower.trace_coherentProj_unitary_mulVec_single
#print axioms TensorPower.symProj_mul_of_permOp_mul
#print axioms TensorPower.trace_symProj_ne_zero
#print axioms TensorPower.continuous_trace_mul_coherentProj
#print axioms TensorPower.integral_trace_mul_coherentProj
#print axioms TensorPower.coherentIntegral_one
#print axioms TensorPower.coherentIntegral_trace_coherentProj
#print axioms TensorPower.norm_coherentIntegral_trace_coherentProj_le
-- Fixed-copy placement, injection averages, and exchange permutations.
#print axioms TensorPower.placeSplit_apply_fst
#print axioms TensorPower.placeSplit_apply_snd
#print axioms TensorPower.placeSplit_symm_apply_self
#print axioms TensorPower.placeSplit_symm_apply_of_notMem
#print axioms TensorPower.placeOp_apply
#print axioms TensorPower.placeOp_one
#print axioms TensorPower.l2_opNorm_placeOp_le
#print axioms TensorPower.l2_opNorm_injectionAverage_le
#print axioms TensorPower.injectionSwapFun_castAdd_self
#print axioms TensorPower.injectionSwapFun_castAdd_of_notMem
#print axioms TensorPower.injectionSwapFun_natAdd
#print axioms TensorPower.injectionSwapFun_involutive
#print axioms TensorPower.injectionSwap_apply
#print axioms TensorPower.injectionSwap_inv
#print axioms TensorPower.injectionSwap_mul_self
#print axioms TensorPower.trace_mul_permOp
#print axioms TensorPower.splitCopies_copyPerm_injectionSwap
#print axioms TensorPower.trace_kronecker_mul_injectionSwap
-- Uniform finite-copy Husimi approximation.
#print axioms Matrix.l2_opNorm_permOp_le
#print axioms Equiv.Perm.card_filter_apply_eq_mul
#print axioms TensorPower.sum_goodPerms
#print axioms TensorPower.card_filter_not_goodPerms_mul_le
#print axioms TensorPower.permOp_mul_apply
#print axioms TensorPower.castAdd_restrictFirst
#print axioms TensorPower.permOp_mul_copyKronecker
#print axioms TensorPower.sum_goodPerms_exchangeTrace
#print axioms TensorPower.card_goodPerms
#print axioms TensorPower.sum_goodPerms_exchangeTrace_eq
#print axioms TensorPower.norm_exchangeTrace_le
#print axioms TensorPower.factorial_mul_trace_copyKronecker_mul_symProj
#print axioms TensorPower.le_of_mul_le_of_bad_le
#print axioms TensorPower.norm_trace_mul_injectionAverage_sub_coherentIntegral_le
-- Products of injection averages and their finite-copy approximation.
#print axioms Function.Embedding.card_filter_apply_eq_mul
#print axioms TensorPower.placeOp_apply'
#print axioms TensorPower.copyKronecker_apply
#print axioms TensorPower.l2_opNorm_copyKronecker_le
#print axioms TensorPower.placeOp_castAdd_mul_placeOp_natAdd
#print axioms TensorPower.sum_filter_not_overlapPairs
#print axioms TensorPower.card_filter_not_overlapPairs
#print axioms TensorPower.card_filter_apply_eq_apply_mul
#print axioms TensorPower.card_overlapPairs_mul_le
#print axioms TensorPower.injectionAverage_mul_injectionAverage
#print axioms TensorPower.norm_injectionAverage_mul_sub_le
-- Finite sums of injection averages and their coherent symbols.
#print axioms TensorPower.mul_permOp_apply
#print axioms TensorPower.symm_copyPerm_apply
#print axioms TensorPower.placeOp_trans_perm
#print axioms TensorPower.permOp_mul_injectionAverage
#print axioms TensorPower.commute_symProj_injectionAverage
#print axioms TensorPower.conjTranspose_placeOp
#print axioms TensorPower.conjTranspose_injectionAverage
#print axioms TensorPower.placeOp_smul
#print axioms TensorPower.injectionAverage_smul
#print axioms TensorPower.injectionAverage_zero
#print axioms TensorPower.conjTranspose_coherentProj
#print axioms TensorPower.coherentExpect_conjTranspose
#print axioms TensorPower.coherentExpect_smul
#print axioms TensorPower.coherentExpect_copyKronecker
#print axioms TensorPower.continuous_coherentExpect
#print axioms TensorPower.continuous_unitary_mulVec_single
#print axioms TensorPower.integrable_coherentIntegrand
#print axioms TensorPower.coherentIntegral_sum
#print axioms TensorPower.coherentIntegral_sub
#print axioms TensorPower.norm_coherentIntegral_le
#print axioms TensorPower.IsInjectionPoly.single
#print axioms TensorPower.IsInjectionPoly.const
#print axioms TensorPower.IsInjectionPoly.add
#print axioms TensorPower.IsInjectionPoly.smul
#print axioms TensorPower.IsInjectionPoly.conjTranspose
#print axioms TensorPower.IsInjectionPoly.commute_symProj
#print axioms TensorPower.IsInjectionPoly.norm_le
#print axioms TensorPower.IsInjectionPoly.continuous
#print axioms TensorPower.sum_finProdFinEquiv_symm
#print axioms TensorPower.IsInjectionPoly.exists_mul
#print axioms TensorPower.IsInjectionPoly.exists_norm_trace_sub_coherentIntegral_le
-- Coherent symbols on the symmetric replica subspace.
#print axioms TensorPower.isCompact_unitSphere
#print axioms TensorPower.unitary_mulVec_single_mem_unitSphere
#print axioms TensorPower.l2_opNorm_symProj_le
#print axioms TensorPower.norm_trace_mul_le_of_symmetric
#print axioms TensorPower.IsInjectionPoly.hasCoherentSymbol
#print axioms TensorPower.HasCoherentSymbol.exists_bound
#print axioms TensorPower.HasCoherentSymbol.exists_bound'
#print axioms TensorPower.HasCoherentSymbol.const
#print axioms TensorPower.HasCoherentSymbol.add
#print axioms TensorPower.HasCoherentSymbol.smul
#print axioms TensorPower.HasCoherentSymbol.conjTranspose
#print axioms TensorPower.HasCoherentSymbol.mul_symProj_eq
#print axioms TensorPower.HasCoherentSymbol.mul
#print axioms TensorPower.HasCoherentSymbol.eventually_norm_trace_sub_le
#print axioms TensorPower.HasCoherentSymbol.freeAlgebra
#print axioms TensorPower.l2_opNorm_symProj_mul_mul_symProj_le
#print axioms TensorPower.HasCoherentSymbol.of_approx
#print axioms Matrix.IsHermitian.abs_eigenvalues_le
#print axioms TensorPower.HasCoherentSymbol.pow
#print axioms TensorPower.HasCoherentSymbol.aeval
#print axioms TensorPower.HasCoherentSymbol.symProj_mul
#print axioms TensorPower.HasCoherentSymbol.cfc
#print axioms TensorPower.HasCoherentSymbol.abs
#print axioms TensorPower.HasCoherentSymbol.skew
-- Operator-valued symbols for words with a marked replica copy.
#print axioms TensorPower.singleEmb_apply
#print axioms TensorPower.placeOp_single
#print axioms TensorPower.coherentExpect_oneCopy
#print axioms TensorPower.commute_placeOp_siteOp
#print axioms TensorPower.l2_opNorm_oneCopy
#print axioms TensorPower.norm_injectionAverage_mul_siteOp_sub_le
#print axioms TensorPower.symProj_mul_permOp
#print axioms TensorPower.symProj_mul_siteOp_mul_symProj
#print axioms TensorPower.IsMarkedPoly.norm_le
#print axioms TensorPower.IsMarkedPoly.continuous
#print axioms TensorPower.IsMarkedPoly.center
#print axioms TensorPower.IsMarkedPoly.injection
#print axioms TensorPower.IsMarkedPoly.add
#print axioms TensorPower.IsMarkedPoly.smul
#print axioms TensorPower.IsMarkedPoly.exists_mul
#print axioms TensorPower.IsMarkedPoly.exists_conjTranspose
#print axioms TensorPower.HasMarkedSymbol.of_isMarkedPoly
#print axioms TensorPower.HasMarkedSymbol.norm_le
#print axioms TensorPower.HasMarkedSymbol.continuous
#print axioms TensorPower.HasMarkedSymbol.of_norm_sub_le
#print axioms TensorPower.HasMarkedSymbol.congr_symbol
#print axioms TensorPower.HasMarkedSymbol.center
#print axioms TensorPower.HasMarkedSymbol.injection
#print axioms TensorPower.HasMarkedSymbol.add
#print axioms TensorPower.HasMarkedSymbol.smul
#print axioms TensorPower.HasMarkedSymbol.mul
#print axioms TensorPower.HasMarkedSymbol.conjTranspose
#print axioms TensorPower.HasMarkedSymbol.pow
#print axioms TensorPower.HasMarkedSymbol.aeval
#print axioms TensorPower.HasMarkedSymbol.sum
#print axioms TensorPower.HasMarkedSymbol.symProj_mul_mul_mul_symProj
#print axioms TensorPower.HasMarkedSymbol.norm_symProj_mul_mul_symProj_le
#print axioms TensorPower.HasMarkedSymbol.hasCoherentSymbol_compress
-- Marked symbols of subsystem star operators.
#print axioms TensorPower.regionUnit_apply
#print axioms TensorPower.siteOp_mul_siteOp_apply_of_ne
#print axioms TensorPower.sum_regionUnit_mul_regionUnit
#print axioms TensorPower.permOp_subsystemPerm_swap_eq_sum
#print axioms TensorPower.localLift_sum
#print axioms TensorPower.sum_expect_regionUnit_smul
#print axioms TensorPower.injectionAverage_oneCopy_eq
#print axioms TensorPower.starOp_subsystemPerm_eq
#print axioms TensorPower.hasMarkedSymbol_starOp
-- Powers of canonical one-copy marginals and marked scalar symbols.
#print axioms Entropy.localLift_conjTranspose
#print axioms Entropy.commute_localLift_of_disjoint
#print axioms Entropy.commute_localLift_of_isSupportedOn
#print axioms Entropy.localLift_pow
#print axioms Entropy.aeval_localLift
#print axioms Entropy.l2_opNorm_localLift_le
#print axioms Entropy.star_dotProduct_localLift_mulVec
#print axioms Entropy.trace_margMatrix
#print axioms Matrix.IsHermitian.mul_cfc
#print axioms Matrix.IsHermitian.l2_opNorm_cfc_sub_aeval_le
#print axioms Matrix.IsHermitian.l2_opNorm_cfc_le
#print axioms TensorPower.suppRpow_eq_max_rpow
#print axioms TensorPower.abs_suppRpow_le_one
#print axioms TensorPower.mul_rpow_neg_sq
#print axioms TensorPower.mul_suppRpow_neg_sq_le_one
#print axioms TensorPower.mul_clip_sub_sq_le
#print axioms TensorPower.isHermitian_margMatrix
#print axioms TensorPower.eigenvalues_margMatrix_mem
#print axioms TensorPower.norm_localLift_cfc_mulVec_sq_le
#print axioms TensorPower.localLift_sub
#print axioms TensorPower.norm_eq_one_of_mem_unitSphere
#print axioms TensorPower.l2_opNorm_localLift_cfc_sub_aeval_le
#print axioms TensorPower.norm_sandwich_sub_le
#print axioms TensorPower.norm_star_dotProduct_sub_le
#print axioms TensorPower.l2_opNorm_regionPow_le_one
#print axioms TensorPower.norm_regionPow_neg_mulVec_le
#print axioms TensorPower.isHermitian_regionPow
#print axioms TensorPower.isHermitian_aeval_margLift
#print axioms TensorPower.norm_regionPow_sandwich_sub_le
-- Spectral and polynomial bounds for finite-replica star operators.
#print axioms Matrix.IsOrthogonalResolution.norm_le_l2_opNorm_hom
#print axioms TensorPower.l2_opNorm_starOp_le
#print axioms TensorPower.abs_starValue_le_one
#print axioms TensorPower.l2_opNorm_cfc_starOp_sub_aeval_le
#print axioms TensorPower.l2_opNorm_aeval_starOp_le
#print axioms TensorPower.isHermitian_aeval_starOp
-- Coherent symbol and trace limits for the marked similarity transform.
#print axioms TensorPower.norm_sandwich_approx_le
#print axioms TensorPower.norm_pairing_approx_le
#print axioms TensorPower.exists_rpow_le
#print axioms TensorPower.sandwich_rearrange
#print axioms TensorPower.star_dotProduct_mul_mulVec
#print axioms TensorPower.norm_markedScalarSymbol_sub_le
#print axioms TensorPower.hasMarkedSymbol_polyWord
#print axioms TensorPower.commute_symProj_of_forall
#print axioms TensorPower.isHermitian_markedRatio
#print axioms TensorPower.isHermitian_markedRatio_inv
#print axioms TensorPower.norm_markedSimilarity_sub_polyWord_le
#print axioms TensorPower.hasCoherentSymbol_markedSimilarity
-- Proposition 9.6, the leaf entropy identity (9.17) and continuity of mutual information.
#print axioms Arealaw.SubState.D₁_restrict_le
-- Proposition 8.1 comparator closure, wave 1: matrix square roots, isometries, Kronecker positivity, spectral cutoffs, Schur-label moments, replica band metrics.
#print axioms PermutationRepresentation.labelEntropy_mul_symProj_of_eq_mul
#print axioms TensorPower.commute_subsystemPerm_of_commute
#print axioms TensorPower.subgroup_signedLabelEntropy_symProj_nonneg
#print axioms PermutationRepresentation.posSemidef_mergeDeficit
-- Proposition 8.1 comparator closure, wave 2: replica defects, marginal supports, subsystem labels, inverse-power bounds, Bell insertions, Uhlmann isometries, relative entropy.
#print axioms TensorPower.exists_replicaMetric_symProj_inverse_bound_and_floor
#print axioms PermutationRepresentation.dim_le_card_of_labelProj_ne_zero
