import Arealaw.Bridge.Entropy
import Arealaw.Bridge.MState
import Arealaw.Bridge.VonNeumann
import Arealaw.Chain
import Arealaw.DataHiding
import Arealaw.Cor
import Arealaw.EDC
import Arealaw.EntropyBounds
import Arealaw.Equipartition
import Arealaw.Fidelity
import Arealaw.Geometry
import Arealaw.Mixed
import Arealaw.OpNorm
import Arealaw.Postselection
import Arealaw.PurifiedDist
import Arealaw.Purify
import Arealaw.PurifyChain
import Arealaw.Sanity.FannesPurifiedDistance
import Arealaw.Saturation
import Arealaw.SmoothEntropy
import Arealaw.Spectrum
import Arealaw.Subadditivity
import Arealaw.TraceDist
import Arealaw.TraceNorm
import Arealaw.Uhlmann
import Arealaw.VonNeumann

/-!
# Axiom audit

`#print axioms` for the headline results, confirming they depend only on the three standard
foundational axioms of Lean/Mathlib, `propext`, `Classical.choice` and `Quot.sound`, with no
`sorry`, no `native_decide`, and no custom axioms.
-/

-- 'Arealaw.dimer_area_law' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.dimer_area_law

-- 'Arealaw.SubState.exists_smoothMaxEntropy_minimizer' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.exists_smoothMaxEntropy_minimizer

-- 'Arealaw.SubState.smoothMaxEntropy_le_log_card' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.smoothMaxEntropy_le_log_card

-- 'Arealaw.SubState.smoothMaxEntropy_eq_top_of_neg' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.smoothMaxEntropy_eq_top_of_neg

-- 'Arealaw.SubState.smoothMaxEntropy₂_antitone' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.smoothMaxEntropy₂_antitone

-- 'Arealaw.le_minEntropy_of_feasible' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.le_minEntropy_of_feasible

-- 'Arealaw.minEntropy₂_eq_iSup' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.minEntropy₂_eq_iSup

-- 'Arealaw.minEntropy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.minEntropy_zero

-- 'Arealaw.SubState.smoothMinEntropy_eq_bot_of_neg' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.smoothMinEntropy_eq_bot_of_neg

-- 'Arealaw.SubState.smoothMinEntropy₂_monotone' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.smoothMinEntropy₂_monotone

-- 'Arealaw.EE_eq_vonNeumann' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.EE_eq_vonNeumann

-- 'Arealaw.ptrace_ptrace' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.ptrace_ptrace

-- 'Arealaw.SubState.restrict_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.restrict_restrict

-- 'Arealaw.MState.rhoA_purify' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.rhoA_purify

-- 'Arealaw.H_eigenvalues_eq_eigenvalues₀' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.H_eigenvalues_eq_eigenvalues₀

-- 'Arealaw.trace_ptrace_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.trace_ptrace_mul

-- 'Arealaw.ptrace_kronUnion_left' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.ptrace_kronUnion_left

-- 'Arealaw.entropy_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.entropy_le_log_card

-- 'Arealaw.purifyChain_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.purifyChain_spec

-- 'Arealaw.ptrace_mul_extendId' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.ptrace_mul_extendId

-- 'Arealaw.vonNeumann_submatrix_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.vonNeumann_submatrix_equiv

-- 'Arealaw.MState.entropy_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.entropy_le_log_card

-- 'Arealaw.SubState.mutualInfo_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.mutualInfo_comm

-- 'Arealaw.MState.restrict_purifyChain' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.restrict_purifyChain

-- 'Arealaw.SubState.entropy_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.entropy_submatrix

-- 'Arealaw.MState.regionEntropy_purifyChain' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.regionEntropy_purifyChain

-- 'Arealaw.MState.isIdempotentElem_purifyChain' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.isIdempotentElem_purifyChain

-- 'Arealaw.MState.Sᵥₙ_physlibEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.Sᵥₙ_physlibEquiv

-- 'Arealaw.traceRight_physlibEquiv_submatrix' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.traceRight_physlibEquiv_submatrix

-- 'Arealaw.traceLeft_physlibEquiv_submatrix' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.traceLeft_physlibEquiv_submatrix

-- 'Arealaw.SubState.traceNorm_submatrix' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.traceNorm_submatrix

-- 'Arealaw.MState.norm_trace_mul_le_one' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.norm_trace_mul_le_one

-- 'Arealaw.regionEntropy_union_le' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.regionEntropy_union_le

-- 'Arealaw.mutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.mutualInfo_nonneg

-- 'Arealaw.mutualInfo_le_two_mul_regionEntropy' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.mutualInfo_le_two_mul_regionEntropy

-- 'Arealaw.Hₛ_mk'_eq_H' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.Hₛ_mk'_eq_H

-- 'Arealaw.H_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.H_le_log_card

-- 'Arealaw.l2_opNorm_submatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.l2_opNorm_submatrix_le

-- 'Arealaw.l2_opNorm_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.l2_opNorm_submatrix

-- 'Arealaw.l2_opNorm_kronecker_le' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.l2_opNorm_kronecker_le

-- 'Arealaw.lemma20' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.lemma20

-- 'Arealaw.l2_opNorm_le_one_of_nonneg_of_le_one' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.l2_opNorm_le_one_of_nonneg_of_le_one

-- 'Arealaw.FannesAudenaert.printed_fails' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.FannesAudenaert.printed_fails

-- 'Arealaw.FannesAudenaert.substitution_safe' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.FannesAudenaert.substitution_safe

-- 'Arealaw.FannesAudenaert.repaired_of_audenaert' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.FannesAudenaert.repaired_of_audenaert

-- 'Arealaw.isGreatest_re_trace_mul_effect' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.isGreatest_re_trace_mul_effect

-- 'Arealaw.SubState.isGreatest_D₁' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.isGreatest_D₁

-- 'Arealaw.SubState.D₁_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D₁_triangle

-- 'Arealaw.SubState.D₁_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D₁_eq_zero_iff

-- 'Arealaw.SubState.D₁_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D₁_le_one

-- 'Arealaw.SubState.D₁_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D₁_submatrix

-- 'Arealaw.MState.D₁_eq_traceNorm_div_two' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.D₁_eq_traceNorm_div_two

-- 'Arealaw.MState.trDistance_physlibEquiv' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.trDistance_physlibEquiv

-- 'Arealaw.bddAbove_corSet' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.bddAbove_corSet

-- 'Arealaw.Cor_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.Cor_submatrix

-- 'Arealaw.Cor_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.Cor_comm

-- 'Arealaw.Cor_le_traceNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.Cor_le_traceNorm

-- 'Arealaw.SubState.Cor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.Cor_nonneg

-- 'Arealaw.SubState.Cor_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.Cor_comm

-- 'Arealaw.MState.Cor_eq_zero_of_product' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.Cor_eq_zero_of_product

-- 'Arealaw.MState.Cor_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.Cor_le_two

-- 'Arealaw.ringDist_sub_right' depends on axioms: [propext, Quot.sound]
#print axioms Arealaw.ringDist_sub_right

-- 'Arealaw.ringDist_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.ringDist_eq_zero_iff

-- 'Arealaw.regionDist_le_regionDist' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.regionDist_le_regionDist

-- 'Arealaw.disjoint_of_lt_separation' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.disjoint_of_lt_separation

-- 'Arealaw.IsInterval.isArc' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.IsInterval.isArc

-- 'Arealaw.SubState.HasEDC.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.HasEDC.mono

-- 'Arealaw.SubState.hasEDC_of_Cor_eq_zero' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.hasEDC_of_Cor_eq_zero

-- 'Arealaw.lemma16' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.lemma16
-- 'Arealaw.traceNorm_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.traceNorm_conjTranspose

-- 'Arealaw.traceNorm_fromBlocks_zero' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.traceNorm_fromBlocks_zero

-- 'Arealaw.traceNorm_fromBlocks_zero_diag' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.traceNorm_fromBlocks_zero_diag

-- 'Arealaw.re_trace_le_traceNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.re_trace_le_traceNorm

-- 'Arealaw.norm_trace_le_traceNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.norm_trace_le_traceNorm

-- 'Arealaw.re_trace_mul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.re_trace_mul_nonneg

-- 'Arealaw.fidelity_eq_re_trace_sqrt' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.fidelity_eq_re_trace_sqrt

-- 'Arealaw.trace_add_trace_sub_two_mul_fidelity_le_traceNorm_sub' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.trace_add_trace_sub_two_mul_fidelity_le_traceNorm_sub

-- 'Arealaw.exists_purification_of_card_le' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.exists_purification_of_card_le

-- 'Arealaw.SubState.fidelity_hat' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.fidelity_hat

-- 'Arealaw.SubState.D₁_hat' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D₁_hat

-- 'Arealaw.SubState.one_sub_F_le_D₁' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.one_sub_F_le_D₁

-- 'Arealaw.SubState.D_le_sqrt_two_mul_D₁' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D_le_sqrt_two_mul_D₁

-- 'Arealaw.SubState.D_sq_le_two_mul_D₁' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D_sq_le_two_mul_D₁

-- 'Arealaw.SubState.F_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.F_le_one

-- 'Arealaw.SubState.F_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.F_eq_one_iff

-- 'Arealaw.SubState.D_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.SubState.D_eq_zero_iff

-- 'Arealaw.MState.fidelity_physlibEquiv' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.MState.fidelity_physlibEquiv

-- 'Arealaw.exists_mem_unitaryGroup_eq_mul_diagonal' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.exists_mem_unitaryGroup_eq_mul_diagonal

-- 'Arealaw.exists_mem_unitaryGroup_trace_mul_eq_traceNorm' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.exists_mem_unitaryGroup_trace_mul_eq_traceNorm

-- 'Arealaw.traceNorm_conjTranspose_mul' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.traceNorm_conjTranspose_mul

-- 'Arealaw.fidelity_vecMulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.fidelity_vecMulVec

-- 'Arealaw.isGreatest_norm_trace_conjTranspose_mul' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.isGreatest_norm_trace_conjTranspose_mul

-- 'Arealaw.uhlmann' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.uhlmann

-- 'Arealaw.lemma9' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.lemma9

-- 'Arealaw.smoothMaxEntropy₂_piProd_le' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
#print axioms Arealaw.smoothMaxEntropy₂_piProd_le
