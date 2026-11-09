import AreaLawForMathlib.QuantumInfo.Region.State
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.Matrix.Order
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.ForMathlib.HermitianMat.Proj

/-!
# Trace norm and trace distance of states

Extends Physlib's `QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean`: the trace norm of a state is
its trace; `|Re Tr(A M)| ≤ ‖A‖₁ / 2`-type bounds for effects `0 ≤ M ≤ 1` of a Hermitian `A`,
attained at the positive spectral projection; the trace distance
`SubState.D₁ ρ σ = ‖ρ - σ‖₁ / 2` as the largest difference of effect expectations.
-/
namespace Arealaw

open scoped ComplexOrder Matrix Matrix.Norms.L2Operator

/-- A sum of `f` over a family depends only on the multiset of its values. -/
theorem sum_eq_of_multiset_map_eq {γ δ : Type*} [Fintype γ] [Fintype δ] (f : ℝ → ℝ) {p : γ → ℝ}
    {q : δ → ℝ} (h : Finset.univ.val.map p = Finset.univ.val.map q) : ∑ i, f (p i) = ∑ j, f (q j) :=
  congrArg Multiset.sum
    (by simpa [Multiset.map_map, Function.comp] using congrArg (Multiset.map f) h)

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]

/-- The trace norm of a subnormalized state is its trace. -/
theorem SubState.traceNorm_eq_trace (ρ : SubState ι 𝕜) : ρ.M.traceNorm = RCLike.re ρ.M.trace := by
  simp [← Matrix.PosSemidef.traceNorm_eq_trace ρ.psd]

/-- A normalized state has trace norm one. -/
@[simp] theorem MState.traceNorm_eq_one (ρ : Arealaw.MState ι 𝕜) : ρ.M.traceNorm = 1 := by
  rw [SubState.traceNorm_eq_trace ρ.toSubState, ρ.tr_eq_one]

/-- The trace norm of the identity is the dimension. -/
@[simp] theorem traceNorm_one [DecidableEq ι] : (1 : Matrix ι ι 𝕜).traceNorm = Fintype.card ι :=
  mod_cast (Matrix.PosSemidef.one (n := ι) (R := 𝕜)).traceNorm_eq_trace.trans Matrix.trace_one

section Reindex

variable {m : Type*} [Fintype m]

/-- The trace norm is invariant under reindexing.  Hermitian-only; the rectangular case
follows from `traceNorm_isometry_left`/`_right`. -/
theorem traceNorm_submatrix_equiv {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (e : m ≃ ι) :
    (A.submatrix e e).traceNorm = A.traceNorm := by
  classical
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues (hA.submatrix e),
    Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hA]
  exact sum_eq_of_multiset_map_eq abs (eigenvalues_multiset_submatrix_equiv hA e)

end Reindex

end Arealaw

namespace Arealaw

open Matrix
open scoped ComplexOrder MatrixOrder HermitianMat InnerProductSpace

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]

section Effect

variable [DecidableEq ι]

private theorem trace_posPart (A : HermitianMat ι 𝕜) :
    (A⁺).trace = ∑ i, max (A.H.eigenvalues i) 0 := by
  obtain ⟨e, he⟩ := A.cfc_eigenvalues fun x => x ⊔ 0
  rw [HermitianMat.posPart_eq_cfc_max, ← HermitianMat.sum_eigenvalues_eq_trace, he]
  exact e.sum_comp fun i => max (A.H.eigenvalues i) 0

private theorem trace_posPart_eq_traceNorm_add_trace (A : HermitianMat ι 𝕜) :
    (A⁺).trace = (A.mat.traceNorm + A.trace) / 2 := by
  -- The typed `have` pins the section instance against the classical one Physlib elaborates in.
  have habs : A.mat.traceNorm = ∑ i, |A.H.eigenvalues i| :=
    Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues A.H
  rw [trace_posPart, habs, ← HermitianMat.sum_eigenvalues_eq_trace,
    ← Finset.sum_add_distrib, Finset.sum_div]
  grind

private theorem inner_projLT_zero (A : HermitianMat ι 𝕜) : ⟪{0 <ₚ A}, A⟫_ℝ = (A⁺).trace := by
  rw [HermitianMat.inner_eq_re_trace, Matrix.trace_mul_comm, HermitianMat.projLT_zero_cfc,
    A.trace_mul_cfc, RCLike.ofReal_re, trace_posPart]
  grind

private theorem inner_effect_le {M : HermitianMat ι 𝕜} (A : HermitianMat ι 𝕜) (hM0 : 0 ≤ M)
    (hM1 : M ≤ 1) : ⟪M, A⟫_ℝ ≤ (A⁺).trace := by
  calc ⟪M, A⟫_ℝ
      = ⟪M, A⁺⟫_ℝ - ⟪M, A⁻⟫_ℝ := by
        rw [← HermitianMat.inner_sub_left, HermitianMat.posPart_add_negPart]
    _ ≤ ⟪1, A⁺⟫_ℝ :=
        (sub_le_self _ (HermitianMat.inner_ge_zero hM0 A.negPart_nonneg)).trans
          (HermitianMat.inner_mono' A.posPart_nonneg hM1)
    _ = (A⁺).trace := HermitianMat.one_inner _

/-- The expectation of an effect on a Hermitian `A` is at most `(‖A‖₁ + tr A) / 2`: the
upper-bound half of `isGreatest_re_trace_mul_effect`. -/
theorem re_trace_mul_effect_le {A M : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hM : 0 ≤ M)
    (hM1 : M ≤ 1) : RCLike.re (M * A).trace ≤ (A.traceNorm + RCLike.re A.trace) / 2 :=
  (inner_effect_le (M := ⟨M, hM.posSemidef.isHermitian⟩) ⟨A, hA⟩ hM hM1).trans_eq
    (trace_posPart_eq_traceNorm_add_trace ⟨A, hA⟩)

/-- The expectation of an effect on a positive semidefinite `A` lies between `0` and `tr A`:
the outcome probability of a postselection. -/
theorem re_trace_mul_mem_Icc {A M : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hM : 0 ≤ M) (hM1 : M ≤ 1) :
    RCLike.re (M * A).trace ∈ Set.Icc 0 (RCLike.re A.trace) := by
  set A' : HermitianMat ι 𝕜 := ⟨A, hA.isHermitian⟩
  set M' : HermitianMat ι 𝕜 := ⟨M, hM.posSemidef.isHermitian⟩
  have hA0' : 0 ≤ A' := HermitianMat.zero_le_iff.mpr hA
  -- Without the `change` the inner product elaborates through a whnf timeout.
  change ⟪M', A'⟫_ℝ ∈ Set.Icc 0 (RCLike.re A.trace)
  exact ⟨HermitianMat.inner_ge_zero hM hA0',
    (HermitianMat.inner_mono' hA0' hM1).trans_eq (HermitianMat.one_inner A')⟩

/-- **The variational form of the trace norm over effects**: for Hermitian `A`, the maximum
of `re tr(M A)` over `0 ≤ M ≤ 1` is `(‖A‖₁ + tr A) / 2`, attained by the projector onto the
positive eigenspace of `A`. -/
theorem isGreatest_re_trace_mul_effect {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ M : Matrix ι ι 𝕜, 0 ≤ M ∧ M ≤ 1 ∧ r = RCLike.re (M * A).trace}
      ((A.traceNorm + RCLike.re A.trace) / 2) := by
  set A' : HermitianMat ι 𝕜 := ⟨A, hA⟩
  exact ⟨⟨({0 <ₚ A'}).mat, HermitianMat.projLT_nonneg 0 A',
    HermitianMat.one_sub_projLT 0 A' ▸ sub_le_self 1 (HermitianMat.projLE_nonneg A' 0),
    ((trace_posPart_eq_traceNorm_add_trace A').symm.trans
      (inner_projLT_zero A').symm).trans (HermitianMat.inner_eq_re_trace _ _)⟩,
    fun _ ⟨_, hM, hM1, h⟩ ↦ h ▸ re_trace_mul_effect_le hA hM hM1⟩

end Effect

/-- The absolute trace of a Hermitian matrix is at most its trace norm: the `RCLike`-generic
Hermitian case of Physlib's `ℂ`-only `Matrix.abs_trace_le_traceNorm`. -/
theorem abs_re_trace_le_traceNorm {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    |RCLike.re A.trace| ≤ A.traceNorm := by
  classical
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hA, ← hA.sum_eigenvalues_eq_trace]
  exact_mod_cast Finset.abs_sum_le_sum_abs _ _

/-! ## The trace distance -/

namespace SubState

/-- The generalized trace distance between subnormalized states: half the trace norm of the
difference plus half `|tr ρ - tr σ|`. -/
noncomputable def D₁ (ρ σ : SubState ι 𝕜) : ℝ :=
  ((ρ.M - σ.M).traceNorm + |RCLike.re ρ.M.trace - RCLike.re σ.M.trace|) / 2

theorem D₁_def (ρ σ : SubState ι 𝕜) :
    ρ.D₁ σ = ((ρ.M - σ.M).traceNorm + |RCLike.re ρ.M.trace - RCLike.re σ.M.trace|) / 2 := rfl

theorem D₁_nonneg (ρ σ : SubState ι 𝕜) : 0 ≤ ρ.D₁ σ :=
  div_nonneg (add_nonneg (Matrix.traceNorm_nonneg _) (abs_nonneg _)) two_pos.le

@[simp] theorem D₁_self (ρ : SubState ι 𝕜) : ρ.D₁ ρ = 0 := by
  simp [D₁_def]

section Reindex

variable {m : Type*} [Fintype m]

/-- **`D₁` does not see a relabelling of the index**: the trace-distance counterpart of
`entropy_submatrix`. -/
@[simp] theorem D₁_submatrix (ρ σ : SubState ι 𝕜) (e : m ≃ ι) :
    (ρ.submatrix e).D₁ (σ.submatrix e) = ρ.D₁ σ := by
  simp [D₁_def, ← traceNorm_submatrix_equiv (ρ.psd.isHermitian.sub σ.psd.isHermitian) e,
    Matrix.submatrix_sub]

end Reindex

section Effect

variable [DecidableEq ι]

/-- **The variational form of the trace distance**: `D₁` is the attained maximum of the
distinguishing advantage `|re tr(M (ρ - σ))|` over effects `0 ≤ M ≤ 1`. -/
theorem isGreatest_D₁ (ρ σ : SubState ι 𝕜) :
    IsGreatest {r : ℝ | ∃ M : Matrix ι ι 𝕜, 0 ≤ M ∧ M ≤ 1 ∧
      r = |RCLike.re (M * (ρ.M - σ.M)).trace|} (ρ.D₁ σ) := by
  set A := ρ.M - σ.M with hA_def
  have hA : A.IsHermitian := ρ.psd.isHermitian.sub σ.psd.isHermitian
  have hD : ρ.D₁ σ = (A.traceNorm + |RCLike.re A.trace|) / 2 := by
    rw [D₁_def, hA_def, Matrix.trace_sub, map_sub]
  have htn := abs_re_trace_le_traceNorm hA
  have hneg : ∀ M : Matrix ι ι 𝕜, RCLike.re (M * -A).trace = -RCLike.re (M * A).trace := by
    simp
  constructor
  · rcases le_total 0 (RCLike.re A.trace) with ht | ht
    · obtain ⟨M, hM, hM1, hval⟩ := (isGreatest_re_trace_mul_effect hA).1
      exact ⟨M, hM, hM1, by grind⟩
    · obtain ⟨M, hM, hM1, hval⟩ := (isGreatest_re_trace_mul_effect hA.neg).1
      exact ⟨M, hM, hM1, by grind [Matrix.traceNorm_neg, Matrix.trace_neg]⟩
  · rintro r ⟨M, hM, hM1, rfl⟩
    grind [Matrix.traceNorm_neg, Matrix.trace_neg, re_trace_mul_effect_le hA hM hM1,
      re_trace_mul_effect_le hA.neg hM hM1]

/-- Every effect's distinguishing advantage is at most `D₁`: the upper-bound half of
`isGreatest_D₁`. -/
theorem abs_re_trace_mul_le_D₁ (ρ σ : SubState ι 𝕜) {M : Matrix ι ι 𝕜} (hM : 0 ≤ M) (hM1 : M ≤ 1) :
    |RCLike.re (M * (ρ.M - σ.M)).trace| ≤ ρ.D₁ σ :=
  (ρ.isGreatest_D₁ σ).2 ⟨M, hM, hM1, rfl⟩

end Effect

/-- `D₁` is at most one on subnormalized states. -/
theorem D₁_le_one (ρ σ : SubState ι 𝕜) : ρ.D₁ σ ≤ 1 := by
  classical
  obtain ⟨M, hM, hM1, hval⟩ := (ρ.isGreatest_D₁ σ).1
  grind [Matrix.mul_sub, Matrix.trace_sub, re_trace_mul_mem_Icc ρ.psd hM hM1,
    re_trace_mul_mem_Icc σ.psd hM hM1, ρ.tr_le_one, σ.tr_le_one]

end SubState

/-- On normalized states `|tr ρ - tr σ|` vanishes and `D₁` is the usual trace distance. -/
theorem MState.D₁_eq_traceNorm_div_two (ρ σ : MState ι 𝕜) :
    ρ.toSubState.D₁ σ.toSubState = (ρ.M - σ.M).traceNorm / 2 := by
  simp [SubState.D₁_def, ρ.tr_eq_one, σ.tr_eq_one]

end Arealaw
