/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from QICLean, file `QICLean/Representation/ReplicaTransport/CoherentLog.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (log-resolvent sections).
-/
import OpenAI.CoherentLogBasic

/-!
# Scalar and matrix resolvent formulas for the logarithm

This is the log-resolvent portion of QICLean's coherent-log development.  It proves the scalar
integral kernel formula, lifts it through continuous functional calculus, and records the matrix
resolvent identities used by the operator Jensen argument.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

section LogResolvent

open Set Filter Topology

/-- The resolvent kernel `1/(1+s) - 1/(x+s)` of the logarithm. -/
def logKernel (s x : ℝ) : ℝ := (1 + s)⁻¹ - (x + s)⁻¹

/-- The antiderivative `log(1+s) - log(x+s)` of the kernel in `s`. -/
private theorem hasDerivAt_logKernel_primitive {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    HasDerivAt (fun s => Real.log (1 + s) - Real.log (x + s)) (logKernel s x) s := by
  have h1 : (1 + s) ≠ 0 := by positivity
  have h2 : (x + s) ≠ 0 := by positivity
  have h := (((hasDerivAt_id s).const_add 1).log h1).sub (((hasDerivAt_id s).const_add x).log h2)
  convert! h using 1
  all_goals simp [logKernel]

private theorem tendsto_logKernel_primitive {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s => Real.log (1 + s) - Real.log (x + s)) atTop (𝓝 0) := by
  have hq : Tendsto (fun s : ℝ => 1 + (1 - x) / (x + s)) atTop (𝓝 1) := by
    have : Tendsto (fun s : ℝ => (1 - x) / (x + s)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)
    simpa using this.const_add 1
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq)
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have h2 : 0 < x + s := by linarith
  simp only [Function.comp]
  rw [← Real.log_div h1.ne' h2.ne']
  congr 1
  field_simp
  ring

/-- **Resolvent representation of the logarithm**: for `x > 0`,
`log x = ∫_0^∞ (1/(1+s) - 1/(x+s)) ds`, and the integrand is integrable. -/
theorem integrableOn_logKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s => logKernel s x) (Ioi 0) := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun s => Real.log (1 + s) - Real.log (x + s))
      (logKernel s x) s := fun s hs => hasDerivAt_logKernel_primitive hx hs
  rcases le_total 1 x with h | h
  · refine integrableOn_Ioi_deriv_of_nonneg' hd (fun s hs => ?_) (tendsto_logKernel_primitive hx)
    have hs : (0 : ℝ) < s := hs
    simp only [logKernel, sub_nonneg]
    exact inv_anti₀ (by linarith) (by linarith)
  · refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun s hs => hd s (Ioi_subset_Ici_self hs))
      (fun s hs => ?_)
      (tendsto_logKernel_primitive hx)
    · exact (hd 0 self_mem_Ici).continuousAt.continuousWithinAt
    have hs : (0 : ℝ) < s := hs
    simp only [logKernel, sub_nonpos]
    exact inv_anti₀ (by linarith) (by linarith)

theorem integral_logKernel {x : ℝ} (hx : 0 < x) :
    ∫ s in Ioi 0, logKernel s x = Real.log x := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun s hs => hasDerivAt_logKernel_primitive hx hs)
    (integrableOn_logKernel hx) (tendsto_logKernel_primitive hx)]
  simp

/-- The kernel is monotone in `x`. -/
theorem logKernel_mono {s x y : ℝ} (hs : 0 ≤ s) (hx : 0 < x) (hxy : x ≤ y) :
    logKernel s x ≤ logKernel s y := by
  simp only [logKernel]
  have : (y + s)⁻¹ ≤ (x + s)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  linarith

/-- A two-sided integrable bound for the kernel on `[m, M]`. -/
theorem abs_logKernel_le {s x m M : ℝ} (hs : 0 ≤ s) (hm : 0 < m) (hmx : m ≤ x) (hxM : x ≤ M) :
    |logKernel s x| ≤ |logKernel s m| + |logKernel s M| := by
  have h1 := logKernel_mono hs hm hmx
  have h2 := logKernel_mono hs (hm.trans_le hmx) hxM
  rw [abs_le]
  constructor <;> cases abs_cases (logKernel s m) <;> cases abs_cases (logKernel s M) <;> linarith

end LogResolvent

section MatrixLog

open Set Filter

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The spectrum of a positive definite matrix lies in a compact interval `[lo, hi]` with
`lo > 0`. -/
theorem exists_spectrum_subset_Icc {X : Matrix m m ℂ} (hX : X.PosDef) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ z ∈ spectrum ℝ X, lo ≤ z ∧ z ≤ hi := by
  rcases (spectrum ℝ X).eq_empty_or_nonempty with he | hne
  · exact ⟨1, 1, one_pos, le_rfl, by simp [he]⟩
  obtain ⟨zl, hzl, hl⟩ := (spectrum.isCompact X).exists_isMinOn hne continuousOn_id
  obtain ⟨zh, hzh, hh⟩ := (spectrum.isCompact X).exists_isMaxOn hne continuousOn_id
  exact ⟨zl, zh, hX.isStrictlyPositive.spectrum_pos hzl, hl hzh, fun z hz => ⟨hl hz, hh hz⟩⟩

/-- **Resolvent representation of the matrix logarithm**:
`log X = ∫_0^∞ k_s(X) ds` with `k_s(x) = 1/(1+s) - 1/(x+s)`, for positive definite `X`. -/
theorem integrableOn_cfc_logKernel {X : Matrix m m ℂ} (hX : X.PosDef) :
    IntegrableOn (fun s => cfc (logKernel s) X) (Ioi 0) ∧
      CFC.log X = ∫ s in Ioi 0, cfc (logKernel s) X := by
  obtain ⟨lo, hi, hlo, hlohi, hsp⟩ := exists_spectrum_subset_Icc hX
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hcont : ContinuousOn (Function.uncurry logKernel) (Ioi 0 ×ˢ spectrum ℝ X) := by
    refine ContinuousOn.sub ?_ ?_
    · refine (continuousOn_const.add continuousOn_fst).inv₀ fun q hq => ?_
      have : (0 : ℝ) < q.1 := hq.1
      exact (by linarith : (0 : ℝ) < 1 + q.1).ne'
    · refine (continuousOn_snd.add continuousOn_fst).inv₀ fun q hq => ?_
      have h1 : (0 : ℝ) < q.1 := hq.1
      have h2 := (hsp _ hq.2).1
      have : 0 < q.2 + q.1 := by linarith
      exact this.ne'
  have hbound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ spectrum ℝ X,
      ‖logKernel s z‖ ≤ |logKernel s lo| + |logKernel s hi| :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs z hz => by
      rw [Real.norm_eq_abs]
      exact abs_logKernel_le (le_of_lt hs) hlo (hsp z hz).1 (hsp z hz).2
  have hbi : MeasureTheory.HasFiniteIntegral (fun s => |logKernel s lo| + |logKernel s hi|)
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    ((integrableOn_logKernel hlo).abs.add (integrableOn_logKernel hhi).abs).hasFiniteIntegral
  refine ⟨integrableOn_cfc measurableSet_Ioi logKernel _ X hcont hbound hbi, ?_⟩
  rw [← cfc_setIntegral measurableSet_Ioi logKernel _ X hcont hbound hbi, CFC.log]
  refine cfc_congr fun z hz => ?_
  exact (integral_logKernel (hlo.trans_le (hsp z hz).1)).symm

/-- The resolvent `(X + s)⁻¹` through the functional calculus. -/
noncomputable def resolvent (X : Matrix m m ℂ) (s : ℝ) : Matrix m m ℂ :=
  cfc (fun x : ℝ => (x + s)⁻¹) X

theorem cfc_logKernel {X : Matrix m m ℂ} (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    cfc (logKernel s) X = (1 + s)⁻¹ • (1 : Matrix m m ℂ) - resolvent X s := by
  have hc : ContinuousOn (fun x : ℝ => (x + s)⁻¹) (spectrum ℝ X) :=
    (continuousOn_id.add continuousOn_const).inv₀ fun z hz => by
      have := hX.isStrictlyPositive.spectrum_pos hz
      exact (by simp only [id_eq]; linarith : (0 : ℝ) < id z + s).ne'
  rw [show logKernel s = fun x => (fun _ => (1 + s)⁻¹) x - (fun x : ℝ => (x + s)⁻¹) x from rfl,
    cfc_sub _ _ X continuousOn_const hc, cfc_const _ X hX.isHermitian.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, resolvent]

theorem add_smul_one_mul_resolvent {X : Matrix m m ℂ} (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    (X + s • (1 : Matrix m m ℂ)) * resolvent X s = 1 := by
  have hX' : IsSelfAdjoint X := hX.isHermitian.isSelfAdjoint
  have hpos : ∀ z ∈ spectrum ℝ X, z + s ≠ 0 := fun z hz => by
    have := hX.isStrictlyPositive.spectrum_pos hz
    exact (by linarith : (0 : ℝ) < z + s).ne'
  have hc : ContinuousOn (fun x : ℝ => (x + s)⁻¹) (spectrum ℝ X) :=
    (continuousOn_id.add continuousOn_const).inv₀ hpos
  have hlin : cfc (fun x : ℝ => x + s) X = X + s • (1 : Matrix m m ℂ) := by
    rw [cfc_add_const s (fun x : ℝ => x) X continuousOn_id hX', cfc_id' ℝ X hX',
      Algebra.algebraMap_eq_smul_one]
  rw [← hlin, resolvent, ← cfc_mul (fun x : ℝ => x + s) (fun x : ℝ => (x + s)⁻¹) X
    (continuousOn_id.add continuousOn_const) hc, ← cfc_one ℝ X hX']
  exact cfc_congr fun z hz => mul_inv_cancel₀ (hpos z hz)

theorem commute_resolvent {X Y : Matrix m m ℂ} (h : Commute X Y) (s : ℝ) :
    Commute (resolvent X s) Y := by
  exact Commute.cfc_real h _

theorem isHermitian_resolvent (X : Matrix m m ℂ) (s : ℝ) : (resolvent X s).IsHermitian := by
  exact cfc_predicate (p := IsSelfAdjoint) _ X

end MatrixLog

end TensorPower
