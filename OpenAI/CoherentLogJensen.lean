/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from QICLean, file `QICLean/Representation/ReplicaTransport/CoherentLog.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (operator-Jensen section).
-/
import OpenAI.CoherentLogAverage

/-!
# Operator Jensen inequality for coherent averages

This section proves the resolvent comparison, exchanges the Haar and logarithmic resolvent
integrals, extends coherent averages positively off the symmetric sector, and obtains the
compressed operator Jensen inequality for `log`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

section Jensen

open Set Filter

variable (k : ℕ) (a : Ω)

omit [Fintype Ω] [DecidableEq Ω] in
private theorem mul_resolvent_aux {α : Type*} [Ring α] {P R B : α} (hPP : P * P = P)
    (hRP : Commute R P) (hBP : Commute B P) (hRB : R * B = 1) :
    R * P * (B * P) * (R * P) = R * P := by
  calc R * P * (B * P) * (R * P) = R * (P * B) * (P * (R * P)) := by noncomm_ring
    _ = R * (B * P) * (P * (R * P)) := by rw [← hBP.eq]
    _ = R * B * ((P * P) * R) * P := by noncomm_ring
    _ = R * B * (R * P) * P := by rw [hPP, ← hRP.eq]
    _ = (R * B) * R * (P * P) := by noncomm_ring
    _ = R * P := by rw [hRB, hPP]; noncomm_ring

/-- **Resolvent form of the Jensen step** (`06-transport.tex` lines 526--546): if `Y` is
positive definite, commutes with `Π`, and `Π Y Π = 𝒬_k(f)`, then for each `s ≥ 0`
`𝒬_k(k_s ∘ f) ≤ Π k_s(Y) Π` for the resolvent kernel `k_s(x) = 1/(1+s) - 1/(x+s)`. -/
theorem coherentAverage_logKernel_le {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) {Y : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hY : Y.PosDef)
    (hYP : Commute Y (symProj (copyPerm Ω k)))
    (hPYP : symProj (copyPerm Ω k) * Y * symProj (copyPerm Ω k) = coherentAverage k a f)
    {s : ℝ} (hs : 0 ≤ s) :
    coherentAverage k a (fun θ => logKernel s (f θ)) ≤
      symProj (copyPerm Ω k) * cfc (logKernel s) Y * symProj (copyPerm Ω k) := by
  set P := symProj (copyPerm Ω k) with hPdef
  have hPP : P * P = P := symProj_mul_self k
  have hPh : P.IsHermitian := isHermitian_symProj (k := k)
  set R := resolvent Y s with hRdef
  set B := Y + s • (1 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) with hBdef
  have hBR : B * R = 1 := add_smul_one_mul_resolvent hY hs
  have hRP : Commute R P := commute_resolvent hYP s
  have hBP : Commute B P := hYP.add_left ((Commute.one_left P).smul_left s)
  have hRB' : Commute R B :=
    (commute_resolvent (Commute.refl Y) s).add_right ((Commute.one_right R).smul_right s)
  have hRB : R * B = 1 := by rw [hRB'.eq, hBR]
  have hQf : coherentAverage k a f = Y * P := by
    rw [← hPYP, ← hYP.eq, Matrix.mul_assoc, hPP]
  have hQs : coherentAverage k a (fun θ => f θ + s) = B * P := by
    rw [coherentAverage_add k a hf continuous_const, coherentAverage_const, hQf, hBdef, add_mul,
      smul_mul_assoc, Matrix.one_mul]
  have hXdef : P * R * P = R * P := by rw [← hRP.eq, Matrix.mul_assoc, hPP]
  have hXh : (P * R * P).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, hPh.eq, (isHermitian_resolvent Y s).eq,
      ← hRdef, Matrix.mul_assoc]
  have hXP : P * R * P * P = P * R * P := by rw [Matrix.mul_assoc, hPP]
  have hPX : P * (P * R * P) = P * R * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
  have hXQ : P * R * P * coherentAverage k a (fun θ => f θ + s) * (P * R * P) = P * R * P := by
    rw [hQs, hXdef]
    exact mul_resolvent_aux hPP hRP hBP hRB
  have hle := le_coherentAverage_inv k a (g := fun θ => f θ + s) (hf.add continuous_const)
    (fun θ => add_pos_of_pos_of_nonneg (hpos θ) hs) hXh hXQ hXP hPX
  have hinv : Continuous fun θ => (f θ + s)⁻¹ :=
    (hf.add continuous_const).inv₀ fun θ => (add_pos_of_pos_of_nonneg (hpos θ) hs).ne'
  have hL : coherentAverage k a (fun θ => logKernel s (f θ)) =
      (1 + s)⁻¹ • P - coherentAverage k a (fun θ => (f θ + s)⁻¹) := by
    rw [← coherentAverage_const, ← coherentAverage_sub k a continuous_const hinv]
    rfl
  rw [hL, cfc_logKernel hY hs, ← hRdef, mul_sub, sub_mul, mul_smul_comm, Matrix.mul_one,
    smul_mul_assoc, hPP]
  exact sub_le_sub_left hle _

/-- A continuous function is bounded above and below on the coherent vectors `U e_a`, and the
lower bound is positive for a positive function. -/
theorem exists_bounds_coherentVec {f : (Ω → ℂ) → ℝ} (hf : Continuous f) (hpos : ∀ θ, 0 < f θ) :
    ∃ lo hi : ℝ, 0 < lo ∧ ∀ U : unitaryGroup Ω ℂ,
      lo ≤ f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ∧
        f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ≤ hi := by
  have hc := hf.comp (continuous_coherentVec a)
  obtain ⟨U₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  obtain ⟨U₁, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  exact ⟨_, _, hpos _, fun U => ⟨hmin (Set.mem_univ U), hmax (Set.mem_univ U)⟩⟩

/-- **Exchange of the Haar and resolvent integrals**:
`𝒬_k(log f) = ∫_0^∞ 𝒬_k(k_s ∘ f) ds` for continuous `f > 0`. -/
theorem coherentAverage_log_eq_integral {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) :
    IntegrableOn (fun s => coherentAverage k a (fun θ => logKernel s (f θ))) (Ioi 0) ∧
      coherentAverage k a (fun θ => Real.log (f θ)) =
        ∫ s in Ioi 0, coherentAverage k a (fun θ => logKernel s (f θ)) := by
  set μ := unitaryHaar Ω
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1 with hθdef
  have hcθ : Continuous θ := continuous_coherentVec a
  obtain ⟨lo, hi, hlo, hb⟩ := exists_bounds_coherentVec a hf hpos
  have hhi : 0 < hi := hlo.trans_le ((hb 1).1.trans (hb 1).2)
  have hPc : Continuous fun U => coherentProj k (θ U) := continuous_coherentProj k hcθ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hPc.continuousOn
  set F : unitaryGroup Ω ℂ → ℝ → Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
    fun U s => ((logKernel s (f (θ U)) : ℝ) : ℂ) • coherentProj k (θ U) with hFdef
  have hmeas : StronglyMeasurable (Function.uncurry F) := by
    have h1 : Measurable fun p : unitaryGroup Ω ℂ × ℝ => logKernel p.2 (f (θ p.1)) := by
      unfold logKernel
      exact ((measurable_const.add measurable_snd).inv).sub
        ((((hf.comp hcθ).measurable.comp measurable_fst).add measurable_snd).inv)
    exact (Complex.measurable_ofReal.comp h1).stronglyMeasurable.smul
      (hPc.stronglyMeasurable.comp_measurable measurable_fst)
  have hbd : Integrable (fun s => (|logKernel s lo| + |logKernel s hi|) * C)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrableOn_logKernel hlo).abs.add (integrableOn_logKernel hhi).abs).mul_const C
  have hint : Integrable (Function.uncurry F) (μ.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (hbd.comp_snd μ).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
      with p hp
    have hp' : (0 : ℝ) ≤ p.2 := le_of_lt hp
    simp only [Function.uncurry, hFdef]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (abs_logKernel_le hp' hlo (hb p.1).1 (hb p.1).2) (hC _ (Set.mem_univ _))
      (norm_nonneg _) (by positivity)
  refine ⟨(hint.integral_prod_right).smul (symDim Ω k : ℂ), ?_⟩
  change (symDim Ω k : ℂ) • ∫ U, ((Real.log (f (θ U)) : ℝ) : ℂ) • coherentProj k (θ U) ∂μ =
    ∫ s in Ioi 0, (symDim Ω k : ℂ) • ∫ U, F U s ∂μ
  rw [integral_smul, ← integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [hFdef]
  rw [integral_smul_const, integral_complex_ofReal, integral_logKernel ((hlo.trans_le (hb U).1))]

/-- The projector `Π` is positive semidefinite. -/
theorem posSemidef_symProj : (symProj (copyPerm Ω k)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (symProj (copyPerm Ω k))
  rwa [(isHermitian_symProj (k := k)).eq, symProj_mul_self] at h

/-- The complementary projector `1 - Π` is positive semidefinite. -/
theorem posSemidef_one_sub_symProj : (1 - symProj (copyPerm Ω k)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (1 - symProj (copyPerm Ω k))
  rwa [conjTranspose_sub, conjTranspose_one, (isHermitian_symProj (k := k)).eq, sub_mul, mul_sub,
    mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, symProj_mul_self, sub_self,
    sub_zero] at h

theorem mul_coherentAverage_add_smul_symProj {f : (Ω → ℂ) → ℝ} (hf : Continuous f) (c : ℝ) :
    (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))) * symProj (copyPerm Ω k) =
      coherentAverage k a f := by
  rw [add_mul, coherentAverage_mul_symProj k a hf, smul_mul_assoc, sub_mul, Matrix.one_mul,
    symProj_mul_self, sub_self, smul_zero, add_zero]

theorem symProj_mul_coherentAverage_add_smul {f : (Ω → ℂ) → ℝ} (hf : Continuous f) (c : ℝ) :
    symProj (copyPerm Ω k) * (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))) =
      coherentAverage k a f := by
  rw [mul_add, symProj_mul_coherentAverage k a hf, mul_smul_comm, mul_sub, Matrix.mul_one,
    symProj_mul_self, sub_self, smul_zero, add_zero]

/-- `𝒬_k(f) + c (1 - Π)` is positive definite for continuous `f > 0` and `c > 0`. -/
theorem posDef_coherentAverage_add_smul {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) {c : ℝ} (hc : 0 < c) :
    (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))).PosDef := by
  obtain ⟨lo, hi, hlo, hb⟩ := exists_bounds_coherentVec a hf hpos
  set P := symProj (copyPerm Ω k)
  set m := min lo c
  have hm : 0 < m := lt_min hlo hc
  have hQ : lo • P ≤ coherentAverage k a f := by
    rw [← coherentAverage_const]
    exact coherentAverage_mono k a continuous_const hf fun U => (hb U).1
  have hsum : (coherentAverage k a f + c • (1 - P) - m • 1).PosSemidef := by
    have e : coherentAverage k a f + c • (1 - P) - m • 1 =
        (coherentAverage k a f - lo • P) + (lo - m) • P + (c - m) • (1 - P) := by
      simp only [sub_smul, smul_sub]
      abel
    rw [e]
    exact ((Matrix.le_iff.mp hQ).add ((posSemidef_symProj k).smul
      (sub_nonneg.mpr (min_le_left _ _)))).add ((posSemidef_one_sub_symProj k).smul
      (sub_nonneg.mpr (min_le_right _ _)))
  have := (PosDef.one.smul hm).add_posSemidef hsum
  rwa [add_sub_cancel] at this

/-- **Operator Jensen inequality for the logarithm** with an arbitrary positive filler `c` on
the complement of `𝒮_k` (`06-transport.tex`, display `transport:log-jensen`). -/
theorem coherentAverage_log_le_of_pos {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) {c : ℝ} (hc : 0 < c) :
    coherentAverage k a (fun θ => Real.log (f θ)) ≤
      symProj (copyPerm Ω k) *
        CFC.log (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))) *
          symProj (copyPerm Ω k) := by
  set P := symProj (copyPerm Ω k)
  set Y := coherentAverage k a f + c • (1 - P)
  have hY : Y.PosDef := posDef_coherentAverage_add_smul k a hf hpos hc
  have hYP' : Y * P = coherentAverage k a f := mul_coherentAverage_add_smul_symProj k a hf c
  have hPY' : P * Y = coherentAverage k a f := symProj_mul_coherentAverage_add_smul k a hf c
  have hYP : Commute Y P := hYP'.trans hPY'.symm
  have hPYP : P * Y * P = coherentAverage k a f := by
    rw [hPY', coherentAverage_mul_symProj k a hf]
  obtain ⟨hintY, hlogY⟩ := integrableOn_cfc_logKernel hY
  obtain ⟨hintQ, hlogQ⟩ := coherentAverage_log_eq_integral k a hf hpos
  have hint1 := ((ContinuousLinearMap.mul ℂ _) P).integrable_comp hintY
  have hint2 := ((ContinuousLinearMap.mul ℂ _).flip P).integrable_comp hint1
  simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hint1 hint2
  rw [hlogY, mul_integral' P hintY, integral_mul' P hint1, hlogQ, ← sub_nonneg,
    ← integral_sub hint2 hintQ]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change (0 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) ≤ _
  exact sub_nonneg.mpr (coherentAverage_logKernel_le k a hf hpos hY hYP hPYP (le_of_lt hs))

end Jensen

end TensorPower
