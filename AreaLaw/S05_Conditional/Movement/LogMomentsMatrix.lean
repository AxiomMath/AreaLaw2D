import AreaLaw.S05_Conditional.Movement.Setup

/-!
# §5 D5.2 The relative log-moments of a conditional pair (matrix level)

Digest `digest/05-conditional.md`, D5.2. For a conditional pair `(ρ, Q)` every moment
`𝔼 e^{sL}` of `L = log p_i − log q_j` under `w_{ij} = p_i |⟨i,j⟩|²` is the trace
`Tr ρ^{1+s} Q^{-s}`; `s = 1` (`Tr ρ² Q⁻¹ ≤ d` from `ρ ≤ d Q`) and `s = -1`
(`Tr Π_{supp ρ} Q ≤ d`) give the two exponential bounds.
-/

namespace AreaLaw

open Matrix Conditional
open scoped ComplexOrder MatrixOrder

universe u

namespace Conditional.LM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Re Tr f(A) g(B) = ∑_{ij} F(α_i, β_j) |⟨v_i, w_j⟩|²` when `f(α) g(β) = F(α, β)` is real. -/
theorem re_trace_specFun_mul_specFun {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (f g : ℝ → ℂ) (F : ℝ → ℝ → ℝ)
    (h : ∀ i j, f (hA.eigenvalues i) * g (hB.eigenvalues j) =
      F (hA.eigenvalues i) (hB.eigenvalues j)) :
    (specFun hA f * specFun hB g).trace.re =
      ∑ i, ∑ j, F (hA.eigenvalues i) (hB.eigenvalues j) * ovl hA hB i j := by
  simp_rw [trace_specFun_mul_specFun, Complex.re_sum, h, ← Complex.ofReal_mul, Complex.ofReal_re]

open scoped Matrix.Norms.L2Operator in
/-- `T Tᴴ ≤ c` implies `Tᴴ T ≤ c` (both have norm `‖T‖²`). -/
theorem conjTranspose_mul_le {T : Matrix n n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : T * Tᴴ ≤ (c : ℂ) • 1) : Tᴴ * T ≤ (c : ℂ) • 1 := by
  have e : algebraMap ℝ (Matrix n n ℂ) c = (c : ℂ) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  have h1 := (CStarAlgebra.norm_le_iff_le_algebraMap (T * star T) hc).2 (by rwa [e])
  rw [← e]
  exact (CStarAlgebra.norm_le_iff_le_algebraMap (star T * T) hc).1
    (by rwa [CStarRing.norm_star_mul_self, ← CStarRing.norm_self_mul_star])

end Conditional.LM

open Conditional.LM in
/-- D5.2 (`eq:conditional-log-moments`), matrix level. For a conditional pair `(ρ, Q)`,
eigenvalues `p_i` of `ρ`, `q_j > 0` of `Q`, the weights `w_{ij} = p_i |⟨i, j⟩|²` and
`L_{ij} = log p_i − log q_j`: `∑ w = 1`, `𝔼 e^{L} ≤ d`, `𝔼 e^{-L} ≤ d`, `𝔼 L = Tr ρ log ρ −
Tr ρ log Q`, and `Tr ρ^{1+s} Q^{-s} = 𝔼 e^{sL}` for real `s`. -/
theorem step_5_2 : Step_5_2.{u} := by
  rintro n _ _ ρ Q d hρ hQ ⟨hρp, htr, hQp, -, hdom, hsupp⟩
  have hp := hρp.eigenvalues_nonneg
  have hq := hQp.eigenvalues_pos
  -- the moments `𝔼 e^{sL} = Tr ρ^{1+s} Q^{-s}`
  have hmom : ∀ s : ℝ, (bracketPow ρ ((1 + s : ℝ) : ℂ) * hatPow Q ((-s : ℝ) : ℂ)).trace.re =
      ∑ i, ∑ j, hρ.eigenvalues i * ovl hρ hQ i j *
        Real.exp (s * (Real.log (hρ.eigenvalues i) - Real.log (hQ.eigenvalues j))) := by
    intro s
    rw [bracketPow_eq hρ, hatPow_eq hQ, re_trace_specFun_mul_specFun hρ hQ _ _
      (fun x y ↦ x * Real.exp (s * (Real.log x - Real.log y))) fun i j ↦ ?_]
    · simp_rw [mul_right_comm]
    rcases (hp i).eq_or_lt with h | h
    · simp [bfun, ← h]
    rw [bfun, hfun, if_pos h, if_pos (hq j), ← Complex.exp_add, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_exp, Complex.ofReal_inj,
      ← Real.exp_log h, ← Real.exp_add, Real.log_exp]
    ring_nf
  refine ⟨fun i j ↦ mul_nonneg (hp i) (ovl_nonneg hρ hQ i j), ?_, ?_, ?_, ?_, hmom⟩
  · -- `∑ w = ∑ p = Tr ρ = 1`
    simp_rw [← Finset.mul_sum, sum_ovl_right, mul_one]
    exact_mod_cast (congrArg Complex.re (hρ.trace_eq_sum_eigenvalues.symm.trans htr)).trans
      Complex.one_re
  · -- D5.2.4 `𝔼 e^L = Tr ρ² Q⁻¹ ≤ d`: `Q^{-1/2} ρ Q^{-1/2} ≤ d`, so `ρ^{1/2} Q⁻¹ ρ^{1/2} ≤ d`
    have hR := isHermitian_bracketPow_ofReal ρ (1 / 2)
    set R := bracketPow ρ ((1 / 2 : ℝ) : ℂ)
    have hRR : R * R = ρ := by
      rw [bracketPow_mul_bracketPow, ← Complex.ofReal_add]; norm_num; exact bracketPow_one hρp
    set H := hatPow Q (-(1 / 2))
    have hH : Hᴴ = H := conjTranspose_hatPow_neg_half Q
    have hT : (H * R) * (H * R)ᴴ ≤ ((d : ℝ) : ℂ) • 1 := by
      rw [conjTranspose_mul, hR.eq, hH, Complex.ofReal_natCast, ← hatPow_neg_half_conj hQp,
        ← Matrix.smul_mul, ← Matrix.mul_smul]
      rw [← Matrix.mul_assoc (H * R) R H, Matrix.mul_assoc H R R, hRR]
      exact IsSelfAdjoint.conjugate_le_conjugate hdom hH
    have key := re_trace_conj_le hR (conjTranspose_mul_le (Nat.cast_nonneg d) hT)
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRR, trace_smul, htr,
      conjTranspose_mul, hR.eq, hH] at key
    have hmom1 := hmom 1
    norm_num at hmom1
    have hHH : H * H = hatPow Q (-1) := by rw [hatPow_mul_hatPow]; norm_num
    have e : R * (R * H * (H * R)) * R = ρ * hatPow Q (-1) * ρ := by
      rw [← hRR, ← hHH]; simp only [Matrix.mul_assoc]
    rw [e, trace_mul_cycle] at key
    rw [← hmom1, show (2 : ℂ) = 1 + 1 by norm_num, ← bracketPow_mul_bracketPow,
      bracketPow_one hρp]
    simpa using key
  · -- D5.2.5 `𝔼 e^{-L} = Tr Π_{supp ρ} Q ≤ d`
    have := hmom (-1)
    simp only [neg_mul, one_mul, neg_neg, add_neg_cancel, Complex.ofReal_zero, Complex.ofReal_one,
      hatPow_one_of_posDef hQp] at this
    linarith
  · -- D5.2.3 `𝔼 L = Tr ρ log ρ − Tr ρ log Q`
    have e1 := specFun_mul hρ (fun t ↦ (t : ℂ)) fun t ↦ (Real.log t : ℂ)
    rw [specFun_ofReal, specFun_ofReal_comp, ← mul_one (specFun hρ _), ← specFun_one hQ] at e1
    have e2 : ρ * cfc Real.log Q =
        specFun hρ (fun t ↦ (t : ℂ)) * specFun hQ fun t ↦ (Real.log t : ℂ) := by
      rw [specFun_ofReal, specFun_ofReal_comp]
    rw [relEnt, e1, e2,
      re_trace_specFun_mul_specFun hρ hQ _ _ (fun x _ ↦ x * Real.log x) fun i j ↦ by simp,
      re_trace_specFun_mul_specFun hρ hQ _ _ (fun x y ↦ x * Real.log y) fun i j ↦ by simp,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.sum_sub_distrib]; congr! 1; ring

end AreaLaw
