import AreaLaw.S05_Conditional.Movement.Setup

/-!
# §5.1 D5.7: `ρ` and `ξ` are Hellinger-close

Digest `digest/05-conditional.md`, D5.7. `step_5_7_matrix_of` derives `Step_5_7_matrix` from the
log-moment identities (`Step_5_2`), the Schatten bound (`Step_5_4`) and the overlap identity
(`Step_5_6`).
-/

namespace AreaLaw

open Arealaw Matrix Complex Conditional
open scoped ComplexOrder MatrixOrder InnerProductSpace

universe u

namespace Conditional.Hel

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

omit [DecidableEq n] in
/-- `Tr B` is real for `B ≥ 0`. -/
theorem trace_eq_re {B : Matrix n n ℂ} (hB : B.PosSemidef) : B.trace = (B.trace.re : ℂ) :=
  Complex.ext rfl (by simpa using (Complex.nonneg_iff.1 hB.trace_nonneg).2.symm)

/-- D5.7.1, Cauchy–Schwarz for `X = ρ^a Q^{-a} √ρ`, `Y = √ρ`:
`Re Tr ρ^{1+a} Q^{-a} ≤ √(Tr ρ^{2a} K)` for a density matrix `ρ`. -/
theorem re_trace_le_sqrt (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (Q : Matrix n n ℂ) (a : ℝ) :
    (bracketPow ρ ((1 + a : ℝ) : ℂ) * hatPow Q ((-a : ℝ) : ℂ)).trace.re ≤
      √(bracketPow ρ ((2 * a : ℝ) : ℂ) * Kmat ρ Q a).trace.re := by
  set R := bracketPow ρ
  set Qa := hatPow Q ((-a : ℝ) : ℂ)
  have hY : (R (1 / 2))ᴴ = R (1 / 2) := by
    have := isHermitian_bracketPow_ofReal ρ (1 / 2); push_cast at this; exact this
  have hRa : (R a)ᴴ = R a := isHermitian_bracketPow_ofReal ρ a
  have hQa : Qaᴴ = Qa := isHermitian_hatPow_ofReal Q (-a)
  have hρ' : R (1 / 2) * R (1 / 2) = ρ := by
    rw [bracketPow_mul_bracketPow]; norm_num; exact bracketPow_one hρ
  have cs := norm_inner_le_norm (𝕜 := ℂ) (hs (R (1 / 2))) (hs (R a * Qa * R (1 / 2)))
  rw [inner_hs, norm_hs, norm_hs, hY, hρ', hρ1] at cs
  have e1 : (R (1 / 2) * (R a * Qa * R (1 / 2))).trace = (R ((1 + a : ℝ) : ℂ) * Qa).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      bracketPow_mul_bracketPow, bracketPow_mul_bracketPow]
    congr 3; push_cast; ring
  have e2 : ((R a * Qa * R (1 / 2))ᴴ * (R a * Qa * R (1 / 2))).trace =
      (R ((2 * a : ℝ) : ℂ) * Kmat ρ Q a).trace := by
    simp only [conjTranspose_mul, hY, hRa, hQa]
    rw [trace_mul_comm, show R a * Qa * R (1 / 2) * (R (1 / 2) * (Qa * R a)) =
      R a * (Qa * (R (1 / 2) * R (1 / 2)) * Qa) * R a by simp only [Matrix.mul_assoc],
      trace_mul_comm, ← Matrix.mul_assoc, bracketPow_mul_bracketPow, hρ', Kmat]
    congr 3; push_cast; ring
  rw [e1, e2] at cs
  simpa using (Complex.re_le_norm _).trans cs

/-- D5.7.1, Jensen for `exp` against weights `w` with `∑ w = 1`: `e^{a 𝔼 L} ≤ 𝔼 e^{a L}`. -/
theorem exp_le_sum_exp {ι κ : Type*} [Fintype ι] [Fintype κ] (w L : ι → κ → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hw1 : ∑ i, ∑ j, w i j = 1) (a : ℝ) :
    Real.exp (a * ∑ i, ∑ j, w i j * L i j) ≤ ∑ i, ∑ j, w i j * Real.exp (a * L i j) := by
  set m := ∑ i, ∑ j, w i j * L i j
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ Finset.sum_le_sum
    fun j (_ : j ∈ Finset.univ) ↦ mul_le_mul_of_nonneg_left (show
      Real.exp (a * m) * (a * L i j - a * m + 1) ≤ Real.exp (a * L i j) by
        have := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a * L i j - a * m))
          (Real.exp_pos (a * m)).le
        rwa [← Real.exp_add, add_sub_cancel] at this) (hw i j)
  have e (i : ι) (j : κ) : w i j * (Real.exp (a * m) * (a * L i j - a * m + 1)) =
      Real.exp (a * m) * a * (w i j * L i j) + Real.exp (a * m) * (1 - a * m) * w i j := by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hw1] at h
  linarith

/-- `√ρ` as a spectral function. -/
private theorem sqrt_eq_specFun (hρ : ρ.PosSemidef) :
    CFC.sqrt ρ = specFun hρ.isHermitian (fun t ↦ ((√t : ℝ) : ℂ)) := by
  rw [CFC.sqrt_eq_real_sqrt _ hρ.nonneg, cfcₙ_eq_cfc (hf0 := Real.sqrt_zero),
    specFun_ofReal_comp]

end Conditional.Hel

open Conditional.Hel

/-- D5.7 (`eq:conditional-hellinger`), matrix level. `H := ‖√ρ − √ξ‖₂ ≤ C √a ℓ` (for
`0 < a ℓ ≤ c`): universal `c, C` such that for a conditional pair `(ρ, Q)` with dimension `d` and
`0 < a`, `a ℓ ≤ c`, `ξ = K^r / Tr K^r` is a density matrix and `H² ≤ C a ℓ²`. -/
theorem step_5_7_matrix_of (h2 : Step_5_2.{u}) (h4 : Step_5_4.{u}) (h6 : Step_5_6.{u}) :
    Step_5_7_matrix.{u} := by
  obtain ⟨c, C, hc, hc8, hC, h4⟩ := h4
  refine ⟨c, C, hc, hC, fun n _ _ ρ Q d hcp a ha hac ↦ ?_⟩
  obtain ⟨hρ, hρ1, hQ, hd, -, -⟩ := id hcp
  have hℓ := one_le_ℓ hd
  have ha8 : a ≤ 1 / 8 := by nlinarith
  obtain ⟨hZ, hlogZ, -⟩ := h4 n ρ Q d hcp a ha hac
  obtain ⟨htr, h6ρ⟩ := h6 n ρ Q d hcp a ha (by linarith)
  obtain ⟨hw, hw1, -, -, hwL, hs⟩ := h2 n ρ Q d hρ.isHermitian hQ.isHermitian hcp
  -- `ξ` is a density matrix
  have hK : (Kmat ρ Q a).PosSemidef := by
    have := hρ.mul_mul_conjTranspose_same (hatPow Q ((-a : ℝ) : ℂ))
    rwa [(isHermitian_hatPow_ofReal Q (-a)).eq] at this
  have hB : (bracketPow (Kmat ρ Q a) (rexp a : ℂ)).PosSemidef := by
    have : 1 - 2 * a ≠ 0 := by linarith
    rw [bracketPow_ofReal hK (a := rexp a) (by unfold rexp; exact inv_ne_zero this)]
    exact Matrix.nonneg_iff_posSemidef.1 CFC.rpow_nonneg
  have hξ : (xiMat ρ Q a).PosSemidef :=
    hB.smul (by rw [← Complex.ofReal_inv]; exact_mod_cast (inv_pos.2 htr).le)
  have hξ1 : (xiMat ρ Q a).trace = 1 := by
    rw [xiMat, trace_smul, trace_eq_re hB, smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast htr.ne')
  refine ⟨hξ, hξ1, ?_⟩
  set hρh := hρ.isHermitian
  set hξh := hξ.isHermitian
  -- D5.7.1: `Tr ρ^{2a} K ≥ (Tr ρ^{1+a} Q^{-a})² ≥ e^{2a 𝔼L}`
  have hJ : Real.exp (a * relEnt ρ Q) ≤
      (bracketPow ρ ((1 + a : ℝ) : ℂ) * hatPow Q ((-a : ℝ) : ℂ)).trace.re := by
    have := exp_le_sum_exp _ (fun i j ↦ Real.log (hρh.eigenvalues i) -
      Real.log (hQ.isHermitian.eigenvalues j)) hw hw1 a
    rwa [hwL, ← hs a] at this
  have h71 : Real.exp (2 * a * relEnt ρ Q) ≤
      (bracketPow ρ ((2 * a : ℝ) : ℂ) * Kmat ρ Q a).trace.re := by
    have := (Real.le_sqrt' (Real.exp_pos _)).1 (hJ.trans (re_trace_le_sqrt hρ hρ1 Q a))
    rwa [← Real.exp_nat_mul, ← mul_assoc] at this
  -- D5.7.2: divide by `Z ≤ e^{2a 𝔼L + C a² ℓ²}`
  set T := (bracketPow ρ ((2 * a : ℝ) : ℂ) *
    bracketPow (xiMat ρ Q a) ((1 - 2 * a : ℝ) : ℂ)).trace.re with hT
  have h72 : 1 - C * a ^ 2 * ℓ d ^ 2 ≤ T := by
    rw [hT, (h6ρ ρ hρ).1, le_div_iff₀ hZ]
    calc (1 - C * a ^ 2 * ℓ d ^ 2) * Zval ρ Q a
        ≤ Real.exp (-(C * a ^ 2 * ℓ d ^ 2)) *
            Real.exp (2 * a * relEnt ρ Q + C * a ^ 2 * ℓ d ^ 2) :=
          mul_le_mul (by linarith [Real.add_one_le_exp (-(C * a ^ 2 * ℓ d ^ 2))])
            ((Real.log_le_iff_le_exp hZ).1 hlogZ) hZ.le (Real.exp_pos _).le
      _ = Real.exp (2 * a * relEnt ρ Q) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := h71
  -- D5.7.3: eigenbasis forms, `p` of `ξ`, `q` of `ρ`
  set p := hξh.eigenvalues
  set q := hρh.eigenvalues
  have hp1 : ∑ i, ∑ j, ovl hξh hρh i j * p i = 1 := by
    have h := hξh.trace_eq_sum_eigenvalues
    rw [hξ1] at h
    simp_rw [← Finset.sum_mul, sum_ovl_right, one_mul]
    exact Complex.ofReal_injective (by push_cast; exact h.symm)
  have hq1 : ∑ i, ∑ j, ovl hξh hρh i j * q j = 1 := by
    have h := hρh.trace_eq_sum_eigenvalues
    rw [hρ1] at h
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_ovl_left, one_mul]
    exact Complex.ofReal_injective (by push_cast; exact h.symm)
  have e72 : T = ∑ i, ∑ j, ovl hξh hρh i j * (p i ^ (1 - 2 * a) * q j ^ (2 * a)) := by
    rw [hT, trace_mul_comm, bracketPow_eq hξh, bracketPow_eq hρh, trace_specFun_mul_specFun]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [bfun_ofReal (by linarith) (hξ.eigenvalues_nonneg i),
      bfun_ofReal (by positivity) (hρ.eigenvalues_nonneg j), ← ofReal_mul, ← ofReal_mul,
      ofReal_re]
    ring
  -- D5.7.5: `H² = Tr ρ + Tr ξ − 2 Tr √ξ √ρ`
  have e75 : ((CFC.sqrt ρ - CFC.sqrt (xiMat ρ Q a))ᴴ *
      (CFC.sqrt ρ - CFC.sqrt (xiMat ρ Q a))).trace.re =
      2 - 2 * ∑ i, ∑ j, ovl hξh hρh i j * (√(p i) * √(q j)) := by
    have hsa : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).isSelfAdjoint
    have hsb : (CFC.sqrt (xiMat ρ Q a))ᴴ = CFC.sqrt (xiMat ρ Q a) :=
      (CFC.sqrt_nonneg _).isSelfAdjoint
    rw [conjTranspose_sub, hsa, hsb, sub_mul, mul_sub, mul_sub,
      CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, CFC.sqrt_mul_sqrt_self _ hξ.nonneg, trace_sub,
      trace_sub, trace_sub, trace_mul_comm (CFC.sqrt ρ), hρ1, hξ1, sqrt_eq_specFun hξ,
      sqrt_eq_specFun hρ, trace_specFun_mul_specFun]
    have hsum : (∑ i, ∑ j, ((√(p i) : ℝ) : ℂ) * ((√(q j) : ℝ) : ℂ) *
        (ovl hξh hρh i j : ℂ)).re = ∑ i, ∑ j, ovl hξh hρh i j * (√(p i) * √(q j)) := by
      simp only [Complex.re_sum, ← ofReal_mul, ofReal_re]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [sub_re, sub_re, sub_re, one_re, hsum]
    ring
  -- D5.7.4: the scalar core with `b = 2a ≤ 1/2`
  have core := step_5_7 (ovl hξh hρh) p q (ovl_nonneg hξh hρh) hξ.eigenvalues_nonneg
    hρ.eigenvalues_nonneg hp1 hq1 (b := 2 * a) (by positivity) (by linarith)
  rw [← e72] at core
  have h74 : (1 - T) / (2 * (2 * a)) ≤ C * a * ℓ d ^ 2 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [show C * a * ℓ d ^ 2 / 4 * (2 * (2 * a)) = C * a ^ 2 * ℓ d ^ 2 by ring]
  rw [e75]
  nlinarith [mul_pos (mul_pos hC ha) (by positivity : 0 < ℓ d ^ 2)]

end AreaLaw
