import AreaLawRefactored.S03_InitialBox.BufferDiscount
import AreaLawForMathlib.Analysis.Matrix.TraceHolder

/-!
# §3.2 Optimized filters (proof of Lemma 3.2, D3.7–D3.13)

Digest `digest/03-initial-box.md` (D3.7–D3.13), paper `paper/sections/02-initial.tex`,
lines 335–573.
-/

namespace AreaLaw

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## D3.7 Optimized filters commute with their marginals -/

section D37

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- D3.7.4. If `L > 0`, `ρ = ρ*` and `Re Tr(L⁻¹ ρ L B) = 0` for every anti-Hermitian `B`,
then `[L, ρ] = 0`. -/
theorem step_3_7_4 {L ρ : Matrix m m ℂ} (hL : L.PosDef) (hρ : ρ.IsHermitian)
    (h : ∀ B : Matrix m m ℂ, Bᴴ = -B → (L⁻¹ * ρ * L * B).trace.re = 0) : L * ρ = ρ * L := by
  generalize hY : L⁻¹ * ρ * L = Y at h
  -- `Y_a = Y - Y*` is anti-Hermitian, `Tr(Y_a B) = 2i Im Tr(Y B) = 0`; `B = Y_a`: `‖Y_a‖₂ = 0`
  set N := Y - Yᴴ
  have hN : Nᴴ = -N := by simp [N]
  have hNB : ∀ B : Matrix m m ℂ, Bᴴ = -B → (N * B).trace = 0 := by
    intro B hB
    have h2 : (Yᴴ * B).trace = -star (Y * B).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hB, Matrix.neg_mul, trace_neg, neg_neg,
        trace_mul_comm]
    rw [show N * B = Y * B - Yᴴ * B by simp [N, Matrix.sub_mul], trace_sub, h2, sub_neg_eq_add,
      RCLike.star_def, RCLike.add_conj, RCLike.re_to_complex, h B hB]
    simp
  have hNN : (Nᴴ * N).trace = 0 := by rw [hN, Matrix.neg_mul, trace_neg, hNB N hN, neg_zero]
  rw [trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero] at hNN
  -- `L⁻¹ ρ L = L ρ L⁻¹`, so `ρ L² = L² ρ`
  have hLu : IsUnit L.det := (isUnit_iff_isUnit_det L).mp hL.isUnit
  have h1 : L⁻¹ * ρ * L = L * ρ * L⁻¹ := by
    have := hNN
    rw [← hY] at this
    simp only [conjTranspose_mul, hρ.eq, hL.1.eq, conjTranspose_nonsing_inv] at this
    rw [this, Matrix.mul_assoc]
  have h2 : Commute (L * L) ρ := by
    have := congrArg (fun X ↦ L * X * L) h1
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hLu, Matrix.one_mul] at this
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ hLu, Matrix.mul_one] at this
    simpa [Commute, SemiconjBy, Matrix.mul_assoc] using this.symm
  -- `L = (L²)^{1/2}` commutes with `ρ`
  have hL0 : 0 ≤ L := hL.posSemidef.nonneg
  have := h2.cfc_nnreal NNReal.sqrt
  rw [← CFC.sqrt_eq_cfc, CFC.sqrt_mul_self L hL0] at this
  exact this

end D37

/-! ## D3.11 First norm comparison -/

section D311

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- D3.11.3. Schatten Hölder with exponents `1/(1-a)`, `1/a`: for `ρ ≥ 0` and `B ≥ 0` with
`Tr B^{1/a} = 1` (`B = L_j²`, `Tr L_j^{2/a} = 1`), `Tr(ρ B) ≤ (Tr ρ^{1/(1-a)})^{1-a}`. -/
theorem step_3_11_3 {ρ B : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hB : B.PosSemidef) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hBn : ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1) :
    (ρ * B).trace.re ≤ (∑ i, hρ.1.eigenvalues i ^ (1 / (1 - a))) ^ (1 - a) := by
  have := hρ.re_trace_mul_le hB 
    (Real.holderConjugate_one_div (a := 1 - a) (b := a) (by linarith) ha0 (by ring))
  rwa [hBn, Real.one_rpow, mul_one, one_div_one_div, RCLike.re_to_complex] at this

end D311

end AreaLaw
