/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from QICLean, file `QICLean/Representation/ReplicaTransport/CoherentLog.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (average-algebra and Schwarz sections).
-/
import OpenAI.CoherentLogKernel

/-!
# Algebra and Schwarz inequality for coherent averages

This section proves symmetric-projector support, linearity and monotonicity of coherent averages,
then establishes the inverse Schwarz inequality used in the operator Jensen argument.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

section AverageAlgebra

variable (k : ℕ) (a : Ω)

omit [DecidableEq Ω] in
set_option linter.unusedFintypeInType false in
theorem isHermitian_coherentProj (θ : Ω → ℂ) : (coherentProj k θ).IsHermitian := by
  exact (posSemidef_vecMulVec_self_star _).isHermitian

theorem symProj_mul_coherentProj (θ : Ω → ℂ) :
    symProj (copyPerm Ω k) * coherentProj k θ = coherentProj k θ := by
  rw [coherentProj, mul_vecMulVec, symProj_mulVec_of_mem _ (tensorVec_mem_symmetricSubspace θ)]

theorem coherentProj_mul_symProj (θ : Ω → ℂ) :
    coherentProj k θ * symProj (copyPerm Ω k) = coherentProj k θ := by
  have h := congrArg conjTranspose (symProj_mul_coherentProj k θ)
  rwa [conjTranspose_mul, (isHermitian_symProj (k := k)).eq, (isHermitian_coherentProj k θ).eq] at h

/-- Left multiplication by a fixed matrix commutes with the Haar integral. -/
theorem mul_integral {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℂ)
    {F : unitaryGroup Ω ℂ → Matrix X X ℂ} (hF : Integrable F (unitaryHaar Ω)) :
    B * ∫ U, F U ∂(unitaryHaar Ω) = ∫ U, B * F U ∂(unitaryHaar Ω) := by
  exact ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)) B).integral_comp_comm hF |>.symm

/-- Right multiplication by a fixed matrix commutes with the Haar integral. -/
theorem integral_mul {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℂ)
    {F : unitaryGroup Ω ℂ → Matrix X X ℂ} (hF : Integrable F (unitaryHaar Ω)) :
    (∫ U, F U ∂(unitaryHaar Ω)) * B = ∫ U, F U * B ∂(unitaryHaar Ω) := by
  exact ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)).flip B).integral_comp_comm hF |>.symm

theorem symProj_mul_coherentAverage {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    symProj (copyPerm Ω k) * coherentAverage k a f = coherentAverage k a f := by
  rw [coherentAverage, mul_smul_comm, mul_integral _ (integrable_smul_coherentProj k a hf)]
  simp_rw [mul_smul_comm, symProj_mul_coherentProj]

theorem coherentAverage_mul_symProj {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    coherentAverage k a f * symProj (copyPerm Ω k) = coherentAverage k a f := by
  rw [coherentAverage, smul_mul_assoc, integral_mul _ (integrable_smul_coherentProj k a hf)]
  simp_rw [smul_mul_assoc, coherentProj_mul_symProj]

theorem coherentAverage_sub {f g : (Ω → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    coherentAverage k a (fun θ => f θ - g θ) = coherentAverage k a f - coherentAverage k a g := by
  simp only [coherentAverage, ← smul_sub]
  rw [← integral_sub (integrable_smul_coherentProj k a hf) (integrable_smul_coherentProj k a hg)]
  simp_rw [Complex.ofReal_sub, sub_smul]

theorem coherentAverage_add {f g : (Ω → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    coherentAverage k a (fun θ => f θ + g θ) = coherentAverage k a f + coherentAverage k a g := by
  simp only [coherentAverage, ← smul_add]
  rw [← integral_add (integrable_smul_coherentProj k a hf) (integrable_smul_coherentProj k a hg)]
  simp_rw [Complex.ofReal_add, add_smul]

theorem coherentAverage_const (c : ℝ) :
    coherentAverage k a (fun _ => c) = c • symProj (copyPerm Ω k) := by
  rw [← coherentAverage_one k a, coherentAverage, coherentAverage, smul_comm]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), ← integral_smul]
  simp only [Complex.ofReal_one, one_smul]
  convert! rfl using 1

end AverageAlgebra

section Jensen

variable (k : ℕ) (a : Ω)

/-- The coherent-state vector `U e_a` is a unit vector. -/
theorem star_coherentVec_dotProduct (U : unitaryGroup Ω ℂ) :
    star ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ⬝ᵥ ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) = 1 := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp U.2, vecMul_one]
  simp [dotProduct, Pi.single_apply]

/-- A coherent average of a nonnegative function is positive semidefinite. -/
theorem coherentAverage_nonneg {f : (Ω → ℂ) → ℝ}
    (hf0 : ∀ U : unitaryGroup Ω ℂ, 0 ≤ f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) :
    0 ≤ coherentAverage k a f := by
  rw [Matrix.nonneg_iff_posSemidef, coherentAverage]
  refine PosSemidef.smul ?_ (by exact_mod_cast Nat.zero_le _)
  rw [← Matrix.nonneg_iff_posSemidef]
  refine integral_nonneg fun U => ?_
  rw [Pi.zero_apply, Matrix.nonneg_iff_posSemidef]
  exact (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hf0 _)

/-- The coherent average is monotone. -/
theorem coherentAverage_mono {f g : (Ω → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ U : unitaryGroup Ω ℂ,
      f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ≤ g ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) :
    coherentAverage k a f ≤ coherentAverage k a g := by
  have := coherentAverage_nonneg k a (f := fun θ => g θ - f θ) fun U => sub_nonneg.mpr (hfg U)
  rwa [coherentAverage_sub k a hg hf, sub_nonneg] at this

/-- Left multiplication commutes with a Bochner integral. -/
theorem mul_integral' {α X : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype X]
    [DecidableEq X] (B : Matrix X X ℂ) {F : α → Matrix X X ℂ} (hF : Integrable F μ) :
    B * ∫ x, F x ∂μ = ∫ x, B * F x ∂μ := by
  exact ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)) B).integral_comp_comm hF |>.symm

/-- Right multiplication commutes with a Bochner integral. -/
theorem integral_mul' {α X : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype X]
    [DecidableEq X] (B : Matrix X X ℂ) {F : α → Matrix X X ℂ} (hF : Integrable F μ) :
    (∫ x, F x ∂μ) * B = ∫ x, F x * B ∂μ := by
  exact ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)).flip B).integral_comp_comm hF |>.symm

/-- **Schwarz step** (`06-transport.tex` lines 526--540): if `X` is Hermitian, supported on
`𝒮_k`, and `X 𝒬_k(g) X = X`, then `X ≤ 𝒬_k(g⁻¹)`. Pointwise,
`g (X - g⁻¹) P_θ (X - g⁻¹) ≥ 0`; integrating gives `X - 2X + 𝒬_k(g⁻¹) ≥ 0`. -/
theorem le_coherentAverage_inv {g : (Ω → ℂ) → ℝ} (hg : Continuous g) (hpos : ∀ θ, 0 < g θ)
    {X : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hX : X.IsHermitian)
    (hXQ : X * coherentAverage k a g * X = X) (hXP : X * symProj (copyPerm Ω k) = X)
    (hPX : symProj (copyPerm Ω k) * X = X) :
    X ≤ coherentAverage k a (fun θ => (g θ)⁻¹) := by
  have hgi : Continuous fun θ => (g θ)⁻¹ := hg.inv₀ fun θ => (hpos θ).ne'
  have hFg := integrable_smul_coherentProj k a hg
  have hF1 := integrable_smul_coherentProj k a (f := fun _ => 1) continuous_const
  have hFi := integrable_smul_coherentProj k a hgi
  have h0 := ((ContinuousLinearMap.mul ℂ _) X).integrable_comp hFg
  have h1 := ((ContinuousLinearMap.mul ℂ _).flip X).integrable_comp h0
  have h2 := ((ContinuousLinearMap.mul ℂ _) X).integrable_comp hF1
  have h3 := ((ContinuousLinearMap.mul ℂ _).flip X).integrable_comp hF1
  simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at h0 h1 h2 h3
  set μ := unitaryHaar Ω
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1
  set P := symProj (copyPerm Ω k)
  have hpt : ∀ U, 0 ≤ X * (((g (θ U) : ℝ) : ℂ) • coherentProj k (θ U)) * X -
      X * (((1 : ℝ) : ℂ) • coherentProj k (θ U)) - ((1 : ℝ) : ℂ) • coherentProj k (θ U) * X +
      (((g (θ U))⁻¹ : ℝ) : ℂ) • coherentProj k (θ U) := by
    intro U
    set r : ℝ := g (θ U)
    have hr : r ≠ 0 := (hpos _).ne'
    set N := X - ((r⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ)
    have hN : Nᴴ = N := by
      simp only [N, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq,
        Complex.star_def, Complex.conj_ofReal]
    have hpsd : ((r : ℂ) • (Nᴴ * coherentProj k (θ U) * N)).PosSemidef :=
      ((posSemidef_vecMulVec_self_star _).conjTranspose_mul_mul_same N).smul
        (by exact_mod_cast (hpos _).le)
    rw [Matrix.nonneg_iff_posSemidef]
    convert! hpsd using 1
    rw [hN]
    simp only [N, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul, Complex.ofReal_one, one_smul]
    have e1 : (r : ℂ) * (r⁻¹ : ℝ) = 1 := by
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hr)]
    have e2 : (r : ℂ) * ((r⁻¹ : ℝ) * (r⁻¹ : ℝ)) = (r⁻¹ : ℝ) := by
      calc
        _ = ((r : ℂ) * (r⁻¹ : ℝ)) * (r⁻¹ : ℝ) := by ring
        _ = (r⁻¹ : ℝ) := by rw [e1]; ring
    rw [e1, e2, one_smul, one_smul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    abel
  have hint : 0 ≤ ∫ U, (X * (((g (θ U) : ℝ) : ℂ) • coherentProj k (θ U)) * X -
      X * (((1 : ℝ) : ℂ) • coherentProj k (θ U)) - ((1 : ℝ) : ℂ) • coherentProj k (θ U) * X +
      (((g (θ U))⁻¹ : ℝ) : ℂ) • coherentProj k (θ U)) ∂μ := integral_nonneg fun U => hpt U
  rw [integral_add, integral_sub, integral_sub,
    ← integral_mul' X h0, ← mul_integral' X hFg, ← mul_integral' X hF1,
    ← integral_mul' X hF1] at hint
  rotate_left
  · exact h1
  · exact h2
  · exact h1.sub h2
  · exact h3
  · exact (h1.sub h2).sub h3
  · exact hFi
  have hD : (0 : ℂ) ≤ (symDim Ω k : ℂ) := by exact_mod_cast Nat.zero_le _
  have hfin := (Matrix.nonneg_iff_posSemidef.mp hint).smul hD
  have hQ1 := coherentAverage_one k a
  simp only [coherentAverage] at hXQ hQ1 ⊢
  rw [smul_add, smul_sub, smul_sub, ← smul_mul_assoc, ← mul_smul_comm, hXQ, ← mul_smul_comm,
    ← smul_mul_assoc, hQ1, hXP, hPX] at hfin
  rw [Matrix.le_iff]
  convert hfin using 1
  abel

end Jensen

end TensorPower
