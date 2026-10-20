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

/-- The derivative at `0` of `z ↦ e^{zB} K e^{-zB}` is `BK - KB`. -/
theorem hasDerivAt_exp_conj (B K : Matrix m m ℂ) :
    HasDerivAt (fun z : ℂ ↦ NormedSpace.exp (z • B) * K * NormedSpace.exp ((-z) • B))
      (B * K - K * B) 0 := by
  have h2 : HasDerivAt (fun z : ℂ ↦ NormedSpace.exp ((-z) • B)) (-B) 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_exp_smul_const (𝕂 := ℂ) B (-0 : ℂ)).scomp (0 : ℂ) (hasDerivAt_neg 0)
  refine (((hasDerivAt_exp_smul_const (𝕂 := ℂ) B (0 : ℂ)).mul_const K).mul h2).congr_deriv ?_
  simp [sub_eq_add_neg]

/-- D3.7.2. If `t ↦ ‖A Φ(e^{tB} L e^{-tB}) w‖²` has a local maximum at `t = 0` (`Φ` the lift to
the whole region, `A = K_{>j}`, `w = K_{<j} Ω`), then `Re ⟨A Φ(L) w, A Φ(BL - LB) w⟩ = 0`. -/
theorem step_3_7_2 {p : Type*} [Fintype p] [DecidableEq p]
    (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix p p ℂ) (A : Matrix p p ℂ) (L B : Matrix m m ℂ)
    (w : EuclideanSpace ℂ p)
    (hmax : IsLocalMax (fun t : ℝ ↦ ‖toEuclideanLin (A * Φ (NormedSpace.exp ((t : ℂ) • B) * L *
      NormedSpace.exp ((-(t : ℂ)) • B))) w‖ ^ 2) 0) :
    (inner ℂ (toEuclideanLin (A * Φ L) w) (toEuclideanLin (A * Φ (B * L - L * B)) w)).re = 0 := by
  let T : Matrix m m ℂ →L[ℂ] EuclideanSpace ℂ p := LinearMap.toContinuousLinearMap
    { toFun := fun X ↦ toEuclideanLin (A * Φ X) w
      map_add' := fun X Y ↦ by simp [Matrix.mul_add]
      map_smul' := fun c X ↦ by simp }
  have hMF : HasFDerivAt (fun z : ℂ ↦ NormedSpace.exp (z • B) * L * NormedSpace.exp ((-z) • B))
      ((ContinuousLinearMap.toSpanSingleton ℂ (B * L - L * B)).restrictScalars ℝ)
      ((fun t : ℝ ↦ (t : ℂ)) 0) := by
    simpa using (hasDerivAt_exp_conj B L).hasFDerivAt.restrictScalars ℝ
  have hv := (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hMF.comp_hasDerivAt (0 : ℝ) (Complex.ofRealCLM.hasDerivAt (x := 0)))
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.inner ℂ hv)
  have hfun : (⇑Complex.reCLM ∘ fun t ↦ inner ℂ ((⇑(T.restrictScalars ℝ) ∘
      (fun z : ℂ ↦ NormedSpace.exp (z • B) * L * NormedSpace.exp ((-z) • B)) ∘ Complex.ofReal) t)
      ((⇑(T.restrictScalars ℝ) ∘
      (fun z : ℂ ↦ NormedSpace.exp (z • B) * L * NormedSpace.exp ((-z) • B)) ∘ Complex.ofReal) t)) =
      fun t : ℝ ↦ ‖toEuclideanLin (A * Φ (NormedSpace.exp ((t : ℂ) • B) * L *
        NormedSpace.exp ((-(t : ℂ)) • B))) w‖ ^ 2 := by
    funext t
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [← RCLike.re_to_complex, ← @norm_sq_eq_re_inner ℂ]
    rfl
  rw [hfun] at hre
  have h0 := hmax.hasDerivAt_eq_zero hre
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.add_re, Complex.ofReal_zero,
    zero_smul, neg_zero, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h0
  rw [← inner_conj_symm (T (B * L - L * B)), Complex.conj_re] at h0
  change (inner ℂ (toEuclideanLin (A * Φ L) w) (toEuclideanLin (A * Φ (B * L - L * B)) w)).re +
    (inner ℂ (toEuclideanLin (A * Φ L) w) (toEuclideanLin (A * Φ (B * L - L * B)) w)).re = 0
    at h0
  linarith

/-- D3.7.3 (one peel). If `L` is invertible on `X ⊆ U` and commutes with the marginal
`ρ_{φ,X}`, then `⟨φ, L W L⁻¹ φ⟩ = ⟨φ, W φ⟩` for every `W` on `X`. -/
theorem step_3_7_3 {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {X U : Finset σ} (hX : X ⊆ U) (φ : Arealaw.Reg loc U → ℂ)
    {L : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ} (hL : IsUnit L.det)
    (hc : L * Arealaw.ptrace hX (vecMulVec φ (star φ)) =
      Arealaw.ptrace hX (vecMulVec φ (star φ)) * L)
    (W : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ) :
    star φ ⬝ᵥ (Arealaw.extendId hX (L * W * L⁻¹) *ᵥ φ) =
      star φ ⬝ᵥ (Arealaw.extendId hX W *ᵥ φ) := by
  have key (M : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ) :
      star φ ⬝ᵥ (Arealaw.extendId hX M *ᵥ φ) =
        (Arealaw.ptrace hX (vecMulVec φ (star φ)) * M).trace := by
    rw [Arealaw.trace_ptrace_mul, vecMulVec_mul, trace_vecMulVec, dotProduct_comm φ,
      ← dotProduct_mulVec]
  set ρ := Arealaw.ptrace hX (vecMulVec φ (star φ))
  rw [key, key, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hc, trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hL, Matrix.one_mul]

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
