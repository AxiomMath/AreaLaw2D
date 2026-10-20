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
  rw [Arealaw.dotProduct_extendId_mulVec, Arealaw.dotProduct_extendId_mulVec, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← hc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    nonsing_inv_mul _ hL, Matrix.one_mul]

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

/-! ## D3.9 The optimized vector has small excitation energy -/

section D39

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- D3.9.1. If `HΩ = E₀Ω`, `K` is invertible and `φ = c KΩ`, then `KHK⁻¹φ = E₀φ`, so
`⟨φ, (H - E₀)φ⟩ = ⟨φ, (H - KHK⁻¹)φ⟩`. -/
theorem step_3_9_1 {H K : Matrix n n ℂ} {Ω : n → ℂ} {E₀ : ℝ} (hΩ : H *ᵥ Ω = (E₀ : ℂ) • Ω)
    (hK : IsUnit K.det) (c : ℂ) :
    star (c • K *ᵥ Ω) ⬝ᵥ ((H - (E₀ : ℂ) • 1) *ᵥ (c • K *ᵥ Ω)) =
      star (c • K *ᵥ Ω) ⬝ᵥ ((H - K * H * K⁻¹) *ᵥ (c • K *ᵥ Ω)) := by
  have h : (K * H * K⁻¹) *ᵥ (c • K *ᵥ Ω) = (E₀ : ℂ) • (c • K *ᵥ Ω) := by
    rw [mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hK, Matrix.mul_one,
      ← mulVec_mulVec, hΩ, mulVec_smul, smul_comm]
  rw [sub_mulVec, sub_mulVec, h, smul_mulVec, one_mulVec]

end D39

/-! ## D3.11 First norm comparison -/

section D311

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- D3.11.2. For `L_j = L_j*`, `N_j = ‖L_j K_{<j} Ω‖` and an overlap
`s ≤ |⟨Ω, φ_j⟩|`, `φ_j = L_j K_{<j} Ω / N_j`: `s N_j ≤ |⟨L_j Ω, K_{<j} Ω⟩| ≤ ‖L_j Ω‖ ‖K_{<j} Ω‖`. -/
theorem step_3_11_2 {L : Matrix m m ℂ} (hL : L.IsHermitian) (Ω ψ : EuclideanSpace ℂ m) {s : ℝ}
    (hs : s ≤ ‖inner ℂ Ω (((‖toEuclideanLin L ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin L ψ)‖) :
    s * ‖toEuclideanLin L ψ‖ ≤ ‖toEuclideanLin L Ω‖ * ‖ψ‖ := by
  rcases (norm_nonneg (toEuclideanLin L ψ)).lt_or_eq with hN | hN
  · rw [inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hN, ← isSymmetric_toEuclideanLin_iff.2 hL] at hs
    calc s * ‖toEuclideanLin L ψ‖
        ≤ ‖toEuclideanLin L ψ‖⁻¹ * ‖inner ℂ (toEuclideanLin L Ω) ψ‖ * ‖toEuclideanLin L ψ‖ := by
          gcongr
      _ = ‖inner ℂ (toEuclideanLin L Ω) ψ‖ := by field_simp
      _ ≤ _ := norm_inner_le_norm _ _
  · rw [← hN, mul_zero]; positivity

/-- D3.11.3. Schatten Hölder with exponents `1/(1-a)`, `1/a`: for `ρ ≥ 0` and `B ≥ 0` with
`Tr B^{1/a} = 1` (`B = L_j²`, `Tr L_j^{2/a} = 1`), `Tr(ρ B) ≤ (Tr ρ^{1/(1-a)})^{1-a}`. -/
theorem step_3_11_3 {ρ B : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hB : B.PosSemidef) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hBn : ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1) :
    (ρ * B).trace.re ≤ (∑ i, hρ.1.eigenvalues i ^ (1 / (1 - a))) ^ (1 - a) := by
  have := hρ.re_trace_mul_le hB 
    (Real.holderConjugate_one_div (a := 1 - a) (b := a) (by linarith) ha0 (by ring))
  rwa [hBn, Real.one_rpow, mul_one, one_div_one_div, RCLike.re_to_complex] at this


/-- `Tr ρ^{1/(1-a)} = ∑_{p_j > 0} p_j e^{-u log p_j}` at `u = -a/(1-a)`
(D3.11.4: `1 - u = 1/(1-a)`). -/
theorem sum_rpow_eq_sum_exp {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ j, 0 ≤ p j) {a : ℝ}
    (ha1 : a < 1) :
    ∑ j, p j ^ (1 / (1 - a)) = ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < p j),
      p j * Real.exp (-(-a / (1 - a)) * Real.log (p j)) := by
  have h1 : 0 < 1 - a := by linarith
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs with hj
  · have hne : 1 + a / (1 - a) ≠ 0 := by
      rw [show 1 + a / (1 - a) = 1 / (1 - a) by field_simp; ring]; positivity
    rw [show -(-a / (1 - a)) * Real.log (p j) = Real.log (p j) * (a / (1 - a)) by ring,
      ← Real.rpow_def_of_pos hj, ← Real.rpow_one_add' (hp j) hne]
    congr 1; field_simp; ring
  · rw [le_antisymm (not_lt.1 hj) (hp j), Real.zero_rpow (by positivity)]

/-- D3.11.3 on a region. For a unit vector `Ω` on `U`, `X ⊆ U` and `L = L*` on `X` with
`Tr (L²)^{1/a} = 1`: `‖L Ω‖² ≤ (Tr ρ_{Ω,X}^{1/(1-a)})^{1-a}`. -/
theorem step_3_11_3_region {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {X U : Finset σ} (hX : X ⊆ U) (Ω : Arealaw.Reg loc U → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) {L : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ}
    (hL : L.IsHermitian) (hB : (L * L).PosSemidef) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hBn : ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1) :
    (star (Arealaw.extendId hX L *ᵥ Ω) ⬝ᵥ (Arealaw.extendId hX L *ᵥ Ω)).re ≤
      (∑ j, ((OpenAI.pureState Ω hΩ).toSubState.restrict hX).psd.isHermitian.eigenvalues j ^
        (1 / (1 - a))) ^ (1 - a) := by
  have hρ := ((OpenAI.pureState Ω hΩ).toSubState.restrict hX).psd
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Arealaw.extendId_conjTranspose, hL.eq,
    ← Arealaw.extendId_mul, Arealaw.dotProduct_extendId_mulVec]
  exact step_3_11_3 hρ hB ha0 ha1 hBn


/-- D3.11.3–D3.11.4 on a region. With Lemma 3.1 at `u = -a/(1-a)` for the cut `X | U ∖ X`
(hypothesis `hM`, admissible by D3.10(iii)) and `0 < a ≤ ½`:
`log ‖L Ω‖² ≤ -a S(X) + 1024 e ϑ 𝓑 a²`. -/
theorem step_3_11_4_region {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {X U : Finset σ} (hX : X ⊆ U) (Ω : Arealaw.Reg loc U → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) {L : Matrix (Arealaw.Reg loc X) (Arealaw.Reg loc X) ℂ}
    (hL : L.IsHermitian) (hB : (L * L).PosSemidef) {a ϑ 𝓑 : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2)
    (hϑ : 0 ≤ ϑ) (h𝓑 : 0 ≤ 𝓑) (hBn : ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1)
    (hpos : 0 < (star (Arealaw.extendId hX L *ᵥ Ω) ⬝ᵥ (Arealaw.extendId hX L *ᵥ Ω)).re)
    (hM : let ρ := (OpenAI.pureState Ω hΩ).toSubState.restrict hX
      let p := ρ.psd.isHermitian.eigenvalues
      Real.log (∑ j ∈ Finset.univ.filter (fun j ↦ 0 < p j),
          p j * Real.exp (-(-a / (1 - a)) * Real.log (p j))) ≤
        -a / (1 - a) * ρ.entropy + 512 * Real.exp 1 * ϑ * 𝓑 * (-a / (1 - a)) ^ 2) :
    Real.log (star (Arealaw.extendId hX L *ᵥ Ω) ⬝ᵥ (Arealaw.extendId hX L *ᵥ Ω)).re ≤
      -a * ((OpenAI.pureState Ω hΩ).toSubState.restrict hX).entropy +
        1024 * Real.exp 1 * ϑ * 𝓑 * a ^ 2 := by
  have ha1 : a < 1 := by linarith
  set ρ := (OpenAI.pureState Ω hΩ).toSubState.restrict hX
  -- D3.11.3
  have h3 := step_3_11_3_region hX Ω hΩ hL hB ha0 ha1 hBn
  rw [sum_rpow_eq_sum_exp (fun j ↦ ρ.psd.eigenvalues_nonneg j) ha1] at h3
  set T := ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < ρ.psd.isHermitian.eigenvalues j),
    ρ.psd.isHermitian.eigenvalues j *
      Real.exp (-(-a / (1 - a)) * Real.log (ρ.psd.isHermitian.eigenvalues j))
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j hj ↦
    mul_nonneg (Finset.mem_filter.1 hj).2.le (Real.exp_pos _).le
  have hT : 0 < T := by
    rcases hT0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.zero_rpow (by linarith)] at h3; linarith
  -- D3.11.4
  calc _ ≤ Real.log (T ^ (1 - a)) := Real.log_le_log hpos h3
    _ = (1 - a) * Real.log T := Real.log_rpow hT _
    _ ≤ _ := step_3_11_4 ha0 ha2 hϑ h𝓑 hM

end D311

/-! ## D3.12 Zero-floor limit and the trial-norm bound -/

section D312

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordered product `f (k-1) ⋯ f 0`. -/
def prodDesc (f : ℕ → Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 1
  | k + 1 => f k * prodDesc f k

/-- D3.12.4. Moving the unitaries `U_j = M_j^{iy}` to the left: with `V_j = U_j ⋯ U_1`,
`(U_m M_m) ⋯ (U_1 M_1) = (U_m ⋯ U_1) (V_{m-1}^* M_m V_{m-1}) ⋯ (V_0^* M_1 V_0)`. -/
theorem step_3_12_4 (U M : ℕ → Matrix n n ℂ) (hU : ∀ j, U j * (U j)ᴴ = 1) (k : ℕ) :
    prodDesc (fun j ↦ U j * M j) k =
      prodDesc U k * prodDesc (fun j ↦ (prodDesc U j)ᴴ * M j * prodDesc U j) k := by
  have hV : ∀ j, prodDesc U j * (prodDesc U j)ᴴ = 1 := by
    intro j
    induction j with
    | zero => simp [prodDesc]
    | succ j ih =>
      simp only [prodDesc, conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (prodDesc U j), ih, Matrix.one_mul, hU]
  induction k with
  | zero => simp [prodDesc]
  | succ k ih =>
    simp only [prodDesc]
    rw [ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (prodDesc U k) (prodDesc U k)ᴴ, hV, Matrix.one_mul]

end D312

/-! ## D3.13 Schmidt-averaged upper bound on `-2 log N` -/

section D313

/-- D3.13. Schmidt weights `p_i > 0`, `∑ p_i = 1`, `S(X) = ∑ p_i (-log p_i)`. From the per-`i`
bounds `-2 log N ≤ -log p_i + ∑_j a_j S_{w_i}(T_j)` (D3.13.1, from D3.12) and concavity
`∑_i p_i S_{w_i}(T_j) ≤ S(T_j)` (D3.13.2): `-2 log N ≤ S(X) + ∑_j a_j S(T_j)`. -/
theorem step_3_13 {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    {J : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ j ∈ J, 0 ≤ a j) {Sw : ι → ℕ → ℝ} {ST : ℕ → ℝ}
    {SX N : ℝ} (hSX : SX = ∑ i, p i * -Real.log (p i))
    (h1 : ∀ i, -2 * Real.log N ≤ -Real.log (p i) + ∑ j ∈ J, a j * Sw i j)
    (h2 : ∀ j ∈ J, ∑ i, p i * Sw i j ≤ ST j) :
    -2 * Real.log N ≤ SX + ∑ j ∈ J, a j * ST j := by
  -- D3.13.1, averaged with weights `p_i`
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (h1 i) (hp i).le
  rw [← Finset.sum_mul, hp1, one_mul] at h
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum] at h
  rw [Finset.sum_comm, ← hSX] at h
  -- D3.13.2
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum fun j hj ↦ ?_))
  calc ∑ i, p i * (a j * Sw i j) = a j * ∑ i, p i * Sw i j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ a j * ST j := mul_le_mul_of_nonneg_left (h2 j hj) (ha j hj)

end D313

end AreaLaw
