import AreaLawRefactored.S03_InitialBox.BufferDiscount
import AreaLawForMathlib.Analysis.Matrix.TraceHolder

/-!
# §3.2 Optimized filters (proof of Lemma 3.2, D3.7–D3.13)

Digest `digest/03-initial-box.md` (D3.7–D3.13), paper `paper/sections/02-initial.tex`,
lines 335–573.
-/

namespace AreaLaw

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker

/-! ## D3.7 Optimized filters commute with their marginals -/

/-- The ordered product `f (k-1) ⋯ f 0`. -/
def prodDesc {n : Type*} [Fintype n] [DecidableEq n] (f : ℕ → Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 1
  | k + 1 => f k * prodDesc f k

section D371

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- D3.7. A feasible filter `L ≥ ε`, `Tr L^{2/a} = 1`, written spectrally:
`L = V diag(x^{a/2}) V*` with `V` unitary, `x_i = l_i^{2/a} ≥ f = ε^{2/a}` and `∑ x_i = 1`. -/
def IsFilter (f a : ℝ) (L : Matrix m m ℂ) : Prop :=
  ∃ V : Matrix m m ℂ, Vᴴ * V = 1 ∧ ∃ x : m → ℝ, (∀ i, f ≤ x i) ∧ ∑ i, x i = 1 ∧
    L = V * diagonal (fun i ↦ ((x i ^ (a / 2) : ℝ) : ℂ)) * Vᴴ

/-- D3.7.1. The feasible filters form a compact set (`0 ≤ x_i ≤ 1`, `V` unitary). -/
theorem isCompact_setOf_isFilter {f a : ℝ} (hf : 0 ≤ f) (ha : 0 ≤ a) :
    IsCompact {L : Matrix m m ℂ | IsFilter f a L} := by
  have hS : IsCompact {x : m → ℝ | (∀ i, f ≤ x i) ∧ ∑ i, x i = 1} := by
    refine (isCompact_univ_pi fun _ : m ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_id).inter
        (isClosed_eq (by fun_prop) continuous_const) : IsClosed {x : m → ℝ | (fun _ ↦ f) ≤ x ∧
          ∑ i, x i = 1}) fun x hx ↦ Set.mem_univ_pi.mpr fun i ↦ ?_
    have h0 : ∀ k, 0 ≤ x k := fun k ↦ hf.trans (hx.1 k)
    exact ⟨h0 i, hx.2 ▸ Finset.single_le_sum (fun k _ ↦ h0 k) (Finset.mem_univ i)⟩
  have heq : {L : Matrix m m ℂ | IsFilter f a L} = (fun p : Matrix m m ℂ × (m → ℝ) ↦
      p.1 * diagonal (fun i ↦ ((p.2 i ^ (a / 2) : ℝ) : ℂ)) * p.1ᴴ) ''
      ({V : Matrix m m ℂ | Vᴴ * V = 1} ×ˢ {x | (∀ i, f ≤ x i) ∧ ∑ i, x i = 1}) := by
    ext L
    exact ⟨fun ⟨V, hV, x, hx, hs, e⟩ ↦ ⟨(V, x), ⟨hV, hx, hs⟩, e.symm⟩,
      fun ⟨⟨V, x⟩, ⟨hV, hx, hs⟩, e⟩ ↦ ⟨V, hV, x, hx, hs, e.symm⟩⟩
  rw [heq]
  refine (isCompact_setOf_conjTranspose_mul_self_eq_one.prod hS).image ?_
  have hd : Continuous fun p : Matrix m m ℂ × (m → ℝ) ↦
      diagonal (fun i ↦ ((p.2 i ^ (a / 2) : ℝ) : ℂ)) :=
    continuous_id.matrix_diagonal.comp (continuous_pi fun i ↦ Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by positivity)).comp ((continuous_apply i).comp
        continuous_snd)))
  exact (continuous_fst.matrix_mul hd).matrix_mul continuous_fst.matrix_conjTranspose

/-- D3.7.1. A feasible filter with floor `f > 0` is invertible. -/
theorem IsFilter.isUnit_det {f a : ℝ} (hf : 0 < f) {L : Matrix m m ℂ} (hL : IsFilter f a L) :
    IsUnit L.det := by
  obtain ⟨V, hV, x, hx, -, rfl⟩ := hL
  have hV' : IsUnit V.det := isUnit_det_of_left_inverse hV
  rw [det_mul, det_mul, det_diagonal, isUnit_iff_ne_zero]
  refine mul_ne_zero (mul_ne_zero hV'.ne_zero (Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_))
    (isUnit_det_of_right_inverse (by rwa [mul_eq_one_comm] at hV)).ne_zero
  exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hf.trans_le (hx i)) _).ne'

/-- D3.7.1. The uniform filter `(dim)^{-a/2}` is feasible when `dim · f ≤ 1`. -/
theorem isFilter_uniform [Nonempty m] {f a : ℝ} (hcard : Fintype.card m * f ≤ 1) :
    IsFilter f a (diagonal fun _ : m ↦ ((((Fintype.card m : ℝ)⁻¹) ^ (a / 2) : ℝ) : ℂ)) := by
  have hpos : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  refine ⟨1, by simp, fun _ ↦ (Fintype.card m : ℝ)⁻¹, fun _ ↦ ?_, ?_, by simp⟩
  · rw [inv_eq_one_div, le_div_iff₀ hpos, mul_comm]; exact hcard
  · simp [Finset.sum_const, Finset.card_univ, hpos.ne']

/-- D3.7.2. Feasibility is invariant under unitary conjugation (same spectrum). -/
theorem IsFilter.conj {f a : ℝ} {L W : Matrix m m ℂ} (hL : IsFilter f a L) (hW : Wᴴ * W = 1) :
    IsFilter f a (W * L * Wᴴ) := by
  obtain ⟨V, hV, x, hx, hs, rfl⟩ := hL
  refine ⟨W * V, ?_, x, hx, hs, by simp only [conjTranspose_mul, Matrix.mul_assoc]⟩
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul, hV]

/-- D3.7.2. For anti-Hermitian `B` and real `t`, `L(t) = e^{tB} L e^{-tB}` is feasible
whenever `L` is. -/
theorem IsFilter.exp_conj {f a : ℝ} {L B : Matrix m m ℂ} (hL : IsFilter f a L) (hB : Bᴴ = -B)
    (t : ℝ) :
    IsFilter f a (NormedSpace.exp ((t : ℂ) • B) * L * NormedSpace.exp ((-(t : ℂ)) • B)) := by
  have hc : (NormedSpace.exp ((t : ℂ) • B))ᴴ = NormedSpace.exp ((-(t : ℂ)) • B) := by
    rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hB, Complex.star_def, Complex.conj_ofReal,
      smul_neg, neg_smul]
  have hu : (NormedSpace.exp ((t : ℂ) • B))ᴴ * NormedSpace.exp ((t : ℂ) • B) = 1 := by
    rw [hc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl B).smul_left _ |>.smul_right _),
      neg_smul, neg_add_cancel, NormedSpace.exp_zero]
  have := hL.conj hu
  rwa [hc] at this

end D371

section D371chain

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

omit [∀ i, Fintype (loc i)] in
/-- `A ↦ A ⊗ 1` is continuous. -/
theorem continuous_extendId {S T : Finset σ} (h : S ⊆ T) :
    Continuous (Arealaw.extendId (loc := loc) (𝕜 := ℂ) h) :=
  continuous_pi fun w ↦ continuous_pi fun w' ↦ by
    simp only [Arealaw.extendId, Matrix.of_apply]
    split_ifs
    exacts [(continuous_apply _).comp (continuous_apply _), continuous_const]

/-- D3.7. The product `K = (L_{k-1} ⊗ 1) ⋯ (L_0 ⊗ 1)` of filters on `X_j ⊆ U`. -/
noncomputable def filterProd (hX : ∀ j, X j ⊆ U)
    (L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ) (k : ℕ) :
    Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ :=
  prodDesc (fun j ↦ Arealaw.extendId (hX j) (L j)) k

/-- `L ↦ K` is continuous (D3.7.1: `N` is continuous). -/
theorem continuous_filterProd (hX : ∀ j, X j ⊆ U) (k : ℕ) :
    Continuous fun L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ ↦
      filterProd hX L k := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    exact ((continuous_extendId (hX k)).comp (continuous_apply k)).matrix_mul ih

/-- D3.7.1. Feasible products with positive floors are invertible. -/
theorem isUnit_det_filterProd (hX : ∀ j, X j ⊆ U)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsUnit (L j).det) (k : ℕ) : IsUnit (filterProd hX L k).det := by
  induction k with
  | zero => simp [filterProd, prodDesc]
  | succ k ih =>
    rw [filterProd, prodDesc, det_mul]
    refine IsUnit.mul (isUnit_det_of_left_inverse (B := Arealaw.extendId (hX k) (L k)⁻¹) ?_) ih
    rw [← Arealaw.extendId_mul, nonsing_inv_mul _ (hL k), Arealaw.extendId_one]

/-- D3.7.1. Existence: for floors `f_j > 0` with `(dim H_{X_j}) f_j ≤ 1`, the norm
`N = ‖L_{k-1} ⋯ L_0 Ω‖` attains its maximum over feasible filters, and `N > 0`. -/
theorem step_3_7_1 (hX : ∀ j, X j ⊆ U) (k : ℕ) {f a : ℕ → ℝ} (hf : ∀ j, 0 < f j)
    (ha : ∀ j, 0 ≤ a j) (hne : ∀ j, Nonempty (Arealaw.Reg loc (X j)))
    (hcard : ∀ j, Fintype.card (Arealaw.Reg loc (X j)) * f j ≤ 1)
    {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)} (hΩ : Ω ≠ 0) :
    ∃ L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L j)) ∧
      (∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
        (∀ j, IsFilter (f j) (a j) (L' j)) →
          ‖toEuclideanLin (filterProd hX L' k) Ω‖ ≤ ‖toEuclideanLin (filterProd hX L k) Ω‖) ∧
      0 < ‖toEuclideanLin (filterProd hX L k) Ω‖ := by
  -- D3.7.1: the feasible set is nonempty and compact, `N` is continuous
  have hcpt := isCompact_univ_pi fun j ↦ isCompact_setOf_isFilter (m := Arealaw.Reg loc (X j))
    (hf j).le (ha j)
  have hne' : (Set.univ.pi fun j ↦ {M | IsFilter (f j) (a j) M}).Nonempty :=
    ⟨fun j ↦ diagonal fun _ ↦ ((((Fintype.card (Arealaw.Reg loc (X j)) : ℝ)⁻¹) ^ (a j / 2) : ℝ)
      : ℂ), fun j _ ↦ isFilter_uniform (hcard j)⟩
  have hcont : Continuous fun L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j))
      (Arealaw.Reg loc (X j)) ℂ ↦ ‖toEuclideanLin (filterProd hX L k) Ω‖ := by
    refine continuous_norm.comp ?_
    simp only [toLpLin_apply]
    exact (PiLp.continuous_toLp 2 _).comp ((continuous_filterProd hX k).matrix_mulVec
      continuous_const)
  obtain ⟨L, hL, hmax⟩ := hcpt.exists_isMaxOn hne' hcont.continuousOn
  refine ⟨L, fun j ↦ hL j trivial, fun L' hL' ↦ hmax (fun j _ ↦ hL' j), norm_pos_iff.2 ?_⟩
  -- D3.7.1: feasible products are invertible, so `N > 0`
  intro h0
  have hK := isUnit_det_filterProd hX (fun j ↦ (hL j trivial).isUnit_det (hf j)) k
  apply hΩ
  have := congrArg (toEuclideanLin (filterProd hX L k)⁻¹) h0
  rwa [← LinearMap.comp_apply, ← toLpLin_mul_same, nonsing_inv_mul _ hK, toLpLin_one,
    LinearMap.id_apply, map_zero] at this

end D371chain

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

/-- D3.7.4. A feasible filter with floor `f > 0` is positive definite. -/
theorem IsFilter.posDef {f a : ℝ} (hf : 0 < f) {L : Matrix m m ℂ} (hL : IsFilter f a L) :
    L.PosDef := by
  obtain ⟨V, hV, x, hx, -, rfl⟩ := hL
  have hD : (diagonal fun i ↦ ((x i ^ (a / 2) : ℝ) : ℂ)).PosDef :=
    posDef_diagonal_iff.2 fun i ↦ by
      exact_mod_cast Real.rpow_pos_of_pos (hf.trans_le (hx i)) _
  have hinj : Function.Injective (Vᴴ).mulVec := fun u v huv ↦ by
    have hV' : V * Vᴴ = 1 := by rwa [mul_eq_one_comm] at hV
    simpa [mulVec_mulVec, hV'] using congrArg (V *ᵥ ·) huv
  simpa using hD.conjTranspose_mul_mul_same hinj

omit [DecidableEq m] in
/-- D3.7.4. `Tr(ρB)` is imaginary for `ρ = ρ*` and `B = -B*`. -/
theorem re_trace_mul_eq_zero {ρ B : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hB : Bᴴ = -B) :
    (ρ * B).trace.re = 0 := by
  have h : star (ρ * B).trace = -(ρ * B).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hB, hρ.eq, Matrix.neg_mul, trace_neg,
      trace_mul_comm]
  have := congrArg Complex.re h
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
  linarith

end D37

section D37chain

/-- Splitting `f (j+n) ⋯ f 0` at index `j`. -/
theorem prodDesc_add {n : Type*} [Fintype n] [DecidableEq n] (f : ℕ → Matrix n n ℂ) (j k : ℕ) :
    prodDesc f (j + 1 + k) = prodDesc (fun i ↦ f (j + 1 + i)) k * f j * prodDesc f j := by
  induction k with
  | zero => simp [prodDesc]
  | succ k ih => rw [← add_assoc, prodDesc, ih, prodDesc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc]

/-- `prodDesc f k` depends only on `f 0, …, f (k-1)`. -/
theorem prodDesc_congr {n : Type*} [Fintype n] [DecidableEq n] {f g : ℕ → Matrix n n ℂ} {k : ℕ}
    (h : ∀ i < k, f i = g i) : prodDesc f k = prodDesc g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prodDesc, prodDesc, h k k.lt_succ_self, ih fun i hi ↦ h i (hi.trans k.lt_succ_self)]

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

/-- D3.7.2. `K = K_{>j} (L_j ⊗ 1) K_{<j}`. -/
theorem filterProd_add (hX : ∀ j, X j ⊆ U)
    (L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ) (j k : ℕ) :
    filterProd hX L (j + 1 + k) = prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i))
      (L (j + 1 + i))) k * Arealaw.extendId (hX j) (L j) * filterProd hX L j := by
  rw [filterProd, filterProd, prodDesc_add]

/-- D3.7.2 at the maximizer of D3.7.1: for anti-Hermitian `B` on `X_j`, with
`K_{>j} = L_{j+k} ⋯ L_{j+1}` and `w = K_{<j} Ω`, `Re ⟨K_{>j} L_j w, K_{>j} (BL_j - L_jB) w⟩ = 0`. -/
theorem step_3_7_2_filter (hX : ∀ j, X j ⊆ U) {f a : ℕ → ℝ}
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (j k : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' (j + 1 + k)) Ω‖ ≤
          ‖toEuclideanLin (filterProd hX L (j + 1 + k)) Ω‖)
    {B : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ} (hB : Bᴴ = -B) :
    (inner ℂ (toEuclideanLin (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i))
        (L (j + 1 + i))) k * Arealaw.extendId (hX j) (L j)) (toEuclideanLin (filterProd hX L j) Ω))
      (toEuclideanLin (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k *
        Arealaw.extendId (hX j) (B * L j - L j * B)) (toEuclideanLin (filterProd hX L j) Ω))).re
      = 0 := by
  let Φ : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ →ₗ[ℂ]
      Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ :=
    { toFun := Arealaw.extendId (hX j)
      map_add' := Arealaw.extendId_add _
      map_smul' := Arealaw.extendId_smul _ }
  refine step_3_7_2 Φ _ (L j) B _ (Filter.Eventually.of_forall fun t ↦ ?_)
  have hΦ : ∀ M, Φ M = Arealaw.extendId (hX j) M := fun _ ↦ rfl
  beta_reduce
  simp only [hΦ, Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, Matrix.one_mul,
    Matrix.mul_one]
  -- D3.7.2: `L_j(t) = e^{tB} L_j e^{-tB}` is feasible, the other filters are unchanged
  set M := NormedSpace.exp ((t : ℂ) • B) * L j * NormedSpace.exp ((-(t : ℂ)) • B)
  have hfeas : ∀ i, IsFilter (f i) (a i) (Function.update L j M i) := by
    intro i
    rcases eq_or_ne i j with rfl | hi
    · rw [Function.update_self]; exact (hL i).exp_conj hB t
    · rw [Function.update_of_ne hi]; exact hL i
  have h := hmax _ hfeas
  have hpre : filterProd hX (Function.update L j M) j = filterProd hX L j :=
    prodDesc_congr fun i hi ↦ by rw [Function.update_of_ne hi.ne]
  have hpost : prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i))
      (Function.update L j M (j + 1 + i))) k =
      prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k :=
    prodDesc_congr fun i _ ↦ by rw [Function.update_of_ne (by omega)]
  have e : ∀ Q : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ,
      toEuclideanLin (Q * filterProd hX L j) Ω =
      toEuclideanLin Q (toEuclideanLin (filterProd hX L j) Ω) := fun Q ↦ by
    rw [toLpLin_mul_same]; rfl
  rw [filterProd_add, filterProd_add, hpre, hpost, Function.update_self, e, e] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- D3.7.2. `BL - LB = (B - LBL⁻¹)L` for invertible `L`. -/
theorem sub_mul_inv_mul {n : Type*} [Fintype n] [DecidableEq n] {L : Matrix n n ℂ}
    (hL : IsUnit L.det) (B : Matrix n n ℂ) : B * L - L * B = (B - L * B * L⁻¹) * L := by
  rw [Matrix.sub_mul, Matrix.mul_assoc (L * B), nonsing_inv_mul _ hL, Matrix.mul_one]

/-- D3.7.2 in the paper's form: at the maximizer, with `φ = K Ω` and `K_{>j} = L_{j+k} ⋯ L_{j+1}`,
`Re ⟨φ, K_{>j} (B - L_jBL_j⁻¹) K_{>j}⁻¹ φ⟩ = 0` for anti-Hermitian `B` on `X_j`. -/
theorem step_3_7_2_pairing (hX : ∀ j, X j ⊆ U) {f a : ℕ → ℝ} (hf : ∀ j, 0 < f j)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (j k : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' (j + 1 + k)) Ω‖ ≤
          ‖toEuclideanLin (filterProd hX L (j + 1 + k)) Ω‖)
    {B : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ} (hB : Bᴴ = -B) :
    (inner ℂ (toEuclideanLin (filterProd hX L (j + 1 + k)) Ω)
      (toEuclideanLin (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k *
        Arealaw.extendId (hX j) (B - L j * B * (L j)⁻¹) *
        (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k)⁻¹)
        (toEuclideanLin (filterProd hX L (j + 1 + k)) Ω))).re = 0 := by
  set K := prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k
  have hK : IsUnit K.det :=
    isUnit_det_filterProd (X := fun i ↦ X (j + 1 + i)) (fun i ↦ hX (j + 1 + i))
      (fun i ↦ (hL (j + 1 + i)).isUnit_det (hf _)) k
  have h := step_3_7_2_filter hX hL j k hmax hB
  rw [sub_mul_inv_mul ((hL j).isUnit_det (hf j)), Arealaw.extendId_mul] at h
  have e : ∀ Q : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ,
      toEuclideanLin (Q * filterProd hX L j) Ω =
      toEuclideanLin Q (toEuclideanLin (filterProd hX L j) Ω) := fun Q ↦ by
    rw [toLpLin_mul_same]; rfl
  have e2 : ∀ P Q : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ, ∀ v,
      toEuclideanLin (P * Q) v = toEuclideanLin P (toEuclideanLin Q v) := fun P Q v ↦ by
    rw [toLpLin_mul_same]; rfl
  have hM : K * (Arealaw.extendId (hX j) (B - L j * B * (L j)⁻¹) *
      Arealaw.extendId (hX j) (L j)) = K * Arealaw.extendId (hX j) (B - L j * B * (L j)⁻¹) *
      K⁻¹ * (K * Arealaw.extendId (hX j) (L j)) := by
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hK]
  rw [hM, e2 _ (K * _)] at h
  rw [filterProd_add, e]
  exact h

/-- D3.7.3 through `K_{>j}`, for `W` on `X_{j+1}`: for nested regions and filters
`L_{j+1}, …, L_{j+m}` invertible and commuting with their marginals in `φ`,
`⟨φ, K (W ⊗ 1) K⁻¹ φ⟩ = ⟨φ, (W ⊗ 1) φ⟩` for `K = L_{j+m} ⋯ L_{j+1}`. -/
theorem step_3_7_3_prodDesc_succ (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1))
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ} (j m : ℕ)
    (φ : Arealaw.Reg loc U → ℂ) (hL : ∀ i < m, IsUnit (L (j + 1 + i)).det)
    (hc : ∀ i < m, L (j + 1 + i) * Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) =
      Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) * L (j + 1 + i))
    (W : Matrix (Arealaw.Reg loc (X (j + 1))) (Arealaw.Reg loc (X (j + 1))) ℂ) :
    star φ ⬝ᵥ ((prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) m *
      Arealaw.extendId (hX (j + 1)) W *
      (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) m)⁻¹) *ᵥ φ) =
      star φ ⬝ᵥ (Arealaw.extendId (hX (j + 1)) W *ᵥ φ) := by
  -- the conjugate `K (W ⊗ 1) K⁻¹` is again an operator on `X_{j+1+m}`, extended by `1`
  suffices h : ∃ W' : Matrix (Arealaw.Reg loc (X (j + 1 + m))) (Arealaw.Reg loc (X (j + 1 + m))) ℂ,
      prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) m *
        Arealaw.extendId (hX (j + 1)) W *
        (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) m)⁻¹ =
        Arealaw.extendId (hX (j + 1 + m)) W' ∧
      star φ ⬝ᵥ (Arealaw.extendId (hX (j + 1 + m)) W' *ᵥ φ) =
        star φ ⬝ᵥ (Arealaw.extendId (hX (j + 1)) W *ᵥ φ) by
    obtain ⟨W', e, h⟩ := h
    rw [e, h]
  induction m with
  | zero => exact ⟨W, by simp only [prodDesc, Matrix.one_mul, inv_one, Matrix.mul_one], rfl⟩
  | succ m ih =>
    obtain ⟨W', e, h⟩ := ih (fun i hi ↦ hL i (by omega)) (fun i hi ↦ hc i (by omega))
    have hu := hL m m.lt_succ_self
    have hinv : (Arealaw.extendId (hX (j + 1 + m)) (L (j + 1 + m)))⁻¹ =
        Arealaw.extendId (hX (j + 1 + m)) (L (j + 1 + m))⁻¹ :=
      Matrix.inv_eq_right_inv (by rw [← Arealaw.extendId_mul, mul_nonsing_inv _ hu,
        Arealaw.extendId_one])
    refine ⟨Arealaw.extendId (hnest (j + 1 + m)) (L (j + 1 + m) * W' * (L (j + 1 + m))⁻¹), ?_, ?_⟩
    · rw [Arealaw.extendId_extendId, prodDesc, Matrix.mul_inv_rev,
        show ∀ A P E Q R : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ,
          A * P * E * (Q * R) = A * (P * E * Q) * R from fun _ _ _ _ _ ↦ by
            simp only [Matrix.mul_assoc], e, hinv, ← Arealaw.extendId_mul, ← Arealaw.extendId_mul]
    · rw [Arealaw.extendId_extendId]
      exact (step_3_7_3 (hX (j + 1 + m)) φ hu (hc m m.lt_succ_self) W').trans h

/-- D3.7.3 through `K_{>j}`: for nested regions and filters `L_{j+1}, …, L_{j+m}` invertible and
commuting with their marginals in `φ`, `⟨φ, K (W ⊗ 1) K⁻¹ φ⟩ = ⟨φ, (W ⊗ 1) φ⟩` for
`K = L_{j+m} ⋯ L_{j+1}` and `W` on `X_j`. -/
theorem step_3_7_3_prodDesc (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1))
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ} (j m : ℕ)
    (φ : Arealaw.Reg loc U → ℂ) (hL : ∀ i < m, IsUnit (L (j + 1 + i)).det)
    (hc : ∀ i < m, L (j + 1 + i) * Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) =
      Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) * L (j + 1 + i))
    (W : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ) :
    star φ ⬝ᵥ ((prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) m *
      Arealaw.extendId (hX j) W *
      (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) m)⁻¹) *ᵥ φ) =
      star φ ⬝ᵥ (Arealaw.extendId (hX j) W *ᵥ φ) := by
  have h := step_3_7_3_prodDesc_succ hX hnest j m φ hL hc (Arealaw.extendId (hnest j) W)
  rwa [Arealaw.extendId_extendId] at h

/-- D3.7. At a maximizer of `N = ‖L_{n-1} ⋯ L_0 Ω‖` over feasible filters with floors `f_j > 0`
on nested regions `X_0 ⊆ X_1 ⊆ ⋯ ⊆ U`, every filter commutes with its marginal:
`[L_j, ρ_{φ,X_j}] = 0` for `j < n`, where `φ = K Ω`. -/
theorem step_3_7 (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1)) {f a : ℕ → ℝ}
    (hf : ∀ j, 0 < f j)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (n : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' n) Ω‖ ≤ ‖toEuclideanLin (filterProd hX L n) Ω‖)
    {j : ℕ} (hj : j < n) :
    L j * Arealaw.ptrace (hX j) (vecMulVec (filterProd hX L n *ᵥ WithLp.ofLp Ω)
      (star (filterProd hX L n *ᵥ WithLp.ofLp Ω))) =
      Arealaw.ptrace (hX j) (vecMulVec (filterProd hX L n *ᵥ WithLp.ofLp Ω)
        (star (filterProd hX L n *ᵥ WithLp.ofLp Ω))) * L j := by
  -- descending induction on `k = n - 1 - j`
  suffices H : ∀ k j, j + 1 + k = n →
      L j * Arealaw.ptrace (hX j) (vecMulVec (filterProd hX L n *ᵥ WithLp.ofLp Ω)
        (star (filterProd hX L n *ᵥ WithLp.ofLp Ω))) =
      Arealaw.ptrace (hX j) (vecMulVec (filterProd hX L n *ᵥ WithLp.ofLp Ω)
        (star (filterProd hX L n *ᵥ WithLp.ofLp Ω))) * L j from H (n - 1 - j) j (by omega)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro j hjk
  have hc := fun i (hi : i < k) ↦ ih (k - 1 - i) (by omega) (j + 1 + i) (by omega)
  subst hjk
  set φ := filterProd hX L (j + 1 + k) *ᵥ WithLp.ofLp Ω
  have hρ : (Arealaw.ptrace (hX j) (vecMulVec φ (star φ))).IsHermitian :=
    (Arealaw.posSemidef_ptrace (hX j) (Matrix.posSemidef_vecMulVec_self_star φ)).isHermitian
  refine step_3_7_4 ((hL j).posDef (hf j)) hρ fun B hB ↦ ?_
  -- D3.7.2 at the maximizer, then D3.7.3 peels `K_{>j}`: `Re Tr(ρ (B - L_jBL_j⁻¹)) = 0`
  have h := step_3_7_2_pairing hX hf hL j k hmax hB
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply] at h
  rw [dotProduct_comm, step_3_7_3_prodDesc hX hnest j k φ (fun i _ ↦ (hL _).isUnit_det (hf _))
    hc, Arealaw.dotProduct_extendId_mulVec, Matrix.mul_sub, trace_sub, Complex.sub_re,
    re_trace_mul_eq_zero hρ hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm] at h
  -- D3.7.4: `Re Tr(L_j⁻¹ ρ L_j B) = 0`
  simp only [Matrix.mul_assoc] at h ⊢
  linarith

end D37chain

/-! ## D3.8 Clipping bounds log-ratios of filter eigenvalues (D3.8.1) -/

section D381

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [Fintype m] [DecidableEq m] in
/-- D3.8.1, first order. If `‖c t‖ ≤ ‖c 0‖` for `0 < t < δ` and `c` has derivative `c'` at `0`,
then `Re ⟨c 0, c'⟩ ≤ 0`. -/
theorem step_3_8_1_curve {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {c : ℝ → E} {c' : E} (hc : HasDerivAt c c' 0) {δ : ℝ} (hδ : 0 < δ)
    (hle : ∀ t ∈ Set.Ioo 0 δ, ‖c t‖ ≤ ‖c 0‖) : (inner ℂ (c 0) c').re ≤ 0 := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hc.inner ℂ hc)
  have hfun : (⇑Complex.reCLM ∘ fun t ↦ inner ℂ (c t) (c t)) = fun t ↦ ‖c t‖ ^ 2 := by
    funext t
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [← RCLike.re_to_complex, ← @norm_sq_eq_re_inner ℂ]
  rw [hfun] at hre
  -- the right difference quotients are `≤ 0`
  have h0 := le_of_tendsto hre.tendsto_slope_zero_right (by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    have := pow_le_pow_left₀ (norm_nonneg _) (hle t (by simpa using ht)) 2
    simp only [zero_add, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht.1.le) (by linarith))
  simp only [Complex.reCLM_apply, Complex.add_re] at h0
  rw [← inner_conj_symm c', Complex.conj_re] at h0
  linarith

/-- D3.8.1. The diagonal variation `t ↦ V diag((x + tv)^{a/2}) V*` (`x > 0`) has derivative
`V diag((a/2) x^{a/2-1} v) V*` at `0`. -/
theorem hasDerivAt_conj_diagonal_rpow (V : Matrix m m ℂ) {x : m → ℝ} (hx : ∀ i, 0 < x i)
    (v : m → ℝ) (a : ℝ) :
    HasDerivAt (fun t : ℝ ↦ V * diagonal (fun i ↦ (((x i + t * v i) ^ (a / 2) : ℝ) : ℂ)) * Vᴴ)
      (V * diagonal (fun i ↦ ((a / 2 * x i ^ (a / 2 - 1) * v i : ℝ) : ℂ)) * Vᴴ) 0 := by
  let C : (m → ℂ) →L[ℝ] Matrix m m ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun c ↦ V * diagonal c * Vᴴ
      map_add' := fun c c' ↦ by
        rw [show diagonal (c + c') = diagonal c + diagonal c' from (diagonal_add c c').symm,
          Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r c ↦ by
        ext i j
        simp [mul_apply, diagonal, Finset.mul_sum, mul_assoc, mul_left_comm (r : ℂ)] }
  have hc : HasDerivAt (fun t : ℝ ↦ fun i ↦ (((x i + t * v i) ^ (a / 2) : ℝ) : ℂ))
      (fun i ↦ ((a / 2 * x i ^ (a / 2 - 1) * v i : ℝ) : ℂ)) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have h1 : HasDerivAt (fun t : ℝ ↦ x i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i)
    refine (h1.rpow_const (p := a / 2) (Or.inl (by simp [(hx i).ne']))).ofReal_comp.congr_deriv ?_
    rw [zero_mul, add_zero]
    congr 1
    ring
  exact C.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc

end D381

section D381chain

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

/-- D3.8.1. At a maximizer of `N = ‖L_{n-1} ⋯ L_0 Ω‖` over feasible filters on nested regions,
let `L_j = V diag(x^{a_j/2}) V*` and `ρ_{φ,X_j} = V diag(p) V*` in a common unitary eigenbasis
(`j < n`, `φ = KΩ`). Moving mass from a free coordinate `i` (`x_i > f_j`) to `k`, D3.7.3 peels
`K_{>j}` and gives `d log N ∝ (a_j/2)(p_k/x_k - p_i/x_i) ≤ 0`: the KKT hypothesis of
`step_3_8_2`. -/
theorem step_3_8_1 (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1)) {f a : ℕ → ℝ}
    (hf : ∀ j, 0 < f j)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (n : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' n) Ω‖ ≤ ‖toEuclideanLin (filterProd hX L n) Ω‖)
    {j : ℕ} (hj : j < n) (ha : 0 < a j)
    {V : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ} (hV : Vᴴ * V = 1)
    {x p : Arealaw.Reg loc (X j) → ℝ} (hx : ∀ i, f j ≤ x i) (hsum : ∑ i, x i = 1)
    (hLj : L j = V * diagonal (fun i ↦ ((x i ^ (a j / 2) : ℝ) : ℂ)) * Vᴴ)
    (hρ : Arealaw.ptrace (hX j) (vecMulVec (filterProd hX L n *ᵥ WithLp.ofLp Ω)
      (star (filterProd hX L n *ᵥ WithLp.ofLp Ω))) = V * diagonal (fun i ↦ (p i : ℂ)) * Vᴴ) :
    ∀ i k, f j < x i → p k / x k ≤ p i / x i := by
  intro i k hi
  rcases eq_or_ne i k with rfl | hik
  · exact le_rfl
  obtain ⟨k', rfl⟩ : ∃ k', n = j + 1 + k' := ⟨n - 1 - j, by omega⟩
  have hxpos : ∀ l, 0 < x l := fun l ↦ (hf j).trans_le (hx l)
  set A := prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k'
  set w := toEuclideanLin (filterProd hX L j) Ω
  let Φ : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ →ₗ[ℂ]
      Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ :=
    { toFun := Arealaw.extendId (hX j)
      map_add' := Arealaw.extendId_add _
      map_smul' := Arealaw.extendId_smul _ }
  have hΦ : ∀ M, Φ M = Arealaw.extendId (hX j) M := fun _ ↦ rfl
  have e2 : ∀ P Q : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ, ∀ u,
      toEuclideanLin (P * Q) u = toEuclideanLin P (toEuclideanLin Q u) := fun P Q u ↦ by
    rw [toLpLin_mul_same]; rfl
  -- D3.8.1: `N` along feasible variations of `L_j` alone is `‖A Φ(M) w‖`
  have hN : ∀ M, IsFilter (f j) (a j) M →
      ‖toEuclideanLin (A * Φ M) w‖ ≤ ‖toEuclideanLin (A * Φ (L j)) w‖ := by
    intro M hM
    have hfeas : ∀ l, IsFilter (f l) (a l) (Function.update L j M l) := by
      intro l
      rcases eq_or_ne l j with rfl | hl
      · rw [Function.update_self]; exact hM
      · rw [Function.update_of_ne hl]; exact hL l
    have h := hmax _ hfeas
    have hpre : filterProd hX (Function.update L j M) j = filterProd hX L j :=
      prodDesc_congr fun l hl ↦ by rw [Function.update_of_ne hl.ne]
    have hpost : prodDesc (fun l ↦ Arealaw.extendId (hX (j + 1 + l))
        (Function.update L j M (j + 1 + l))) k' = A :=
      prodDesc_congr fun l _ ↦ by rw [Function.update_of_ne (by omega)]
    rw [filterProd_add, filterProd_add, hpre, hpost, Function.update_self, e2, e2] at h
    simpa only [hΦ, e2] using h
  -- the variation moving mass from `i` to `k`
  set v : Arealaw.Reg loc (X j) → ℝ := Pi.single k 1 - Pi.single i 1
  have hcurve := hasDerivAt_conj_diagonal_rpow V hxpos v (a j)
  have hle : ∀ t ∈ Set.Ioo (0 : ℝ) (x i - f j),
      ‖toEuclideanLin (A * Φ (V * diagonal (fun l ↦ (((x l + t * v l) ^ (a j / 2) : ℝ) : ℂ)) *
        Vᴴ)) w‖ ≤ ‖toEuclideanLin (A * Φ (V * diagonal (fun l ↦ (((x l + 0 * v l) ^ (a j / 2) :
          ℝ) : ℂ)) * Vᴴ)) w‖ := by
    intro t ht
    simp only [zero_mul, add_zero, ← hLj]
    refine hN _ ⟨V, hV, _, fun l ↦ ?_, ?_, rfl⟩
    · by_cases hlk : l = k
      · subst hlk; simp [v, hik.symm]; linarith [hx l, ht.1]
      · by_cases hli : l = i
        · subst hli; simp [v, hlk]; linarith [ht.2]
        · simp [v, hlk, hli, hx l]
    · simp only [v, Pi.sub_apply, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      simp [hsum]
  let T : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ →L[ℂ]
      EuclideanSpace ℂ (Arealaw.Reg loc U) := LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ toEuclideanLin (A * Φ M) w
      map_add' := fun M M' ↦ by simp [Matrix.mul_add]
      map_smul' := fun c M ↦ by simp }
  have hder := step_3_8_1_curve ((T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcurve)
    (by linarith) hle
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at hder
  change (inner ℂ (toEuclideanLin (A * Φ _) w) (toEuclideanLin (A * Φ _) w)).re ≤ 0 at hder
  simp only [zero_mul, add_zero, ← hLj] at hder
  -- the derivative is `G L_j` with `G = V diag((a_j/2) v / x) V*`
  set G := V * diagonal (fun l ↦ ((a j / 2 * (v l / x l) : ℝ) : ℂ)) * Vᴴ
  have hGK : V * diagonal (fun l ↦ ((a j / 2 * x l ^ (a j / 2 - 1) * v l : ℝ) : ℂ)) * Vᴴ =
      G * L j := by
    rw [hLj, show G * (V * diagonal (fun i ↦ ((x i ^ (a j / 2) : ℝ) : ℂ)) * Vᴴ) =
      V * (diagonal (fun l ↦ ((a j / 2 * (v l / x l) : ℝ) : ℂ)) * (Vᴴ * V) *
        diagonal (fun i ↦ ((x i ^ (a j / 2) : ℝ) : ℂ))) * Vᴴ by simp only [G, Matrix.mul_assoc],
      hV, Matrix.mul_one, diagonal_mul_diagonal]
    congr 3
    funext l
    rw [Real.rpow_sub_one (hxpos l).ne']
    push_cast
    field_simp
  -- D3.7.3: peel `K_{>j}`, leaving `Re Tr(ρ G)`
  have hK : IsUnit A.det :=
    isUnit_det_filterProd (X := fun l ↦ X (j + 1 + l)) (fun l ↦ hX (j + 1 + l))
      (fun l ↦ (hL (j + 1 + l)).isUnit_det (hf _)) k'
  have hM : A * Φ (G * L j) = A * Arealaw.extendId (hX j) G * A⁻¹ * (A * Φ (L j)) := by
    simp only [hΦ, Arealaw.extendId_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hK]
  have hφ : toEuclideanLin (A * Φ (L j)) w =
      WithLp.toLp 2 (filterProd hX L (j + 1 + k') *ᵥ WithLp.ofLp Ω) := by
    rw [hΦ, ← e2, filterProd_add]; rfl
  have hc := fun l (hl : l < k') ↦ step_3_7 hX hnest hf hL (j + 1 + k') hmax
    (j := j + 1 + l) (by omega)
  rw [hGK, hM, e2 _ (A * Φ (L j)), hφ] at hder
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply] at hder
  rw [dotProduct_comm, step_3_7_3_prodDesc hX hnest j k' _ (fun l _ ↦ (hL _).isUnit_det (hf _))
    hc, Arealaw.dotProduct_extendId_mulVec, hρ] at hder
  -- `Tr(V diag(p) V* V diag(c) V*) = ∑ p_l c_l`
  rw [show V * diagonal (fun i ↦ (p i : ℂ)) * Vᴴ * G =
      V * (diagonal (fun i ↦ (p i : ℂ)) * (Vᴴ * V) *
        diagonal (fun l ↦ ((a j / 2 * (v l / x l) : ℝ) : ℂ))) * Vᴴ by
      simp only [G, Matrix.mul_assoc], hV, Matrix.mul_one, diagonal_mul_diagonal, trace_mul_cycle,
    hV, Matrix.one_mul, trace_diagonal] at hder
  have hreal : ∑ l, p l * (a j / 2 * (v l / x l)) = a j / 2 * (p k / x k - p i / x i) := by
    have hv : ∀ l, p l * (a j / 2 * (v l / x l)) =
        (if l = k then a j / 2 * (p k / x k) else 0) -
          (if l = i then a j / 2 * (p i / x i) else 0) := by
      intro l
      simp only [v, Pi.sub_apply, Pi.single_apply]
      split_ifs with h1 h2 h2 <;> subst_vars <;> first | exact absurd rfl hik | ring
    simp only [hv, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hsum' : (∑ l, (p l : ℂ) * ((a j / 2 * (v l / x l) : ℝ) : ℂ)).re =
      a j / 2 * (p k / x k - p i / x i) := by
    rw [← hreal]; push_cast; simp [Complex.re_sum]
  rw [hsum'] at hder
  nlinarith

end D381chain

/-! ## D3.8 assembled: common eigenbasis, normalisation, clipping -/

section D38eigen

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- D3.8. In any orthonormal eigenbasis `L = U diag(l) U*` of a feasible filter `L`, the
eigenvalues are `l_i = x_i^{a/2}` with `x_i ≥ f` and `∑ x_i = 1` (`x_i := l_i^{2/a}`). -/
theorem IsFilter.exists_rpow_of_eq_diagonal {f a : ℝ} (hf : 0 < f) (ha : 0 < a)
    {L U : Matrix m m ℂ} (hL : IsFilter f a L) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    {l : m → ℝ} (hLU : L = U * diagonal (fun i ↦ (l i : ℂ)) * Uᴴ) :
    ∃ x : m → ℝ, (∀ i, f ≤ x i) ∧ ∑ i, x i = 1 ∧ ∀ i, l i = x i ^ (a / 2) := by
  obtain ⟨V, hV, y, hy, hys, hLV⟩ := hL
  set W := Uᴴ * V
  have hW : Wᴴ * W = 1 := by
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ V, hU', Matrix.one_mul, hV]
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  -- `diag(l) W = W diag(y^{a/2})`
  have hd : diagonal (fun i ↦ (l i : ℂ)) * W =
      W * diagonal (fun k ↦ ((y k ^ (a / 2) : ℝ) : ℂ)) := by
    have e : diagonal (fun i ↦ (l i : ℂ)) = Uᴴ * L * U := by
      rw [hLU]; simp only [Matrix.mul_assoc]
      rw [hU, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [e, hLV]
    simp only [W, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ V, hU', Matrix.one_mul, hV, Matrix.mul_one]
  have hent : ∀ i k, W i k ≠ 0 → l i = y k ^ (a / 2) := by
    intro i k h
    have := congrFun (congrFun hd i) k
    rw [diagonal_mul, mul_diagonal, mul_comm] at this
    exact_mod_cast mul_left_cancel₀ h this
  have hrow : ∀ i, ∃ k, W i k ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    have := sum_norm_sq_row_of_mul_conjTranspose hW' i
    simp [h] at this
  have hcol : ∀ k, ∑ i, ‖W i k‖ ^ 2 = 1 := fun k ↦ by
    simpa [conjTranspose_apply, norm_star] using
      sum_norm_sq_row_of_mul_conjTranspose (W := Wᴴ)
        (by rw [conjTranspose_conjTranspose]; exact hW) k
  set x : m → ℝ := fun i ↦ l i ^ (2 / a)
  have hx : ∀ i k, W i k ≠ 0 → x i = y k := by
    intro i k h
    simp only [x]
    rw [hent i k h, ← Real.rpow_mul (hf.le.trans (hy k)), show a / 2 * (2 / a) = 1 by field_simp,
      Real.rpow_one]
  refine ⟨x, fun i ↦ ?_, ?_, fun i ↦ ?_⟩
  · obtain ⟨k, hk⟩ := hrow i
    rw [hx i k hk]; exact hy k
  · calc ∑ i, x i = ∑ i, ∑ k, ‖W i k‖ ^ 2 * x i := Finset.sum_congr rfl fun i _ ↦ by
          rw [← Finset.sum_mul, sum_norm_sq_row_of_mul_conjTranspose hW' i, one_mul]
      _ = ∑ i, ∑ k, ‖W i k‖ ^ 2 * y k := Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun k _ ↦ by
            by_cases h : W i k = 0
            · simp [h]
            · rw [hx i k h]
      _ = ∑ k, (∑ i, ‖W i k‖ ^ 2) * y k := by
          rw [Finset.sum_comm]; simp only [Finset.sum_mul]
      _ = 1 := by simp only [hcol, one_mul, hys]
  · obtain ⟨k, hk⟩ := hrow i
    rw [hx i k hk, hent i k hk]

end D38eigen

section D38

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

/-- D3.8. At a maximizer of `N = ‖L_{n-1} ⋯ L_0 Ω‖` over feasible filters on nested regions
(`j < n`, `a_j > 0`, `(dim H_{X_j}) f_j < 1`), `L_j` and `ρ_{φ,X_j}` (`φ = KΩ`) have a common
orthonormal eigenbasis, `L_j = U diag(l) U*`, `ρ_{φ,X_j} = U diag(p) U*`, in which
`|log (l_i/l_k)| ≤ (a_j/2) |log (p_i/p_k)|` whenever `p_i, p_k > 0`. -/
theorem step_3_8 (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1)) {f a : ℕ → ℝ}
    (hf : ∀ j, 0 < f j)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (n : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' n) Ω‖ ≤ ‖toEuclideanLin (filterProd hX L n) Ω‖)
    {j : ℕ} (hj : j < n) (ha : 0 < a j)
    (hcard : (Fintype.card (Arealaw.Reg loc (X j)) : ℝ) * f j < 1) :
    ∃ (V : Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ)
      (l p : Arealaw.Reg loc (X j) → ℝ), Vᴴ * V = 1 ∧ (∀ i, 0 < l i) ∧
      L j = V * diagonal (fun i ↦ (l i : ℂ)) * Vᴴ ∧
      Arealaw.ptrace (hX j) (vecMulVec (filterProd hX L n *ᵥ WithLp.ofLp Ω)
        (star (filterProd hX L n *ᵥ WithLp.ofLp Ω))) = V * diagonal (fun i ↦ (p i : ℂ)) * Vᴴ ∧
      ∀ i k, 0 < p i → 0 < p k →
        |Real.log (l i / l k)| ≤ a j / 2 * |Real.log (p i / p k)| := by
  have hρ := Arealaw.posSemidef_ptrace (hX j)
    (Matrix.posSemidef_vecMulVec_self_star (filterProd hX L n *ᵥ WithLp.ofLp Ω))
  -- D3.7: common eigenbasis
  obtain ⟨V, l, p, hV, hV', hLV, hρV⟩ := exists_unitary_diagonal_of_commute
    ((hL j).posDef (hf j)).isHermitian hρ.isHermitian (step_3_7 hX hnest hf hL n hmax hj)
  obtain ⟨x, hx, hxs, hlx⟩ := (hL j).exists_rpow_of_eq_diagonal (l := l) (hf j) ha hV hV' hLV
  have hLj : L j = V * diagonal (fun i ↦ ((x i ^ (a j / 2) : ℝ) : ℂ)) * Vᴴ := by
    rw [hLV]; simp only [hlx]; rfl
  -- D3.8.1
  have hopt := step_3_8_1 (x := x) (p := p) hX hnest hf hL n hmax hj ha hV hx hxs hLj hρV
  have hp : ∀ i, 0 ≤ p i := by
    have hd := hρ.conjTranspose_mul_mul_same V
    rw [hρV] at hd
    simp only [Matrix.mul_assoc] at hd
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, Matrix.mul_one, posSemidef_diagonal_iff] at hd
    exact fun i ↦ Complex.zero_le_real.mp (hd i)
  refine ⟨V, l, p, hV, fun i ↦ by rw [hlx]; exact Real.rpow_pos_of_pos ((hf j).trans_le (hx i)) _,
    hLV, hρV, fun i k hpi hpk ↦ ?_⟩
  set S := ∑ i, p i
  have hS : 0 < S := hpi.trans_le (Finset.single_le_sum (fun l _ ↦ hp l) (Finset.mem_univ i))
  -- D3.8.2: a free coordinate exists, as `dim · f_j < 1`
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, f j < x i₀ := by
    by_contra h
    push Not at h
    rw [Finset.sum_congr rfl (fun i _ ↦ le_antisymm (h i) (hx i)), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at hxs
    linarith
  -- D3.8.2 for `p / ∑ p` (the KKT condition is homogeneous)
  obtain ⟨lam, hlam, hxl⟩ := step_3_8_2 (p := fun i ↦ p i / S) (hf j) hx
    (fun i ↦ div_nonneg (hp i) hS.le) (by rw [← Finset.sum_div, div_self hS.ne']) hi₀
    (fun i k h ↦ by
      show p k / S / x k ≤ p i / S / x i
      rw [div_right_comm, div_right_comm (p i)]
      exact div_le_div_of_nonneg_right (hopt i k h) hS.le)
  -- D3.8.3 (ratios are scale-invariant)
  have h3 := step_3_8_3 (hf j) hlam ha.le (div_pos hpi hS) (div_pos hpk hS)
  rwa [← hxl i, ← hxl k, ← hlx i, ← hlx k, div_div_div_cancel_right₀ hS.ne'] at h3

end D38

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

section D392

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {X : ℕ → Finset σ}

/-- `(A ⊗ 1)⁻¹ = A⁻¹ ⊗ 1` for invertible `A`. -/
theorem inv_extendId {S T : Finset σ} (hST : S ⊆ T)
    {A : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ} (hA : IsUnit A.det) :
    (Arealaw.extendId hST A)⁻¹ = Arealaw.extendId hST A⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [← Arealaw.extendId_mul, mul_nonsing_inv _ hA,
    Arealaw.extendId_one])

/-- D3.9.2, split index `j`. Let `h` be supported in `S_h ⊆ X_{j+1}`, let the filters `L_i`,
`i < j` (`I_in`), commute with `h`, and let `L_{j+1}, …, L_{j+k}` (`I_out`) commute with their
marginals in `φ` (D3.7). Then for `K = L_{j+k} ⋯ L_0`,
`⟨φ, (h - KhK⁻¹) φ⟩ = ⟨φ, (h - L_jhL_j⁻¹) φ⟩`. -/
theorem step_3_9_2 (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1))
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ i, IsUnit (L i).det) (j k : ℕ) (φ : Arealaw.Reg loc U → ℂ)
    (hc : ∀ i < k, L (j + 1 + i) * Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) =
      Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) * L (j + 1 + i))
    {S : Finset σ} (hS : S ⊆ X (j + 1)) (h : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ)
    (hin : ∀ i < j, Commute (Arealaw.extendId (hX i) (L i))
      (Arealaw.extendId (hS.trans (hX (j + 1))) h)) :
    star φ ⬝ᵥ ((Arealaw.extendId (hS.trans (hX (j + 1))) h - filterProd hX L (j + 1 + k) *
      Arealaw.extendId (hS.trans (hX (j + 1))) h * (filterProd hX L (j + 1 + k))⁻¹) *ᵥ φ) =
    star φ ⬝ᵥ ((Arealaw.extendId (hS.trans (hX (j + 1))) h - Arealaw.extendId (hX j) (L j) *
      Arealaw.extendId (hS.trans (hX (j + 1))) h * (Arealaw.extendId (hX j) (L j))⁻¹) *ᵥ φ) := by
  -- `I_in`: `K_{<j}` commutes with `h`, so it cancels in `KhK⁻¹`
  have hcomm : ∀ i ≤ j,
      Commute (filterProd hX L i) (Arealaw.extendId (hS.trans (hX (j + 1))) h) := by
    intro i hi
    induction i with
    | zero => exact Commute.one_left _
    | succ i ih => exact (hin i (by omega)).mul_left (ih (by omega))
  have hK : filterProd hX L (j + 1 + k) * Arealaw.extendId (hS.trans (hX (j + 1))) h *
      (filterProd hX L (j + 1 + k))⁻¹ =
      prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k *
        (Arealaw.extendId (hX j) (L j) * Arealaw.extendId (hS.trans (hX (j + 1))) h *
          (Arealaw.extendId (hX j) (L j))⁻¹) *
        (prodDesc (fun i ↦ Arealaw.extendId (hX (j + 1 + i)) (L (j + 1 + i))) k)⁻¹ := by
    rw [filterProd_add, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc _ (filterProd hX L j), (hcomm j le_rfl).eq, ← Matrix.mul_assoc,
      mul_nonsing_inv_cancel_right _ _ (isUnit_det_filterProd hX hL j)]
  -- `L_jhL_j⁻¹` lives on `X_{j+1}`; `I_out`: peel `K_{>j}` by D3.7
  have hW : Arealaw.extendId (hX j) (L j) * Arealaw.extendId (hS.trans (hX (j + 1))) h *
      (Arealaw.extendId (hX j) (L j))⁻¹ = Arealaw.extendId (hX (j + 1))
        (Arealaw.extendId (hnest j) (L j) * Arealaw.extendId hS h *
          Arealaw.extendId (hnest j) (L j)⁻¹) := by
    rw [inv_extendId _ (hL j), Arealaw.extendId_mul, Arealaw.extendId_mul,
      Arealaw.extendId_extendId, Arealaw.extendId_extendId, Arealaw.extendId_extendId]
  rw [hK, sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, hW,
    step_3_7_3_prodDesc_succ hX hnest j k φ (fun i _ ↦ hL _) hc]

/-- D3.9.2 with `I_in` read off the supports: the filters `L_i`, `i < j`, act on regions `X_i`
disjoint from the support `S` of `h`, so they commute with `h` (`commute_extendId_extendId`). -/
theorem step_3_9_2_of_disjoint (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1))
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ i, IsUnit (L i).det) (j k : ℕ) (φ : Arealaw.Reg loc U → ℂ)
    (hc : ∀ i < k, L (j + 1 + i) * Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) =
      Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) * L (j + 1 + i))
    {S : Finset σ} (hS : S ⊆ X (j + 1)) (h : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ)
    (hd : ∀ i < j, Disjoint (X i) S) :
    star φ ⬝ᵥ ((Arealaw.extendId (hS.trans (hX (j + 1))) h - filterProd hX L (j + 1 + k) *
      Arealaw.extendId (hS.trans (hX (j + 1))) h * (filterProd hX L (j + 1 + k))⁻¹) *ᵥ φ) =
    star φ ⬝ᵥ ((Arealaw.extendId (hS.trans (hX (j + 1))) h - Arealaw.extendId (hX j) (L j) *
      Arealaw.extendId (hS.trans (hX (j + 1))) h * (Arealaw.extendId (hX j) (L j))⁻¹) *ᵥ φ) :=
  step_3_9_2 hX hnest hL j k φ hc hS h fun i hi ↦
    Arealaw.commute_extendId_extendId (hX i) (hS.trans (hX (j + 1))) (hd i hi) (L i) h

/-- D3.9.2, no split index. Let `h` be supported in `S_h ⊆ X_j`, let the filters `L_i`, `i < j`
(`I_in`), act on regions disjoint from `S_h`, and let `L_j, …, L_{j+k}` (`I_out`) commute with
their marginals in `φ` (D3.7). Then for `K = L_{j+k} ⋯ L_0`, `⟨φ, (h - KhK⁻¹) φ⟩ = 0`. -/
theorem step_3_9_2_unsplit (hX : ∀ j, X j ⊆ U) (hnest : ∀ j, X j ⊆ X (j + 1))
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ i, IsUnit (L i).det) (j k : ℕ) (φ : Arealaw.Reg loc U → ℂ)
    (hcj : L j * Arealaw.ptrace (hX j) (vecMulVec φ (star φ)) =
      Arealaw.ptrace (hX j) (vecMulVec φ (star φ)) * L j)
    (hc : ∀ i < k, L (j + 1 + i) * Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) =
      Arealaw.ptrace (hX (j + 1 + i)) (vecMulVec φ (star φ)) * L (j + 1 + i))
    {S : Finset σ} (hS : S ⊆ X j) (h : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ)
    (hd : ∀ i < j, Disjoint (X i) S) :
    star φ ⬝ᵥ ((Arealaw.extendId (hS.trans (hX j)) h - filterProd hX L (j + 1 + k) *
      Arealaw.extendId (hS.trans (hX j)) h * (filterProd hX L (j + 1 + k))⁻¹) *ᵥ φ) = 0 := by
  -- `I_in` cancels and `K_{>j}` is peeled (D3.9.2 at `j`); `L_j` is peeled by D3.7.3
  refine (step_3_9_2_of_disjoint hX hnest hL j k φ hc (hS.trans (hnest j)) h hd).trans ?_
  rw [inv_extendId _ (hL j), ← Arealaw.extendId_extendId hS (hX j), ← Arealaw.extendId_mul,
    ← Arealaw.extendId_mul, sub_mulVec, dotProduct_sub, step_3_7_3 (hX j) φ (hL j) hcj, sub_self]

end D392

/-- D3.9.6. Sum over supports: if the term of `h` is at most `C a_j²` when `h` is split by
`X_j` (`j < m`), vanishes when no `X_j` splits it, and at most `C' (r + d_j)` supports are
split by `X_j`, then the total is at most `C C' ∑_j (r + d_j) a_j² = C C' 𝓔`. -/
theorem step_3_9_6 {ι : Type*} (T : Finset ι) (e : ι → ℝ) (sp : ι → ℕ) (m : ℕ) (a w : ℕ → ℝ)
    {C C' : ℝ} (hC : 0 ≤ C) (he : ∀ h ∈ T, sp h < m → e h ≤ C * a (sp h) ^ 2)
    (he0 : ∀ h ∈ T, m ≤ sp h → e h = 0)
    (hcount : ∀ j < m, ((T.filter fun h ↦ sp h = j).card : ℝ) ≤ C' * w j) :
    ∑ h ∈ T, e h ≤ C * C' * ∑ j ∈ Finset.range m, w j * a j ^ 2 := by
  calc ∑ h ∈ T, e h
      ≤ ∑ h ∈ T, ∑ j ∈ Finset.range m, if sp h = j then C * a j ^ 2 else 0 := by
        refine Finset.sum_le_sum fun h hh ↦ ?_
        rw [Finset.sum_ite_eq]
        rcases lt_or_ge (sp h) m with hl | hl
        · rw [if_pos (Finset.mem_range.2 hl)]; exact he h hh hl
        · rw [if_neg (by simpa using hl), he0 h hh hl]
    _ = ∑ j ∈ Finset.range m, C * a j ^ 2 * ((T.filter fun h ↦ sp h = j).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ j ∈ Finset.range m, C * a j ^ 2 * (C' * w j) :=
        Finset.sum_le_sum fun j hj ↦
          mul_le_mul_of_nonneg_left (hcount j (Finset.mem_range.1 hj)) (by positivity)
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring

section D393

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- D3.9.3 (pairing `(i,k)` with `(k,i)`). For `H_{ki} = conj H_{ik}` and `l > 0`:
`Re ∑_{i,k} (1 - l_i/l_k) H_{ik} = -∑_{i,k} (cosh log (l_i/l_k) - 1) Re H_{ik}`. -/
theorem re_sum_pairing {ι : Type*} [Fintype ι] {H : ι → ι → ℂ}
    (hH : ∀ i k, H k i = star (H i k)) {l : ι → ℝ} (hl : ∀ i, 0 < l i) :
    (∑ i, ∑ k, ((1 - l i / l k : ℝ) : ℂ) * H i k).re =
      -∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) * (H i k).re := by
  have hc : ∀ i k, Real.cosh (Real.log (l i / l k)) = (l i / l k + l k / l i) / 2 := by
    intro i k
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_log (div_pos (hl i) (hl k)), inv_div]
  have hsw : ∑ i, ∑ k, l i / l k * (H i k).re = ∑ i, ∑ k, l k / l i * (H i k).re := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hH k i, Complex.star_def, Complex.conj_re]
  simp only [Complex.re_sum, Complex.re_ofReal_mul, hc]
  have e1 : ∑ i, ∑ k, (1 - l i / l k) * (H i k).re =
      ∑ i, ∑ k, (H i k).re - ∑ i, ∑ k, l i / l k * (H i k).re := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  have e2 : ∑ i, ∑ k, ((l i / l k + l k / l i) / 2 - 1) * (H i k).re =
      (∑ i, ∑ k, l i / l k * (H i k).re + ∑ i, ∑ k, l k / l i * (H i k).re) / 2 -
        ∑ i, ∑ k, (H i k).re := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, add_div, add_mul, div_mul_eq_mul_div,
      Finset.sum_add_distrib, Finset.sum_div]
  rw [e1, e2, ← hsw]; ring

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- `X ↦ ⟨Θ_j, X_{jk} Θ_k⟩` is additive. -/
theorem pair_sum (Θ : EuclideanSpace ℂ (α × β)) {κ : Type*} [Fintype κ]
    (X : κ → Matrix (α × β) (α × β) ℂ) (j k : α) :
    pair Θ (∑ x, X x) j k = ∑ x, pair Θ (X x) j k := by
  simp only [pair, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (γ := κ)]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_comm

/-- D3.9.3. Split term in Schmidt coordinates: for `h = h*` on `X_j ∪ X_j^c` and
`L_j = diag l` (`l > 0`) in the common eigenbasis of `L_j` and `ρ_{φ,X_j}`,
`Re ⟨φ, (h - L_j h L_j⁻¹) φ⟩ = -∑_{i,k} (cosh log (l_i/l_k) - 1) Re H_{ik}`,
`H_{ik} = ⟨φ_i, h_{ik} φ_k⟩ = √(p_i p_k) ∑_α (c_α)_{ik} (d_α)_{ik}`. -/
theorem step_3_9_3 {h : Matrix (α × β) (α × β) ℂ} (hh : h.IsHermitian) {l : α → ℝ}
    (hl : ∀ i, 0 < l i) (Θ : EuclideanSpace ℂ (α × β)) :
    (⟪Θ, toEuclideanLin (h - diagonal (fun x ↦ (l x.1 : ℂ)) * h *
      diagonal (fun x ↦ ((l x.1)⁻¹ : ℂ))) Θ⟫_ℂ).re =
      -∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) * (pair Θ h i k).re := by
  rw [← re_sum_pairing (H := pair Θ h) ?_ hl, ← rowWeight_one Θ, inner_rowWeight, rowWeight_one]
  · congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [pair, Matrix.sub_apply, mul_diagonal, diagonal_mul, Finset.mul_sum, star_one,
      one_mul]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
    have := (hl k).ne'
    push_cast
    field_simp
  · intro i k
    simp only [pair, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
    rw [← hh.apply (k, b') (i, b)]; ring

/-- D3.9.5. For `h = ∑_α c_α ⊗ d_α` Hermitian, `φ` in Schmidt form with weights `p`, and
`L_j = diag l` with the clipping bound of D3.8 and `0 ≤ a_j ≤ ½`: the split term is at most
`(16/e²) a_j² ∑_α ‖c_α‖ ‖d_α‖` (D3.9.3, D3.9.4, row/column sums as in D3.1.6). -/
theorem step_3_9_5 {Θ : EuclideanSpace ℂ (α × β)} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hΘ : IsSchmidt Θ p) {κ : Type*} [Fintype κ]
    (c : κ → Matrix α α ℂ) (d : κ → Matrix β β ℂ) (hh : (∑ x, c x ⊗ₖ d x).IsHermitian)
    {l : α → ℝ} (hl : ∀ i, 0 < l i) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hclip : ∀ i k, 0 < p i → 0 < p k →
      |Real.log (l i / l k)| ≤ a / 2 * |Real.log (p i / p k)|) :
    |(⟪Θ, toEuclideanLin ((∑ x, c x ⊗ₖ d x) - diagonal (fun x ↦ (l x.1 : ℂ)) *
      (∑ x, c x ⊗ₖ d x) * diagonal (fun x ↦ ((l x.1)⁻¹ : ℂ))) Θ⟫_ℂ).re| ≤
      16 / Real.exp 2 * a ^ 2 * ∑ x, ‖c x‖ * ‖d x‖ := by
  set ω := unitRow Θ p
  set C := 8 / Real.exp 2 * a ^ 2
  have hC : 0 ≤ C := by positivity
  have hcosh : ∀ i k, 0 ≤ Real.cosh (Real.log (l i / l k)) - 1 := fun i k ↦
    sub_nonneg.2 (Real.one_le_cosh _)
  -- D3.9.4 for each pair, trivially when `p_i p_k = 0`
  have hcoef : ∀ i k, (Real.cosh (Real.log (l i / l k)) - 1) * (√(p i) * √(p k)) ≤
      C * (p i + p k) := by
    intro i k
    rcases (hp i).eq_or_lt with hi | hi
    · calc _ = 0 := by rw [← hi]; simp
        _ ≤ _ := mul_nonneg hC (add_nonneg (hp i) (hp k))
    rcases (hp k).eq_or_lt with hk | hk
    · calc _ = 0 := by rw [← hk]; simp
        _ ≤ _ := mul_nonneg hC (add_nonneg (hp i) (hp k))
    rw [mul_comm, ← Real.sqrt_mul hi.le]
    exact step_3_9_4 ha ha2 hi hk (hclip i k hi hk)
  -- the matrix elements `H_{ik} = √(p_i p_k) ∑_α (c_α)_{ik} ⟨g_i, d_α g_k⟩`
  have hpair : ∀ i k, ‖pair Θ (∑ x, c x ⊗ₖ d x) i k‖ ≤
      ∑ x, √(p i) * √(p k) * (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) := by
    intro i k
    rw [pair_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ ↦ le_of_eq ?_)
    rw [pair_kronecker, row_eq_smul_unitRow hp hΘ i, row_eq_smul_unitRow hp hΘ k, map_smul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, norm_mul, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    ring
  -- D3.9.3
  rw [step_3_9_3 hh hl, abs_neg]
  calc _ ≤ ∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) *
        ‖pair Θ (∑ x, c x ⊗ₖ d x) i k‖ :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ by
            rw [abs_mul, abs_of_nonneg (hcosh i k)]
            exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (hcosh i k)))
    _ ≤ ∑ i, ∑ k, ∑ x, C * ((p i + p k) *
        (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖)) := by
      refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
      refine (mul_le_mul_of_nonneg_left (hpair i k) (hcosh i k)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ ↦ ?_
      calc _ = (Real.cosh (Real.log (l i / l k)) - 1) * (√(p i) * √(p k)) *
            (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) := by ring
        _ ≤ C * (p i + p k) * (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) :=
          mul_le_mul_of_nonneg_right (hcoef i k) (by positivity)
        _ = _ := by ring
    _ = ∑ x, C * ∑ i, ∑ k, (p i + p k) *
        (‖c x i k‖ * ‖⟪ω i, toEuclideanLin (d x) (ω k)⟫_ℂ‖) := by
      simp only [Finset.mul_sum]
      exact (Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm).trans Finset.sum_comm
    -- D3.9.5: row/column sums
    _ ≤ ∑ x, C * (2 * (‖c x‖ * ‖d x‖)) := Finset.sum_le_sum fun x _ ↦
        mul_le_mul_of_nonneg_left (sum_add_mul_unitRow_le hp hsum hΘ (c x) (d x)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]; simp only [C]; ring

end D393

section D393region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-- A quadratic form is unchanged by the change of basis `ψ ↦ Pᴴ ψ`, `M ↦ Pᴴ M P`, for
`P Pᴴ = 1`. -/
theorem star_dotProduct_mulVec_conj {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    {P : Matrix n m ℂ} (hP : P * Pᴴ = 1) (M : Matrix n n ℂ) (ψ : n → ℂ) :
    star (Pᴴ *ᵥ ψ) ⬝ᵥ ((Pᴴ * M * P) *ᵥ (Pᴴ *ᵥ ψ)) = star ψ ⬝ᵥ (M *ᵥ ψ) := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec]
  simp only [← Matrix.mul_assoc, hP]
  rw [Matrix.one_mul, Matrix.mul_assoc M, hP, Matrix.mul_one]

/-- A quadratic form is unchanged by relabelling the index set. -/
theorem star_dotProduct_mulVec_submatrix {n m : Type*} [Fintype n] [Fintype m] (e : m ≃ n)
    (M : Matrix n n ℂ) (ψ : n → ℂ) :
    star (ψ ∘ e) ⬝ᵥ (M.submatrix e e *ᵥ (ψ ∘ e)) = star ψ ⬝ᵥ (M *ᵥ ψ) := by
  simp only [dotProduct, mulVec, submatrix_apply, Function.comp_apply, Pi.star_apply]
  refine Fintype.sum_equiv e _ _ fun x ↦ ?_
  congr 1
  exact Fintype.sum_equiv e _ _ fun y ↦ rfl

/-- D3.9.3 on regions. Let `h = h*` act on `T`, and `L = V diag(l) V*` (`V` unitary, `l > 0`)
act on `S ⊆ T`. In the Schmidt coordinates `Θ = (V* ⊗ 1) φ` of the cut `S | T ∖ S`, with
`h' = (V* ⊗ 1) h (V ⊗ 1)`:
`Re ⟨φ, (h - (L ⊗ 1) h (L ⊗ 1)⁻¹) φ⟩ = -∑_{i,k} (cosh log (l_i/l_k) - 1) Re H_{ik}`,
`H_{ik} = ⟨Θ_i, h'_{ik} Θ_k⟩`. -/
theorem step_3_9_3_region {S T : Finset σ} (hST : S ⊆ T)
    {h : Matrix (Arealaw.Reg loc T) (Arealaw.Reg loc T) ℂ} (hh : h.IsHermitian)
    {L V : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ} (hV : Vᴴ * V = 1)
    {l : Arealaw.Reg loc S → ℝ} (hl : ∀ i, 0 < l i)
    (hLV : L = V * diagonal (fun i ↦ (l i : ℂ)) * Vᴴ) (φ : Arealaw.Reg loc T → ℂ) :
    (star φ ⬝ᵥ ((h - Arealaw.extendId hST L * h * (Arealaw.extendId hST L)⁻¹) *ᵥ φ)).re =
      -∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) *
        (pair (WithLp.toLp 2 ((Vᴴ ⊗ₖ (1 : Matrix (Arealaw.Reg loc (T \ S))
            (Arealaw.Reg loc (T \ S)) ℂ)) *ᵥ (φ ∘ Arealaw.glueEquiv hST)))
          ((Vᴴ ⊗ₖ (1 : Matrix (Arealaw.Reg loc (T \ S)) (Arealaw.Reg loc (T \ S)) ℂ)) *
            h.submatrix (Arealaw.glueEquiv hST) (Arealaw.glueEquiv hST) *
            (V ⊗ₖ (1 : Matrix (Arealaw.Reg loc (T \ S)) (Arealaw.Reg loc (T \ S)) ℂ))) i k).re := by
  set e := Arealaw.glueEquiv hST
  set one : Matrix (Arealaw.Reg loc (T \ S)) (Arealaw.Reg loc (T \ S)) ℂ := 1
  set W := V ⊗ₖ one
  have hWh : Wᴴ = Vᴴ ⊗ₖ one := by simp [W, one, conjTranspose_kronecker]
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  have hW : Wᴴ * W = 1 := by
    rw [hWh, ← mul_kronecker_mul, hV, Matrix.one_mul, one_kronecker_one]
  have hW' : W * Wᴴ = 1 := by
    rw [hWh, ← mul_kronecker_mul, hV', Matrix.one_mul, one_kronecker_one]
  set D : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ := diagonal (fun i ↦ (l i : ℂ))
  set D' : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ := diagonal (fun i ↦ ((l i)⁻¹ : ℂ))
  have hDD : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i ↦ mul_inv_cancel₀ (by exact_mod_cast (hl i).ne'))
  have hinv : (Arealaw.extendId hST L)⁻¹ = Arealaw.extendId hST (V * D' * Vᴴ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Arealaw.extendId_mul, hLV]
    have : V * D * Vᴴ * (V * D' * Vᴴ) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, ← Matrix.mul_assoc D, hDD, Matrix.one_mul,
        hV']
    rw [this, Arealaw.extendId_one]
  have hext : ∀ A : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ,
      (Arealaw.extendId hST A).submatrix e e = A ⊗ₖ one := by
    intro A
    rw [Arealaw.extendId_eq_kronecker, submatrix_submatrix]
    simp [e, one]
  have hconj : ∀ A : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ,
      (V * A * Vᴴ) ⊗ₖ one = W * (A ⊗ₖ one) * Wᴴ := by
    intro A
    rw [hWh, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp [one]
  have hdiag : ∀ c : Arealaw.Reg loc S → ℂ,
      diagonal c ⊗ₖ one = diagonal (fun x ↦ c x.1) := by
    intro c
    rw [show one = diagonal (fun _ ↦ 1) from diagonal_one.symm, diagonal_kronecker_diagonal]
    simp
  set h' := Wᴴ * h.submatrix e e * W
  have hh' : h'.IsHermitian := isHermitian_conjTranspose_mul_mul W (hh.submatrix e)
  have hM : (h - Arealaw.extendId hST L * h * Arealaw.extendId hST (V * D' * Vᴴ)).submatrix e e =
      h.submatrix e e - (L ⊗ₖ one) * h.submatrix e e * ((V * D' * Vᴴ) ⊗ₖ one) := by
    rw [show (h - Arealaw.extendId hST L * h * Arealaw.extendId hST (V * D' * Vᴴ)).submatrix e e =
      h.submatrix e e -
        (Arealaw.extendId hST L * h * Arealaw.extendId hST (V * D' * Vᴴ)).submatrix e e from rfl,
      ← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _, hext, hext]
  have hM2 : Wᴴ * (h.submatrix e e - (L ⊗ₖ one) * h.submatrix e e * ((V * D' * Vᴴ) ⊗ₖ one)) * W =
      h' - diagonal (fun x ↦ (l x.1 : ℂ)) * h' * diagonal (fun x ↦ ((l x.1)⁻¹ : ℂ)) := by
    have hD1 : D ⊗ₖ one = diagonal (fun x ↦ (l x.1 : ℂ)) := hdiag _
    have hD2 : D' ⊗ₖ one = diagonal (fun x ↦ ((l x.1)⁻¹ : ℂ)) := hdiag _
    rw [hLV, hconj, hconj, hD1, hD2]
    simp only [h', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul, Matrix.mul_one]
  have key := step_3_9_3 hh' hl (WithLp.toLp 2 (Wᴴ *ᵥ (φ ∘ e)))
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply] at key
  rw [← star_dotProduct_mulVec_submatrix e, ← star_dotProduct_mulVec_conj hW', hinv, hM, hM2]
  rw [← hWh, dotProduct_comm]
  exact key

/-- D3.9.5 on regions. Let `φ` be a unit vector on `U`, `S ⊆ U`, and let
`ρ_{φ,S} = V diag(p) V*` and `L = V diag(l) V*` (`V` unitary, `l > 0`) with the clipping bound
of D3.8 and `0 ≤ a ≤ ½`. For a Hermitian term `h = Y ⊗ 1` supported on `D ⊆ U`, the split term
is at most `(16/e²) a² (dim ℋ_D)² ‖h‖`: in the Schmidt coordinates of `S | U ∖ S`
(`isSchmidt_cut_of_eq`), `h` is `∑_α c_α ⊗ d_α` over the matrix units of `ℋ_{D ∩ S}`
(D3.1.6), `‖c_α‖ ‖d_α‖ ≤ ‖h‖`, and `step_3_9_5` applies. -/
theorem step_3_9_5_region {S U D : Finset σ} (hS : S ⊆ U) (hD : D ⊆ U)
    {Y : Matrix (Arealaw.Reg loc D) (Arealaw.Reg loc D) ℂ} (hY : Y.IsHermitian)
    (φ : Arealaw.Reg loc U → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    {L V : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ} (hV : Vᴴ * V = 1)
    {l p : Arealaw.Reg loc S → ℝ} (hl : ∀ i, 0 < l i)
    (hLV : L = V * diagonal (fun i ↦ (l i : ℂ)) * Vᴴ)
    (hρ : ((OpenAI.pureState φ hφ).toSubState.restrict hS).M =
      V * diagonal (fun i ↦ (p i : ℂ)) * Vᴴ)
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hclip : ∀ i k, 0 < p i → 0 < p k →
      |Real.log (l i / l k)| ≤ a / 2 * |Real.log (p i / p k)|) :
    |(star φ ⬝ᵥ ((Arealaw.extendId hD Y - Arealaw.extendId hS L * Arealaw.extendId hD Y *
      (Arealaw.extendId hS L)⁻¹) *ᵥ φ)).re| ≤
      16 / Real.exp 2 * a ^ 2 * ((Fintype.card (Arealaw.Reg loc D) : ℝ) ^ 2 * ‖Y‖) := by
  classical
  obtain ⟨x₀⟩ : Nonempty (Arealaw.Reg loc U) := by
    by_contra hU
    rw [not_nonempty_iff] at hU
    simp [dotProduct, Finset.univ_eq_empty] at hφ
  set e := Arealaw.glueEquiv hS
  set one : Matrix (Arealaw.Reg loc (U \ S)) (Arealaw.Reg loc (U \ S)) ℂ := 1
  set Θ := WithLp.toLp 2 ((Vᴴ ⊗ₖ one) *ᵥ (φ ∘ e))
  -- the Schmidt form of `φ` at `S | U ∖ S` in the eigenbasis `V`
  have hΘ : IsSchmidt Θ p := isSchmidt_cut_of_eq hS φ hφ hV hρ
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    have h := hΘ i i
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K] at h
    have : p i = ‖row Θ i‖ ^ 2 := Complex.ofReal_injective (by push_cast; exact h.symm)
    rw [this]; positivity
  have hsum : ∑ i, p i = 1 := by
    have h2 := ((OpenAI.pureState φ hφ).restrict hS).tr_eq_one
    rw [show ((OpenAI.pureState φ hφ).restrict hS).M =
      ((OpenAI.pureState φ hφ).toSubState.restrict hS).M from rfl, hρ, trace_mul_comm,
      ← Matrix.mul_assoc, hV, Matrix.one_mul, trace_diagonal] at h2
    simpa using h2
  -- D3.1.6: `h' = ∑_{ab} (V* E_{ab} V) ⊗ h_{ab}` over the matrix units of `ℋ_{D ∩ S}`
  set w₀ : Arealaw.Reg loc (S \ (D ∩ S)) :=
    Arealaw.restr Finset.sdiff_subset (Arealaw.restr hS x₀)
  set c : Arealaw.Reg loc (D ∩ S) × Arealaw.Reg loc (D ∩ S) →
      Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ := fun ab ↦
    Vᴴ * Arealaw.extendId Finset.inter_subset_right (single ab.1 ab.2 (1 : ℂ)) * V
  set d : Arealaw.Reg loc (D ∩ S) × Arealaw.Reg loc (D ∩ S) →
      Matrix (Arealaw.Reg loc (U \ S)) (Arealaw.Reg loc (U \ S)) ℂ := fun ab ↦
    (Arealaw.extendId hD Y).submatrix
      (fun z ↦ Arealaw.glue (Arealaw.glue ab.1 w₀ : Arealaw.Reg loc S) z)
      (fun z ↦ Arealaw.glue (Arealaw.glue ab.2 w₀ : Arealaw.Reg loc S) z)
  have hdec : (Vᴴ ⊗ₖ one) * (Arealaw.extendId hD Y).submatrix e e * (V ⊗ₖ one) =
      ∑ ab, c ab ⊗ₖ d ab := by
    rw [extendId_submatrix_eq_sum hS hD Y w₀, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ab _ ↦ ?_
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    simp [one, c, d]
  have hh : (Arealaw.extendId hD Y).IsHermitian := Arealaw.isHermitian_extendId hD hY
  have hh' : (∑ ab, c ab ⊗ₖ d ab).IsHermitian := by
    rw [← hdec]
    have := isHermitian_conjTranspose_mul_mul (V ⊗ₖ one) (hh.submatrix e)
    simpa [conjTranspose_kronecker, one] using this
  -- D3.9.3 on regions, then D3.9.3–D3.9.5 in Schmidt coordinates
  rw [step_3_9_3_region hS hh hV hl hLV φ]
  change |-∑ i, ∑ k, (Real.cosh (Real.log (l i / l k)) - 1) *
    (pair Θ ((Vᴴ ⊗ₖ one) * (Arealaw.extendId hD Y).submatrix e e * (V ⊗ₖ one)) i k).re| ≤ _
  rw [hdec, ← step_3_9_3 hh' hl Θ]
  refine (step_3_9_5 hp hsum hΘ c d hh' hl ha ha2 hclip).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- `‖c_{ab}‖ ‖d_{ab}‖ ≤ ‖h‖`, and there are `(dim ℋ_{D ∩ S})² ≤ (dim ℋ_D)²` of them
  have hVn : ‖V‖ ≤ 1 := Arealaw.l2_opNorm_le_one_of_conjTranspose_mul_self hV
  have hY' : ‖Arealaw.extendId hD Y‖ ≤ ‖Y‖ := by
    rw [Arealaw.extendId_eq_kronecker, Arealaw.l2_opNorm_submatrix]
    exact Arealaw.l2_opNorm_kronecker_one_le _
  have hcd : ∀ ab, ‖c ab‖ * ‖d ab‖ ≤ ‖Y‖ := by
    intro ab
    refine (mul_le_mul ((l2_opNorm_mul_mul_le_of_le_one
      (by rwa [l2_opNorm_conjTranspose]) hVn _).trans ?_)
      ((Arealaw.l2_opNorm_submatrix_le _ (Arealaw.glue_right_injective _)
        (Arealaw.glue_right_injective _)).trans hY')
      (norm_nonneg _) zero_le_one).trans (by simp)
    rw [Arealaw.extendId_eq_kronecker, Arealaw.l2_opNorm_submatrix]
    exact (Arealaw.l2_opNorm_kronecker_one_le _).trans (by simp)
  have hκ : Fintype.card (Arealaw.Reg loc (D ∩ S) × Arealaw.Reg loc (D ∩ S)) ≤
      Fintype.card (Arealaw.Reg loc D) ^ 2 := by
    rw [Fintype.card_prod, ← sq]
    refine Nat.pow_le_pow_left (Fintype.card_le_of_surjective
      (Arealaw.restr (S := D ∩ S) Finset.inter_subset_left) fun y ↦ ?_) 2
    exact ⟨Arealaw.glue y (Arealaw.restr Finset.sdiff_subset (Arealaw.restr hD x₀)),
      Arealaw.restr_glue _ _ _⟩
  calc ∑ ab, ‖c ab‖ * ‖d ab‖ ≤ ∑ _ab : Arealaw.Reg loc (D ∩ S) × Arealaw.Reg loc (D ∩ S), ‖Y‖ :=
        Finset.sum_le_sum fun ab _ ↦ hcd ab
    _ = (Fintype.card (Arealaw.Reg loc (D ∩ S) × Arealaw.Reg loc (D ∩ S)) : ℝ) * ‖Y‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hκ) (norm_nonneg _)

end D393region

section D39assembled

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-- `|cψ⟩⟨cψ| = |c|² |ψ⟩⟨ψ|` for real `c`. -/
theorem vecMulVec_smul_self_star {n : Type*} (c : ℝ) (ψ : n → ℂ) :
    vecMulVec ((c : ℂ) • ψ) (star ((c : ℂ) • ψ)) = ((c ^ 2 : ℝ) : ℂ) • vecMulVec ψ (star ψ) := by
  ext x y
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul',
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_apply]
  push_cast; ring

/-- D3.9 (lower bound). Under a gap `H - E₀ ≥ g₀ (1 - |Ω⟩⟨Ω|)`, `g₀ ≥ 0`, `‖Ω‖ = 1`:
`0 ≤ ⟨φ, (H - E₀) φ⟩` for every `φ`. -/
theorem re_dotProduct_sub_nonneg {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    {E₀ g₀ : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ1 : ‖Ω‖ = 1) (hg₀ : 0 ≤ g₀)
    (hgap : OpenAI.HasGlobalGap H (WithLp.ofLp Ω) E₀ g₀) (φ : n → ℂ) :
    0 ≤ (star φ ⬝ᵥ ((H - (E₀ : ℂ) • 1) *ᵥ φ)).re := by
  set ψ : EuclideanSpace ℂ n := WithLp.toLp 2 φ
  have h := gap_le hgap ψ
  have hcs : ‖⟪Ω, ψ⟫_ℂ‖ ≤ ‖ψ‖ := (norm_inner_le_norm _ _).trans (by rw [hΩ1, one_mul])
  have h2 : 0 ≤ g₀ * (‖ψ‖ ^ 2 - ‖⟪Ω, ψ⟫_ℂ‖ ^ 2) :=
    mul_nonneg hg₀ (sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg _) hcs 2))
  have hn := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
  have hH : ⟪ψ, toEuclideanLin H ψ⟫_ℂ = star φ ⬝ᵥ (H *ᵥ φ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hn
  rw [hH] at h
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, Complex.sub_re,
    smul_eq_mul, Complex.re_ofReal_mul]
  change 0 ≤ (star φ ⬝ᵥ (H *ᵥ φ)).re - E₀ * (star φ ⬝ᵥ φ).re
  have hre : (star φ ⬝ᵥ φ).re = ‖ψ‖ ^ 2 := by
    rw [hn]; norm_cast
  rw [hre]
  linarith

/-- D3.9. Let `L_0, …, L_{n-1}` be feasible filters (floors `f_j > 0`, `0 < a_j ≤ ½`,
`(dim ℋ_{X_j}) f_j < 1`) on nested regions `X_0 ⊆ X_1 ⊆ ⋯ ⊆ U` maximizing
`N = ‖L_{n-1} ⋯ L_0 Ω‖`, `φ = L_{n-1} ⋯ L_0 Ω / N`. Let `H = ∑_{t ∈ T} h_t`, `h_t = Y_t ⊗ 1`
Hermitian on `D_t ⊆ U` with `(dim ℋ_{D_t})² ‖h_t‖ ≤ c₀` (D2.10), `HΩ = E₀Ω`, every support
split by `X_j` disjoint from `X_i` (`i < j`) and inside `X_{j+1}` (D3.5(d)), and at most
`C' w_j` supports split by `X_j` (D3.5(e)). Then
`⟨φ, (H - E₀) φ⟩ ≤ (16/e²) c₀ C' ∑_j w_j a_j²`. -/
theorem step_3_9 {U : Finset σ} {X : ℕ → Finset σ} (hX : ∀ j, X j ⊆ U)
    (hnest : ∀ j, X j ⊆ X (j + 1)) {f a : ℕ → ℝ} (hf : ∀ j, 0 < f j)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (n : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hΩ1 : ‖Ω‖ = 1)
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' n) Ω‖ ≤ ‖toEuclideanLin (filterProd hX L n) Ω‖)
    (ha : ∀ j < n, 0 < a j ∧ a j ≤ 1 / 2)
    (hcard : ∀ j < n, (Fintype.card (Arealaw.Reg loc (X j)) : ℝ) * f j < 1)
    {ι : Type*} (T : Finset ι) {D : ι → Finset σ} (hD : ∀ t, D t ⊆ U)
    {Y : (t : ι) → Matrix (Arealaw.Reg loc (D t)) (Arealaw.Reg loc (D t)) ℂ}
    (hY : ∀ t, (Y t).IsHermitian) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hYc : ∀ t ∈ T, (Fintype.card (Arealaw.Reg loc (D t)) : ℝ) ^ 2 * ‖Y t‖ ≤ c₀) {E₀ : ℝ}
    (hΩ : (∑ t ∈ T, Arealaw.extendId (hD t) (Y t)) *ᵥ WithLp.ofLp Ω =
      (E₀ : ℂ) • WithLp.ofLp Ω) {g₀ : ℝ} (hg₀ : 0 ≤ g₀)
    (hgap : OpenAI.HasGlobalGap (∑ t ∈ T, Arealaw.extendId (hD t) (Y t)) (WithLp.ofLp Ω) E₀ g₀)
    (hd : ∀ t ∈ T, ∀ j < n, (D t ∩ X j).Nonempty → (D t \ X j).Nonempty →
      D t ⊆ X (j + 1) ∧ ∀ i < j, Disjoint (X i) (D t))
    {C' : ℝ} {w : ℕ → ℝ}
    (hcount : ∀ j < n, ((T.filter fun t ↦ (D t ∩ X j).Nonempty ∧ (D t \ X j).Nonempty).card : ℝ)
      ≤ C' * w j) :
    let φ := ((‖toEuclideanLin (filterProd hX L n) Ω‖⁻¹ : ℝ) : ℂ) •
      (filterProd hX L n *ᵥ WithLp.ofLp Ω)
    0 ≤ (star φ ⬝ᵥ ((∑ t ∈ T, Arealaw.extendId (hD t) (Y t) - (E₀ : ℂ) • 1) *ᵥ φ)).re ∧
    (star φ ⬝ᵥ ((∑ t ∈ T, Arealaw.extendId (hD t) (Y t) - (E₀ : ℂ) • 1) *ᵥ φ)).re ≤
      16 / Real.exp 2 * c₀ * C' * ∑ j ∈ Finset.range n, w j * a j ^ 2 := by
  intro φ
  classical
  refine ⟨re_dotProduct_sub_nonneg hΩ1 hg₀ hgap φ, ?_⟩
  have hΩ0 : Ω ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at hΩ1; exact zero_ne_one hΩ1
  set K := filterProd hX L n
  set ψ := K *ᵥ WithLp.ofLp Ω
  set N := ‖toEuclideanLin K Ω‖
  have hLu : ∀ j, IsUnit (L j).det := fun j ↦ (hL j).isUnit_det (hf j)
  have hK := isUnit_det_filterProd hX hLu n
  have hN : 0 < N := by
    refine norm_pos_iff.2 fun h0 ↦ hΩ0 ?_
    have := congrArg (toEuclideanLin K⁻¹) h0
    rwa [← LinearMap.comp_apply, ← toLpLin_mul_same, nonsing_inv_mul _ hK, toLpLin_one,
      LinearMap.id_apply, map_zero] at this
  have hψψ : star ψ ⬝ᵥ ψ = ((N ^ 2 : ℝ) : ℂ) := by
    rw [dotProduct_comm]
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (toEuclideanLin K Ω)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply] at h
    rw [h]; push_cast; rfl
  have hφ1 : star φ ⬝ᵥ φ = 1 := by
    simp only [φ, star_smul, smul_dotProduct, dotProduct_smul]
    change ((N⁻¹ : ℝ) : ℂ) • (star (((N⁻¹ : ℝ) : ℂ)) • (star ψ ⬝ᵥ ψ)) = 1
    rw [hψψ, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1; field_simp
  -- the marginals of `φ` are those of `KΩ`, rescaled by `N⁻²`
  have hρφ : ∀ j, Arealaw.ptrace (hX j) (vecMulVec φ (star φ)) =
      (((N⁻¹) ^ 2 : ℝ) : ℂ) • Arealaw.ptrace (hX j) (vecMulVec ψ (star ψ)) := by
    intro j
    rw [← Arealaw.ptrace_smul, ← vecMulVec_smul_self_star]
  -- D3.7 for `φ`
  have hcomm : ∀ j < n, L j * Arealaw.ptrace (hX j) (vecMulVec φ (star φ)) =
      Arealaw.ptrace (hX j) (vecMulVec φ (star φ)) * L j := by
    intro j hj
    rw [hρφ, Matrix.mul_smul, Matrix.smul_mul, step_3_7 hX hnest hf hL n hmax hj]
  set h : ι → Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ :=
    fun t ↦ Arealaw.extendId (hD t) (Y t)
  set e : ι → ℝ := fun t ↦ (star φ ⬝ᵥ ((h t - K * h t * K⁻¹) *ᵥ φ)).re
  -- D3.9.1
  have h1 : (star φ ⬝ᵥ ((∑ t ∈ T, h t - (E₀ : ℂ) • 1) *ᵥ φ)).re = ∑ t ∈ T, e t := by
    rw [step_3_9_1 hΩ hK, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  -- the split index of a support
  set sp : ι → ℕ := fun t ↦
    if hex : ∃ j < n, (D t ∩ X j).Nonempty ∧ (D t \ X j).Nonempty then Nat.find hex else n
  have hsp : ∀ t, sp t < n → sp t < n ∧ (D t ∩ X (sp t)).Nonempty ∧ (D t \ X (sp t)).Nonempty := by
    intro t ht
    simp only [sp] at ht ⊢
    split_ifs at ht ⊢ with hex
    · exact Nat.find_spec hex
    · exact absurd ht (lt_irrefl n)
  -- D3.9.2–D3.9.5: a split term is at most `(16/e²) c₀ a_j²`
  have he : ∀ t ∈ T, sp t < n → e t ≤ 16 / Real.exp 2 * c₀ * a (sp t) ^ 2 := by
    intro t ht hlt
    obtain ⟨hj, hs1, hs2⟩ := hsp t hlt
    set j := sp t
    obtain ⟨hS, hdis⟩ := hd t ht j hj hs1 hs2
    have hk : j + 1 + (n - 1 - j) = n := by omega
    have h2 := step_3_9_2_of_disjoint hX hnest hLu j (n - 1 - j) φ
      (fun i hi ↦ hcomm _ (by omega)) hS (Y t) hdis
    rw [hk] at h2
    obtain ⟨V, l, p, hV, hl, hLV, hρV, hclip⟩ :=
      step_3_8 hX hnest hf hL n hmax hj (ha j hj).1 (hcard j hj)
    have hρ' : ((OpenAI.pureState φ hφ1).toSubState.restrict (hX j)).M =
        V * diagonal (fun i ↦ (((N⁻¹) ^ 2 * p i : ℝ) : ℂ)) * Vᴴ := by
      change Arealaw.ptrace (hX j) (vecMulVec φ (star φ)) = _
      have hdg : diagonal (fun i ↦ (((N⁻¹) ^ 2 * p i : ℝ) : ℂ)) =
          (((N⁻¹) ^ 2 : ℝ) : ℂ) • diagonal (fun i ↦ (p i : ℂ)) := by
        rw [← diagonal_smul]; congr 1; funext i; push_cast; rfl
      rw [hρφ, hρV, hdg, Matrix.mul_smul, Matrix.smul_mul]
    have hc2 : 0 < (N⁻¹) ^ 2 := by positivity
    have h5 := step_3_9_5_region (hX j) (hD t) (hY t) φ hφ1 hV hl hLV hρ' (ha j hj).1.le
      (ha j hj).2 (fun i k hi hk' ↦ by
        rw [mul_div_mul_left _ _ hc2.ne']
        exact hclip i k (pos_of_mul_pos_right hi hc2.le) (pos_of_mul_pos_right hk' hc2.le))
    calc e t ≤ |e t| := le_abs_self _
      _ = |(star φ ⬝ᵥ ((h t - Arealaw.extendId (hX j) (L j) * h t *
            (Arealaw.extendId (hX j) (L j))⁻¹) *ᵥ φ)).re| := by
          simp only [e, K]; rw [h2]
      _ ≤ 16 / Real.exp 2 * a j ^ 2 *
            ((Fintype.card (Arealaw.Reg loc (D t)) : ℝ) ^ 2 * ‖Y t‖) := h5
      _ ≤ 16 / Real.exp 2 * a j ^ 2 * c₀ :=
          mul_le_mul_of_nonneg_left (hYc t ht) (by positivity)
      _ = _ := by ring
  -- D3.9.2: an unsplit term contributes `0`
  have he0 : ∀ t ∈ T, n ≤ sp t → e t = 0 := by
    intro t ht hge
    have hns : ∀ j < n, ¬((D t ∩ X j).Nonempty ∧ (D t \ X j).Nonempty) := by
      intro j hj hs
      have hex : ∃ j < n, (D t ∩ X j).Nonempty ∧ (D t \ X j).Nonempty := ⟨j, hj, hs⟩
      have : sp t < n := by simp only [sp, dif_pos hex]; exact (Nat.find_spec hex).1
      omega
    by_cases hm : ∃ j < n, (D t ∩ X j).Nonempty
    · -- `h_t` lives in the first `X_{j₀}` it meets
      set j₀ := Nat.find hm
      obtain ⟨hj₀, hmeet⟩ := Nat.find_spec hm
      have hS : D t ⊆ X j₀ := by
        have := hns j₀ hj₀
        rw [not_and, Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at this
        exact this hmeet
      have hdis : ∀ i < j₀, Disjoint (X i) (D t) := by
        intro i hi
        have := Nat.find_min hm hi
        rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm,
          ← Finset.not_nonempty_iff_eq_empty]
        exact fun hne ↦ this ⟨by omega, hne⟩
      have hk : j₀ + 1 + (n - 1 - j₀) = n := by omega
      have h2 := step_3_9_2_unsplit hX hnest hLu j₀ (n - 1 - j₀) φ (hcomm j₀ hj₀)
        (fun i hi ↦ hcomm _ (by omega)) hS (Y t) hdis
      rw [hk] at h2
      simp only [e, K]; rw [h2, Complex.zero_re]
    · -- `h_t` misses every `X_j`: it commutes with `K`
      push Not at hm
      have hc : ∀ i ≤ n, Commute (filterProd hX L i) (h t) := by
        intro i hi
        induction i with
        | zero => exact Commute.one_left _
        | succ i ih =>
          refine (Arealaw.commute_extendId_extendId (hX i) (hD t) ?_ (L i) (Y t)).mul_left
            (ih (by omega))
          rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
          exact hm i (by omega)
      simp only [e, K]
      rw [(hc n le_rfl).eq, Matrix.mul_assoc, mul_nonsing_inv _ hK, Matrix.mul_one, sub_self,
        zero_mulVec, dotProduct_zero, Complex.zero_re]
  -- D3.9.6
  rw [h1]
  refine (step_3_9_6 (C := 16 / Real.exp 2 * c₀) (C' := C') T e sp n a w (by positivity)
    he he0 fun j hj ↦ ?_).trans_eq (by ring)
  refine le_trans ?_ (hcount j hj)
  exact_mod_cast Finset.card_le_card fun t ht ↦ by
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, by rw [← ht.2]; exact (hsp t (by rw [ht.2]; exact hj)).2⟩

end D39assembled

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

section D311assembled

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-- D3.11.3. `Tr (L²)^{1/a} = Tr L^{2/a} = 1` for a feasible filter. -/
theorem IsFilter.sum_eigenvalues_rpow {m : Type*} [Fintype m] [DecidableEq m] {f a : ℝ}
    (hf : 0 < f) (ha : 0 < a) {L : Matrix m m ℂ} (hL : IsFilter f a L) (hB : (L * L).PosSemidef) :
    ∑ j, hB.1.eigenvalues j ^ (1 / a) = 1 := by
  obtain ⟨V, hV, x, hx, hs, rfl⟩ := hL
  have hx0 : ∀ i, 0 < x i := fun i ↦ hf.trans_le (hx i)
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  have hLL : V * diagonal (fun i ↦ ((x i ^ (a / 2) : ℝ) : ℂ)) * Vᴴ *
      (V * diagonal (fun i ↦ ((x i ^ (a / 2) : ℝ) : ℂ)) * Vᴴ) =
      V * diagonal (fun i ↦ ((x i ^ a : ℝ) : ℂ)) * Vᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    congr 3
    funext i
    rw [← Complex.ofReal_mul, ← Real.rpow_add (hx0 i), add_halves]
  obtain ⟨τ, hτ⟩ := hB.1.eigenvalues_eq_of_unitary_similarity_diagonal
    (by rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]; exact hV') hLL
  rw [← Equiv.sum_comp τ]
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans hs
  rw [show hB.1.eigenvalues (τ j) = x j ^ a from congrFun hτ j, ← Real.rpow_mul (hx0 j).le,
    mul_one_div_cancel ha.ne', Real.rpow_one]

/-- `⟨φ, (H - E₀) φ⟩ = ⟨φ, H φ⟩ - E₀ ‖φ‖²`, real parts. -/
theorem re_dotProduct_sub_eq {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (E₀ : ℝ) (φ : n → ℂ) :
    (star φ ⬝ᵥ ((H - (E₀ : ℂ) • 1) *ᵥ φ)).re =
      (⟪WithLp.toLp 2 φ, toEuclideanLin H (WithLp.toLp 2 φ)⟫_ℂ).re -
        E₀ * ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ n)‖ ^ 2 := by
  have hn := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 φ : EuclideanSpace ℂ n)
  have hH : ⟪(WithLp.toLp 2 φ : EuclideanSpace ℂ n), toEuclideanLin H (WithLp.toLp 2 φ)⟫_ℂ =
      star φ ⬝ᵥ (H *ᵥ φ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hn
  rw [hH, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, Complex.sub_re,
    smul_eq_mul, Complex.re_ofReal_mul]
  have hre : (star φ ⬝ᵥ φ).re = ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ n)‖ ^ 2 := by
    change (star (WithLp.ofLp (WithLp.toLp 2 φ : EuclideanSpace ℂ n)) ⬝ᵥ
      WithLp.ofLp (WithLp.toLp 2 φ : EuclideanSpace ℂ n)).re = _
    rw [hn]; norm_cast
  rw [hre]

/-- D3.9, Output (with the gap `Δ` of D1.4): `1 - |⟨Ω, φ⟩|² ≤ C 𝓔 / Δ` for the optimized
vector `φ = KΩ/N`, `C 𝓔 = (16/e²) c₀ C' ∑_j w_j a_j²` the bound of `step_3_9`. -/
theorem step_3_9_overlap {U : Finset σ} {X : ℕ → Finset σ} (hX : ∀ j, X j ⊆ U)
    (hnest : ∀ j, X j ⊆ X (j + 1)) {f a : ℕ → ℝ} (hf : ∀ j, 0 < f j)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j)) (n : ℕ) {Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)}
    (hΩ1 : ‖Ω‖ = 1)
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' n) Ω‖ ≤ ‖toEuclideanLin (filterProd hX L n) Ω‖)
    (ha : ∀ j < n, 0 < a j ∧ a j ≤ 1 / 2)
    (hcard : ∀ j < n, (Fintype.card (Arealaw.Reg loc (X j)) : ℝ) * f j < 1)
    {ι : Type*} (T : Finset ι) {D : ι → Finset σ} (hD : ∀ t, D t ⊆ U)
    {Y : (t : ι) → Matrix (Arealaw.Reg loc (D t)) (Arealaw.Reg loc (D t)) ℂ}
    (hY : ∀ t, (Y t).IsHermitian) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hYc : ∀ t ∈ T, (Fintype.card (Arealaw.Reg loc (D t)) : ℝ) ^ 2 * ‖Y t‖ ≤ c₀) {E₀ : ℝ}
    (hΩ : (∑ t ∈ T, Arealaw.extendId (hD t) (Y t)) *ᵥ WithLp.ofLp Ω =
      (E₀ : ℂ) • WithLp.ofLp Ω) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : OpenAI.HasGlobalGap (∑ t ∈ T, Arealaw.extendId (hD t) (Y t)) (WithLp.ofLp Ω) E₀ Δ)
    (hd : ∀ t ∈ T, ∀ j < n, (D t ∩ X j).Nonempty → (D t \ X j).Nonempty →
      D t ⊆ X (j + 1) ∧ ∀ i < j, Disjoint (X i) (D t))
    {C' : ℝ} {w : ℕ → ℝ}
    (hcount : ∀ j < n, ((T.filter fun t ↦ (D t ∩ X j).Nonempty ∧ (D t \ X j).Nonempty).card : ℝ)
      ≤ C' * w j) :
    1 - ‖⟪Ω, ((‖toEuclideanLin (filterProd hX L n) Ω‖⁻¹ : ℝ) : ℂ) •
      toEuclideanLin (filterProd hX L n) Ω⟫_ℂ‖ ^ 2 ≤
      16 / Real.exp 2 * c₀ * C' * (∑ j ∈ Finset.range n, w j * a j ^ 2) / Δ := by
  obtain ⟨-, hup⟩ := step_3_9 hX hnest hf hL n hΩ1 hmax ha hcard T hD hY hc₀ hYc hΩ hΔ.le hgap
    hd hcount
  set K := filterProd hX L n
  set N := ‖toEuclideanLin K Ω‖
  have hN : 0 < N := by
    have hK := isUnit_det_filterProd hX (fun j ↦ (hL j).isUnit_det (hf j)) n
    refine norm_pos_iff.2 fun h0 ↦ ?_
    have := congrArg (toEuclideanLin K⁻¹) h0
    rw [← LinearMap.comp_apply, ← toLpLin_mul_same, nonsing_inv_mul _ hK, toLpLin_one,
      LinearMap.id_apply, map_zero] at this
    rw [this, norm_zero] at hΩ1; exact zero_ne_one hΩ1
  set ψ : EuclideanSpace ℂ (Arealaw.Reg loc U) := ((N⁻¹ : ℝ) : ℂ) • toEuclideanLin K Ω
  have hψ1 : ‖ψ‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hN.le),
      inv_mul_cancel₀ hN.ne']
  have h := gap_le hgap ψ
  have he := re_dotProduct_sub_eq (∑ t ∈ T, Arealaw.extendId (hD t) (Y t)) E₀
    (((N⁻¹ : ℝ) : ℂ) • (K *ᵥ WithLp.ofLp Ω))
  change _ = (⟪ψ, toEuclideanLin _ ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 at he
  rw [hψ1] at h he
  rw [le_div_iff₀ hΔ]
  linarith

/-- D3.11 (eq:initial-norm-lower). Let `L_0, …, L_{m-1}` maximize `N = ‖L_{m-1} ⋯ L_0 Ω‖` over
feasible filters (floors `f_j > 0`, `(dim ℋ_{X_j}) f_j < 1`, `0 < a_j ≤ ½`) on nested regions
`X_0 ⊆ X_1 ⊆ ⋯ ⊆ U`, under the hypotheses of D3.9 (`step_3_9`) with gap `Δ > 0`, overlap budget
`v = C 𝓔 / Δ ≤ ¼` (D3.10(i)), and Lemma 3.1 at `u = -a_j/(1-a_j)` for the cut `X_j | U ∖ X_j`
(`hM`, admissible by D3.10(iii)). Then
`-2 log N ≥ ∑_j (a_j S(X_j) - 1024 e ϑ 𝓑_j a_j²) - 2 m v`. -/
theorem step_3_11 {U : Finset σ} {X : ℕ → Finset σ} (hX : ∀ j, X j ⊆ U)
    (hnest : ∀ j, X j ⊆ X (j + 1)) {f a : ℕ → ℝ} (hf : ∀ j, 0 < f j) (ha0 : ∀ j, 0 ≤ a j)
    (m : ℕ) (ha : ∀ j < m, 0 < a j ∧ a j ≤ 1 / 2)
    (hne : ∀ j, Nonempty (Arealaw.Reg loc (X j)))
    (hcard : ∀ j, (Fintype.card (Arealaw.Reg loc (X j)) : ℝ) * f j < 1)
    (Ω : Arealaw.Reg loc U → ℂ) (hΩ1 : star Ω ⬝ᵥ Ω = 1)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ}
    (hL : ∀ j, IsFilter (f j) (a j) (L j))
    (hmax : ∀ L' : (j : ℕ) → Matrix (Arealaw.Reg loc (X j)) (Arealaw.Reg loc (X j)) ℂ,
      (∀ j, IsFilter (f j) (a j) (L' j)) →
        ‖toEuclideanLin (filterProd hX L' m) (WithLp.toLp 2 Ω)‖ ≤
          ‖toEuclideanLin (filterProd hX L m) (WithLp.toLp 2 Ω)‖)
    {ι : Type*} (T : Finset ι) {D : ι → Finset σ} (hD : ∀ t, D t ⊆ U)
    {Y : (t : ι) → Matrix (Arealaw.Reg loc (D t)) (Arealaw.Reg loc (D t)) ℂ}
    (hY : ∀ t, (Y t).IsHermitian) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hYc : ∀ t ∈ T, (Fintype.card (Arealaw.Reg loc (D t)) : ℝ) ^ 2 * ‖Y t‖ ≤ c₀) {E₀ : ℝ}
    (hΩ : (∑ t ∈ T, Arealaw.extendId (hD t) (Y t)) *ᵥ Ω = (E₀ : ℂ) • Ω) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : OpenAI.HasGlobalGap (∑ t ∈ T, Arealaw.extendId (hD t) (Y t)) Ω E₀ Δ)
    (hd : ∀ t ∈ T, ∀ j < m, (D t ∩ X j).Nonempty → (D t \ X j).Nonempty →
      D t ⊆ X (j + 1) ∧ ∀ i < j, Disjoint (X i) (D t))
    {C' : ℝ} (hC' : 0 ≤ C') {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hcount : ∀ j < m, ((T.filter fun t ↦ (D t ∩ X j).Nonempty ∧ (D t \ X j).Nonempty).card : ℝ)
      ≤ C' * w j)
    (hv : 16 / Real.exp 2 * c₀ * C' * (∑ j ∈ Finset.range m, w j * a j ^ 2) / Δ ≤ 1 / 4)
    {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {𝓑 : ℕ → ℝ} (h𝓑 : ∀ j, 0 ≤ 𝓑 j)
    (hM : ∀ j < m, let ρ := (OpenAI.pureState Ω hΩ1).toSubState.restrict (hX j)
      let p := ρ.psd.isHermitian.eigenvalues
      Real.log (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < p i),
          p i * Real.exp (-(-a j / (1 - a j)) * Real.log (p i))) ≤
        -a j / (1 - a j) * ρ.entropy + 512 * Real.exp 1 * ϑ * 𝓑 j * (-a j / (1 - a j)) ^ 2) :
    ∑ j ∈ Finset.range m, (a j * ((OpenAI.pureState Ω hΩ1).toSubState.restrict (hX j)).entropy -
        1024 * Real.exp 1 * ϑ * 𝓑 j * a j ^ 2) -
      2 * m * (16 / Real.exp 2 * c₀ * C' * (∑ j ∈ Finset.range m, w j * a j ^ 2) / Δ) ≤
      -2 * Real.log ‖toEuclideanLin (filterProd hX L m) (WithLp.toLp 2 Ω)‖ := by
  set Ω' : EuclideanSpace ℂ (Arealaw.Reg loc U) := WithLp.toLp 2 Ω
  set v := 16 / Real.exp 2 * c₀ * C' * (∑ j ∈ Finset.range m, w j * a j ^ 2) / Δ
  have hΩ'1 : ‖Ω'‖ = 1 := by
    have hn := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Ω'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hn
    change star Ω ⬝ᵥ Ω = _ at hn
    rw [hΩ1] at hn
    have h' : ((‖Ω'‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact hn.symm
    have : ‖Ω'‖ ^ 2 = 1 := Complex.ofReal_injective h'
    nlinarith [norm_nonneg Ω']
  have hΩ0 : Ω' ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at hΩ'1; exact zero_ne_one hΩ'1
  have hv0 : 0 ≤ v := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range m) ↦
      mul_nonneg (hw j) (sq_nonneg (a j))
    positivity
  -- D3.11.1: the prefix problems `N_k` and their maximizers
  choose Lk hLk hmaxk hNk using fun k ↦
    step_3_7_1 hX k hf ha0 hne (fun j ↦ (hcard j).le) hΩ0
  set N : ℕ → ℝ := fun k ↦ ‖toEuclideanLin (filterProd hX (Lk k) k) Ω'‖
  set x : ℕ → ℝ := fun k ↦
    ‖toEuclideanLin (Arealaw.extendId (hX (k - 1)) (Lk k (k - 1))) Ω'‖
  -- D3.9–D3.10 on every prefix: `|⟨Ω, φ_k⟩| ≥ √(1 - v)`
  have hov : ∀ k ≤ m, √(1 - v) ≤ ‖⟪Ω', (((N k)⁻¹ : ℝ) : ℂ) •
      toEuclideanLin (filterProd hX (Lk k) k) Ω'⟫_ℂ‖ := by
    intro k hk
    have h := step_3_9_overlap hX hnest hf (hLk k) k hΩ'1 (hmaxk k)
      (fun j hj ↦ ha j (by omega)) (fun j _ ↦ hcard j) T hD hY hc₀ hYc hΩ hΔ hgap
      (fun t ht j hj ↦ hd t ht j (by omega)) (fun j hj ↦ hcount j (by omega))
    have hle : 16 / Real.exp 2 * c₀ * C' * (∑ j ∈ Finset.range k, w j * a j ^ 2) / Δ ≤ v := by
      have hsub : ∑ j ∈ Finset.range k, w j * a j ^ 2 ≤ ∑ j ∈ Finset.range m, w j * a j ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
          fun j _ _ ↦ mul_nonneg (hw j) (sq_nonneg (a j))
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsub (by positivity)) hΔ.le
    rw [← Real.sqrt_sq (norm_nonneg (⟪Ω', (((N k)⁻¹ : ℝ) : ℂ) •
      toEuclideanLin (filterProd hX (Lk k) k) Ω'⟫_ℂ))]
    exact Real.sqrt_le_sqrt (by linarith)
  -- D3.11.2: telescoping
  have hstep : ∀ k, toEuclideanLin (Arealaw.extendId (hX k) (Lk (k + 1) k))
      (toEuclideanLin (filterProd hX (Lk (k + 1)) k) Ω') =
      toEuclideanLin (filterProd hX (Lk (k + 1)) (k + 1)) Ω' := by
    intro k
    rw [show filterProd hX (Lk (k + 1)) (k + 1) = Arealaw.extendId (hX k) (Lk (k + 1) k) *
      filterProd hX (Lk (k + 1)) k from rfl, toLpLin_mul_same, LinearMap.comp_apply]
  have htel : ∀ j ∈ Finset.Icc 1 m, √(1 - v) * N j ≤ x j * N (j - 1) := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.1 hj).1; omega⟩
    have hk : k + 1 ≤ m := (Finset.mem_Icc.1 hj).2
    have hLh : (Arealaw.extendId (hX k) (Lk (k + 1) k)).IsHermitian :=
      Arealaw.isHermitian_extendId (hX k) ((hLk (k + 1) k).posDef (hf k)).isHermitian
    have h2 := step_3_11_2 hLh Ω' (toEuclideanLin (filterProd hX (Lk (k + 1)) k) Ω')
      (s := √(1 - v)) (by rw [hstep]; exact hov (k + 1) hk)
    rw [hstep] at h2
    simp only [N, x, Nat.add_sub_cancel]
    exact h2.trans (mul_le_mul_of_nonneg_left (hmaxk k _ (hLk (k + 1))) (norm_nonneg _))
  have hs : 0 < √(1 - v) := Real.sqrt_pos.2 (by linarith)
  have hx : ∀ j ∈ Finset.Icc 1 m, 0 < x j := by
    intro j hj
    have h := htel j hj
    have h1 : 0 < √(1 - v) * N j := mul_pos hs (hNk j)
    by_contra hneg
    have : x j = 0 := le_antisymm (not_lt.1 hneg) (norm_nonneg _)
    rw [this, zero_mul] at h; linarith
  -- D3.11.3–D3.11.4
  have hlog : ∀ j ∈ Finset.Icc 1 m, 2 * Real.log (x j) ≤
      -(a (j - 1) * ((OpenAI.pureState Ω hΩ1).toSubState.restrict (hX (j - 1))).entropy) +
        1024 * Real.exp 1 * ϑ * 𝓑 (j - 1) * a (j - 1) ^ 2 := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.1 hj).1; omega⟩
    have hk : k < m := (Finset.mem_Icc.1 hj).2
    simp only [Nat.add_sub_cancel] at hx ⊢
    have hLh := ((hLk (k + 1) k).posDef (hf k)).isHermitian
    have hB : (Lk (k + 1) k * Lk (k + 1) k).PosSemidef := by
      have := posSemidef_conjTranspose_mul_self (Lk (k + 1) k)
      rwa [hLh.eq] at this
    have hxx : (star (Arealaw.extendId (hX k) (Lk (k + 1) k) *ᵥ Ω) ⬝ᵥ
        (Arealaw.extendId (hX k) (Lk (k + 1) k) *ᵥ Ω)).re = x (k + 1) ^ 2 := by
      have hn := inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
        (toEuclideanLin (Arealaw.extendId (hX k) (Lk (k + 1) k)) Ω')
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hn
      change _ = ((x (k + 1) : ℂ)) ^ 2 at hn
      change (star (WithLp.ofLp (toEuclideanLin (Arealaw.extendId (hX k) (Lk (k + 1) k)) Ω')) ⬝ᵥ
        WithLp.ofLp (toEuclideanLin (Arealaw.extendId (hX k) (Lk (k + 1) k)) Ω')).re = _
      rw [hn]; norm_cast
    have h4 := step_3_11_4_region (hX k) Ω hΩ1 hLh hB (ha k hk).1 (ha k hk).2 hϑ (h𝓑 k)
      ((hLk (k + 1) k).sum_eigenvalues_rpow (hf k) (ha k hk).1 hB)
      (by rw [hxx]; exact pow_pos (hx (k + 1) hj) 2) (hM k hk)
    rw [hxx, Real.log_pow] at h4
    push_cast at h4
    linarith
  -- D3.11.5
  have h5 := step_3_11_5 (N := N) (x := x) (a := fun j ↦ a (j - 1))
    (S := fun j ↦ ((OpenAI.pureState Ω hΩ1).toSubState.restrict (hX (j - 1))).entropy)
    (c := fun j ↦ 1024 * Real.exp 1 * ϑ * 𝓑 (j - 1) * a (j - 1) ^ 2) hv0 hv
    (by simp [N, filterProd, prodDesc, hΩ'1]) hNk hx htel hlog
  have hNm : N m = ‖toEuclideanLin (filterProd hX L m) Ω'‖ :=
    le_antisymm (hmax _ (hLk m)) (hmaxk m L hL)
  rw [← hNm]
  refine le_trans (le_of_eq ?_) h5
  congr 1
  refine Finset.sum_bij' (fun j _ ↦ j + 1) (fun j _ ↦ j - 1) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
    (fun j _ ↦ by simp) (fun j hj ↦ ?_) (fun j _ ↦ by simp)
  · simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢; omega
  · simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢; omega
  · simp only [Finset.mem_Icc] at hj; omega

end D311assembled

/-! ## D3.12 Zero-floor limit and the trial-norm bound -/

section D312

variable {n : Type*} [Fintype n] [DecidableEq n]

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

end AreaLaw
