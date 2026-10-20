import AreaLawRefactored.S03_InitialBox.Filters
import AreaLawForMathlib.Analysis.Matrix.SpecPow

/-!
# §3.2, D3.12.3–D3.12.6 of digest/03-initial-box.md: vector three-lines and the trial filters
-/

namespace AreaLaw

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker

section D3123

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ} {T : ℕ → Finset σ}

/-- `‖A ⊗ 1‖ ≤ ‖A‖`. -/
theorem l2_opNorm_extendId_le {S S' : Finset σ} (h : S ⊆ S')
    (A : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ) : ‖Arealaw.extendId h A‖ ≤ ‖A‖ := by
  rw [Arealaw.extendId_eq_kronecker, Arealaw.l2_opNorm_submatrix]
  exact Arealaw.l2_opNorm_kronecker_one_le A

set_option linter.unusedFintypeInType false in
/-- `A ↦ A ⊗ 1` commutes with derivatives. -/
theorem hasDerivAt_extendId {S S' : Finset σ} (h : S ⊆ S')
    {P : ℂ → Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ}
    {P' : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ} {z : ℂ} (hP : HasDerivAt P P' z) :
    HasDerivAt (fun z ↦ Arealaw.extendId h (P z)) (Arealaw.extendId h P') z := by
  let Φ : Matrix (Arealaw.Reg loc S) (Arealaw.Reg loc S) ℂ →ₗ[ℂ]
      Matrix (Arealaw.Reg loc S') (Arealaw.Reg loc S') ℂ :=
    { toFun := Arealaw.extendId h, map_add' := Arealaw.extendId_add h
      map_smul' := Arealaw.extendId_smul h }
  exact (⟨Φ, continuous_extendId h⟩ : _ →L[ℂ] _).hasFDerivAt.comp_hasDerivAt z hP

/-- `‖(L_{k-1} ⊗ 1) ⋯ (L_0 ⊗ 1)‖ ≤ ∏ c_j` when `‖L_j‖ ≤ c_j`. -/
theorem norm_filterProd_le (hTU : ∀ j, T j ⊆ U)
    {L : (j : ℕ) → Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ} {c : ℕ → ℝ}
    (hc : ∀ j, ‖L j‖ ≤ c j) (k : ℕ) : ‖filterProd hTU L k‖ ≤ ∏ j ∈ Finset.range k, c j := by
  induction k with
  | zero => exact Arealaw.l2_opNorm_one_le
  | succ k ih =>
    rw [Finset.prod_range_succ, mul_comm]
    exact (norm_mul_le _ _).trans (mul_le_mul ((l2_opNorm_extendId_le _ _).trans (hc k)) ih
      (norm_nonneg _) ((norm_nonneg _).trans (hc k)))

variable {W : (j : ℕ) → Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ}

/-- D3.12.3. For `M_j = W_j diag(l_j) W_j*` on `T_j ⊆ U` and a unit vector `ξ`,
`F(z) = M_{m-1}^z ⋯ M_0^z ξ` is analytic, bounded on `0 ≤ Re z ≤ 1`, and of norm at most `1`
on `Re z = 0`. -/
theorem step_3_12_3 (hTU : ∀ j, T j ⊆ U) (hW : ∀ j, (W j)ᴴ * W j = 1)
    (l : (j : ℕ) → Arealaw.Reg loc (T j) → ℝ) (m : ℕ)
    {ξ : EuclideanSpace ℂ (Arealaw.Reg loc U)} (hξ : ‖ξ‖ = 1) :
    let F := fun z ↦ toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j) z) m) ξ
    Differentiable ℂ F ∧
      BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) ∧
      ∀ z ∈ Complex.re ⁻¹' {0}, ‖F z‖ ≤ 1 := by
  intro F
  have hF : ∀ z, ‖F z‖ ≤ ‖filterProd hTU (fun j ↦ specPow (W j) (l j) z) m‖ := fun z ↦
    (l2_opNorm_mulVec _ ξ).trans (by rw [hξ, mul_one])
  refine ⟨fun z ↦ ?_, ⟨∏ j ∈ Finset.range m, Real.exp ‖fun k ↦ Real.log (l j k)‖, ?_⟩,
    fun z hz ↦ ?_⟩
  -- D3.12.3: `F` is analytic
  · have hK : ∀ k, DifferentiableAt ℂ (fun z ↦ filterProd hTU (fun j ↦ specPow (W j) (l j) z) k)
        z := by
      intro k
      induction k with
      | zero => exact differentiableAt_const _
      | succ k ih =>
        exact (hasDerivAt_extendId (hTU k) (hasDerivAt_specPow _ _ z)).differentiableAt.mul ih
    exact (LinearMap.toContinuousLinearMap ((LinearMap.applyₗ ξ).comp
      toEuclideanLin.toLinearMap)).differentiableAt.comp z (hK m)
  -- D3.12.3: `F` is bounded on the strip
  · rintro _ ⟨z, hz, rfl⟩
    exact (hF z).trans (norm_filterProd_le hTU (fun j ↦ norm_specPow_le (hW j) (l j) hz.1 hz.2) m)
  -- D3.12.3: `‖F(iy)‖ ≤ 1` (unitaries)
  · have hz' : z = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [show z.re = 0 from hz]
    refine (hF z).trans ((norm_filterProd_le hTU (c := fun _ ↦ 1) (fun j ↦ ?_) m).trans
      (by simp))
    rw [hz']
    exact l2_opNorm_le_one_of_mul_conjTranspose (specPow_mul_conjTranspose_I (hW j) _ _)

/-- D3.12.4. With `T_j ⊆ T_{j+1}`, `V_j = U_{j-1} ⋯ U_0` for `U_j = M_j^{iy}` is `V_j ⊗ 1` for a
unitary `V_j` on `T_j`. -/
theorem exists_filterProd_specPow_I (hTU : ∀ j, T j ⊆ U) (hT : ∀ j, T j ⊆ T (j + 1))
    (hW : ∀ j, (W j)ᴴ * W j = 1) (l : (j : ℕ) → Arealaw.Reg loc (T j) → ℝ) (y : ℝ) :
    ∃ V : (j : ℕ) → Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ,
      (∀ j, V j * (V j)ᴴ = 1) ∧ ∀ j,
        filterProd hTU (fun j ↦ specPow (W j) (l j) (y * Complex.I)) j =
          Arealaw.extendId (hTU j) (V j) := by
  let V : (j : ℕ) → Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ := fun j ↦
    Nat.rec (motive := fun j ↦ Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ) 1
      (fun j V ↦ Arealaw.extendId (hT j) (specPow (W j) (l j) (y * Complex.I) * V)) j
  refine ⟨V, fun j ↦ ?_, fun j ↦ ?_⟩
  · induction j with
    | zero => simp [V]
    | succ j ih =>
      change Arealaw.extendId (hT j) (specPow (W j) (l j) (y * Complex.I) * V j) *
        (Arealaw.extendId (hT j) (specPow (W j) (l j) (y * Complex.I) * V j))ᴴ = 1
      rw [← Arealaw.extendId_conjTranspose, ← Arealaw.extendId_mul, conjTranspose_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc (V j), ih, Matrix.one_mul,
        specPow_mul_conjTranspose_I (hW j), Arealaw.extendId_one]
  · induction j with
    | zero => simp [V, filterProd, prodDesc]
    | succ j ih =>
      change _ * filterProd hTU _ j = Arealaw.extendId (hTU (j + 1))
        (Arealaw.extendId (hT j) (specPow (W j) (l j) (y * Complex.I) * V j))
      rw [ih, extendId_extendId, ← Arealaw.extendId_mul]

/-- D3.12.4 on regions. If `‖M_{m-1} ⋯ M_0 ξ‖ ≤ B` for all zero-floor filters `M_j` on `T_j`,
then `‖F(1 + iy)‖ ≤ B`: `F(1 + iy) = (U_m ⋯ U_1) (V_{m-1}^* M_m V_{m-1}) ⋯ (V_0^* M_1 V_0) ξ` with
each `V_{j-1}^* M_j V_{j-1}` a filter on `T_j`. -/
theorem step_3_12_4_region (hTU : ∀ j, T j ⊆ U) (hT : ∀ j, T j ⊆ T (j + 1))
    (hW : ∀ j, (W j)ᴴ * W j = 1) {l : (j : ℕ) → Arealaw.Reg loc (T j) → ℝ}
    (hl : ∀ j x, 0 < l j x) {a : ℕ → ℝ}
    (hM : ∀ j, IsFilter 0 (a j) (W j * diagonal (fun x ↦ (l j x : ℂ)) * (W j)ᴴ)) (m : ℕ)
    (ξ : EuclideanSpace ℂ (Arealaw.Reg loc U)) {B : ℝ}
    (hB : ∀ M : (j : ℕ) → Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ,
      (∀ j, IsFilter 0 (a j) (M j)) → ‖toEuclideanLin (filterProd hTU M m) ξ‖ ≤ B) (y : ℝ) :
    ‖toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j) (1 + y * Complex.I)) m) ξ‖ ≤
      B := by
  obtain ⟨V, hV, hVe⟩ := exists_filterProd_specPow_I hTU hT hW l y
  set U' := fun j ↦ Arealaw.extendId (hTU j) (specPow (W j) (l j) (y * Complex.I))
  have hU' : ∀ j, U' j * (U' j)ᴴ = 1 := fun j ↦ by
    rw [← Arealaw.extendId_conjTranspose, ← Arealaw.extendId_mul,
      specPow_mul_conjTranspose_I (hW j), Arealaw.extendId_one]
  have hVe' : ∀ j, prodDesc U' j = Arealaw.extendId (hTU j) (V j) := hVe
  -- D3.12.4: `M_j^{1+iy} = U_j M_j`, then the unitaries move to the left
  have h1 : filterProd hTU (fun j ↦ specPow (W j) (l j) (1 + y * Complex.I)) m =
      prodDesc U' m * filterProd hTU (fun j ↦ (V j)ᴴ * (W j * diagonal (fun x ↦ (l j x : ℂ)) *
        (W j)ᴴ) * V j) m := by
    calc _ = prodDesc (fun j ↦ U' j * Arealaw.extendId (hTU j)
          (W j * diagonal (fun x ↦ (l j x : ℂ)) * (W j)ᴴ)) m := by
          refine congrArg (prodDesc · m) (funext fun j ↦ ?_)
          change Arealaw.extendId (hTU j) (specPow (W j) (l j) (1 + y * Complex.I)) = _
          rw [add_comm, specPow_add (hW j), specPow_one _ (hl j), Arealaw.extendId_mul]
      _ = _ := step_3_12_4 U' _ hU' m
      _ = _ := by
          refine congrArg (prodDesc U' m * prodDesc · m) (funext fun j ↦ ?_)
          change (prodDesc U' j)ᴴ * Arealaw.extendId (hTU j) (W j * diagonal (fun x ↦ (l j x : ℂ)) *
            (W j)ᴴ) * prodDesc U' j = Arealaw.extendId (hTU j) ((V j)ᴴ *
              (W j * diagonal (fun x ↦ (l j x : ℂ)) * (W j)ᴴ) * V j)
          rw [hVe', ← Arealaw.extendId_conjTranspose, ← Arealaw.extendId_mul,
            ← Arealaw.extendId_mul]
  rw [h1, toLpLin_mul_same, LinearMap.comp_apply, hVe']
  have hK := hB (fun j ↦ (V j)ᴴ * (W j * diagonal (fun x ↦ (l j x : ℂ)) * (W j)ᴴ) * V j)
    fun j ↦ by
      have := (hM j).conj (W := (V j)ᴴ) (by rw [conjTranspose_conjTranspose]; exact hV j)
      rwa [conjTranspose_conjTranspose] at this
  exact (norm_toEuclideanLin_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
    ((l2_opNorm_extendId_le _ _).trans (l2_opNorm_le_one_of_mul_conjTranspose (hV m)))) |>.trans hK

/-- `z ↦ M_{k-1}^z ⋯ M_0^z` is `1` at `z = 0`. -/
theorem filterProd_specPow_zero (hTU : ∀ j, T j ⊆ U) (hW : ∀ j, (W j)ᴴ * W j = 1)
    (l : (j : ℕ) → Arealaw.Reg loc (T j) → ℝ) (k : ℕ) :
    filterProd hTU (fun j ↦ specPow (W j) (l j) 0) k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Arealaw.extendId (hTU k) (specPow (W k) (l k) 0) * filterProd hTU _ k = 1
    rw [ih, specPow_zero (hW k), Arealaw.extendId_one, Matrix.mul_one]

/-- The derivative at `0` of `z ↦ M_{k-1}^z ⋯ M_0^z` is `∑_j log M_j ⊗ 1`. -/
theorem hasDerivAt_filterProd_specPow_zero (hTU : ∀ j, T j ⊆ U) (hW : ∀ j, (W j)ᴴ * W j = 1)
    (l : (j : ℕ) → Arealaw.Reg loc (T j) → ℝ) (k : ℕ) :
    HasDerivAt (fun z ↦ filterProd hTU (fun j ↦ specPow (W j) (l j) z) k)
      (∑ j ∈ Finset.range k, Arealaw.extendId (hTU j)
        (W j * diagonal (fun x ↦ (Real.log (l j x) : ℂ)) * (W j)ᴴ)) 0 := by
  induction k with
  | zero => exact hasDerivAt_const (0 : ℂ) (1 : Matrix (Arealaw.Reg loc U) _ ℂ)
  | succ k ih =>
    have h1 := hasDerivAt_extendId (hTU k) (hasDerivAt_specPow (W k) (l k) 0)
    refine (h1.mul ih).congr_deriv ?_
    rw [filterProd_specPow_zero hTU hW l k, specPow_zero (hW k), Arealaw.extendId_one,
      Matrix.mul_one, Matrix.one_mul, Finset.sum_range_succ, add_comm]
    simp

/-- D3.12.5 (three lines). If `‖M_{m-1} ⋯ M_0 ξ‖ ≤ B` for all zero-floor filters `M_j` on
`T_j`, then `‖M_{m-1}^x ⋯ M_0^x ξ‖ ≤ B^x` for `0 ≤ x ≤ 1`. -/
theorem norm_filterProd_specPow_le_rpow (hTU : ∀ j, T j ⊆ U) (hT : ∀ j, T j ⊆ T (j + 1))
    (hW : ∀ j, (W j)ᴴ * W j = 1) {l : (j : ℕ) → Arealaw.Reg loc (T j) → ℝ}
    (hl : ∀ j x, 0 < l j x) {a : ℕ → ℝ}
    (hM : ∀ j, IsFilter 0 (a j) (W j * diagonal (fun x ↦ (l j x : ℂ)) * (W j)ᴴ)) (m : ℕ)
    {ξ : EuclideanSpace ℂ (Arealaw.Reg loc U)} (hξ : ‖ξ‖ = 1) {B : ℝ}
    (hB : ∀ M : (j : ℕ) → Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ,
      (∀ j, IsFilter 0 (a j) (M j)) → ‖toEuclideanLin (filterProd hTU M m) ξ‖ ≤ B)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j) x) m) ξ‖ ≤ B ^ x := by
  obtain ⟨hd, hbdd, h0⟩ := step_3_12_3 hTU hW l m hξ
  have h1 : ∀ z ∈ Complex.re ⁻¹' {1},
      ‖toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j) z) m) ξ‖ ≤ B := by
    intro z hz
    have hz' : z = 1 + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [show z.re = 1 from hz]
    rw [hz']
    exact step_3_12_4_region hTU hT hW hl hM m ξ hB z.im
  have hmem : (x : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hx0, hx1]
  simpa using Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' _ hmem
    hd.diffContOnCl hbdd h0 h1

/-- D3.12.5 (derivative at `0⁺`). Under the hypotheses of the three-lines bound with `B > 0`,
`∑_j Re ⟨ξ, (log M_j ⊗ 1) ξ⟩ ≤ log B`. -/
theorem step_3_12_5 (hTU : ∀ j, T j ⊆ U) (hT : ∀ j, T j ⊆ T (j + 1))
    (hW : ∀ j, (W j)ᴴ * W j = 1) {l : (j : ℕ) → Arealaw.Reg loc (T j) → ℝ}
    (hl : ∀ j x, 0 < l j x) {a : ℕ → ℝ}
    (hM : ∀ j, IsFilter 0 (a j) (W j * diagonal (fun x ↦ (l j x : ℂ)) * (W j)ᴴ)) (m : ℕ)
    {ξ : EuclideanSpace ℂ (Arealaw.Reg loc U)} (hξ : ‖ξ‖ = 1) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ M : (j : ℕ) → Matrix (Arealaw.Reg loc (T j)) (Arealaw.Reg loc (T j)) ℂ,
      (∀ j, IsFilter 0 (a j) (M j)) → ‖toEuclideanLin (filterProd hTU M m) ξ‖ ≤ B) :
    ∑ j ∈ Finset.range m, (⟪ξ, toEuclideanLin (Arealaw.extendId (hTU j)
      (W j * diagonal (fun x ↦ (Real.log (l j x) : ℂ)) * (W j)ᴴ)) ξ⟫_ℂ).re ≤ Real.log B := by
  set G := ∑ j ∈ Finset.range m, Arealaw.extendId (hTU j)
    (W j * diagonal (fun x ↦ (Real.log (l j x) : ℂ)) * (W j)ᴴ)
  set Λξ : Matrix (Arealaw.Reg loc U) (Arealaw.Reg loc U) ℂ →L[ℂ]
      EuclideanSpace ℂ (Arealaw.Reg loc U) :=
    LinearMap.toContinuousLinearMap ((LinearMap.applyₗ ξ).comp toEuclideanLin.toLinearMap)
  -- D3.12.5: `F(x) = M^x ξ` has `F(0) = ξ`, `F'(0) = (∑ log M_j) ξ`
  have hF : HasDerivAt (fun x : ℝ ↦ toEuclideanLin (filterProd hTU
      (fun j ↦ specPow (W j) (l j) x) m) ξ) (toEuclideanLin G ξ) 0 := by
    have h := Λξ.hasFDerivAt.comp_hasDerivAt (0 : ℂ)
      (hasDerivAt_filterProd_specPow_zero hTU hW l m)
    have h' : HasDerivAt (⇑Λξ ∘ fun z ↦ filterProd hTU (fun j ↦ specPow (W j) (l j) z) m)
        (Λξ G) (Complex.ofRealCLM 0) := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_zero] using h
    have h2 := (h'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ)
      Complex.ofRealCLM.hasDerivAt
    exact h2.congr_deriv (by simp [Λξ])
  have hF0 : toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j) ((0 : ℝ) : ℂ)) m) ξ =
      ξ := by
    rw [Complex.ofReal_zero, filterProd_specPow_zero hTU hW l m, toLpLin_one, LinearMap.id_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ ‖toEuclideanLin (filterProd hTU
      (fun j ↦ specPow (W j) (l j) x) m) ξ‖ ^ 2) (2 * (⟪ξ, toEuclideanLin G ξ⟫_ℂ).re) 0 := by
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hF.inner ℂ hF)
    refine (hre.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    · simp only [Complex.reCLM_apply, hF0, Complex.add_re]
      rw [← inner_conj_symm (toEuclideanLin G ξ) ξ, Complex.conj_re]
      ring
    · simp only [Function.comp_apply, Complex.reCLM_apply]
      rw [← RCLike.re_to_complex, ← @norm_sq_eq_re_inner ℂ]
  -- D3.12.5: `‖F(x)‖² ≤ B^{2x}`, equality at `x = 0`
  have he : HasDerivAt (fun x : ℝ ↦ Real.exp (2 * x * Real.log B)) (2 * Real.log B) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.log B)).exp
    simp only [id, mul_zero, Real.exp_zero, one_mul, mul_one] at this
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ by ring_nf)
  have hd := (hg.sub he).tendsto_slope_zero_right
  have hle : (2 * (⟪ξ, toEuclideanLin G ξ⟫_ℂ).re - 2 * Real.log B) ≤ 0 := by
    refine le_of_tendsto hd ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have h3 := norm_filterProd_specPow_le_rpow hTU hT hW hl hM m hξ hB hx.1.le hx.2.le
    have h4 : ‖toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j) (x : ℂ)) m) ξ‖ ^ 2 ≤
        Real.exp (2 * x * Real.log B) := by
      calc _ ≤ (B ^ x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = _ := by rw [Real.rpow_def_of_pos hB0, ← Real.exp_nat_mul]; ring_nf
    have h5 : ‖toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j)
        ((0 + x : ℝ) : ℂ)) m) ξ‖ ^ 2 - Real.exp (2 * (0 + x) * Real.log B) ≤
        ‖toEuclideanLin (filterProd hTU (fun j ↦ specPow (W j) (l j) ((0 : ℝ) : ℂ)) m) ξ‖ ^ 2 -
          Real.exp (2 * 0 * Real.log B) := by
      rw [hF0, hξ, zero_add]; simp only [mul_zero, zero_mul, Real.exp_zero, one_pow]; linarith
    simp only [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hx.1.le)
      (by simp only [Pi.sub_apply]; linarith)
  have hsum : (⟪ξ, toEuclideanLin G ξ⟫_ℂ).re = ∑ j ∈ Finset.range m,
      (⟪ξ, toEuclideanLin (Arealaw.extendId (hTU j)
        (W j * diagonal (fun x ↦ (Real.log (l j x) : ℂ)) * (W j)ᴴ)) ξ⟫_ℂ).re := by
    simp only [G, map_sum, LinearMap.sum_apply, inner_sum, Complex.re_sum]
  linarith

end D3123

end AreaLaw
