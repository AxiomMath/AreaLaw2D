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
      simpa using (hM j).conj (W := (V j)ᴴ) (by rw [conjTranspose_conjTranspose]; exact hV j)
  refine (l2_opNorm_mulVec (Arealaw.extendId (hTU m) (V m)) _).trans ?_
  exact (mul_le_of_le_one_left (norm_nonneg _) ((l2_opNorm_extendId_le _ _).trans
    (l2_opNorm_le_one_of_mul_conjTranspose (hV m)))).trans hK

end D3123

end AreaLaw
