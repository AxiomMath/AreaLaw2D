import AreaLawForMathlib.Analysis.Matrix.MatrixPowers

/-!
# Products of commuting positive definite matrices

Extends `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`.

For pairwise commuting positive definite matrices `X_1, …, X_K` the ordered product is positive
definite and its logarithm is `∑_g log X_g`; whitening a product `∏_g B_g` by a product
`∏_g A_g` factors band by band when `A_g` commutes with `A_{g'}` and `B_{g'}` for `g ≠ g'`.
Also: the inverse square root as a real power, a rank-one Loewner bound from quadratic forms,
and monotonicity of `X ↦ Re Tr(ρ X)` for `ρ ≥ 0`.

## Main declarations

* `Matrix.PosDef.listProd_ofFn` — the ordered product of commuting positive definite matrices.
* `Matrix.cfc_log_listProd_ofFn` — `log ∏_g X_g = ∑_g log X_g`.
* `Matrix.listProd_whiten` — whitening `∏_g B_g` by `∏_g A_g` is `∏_g A_g^{-1/2} B_g A_g^{-1/2}`.
* `Matrix.PosDef.rpow_neg_half_eq_inv_sqrt` — `A^{-1/2} = (√A)⁻¹`.
* `Matrix.smul_vecMulVec_le_of_forall` — `c |z⟩⟨z| ≤ M` from `c |⟨z, w⟩|² ≤ ⟨w, M w⟩`.
* `Matrix.PosSemidef.re_trace_mul_mono` — `X ≤ Y ⇒ Re Tr(ρ X) ≤ Re Tr(ρ Y)` for `ρ ≥ 0`.
* `Matrix.add_le_of_isStarProjection` — lower bounds on the two sides of a commuting projection
  add.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The ordered product of pairwise commuting positive definite matrices is positive definite. -/
theorem PosDef.listProd_ofFn {K : ℕ} {X : Fin K → Matrix m m ℂ} (hX : ∀ g, (X g).PosDef)
    (hXX : ∀ g g', g ≠ g' → Commute (X g) (X g')) : (List.ofFn X).prod.PosDef := by
  induction K with
  | zero => simpa using PosDef.one
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine (hX 0).mul_of_commute (ih (X := fun g ↦ X g.succ) (fun g ↦ hX _)
      (fun g g' h ↦ hXX _ _ (fun h' ↦ h (Fin.succ_injective _ h'))))
      (Commute.list_prod_right _ _ fun y hy ↦ ?_)
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
    exact hXX _ _ (Fin.succ_ne_zero g).symm

/-- The logarithm of an ordered product of pairwise commuting positive definite matrices is the
sum of the logarithms. -/
theorem cfc_log_listProd_ofFn {K : ℕ} {X : Fin K → Matrix m m ℂ} (hX : ∀ g, (X g).PosDef)
    (hXX : ∀ g g', g ≠ g' → Commute (X g) (X g')) :
    CFC.log (List.ofFn X).prod = ∑ g, CFC.log (X g) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      (hX 0).cfc_log_mul (PosDef.listProd_ofFn (fun g => hX _)
        (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h'))))
        (Commute.list_prod_right _ _ fun y hy => by
          obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
          exact hXX _ _ (Fin.succ_ne_zero g).symm),
      ih (fun g => hX _) (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h')))]

/-- Whitening a product of bands by the square root of a product of commuting bands factors band
by band, when the factors of different bands commute. -/
theorem listProd_whiten {K : ℕ} {A B : Fin K → Matrix m m ℂ} (hA : ∀ g, (A g).PosDef)
    (hAA : ∀ g g', g ≠ g' → Commute (A g) (A g'))
    (hAB : ∀ g g', g ≠ g' → Commute (A g) (B g')) :
    (List.ofFn A).prod ^ (-(1 / 2) : ℝ) * (List.ofFn B).prod *
        (List.ofFn A).prod ^ (-(1 / 2) : ℝ) =
      (List.ofFn fun g => A g ^ (-(1 / 2) : ℝ) * B g * A g ^ (-(1 / 2) : ℝ)).prod := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    set PA := (List.ofFn fun g : Fin K => A g.succ).prod
    set PB := (List.ofFn fun g : Fin K => B g.succ).prod
    have hPA : PA.PosDef := PosDef.listProd_ofFn (fun g => hA _)
      (fun g g' h => hAA _ _ (fun h' => h (Fin.succ_injective _ h')))
    have hA0PA : Commute (A 0) PA := Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact hAA _ _ (Fin.succ_ne_zero g).symm
    have hA0PB : Commute (A 0) PB := Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact hAB _ _ (Fin.succ_ne_zero g).symm
    have hPAB0 : Commute PA (B 0) := Commute.list_prod_left _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact hAB _ _ (Fin.succ_ne_zero g)
    rw [(hA 0).mul_rpow_of_commute hPA hA0PA, ← ih (fun g => hA _)
      (fun g g' h => hAA _ _ (fun h' => h (Fin.succ_injective _ h')))
      (fun g g' h => hAB _ _ (fun h' => h (Fin.succ_injective _ h')))]
    set r : ℝ := -(1 / 2)
    have c1 : Commute (PA ^ r) (B 0) := hPA.commute_rpow_left hPAB0 r
    have c2 : Commute PB (A 0 ^ r) := ((hA 0).commute_rpow_left hA0PB r).symm
    have c3 : Commute (PA ^ r) (A 0 ^ r) := hPA.commute_rpow (hA 0) hA0PA.symm r r
    simp only [Matrix.mul_assoc]
    rw [c1.left_comm, c2.left_comm, c3.left_comm]

/-- `A^{-1/2} = (√A)⁻¹` for positive definite `A`. -/
theorem PosDef.rpow_neg_half_eq_inv_sqrt {A : Matrix m m ℂ} (hA : A.PosDef) :
    A ^ (-(1 / 2) : ℝ) = (CFC.sqrt A)⁻¹ := by
  rw [CFC.sqrt_eq_rpow, eq_comm]
  exact Matrix.inv_eq_right_inv (hA.rpow_mul_rpow_neg (1 / 2))

omit [DecidableEq m] in
/-- A rank-one Loewner bound from quadratic forms: if `c |⟨z, w⟩|² ≤ ⟨w, M w⟩` for every `w`
and `M` is Hermitian, then `c |z⟩⟨z| ≤ M`. -/
theorem smul_vecMulVec_le_of_forall {M : Matrix m m ℂ} (hM : M.IsHermitian) {c : ℝ}
    {z : m → ℂ} (h : ∀ w, c * ‖star z ⬝ᵥ w‖ ^ 2 ≤ (star w ⬝ᵥ (M *ᵥ w)).re) :
    c • vecMulVec z (star z) ≤ M := by
  have hP : (c • vecMulVec z (star z)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, star_trivial,
      (posSemidef_vecMulVec_self_star z).isHermitian.eq]
  rw [Matrix.le_iff]
  refine .of_dotProduct_mulVec_nonneg (hM.sub hP) fun w => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, ((hM.sub hP).im_star_dotProduct_mulVec_self w).symm⟩
  have hc : star w ⬝ᵥ z = (starRingEnd ℂ) (star z ⬝ᵥ w) := by
    simp [dotProduct, map_sum, mul_comm]
  have h1 : star w ⬝ᵥ ((c • vecMulVec z (star z)) *ᵥ w) =
      (c : ℂ) * ((‖star z ⬝ᵥ w‖ ^ 2 : ℝ) : ℂ) := by
    rw [smul_mulVec, vecMulVec_mulVec]
    simp only [dotProduct_smul, hc, op_smul_eq_smul]
    change (c : ℂ) * ((star z ⬝ᵥ w) * (starRingEnd ℂ) (star z ⬝ᵥ w)) = _
    rw [Complex.mul_conj']
    push_cast
    rfl
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, h1, ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith [h w]

omit [DecidableEq m] in
/-- `Re Tr(ρ X)` is monotone in `X` for `ρ ≥ 0`. -/
theorem PosSemidef.re_trace_mul_mono {ρ X Y : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hXY : X ≤ Y) :
    (ρ * X).trace.re ≤ (ρ * Y).trace.re := by
  classical
  set B := CFC.sqrt ρ
  have hB : Bᴴ = B := (CFC.sqrt_nonneg ρ).isSelfAdjoint
  have hρB : ρ = Bᴴ * B := by rw [hB, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
  rw [hρB]
  have h := (Matrix.le_iff.mp hXY).mul_mul_conjTranspose_same B
  have e : ∀ Z : Matrix m m ℂ, (Bᴴ * B * Z).trace = (B * Z * Bᴴ).trace := fun Z => by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have h0 := (Complex.nonneg_iff.mp h.trace_nonneg).1
  rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, Complex.sub_re] at h0
  rw [e, e]
  linarith

/-- Lower bounds on the two sides of a commuting orthogonal projection add: if `P` commutes with
`X`, `Y = P Y P ≤ X` and `Z = (1 - P) Z (1 - P) ≤ X`, then `Y + Z ≤ X`. -/
theorem add_le_of_isStarProjection {P X Y Z : Matrix m m ℂ} (hP : IsStarProjection P)
    (hPX : Commute P X) (hY : P * Y * P = Y) (hZ : (1 - P) * Z * (1 - P) = Z) (h1 : Y ≤ X)
    (h2 : Z ≤ X) : Y + Z ≤ X := by
  have hPh : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hQh : (1 - P)ᴴ = 1 - P := hP.one_sub.isSelfAdjoint.star_eq
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hQQ : (1 - P) * (1 - P) = 1 - P := hP.one_sub.isIdempotentElem.eq
  have a1 := (Matrix.le_iff.mp h1).conjTranspose_mul_mul_same P
  have a2 := (Matrix.le_iff.mp h2).conjTranspose_mul_mul_same (1 - P)
  rw [hPh] at a1
  rw [hQh] at a2
  have hX1 : P * X * P = X * P := by rw [hPX.eq, Matrix.mul_assoc, hPP]
  have hQX : Commute (1 - P) X := (Commute.one_left X).sub_left hPX
  have hX2 : (1 - P) * X * (1 - P) = X * (1 - P) := by rw [hQX.eq, Matrix.mul_assoc, hQQ]
  have e : X - (Y + Z) = P * (X - Y) * P + (1 - P) * (X - Z) * (1 - P) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub (1 - P), Matrix.sub_mul, hX1, hX2, hY, hZ,
      Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [Matrix.le_iff, e]
  exact a1.add a2

end Matrix
