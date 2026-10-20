import AreaLawForMathlib.Analysis.Matrix.MatrixPowers

/-!
# An auxiliary positive block realising the skew defect `|O^*| + |O| - O - O^*`

For a positive definite `A` and a positive semidefinite `h`, put `T = h^{1/2}` and
`O = A^{-1/2} h A^{1/2}`. For every positive definite `B`, the maps
`Y = B^{1/2} T A^{-1/2}` and `Z = B^{-1/2} T A^{1/2}` satisfy `Y^* Z = O`. We construct a
positive definite `B = auxBlock A h` with `Y^* Y = |O^*|` and `Z^* Z = |O|`
(`|X| = (X^* X)^{1/2}`), hence
`(Y - Z)^*(Y - Z) = |O^*| + |O| - O - O^*`, and `Y = Z = T` when `A` commutes with `h`.

When `A` and `h` do not commute, `B` is the geometric mean `U^{-1} # V` of the regularized
Gram operators `U = T A^{-1} T + P₀`, `V = T A T + P₀`, `P₀` the kernel projection of `h`,
i.e. the positive solution of `B U B = V`.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The skew defect `|O^*| + |O| - O - O^*` with `|X| = (X^* X)^{1/2}`. -/
noncomputable def skewAbs (O : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt (O * Oᴴ) + CFC.sqrt (Oᴴ * O) - O - Oᴴ

/-- The projection onto the kernel of a Hermitian matrix, through the functional calculus. -/
noncomputable def kerProj (h : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) h

/-- `Y = B^{1/2} h^{1/2} A^{-1/2}`. -/
noncomputable def auxY (A B h : Matrix n n ℂ) : Matrix n n ℂ :=
  B ^ (1 / 2 : ℝ) * CFC.sqrt h * A ^ (-(1 / 2) : ℝ)

/-- `Z = B^{-1/2} h^{1/2} A^{1/2}`. -/
noncomputable def auxZ (A B h : Matrix n n ℂ) : Matrix n n ℂ :=
  B ^ (-(1 / 2) : ℝ) * CFC.sqrt h * A ^ (1 / 2 : ℝ)

/-- The auxiliary block: `A` if `A` commutes with `h`, otherwise the positive solution `B` of
`B (T A^{-1} T + P₀) B = T A T + P₀`, `T = h^{1/2}`, `P₀ = kerProj h`. -/
noncomputable def auxBlock (A h : Matrix n n ℂ) : Matrix n n ℂ :=
  open Classical in
  if Commute A h then A else
    let U := CFC.sqrt h * A ^ (-1 : ℝ) * CFC.sqrt h + kerProj h
    let V := CFC.sqrt h * A * CFC.sqrt h + kerProj h
    U ^ (-(1 / 2) : ℝ) * (U ^ (1 / 2 : ℝ) * V * U ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
      U ^ (-(1 / 2) : ℝ)

theorem sub_conjTranspose_mul_sub_eq_skewAbs {Y Z O : Matrix n n ℂ}
    (hYY : Yᴴ * Y = CFC.sqrt (O * Oᴴ)) (hZZ : Zᴴ * Z = CFC.sqrt (Oᴴ * O)) (hYZ : Yᴴ * Z = O) :
    (Y - Z)ᴴ * (Y - Z) = skewAbs O := by
  have hZY : Zᴴ * Y = Oᴴ := by rw [← hYZ, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [skewAbs, conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hYY, hZZ, hYZ,
    hZY]
  abel

theorem posSemidef_skewAbs_of_eq {Y Z O : Matrix n n ℂ} (h : (Y - Z)ᴴ * (Y - Z) = skewAbs O) :
    (skewAbs O).PosSemidef :=
  h ▸ posSemidef_conjTranspose_mul_self _

section KerProj

theorem sqrt_eq_cfc_real {h : Matrix n n ℂ} (hh : h.PosSemidef) :
    CFC.sqrt h = cfc Real.sqrt h := by
  rw [CFC.sqrt_eq_real_sqrt h hh.nonneg, cfcₙ_eq_cfc (hf0 := by simp)]

theorem kerProj_mul_sqrt {h : Matrix n n ℂ} (hh : h.PosSemidef) : kerProj h * CFC.sqrt h = 0 := by
  have hfin := Matrix.finite_real_spectrum (A := h)
  rw [sqrt_eq_cfc_real hh, kerProj, ← cfc_mul _ _ h (hfin.continuousOn _) (hfin.continuousOn _)]
  refine (cfc_congr fun x _ => ?_).trans (cfc_zero ℝ h)
  split_ifs with hx <;> simp [hx]

theorem sqrt_mul_kerProj {h : Matrix n n ℂ} (hh : h.PosSemidef) : CFC.sqrt h * kerProj h = 0 := by
  have hfin := Matrix.finite_real_spectrum (A := h)
  rw [sqrt_eq_cfc_real hh, kerProj, ← cfc_mul _ _ h (hfin.continuousOn _) (hfin.continuousOn _)]
  refine (cfc_congr fun x _ => ?_).trans (cfc_zero ℝ h)
  split_ifs with hx <;> simp [hx]

theorem posSemidef_kerProj (h : Matrix n n ℂ) : (kerProj h).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg fun x _ => by split_ifs <;> norm_num

theorem isUnit_sqrt_add_kerProj {h : Matrix n n ℂ} (hh : h.PosSemidef) :
    IsUnit (CFC.sqrt h + kerProj h) := by
  have hfin := Matrix.finite_real_spectrum (A := h)
  rw [sqrt_eq_cfc_real hh, kerProj,
    ← cfc_add (a := h) _ _ (hfin.continuousOn _) (hfin.continuousOn _),
    isUnit_cfc_iff _ h (hfin.continuousOn _)]
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hh.nonneg hx
  split_ifs with h0
  · simp [h0]
  · have : 0 < Real.sqrt x := Real.sqrt_pos.mpr (lt_of_le_of_ne hx0 (Ne.symm h0))
    simp only [add_zero]; exact this.ne'

/-- The regularized Gram operator `T X T + P₀` is positive definite for positive definite `X`. -/
theorem posDef_sqrt_mul_mul_sqrt_add_kerProj {h X : Matrix n n ℂ} (hh : h.PosSemidef)
    (hX : X.PosDef) : (CFC.sqrt h * X * CFC.sqrt h + kerProj h).PosDef := by
  have hT : (CFC.sqrt h)ᴴ = CFC.sqrt h := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
  have h1 : (CFC.sqrt h * X * CFC.sqrt h).PosSemidef := by
    simpa [hT] using hX.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt h)
  have h2 := posSemidef_kerProj h
  refine (h1.add h2).posDef_iff_isUnit.mpr (mulVec_injective_iff_isUnit.mp fun x y hxy => ?_)
  rw [← sub_eq_zero, ← mulVec_sub] at hxy
  rw [← sub_eq_zero]
  set z := x - y
  have hsum : star z ⬝ᵥ ((CFC.sqrt h * X * CFC.sqrt h) *ᵥ z) + star z ⬝ᵥ (kerProj h *ᵥ z) = 0 := by
    rw [← dotProduct_add, ← add_mulVec, hxy, dotProduct_zero]
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (h1.dotProduct_mulVec_nonneg z)
    (h2.dotProduct_mulVec_nonneg z)).mp hsum
  have hTz : CFC.sqrt h *ᵥ z = 0 := by
    have h0 : star (CFC.sqrt h *ᵥ z) ⬝ᵥ (X *ᵥ (CFC.sqrt h *ᵥ z)) = 0 := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hT, ← ha,
        Matrix.mul_assoc]
    by_contra hne
    exact (hX.dotProduct_mulVec_pos hne).ne' h0
  have hPz := (h2.dotProduct_mulVec_zero_iff z).mp hb
  apply mulVec_injective_iff_isUnit.mpr (isUnit_sqrt_add_kerProj hh)
  rw [add_mulVec, hTz, hPz, add_zero, mulVec_zero]

/-- The kernel projection commutes with the regularized Gram operator. -/
theorem commute_kerProj_sandwich {h : Matrix n n ℂ} (hh : h.PosSemidef) (X : Matrix n n ℂ) :
    Commute (kerProj h) (CFC.sqrt h * X * CFC.sqrt h + kerProj h) := by
  change kerProj h * (_ + _) = (_ + _) * kerProj h
  rw [mul_add, add_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, kerProj_mul_sqrt hh, zero_mul,
    zero_mul, Matrix.mul_assoc, sqrt_mul_kerProj hh, mul_zero]

end KerProj

omit [DecidableEq n] in
/-- The ring identity behind `Y^*Y = |O^*|` and `Z^*Z = |O|`: if
`B (T x x T + Q) B = T y y T + Q` with `Q T = T Q = 0` and `[Q, B] = 0`, then
`(x T B T x)² = (x T T y)(y T T x)`. -/
theorem sandwich_sq_eq {T Q x y B : Matrix n n ℂ} (hQT : Q * T = 0) (hTQ : T * Q = 0)
    (hQB : Q * B = B * Q) (hB : B * (T * (x * x) * T + Q) * B = T * (y * y) * T + Q) :
    (x * T * B * T * x) * (x * T * B * T * x) = (x * (T * T) * y) * (y * (T * T) * x) := by
  have e : B * (T * (x * x) * T) * B = T * (y * y) * T + Q - B * B * Q := by
    have : B * Q * B = B * B * Q := by
      rw [Matrix.mul_assoc, hQB, ← Matrix.mul_assoc]
    rw [← hB, mul_add, add_mul, this]; abel
  calc _ = x * T * (B * (T * (x * x) * T) * B) * T * x := by noncomm_ring
    _ = x * (T * T) * y * (y * (T * T) * x) + x * (T * Q) * T * x -
        x * T * B * B * (Q * T) * x := by rw [e]; noncomm_ring
    _ = _ := by rw [hQT, hTQ]; noncomm_ring

section AuxBlock

variable {A h : Matrix n n ℂ}

theorem conjTranspose_sqrt (h : Matrix n n ℂ) : (CFC.sqrt h)ᴴ = CFC.sqrt h :=
  (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq

/-- `Y^* Z = A^{-1/2} h A^{1/2}` for every positive definite `B`. -/
theorem auxY_conjTranspose_mul_auxZ {B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hh : h.PosSemidef) :
    (auxY A B h)ᴴ * auxZ A B h = A ^ (-(1 / 2) : ℝ) * h * A ^ (1 / 2 : ℝ) := by
  have hTT : CFC.sqrt h * CFC.sqrt h = h := CFC.sqrt_mul_sqrt_self h hh.nonneg
  rw [auxY, auxZ, conjTranspose_mul, conjTranspose_mul, conjTranspose_sqrt,
    (hB.rpow_isHermitian _).eq, (hA.rpow_isHermitian _).eq]
  calc _ = A ^ (-(1 / 2) : ℝ) * CFC.sqrt h * (B ^ (1 / 2 : ℝ) * B ^ (-(1 / 2) : ℝ)) *
        CFC.sqrt h * A ^ (1 / 2 : ℝ) := by noncomm_ring
    _ = _ := by
      rw [hB.rpow_mul_rpow_neg, Matrix.mul_one]; conv_rhs => rw [← hTT]
      noncomm_ring

/-- Commuting case: `auxBlock A h = A`. -/
theorem auxBlock_of_commute (hc : Commute A h) : auxBlock A h = A := by
  simp [auxBlock, hc]

/-- Commuting case: `Y = Z = h^{1/2}` for `B = A`. -/
theorem auxY_self_of_commute (hA : A.PosDef) (hh : h.PosSemidef) (hc : Commute A h) :
    auxY A A h = CFC.sqrt h ∧ auxZ A A h = CFC.sqrt h := by
  have hAT : Commute A (CFC.sqrt h) := by
    rw [sqrt_eq_cfc_real hh]; exact (Commute.cfc_real hc.symm _).symm
  constructor
  · rw [auxY, Matrix.mul_assoc, ← (hA.commute_rpow_left hAT _).eq, ← Matrix.mul_assoc,
      hA.rpow_mul_rpow_neg, Matrix.one_mul]
  · rw [auxZ, Matrix.mul_assoc, ← (hA.commute_rpow_left hAT _).eq, ← Matrix.mul_assoc,
      hA.rpow_neg_mul_rpow, Matrix.one_mul]

omit [DecidableEq n] in
theorem posDef_mul_mul_of_posDef {X Y : Matrix n n ℂ} (hX : X.PosDef) (hY : Y.PosDef) :
    (X * Y * X).PosDef := by
  classical
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Y) hX.isUnit).mpr hY
  rwa [star_eq_conjTranspose, hX.isHermitian.eq] at h

/-- The auxiliary block is positive definite. -/
theorem posDef_auxBlock (hA : A.PosDef) (hh : h.PosSemidef) : (auxBlock A h).PosDef := by
  unfold auxBlock
  split_ifs
  · exact hA
  · have hU := posDef_sqrt_mul_mul_sqrt_add_kerProj hh (hA.rpow (-1))
    have hV := posDef_sqrt_mul_mul_sqrt_add_kerProj hh hA
    exact posDef_mul_mul_of_posDef (hU.rpow _)
      ((posDef_mul_mul_of_posDef (hU.rpow _) hV).rpow _)

/-- `Y^* Y = |O^*|` and `Z^* Z = |O|` for `B = auxBlock A h`, `O = A^{-1/2} h A^{1/2}`. -/
theorem auxBlock_gram (hA : A.PosDef) (hh : h.PosSemidef) :
    let O := A ^ (-(1 / 2) : ℝ) * h * A ^ (1 / 2 : ℝ)
    (auxY A (auxBlock A h) h)ᴴ * auxY A (auxBlock A h) h = CFC.sqrt (O * Oᴴ) ∧
      (auxZ A (auxBlock A h) h)ᴴ * auxZ A (auxBlock A h) h = CFC.sqrt (Oᴴ * O) := by
  intro O
  have hh0 : 0 ≤ h := hh.nonneg
  have hTT : CFC.sqrt h * CFC.sqrt h = h := CFC.sqrt_mul_sqrt_self h hh0
  by_cases hc : Commute A h
  · obtain ⟨hY, hZ⟩ := auxY_self_of_commute hA hh hc
    have hO : O = h := by
      simp only [O]
      rw [Matrix.mul_assoc, ← (hA.commute_rpow_left hc _).eq, ← Matrix.mul_assoc,
        hA.rpow_neg_mul_rpow, Matrix.one_mul]
    rw [auxBlock_of_commute hc, hY, hZ, conjTranspose_sqrt, hTT, hO, hh.isHermitian.eq,
      CFC.sqrt_mul_self h hh0]
    exact ⟨rfl, rfl⟩
  set T := CFC.sqrt h with hTdef
  set Q := kerProj h
  have hT : Tᴴ = T := conjTranspose_sqrt h
  have hQT : Q * T = 0 := kerProj_mul_sqrt hh
  have hTQ : T * Q = 0 := sqrt_mul_kerProj hh
  set a := A ^ (1 / 2 : ℝ)
  set ai := A ^ (-(1 / 2) : ℝ)
  have hai : ai * ai = A ^ (-1 : ℝ) := by simp only [ai]; rw [hA.rpow_mul_rpow]; norm_num
  have haa : a * a = A := hA.rpow_half_mul_rpow_half
  set U := T * A ^ (-1 : ℝ) * T + Q with hUdef
  set V := T * A * T + Q with hVdef
  have hU : U.PosDef := posDef_sqrt_mul_mul_sqrt_add_kerProj hh (hA.rpow (-1))
  have hV : V.PosDef := posDef_sqrt_mul_mul_sqrt_add_kerProj hh hA
  set C := U ^ (1 / 2 : ℝ) * V * U ^ (1 / 2 : ℝ)
  have hC : C.PosDef := posDef_mul_mul_of_posDef (hU.rpow _) hV
  have hBdef : auxBlock A h = U ^ (-(1 / 2) : ℝ) * C ^ (1 / 2 : ℝ) * U ^ (-(1 / 2) : ℝ) := by
    simp only [auxBlock, hc, if_false]; rfl
  set B := auxBlock A h
  have hB : B.PosDef := posDef_auxBlock hA hh
  have hUU : U ^ (-(1 / 2) : ℝ) * U * U ^ (-(1 / 2) : ℝ) = 1 := by
    have : U ^ (-(1 / 2) : ℝ) * U = U ^ (1 / 2 : ℝ) := by
      nth_rw 2 [← hU.rpow_one]; rw [hU.rpow_mul_rpow]; norm_num
    rw [this, hU.rpow_mul_rpow_neg]
  have hBUB : B * U * B = V := by
    rw [hBdef]
    calc U ^ (-(1 / 2) : ℝ) * C ^ (1 / 2 : ℝ) * U ^ (-(1 / 2) : ℝ) * U *
          (U ^ (-(1 / 2) : ℝ) * C ^ (1 / 2 : ℝ) * U ^ (-(1 / 2) : ℝ))
        = U ^ (-(1 / 2) : ℝ) * C ^ (1 / 2 : ℝ) *
          (U ^ (-(1 / 2) : ℝ) * U * U ^ (-(1 / 2) : ℝ)) * C ^ (1 / 2 : ℝ) *
            U ^ (-(1 / 2) : ℝ) := by noncomm_ring
      _ = U ^ (-(1 / 2) : ℝ) * U ^ (1 / 2 : ℝ) * V * (U ^ (1 / 2 : ℝ) *
            U ^ (-(1 / 2) : ℝ)) := by
        rw [hUU, Matrix.mul_one, Matrix.mul_assoc (U ^ (-(1 / 2) : ℝ)) (C ^ (1 / 2 : ℝ))
          (C ^ (1 / 2 : ℝ)), hC.rpow_half_mul_rpow_half]; simp only [C]; noncomm_ring
      _ = V := by rw [hU.rpow_neg_mul_rpow, hU.rpow_mul_rpow_neg, Matrix.one_mul,
        Matrix.mul_one]
  set Bi := B ^ (-1 : ℝ)
  have hBBi : B * Bi = 1 := by
    have := hB.rpow_mul_rpow_neg 1; rwa [hB.rpow_one] at this
  have hBiB : Bi * B = 1 := by
    have := hB.rpow_neg_mul_rpow 1; rwa [hB.rpow_one] at this
  have hBiVBi : Bi * V * Bi = U := by
    rw [← hBUB]
    calc Bi * (B * U * B) * Bi = (Bi * B) * U * (B * Bi) := by noncomm_ring
      _ = U := by rw [hBiB, hBBi, Matrix.one_mul, Matrix.mul_one]
  have hQU : Commute Q U := commute_kerProj_sandwich hh _
  have hQV : Commute Q V := commute_kerProj_sandwich hh _
  have hQUr : ∀ r : ℝ, Commute Q (U ^ r) := fun r => (hU.commute_rpow_left hQU.symm r).symm
  have hQC : Commute Q C := ((hQUr _).mul_right hQV).mul_right (hQUr _)
  have hQB : Commute Q B := by
    rw [hBdef]
    exact ((hQUr _).mul_right (hC.commute_rpow_left hQC.symm _).symm).mul_right (hQUr _)
  have hQBi : Commute Q Bi := (hB.commute_rpow_left hQB.symm _).symm
  have hYY : (auxY A B h)ᴴ * auxY A B h = ai * T * B * T * ai := by
    rw [auxY, conjTranspose_mul, conjTranspose_mul, ← hTdef, hT, (hB.rpow_isHermitian _).eq,
      (hA.rpow_isHermitian _).eq]
    calc _ = ai * T * (B ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) * T * ai := by noncomm_ring
      _ = _ := by rw [hB.rpow_half_mul_rpow_half]
  have hZZ : (auxZ A B h)ᴴ * auxZ A B h = a * T * Bi * T * a := by
    rw [auxZ, conjTranspose_mul, conjTranspose_mul, ← hTdef, hT, (hB.rpow_isHermitian _).eq,
      (hA.rpow_isHermitian _).eq]
    calc _ = a * T * (B ^ (-(1 / 2) : ℝ) * B ^ (-(1 / 2) : ℝ)) * T * a := by noncomm_ring
      _ = _ := by rw [hB.rpow_mul_rpow]; norm_num; rfl
  have hO : O = ai * (T * T) * a := by simp only [O]; rw [hTT]
  have hOH : (ai * (T * T) * a)ᴴ = a * (T * T) * ai := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, hT,
      (hA.rpow_isHermitian _).eq, (hA.rpow_isHermitian _).eq]
    simp only [a, ai, Matrix.mul_assoc]
  have hY0 : 0 ≤ ai * T * B * T * ai := by
    rw [← hYY]; exact Matrix.nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self _)
  have hZ0 : 0 ≤ a * T * Bi * T * a := by
    rw [← hZZ]; exact Matrix.nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self _)
  refine ⟨?_, ?_⟩
  · rw [hYY, hO, eq_comm, CFC.sqrt_eq_iff _ _ (Matrix.nonneg_iff_posSemidef.mpr
      (posSemidef_self_mul_conjTranspose _)) hY0, hOH]
    exact sandwich_sq_eq hQT hTQ hQB.eq (by rw [hai, ← hUdef, haa, ← hVdef, hBUB])
  · rw [hZZ, hO, eq_comm, CFC.sqrt_eq_iff _ _ (Matrix.nonneg_iff_posSemidef.mpr
      (posSemidef_conjTranspose_mul_self _)) hZ0, hOH]
    exact sandwich_sq_eq hQT hTQ hQBi.eq (by rw [haa, ← hVdef, hai, ← hUdef, hBiVBi])

end AuxBlock

end Matrix
