import AreaLawForMathlib.Analysis.Matrix.AuxiliaryBlock
import AreaLawForMathlib.Analysis.Matrix.ProjectionCompressionCfc

/-!
# Reductions of similarity transforms and of the skew defect

Extends `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`.

* `Matrix.list_ofFn_prod_rpow_conj`: for pairwise commuting positive definite factors `D_g`,
  `(∏ D)^{-1/2} X (∏ D)^{1/2} = D_g^{-1/2} X D_g^{1/2}` when `X` commutes with every factor
  except `D_g`.
* `Matrix.proj_mul_skewAbs_conj_proj_mul_add_one_sub`: for an orthogonal projection `P`
  commuting with a positive definite `A` and with `X`, the skew defects of the similarity
  transforms of `X` by `P A + (1 - P)` and by `A` agree after multiplication by `P`.
* `Matrix.proj_mul_cfc_sqrt_proj_mul`: `P (P Y)^{1/2} = P Y^{1/2}` for `[P, Y] = 0`.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Conjugating by the square root of `A R` with `R` commuting with `A` and `X` only sees `A`. -/
theorem PosDef.rpow_conj_mul_of_commute {A R X : Matrix m m ℂ} (hA : A.PosDef)
    (hR : R.PosDef) (hAR : Commute A R) (hRX : Commute R X) :
    (A * R) ^ (-(1 / 2) : ℝ) * X * (A * R) ^ (1 / 2 : ℝ) =
      A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ) := by
  rw [hA.mul_rpow_of_commute hR hAR, hA.mul_rpow_of_commute hR hAR]
  have h1 : Commute (R ^ (-(1 / 2) : ℝ)) X := hR.commute_rpow_left hRX _
  have h2 : Commute (R ^ (-(1 / 2) : ℝ)) (A ^ (1 / 2 : ℝ)) :=
    (hA.commute_rpow hR hAR _ _).symm
  calc A ^ (-(1 / 2) : ℝ) * R ^ (-(1 / 2) : ℝ) * X * (A ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ))
      = A ^ (-(1 / 2) : ℝ) * (R ^ (-(1 / 2) : ℝ) * X) * A ^ (1 / 2 : ℝ) *
          R ^ (1 / 2 : ℝ) := by simp only [Matrix.mul_assoc]
    _ = A ^ (-(1 / 2) : ℝ) * X * (R ^ (-(1 / 2) : ℝ) * A ^ (1 / 2 : ℝ)) *
          R ^ (1 / 2 : ℝ) := by rw [h1.eq]; simp only [Matrix.mul_assoc]
    _ = A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ) *
          (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) := by rw [h2.eq]; simp only [Matrix.mul_assoc]
    _ = A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ) := by
          rw [hR.rpow_neg_mul_rpow, Matrix.mul_one]

/-- A product of pairwise commuting positive definite matrices is positive definite. -/
theorem posDef_list_ofFn_prod {K : ℕ} (f : Fin K → Matrix m m ℂ)
    (hf : ∀ g, (f g).PosDef) (hcomm : ∀ g g', g ≠ g' → Commute (f g) (f g')) :
    (List.ofFn f).prod.PosDef := by
  induction K with
  | zero => simpa using Matrix.PosDef.one
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine (hf 0).mul_of_commute (ih _ (fun g => hf _) fun g g' hg => hcomm _ _ ?_) ?_
    · exact fun e => hg (Fin.succ_injective _ e)
    · refine Commute.list_prod_right _ _ fun M hM => ?_
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hM
      exact hcomm _ _ (Fin.succ_ne_zero g).symm

/-- **Single-factor reduction.** For pairwise commuting positive definite factors `f g'`, the
similarity transform by the square root of `∏_{g'} f g'` of a matrix commuting with every
factor except `f g` is the similarity transform by the square root of `f g`. -/
theorem list_ofFn_prod_rpow_conj {K : ℕ} (f : Fin K → Matrix m m ℂ)
    (hf : ∀ g, (f g).PosDef) (hcomm : ∀ g g', g ≠ g' → Commute (f g) (f g')) (g : Fin K)
    {X : Matrix m m ℂ} (hX : ∀ g', g' ≠ g → Commute (f g') X) :
    (List.ofFn f).prod ^ (-(1 / 2) : ℝ) * X * (List.ofFn f).prod ^ (1 / 2 : ℝ) =
      f g ^ (-(1 / 2) : ℝ) * X * f g ^ (1 / 2 : ℝ) := by
  induction K with
  | zero => exact g.elim0
  | succ K ih =>
    have htailPD : (List.ofFn fun g' => f g'.succ).prod.PosDef :=
      posDef_list_ofFn_prod _ (fun _ => hf _) fun a b hab =>
        hcomm _ _ fun e => hab (Fin.succ_injective _ e)
    have hcomm0 : Commute (f 0) (List.ofFn fun g' => f g'.succ).prod :=
      Commute.list_prod_right _ _ fun M hM => by
        obtain ⟨g', rfl⟩ := List.mem_ofFn.mp hM
        exact hcomm _ _ (Fin.succ_ne_zero g').symm
    rw [List.ofFn_succ, List.prod_cons]
    cases g using Fin.cases with
    | zero =>
      refine (hf 0).rpow_conj_mul_of_commute htailPD hcomm0 ?_
      refine Commute.list_prod_left _ _ fun M hM => ?_
      obtain ⟨g', rfl⟩ := List.mem_ofFn.mp hM
      exact hX _ (Fin.succ_ne_zero g')
    | succ g' =>
      rw [hcomm0.eq, htailPD.rpow_conj_mul_of_commute (hf 0) hcomm0.symm
        (hX 0 (Fin.succ_ne_zero g').symm)]
      exact ih _ (fun _ => hf _) (fun a b hab => hcomm _ _ fun e => hab (Fin.succ_injective _ e))
        g' fun a ha => hX _ fun e => ha (Fin.succ_injective _ e)

/-- `P (P Y)^{1/2} = P Y^{1/2}` for a positive semidefinite `Y` commuting with an idempotent
Hermitian `P`. -/
theorem proj_mul_cfc_sqrt_proj_mul {P Y : Matrix m m ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (hY : Y.PosSemidef) (hPY : Commute P Y) :
    P * cfc Real.sqrt (P * Y) = P * CFC.sqrt Y := by
  have hPYh : (P * Y).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, hP.eq, hY.isHermitian.eq, hPY.eq]
  rw [CFC.sqrt_eq_real_sqrt Y hY.nonneg, cfcₙ_eq_cfc (hf0 := by simp)]
  exact mul_cfc_eq_mul_cfc_of_mul_eq hPYh hY.isHermitian hPY (by rw [← Matrix.mul_assoc, hPP]) _

/-- **The skew defect on the range of a projection.** For an orthogonal projection `P`
commuting with a positive definite `A` and with `X`, with `E = P A + (1 - P)`,
`P 𝖣(E^{-1/2} X E^{1/2}) = P 𝖣(A^{-1/2} X A^{1/2})`. -/
theorem proj_mul_skewAbs_conj_proj_mul_add_one_sub {P A X : Matrix m m ℂ} (hA : A.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : Commute P A) (hPX : Commute P X) :
    P * skewAbs ((P * A + (1 - P)) ^ (-(1 / 2) : ℝ) * X * (P * A + (1 - P)) ^ (1 / 2 : ℝ)) =
      P * skewAbs (A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ)) := by
  set E := P * A + (1 - P)
  have hE : E.PosDef := hA.proj_mul_add_one_sub hP hPP hPA
  have hPE : Commute P E := (Commute.refl P).mul_right hPA |>.add_right
    ((Commute.one_right P).sub_right (Commute.refl P))
  have hPr : ∀ r : ℝ, Commute P (A ^ r) := fun r => (hA.commute_rpow_left hPA.symm r).symm
  have hPEr : ∀ r : ℝ, Commute P (E ^ r) := fun r => (hE.commute_rpow_left hPE.symm r).symm
  have hext : ∀ r : ℝ, P * E ^ r = P * A ^ r := fun r => by
    rw [hA.rpow_proj_mul_add_one_sub hP hPP hPA, Matrix.mul_add, ← Matrix.mul_assoc, hPP,
      Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, add_zero]
  set O := A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ)
  set Oc := E ^ (-(1 / 2) : ℝ) * X * E ^ (1 / 2 : ℝ)
  have hPO : Commute P O := ((hPr _).mul_right hPX).mul_right (hPr _)
  have hPOc : Commute P Oc := ((hPEr _).mul_right hPX).mul_right (hPEr _)
  have hPstar : ∀ {M : Matrix m m ℂ}, Commute P M → Commute P Mᴴ := fun {M} h => by
    have := congrArg conjTranspose h.eq
    rw [conjTranspose_mul, conjTranspose_mul, hP.eq] at this
    exact this.symm
  have e1 : P * Oc = P * O := by
    calc P * Oc = P * E ^ (-(1 / 2) : ℝ) * X * E ^ (1 / 2 : ℝ) := by
          simp only [Oc, Matrix.mul_assoc]
      _ = A ^ (-(1 / 2) : ℝ) * (P * X) * E ^ (1 / 2 : ℝ) := by
          rw [hext, (hPr _).eq]; simp only [Matrix.mul_assoc]
      _ = A ^ (-(1 / 2) : ℝ) * X * (P * E ^ (1 / 2 : ℝ)) := by
          rw [hPX.eq]; simp only [Matrix.mul_assoc]
      _ = O * P := by rw [hext, (hPr _).eq]; simp only [O, Matrix.mul_assoc]
      _ = P * O := hPO.eq.symm
  have e2 : P * Ocᴴ = P * Oᴴ := by
    have := congrArg conjTranspose e1
    rw [conjTranspose_mul P Oc, conjTranspose_mul P O, hP.eq] at this
    rw [(hPstar hPOc).eq, (hPstar hPO).eq, this]
  have e3 : P * (Oc * Ocᴴ) = P * (O * Oᴴ) := by
    calc P * (Oc * Ocᴴ) = O * (P * Ocᴴ) := by
          rw [← Matrix.mul_assoc, e1, hPO.eq, Matrix.mul_assoc]
      _ = P * (O * Oᴴ) := by rw [e2, ← Matrix.mul_assoc, ← hPO.eq, Matrix.mul_assoc]
  have e4 : P * (Ocᴴ * Oc) = P * (Oᴴ * O) := by
    calc P * (Ocᴴ * Oc) = Oᴴ * (P * Oc) := by
          rw [← Matrix.mul_assoc, e2, (hPstar hPO).eq, Matrix.mul_assoc]
      _ = P * (Oᴴ * O) := by
          rw [e1, ← Matrix.mul_assoc, ← (hPstar hPO).eq, Matrix.mul_assoc]
  have hsq : ∀ {Y Z : Matrix m m ℂ}, Y.PosSemidef → Z.PosSemidef → Commute P Z →
      P * Y = P * Z → P * CFC.sqrt Y = P * CFC.sqrt Z := fun {Y Z} hY hZ hPZ h => by
    rw [CFC.sqrt_eq_real_sqrt Y hY.nonneg, CFC.sqrt_eq_real_sqrt Z hZ.nonneg,
      cfcₙ_eq_cfc, cfcₙ_eq_cfc]
    exact mul_cfc_eq_mul_cfc_of_mul_eq hY.isHermitian hZ.isHermitian hPZ h _
  have s1 := hsq (posSemidef_self_mul_conjTranspose Oc) (posSemidef_self_mul_conjTranspose O)
    (hPO.mul_right (hPstar hPO)) e3
  have s2 := hsq (posSemidef_conjTranspose_mul_self Oc) (posSemidef_conjTranspose_mul_self O)
    ((hPstar hPO).mul_right hPO) e4
  simp only [skewAbs]
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, s1, s2, e1, e2, ← Matrix.mul_add,
    ← Matrix.mul_sub, ← Matrix.mul_sub]

end Matrix
