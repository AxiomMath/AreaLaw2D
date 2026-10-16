import Arealaw.TraceDist
import QuantumInfo.ForMathlib.Matrix

/-!
# Fidelity

`F(A, B) = tr √(√B A √B) = ‖√A √B‖₁` on positive semidefinite matrices, unsquared as in
Brandão–Horodecki (arXiv:1206.2947, Appendix A), and Powers–Størmer:
`tr A + tr B - 2F(A, B) ≤ ‖A - B‖₁`.

## Main definitions

* `fidelity`: `‖√A √B‖₁`.

## Main statements

* `fidelity_eq_re_trace_sqrt`: the paper's spelling `tr √(√B A √B)`.
* `trace_add_trace_sub_two_mul_fidelity_le_traceNorm_sub`: Renner05 Lemma A.2.6, via
  Powers–Størmer rather than Renner's POVM argument.
* `traceNorm_conjTranspose`, `traceNorm_fromBlocks_zero`, `norm_trace_le_traceNorm`: the trace
  norm under adjoints, block sums and the trace.

## Implementation notes

The trace-norm section is here, not in `Arealaw.TraceNorm`, because `norm_trace_le_traceNorm`
runs through `re_trace_mul_effect_le` in `Arealaw.TraceDist`.

Physlib's trace-norm facts go through the SVD and are `ℂ`-only; the routes here go through
`charpoly` and are `RCLike`-generic.  `re_trace_mul_nonneg` is different: its upstream is
generic, only the `Matrix`-level spelling is missing.

`trace_fromBlocks` and `posSemidef_fromBlocks_zero` are Mathlib-level facts Mathlib lacks,
stated at the weakest typeclass their proofs need.  Positive semidefiniteness is a `Finite`
notion; only the dot product in the proof wants a `Fintype`.
-/
namespace Arealaw

open Matrix
open scoped ComplexOrder MatrixOrder HermitianMat

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]

/-! ## The functional calculus square root -/

open scoped Classical in
@[simp] theorem conjTranspose_cfcSqrt (A : Matrix ι ι 𝕜) : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
  (CFC.sqrt_nonneg A).posSemidef.isHermitian

section Spectrum

variable [DecidableEq ι]

theorem cfcSqrt_eq_cfc_real_sqrt {A : Matrix ι ι 𝕜} (hA : 0 ≤ A) :
    CFC.sqrt A = cfc Real.sqrt A :=
  (CFC.sqrt_eq_real_sqrt A hA).trans (cfcₙ_eq_cfc (by fun_prop) (by simp))

/-- The square root of a nonnegative real diagonal matrix is taken entrywise. -/
theorem cfcSqrt_diagonal {d : ι → ℝ} (hd : 0 ≤ d) :
    CFC.sqrt (diagonal (RCLike.ofReal ∘ d) : Matrix ι ι 𝕜) =
      diagonal (RCLike.ofReal ∘ (Real.sqrt ∘ d)) :=
  (cfcSqrt_eq_cfc_real_sqrt (posSemidef_diagonal_iff.mpr fun i =>
    RCLike.ofReal_nonneg.mpr (hd i)).nonneg).trans (cfc_diagonal d Real.sqrt)

/-- `Re tr f(A) = ∑ᵢ f(λᵢ)` for Hermitian `A` with eigenvalues `λᵢ`. -/
theorem re_trace_cfc {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    RCLike.re (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  simp [hA.cfc_eq, Matrix.IsHermitian.cfc, Matrix.trace_mul_cycle]

theorem re_trace_cfcSqrt {P : Matrix ι ι 𝕜} (hP : P.PosSemidef) :
    RCLike.re (CFC.sqrt P).trace = ∑ i, Real.sqrt (hP.isHermitian.eigenvalues i) := by
  rw [cfcSqrt_eq_cfc_real_sqrt hP.nonneg, re_trace_cfc hP.isHermitian]

end Spectrum

open scoped Classical in
theorem conjTranspose_cfcSqrt_mul_mul_cfcSqrt_mul {κ : Type*} {P : Matrix ι ι 𝕜}
    (hP : P.PosSemidef) (Y : Matrix ι κ 𝕜) :
    (CFC.sqrt P * Y)ᴴ * (CFC.sqrt P * Y) = Yᴴ * P * Y := by
  rw [Matrix.conjTranspose_mul, conjTranspose_cfcSqrt, Matrix.mul_assoc,
    ← Matrix.mul_assoc (CFC.sqrt P), CFC.sqrt_mul_sqrt_self P hP.nonneg, ← Matrix.mul_assoc]

/-! ## The trace norm under adjoints, blocks and the trace -/

-- `XᴴX` and `XXᴴ` share a characteristic polynomial, hence a spectrum.
private theorem traceNorm_conjTranspose_square (X : Matrix ι ι 𝕜) : Xᴴ.traceNorm = X.traceNorm := by
  classical
  rw [Matrix.traceNorm, Matrix.traceNorm, Matrix.conjTranspose_conjTranspose,
    re_trace_cfcSqrt (Matrix.posSemidef_self_mul_conjTranspose X),
    re_trace_cfcSqrt (Matrix.posSemidef_conjTranspose_mul_self X),
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr (Matrix.charpoly_mul_comm X Xᴴ)]

/-- `‖Xᴴ‖₁ = ‖X‖₁`, rectangular `X` included.  Physlib's `Matrix.traceNorm_conjTranspose` is
square and `ℂ`-only. -/
theorem traceNorm_conjTranspose {κ : Type*} [Fintype κ] (X : Matrix ι κ 𝕜) :
    Xᴴ.traceNorm = X.traceNorm := by
  classical
  have hl := Matrix.submatrix_one_id_right_isometry (R := 𝕜) (d := ι ⊕ κ) Sum.inl_injective
  have hr := Matrix.submatrix_one_id_right_isometry (R := 𝕜) (d := ι ⊕ κ) Sum.inr_injective
  rw [← Matrix.traceNorm_isometry_left hr, ← Matrix.traceNorm_isometry_right hl,
    ← Matrix.traceNorm_isometry_left hl, ← Matrix.traceNorm_isometry_right hr,
    ← traceNorm_conjTranspose_square]
  simp [Matrix.mul_assoc]

section Blocks

variable {κ : Type*} [Fintype κ]

theorem trace_fromBlocks {R : Type*} [AddCommMonoid R] (A : Matrix ι ι R) (B : Matrix ι κ R)
    (C : Matrix κ ι R) (D : Matrix κ κ R) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := Fintype.sum_sum_type _

omit [Fintype ι] [Fintype κ] in
/-- A block-diagonal sum of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_fromBlocks_zero {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    [AddLeftMono R] [Finite ι] [Finite κ] {A : Matrix ι ι R} {D : Matrix κ κ R}
    (hA : A.PosSemidef) (hD : D.PosSemidef) : (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  have _ := Fintype.ofFinite ι
  have _ := Fintype.ofFinite κ
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA hD ⊢
  refine ⟨hA.1.fromBlocks Matrix.conjTranspose_zero hD.1, fun x => ?_⟩
  simpa [fromBlocks_mulVec, dotProduct] using add_nonneg (hA.2 (x ∘ .inl)) (hD.2 (x ∘ .inr))

open scoped Classical in
/-- The square root of a block-diagonal positive semidefinite matrix is blockwise. -/
theorem cfcSqrt_fromBlocks_zero {A : Matrix ι ι 𝕜} {D : Matrix κ κ 𝕜} (hA : A.PosSemidef)
    (hD : D.PosSemidef) : CFC.sqrt (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt D) := by
  refine (CFC.sqrt_eq_iff _ _ (posSemidef_fromBlocks_zero hA hD).nonneg
    (posSemidef_fromBlocks_zero (CFC.sqrt_nonneg A).posSemidef
      (CFC.sqrt_nonneg D).posSemidef).nonneg).mpr ?_
  simp [Matrix.fromBlocks_multiply, CFC.sqrt_mul_sqrt_self, hA.nonneg, hD.nonneg]

/-- The trace norm is additive over block-diagonal sums. -/
theorem traceNorm_fromBlocks_zero (A : Matrix ι ι 𝕜) (D : Matrix κ κ 𝕜) :
    (Matrix.fromBlocks A 0 0 D).traceNorm = A.traceNorm + D.traceNorm := by
  simp only [Matrix.traceNorm, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [cfcSqrt_fromBlocks_zero (Matrix.posSemidef_conjTranspose_mul_self A)
    (Matrix.posSemidef_conjTranspose_mul_self D), trace_fromBlocks, map_add]

end Blocks

-- A Gram matrix; the dilation uses `B = ±1`.
private theorem posSemidef_fromBlocks_one [DecidableEq ι] (B : Matrix ι ι 𝕜) :
    (Matrix.fromBlocks (1 : Matrix ι ι 𝕜) B Bᴴ (Bᴴ * B)).PosSemidef := by
  simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] using
    (Matrix.fromBlocks 1 B (0 : Matrix ι ι 𝕜) 0).posSemidef_conjTranspose_mul_self

/-- The Hermitian dilation `[[0, Z], [Zᴴ, 0]]` has trace norm `2‖Z‖₁`. -/
theorem traceNorm_fromBlocks_zero_diag (Z : Matrix ι ι 𝕜) :
    (Matrix.fromBlocks 0 Z Zᴴ 0).traceNorm = 2 * Z.traceNorm := by
  rw [Matrix.traceNorm, show (Matrix.fromBlocks 0 Z Zᴴ 0)ᴴ * Matrix.fromBlocks 0 Z Zᴴ 0 =
      (Matrix.fromBlocks Zᴴ 0 0 Z)ᴴ * Matrix.fromBlocks Zᴴ 0 0 Z by
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply],
    ← Matrix.traceNorm, traceNorm_fromBlocks_zero, traceNorm_conjTranspose, two_mul]

/-- `re tr Z ≤ ‖Z‖₁`.  Physlib's `Matrix.abs_trace_le_traceNorm` is `ℂ`-only. -/
theorem re_trace_le_traceNorm (Z : Matrix ι ι 𝕜) : RCLike.re Z.trace ≤ Z.traceNorm := by
  classical
  let W : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝕜 := Matrix.fromBlocks 0 Z Zᴴ 0
  let M : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝕜 := (2⁻¹ : ℝ) • Matrix.fromBlocks 1 1 1 1
  have hherm : W.IsHermitian := Matrix.isHermitian_zero.fromBlocks rfl Matrix.isHermitian_zero
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr <|
    .smul (by simpa using posSemidef_fromBlocks_one (1 : Matrix ι ι 𝕜)) (by norm_num)
  have hM1 : M ≤ 1 := by
    rw [Matrix.le_iff]
    convert (posSemidef_fromBlocks_one (-1 : Matrix ι ι 𝕜)).smul (a := (2⁻¹ : ℝ)) (by norm_num)
      using 1
    rw [← Matrix.fromBlocks_one]
    ext (i | i) (j | j) <;> simp [M, Matrix.one_apply] <;> split_ifs <;> module
  have hMW : RCLike.re (M * W).trace = RCLike.re Z.trace := by
    simp [M, W, Matrix.fromBlocks_multiply, trace_fromBlocks, Matrix.trace_conjTranspose,
      RCLike.smul_re, RCLike.conj_re, inv_mul_eq_div, add_halves]
  have htr : RCLike.re W.trace = 0 := by simp [W, trace_fromBlocks]
  linarith [re_trace_mul_effect_le hherm hM0 hM1, traceNorm_fromBlocks_zero_diag Z]

/-- `|tr Z| ≤ ‖Z‖₁`.  Physlib's `Matrix.abs_trace_le_traceNorm` is `ℂ`-only. -/
theorem norm_trace_le_traceNorm (Z : Matrix ι ι 𝕜) : ‖Z.trace‖ ≤ Z.traceNorm := by
  obtain ⟨c, hc, hct⟩ := RCLike.exists_norm_eq_mul_self Z.trace
  simpa [Matrix.traceNorm_smul, hc, ← hct] using re_trace_le_traceNorm (c • Z)

/-! ## Fidelity -/

section Fidelity

variable [DecidableEq ι]

/-- **Fidelity** `F(A, B) = ‖√A √B‖₁`, unsquared as in BH12; Tomamichel15 squares it. -/
noncomputable def fidelity (A B : Matrix ι ι 𝕜) : ℝ :=
  (CFC.sqrt A * CFC.sqrt B).traceNorm

theorem fidelity_def (A B : Matrix ι ι 𝕜) :
    fidelity A B = (CFC.sqrt A * CFC.sqrt B).traceNorm := rfl

theorem fidelity_nonneg (A B : Matrix ι ι 𝕜) : 0 ≤ fidelity A B := Matrix.traceNorm_nonneg _

/-- Fidelity is symmetric.  Not `@[simp]`: it loops. -/
theorem fidelity_comm (A B : Matrix ι ι 𝕜) : fidelity A B = fidelity B A := by
  simpa [fidelity_def] using traceNorm_conjTranspose (CFC.sqrt B * CFC.sqrt A)

/-- BH12's spelling.  `B` needs no positivity: both sides carry the same `CFC.sqrt B`. -/
theorem fidelity_eq_re_trace_sqrt {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) (B : Matrix ι ι 𝕜) :
    fidelity A B = RCLike.re (CFC.sqrt (CFC.sqrt B * A * CFC.sqrt B)).trace := by
  rw [fidelity_def, Matrix.traceNorm, Matrix.conjTranspose_mul, conjTranspose_cfcSqrt,
    conjTranspose_cfcSqrt, ← mul_assoc, mul_assoc (CFC.sqrt B),
    CFC.sqrt_mul_sqrt_self A hA.nonneg]

/-- The fidelity of a positive semidefinite matrix with itself is its trace. -/
theorem fidelity_self {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    fidelity A A = RCLike.re A.trace := by
  simp [fidelity_def, CFC.sqrt_mul_sqrt_self A hA.nonneg, ← hA.traceNorm_eq_trace]

end Fidelity

/-! ## Powers–Størmer -/

/-- The trace of a product of positive semidefinite matrices has nonnegative real part. -/
theorem re_trace_mul_nonneg {P S : Matrix ι ι 𝕜} (hP : P.PosSemidef) (hS : S.PosSemidef) :
    0 ≤ RCLike.re (P * S).trace :=
  HermitianMat.inner_eq_re_trace (A := ⟨P, hP.isHermitian⟩) (B := ⟨S, hS.isHermitian⟩) ▸
    HermitianMat.inner_ge_zero (HermitianMat.zero_le_iff.mpr hP) (HermitianMat.zero_le_iff.mpr hS)

private theorem projLT_zero_mul_self [DecidableEq ι] (X : HermitianMat ι 𝕜) :
    ({0 <ₚ X} : HermitianMat ι 𝕜).mat * X.mat = (X⁺).mat := by
  rw [HermitianMat.posPart_eq_cfc_lt, HermitianMat.projLT_zero_cfc]
  simpa using (X.mat_cfc_mul_apply (fun x => if 0 < x then 1 else 0) id).symm

private theorem self_mul_projLT_zero [DecidableEq ι] (X : HermitianMat ι 𝕜) :
    X.mat * ({0 <ₚ X} : HermitianMat ι 𝕜).mat = (X⁺).mat := by
  simpa using congrArg Matrix.conjTranspose (projLT_zero_mul_self X)

open scoped Classical in
-- `2(A - B) = XY + YX` for `X = √A - √B`, `Y = √A + √B`.
private theorem trace_mul_sub_eq_trace_mul_add {A B C Z : Matrix ι ι 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (h1 : C * (CFC.sqrt A - CFC.sqrt B) = Z)
    (h2 : (CFC.sqrt A - CFC.sqrt B) * C = Z) :
    (C * (A - B)).trace = (Z * (CFC.sqrt A + CFC.sqrt B)).trace := by
  set sa := CFC.sqrt A
  set sb := CFC.sqrt B
  have hI3 : (A - B) + (A - B) = (sa - sb) * (sa + sb) + (sa + sb) * (sa - sb) := by
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self A hA.nonneg, ← CFC.sqrt_mul_sqrt_self B hB.nonneg]
    noncomm_ring
  have h := congrArg (fun M => (C * M).trace) hI3
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, ← Matrix.mul_assoc, h1,
    ← Matrix.mul_assoc, Matrix.trace_mul_cycle, h2] at h
  linear_combination h / 2

open scoped Classical in
/-- **Powers–Størmer**: `‖√A - √B‖₂² ≤ ‖A - B‖₁`. -/
theorem re_trace_sq_sqrt_sub_le_traceNorm_sub {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    RCLike.re ((CFC.sqrt A - CFC.sqrt B) * (CFC.sqrt A - CFC.sqrt B)).trace
      ≤ (A - B).traceNorm := by
  set sa := CFC.sqrt A
  set sb := CFC.sqrt B
  set X : HermitianMat ι 𝕜 := ⟨sa, (CFC.sqrt_nonneg A).posSemidef.isHermitian⟩ -
    ⟨sb, (CFC.sqrt_nonneg B).posSemidef.isHermitian⟩
  set xp := (X⁺).mat
  set xm := (X⁻).mat
  set p := ({0 <ₚ X} : HermitianMat ι 𝕜).mat
  have hI1 : xp - xm = sa - sb := congrArg HermitianMat.mat (HermitianMat.posPart_add_negPart X)
  have ha2pos : 0 ≤ RCLike.re (xp * sb).trace := re_trace_mul_nonneg
    (HermitianMat.zero_le_iff.mp (HermitianMat.posPart_nonneg X)) (CFC.sqrt_nonneg B).posSemidef
  have ha3pos : 0 ≤ RCLike.re (xm * sa).trace := re_trace_mul_nonneg
    (HermitianMat.zero_le_iff.mp (HermitianMat.negPart_nonneg X)) (CFC.sqrt_nonneg A).posSemidef
  have hP1 : ({0 <ₚ X} : HermitianMat ι 𝕜) ≤ 1 :=
    HermitianMat.one_sub_projLT 0 X ▸ sub_le_self 1 (HermitianMat.projLE_nonneg X 0)
  have hkey : RCLike.re (p * (A - B)).trace ≤
      ((A - B).traceNorm + RCLike.re (A - B).trace) / 2 :=
    re_trace_mul_effect_le (hA.isHermitian.sub hB.isHermitian) (HermitianMat.projLT_nonneg 0 X)
      hP1
  grind [trace_mul_sub_eq_trace_mul_add hA hB (projLT_zero_mul_self X) (self_mul_projLT_zero X),
    CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg,
    Matrix.trace_mul_comm sa sb, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.trace_sub, Matrix.trace_add]

open scoped Classical in
private theorem re_trace_sq_sqrt_sub {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re ((CFC.sqrt A - CFC.sqrt B) * (CFC.sqrt A - CFC.sqrt B)).trace =
      RCLike.re A.trace + RCLike.re B.trace - 2 * RCLike.re (CFC.sqrt A * CFC.sqrt B).trace := by
  grind [Matrix.sub_mul, Matrix.mul_sub, CFC.sqrt_mul_sqrt_self A hA.nonneg,
    CFC.sqrt_mul_sqrt_self B hB.nonneg, Matrix.trace_sub, Matrix.trace_mul_comm]

/-- **Fuchs–van de Graaf**, lower bound (Renner05 Lemma A.2.6): `1 - F ≤ ½‖A - B‖₁` on
normalized states. -/
theorem trace_add_trace_sub_two_mul_fidelity_le_traceNorm_sub [DecidableEq ι] {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.trace + RCLike.re B.trace - 2 * fidelity A B ≤ (A - B).traceNorm := by
  have h : RCLike.re (CFC.sqrt A * CFC.sqrt B).trace ≤ fidelity A B := re_trace_le_traceNorm _
  linarith [re_trace_sq_sqrt_sub_le_traceNorm_sub hA hB, re_trace_sq_sqrt_sub hA hB]

end Arealaw
