import OpenAI.ComplementaryWeylTwirl
import OpenAI.CutTransport
import OpenAI.Embedding
import OpenAI.RegionLift

/-!
# The normalized regional conditional expectation

This file develops the algebraic, order, support, and operator-norm API for the existing
`OpenAI.condExpect` of [OAI265, eq. (4.1)].  The norm proof uses the complementary Weyl twirl
ported from LionSR/QICLean at commit `5f76b263` and used by LionSR/TNLean at commit
`fc565830`; both sources are Apache 2.0.  No second conditional-expectation definition is
introduced.
-/

namespace OpenAI

open Arealaw Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker ComplexOrder

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T : Finset σ}

section Algebra

variable {𝕜 : Type*} [RCLike 𝕜]

@[simp] theorem condExpect_zero (h : S ⊆ T) :
    condExpect h (0 : Matrix (Reg loc T) (Reg loc T) 𝕜) = 0 := by
  simp [condExpect]

@[simp] theorem condExpect_add (h : S ⊆ T)
    (A B : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    condExpect h (A + B) = condExpect h A + condExpect h B := by
  simp [condExpect, smul_add]

@[simp] theorem condExpect_smul (h : S ⊆ T) (c : 𝕜)
    (A : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    condExpect h (c • A) = c • condExpect h A := by
  simp [condExpect, smul_comm c]

@[simp] theorem condExpect_sub (h : S ⊆ T)
    (A B : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    condExpect h (A - B) = condExpect h A - condExpect h B := by
  unfold condExpect
  rw [ptrace_sub, extendId_sub, smul_sub]

/-- The normalized regional conditional expectation as a linear map. -/
noncomputable def condExpectₗ (h : S ⊆ T) :
    Matrix (Reg loc T) (Reg loc T) 𝕜 →ₗ[𝕜] Matrix (Reg loc T) (Reg loc T) 𝕜 where
  toFun := condExpect h
  map_add' := condExpect_add h
  map_smul' := condExpect_smul h

@[simp] theorem condExpectₗ_apply (h : S ⊆ T)
    (A : Matrix (Reg loc T) (Reg loc T) 𝕜) : condExpectₗ h A = condExpect h A := rfl

/-- Conditional expectation preserves Hermitian matrices. -/
theorem isHermitian_condExpect (h : S ⊆ T) {A : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hA : A.IsHermitian) : (condExpect h A).IsHermitian := by
  unfold condExpect
  exact (isHermitian_extendId h (isHermitian_ptrace h hA)).smul (by
    rw [isSelfAdjoint_iff]
    simp)

/-- Every conditional expectation is supported on its target region. -/
theorem isSupportedOn_condExpect (h : S ⊆ T) (A : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    IsSupportedOn h (condExpect h A) := by
  refine ⟨(Fintype.card (Reg loc (T \ S)) : 𝕜)⁻¹ • ptrace h A, ?_⟩
  exact (extendId_smul h _ _).symm

/-- Extension by the identity commutes with the C*-algebra absolute value. -/
theorem cfcAbs_extendId (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    CFC.abs (extendId h A) = extendId h (CFC.abs A) := by
  rw [CFC.abs, CFC.abs]
  have hsqrt : 0 ≤ CFC.sqrt (star A * A) := CFC.sqrt_nonneg _
  have hext : 0 ≤ extendId h (CFC.sqrt (star A * A)) :=
    (posSemidef_extendId h hsqrt.posSemidef).nonneg
  refine (CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) hext).mpr ?_
  rw [← extendId_mul,
    CFC.sqrt_mul_sqrt_self (star A * A) (star_mul_self_nonneg A)]
  change extendId h (Aᴴ * A) = (extendId h A)ᴴ * extendId h A
  rw [← extendId_conjTranspose, ← extendId_mul]

/-- Taking the C*-algebra absolute value does not enlarge support. -/
theorem IsSupportedOn.cfcAbs {h : S ⊆ T} {A : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hA : IsSupportedOn h A) : IsSupportedOn h (CFC.abs A) := by
  obtain ⟨A, rfl⟩ := hA
  rw [cfcAbs_extendId]
  exact isSupportedOn_extendId h _

theorem posSemidef_condExpect (h : S ⊆ T) {A : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hA : A.PosSemidef) : (condExpect h A).PosSemidef := by
  have hn : 0 ≤ (Fintype.card (Reg loc (T \ S)) : 𝕜)⁻¹ := by positivity
  exact (posSemidef_extendId h (posSemidef_ptrace h hA)).smul hn

theorem condExpect_nonneg (h : S ⊆ T) {A : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hA : 0 ≤ A) : 0 ≤ condExpect h A := by
  rw [Matrix.le_iff] at hA ⊢
  simpa only [sub_zero] using posSemidef_condExpect h (by simpa only [sub_zero] using hA)

theorem condExpect_mono (h : S ⊆ T) {A B : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hAB : A ≤ B) : condExpect h A ≤ condExpect h B := by
  rw [Matrix.le_iff] at hAB ⊢
  rw [← condExpect_sub]
  exact posSemidef_condExpect h hAB

theorem condExpect_one (h : S ⊆ T) [Nonempty (Reg loc (T \ S))] :
    condExpect h (1 : Matrix (Reg loc T) (Reg loc T) 𝕜) = 1 := by
  simp only [condExpect, ptrace_one, extendId_smul, extendId_one, smul_smul]
  have hn : (Fintype.card (Reg loc (T \ S)) : 𝕜) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hn, one_smul]

theorem condExpect_le_one (h : S ⊆ T) [Nonempty (Reg loc (T \ S))]
    {A : Matrix (Reg loc T) (Reg loc T) 𝕜} (hA : A ≤ 1) : condExpect h A ≤ 1 := by
  rw [← condExpect_one h]
  exact condExpect_mono h hA

theorem condExpect_extendId (h : S ⊆ T) [Nonempty (Reg loc (T \ S))]
    (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    condExpect h (extendId h A) = extendId h A := by
  have hp := ptrace_mul_extendId h (1 : Matrix (Reg loc T) (Reg loc T) 𝕜) A
  simp only [one_mul, ptrace_one, smul_mul, one_mul] at hp
  simp only [condExpect, hp, extendId_smul, smul_smul]
  have hn : (Fintype.card (Reg loc (T \ S)) : 𝕜) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hn, one_smul]

theorem condExpect_of_isSupportedOn (h : S ⊆ T) [Nonempty (Reg loc (T \ S))]
    {A : Matrix (Reg loc T) (Reg loc T) 𝕜} (hA : IsSupportedOn h A) :
    condExpect h A = A := by
  obtain ⟨A, rfl⟩ := hA
  exact condExpect_extendId h A

/-- Conditional expectation fixes the absolute value of its own output. -/
theorem condExpect_cfcAbs_condExpect (h : S ⊆ T) [Nonempty (Reg loc (T \ S))]
    (A : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    condExpect h (CFC.abs (condExpect h A)) = CFC.abs (condExpect h A) :=
  condExpect_of_isSupportedOn h ((isSupportedOn_condExpect h A).cfcAbs)

theorem condExpect_map_toComplex (h : S ⊆ T)
    (A : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    (condExpect h A).map (toComplex 𝕜) = condExpect h (A.map (toComplex 𝕜)) := by
  simp only [condExpect, map_toComplex_smul, extendId_map_toComplex, ptrace_map_toComplex]
  congr 1
  simp

end Algebra

section Norm

variable (h : S ⊆ T)

/-- The canonical identification of a nonempty finite type with the cyclic group of its
cardinality. -/
noncomputable def regZModEquiv (C : Type*) [Fintype C] [Nonempty C] :
    C ≃ ZMod (Fintype.card C) :=
  (Fintype.equivFin C).trans (ZMod.finEquiv (Fintype.card C)).toEquiv

noncomputable def regWeylRoot (C : Type*) [Fintype C] [Nonempty C] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / Fintype.card C)

theorem isPrimitiveRoot_regWeylRoot (C : Type*) [Fintype C] [Nonempty C] :
    IsPrimitiveRoot (regWeylRoot C) (Fintype.card C) := by
  letI : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  exact Complex.isPrimitiveRoot_exp _ (NeZero.ne _)

/-- In product coordinates, `condExpect` is exactly the complementary Weyl twirl. -/
theorem condExpect_submatrix_glueEquiv_eq_complementaryWeylTwirl
    [Nonempty (Reg loc (T \ S))] (A : Matrix (Reg loc T) (Reg loc T) ℂ) :
    (condExpect h A).submatrix (glueEquiv h) (glueEquiv h) =
      Matrix.complementaryWeylTwirl (regZModEquiv (Reg loc (T \ S)))
        (regWeylRoot (Reg loc (T \ S)))
        (A.submatrix (glueEquiv h) (glueEquiv h)) := by
  let C := Reg loc (T \ S)
  let d := Fintype.card C
  letI : NeZero d := ⟨Fintype.card_ne_zero⟩
  have hroot : IsPrimitiveRoot (regWeylRoot C) d := isPrimitiveRoot_regWeylRoot C
  rw [Matrix.complementaryWeylTwirl_eq_smul_traceRight_kronecker_one
    (regZModEquiv C) hroot]
  ext ⟨x, z⟩ ⟨y, w⟩
  simp only [Matrix.submatrix_apply, glueEquiv_apply, condExpect, Matrix.smul_apply,
    extendId_apply_glue, Matrix.kronecker_apply, Matrix.one_apply,
    ptrace_eq_traceRight_submatrix_glueEquiv, smul_eq_mul]
  by_cases hzw : z = w
  · subst w
    simp only [if_pos, mul_one]
    rfl
  · simp [hzw]

/-- The normalized conditional expectation is contractive in L2 operator norm. -/
theorem norm_condExpect_le [Nonempty (Reg loc S)] [Nonempty (Reg loc (T \ S))]
    (A : Matrix (Reg loc T) (Reg loc T) ℂ) : ‖condExpect h A‖ ≤ ‖A‖ := by
  let C := Reg loc (T \ S)
  let d := Fintype.card C
  letI : NeZero d := ⟨Fintype.card_ne_zero⟩
  have hroot : IsPrimitiveRoot (regWeylRoot C) d := isPrimitiveRoot_regWeylRoot C
  rw [← l2_opNorm_submatrix (condExpect h A) (glueEquiv h) (glueEquiv h),
    condExpect_submatrix_glueEquiv_eq_complementaryWeylTwirl h A,
    ← l2_opNorm_submatrix A (glueEquiv h) (glueEquiv h)]
  exact Matrix.norm_complementaryWeylTwirl_le (regZModEquiv C) hroot _

/-- An operator that almost commutes with every contraction supported on the complementary
region is close, with the same error, to its normalized conditional expectation. -/
theorem norm_sub_condExpect_le_of_forall_commutator
    [Nonempty (Reg loc S)] [Nonempty (Reg loc (T \ S))]
    (A : Matrix (Reg loc T) (Reg loc T) ℂ) (ε : ℝ)
    (hcomm : ∀ B : Matrix (Reg loc T) (Reg loc T) ℂ,
      IsSupportedOn (Finset.sdiff_subset : T \ S ⊆ T) B → ‖B‖ ≤ 1 →
        ‖A * B - B * A‖ ≤ ε) :
    ‖A - condExpect h A‖ ≤ ε := by
  let C := Reg loc (T \ S)
  let d := Fintype.card C
  letI : NeZero d := ⟨Fintype.card_ne_zero⟩
  let e := regZModEquiv C
  let ζ := regWeylRoot C
  have hζ : IsPrimitiveRoot ζ d := isPrimitiveRoot_regWeylRoot C
  rw [← l2_opNorm_submatrix (A - condExpect h A) (glueEquiv h) (glueEquiv h)]
  change ‖A.submatrix (glueEquiv h) (glueEquiv h) -
    (condExpect h A).submatrix (glueEquiv h) (glueEquiv h)‖ ≤ ε
  rw [condExpect_submatrix_glueEquiv_eq_complementaryWeylTwirl h A]
  apply Matrix.norm_sub_complementaryWeylTwirl_le e hζ
  intro a b
  let W := Matrix.reindexedWeyl e ζ a b
  let B := extendId (Finset.sdiff_subset : T \ S ⊆ T) W
  have hBnorm : ‖B‖ ≤ 1 := by
    calc
      ‖B‖ ≤ ‖W‖ := l2_opNorm_extendId_le _ _
      _ = 1 := CStarRing.norm_of_mem_unitary
        (Matrix.reindexedWeyl_mem_unitary e hζ a b)
  have hbound : ‖A * B - B * A‖ ≤ ε :=
    hcomm B ⟨W, rfl⟩ hBnorm
  rw [← l2_opNorm_submatrix (A * B - B * A) (glueEquiv h) (glueEquiv h)] at hbound
  change ‖(A * B).submatrix (glueEquiv h) (glueEquiv h) -
    (B * A).submatrix (glueEquiv h) (glueEquiv h)‖ ≤ ε at hbound
  rw [← Matrix.submatrix_mul_equiv A B (glueEquiv h) (glueEquiv h) (glueEquiv h),
    ← Matrix.submatrix_mul_equiv B A (glueEquiv h) (glueEquiv h) (glueEquiv h),
    show B.submatrix (glueEquiv h) (glueEquiv h) =
        (1 : Matrix (Reg loc S) (Reg loc S) ℂ) ⊗ₖ W by
      exact extendId_sdiff_submatrix_glueEquiv h W] at hbound
  exact hbound

end Norm

end OpenAI
