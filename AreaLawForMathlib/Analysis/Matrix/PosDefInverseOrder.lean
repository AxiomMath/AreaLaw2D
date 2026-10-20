/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Analysis/SuperoperatorResolvent.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0),
inverse-antitonicity portion.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Inverse antitonicity for positive-definite matrices -/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix.PosDef

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `A ≤ B` are positive definite, then `B⁻¹ ≤ A⁻¹`. -/
lemma inv_le_inv_of_le {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hle : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hsub : (B - A).PosSemidef := Matrix.le_iff.mp hle
  have hAinv : A⁻¹.PosDef := hA.inv
  let : Invertible A := hA.isUnit.invertible
  let : Invertible A⁻¹ := hAinv.isUnit.invertible
  let : Invertible B := hB.isUnit.invertible
  have hinvinv : (A⁻¹)⁻¹ = A := Matrix.inv_inv_of_invertible A
  have hBlock : (Matrix.fromBlocks A⁻¹ 1 1 B).PosSemidef := by
    have h11 := Matrix.PosDef.fromBlocks₁₁
      (B := (1 : Matrix n n ℂ)) (D := B) hAinv
    rw [show (1 : Matrix n n ℂ)ᴴ = 1 from Matrix.conjTranspose_one] at h11
    refine h11.2 ?_
    have hcomp : B - (1 : Matrix n n ℂ) * (A⁻¹)⁻¹ * 1 = B - A := by
      rw [hinvinv, Matrix.one_mul, Matrix.mul_one]
    rw [hcomp]
    exact hsub
  have hSchur := Matrix.PosDef.fromBlocks₂₂
    (A := A⁻¹) (B := (1 : Matrix n n ℂ)) hB
  rw [show (1 : Matrix n n ℂ)ᴴ = 1 from Matrix.conjTranspose_one] at hSchur
  have hfinal : (A⁻¹ - B⁻¹).PosSemidef := by
    have h := hSchur.1 hBlock
    rwa [Matrix.one_mul, Matrix.mul_one] at h
  exact Matrix.le_iff.mpr hfinal

end Matrix.PosDef
