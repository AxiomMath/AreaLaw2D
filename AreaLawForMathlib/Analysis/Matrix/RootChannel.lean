/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported and adapted from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3, `QICLean/Analysis/RootChannel.lean`,
as used by LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576.
Apache 2.0; adapted to this repository's operator-norm and square-root API.
-/
import AreaLawForMathlib.Analysis.CStarAlgebra.Matrix
import AreaLawForMathlib.Analysis.Matrix.SqrtHolder
import Mathlib.Analysis.Matrix.Order

/-!
# Square-root channels of positive contractions

Extends `Mathlib/Analysis/Matrix/Order.lean`.

For `0 ≤ k ≤ 1`, the roots `G = √(1-k)` and `K = √k` define the channel
`B ↦ G B G + K B K`.  This file proves positivity and contraction after adjoining an
arbitrary finite reference, dimension-free perturbation bounds, and the fixed-point and
ground-vector identities used in Lemma 4.4 of OAI265.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

open Arealaw

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Kraus contractions -/

/-! ### The root channel -/

/-- The square-root channel `B ↦ G B G + K B K`. -/
def rootChannel (G K B : Matrix n n ℂ) : Matrix n n ℂ :=
  G * B * G + K * B * K

omit [DecidableEq n] in
theorem rootChannel_nonneg {G K B : Matrix n n ℂ} (hG : G.IsHermitian) (hK : K.IsHermitian)
    (hB : 0 ≤ B) : 0 ≤ rootChannel G K B := by
  rw [Matrix.nonneg_iff_posSemidef] at hB ⊢
  have h1 := hB.conjTranspose_mul_mul_same G
  have h2 := hB.conjTranspose_mul_mul_same K
  rw [hG.eq] at h1
  rw [hK.eq] at h2
  exact h1.add h2

/-- The elementary perturbation estimate for one Kraus term. -/
theorem norm_mul_mul_sub_mul_mul_le (A A' B : Matrix n n ℂ) :
    ‖A * B * A - A' * B * A'‖ ≤ (‖A‖ + ‖A'‖) * ‖A - A'‖ * ‖B‖ := by
  have hdecomp : A * B * A - A' * B * A' = (A - A') * B * A + A' * B * (A - A') := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hdecomp]
  calc
    ‖(A - A') * B * A + A' * B * (A - A')‖
        ≤ ‖A - A'‖ * ‖B‖ * ‖A‖ + ‖A'‖ * ‖B‖ * ‖A - A'‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          · exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = (‖A‖ + ‖A'‖) * ‖A - A'‖ * ‖B‖ := by ring

theorem norm_rootChannel_sub_le (G K G' K' B : Matrix n n ℂ) :
    ‖rootChannel G K B - rootChannel G' K' B‖ ≤
      ((‖G‖ + ‖G'‖) * ‖G - G'‖ + (‖K‖ + ‖K'‖) * ‖K - K'‖) * ‖B‖ := by
  have h : rootChannel G K B - rootChannel G' K' B =
      (G * B * G - G' * B * G') + (K * B * K - K' * B * K') := by
    simp only [rootChannel]
    abel
  rw [h, add_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_mul_mul_sub_mul_mul_le _ _ _) (norm_mul_mul_sub_mul_mul_le _ _ _))

theorem rootChannel_eq_self_of_commute {G K B : Matrix n n ℂ} (h : G * G + K * K = 1)
    (hG : Commute G B) (hK : Commute K B) : rootChannel G K B = B := by
  rw [rootChannel, hG.eq, hK.eq, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h,
    Matrix.mul_one]

/-! ### Square roots of a positive contraction -/

theorem sqrt_le_one {k : Matrix n n ℂ} (hk₁ : k ≤ 1) : CFC.sqrt k ≤ 1 := by
  simpa using CFC.sqrt_le_sqrt k 1 hk₁

end Matrix
