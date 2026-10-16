/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Rectangles
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite counts for ambient neighborhoods and dyadic children

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/CellCounting.lean` (Apache 2.0).  The cut is kept
in this project's ambient-site encoding: `cutEndpoints Λ A`, obtained from the
ordered `edgeBoundary Λ A`.
-/

open scoped BigOperators Pointwise

namespace OpenAI.Geometry

/-- An ambient integer neighborhood has at most one square of side `2r+1`
per point of its defining set. -/
theorem card_ambientDilation_le (T : Finset (ℤ × ℤ)) (r : ℕ) :
    (ambientDilation T r).card ≤ (2 * r + 1) ^ 2 * T.card := by
  unfold ambientDilation
  calc
    (T + Finset.Icc (-(r : ℤ), -(r : ℤ)) ((r : ℤ), (r : ℤ))).card ≤
        T.card * (Finset.Icc (-(r : ℤ), -(r : ℤ)) ((r : ℤ), (r : ℤ))).card :=
      Finset.card_image₂_le _ _ _
    _ = (2 * r + 1) ^ 2 * T.card := by
      rw [OpenAI.card_Icc_eq_mul]
      have h : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
      rw [h]
      ring

/-- The frozen cut endpoint set has at most two sites per crossing edge. -/
theorem card_cutEndpoints_le (Λ A : Finset (ℤ × ℤ)) :
    (cutEndpoints Λ A).card ≤ 2 * (edgeBoundary Λ A).card := by
  unfold cutEndpoints
  exact (Finset.card_union_le _ _).trans (by
    rw [two_mul]
    exact add_le_add Finset.card_image_le Finset.card_image_le)

/-- Integer indices of the four dyadic children of a parent cell. -/
def dyadicChildren (P : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (P ×ˢ (Finset.univ : Finset (Fin 2 × Fin 2))).image
    fun (z, a) ↦ (2 * z.1 + (a.1.val : ℤ), 2 * z.2 + (a.2.val : ℤ))

/-- Distinct dyadic parents have disjoint four-element child families. -/
theorem card_dyadicChildren (P : Finset (ℤ × ℤ)) :
    (dyadicChildren P).card = 4 * P.card := by
  have hinj : Function.Injective
      (fun (za : (ℤ × ℤ) × (Fin 2 × Fin 2)) ↦
        (2 * za.1.1 + (za.2.1.val : ℤ), 2 * za.1.2 + (za.2.2.val : ℤ))) := by
    rintro ⟨z, a⟩ ⟨w, b⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp at h₁ h₂
    have hz : z = w := Prod.ext (by omega) (by omega)
    have ha : a = b := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    exact Prod.ext hz ha
  rw [dyadicChildren, Finset.card_image_of_injective _ hinj, Finset.card_product]
  simp [Nat.mul_comm]

end OpenAI.Geometry
