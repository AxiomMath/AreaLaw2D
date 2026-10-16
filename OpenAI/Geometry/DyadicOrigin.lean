/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# The translated dyadic origin

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/DyadicOrigin.lean` (Apache 2.0), for [OAI265,
§11].  The irrational translation keeps every permitted supporting line away
from integer lattice sites.
-/

noncomputable section

namespace OpenAI.Geometry

/-- The translated origin prescribed in the manuscript. -/
def dyadicOrigin : ℝ × ℝ := (Real.sqrt 2, Real.sqrt 3)

private theorem ne_int_of_between {x : ℝ} (n : ℤ)
    (hl : (n : ℝ) < x) (hu : x < (n : ℝ) + 1) (m : ℤ) : x ≠ (m : ℝ) := by
  intro h
  have hnm : n < m := Int.cast_lt.mp (h ▸ hl)
  have hmn : m < n + 1 := Int.cast_lt.mp (by
    simpa only [Int.cast_add, Int.cast_one] using h ▸ hu)
  exact (not_lt_of_ge (Int.add_one_le_iff.mpr hnm)) hmn

/-- Each coordinate of the origin, their sum, and their difference is
nonintegral. -/
theorem dyadicOrigin_nonintegral (m : ℤ) :
    dyadicOrigin.1 ≠ (m : ℝ) ∧ dyadicOrigin.2 ≠ (m : ℝ) ∧
      dyadicOrigin.1 + dyadicOrigin.2 ≠ (m : ℝ) ∧
      dyadicOrigin.1 - dyadicOrigin.2 ≠ (m : ℝ) := by
  have h₂l : (4 / 3 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h₃l : (5 / 3 : ℝ) < Real.sqrt 3 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h₂u : Real.sqrt 2 < 2 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h₃u : Real.sqrt 3 < 2 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h₂₃ : Real.sqrt 2 < Real.sqrt 3 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨ne_int_of_between 1 ?_ ?_ m, ne_int_of_between 1 ?_ ?_ m,
    ne_int_of_between 3 ?_ ?_ m, ne_int_of_between (-1) ?_ ?_ m⟩ <;>
    norm_num [dyadicOrigin] <;> linarith

/-- No integer lattice point lies on an integer translate of any of the four
permitted supporting lines. -/
theorem dyadicOrigin_supporting_lines_avoid_lattice (z : ℤ × ℤ) (m : ℤ) :
    (z.1 : ℝ) ≠ dyadicOrigin.1 + (m : ℝ) ∧
      (z.2 : ℝ) ≠ dyadicOrigin.2 + (m : ℝ) ∧
      (z.1 : ℝ) + (z.2 : ℝ) ≠ dyadicOrigin.1 + dyadicOrigin.2 + (m : ℝ) ∧
      (z.1 : ℝ) - (z.2 : ℝ) ≠ dyadicOrigin.1 - dyadicOrigin.2 + (m : ℝ) := by
  refine ⟨fun h ↦ (dyadicOrigin_nonintegral (z.1 - m)).1 ?_,
    fun h ↦ (dyadicOrigin_nonintegral (z.2 - m)).2.1 ?_,
    fun h ↦ (dyadicOrigin_nonintegral (z.1 + z.2 - m)).2.2.1 ?_,
    fun h ↦ (dyadicOrigin_nonintegral (z.1 - z.2 - m)).2.2.2 ?_⟩ <;>
    push_cast <;> linarith

end OpenAI.Geometry
