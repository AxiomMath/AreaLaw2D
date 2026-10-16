/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.ModEq

/-!
# Sparse selection of coordinate residue classes

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/SparseBelts.lean` (Apache 2.0), for [OAI265,
§11, `geometry:belt-count`].
-/

namespace OpenAI.Geometry

/-- Two coordinate residue classes select at most `2 / m` of a finite cell
set.  The integer formulation avoids division and includes empty sets and
`m = 1`. -/
theorem exists_sparse_belt_shift (F : Finset (ℤ × ℤ)) (m : ℕ) (hm : 0 < m) :
    ∃ a b : Fin m,
      m * (F.filter fun z ↦
        z.1 % (m : ℤ) = (a.val : ℤ) ∨ z.2 % (m : ℤ) = (b.val : ℤ)).card ≤
          2 * F.card := by
  have small_fiber (f : ℤ × ℤ → Fin m) :
      ∃ a, m * (F.filter fun z ↦ f z = a).card ≤ F.card := by
    obtain ⟨a, _, ha⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul
      (s := F) (t := Finset.univ) (f := f)
      (by simpa using Nat.lt_mul_div_succ F.card hm)
    exact ⟨a, (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ ha)).trans (Nat.mul_div_le _ _)⟩
  let residue (x : ℤ) : Fin m :=
    ⟨(x % (m : ℤ)).toNat,
      (Int.toNat_lt (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hm.ne'))).mpr
        (Int.emod_lt_of_pos _ (Int.natCast_pos.mpr hm))⟩
  have residue_val (x : ℤ) : ((residue x).val : ℤ) = x % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hm.ne'))
  obtain ⟨a, ha⟩ := small_fiber (fun z ↦ residue z.1)
  obtain ⟨b, hb⟩ := small_fiber (fun z ↦ residue z.2)
  simp only [Fin.ext_iff, ← Int.natCast_inj, residue_val] at ha hb
  refine ⟨a, b, ?_⟩
  rw [Finset.filter_or]
  exact (Nat.mul_le_mul_left m (Finset.card_union_le _ _)).trans
    (by simpa only [Nat.mul_add, two_mul] using Nat.add_le_add ha hb)

end OpenAI.Geometry
