/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Geometry.DyadicLayers

/-!
# Exhaustion by translated dyadic neighborhoods

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/DyadicExhaustion.lean` (Apache 2.0).
-/

namespace OpenAI.Geometry

/-- Enlarged occupied-cell neighborhoods exhaust the plane when the endpoint
set is nonempty and the index radius is at least two. -/
theorem exists_mem_dyadicNeighborhood (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C) (x : ℝ × ℝ) :
    ∃ k : ℕ, x ∈ dyadicNeighborhood o k Z C := by
  obtain ⟨z, hz⟩ := hZ
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    (|x.1 - o.1| + |x.2 - o.2| + |(z.1 : ℝ) - o.1| + |(z.2 : ℝ) - o.2|)
    (by norm_num : (1 : ℝ) < 2)
  have hp : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
  have floor_bounds (a : ℝ) (ha : |a| < (2 : ℝ) ^ k) :
      -1 ≤ ⌊a / (2 : ℝ) ^ k⌋ ∧ ⌊a / (2 : ℝ) ^ k⌋ ≤ 0 := by
    obtain ⟨ha₀, ha₁⟩ := abs_lt.mp ha
    have hlo : (-1 : ℝ) ≤ a / (2 : ℝ) ^ k :=
      (le_div_iff₀ hp).mpr (by linarith)
    have hhi : a / (2 : ℝ) ^ k < (1 : ℝ) :=
      (div_lt_iff₀ hp).mpr (by linarith)
    refine ⟨Int.le_floor.mpr (by simpa using hlo), ?_⟩
    have hf : ⌊a / (2 : ℝ) ^ k⌋ < (1 : ℤ) :=
      Int.floor_lt.mpr (by simpa using hhi)
    omega
  have hb : |x.1 - o.1| < (2 : ℝ) ^ k ∧ |x.2 - o.2| < (2 : ℝ) ^ k ∧
      |(z.1 : ℝ) - o.1| < (2 : ℝ) ^ k ∧ |(z.2 : ℝ) - o.2| < (2 : ℝ) ^ k := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [abs_nonneg (x.1 - o.1), abs_nonneg (x.2 - o.2),
      abs_nonneg ((z.1 : ℝ) - o.1), abs_nonneg ((z.2 : ℝ) - o.2)]
  have hx₁ := floor_bounds (x.1 - o.1) hb.1
  have hx₂ := floor_bounds (x.2 - o.2) hb.2.1
  have hz₁ := floor_bounds ((z.1 : ℝ) - o.1) hb.2.2.1
  have hz₂ := floor_bounds ((z.2 : ℝ) - o.2) hb.2.2.2
  refine ⟨k, ?_⟩
  rw [mem_dyadicNeighborhood_iff, OpenAI.mem_ambientDilation]
  refine ⟨dyadicCellIndex o k ((z.1 : ℝ), (z.2 : ℝ)), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  · simp only [dyadicCellIndex]
    constructor <;> rw [abs_le] <;> omega

/-- The union of all enlarged occupied-cell neighborhoods is the plane. -/
theorem iUnion_dyadicNeighborhood_eq_univ (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C) :
    (⋃ k : ℕ, dyadicNeighborhood o k Z C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr (exists_mem_dyadicNeighborhood o Z C hZ hC x)

end OpenAI.Geometry
