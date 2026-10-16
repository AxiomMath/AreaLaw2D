/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Geometry.DyadicLayers
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.Convex.Basic

/-!
# Closures of dyadic cells and layers

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/DyadicClosure.lean` (Apache 2.0).
-/

namespace OpenAI.Geometry

/-- The closure of a translated half-open dyadic cell is its closed rectangle. -/
theorem closure_dyadicCell (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    closure (dyadicCell o k z) =
      Set.Icc (o.1 + (2 : ℝ) ^ k * z.1) (o.1 + (2 : ℝ) ^ k * (z.1 + 1)) ×ˢ
        Set.Icc (o.2 + (2 : ℝ) ^ k * z.2) (o.2 + (2 : ℝ) ^ k * (z.2 + 1)) := by
  have h (a : ℝ) (i : ℤ) :
      a + (2 : ℝ) ^ k * i ≠ a + (2 : ℝ) ^ k * (i + 1) := by
    have hp : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
    linarith
  rw [dyadicCell, closure_prod_eq, closure_Ico (h _ _), closure_Ico (h _ _)]

/-- The closed rectangle of a dyadic cell is convex. -/
theorem convex_closure_dyadicCell (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    Convex ℝ (closure (dyadicCell o k z)) := by
  rw [closure_dyadicCell]
  exact (convex_Icc _ _).prod (convex_Icc _ _)

/-- The closure of a dyadic layer is the finite union of its cell closures. -/
theorem closure_dyadicLayer_eq_iUnion (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    closure (dyadicLayer o k Z C) =
      ⋃ z ∈ dyadicLayerIndices o k Z C, closure (dyadicCell o k z) := by
  rw [dyadicLayer_eq_iUnion, Finset.closure_biUnion]

end OpenAI.Geometry
