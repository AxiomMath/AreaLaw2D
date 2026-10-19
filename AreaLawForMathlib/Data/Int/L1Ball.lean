import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Cardinality of an `ℓ¹`-ball in `ℤ²`

Extends `Mathlib/Data/Int/Interval.lean`.
-/

namespace Finset

/-- A finite set of `ℤ²` within `ℓ¹`-distance `r` of a point has at most `1 + 2r(r+1)` points.
The `ℓ¹`-ball is covered by two rotated squares of `(r+1)²` and `r²` points. -/
theorem card_le_of_forall_natAbs_add_natAbs_le {s : Finset (ℤ × ℤ)} (x : ℤ × ℤ) (r : ℕ)
    (hs : ∀ y ∈ s, (y.1 - x.1).natAbs + (y.2 - x.2).natAbs ≤ r) :
    #s ≤ 1 + 2 * r * (r + 1) := by
  let P := Icc (0 : ℤ) r ×ˢ Icc (0 : ℤ) r
  let Q := Icc (0 : ℤ) (r - 1) ×ˢ Icc (0 : ℤ) (r - 1)
  let f : ℤ × ℤ → ℤ × ℤ := fun p => (x.1 + p.1 - p.2, x.2 + p.1 + p.2 - r)
  let g : ℤ × ℤ → ℤ × ℤ := fun p => (x.1 + p.1 - p.2, x.2 + p.1 + p.2 - r + 1)
  calc #s ≤ #(P.image f ∪ Q.image g) := card_le_card fun y hy => by
        have h := hs y hy
        simp only [mem_union, mem_image, mem_product, mem_Icc, P, Q, f, g, Prod.ext_iff,
          Prod.exists]
        rcases Int.emod_two_eq_zero_or_one (y.1 - x.1 + (y.2 - x.2) + r) with he | he
        · exact .inl ⟨(y.1 - x.1 + (y.2 - x.2) + r) / 2, (y.2 - x.2 - (y.1 - x.1) + r) / 2,
            by omega⟩
        · exact .inr ⟨(y.1 - x.1 + (y.2 - x.2) + r - 1) / 2,
            (y.2 - x.2 - (y.1 - x.1) + r - 1) / 2, by omega⟩
    _ ≤ #P + #Q := (card_union_le _ _).trans (add_le_add card_image_le card_image_le)
    _ = 1 + 2 * r * (r + 1) := by simp [P, Q]; ring

end Finset
