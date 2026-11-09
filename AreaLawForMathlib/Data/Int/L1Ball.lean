import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Cardinality of `ℓ¹`-balls in `ℤ^d`, and the lattice graph `ℤ^d`

Extends `Mathlib/Data/Int/Interval.lean`: the nearest-neighbour graph `SimpleGraph.l1Lattice d`
on `Fin d → ℤ`, the count `Int.l1BallCard d r` of an `ℓ¹`-ball of radius `r` in `ℤ^d`
(`Int.l1BallCard 2 r = 1 + 2r(r+1)`), and the bounds `Finset.card_le_l1BallCard` (`ℤ^d`) and
`Finset.card_le_of_forall_natAbs_add_natAbs_le` (`ℤ × ℤ`).
-/

namespace Int

/-- The number of points of `ℤ^d` in a closed `ℓ¹`-ball of radius `r`, by slicing along the first
coordinate: `l1BallCard 0 r = 1` and
`l1BallCard (d + 1) r = l1BallCard d r + 2 ∑_{s < r} l1BallCard d s`. -/
def l1BallCard : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d + 1, r => l1BallCard d r + 2 * ∑ s ∈ Finset.range r, l1BallCard d s

theorem l1BallCard_two (r : ℕ) : l1BallCard 2 r = 1 + 2 * r * (r + 1) := by
  have h1 (s : ℕ) : l1BallCard 1 s = 1 + 2 * s := by simp [l1BallCard]
  have h : ∀ r, ∑ s ∈ Finset.range r, (1 + 2 * s) = r * r := by
    intro r; induction r with
    | zero => simp
    | succ r ih => rw [Finset.sum_range_succ, ih]; ring
  change l1BallCard 1 r + 2 * ∑ s ∈ Finset.range r, l1BallCard 1 s = _
  simp only [h1, h]
  ring

end Int

namespace SimpleGraph

/-- The nearest-neighbour graph of `ℤ^d`: `x ~ y` iff `∑ i |x i - y i| = 1`. -/
def l1Lattice (d : ℕ) : SimpleGraph (Fin d → ℤ) where
  Adj x y := ∑ i, (x i - y i).natAbs = 1
  symm := ⟨fun x y (h : ∑ i, (x i - y i).natAbs = 1) => by
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by omega⟩
  loopless := ⟨fun x (h : ∑ i, (x i - x i).natAbs = 1) => by simp at h⟩

end SimpleGraph

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

/-- A finite set of `ℤ^d` within `ℓ¹`-distance `r` of a point has at most `l1BallCard d r`
points: slice along the first coordinate and induct on `d`. -/
theorem card_le_l1BallCard {d : ℕ} {s : Finset (Fin d → ℤ)} (x : Fin d → ℤ) (r : ℕ)
    (hs : ∀ y ∈ s, ∑ i, (y i - x i).natAbs ≤ r) : #s ≤ Int.l1BallCard d r := by
  induction d generalizing r with
  | zero =>
    exact card_le_one.2 fun a _ b _ => funext fun i : Fin 0 => i.elim0
  | succ d ih =>
    -- the slice `y 0 = c` injects into the ball of radius `r - |c - x 0|` of `ℤ^d`
    have hslice (c : ℤ) :
        #(s.filter fun y => y 0 = c) ≤ Int.l1BallCard d (r - (c - x 0).natAbs) := by
      rw [← card_image_of_injOn (f := Fin.tail) fun y hy z hz h => by
        rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail z, h,
          (mem_filter.1 hy).2, (mem_filter.1 hz).2]]
      refine ih (Fin.tail x) _ fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hz
      have := hs y (mem_filter.1 hy).1
      rw [Fin.sum_univ_succ, (mem_filter.1 hy).2] at this
      simp only [Fin.tail]
      omega
    have hfib : #s = ∑ k ∈ range (r + 1), #(s.filter fun y => (y 0 - x 0).natAbs = k) :=
      card_eq_sum_card_fiberwise fun y hy => by
        have := hs y hy
        rw [Fin.sum_univ_succ] at this
        exact mem_range.2 (by omega)
    have hk (k : ℕ) :
        #(s.filter fun y => (y 0 - x 0).natAbs = k) ≤ 2 * Int.l1BallCard d (r - k) := by
      calc #(s.filter fun y => (y 0 - x 0).natAbs = k)
          ≤ #((s.filter fun y => y 0 = x 0 + k) ∪ (s.filter fun y => y 0 = x 0 - k)) :=
            card_le_card fun y hy => by
              simp only [mem_filter, mem_union] at hy ⊢
              exact (Int.natAbs_eq (y 0 - x 0)).imp (fun h => ⟨hy.1, by omega⟩)
                fun h => ⟨hy.1, by omega⟩
        _ ≤ Int.l1BallCard d (r - k) + Int.l1BallCard d (r - k) :=
            (card_union_le _ _).trans (add_le_add
              ((hslice _).trans_eq (by congr 2; omega)) ((hslice _).trans_eq (by congr 2; omega)))
        _ = 2 * Int.l1BallCard d (r - k) := by ring
    have h0 : #(s.filter fun y => (y 0 - x 0).natAbs = 0) ≤ Int.l1BallCard d r := by
      refine (card_le_card fun y hy => ?_).trans ((hslice (x 0)).trans_eq (by simp))
      simp only [mem_filter] at hy ⊢
      exact ⟨hy.1, by omega⟩
    rw [hfib, sum_range_succ', Int.l1BallCard, add_comm]
    gcongr
    calc ∑ k ∈ range r, #(s.filter fun y => (y 0 - x 0).natAbs = k + 1)
        ≤ ∑ k ∈ range r, 2 * Int.l1BallCard d (r - 1 - k) :=
          sum_le_sum fun k _ => (hk _).trans_eq (by congr 2; omega)
      _ = 2 * ∑ s ∈ range r, Int.l1BallCard d s := by
          rw [← mul_sum]; congr 1
          exact sum_range_reflect (Int.l1BallCard d) r

end Finset
