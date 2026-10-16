import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Interval.Finset.Nat

/-!
# Colouring chunk positions modulo `P`

Colour the position `(a, b) ∈ ℕ × ℕ` by `(a mod P) P + (b mod P)`, one of `P²` colours.  Two
positions of the same colour within distance `C < P` along both axes coincide, since equal
residues at distance less than `P` are equal.  Along an axis of `n` positions, at most `2 C + 1`
positions `a` fail `C ≤ a` and `a + C + 2 ≤ n`.  In the proof of Proposition 3.3 of [OAI265]
these are the two counting facts about the children of a safe parent: the padding of an interior
child meets only children of other colours, and all but `O(C M)` of the at most `M²` children are
interior.

## Implementation notes

Ported from TNLean (`LionSR/TNLean`, commit `f4c2d204`, Apache 2.0),
`TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean`, theorems `eq_of_color_eq` and
`card_filter_not_interior_le`; the statements and proofs are unchanged.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.3, proof of Proposition 3.3.
-/

namespace OpenAI

/-- Equal colours `(a mod P) P + (b mod P)` at distance at most `C < P` along both axes force
equal positions. -/
theorem eq_of_color_eq {P a b a' b' C : ℕ} (hCP : C < P)
    (hcol : (a % P) * P + b % P = (a' % P) * P + b' % P)
    (h1 : a' ≤ a + C) (h2 : a ≤ a' + C) (h3 : b' ≤ b + C) (h4 : b ≤ b' + C) :
    a = a' ∧ b = b' := by
  have hP : 0 < P := by omega
  have hb : b % P < P := Nat.mod_lt _ hP
  have hb' : b' % P < P := Nat.mod_lt _ hP
  have hmb : b % P = b' % P := by
    have := congrArg (· % P) hcol
    simpa [Nat.add_mod, Nat.mul_mod_left, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hb'] using this
  have hma : a % P = a' % P := by
    rw [hmb] at hcol
    exact Nat.eq_of_mul_eq_mul_right hP (Nat.add_right_cancel hcol)
  -- equal residues at distance less than `P`
  have key : ∀ {x y : ℕ}, x % P = y % P → x ≤ y + C → y ≤ x + C → x = y :=
    fun hxy hx hy ↦ Nat.ModEq.eq_of_abs_lt hxy (abs_lt.mpr ⟨by omega, by omega⟩)
  exact ⟨key hma h2 h1, key hmb h4 h3⟩

/-- At most `2 C + 1` positions in `[0, n)` violate `C ≤ a ∧ a + C + 2 ≤ n`. -/
theorem card_filter_not_interior_le (n C : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter fun a : Fin n ↦ ¬ (C ≤ a.val ∧ a.val + C + 2 ≤ n)).card
      ≤ 2 * C + 1 := by
  have hsub : ((Finset.univ : Finset (Fin n)).filter
      fun a : Fin n ↦ ¬ (C ≤ a.val ∧ a.val + C + 2 ≤ n)).map Fin.valEmbedding ⊆
      Finset.range C ∪ Finset.Ico (n - (C + 1)) n := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    have := a.isLt
    omega
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_map, Finset.card_range, Nat.card_Ico] at this
  omega

end OpenAI
