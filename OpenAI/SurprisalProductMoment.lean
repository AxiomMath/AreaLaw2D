/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/SurprisalProductMoment.lean` (Apache 2.0).
Namespace `Entropy` renamed to `OpenAI`, following `OpenAI.surprisalMoment`.
-/
import OpenAI.SurprisalMoment
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact surprisal moments of independent copies

The moment of a finite product law is the corresponding power of the
one-copy moment. Zero weights contribute zero before logarithms are
expanded. The identity also holds for zero copies and does not require
normalization of the weights.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 218--238,
`comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace OpenAI

/-- Independent finite copies have multiplicative surprisal moments.
The weights may vanish and need not sum to one. Source:
`07-comparators.tex`, lines 218--238. -/
theorem surprisalMoment_pi {n : Type*} [Fintype n]
    (p : n → ℝ) (k : ℕ) (u : ℝ) :
    surprisalMoment (fun x : Fin k → n ↦ ∏ j, p (x j)) u =
      surprisalMoment p u ^ k := by
  unfold surprisalMoment
  trans ∑ x : Fin k → n, ∏ j, p (x j) * Real.exp (u * -Real.log (p (x j)))
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : ∏ j, p (x j) = 0
    · simp only [Finset.prod_mul_distrib, hx, zero_mul]
    · rw [Real.log_prod (Finset.prod_ne_zero_iff.mp hx),
        ← Finset.sum_neg_distrib, Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
  · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Fintype.prod_sum (fun (_ : Fin k) i ↦ p i * Real.exp (u * -Real.log (p i)))).symm

end OpenAI
