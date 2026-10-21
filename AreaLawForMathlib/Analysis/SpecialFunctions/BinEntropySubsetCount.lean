import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset

/-!
# Counting small subsets by the binary entropy

Extends `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`.

For `0 < τ ≤ 1/2` and a finite type of cardinality `k`, the subsets of size at most `τ k` number
at most `e^{k h(τ)}`, `h` the binary entropy; in particular `binom(k, r) ≤ e^{k h(τ)}` for
`r ≤ τ k`. Proof: `τ^{|B|} (1-τ)^{k-|B|} ≥ e^{-k h(τ)}` for `|B| ≤ τ k`, and these weights sum
to `(τ + (1 - τ))^k = 1`.
-/

open Real Finset

/-- For `0 < τ ≤ 1/2` and `r ≤ τ k`: `e^{-k h(τ)} ≤ τ^r (1 - τ)^{k - r}`. -/
theorem exp_neg_mul_binEntropy_le_pow_mul_pow {τ : ℝ} (h0 : 0 < τ) (h1 : τ ≤ 1 / 2)
    {k r : ℕ} (hr : r ≤ k) (hrτ : (r : ℝ) ≤ τ * k) :
    exp (-(k * binEntropy τ)) ≤ τ ^ r * (1 - τ) ^ (k - r) := by
  have h1' : 0 < 1 - τ := by linarith
  have hlog : log τ ≤ log (1 - τ) := log_le_log h0 (by linarith)
  have hpow : τ ^ r * (1 - τ) ^ (k - r) = exp (r * log τ + ((k : ℝ) - r) * log (1 - τ)) := by
    rw [exp_add, ← Nat.cast_sub hr, ← rpow_natCast, ← rpow_natCast, rpow_def_of_pos h0,
      rpow_def_of_pos h1', mul_comm (log τ), mul_comm (log (1 - τ))]
  rw [hpow, exp_le_exp, binEntropy, log_inv, log_inv]
  nlinarith [mul_le_mul_of_nonneg_right hrτ (sub_nonneg.mpr hlog)]

/-- For `0 < τ ≤ 1/2`: `#{B ⊆ α : |B| ≤ τ |α|} ≤ e^{|α| h(τ)}`. -/
theorem card_filter_card_le_le_exp_binEntropy {α : Type*} [Fintype α]
    {τ : ℝ} (h0 : 0 < τ) (h1 : τ ≤ 1 / 2) :
    ((univ.filter fun B : Finset α => (B.card : ℝ) ≤ τ * Fintype.card α).card : ℝ) ≤
      exp (Fintype.card α * binEntropy τ) := by
  classical
  set k := Fintype.card α
  set S := univ.filter fun B : Finset α => (B.card : ℝ) ≤ τ * k
  have hsum : ∑ B : Finset α, τ ^ B.card * (1 - τ) ^ (k - B.card) = 1 := by
    have := Finset.sum_pow_mul_eq_add_pow τ (1 - τ) (univ : Finset α)
    rw [powerset_univ, card_univ, add_sub_cancel, one_pow] at this
    exact this
  have hle : (S.card : ℝ) * exp (-(k * binEntropy τ)) ≤ 1 := by
    calc (S.card : ℝ) * exp (-(k * binEntropy τ)) = ∑ B ∈ S, exp (-(k * binEntropy τ)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ B ∈ S, τ ^ B.card * (1 - τ) ^ (k - B.card) :=
          sum_le_sum fun B hB => exp_neg_mul_binEntropy_le_pow_mul_pow h0 h1
            (card_le_univ B) (mem_filter.mp hB).2
      _ ≤ ∑ B : Finset α, τ ^ B.card * (1 - τ) ^ (k - B.card) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun B _ _ => by
            have : 0 ≤ 1 - τ := by linarith
            positivity
      _ = 1 := hsum
  rw [exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)] at hle
  exact hle

/-- For `0 < τ ≤ 1/2` and `r ≤ τ |α|`: `binom(|α|, r) ≤ e^{|α| h(τ)}`. -/
theorem choose_le_exp_binEntropy {α : Type*} [Fintype α] {τ : ℝ} (h0 : 0 < τ)
    (h1 : τ ≤ 1 / 2) {r : ℕ} (hr : (r : ℝ) ≤ τ * Fintype.card α) :
    ((Fintype.card α).choose r : ℝ) ≤ exp (Fintype.card α * binEntropy τ) := by
  classical
  refine le_trans ?_ (card_filter_card_le_le_exp_binEntropy (α := α) h0 h1)
  rw [← card_univ, ← card_powersetCard]
  exact_mod_cast card_le_card fun B hB => by
    rw [mem_powersetCard] at hB
    rw [mem_filter, hB.2]
    exact ⟨mem_univ _, hr⟩
