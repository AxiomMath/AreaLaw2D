import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.BigOperators.Field

/-!
# Second moment and Chebyshev bound for iid words

Extends `Mathlib/Probability/Moments/Variance.lean`.

For a probability vector `p` on a finite type `n` and `X : n → ℝ` with mean `μ = ∑ p_i X_i`, the
words `x : Fin k → n` weighted by `∏_j p_{x_j}` are `k` independent samples. The centred sum
`∑_j (X_{x_j} - μ)` has second moment `k Var(X)`, and the Chebyshev bound
`∑_{|∑_j X_{x_j} - kμ| ≥ t} ∏_j p_{x_j} ≤ k Var(X) / t²` follows. These are the finite-sum forms
of `ProbabilityTheory.variance_sum_pi` and `ProbabilityTheory.meas_ge_le_variance_div_sq`.
-/

namespace Finset

variable {n : Type*} [Fintype n]

/-- The weights `∏_j p_{x_j}` of words of length `k` sum to `1`. -/
theorem sum_prod_iid_eq_one {p : n → ℝ} (hp : ∑ i, p i = 1) (k : ℕ) :
    ∑ x : Fin k → n, ∏ j, p (x j) = 1 := by
  rw [← Fintype.prod_sum (fun _ : Fin k => p)]
  simp [hp]

/-- **Second moment of an iid sum**: `E (∑_j (X_{x_j} - μ))² = k Var(X)`. -/
theorem sum_prod_iid_mul_sum_sub_sq {p : n → ℝ} (hp : ∑ i, p i = 1) (X : n → ℝ) (k : ℕ) :
    ∑ x : Fin k → n, (∏ j, p (x j)) * (∑ j, (X (x j) - ∑ i, p i * X i)) ^ 2 =
      k * ∑ i, p i * (X i - ∑ i', p i' * X i') ^ 2 := by
  set μ := ∑ i, p i * X i
  have hZ : ∑ i, p i * (X i - μ) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, μ, sub_self]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => n).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    have h1 : ∀ a : n, ∑ y : Fin k → n, p a * (∏ j, p (y j)) *
        (X a - μ + ∑ j, (X (y j) - μ)) ^ 2 =
        p a * (X a - μ) ^ 2 * ∑ y : Fin k → n, ∏ j, p (y j) +
          2 * (p a * (X a - μ)) * ∑ y : Fin k → n, (∏ j, p (y j)) * ∑ j, (X (y j) - μ) +
          p a * ∑ y : Fin k → n, (∏ j, p (y j)) * (∑ j, (X (y j) - μ)) ^ 2 := by
      intro a
      have e : ∀ y : Fin k → n, p a * (∏ j, p (y j)) * (X a - μ + ∑ j, (X (y j) - μ)) ^ 2 =
          p a * (X a - μ) ^ 2 * ∏ j, p (y j) +
            2 * (p a * (X a - μ)) * ((∏ j, p (y j)) * ∑ j, (X (y j) - μ)) +
            p a * ((∏ j, p (y j)) * (∑ j, (X (y j) - μ)) ^ 2) := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [h1, Finset.sum_add_distrib, ← Finset.sum_mul, sum_prod_iid_eq_one hp, ih, hZ,
      ← Finset.mul_sum, hp]
    push_cast
    ring

/-- **Chebyshev bound for iid words**:
`∑_{|∑_j X_{x_j} - kμ| ≥ t} ∏_j p_{x_j} ≤ k Var(X) / t²`. -/
theorem sum_prod_iid_indicator_le {p : n → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (X : n → ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ x : Fin k → n, (∏ j, p (x j)) *
        (if t ≤ |∑ j, X (x j) - k * ∑ i, p i * X i| then 1 else 0) ≤
      k * (∑ i, p i * (X i - ∑ i', p i' * X i') ^ 2) / t ^ 2 := by
  rw [← sum_prod_iid_mul_sum_sub_sq hp X k, Finset.sum_div]
  refine Finset.sum_le_sum fun x _ => ?_
  have hP : 0 ≤ ∏ j, p (x j) := Finset.prod_nonneg fun j _ => hp0 _
  have hc : ∑ j, (X (x j) - ∑ i, p i * X i) = ∑ j, X (x j) - k * ∑ i, p i * X i := by
    simp [Finset.sum_sub_distrib]
  rw [hc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hP
  split_ifs with h
  · rw [le_div_iff₀ (by positivity), one_mul, ← sq_abs (∑ j, X (x j) - _)]
    exact pow_le_pow_left₀ ht.le h 2
  · positivity

end Finset
