import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Log

/-!
# Harmonic weights and power bounds from a scale recurrence

Two scalar estimates behind the initial area-law bound of [OAI265].

For positive costs `c_j`, `j ∈ s`, put `Z = ∑ 1/c_j` and `a_j = 2/(Z c_j)`.  These weights have
total mass two and quadratic cost `∑ c_j a_j² = 4/Z`, the least quadratic cost among all weights
of total mass two (Cauchy–Schwarz).  For the nested contours `c_j = 2r + jD`, `1 ≤ j ≤ m`, with
`D(m+1) ≥ (P-1) r` and `r ≥ 1`, the sum satisfies `Z ≥ (1/D) log ((P+1)/(2+D))`, uniformly in
`r`.

Let `F` be a nondecreasing function on the positive integers, `M ≥ 2` an integer, and `λ > M`.
If `F (M r) ≤ λ F r + K r` for every `r ≥ 1`, with `K ≥ 0`, then iterating at `r = 1, M, M², …`
gives `F (M^j) ≤ C λ^j`, the inhomogeneous terms forming a geometric series of ratio `M/λ < 1`.
Monotonicity then gives `F r ≤ C' r^{log_M λ}` for all `r ≥ 1`, and `log_M λ ∈ (1, 2)` when
`M < λ < M²`.

## Main definitions

* `OpenAI.harmonicWeight`: the weight `a_j = 2/(Z c_j)`.

## Main statements

* `OpenAI.sum_harmonicWeight`, `OpenAI.sum_mul_harmonicWeight_sq`: mass two and cost `4/Z`.
* `OpenAI.harmonic_cost_le`: optimality among weights of total mass two.
* `OpenAI.log_div_le_sum_inv_contour_of_le`: the uniform lower bound for nested contours.
* `OpenAI.exists_le_mul_rpow_of_scale_recurrence`: the power bound for all `r ≥ 1`.
* `OpenAI.one_lt_log_div_log_lt_two`: the exponent lies in `(1, 2)`.

## Implementation notes

Ported from QICLean, `QICLean/Analysis/HarmonicWeights.lean` and
`QICLean/Analysis/ScaleRecurrence.lean` at commit `32a5a1a8` (Apache 2.0), themselves written
from the proofs of Lemma 3.2 (`eq:initial-harmonic-weights`, `eq:initial-harmonic-lower`) and
Proposition 3.3 of [OAI265].  Changes: the two files are merged, and namespace `Entropy` is
replaced by `OpenAI`; the proofs are unchanged.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.2, proof of Lemma 3.2, and §3.3, proof of Proposition 3.3.
-/

open scoped BigOperators

namespace OpenAI

/-! ## Harmonic weights -/

section Harmonic

variable {ι : Type*}

/-- The harmonic weight `a_j = 2/(Z c_j)` with `Z = ∑ 1/c_j`. -/
noncomputable def harmonicWeight (s : Finset ι) (c : ι → ℝ) (j : ι) : ℝ :=
  2 / ((∑ i ∈ s, 1 / c i) * c j)

theorem sum_inv_pos {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty) (hc : ∀ j ∈ s, 0 < c j) :
    0 < ∑ i ∈ s, 1 / c i :=
  Finset.sum_pos (fun i hi ↦ one_div_pos.mpr (hc i hi)) hs

/-- The harmonic weights have total mass two. -/
theorem sum_harmonicWeight {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty)
    (hc : ∀ j ∈ s, 0 < c j) : ∑ j ∈ s, harmonicWeight s c j = 2 := by
  have hZ := sum_inv_pos hs hc
  simp only [harmonicWeight]
  have : ∀ j ∈ s, 2 / ((∑ i ∈ s, 1 / c i) * c j) = 2 / (∑ i ∈ s, 1 / c i) * (1 / c j) :=
    fun j hj ↦ by field_simp
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, div_mul_cancel₀ _ hZ.ne']

/-- The quadratic cost of the harmonic weights is `4/Z`. -/
theorem sum_mul_harmonicWeight_sq {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty)
    (hc : ∀ j ∈ s, 0 < c j) :
    ∑ j ∈ s, c j * harmonicWeight s c j ^ 2 = 4 / ∑ i ∈ s, 1 / c i := by
  have hZ := sum_inv_pos hs hc
  simp only [harmonicWeight]
  have : ∀ j ∈ s, c j * (2 / ((∑ i ∈ s, 1 / c i) * c j)) ^ 2 =
      4 / (∑ i ∈ s, 1 / c i) ^ 2 * (1 / c j) := fun j hj ↦ by
    have := (hc j hj).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  field_simp

/-- **Optimality of the harmonic weights.** Every family of weights of total mass two has
quadratic cost at least `4/Z`. -/
theorem harmonic_cost_le {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty)
    (hc : ∀ j ∈ s, 0 < c j) {b : ι → ℝ} (hb : ∑ j ∈ s, b j = 2) :
    4 / ∑ i ∈ s, 1 / c i ≤ ∑ j ∈ s, c j * b j ^ 2 := by
  have hZ := sum_inv_pos hs hc
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j ↦ Real.sqrt (c j) * b j)
    (fun j ↦ 1 / Real.sqrt (c j))
  have h1 : ∑ j ∈ s, Real.sqrt (c j) * b j * (1 / Real.sqrt (c j)) = 2 := by
    rw [← hb]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have := Real.sqrt_pos.mpr (hc j hj)
    field_simp
  have h2 : ∑ j ∈ s, (Real.sqrt (c j) * b j) ^ 2 = ∑ j ∈ s, c j * b j ^ 2 :=
    Finset.sum_congr rfl fun j hj ↦ by rw [mul_pow, Real.sq_sqrt (hc j hj).le]
  have h3 : ∑ j ∈ s, (1 / Real.sqrt (c j)) ^ 2 = ∑ j ∈ s, 1 / c j :=
    Finset.sum_congr rfl fun j hj ↦ by rw [div_pow, one_pow, Real.sq_sqrt (hc j hj).le]
  rw [h1, h2, h3] at hcs
  rw [div_le_iff₀ hZ]
  linarith

/-- One step of the integral comparison: `log (x + D) - log x ≤ D / x`. -/
theorem log_add_sub_log_le_div {x D : ℝ} (hx : 0 < x) (hD : 0 ≤ D) :
    Real.log (x + D) - Real.log x ≤ D / x := by
  rw [← Real.log_div (by positivity) hx.ne']
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + D) / x by positivity)
  have : (x + D) / x - 1 = D / x := by field_simp; ring
  linarith

/-- **Integral comparison for nested contours.** For `r > 0`, `D > 0` and `m ≥ 0`,
`(1/D) log ((2r + D(m+1)) / (2r + D)) ≤ ∑_{j=1}^m 1/(2r + jD)`. -/
theorem log_div_le_sum_inv_contour {r D : ℝ} (hr : 0 < r) (hD : 0 < D) (m : ℕ) :
    Real.log ((2 * r + D * (m + 1)) / (2 * r + D)) / D ≤
      ∑ j ∈ Finset.Icc 1 m, 1 / (2 * r + j * D) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpos : 0 < 2 * r + ((m + 1 : ℕ) : ℝ) * D := by positivity
    have hstep := log_add_sub_log_le_div hpos hD.le
    have hsplit : Real.log ((2 * r + D * (((m + 1 : ℕ) : ℝ) + 1)) / (2 * r + D)) =
        Real.log ((2 * r + D * ((m : ℝ) + 1)) / (2 * r + D)) +
          (Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D + D) -
            Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D)) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity)
        (by positivity)]
      push_cast
      ring_nf
    rw [hsplit, add_div]
    have h2 : (Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D + D) -
        Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D)) / D ≤ 1 / (2 * r + ((m + 1 : ℕ) : ℝ) * D) := by
      rw [div_le_iff₀ hD]
      calc _ ≤ D / (2 * r + ((m + 1 : ℕ) : ℝ) * D) := hstep
        _ = _ := by field_simp
    linarith

/-- **Uniform lower bound for the harmonic sum.** If `r ≥ 1`, `D > 0` and
`D (m + 1) ≥ (P - 1) r`, then `(1/D) log ((P + 1)/(2 + D)) ≤ ∑_{j=1}^m 1/(2r + jD)`. -/
theorem log_div_le_sum_inv_contour_of_le {r D P : ℝ} (hr : 1 ≤ r) (hD : 0 < D)
    (hP : 1 ≤ P) {m : ℕ} (hm : (P - 1) * r ≤ D * (m + 1)) :
    Real.log ((P + 1) / (2 + D)) / D ≤ ∑ j ∈ Finset.Icc 1 m, 1 / (2 * r + j * D) := by
  refine le_trans ?_ (log_div_le_sum_inv_contour (by linarith) hD m)
  refine div_le_div_of_nonneg_right ?_ hD.le
  refine Real.log_le_log (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (P + 1) * r ≤ 2 * r + D * (m + 1) := by linarith
  have h2 : (P + 1) * (2 * r + D) ≤ (P + 1) * r * (2 + D) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ P + 1) hD.le)
      (by linarith : (0 : ℝ) ≤ r - 1)]
  have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 + D)
  linarith

end Harmonic

/-! ## Scale recurrences -/

section ScaleRecurrence

variable {F : ℕ → ℝ} {M : ℕ} {lam K : ℝ}

/-- **Iteration at powers.** Under the scale recurrence,
`F (M^j) ≤ λ^j F 1 + K (λ^j - M^j)/(λ - M)`. -/
theorem le_pow_of_scale_recurrence (hM : 1 ≤ M) (hlam : (M : ℝ) < lam)
    (hrec : ∀ r, 1 ≤ r → F (M * r) ≤ lam * F r + K * r) (j : ℕ) :
    F (M ^ j) ≤ lam ^ j * F 1 + K / (lam - M) * (lam ^ j - (M : ℝ) ^ j) := by
  have hlM : 0 < lam - M := by linarith
  have hlam0 : 0 < lam := lt_of_le_of_lt (by positivity) hlam
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := hrec (M ^ j) (Nat.one_le_pow _ _ hM)
    rw [show M * M ^ j = M ^ (j + 1) by ring] at h1
    calc F (M ^ (j + 1)) ≤ lam * F (M ^ j) + K * ((M ^ j : ℕ) : ℝ) := h1
      _ ≤ lam * (lam ^ j * F 1 + K / (lam - M) * (lam ^ j - (M : ℝ) ^ j)) +
          K * ((M ^ j : ℕ) : ℝ) := by gcongr
      _ = lam ^ (j + 1) * F 1 + K / (lam - M) * (lam ^ (j + 1) - (M : ℝ) ^ (j + 1)) := by
          push_cast
          field_simp
          ring

/-- **Power bound from a scale recurrence.** If `F` is nondecreasing, `M ≥ 2`, `λ > M`,
`K ≥ 0` and `F (M r) ≤ λ F r + K r` for every `r ≥ 1`, then there is a constant `C` with
`F r ≤ C r^{log λ / log M}` for every `r ≥ 1`. -/
theorem exists_le_mul_rpow_of_scale_recurrence (hF : Monotone F) (hM : 2 ≤ M)
    (hlam : (M : ℝ) < lam) (hK : 0 ≤ K)
    (hrec : ∀ r, 1 ≤ r → F (M * r) ≤ lam * F r + K * r) :
    ∃ C, ∀ r, 1 ≤ r → F r ≤ C * (r : ℝ) ^ (Real.log lam / Real.log M) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hlM : 0 < lam - M := by linarith
  have hlam1 : 1 < lam := hM1.trans hlam
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  set e := Real.log lam / Real.log M
  have he : 0 ≤ e := div_nonneg (Real.log_pos hlam1).le hlogM.le
  set B := |F 1| + K / (lam - M)
  have hB : 0 ≤ B := by positivity
  -- the bound at powers
  have hpow (j : ℕ) : F (M ^ j) ≤ B * lam ^ j := by
    have h := le_pow_of_scale_recurrence (by omega) hlam hrec j
    have hMj : 0 ≤ K / (lam - M) * (M : ℝ) ^ j := by positivity
    have hF1 := le_abs_self (F 1)
    have hlj : 0 ≤ lam ^ j := by positivity
    nlinarith
  -- `λ^j = (M^j)^e`
  have hrpow (j : ℕ) : lam ^ j = ((M : ℝ) ^ j) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity)]
    congr 1
    simp only [e]
    field_simp
  refine ⟨B * (M : ℝ) ^ e, fun r hr ↦ ?_⟩
  set j := Nat.clog M r
  have hrj : r ≤ M ^ j := Nat.le_pow_clog (by omega) r
  have hjr : ((M : ℝ) ^ j) ≤ M * r := by
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · have := Nat.pow_pred_clog_lt_self (b := M) (by omega) h1
      have hj : 1 ≤ j := Nat.clog_pos (by omega) h1
      have h2 : M ^ j = M * M ^ (j - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hj]
      have h3 : M ^ j ≤ M * r := by
        rw [h2]; exact Nat.mul_le_mul_left _ this.le
      exact_mod_cast h3
    · have hr1 : r = 1 := le_antisymm h1 hr
      subst hr1
      simp [j]
      linarith
  calc F r ≤ F (M ^ j) := hF hrj
    _ ≤ B * lam ^ j := hpow j
    _ = B * ((M : ℝ) ^ j) ^ e := by rw [hrpow]
    _ ≤ B * ((M : ℝ) * r) ^ e := by gcongr
    _ = B * (M : ℝ) ^ e * (r : ℝ) ^ e := by
        rw [Real.mul_rpow (by positivity) (by positivity)]; ring

/-- If `M < λ < M²` with `M > 1`, the exponent `log_M λ` lies strictly between `1` and `2`,
so `e₀ = log_M λ - 1 ∈ (0, 1)`. -/
theorem one_lt_log_div_log_lt_two {M lam : ℝ} (hM : 1 < M) (h1 : M < lam) (h2 : lam < M ^ 2) :
    1 < Real.log lam / Real.log M ∧ Real.log lam / Real.log M < 2 := by
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hl1 : Real.log M < Real.log lam := Real.log_lt_log (by linarith) h1
  have hl2 : Real.log lam < Real.log (M ^ 2) := Real.log_lt_log (by linarith) h2
  rw [Real.log_pow] at hl2
  push_cast at hl2
  exact ⟨(one_lt_div hlogM).mpr hl1, (div_lt_iff₀ hlogM).mpr (by linarith)⟩

end ScaleRecurrence

end OpenAI
