/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/Scan/ExponentBootstrap.lean`. Apache 2.0.
-/
import OpenAI.BoxEntropy
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite improvement of an entropy exponent

Let a family of functions `F i : ℕ → ℝ` satisfy a uniform quadratic bound `F i n ≤ V n²` and an
initial bound `F i n ≤ C₀ n^(1 + e₀)` on scales `n ≥ 1`.  Suppose every exponent `e` with
`ε < e ≤ e₀` can be replaced by `(1 - ℓ) e` on all sufficiently large scales, with constants and
thresholds uniform over the family.  Since `(1 - ℓ)^m e₀ ≤ ε` for some `m`, finitely many
repetitions give a uniform bound `F i n ≤ C n^(1 + ε)` on every scale `n ≥ 1`; at each step the
quadratic bound absorbs the finitely many excluded scales into the constant.  This is the last
paragraph of the proof of Proposition 9.5 of [OAI265].

The one-step improvement `e ↦ (1 - ℓ) e` is a hypothesis of every theorem here, not a result:
it is the analytic content of Proposition 9.5.  The file proves only the finite iteration, and
specializes it to the safe-box entropy `OpenAI.boxEntropy`, whose quadratic bound is
`OpenAI.boxEntropy_le_sq_mul_log`.

## Main statements

* `OpenAI.exists_uniform_rpow_bound_of_eventually`: a quadratic bound extends an eventual power
  bound to all scales `n ≥ 1`.
* `OpenAI.exists_uniform_rpow_bound_of_eventual_improvement`: the finite iteration.
* `OpenAI.exists_boxEntropy_le_rpow_of_eventual_improvement`: the iteration for `F_box`.

## Implementation notes

TNLean also states the iteration at the paper's fixed exponent `e_* = 2 · 10⁻⁶` and step
`ℓ = (1 - e₀) / 200000`; here `ε` and `ℓ` are arbitrary with `0 < ε` and `0 < ℓ < 1`, which
contains that instance.  The improvement hypothesis is taken for every constant `C`, and its
conclusion asks for no sign on the new constant, matching how Proposition 9.5 is stated.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  proof of Proposition 9.5 (`prop:small-box`), last paragraph.
-/

namespace OpenAI

section Family

variable {ι : Type*} {F : ι → ℕ → ℝ}

/-- A uniform quadratic bound extends a uniform power bound on scales `n ≥ N` to every scale
`n ≥ 1`, with a positive constant independent of the family index. -/
theorem exists_uniform_rpow_bound_of_eventually {V e C : ℝ} {N : ℕ} (he : 0 ≤ e)
    (hsq : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hlarge : ∀ i n, N ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ i n, 1 ≤ n → F i n ≤ C' * (n : ℝ) ^ (1 + e) := by
  have hV : 0 ≤ max V 0 * (N : ℝ) ^ 2 := mul_nonneg (le_max_right _ _) (sq_nonneg _)
  refine ⟨max C 0 + max V 0 * (N : ℝ) ^ 2 + 1, by positivity, fun i n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ (1 + e) := Real.one_le_rpow hn1 (by linarith)
  by_cases hNn : N ≤ n
  · calc F i n ≤ C * (n : ℝ) ^ (1 + e) := hlarge i n hNn
      _ ≤ max C 0 * (n : ℝ) ^ (1 + e) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [le_max_right C 0]) (by positivity)
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (lt_of_not_ge hNn).le
    calc F i n ≤ V * (n : ℝ) ^ 2 := hsq i n hn
      _ ≤ max V 0 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ max V 0 * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) hnN 2) (le_max_right _ _)
      _ ≤ max C 0 + max V 0 * (N : ℝ) ^ 2 + 1 := by linarith [le_max_right C 0]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpow

/-- A power bound on scales `n ≥ 1` persists when the exponent is increased. -/
theorem uniform_rpow_bound_mono {C e e' : ℝ} (hC : 0 ≤ C) (hee' : e ≤ e')
    (hbound : ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) :
    ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e') := fun i n hn =>
  (hbound i n hn).trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hC

/-- **Finite exponent improvement.**  Given a uniform quadratic bound and a uniform bound of
order `n^(1 + e₀)`, if every exponent `ε < e ≤ e₀` improves to `(1 - ℓ) e` on all large scales,
uniformly over the family, then the family is uniformly bounded by `C n^(1 + ε)` on every scale
`n ≥ 1`.  The improvement is a hypothesis. -/
theorem exists_uniform_rpow_bound_of_eventual_improvement {V C₀ e₀ ε ℓ : ℝ}
    (he₀ : 0 < e₀) (hε : 0 < ε) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    (hsq : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hinit : ∀ i n, 1 ≤ n → F i n ≤ C₀ * (n : ℝ) ^ (1 + e₀))
    (himprove : ∀ e : ℝ, ε < e → e ≤ e₀ → ∀ C : ℝ,
      (∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) →
      ∃ (C' : ℝ) (N : ℕ), ∀ i n, N ≤ n → F i n ≤ C' * (n : ℝ) ^ (1 + (1 - ℓ) * e)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + ε) := by
  by_contra hfinal
  have hfactor : 0 < 1 - ℓ := sub_pos.mpr hℓ₁
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hε he₀) (sub_lt_self 1 hℓ)
  have hiter : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + (1 - ℓ) ^ j * e₀) := by
    intro j
    induction j with
    | zero =>
      simpa only [pow_zero, one_mul] using
        exists_uniform_rpow_bound_of_eventually (N := 1) he₀.le hsq hinit
    | succ j hj =>
      obtain ⟨C, hC, hb⟩ := hj
      have he : ε < (1 - ℓ) ^ j * e₀ := lt_of_not_ge fun hle =>
        hfinal ⟨C, hC, uniform_rpow_bound_mono hC.le hle hb⟩
      have heupper : (1 - ℓ) ^ j * e₀ ≤ e₀ :=
        mul_le_of_le_one_left he₀.le (pow_le_one₀ hfactor.le (sub_le_self 1 hℓ.le))
      obtain ⟨C', N, hlarge⟩ := himprove _ he heupper C hb
      simpa only [pow_succ', mul_assoc] using
        exists_uniform_rpow_bound_of_eventually
          (mul_nonneg hfactor.le (hε.trans he).le) hsq hlarge
  obtain ⟨C, hC, hb⟩ := hiter m
  exact hfinal ⟨C, hC, uniform_rpow_bound_mono hC.le ((lt_div_iff₀ he₀).mp hm).le hb⟩

end Family

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ}

/-- **Finite exponent improvement for `F_box`** [OAI265, Proposition 9.5].  If
`F_box(r) ≤ C₀ r^(1 + e₀)` for `r ≥ 1`, and every exponent `ε < e ≤ e₀` of a bound
`F_box(r) ≤ C r^(1 + e)` on `r ≥ 1` improves to `(1 - ℓ) e` on all large `r`, then
`F_box(r) ≤ C r^(1 + ε)` for every `r ≥ 1`.  The improvement is a hypothesis. -/
theorem exists_boxEntropy_le_rpow_of_eventual_improvement {C₀ e₀ ε ℓ : ℝ}
    (he₀ : 0 < e₀) (hε : 0 < ε) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    (hinit : ∀ r : ℕ, 1 ≤ r → boxEntropy 𝕜 q R J Δ r ≤ C₀ * (r : ℝ) ^ (1 + e₀))
    (himprove : ∀ e : ℝ, ε < e → e ≤ e₀ → ∀ C : ℝ,
      (∀ r : ℕ, 1 ≤ r → boxEntropy 𝕜 q R J Δ r ≤ C * (r : ℝ) ^ (1 + e)) →
      ∃ (C' : ℝ) (N : ℕ), ∀ r : ℕ, N ≤ r →
        boxEntropy 𝕜 q R J Δ r ≤ C' * (r : ℝ) ^ (1 + (1 - ℓ) * e)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → boxEntropy 𝕜 q R J Δ r ≤ C * (r : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_rpow_bound_of_eventual_improvement
    (F := fun (_ : Unit) => boxEntropy 𝕜 q R J Δ) (V := Real.log q) he₀ hε hℓ hℓ₁
    (fun _ r _ => (boxEntropy_le_sq_mul_log r).trans_eq (mul_comm _ _))
    (fun _ => hinit) (fun e he he' C hC => by
      obtain ⟨C', N, h⟩ := himprove e he he' C (hC ())
      exact ⟨C', N, fun _ => h⟩)
  exact ⟨C, hC, h ()⟩

end OpenAI
