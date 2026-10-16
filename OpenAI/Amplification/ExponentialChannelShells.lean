/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/ExponentialChannelShells.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations as in
`OpenAI.Amplification.ChannelShellOscillation`: the sites are a region `T : Finset σ` with
local family `loc`, `[NeZero q]` is `[∀ i, Nonempty (loc i)]`, `siteExpectation q K` is
`OpenAI.condExpect (h : K ⊆ T)`, the localized channels and shells take the proofs
`hregions : ∀ l, regions l ⊆ T`, and the monotonicity hypothesis is named `hmono`.
-/
import Mathlib.Analysis.MeanInequalitiesPow
import OpenAI.Amplification.LocalChannelOscillation

/-!
# Stretched-exponential bounds for local channel shells

Localization errors `C e^{-c l^α}` give the shell coefficient the bound
`(2 + 8 √C e^{c/2}) e^{-(c/2) l^α}`, including radius zero.  The same explicit coefficients
bound the shells by the oscillations in their regions, and the finite one-event oscillation
increment, uniformly in the finite spectator [OAI265, §10.1, eqs. (10.7)–(10.9)].  These are
finite-radius statements for increasing regions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 101–139, `eq:amplification-channel-shells`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

/-- Explicit constants in the stretched-exponential shell estimate, including the zeroth shell
[OAI265, §10.1, eq. (10.7), `eq:amplification-channel-shells`]. -/
theorem localRootChannelShellBound_le_exp {C c α : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) (l : ℕ) :
    localRootChannelShellBound (fun j => C * Real.exp (-(c * (j : ℝ) ^ α))) l ≤
      (2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
        Real.exp (-(c / 2 * (l : ℝ) ^ α)) := by
  have hsqrt (j : ℕ) :
      Real.sqrt (C * Real.exp (-(c * (j : ℝ) ^ α))) =
        Real.sqrt C * Real.exp (-(c / 2 * (j : ℝ) ^ α)) := by
    rw [Real.sqrt_mul hC, ← Real.exp_half]
    congr 2
    ring
  cases l with
  | zero =>
    simpa only [localRootChannelShellBound, Nat.cast_zero, Real.zero_rpow hα.ne',
      mul_zero, neg_zero, Real.exp_zero, mul_one] using
      le_add_of_nonneg_right (show 0 ≤ 8 * Real.sqrt C * Real.exp (c / 2) by positivity)
  | succ n =>
    have hstep : ((n + 1 : ℕ) : ℝ) ^ α ≤ (n : ℝ) ^ α + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one, Real.one_rpow] using
        Real.rpow_add_le_add_rpow (Nat.cast_nonneg n) (show (0 : ℝ) ≤ 1 by norm_num)
          hα.le hα₁
    have hprev : Real.exp (-(c / 2 * (n : ℝ) ^ α)) ≤
        Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hstep (show 0 ≤ c / 2 by positivity)]
    have hnext : Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) ≤
        Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) :=
      le_mul_of_one_le_left (Real.exp_pos _).le
        (Real.one_le_exp_iff.mpr (by positivity))
    simp only [localRootChannelShellBound, hsqrt]
    calc
      _ ≤ 4 * (Real.sqrt C *
              (Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α))) +
            Real.sqrt C *
              (Real.exp (c / 2) * Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hnext (Real.sqrt_nonneg C))
            (mul_le_mul_of_nonneg_left hprev (Real.sqrt_nonneg C))) (by norm_num)
      _ = (8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * ((n + 1 : ℕ) : ℝ) ^ α)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] {T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Stretched-exponential localization errors of a positive contraction give an explicit shell
bound by the oscillations in its region
[OAI265, §10.1, eq. (10.8), `09-amplification.tex`, lines 109–121]. -/
theorem norm_localRootChannelShell_le_exp_sum_siteOscillation (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) (l : ℕ)
    (hε : ∀ j ≤ l, ‖k - condExpect (hregions j) k‖ ≤ C * Real.exp (-(c * (j : ℝ) ^ α)))
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannelShell regions hregions k l B‖ ≤
      ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) * Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
        ∑ z ∈ regions l, siteOscillation z B :=
  (norm_localRootChannelShell_le_sum_siteOscillation regions hregions hmono hk₀ hk₁ _ l hε
    B).trans <| mul_le_mul_of_nonneg_right (localRootChannelShellBound_le_exp hC hc hα hα₁ l)
      (Finset.sum_nonneg fun z _ => siteOscillation_nonneg z B)

/-- The finite one-event oscillation increment with explicit stretched-exponential
coefficients; shells contribute exactly when their region contains the observed site
[OAI265, §10.1, eq. (10.9), `09-amplification.tex`, lines 124–139]. -/
theorem siteOscillation_localRootChannel_le_exp (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - condExpect (hregions l) k‖ ≤ C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : σ) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    siteOscillation y (localRootChannel (hregions n) k B) ≤
      siteOscillation y B +
        2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l),
          ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) * Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
            ∑ z ∈ regions l, siteOscillation z B := by
  apply (siteOscillation_localRootChannel_le regions hregions hmono hk₀ hk₁ _ n hε y B).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_right (localRootChannelShellBound_le_exp hC hc hα hα₁ l)
    (Finset.sum_nonneg fun z _ => siteOscillation_nonneg z B)

end OpenAI
