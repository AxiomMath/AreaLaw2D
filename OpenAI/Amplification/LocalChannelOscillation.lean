/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/LocalChannelOscillation.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations as in
`OpenAI.Amplification.ChannelShellOscillation`: the sites are a region `T : Finset σ` with
local family `loc`, `[NeZero q]` is `[∀ i, Nonempty (loc i)]`, `siteExpectation q K` is
`OpenAI.condExpect (h : K ⊆ T)`, the localized channels and shells take the proofs
`hregions : ∀ l, regions l ⊆ T`, and the monotonicity hypothesis is named `hmono`.
-/
import OpenAI.Amplification.ChannelShellOscillation

/-!
# Oscillation increments of a local channel

For increasing finite regions, the oscillation of a localized root channel at a site `y` is
bounded by the original oscillation plus the shells whose regions contain `y`, with
coefficients `localRootChannelShellBound ε` built from the localization errors `ε` of the
positive contraction [OAI265, §10.1, eq. (10.9), before the radius limit].  The observables
are arbitrary, not necessarily Hermitian, and the spectator is an arbitrary finite system.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 101–139, `eq:amplification-oscillation-increment`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

/-- The coefficient of the `l`-th channel shell: `2` for the zeroth shell and
`4 (√ε_{l+1} + √ε_l)` for a successor shell [OAI265, §10.1, eq. (10.7)]. -/
noncomputable def localRootChannelShellBound (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => 2
  | l + 1 => 4 * (Real.sqrt (ε (l + 1)) + Real.sqrt (ε l))

@[simp] theorem localRootChannelShellBound_zero (ε : ℕ → ℝ) :
    localRootChannelShellBound ε 0 = 2 := rfl

theorem localRootChannelShellBound_succ (ε : ℕ → ℝ) (l : ℕ) :
    localRootChannelShellBound ε (l + 1) = 4 * (Real.sqrt (ε (l + 1)) + Real.sqrt (ε l)) :=
  rfl

theorem localRootChannelShellBound_nonneg (ε : ℕ → ℝ) (l : ℕ) :
    0 ≤ localRootChannelShellBound ε l := by
  cases l with
  | zero => norm_num [localRootChannelShellBound]
  | succ l =>
    exact mul_nonneg (by norm_num) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] {T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The localization errors through radius `l` bound the `l`-th shell by the oscillations in
its region [OAI265, §10.1, eq. (10.8), `09-amplification.tex`, lines 101–121]. -/
theorem norm_localRootChannelShell_le_sum_siteOscillation (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (ε : ℕ → ℝ) (l : ℕ) (hε : ∀ j ≤ l, ‖k - condExpect (hregions j) k‖ ≤ ε j)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannelShell regions hregions k l B‖ ≤
      localRootChannelShellBound ε l * ∑ z ∈ regions l, siteOscillation z B := by
  cases l with
  | zero =>
    exact norm_localRootChannelShell_zero_le_sum_siteOscillation regions hregions hmono
      hk₀ hk₁ B
  | succ l =>
    exact norm_localRootChannelShell_succ_le_sum_siteOscillation regions hregions hmono
      hk₀ hk₁ l (hε (l + 1) le_rfl) (hε l (Nat.le_succ l)) B

/-- **Oscillation increment of a local channel** at a finite radius `n`: only the shells whose
regions contain `y` contribute, and only the localization errors through `n` are used
[OAI265, §10.1, eq. (10.9), `09-amplification.tex`, lines 124–139, before the radius limit]. -/
theorem siteOscillation_localRootChannel_le (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (ε : ℕ → ℝ) (n : ℕ) (hε : ∀ l ≤ n, ‖k - condExpect (hregions l) k‖ ≤ ε l)
    (y : σ) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    siteOscillation y (localRootChannel (hregions n) k B) ≤
      siteOscillation y B +
        2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l),
          localRootChannelShellBound ε l * ∑ z ∈ regions l, siteOscillation z B := by
  let a (l : ℕ) := localRootChannelShellBound ε l * ∑ z ∈ regions l, siteOscillation z B
  have ha (l : ℕ) : 0 ≤ a l :=
    mul_nonneg (localRootChannelShellBound_nonneg ε l)
      (Finset.sum_nonneg fun z _ => siteOscillation_nonneg z B)
  change siteOscillation y (localRootChannel (hregions n) k B) ≤
    siteOscillation y B + 2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l), a l
  rw [Finset.sum_filter]
  revert hε
  induction n with
  | zero =>
    intro hε
    by_cases hy : y ∈ regions 0
    · have hsplit : localRootChannel (hregions 0) k B =
          B + localRootChannelShell regions hregions k 0 B := by
        simp only [localRootChannelShell, add_sub_cancel]
      have hnorm := norm_localRootChannelShell_le_sum_siteOscillation
        regions hregions hmono hk₀ hk₁ ε 0 hε B
      change ‖localRootChannelShell regions hregions k 0 B‖ ≤ a 0 at hnorm
      have hosc := siteOscillation_le_two_mul_norm y (localRootChannelShell regions hregions k 0 B)
      calc
        _ ≤ siteOscillation y B +
            siteOscillation y (localRootChannelShell regions hregions k 0 B) := by
          rw [hsplit]
          exact siteOscillation_add_le y _ _
        _ ≤ siteOscillation y B + 2 * a 0 := by linarith
        _ = _ := by simp [hy]
    · simpa [hy] using
        siteOscillation_localRootChannel_le_of_notMem (hregions 0) hk₀ hk₁ y hy B
  | succ n ih =>
    intro hε
    by_cases hy : y ∈ regions (n + 1)
    · have hsplit : localRootChannel (hregions (n + 1)) k B =
          localRootChannel (hregions n) k B +
            localRootChannelShell regions hregions k (n + 1) B := by
        simp only [localRootChannelShell, add_sub_cancel]
      have hnorm := norm_localRootChannelShell_le_sum_siteOscillation
        regions hregions hmono hk₀ hk₁ ε (n + 1) hε B
      change ‖localRootChannelShell regions hregions k (n + 1) B‖ ≤ a (n + 1) at hnorm
      have hosc := siteOscillation_le_two_mul_norm y
        (localRootChannelShell regions hregions k (n + 1) B)
      have hprev := ih fun l hl => hε l (hl.trans (Nat.le_succ n))
      calc
        _ ≤ siteOscillation y (localRootChannel (hregions n) k B) +
            siteOscillation y (localRootChannelShell regions hregions k (n + 1) B) := by
          rw [hsplit]
          exact siteOscillation_add_le y _ _
        _ ≤ (siteOscillation y B +
              2 * ∑ l ∈ Finset.range (n + 1), if y ∈ regions l then a l else 0) +
            2 * a (n + 1) := by linarith
        _ = _ := by
          rw [Finset.sum_range_succ (n := n + 1)]
          simp only [hy, ite_true, mul_add, add_assoc]
    · apply (siteOscillation_localRootChannel_le_of_notMem
        (hregions (n + 1)) hk₀ hk₁ y hy B).trans
      apply le_add_of_nonneg_right
      exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun l _ => by split_ifs <;> [exact ha l; exact le_rfl])

end OpenAI
