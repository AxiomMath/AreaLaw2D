/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/ChannelShellOscillation.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: the sites are a region
`T : Finset σ` with local family `loc` instead of `ι → Fin q`, and `[NeZero q]` is
`[∀ i, Nonempty (loc i)]`; TNLean `siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ T)`,
`localRootChannel K` is `OpenAI.localRootChannel (h : K ⊆ T)`, and
`localRootChannelShell regions` is `OpenAI.localRootChannelShell regions hregions` with
`hregions : ∀ l, regions l ⊆ T`; `spectatorSiteExpectation q (regions l)ᶜ` is
`OpenAI.spectatorCondExpect (Finset.sdiff_subset : T \ regions l ⊆ T)`; membership in
`supportedOperators q ((K : Set ι)ᶜ)` is `IsSupportedOn (Finset.sdiff_subset : T \ K ⊆ T)`;
`siteOscillation q y` is `OpenAI.siteOscillation y`.  The monotonicity hypothesis of the
regions is named `hmono`.
-/
import OpenAI.SpectatorOscillationSupport
import OpenAI.Amplification.LocalRootChannels

/-!
# Channel shells controlled by site oscillations

Average an operator over the physical sites of a shell region, leaving its finite spectator
untouched.  The average lies in the commutant of the operators on the region, where the
difference of two localized root channels vanishes.  The norm of a shell therefore depends
only on the on-site oscillations in its region [OAI265, §10.1, eq. (10.8)].  A channel
localized away from a site does not increase the oscillation there.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 101–127, `eq:amplification-shell-oscillation`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] {K T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- A channel localized away from a site does not increase the oscillation there, also on
operators acting on a spectator [OAI265, §10.1, `09-amplification.tex`, lines 124–127]. -/
theorem siteOscillation_localRootChannel_le_of_notMem (h : K ⊆ T)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (y : σ) (hy : y ∉ K) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    siteOscillation y (localRootChannel h k B) ≤ siteOscillation y B := by
  apply siteOscillation_le
  intro U hU hunitary
  have hUK : IsSupportedOn (Finset.sdiff_subset : T \ K ⊆ T) U :=
    hU.mono (fun z hz => by
      obtain ⟨hzy, hzT⟩ := Finset.mem_inter.1 hz
      rw [Finset.mem_singleton.1 hzy] at hzT ⊢
      exact Finset.mem_sdiff.2 ⟨hzT, hy⟩) _
  rw [localRootChannel_commutator h hk₀ hk₁ hUK B]
  exact (norm_localRootChannel_le h hk₀ hk₁ _).trans
    (norm_commutator_le_siteOscillation y B hU hunitary)

omit [∀ i, Fintype (loc i)] [∀ i, Nonempty (loc i)] in
/-- The operators supported on a subregion `K ⊆ T` are supported on `T \ (T \ K)`. -/
private theorem isSupportedOn_sdiff_sdiff (h : K ⊆ T) {A : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hA : IsSupportedOn h A) :
    IsSupportedOn (Finset.sdiff_subset : T \ (T \ K) ⊆ T) A :=
  hA.mono (by rw [Finset.sdiff_sdiff_eq_self h]) _

private theorem norm_shell_le_sum_oscillation (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (l : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∀ C : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ,
      ‖localRootChannelShell regions hregions k l C‖ ≤ η * ‖C‖)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannelShell regions hregions k l B‖ ≤
      η * ∑ y ∈ regions l, siteOscillation y B := by
  let E := spectatorCondExpect (Finset.sdiff_subset : T \ regions l ⊆ T) B
  have hzero : localRootChannelShell regions hregions k l E = 0 := by
    apply localRootChannelShell_eq_zero_of_forall_commute regions hregions hmono hk₀ hk₁ l
    intro A hA
    exact (spectatorCondExpect_commute _ B
      (isSupportedOn_sdiff_sdiff (hregions l) hA)).symm
  have havg : ‖B - E‖ ≤ ∑ y ∈ regions l, siteOscillation y B := by
    have h := norm_sub_spectatorCondExpect_le (Finset.sdiff_subset : T \ regions l ⊆ T) B
      (fun y => siteOscillation y B) (fun y _ U hU hunitary =>
        norm_commutator_le_siteOscillation_right y B hU hunitary)
    rwa [Finset.sdiff_sdiff_eq_self (hregions l)] at h
  have heq : localRootChannelShell regions hregions k l (B - E) =
      localRootChannelShell regions hregions k l B := by
    rw [localRootChannelShell_sub, hzero, sub_zero]
  rw [← heq]
  exact (hbound (B - E)).trans (mul_le_mul_of_nonneg_left havg hη)

/-- The zeroth localized root-channel shell is bounded by twice the sum of the oscillations in
its region, uniformly in the finite spectator
[OAI265, §10.1, `09-amplification.tex`, lines 101–121]. -/
theorem norm_localRootChannelShell_zero_le_sum_siteOscillation (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannelShell regions hregions k 0 B‖ ≤
      2 * ∑ y ∈ regions 0, siteOscillation y B :=
  norm_shell_le_sum_oscillation regions hregions hmono hk₀ hk₁ 0 (by norm_num)
    (norm_localRootChannelShell_zero_le regions hregions hk₀ hk₁) B

/-- A successor shell is controlled by the two localization errors and the sum of the
oscillations in the larger region, with no spectator dimension factor
[OAI265, §10.1, eq. (10.8), `eq:amplification-shell-oscillation`]. -/
theorem norm_localRootChannelShell_succ_le_sum_siteOscillation (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (l : ℕ) {εNext εPrev : ℝ}
    (hNext : ‖k - condExpect (hregions (l + 1)) k‖ ≤ εNext)
    (hPrev : ‖k - condExpect (hregions l) k‖ ≤ εPrev)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannelShell regions hregions k (l + 1) B‖ ≤
      4 * (Real.sqrt εNext + Real.sqrt εPrev) *
        ∑ y ∈ regions (l + 1), siteOscillation y B :=
  norm_shell_le_sum_oscillation regions hregions hmono hk₀ hk₁ (l + 1)
    (mul_nonneg (by norm_num) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (norm_localRootChannelShell_succ_le regions hregions hk₀ hk₁ l hNext hPrev) B

end OpenAI
