/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/Circuit/SpectatorOscillationSupport.lean` (Apache 2.0).  Adaptations: the sites are a
region `T : Finset σ`; TNLean `spectatorSiteExpectation q K` is `OpenAI.spectatorCondExpect
(h : K ⊆ T)` and `supportedOperators q K` is `OpenAI.IsSupportedOn h`; `[NeZero q]` is
`[∀ i, Nonempty (loc i)]`; the field is a general `RCLike 𝕜`.
-/
import OpenAI.SiteOscillation
import OpenAI.SpectatorSiteExpectation

/-!
# Initial site oscillation of supported operators with spectators

An operator on the sites `T` and a finite spectator is fixed by `E_K ⊗ id` exactly when each of
its spectator blocks is supported on `K`.  Such an operator commutes with the physical operators
on `T \ K`, so its oscillation vanishes there.  With `d_y(B) ≤ 2 ‖B‖` this is the initial bound
`d_y(B) ≤ 2 ‖B‖ 1_K(y)` of [OAI265, §10.1, after eq. (10.10)], with no spectator dimension
factor and no Hermiticity assumption.
-/

namespace OpenAI

open Arealaw Matrix
open scoped Kronecker Matrix.Norms.L2Operator

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] {K T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux] {𝕜 : Type*} [RCLike 𝕜]

omit [Fintype Aux] [DecidableEq Aux] in
/-- An operator with a spectator is fixed by `E_K ⊗ id` exactly when each spectator block is
supported on `K` [OAI265, §10.1, before eq. (10.8) and after eq. (10.10)]. -/
theorem spectatorCondExpect_eq_self_iff (h : K ⊆ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    spectatorCondExpect h B = B ↔
      ∀ a b : Aux, IsSupportedOn h (Matrix.of fun u v => B (u, a) (v, b)) := by
  constructor
  · intro hB a b
    have hblock : condExpect h (Matrix.of fun u v => B (u, a) (v, b)) =
        Matrix.of fun u v => B (u, a) (v, b) := by
      ext u v
      exact congrArg (fun M => M (u, a) (v, b)) hB
    rw [← hblock]
    exact isSupportedOn_condExpect h _
  · intro hB
    ext ⟨u, a⟩ ⟨v, b⟩
    rw [spectatorCondExpect_apply, condExpect_of_isSupportedOn h (hB a b)]
    rfl

/-- An operator whose spectator blocks are supported on `K` has zero oscillation at every site
outside `K` [OAI265, §10.1, after eq. (10.10)]. -/
theorem siteOscillation_eq_zero_of_not_mem_support (h : K ⊆ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    (hB : ∀ a b : Aux, IsSupportedOn h (Matrix.of fun u v => B (u, a) (v, b))) {y : σ}
    (hy : y ∉ K) : siteOscillation y B = 0 := by
  apply siteOscillation_eq_zero_of_commute
  intro U hU
  have hUK : IsSupportedOn (Finset.sdiff_subset : T \ K ⊆ T) U :=
    hU.mono (fun z hz => by
      obtain ⟨hzy, hzT⟩ := Finset.mem_inter.1 hz
      rw [Finset.mem_singleton.1 hzy] at hzT ⊢
      exact Finset.mem_sdiff.2 ⟨hzT, hy⟩) _
  have hfix := (spectatorCondExpect_eq_self_iff h B).mpr hB
  simpa only [hfix] using (spectatorCondExpect_commute h B hUK).symm

/-- **Initial oscillation bound.**  `d_y(B) ≤ 2 ‖B‖ 1_K(y)` for an operator whose spectator
blocks are supported on `K`, with no spectator dimension factor
[OAI265, §10.1, after eq. (10.10)]. -/
theorem siteOscillation_le_support_indicator (h : K ⊆ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    (hB : ∀ a b : Aux, IsSupportedOn h (Matrix.of fun u v => B (u, a) (v, b))) (y : σ) :
    siteOscillation y B ≤ 2 * ‖B‖ * (K : Set σ).indicator (fun _ => (1 : ℝ)) y := by
  by_cases hy : y ∈ K
  · simpa only [Set.indicator_of_mem (Finset.mem_coe.2 hy), mul_one] using
      siteOscillation_le_two_mul_norm y B
  · rw [Set.indicator_of_notMem (by simpa using hy), mul_zero,
      siteOscillation_eq_zero_of_not_mem_support h B hB hy]

end OpenAI
