/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/Circuit/SiteExpectationOrder.lean` (Apache 2.0).  Adaptations: TNLean
`siteExpectation q K` is `OpenAI.condExpect (h : K ⊆ T)` and `supportedOperators q K` is
`OpenAI.IsSupportedOn h`.  Of the source only `sqrt_mem_supportedOperators` is ported, as
`OpenAI.IsSupportedOn.cfcSqrt` over `RCLike 𝕜`, with the closure of support under negation
and subtraction it needs.  `siteExpectation_nonneg`, `siteExpectation_mono`,
`siteExpectation_le_one`, `isHermitian_siteExpectation` and
`siteExpectation_abs_of_mem_supportedOperators` are `OpenAI.condExpect_nonneg`,
`OpenAI.condExpect_mono`, `OpenAI.condExpect_le_one`, `OpenAI.isHermitian_condExpect` and
`OpenAI.condExpect_of_isSupportedOn` with `OpenAI.IsSupportedOn.cfcAbs`
(OpenAI/ConditionalExpectation.lean); `heisenbergEvolution_eq_hermitianUnitaryPath`,
`siteExpectation_conjTranspose`, `siteExpectation_eq_self_of_forall_commute`,
`mem_supportedOperators_of_forall_commute` and `Commute.cfcAbs_of_isHermitian` are not used
along the cone and are omitted.
-/
import OpenAI.ConditionalExpectation

/-!
# Support of square roots

The square root of a positive operator supported on `S ⊆ T` is again supported on `S`
[OAI265, §4.2, proof of Lemma 4.4]: it is the extension by the identity of the square root of
the local operator.  With closure of support under subtraction this places the local roots
`√(1 - E_S(k))` and `√(E_S(k))` of Lemma 4.4 on `S`.
-/

namespace OpenAI

open Arealaw Matrix
open scoped Matrix MatrixOrder ComplexOrder

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T : Finset σ} {𝕜 : Type*} [RCLike 𝕜]

omit [∀ i, Fintype (loc i)] in
theorem IsSupportedOn.neg {h : S ⊆ T} {B : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hB : IsSupportedOn h B) : IsSupportedOn h (-B) := by
  obtain ⟨B, rfl⟩ := hB
  exact ⟨-B, (extendId_neg h B).symm⟩

omit [∀ i, Fintype (loc i)] in
theorem IsSupportedOn.sub {h : S ⊆ T} {B C : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hB : IsSupportedOn h B) (hC : IsSupportedOn h C) : IsSupportedOn h (B - C) := by
  rw [sub_eq_add_neg]
  exact hB.add hC.neg

/-- The square root of a positive operator supported on `S` is supported on `S`
[OAI265, §4.2, proof of Lemma 4.4]. -/
theorem IsSupportedOn.cfcSqrt {h : S ⊆ T} {A : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hA₀ : 0 ≤ A) (hA : IsSupportedOn h A) : IsSupportedOn h (CFC.sqrt A) := by
  obtain ⟨A, rfl⟩ := hA
  rcases isEmpty_or_nonempty (Reg loc (T \ S)) with hE | hN
  · have : IsEmpty (Reg loc T) := (glueEquiv h).symm.isEmpty
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨c⟩ := hN
  have hA0 : 0 ≤ A := by
    have hp := (Matrix.nonneg_iff_posSemidef.1 hA₀).submatrix
      (fun x : Reg loc S => glueEquiv h (x, c))
    have he : (extendId h A).submatrix (fun x : Reg loc S => glueEquiv h (x, c))
        (fun x : Reg loc S => glueEquiv h (x, c)) = A := by
      ext u v
      simp
    rw [he] at hp
    exact hp.nonneg
  refine ⟨CFC.sqrt A, ?_⟩
  refine (CFC.sqrt_eq_iff _ _ hA₀
    (posSemidef_extendId h (CFC.sqrt_nonneg A).posSemidef).nonneg).mpr ?_
  rw [← extendId_mul, CFC.sqrt_mul_sqrt_self A hA0]

end OpenAI
