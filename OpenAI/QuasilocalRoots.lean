/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit
fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/QuasilocalRoots.lean`. Apache 2.0; adapted to the frozen
`OpenAI.condExpect`, `OpenAI.IsSupportedOn`, and `OpenAI.PositiveReplacement` interfaces.
-/
import OpenAI.PositiveReplacement
import OpenAI.RegionLift
import OpenAI.RootChannel

/-!
# Quasilocal square roots and their channels

This is Lemma 4.4 of OAI265 for one constraint and one localization region.  Proposition 4.3
supplies exactly the hypotheses `0 ≤ k ≤ 1`, `k Ω = 0`, and the conditional-expectation tail
used below.  The theorem is over `ℂ`, where the root channel is a C⋆-algebra construction.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw _root_.Matrix

/-- The scalar square-root identity that halves the exponential decay rate. -/
theorem sqrt_mul_exp_neg (C c x : ℝ) :
    Real.sqrt (C * Real.exp (-(c * x))) = Real.sqrt C * Real.exp (-(c / 2 * x)) := by
  rw [Real.sqrt_mul' _ (Real.exp_pos _).le]
  congr 1
  rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T : Finset σ}

/-- **Quasilocal roots** (Lemma 4.4).  For a positive contraction `k`, its normalized
conditional expectation `kₗ`, and `‖k-kₗ‖ ≤ ε`, the four square roots are positive
contractions.  The global roots fix the ground vector, both root channels are unital and
completely positive contractions after adjoining any finite auxiliary system, their distance
is at most `4 √ε`, and the local channel fixes every operator supported outside `S`. -/
theorem quasilocal_roots [Nonempty (Reg loc (T \ S))] (hS : S ⊆ T)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {Ω : Reg loc T → ℂ} (hkΩ : k *ᵥ Ω = 0) {ε : ℝ}
    (hε : ‖k - condExpect hS k‖ ≤ ε) :
    let kl := condExpect hS k
    let G := CFC.sqrt (1 - k)
    let Kr := CFC.sqrt k
    let Gl := CFC.sqrt (1 - kl)
    let Kl := CFC.sqrt kl
    (0 ≤ G ∧ G ≤ 1) ∧ (0 ≤ Kr ∧ Kr ≤ 1) ∧
      (0 ≤ Gl ∧ Gl ≤ 1) ∧ (0 ≤ Kl ∧ Kl ≤ 1) ∧
      G *ᵥ Ω = Ω ∧ Kr *ᵥ Ω = 0 ∧
      ‖G - Gl‖ + ‖Kr - Kl‖ ≤ 2 * Real.sqrt ε ∧ Gl * Gl + Kl * Kl = 1 ∧
      rootChannel G Kr 1 = 1 ∧ rootChannel Gl Kl 1 = 1 ∧
      (∀ (κ : Type*) [Fintype κ] [DecidableEq κ]
          (B : Matrix ((Reg loc T) × κ) ((Reg loc T) × κ) ℂ),
        (0 ≤ B →
            0 ≤ rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B ∧
            0 ≤ rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B) ∧
        ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
        ‖rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
        ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B -
            rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤
          4 * Real.sqrt ε * ‖B‖) ∧
      (∀ B : Matrix (Reg loc T) (Reg loc T) ℂ,
        IsSupportedOn (Finset.sdiff_subset : T \ S ⊆ T) B → rootChannel Gl Kl B = B) := by
  intro kl G Kr Gl Kl
  have hl₀ : 0 ≤ kl := condExpect_nonneg hS hk₀
  have hl₁ : kl ≤ 1 := condExpect_le_one hS hk₁
  have hG : 0 ≤ G := CFC.sqrt_nonneg _
  have hKr : 0 ≤ Kr := CFC.sqrt_nonneg _
  have hGl : 0 ≤ Gl := CFC.sqrt_nonneg _
  have hKl : 0 ≤ Kl := CFC.sqrt_nonneg _
  have hG1 : G ≤ 1 := sqrt_le_one (sub_le_self _ hk₀)
  have hKr1 : Kr ≤ 1 := sqrt_le_one hk₁
  have hGl1 : Gl ≤ 1 := sqrt_le_one (sub_le_self _ hl₀)
  have hKl1 : Kl ≤ 1 := sqrt_le_one hl₁
  have hGn : ‖G‖ ≤ 1 := l2_opNorm_le_one_of_nonneg_of_le_one hG hG1
  have hKrn : ‖Kr‖ ≤ 1 := l2_opNorm_le_one_of_nonneg_of_le_one hKr hKr1
  have hGln : ‖Gl‖ ≤ 1 := l2_opNorm_le_one_of_nonneg_of_le_one hGl hGl1
  have hKln : ‖Kl‖ ≤ 1 := l2_opNorm_le_one_of_nonneg_of_le_one hKl hKl1
  have hsq : G * G + Kr * Kr = 1 := sqrt_one_sub_mul_add_sqrt_mul hk₀ hk₁
  have hsql : Gl * Gl + Kl * Kl = 1 := sqrt_one_sub_mul_add_sqrt_mul hl₀ hl₁
  have htG : ‖G - Gl‖ ≤ Real.sqrt ε :=
    (norm_sqrt_one_sub_sub_le hk₁ hl₁).trans (Real.sqrt_le_sqrt hε)
  have htK : ‖Kr - Kl‖ ≤ Real.sqrt ε :=
    (norm_sqrt_sub_le hk₀ hl₀).trans (Real.sqrt_le_sqrt hε)
  have hGh : G.IsHermitian := hG.isSelfAdjoint
  have hKh : Kr.IsHermitian := hKr.isSelfAdjoint
  have hGlh : Gl.IsHermitian := hGl.isSelfAdjoint
  have hKlh : Kl.IsHermitian := hKl.isSelfAdjoint
  refine ⟨⟨hG, hG1⟩, ⟨hKr, hKr1⟩, ⟨hGl, hGl1⟩, ⟨hKl, hKl1⟩,
    sqrt_one_sub_mulVec_eq_self hk₁ hkΩ, sqrt_mulVec_eq_zero hk₀ hkΩ, by linarith, hsql,
    rootChannel_one hsq, rootChannel_one hsql, fun κ _ _ B => ⟨fun hB =>
      ⟨rootChannel_kronecker_nonneg hGh hKh hB,
        rootChannel_kronecker_nonneg hGlh hKlh hB⟩,
      norm_rootChannel_kronecker_le hGh hKh hsq B,
      norm_rootChannel_kronecker_le hGlh hKlh hsql B, ?_⟩, fun B hB => ?_⟩
  · refine (norm_rootChannel_kronecker_sub_le G Kr Gl Kl B).trans ?_
    have hs := Real.sqrt_nonneg ε
    have hBnorm := norm_nonneg B
    have h1 :
        (‖G‖ + ‖Gl‖) * ‖G - Gl‖ + (‖Kr‖ + ‖Kl‖) * ‖Kr - Kl‖ ≤
          4 * Real.sqrt ε := by
      have a1 : (‖G‖ + ‖Gl‖) * ‖G - Gl‖ ≤ 2 * Real.sqrt ε :=
        mul_le_mul (by linarith) htG (norm_nonneg _) (by norm_num)
      have a2 : (‖Kr‖ + ‖Kl‖) * ‖Kr - Kl‖ ≤ 2 * Real.sqrt ε :=
        mul_le_mul (by linarith) htK (norm_nonneg _) (by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right h1 hBnorm
  · exact rootChannel_sqrt_eq_self_of_commute hl₀ hl₁
      ((isSupportedOn_condExpect hS k).commute hB Finset.disjoint_sdiff)

end OpenAI
