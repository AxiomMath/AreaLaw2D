/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/ChannelGroundVectors.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations: the statements are made for
operators on any finite index type `n` instead of `ι → Fin q`, as for
`OpenAI.spectatorRootChannel`; QICLean `Matrix.sqrt_one_sub_mulVec_eq_self` and
`Matrix.sqrt_mulVec_eq_zero` are the declarations of the same names in OpenAI/RootChannel.lean
and OpenAI/MatrixSqrtKernel.lean.
-/
import Mathlib.LinearAlgebra.Matrix.Vec
import OpenAI.Amplification.ChannelWordObservables

/-!
# Words of root channels on a common ground vector

If every positive contraction `k i` annihilates `Ω`, its spectator root channel evaluated on
`Ω ⊗ ξ` leaves only the left action of `√(1 - k i)` [OAI265, §10.1, eq. (10.13),
`eq:amplification-channel-vector`].  A chronological word of channels therefore evaluates to the
product of these roots in reverse list order, and the vector error of two words is bounded by
the operator-norm error of the channel words.  Neither vector needs to be normalized and the
observable need not be Hermitian.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, `eq:amplification-channel-vector` and lines 218–224.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

variable {n κ Aux : Type*} [Fintype n] [DecidableEq n] [Fintype Aux] [DecidableEq Aux]

omit [DecidableEq n] in
private theorem kronecker_one_mulVec_product (A : Matrix n n ℂ) (Ω : n → ℂ) (ξ : Aux → ℂ) :
    (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (fun p => Ω p.1 * ξ p.2) =
      fun p => (A *ᵥ Ω) p.1 * ξ p.2 := by
  have h := Matrix.kronecker_mulVec_vec (1 : Matrix Aux Aux ℂ) (Matrix.vecMulVec ξ Ω) A
  simp only [Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose] at h
  change (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (fun p => ξ p.2 * Ω p.1) =
    (fun p => ξ p.2 * (A *ᵥ Ω) p.1) at h
  simpa only [mul_comm] using h

/-- A root channel on a ground vector is left multiplication by the complementary root, for an
arbitrary spectator vector and observable [OAI265, §10.1, eq. (10.13)]. -/
theorem spectatorRootChannel_mulVec_ground {k : Matrix n n ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {Ω : n → ℂ} (hΩ : k *ᵥ Ω = 0) (ξ : Aux → ℂ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannel k B *ᵥ (fun p => Ω p.1 * ξ p.2) =
      (CFC.sqrt (1 - k) ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) := by
  simp only [spectatorRootChannel, rootChannel, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, kronecker_one_mulVec_product,
    Matrix.sqrt_one_sub_mulVec_eq_self hk₁ hΩ, Matrix.sqrt_mulVec_eq_zero hk₀ hΩ,
    Pi.zero_apply, zero_mul, ← Pi.zero_def, Matrix.mulVec_zero, add_zero]

/-- A chronological word of root channels on a common ground vector is the product of the
roots with the latest event on the left [OAI265, §10.1, `09-amplification.tex`,
lines 218–224]. -/
theorem spectatorRootChannelWord_mulVec_ground (k : κ → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) {Ω : n → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0)
    (w : List κ) (ξ : Aux → ℂ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannelWord k w B *ᵥ (fun p => Ω p.1 * ξ p.2) =
      ((w.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
        (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w i ih =>
    rw [spectatorRootChannelWord_append_singleton,
      spectatorRootChannel_mulVec_ground (hk₀ i) (hk₁ i) (hΩ i), ih]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
    simp only [List.reverse_append, List.reverse_singleton, List.map_append,
      List.map_singleton, List.prod_append, List.prod_singleton]

/-- The vector error of two root products on `Ω ⊗ ξ` is bounded by the operator-norm error of
the two channel words [OAI265, §10.1, `09-amplification.tex`, lines 218–224]. -/
theorem norm_rootProduct_sub_le_channelWord_sub (k : κ → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) {Ω : n → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0)
    (u w : List κ) (ξ : Aux → ℂ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    ‖WithLp.toLp 2
      (((u.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
          (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) -
        ((w.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
          (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)))‖ ≤
      ‖spectatorRootChannelWord k u B - spectatorRootChannelWord k w B‖ *
        ‖WithLp.toLp 2 (fun p : n × Aux => Ω p.1 * ξ p.2)‖ := by
  rw [← spectatorRootChannelWord_mulVec_ground k hk₀ hk₁ hΩ u ξ B,
    ← spectatorRootChannelWord_mulVec_ground k hk₀ hk₁ hΩ w ξ B, ← Matrix.sub_mulVec]
  exact Matrix.l2_opNorm_mulVec
    (spectatorRootChannelWord k u B - spectatorRootChannelWord k w B)
    (WithLp.toLp 2 (fun p : n × Aux => Ω p.1 * ξ p.2))

end OpenAI
