/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/IsometricDomainExtension.lean` (Apache 2.0). Adapted: only
`Matrix.norm_toLp_mulVec_of_isometry` is ported, with scalars generalized from `ℂ`; the
contraction bound is `Arealaw.l2_opNorm_le_one_of_conjTranspose_mul_self`.
-/
import Arealaw.OpNorm

/-!
# Isometries preserve Euclidean norms

A column isometry `J`, with `Jᴴ * J = 1`, preserves the Euclidean norm of every vector: it is a
contraction, and so is `Jᴴ`, which recovers the vector from its image.

Source: common private slot spaces, *Polynomial PEPS approximation of gapped square-grid
ground states*, September 24, 2026, `04-compression.tex:250–268`.

## Implementation notes

The source file also defines the extension `B * Jᴴ` of a map from an isometrically embedded
domain and its branch versions for `Matrix.sigmaBlockInclusion`; nothing downstream of
Proposition 8.1 uses them, so only the norm statement is ported. The source is over `ℂ`; the
statement holds over `RCLike 𝕜`.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n]

/-- A column isometry preserves Euclidean vector norms, without a nonzero-vector or
nonempty-space premise. -/
theorem norm_toLp_mulVec_of_isometry [Fintype p] [DecidableEq n]
    (J : Matrix p n 𝕜) (hJ : Jᴴ * J = 1) (ψ : EuclideanSpace 𝕜 n) :
    ‖WithLp.toLp 2 (J *ᵥ ψ.ofLp)‖ = ‖ψ‖ := by
  classical
  let v : EuclideanSpace 𝕜 p := WithLp.toLp 2 (J *ᵥ ψ.ofLp)
  have hJn : ‖J‖ ≤ 1 := Arealaw.l2_opNorm_le_one_of_conjTranspose_mul_self hJ
  have hJhn : ‖Jᴴ‖ ≤ 1 := by simpa only [l2_opNorm_conjTranspose] using hJn
  have hrecover : WithLp.toLp 2 (Jᴴ *ᵥ v.ofLp) = ψ := by
    change WithLp.toLp 2 (Jᴴ *ᵥ (J *ᵥ ψ.ofLp)) = ψ
    rw [mulVec_mulVec, hJ, one_mulVec, WithLp.toLp_ofLp]
  apply le_antisymm
  · calc
      ‖v‖ ≤ ‖J‖ * ‖ψ‖ := l2_opNorm_mulVec J ψ
      _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right hJn (norm_nonneg ψ)
      _ = ‖ψ‖ := one_mul _
  · calc
      ‖ψ‖ = ‖WithLp.toLp 2 (Jᴴ *ᵥ v.ofLp)‖ := congrArg norm hrecover.symm
      _ ≤ ‖Jᴴ‖ * ‖v‖ := l2_opNorm_mulVec Jᴴ v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hJhn (norm_nonneg v)
      _ = ‖v‖ := one_mul _

end Matrix
