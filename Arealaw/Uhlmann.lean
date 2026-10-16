import Arealaw.Purify
import Arealaw.SVD
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Uhlmann's theorem

The fidelity of two states is the largest fidelity between their purifications on a common
purifying system, and the largest is attained.  For pure states the fidelity is the overlap
`|⟨ψ|ψ'⟩|`, so this is also the largest overlap.

## Main statements

* `traceNorm_conjTranspose_mul`: `‖Xᴴ Y‖₁ = F(X Xᴴ, Y Yᴴ)` for any two purifications.
* `isGreatest_norm_trace_conjTranspose_mul`: Uhlmann in overlap form, TCR09 and Tomamichel15
  Eq. (3.31).
* `uhlmann`: Renner05 Theorem A.1.2, as stated.

## Implementation notes

A purification of `ρ` on `κ` is a coefficient matrix `ψ : Matrix ι κ 𝕜` with `rhoA ψ = ρ`
(`Arealaw.State`); the ket on `ι × κ` is `vec ψᵀ`.

The purifications of `ρ'` quantified over must share `ψ`'s system, and one must exist: with
`κ` smaller than the rank of `ρ'` the maximum is over the empty set.  That existence is the
only hypothesis added to the source; `exists_purification_of_card_le` supplies it.

Renner05's `ρ, ρ′ ∈ P(H)` are kept as `_hρ`, `_hρ'` although the purification hypotheses force
them (`posSemidef_rhoA`).

Renner05 defers the proof to Nielsen–Chuang Theorem 9.4, whose route is the polar decomposition
and the unitary freedom of purifications.  Neither is needed: `‖Xᴴ Y‖₁` equals the fidelity
for *every* pair, so the bound is `‖tr Z‖ ≤ ‖Z‖₁` and the maximizer is `Y U` for the unitary
`U` attaining `‖Xᴴ Y‖₁`.
-/

namespace Arealaw

open Matrix
open scoped ComplexOrder MatrixOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] {𝕜 : Type*} [RCLike 𝕜]

/-- `F(A, B) = ‖√A Y‖₁` for any purification `Y` of `B`. -/
theorem fidelity_eq_traceNorm_cfcSqrt_mul (A : Matrix ι ι 𝕜) (Y : Matrix ι κ 𝕜) :
    fidelity A (rhoA Y) = (CFC.sqrt A * Y).traceNorm := by
  rw [← traceNorm_conjTranspose, fidelity_comm, fidelity_def]
  refine traceNorm_eq_of_conjTranspose_mul_self_eq ?_
  rw [conjTranspose_cfcSqrt_mul_mul_cfcSqrt_mul (posSemidef_rhoA Y)]
  simp [rhoA, Matrix.mul_assoc]

/-- The trace-norm overlap of two purifications is the fidelity of the states they purify,
`‖Xᴴ Y‖₁ = F(X Xᴴ, Y Yᴴ)`. -/
theorem traceNorm_conjTranspose_mul (X Y : Matrix ι κ 𝕜) :
    (Xᴴ * Y).traceNorm = fidelity (rhoA X) (rhoA Y) := by
  rw [fidelity_eq_traceNorm_cfcSqrt_mul]
  refine traceNorm_eq_of_conjTranspose_mul_self_eq ?_
  rw [conjTranspose_cfcSqrt_mul_mul_cfcSqrt_mul (posSemidef_rhoA X)]
  simp [rhoA, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- The pure state `|v⟩⟨v|` is the reduced state of the column `v`. -/
theorem vecMulVec_self_star_eq_rhoA (v : ι → 𝕜) :
    vecMulVec v (star v) = rhoA (replicateCol Unit v) := by
  rw [rhoA, conjTranspose_replicateCol, vecMulVec_eq Unit]

/-- The fidelity of pure states is their overlap: `F(|v⟩⟨v|, |w⟩⟨w|) = |⟨v|w⟩|`. -/
@[simp]
theorem fidelity_vecMulVec (v w : ι → 𝕜) :
    fidelity (vecMulVec v (star v)) (vecMulVec w (star w)) = ‖star v ⬝ᵥ w‖ := by
  rw [vecMulVec_self_star_eq_rhoA, vecMulVec_self_star_eq_rhoA, ← traceNorm_conjTranspose_mul,
    conjTranspose_replicateCol, replicateRow_mul_replicateCol,
    ← diagonal_unique (fun _ : Unit ↦ star v ⬝ᵥ w), ← smul_one_eq_diagonal, traceNorm_smul]
  simp

/-- **Uhlmann's theorem**, overlap form: `F(ρ, ρ')` is the largest `|tr(ψᴴ ψ')|` over the
purifications `ψ'` of `ρ'` on `ψ`'s system. -/
theorem isGreatest_norm_trace_conjTranspose_mul (ψ : Matrix ι κ 𝕜) {ρ' : Matrix ι ι 𝕜}
    (h : ∃ ψ' : Matrix ι κ 𝕜, rhoA ψ' = ρ') :
    IsGreatest {F | ∃ ψ' : Matrix ι κ 𝕜, rhoA ψ' = ρ' ∧ F = ‖(ψᴴ * ψ').trace‖}
      (fidelity (rhoA ψ) ρ') := by
  classical
  obtain ⟨ψ₀, rfl⟩ := h
  obtain ⟨U, hU, hUZ⟩ := exists_mem_unitaryGroup_trace_mul_eq_traceNorm (ψᴴ * ψ₀)
  refine ⟨⟨ψ₀ * U,
    rhoA_mul_of_mul_conjTranspose_eq_one ψ₀ (Unitary.mul_star_self_of_mem hU), ?_⟩, ?_⟩
  · rw [← Matrix.mul_assoc, trace_mul_comm, hUZ, traceNorm_conjTranspose_mul,
      RCLike.norm_of_nonneg (fidelity_nonneg _ _)]
  · rintro _ ⟨ψ', hψ', rfl⟩
    rw [← hψ', ← traceNorm_conjTranspose_mul]
    exact norm_trace_le_traceNorm _

/-- **Uhlmann's theorem** (Renner05 Theorem A.1.2): if `ψ` purifies `ρ`, then `F(ρ, ρ')` is
the maximum of `F(|ψ⟩⟨ψ|, |ψ'⟩⟨ψ'|)` over the purifications `ψ'` of `ρ'` on the same
purifying system.  `h` is necessary: `ρ' = 1` on `Fin 2` has no purification on `Fin 1`, and
the maximum would be over the empty set. -/
theorem uhlmann [DecidableEq κ] {ρ ρ' : Matrix ι ι 𝕜} (_hρ : ρ.PosSemidef) (_hρ' : ρ'.PosSemidef)
    {ψ : Matrix ι κ 𝕜} (hψ : rhoA ψ = ρ) (h : ∃ ψ' : Matrix ι κ 𝕜, rhoA ψ' = ρ') :
    IsGreatest {F | ∃ ψ' : Matrix ι κ 𝕜, rhoA ψ' = ρ' ∧
        F = fidelity (vecMulVec (vec ψᵀ) (star (vec ψᵀ))) (vecMulVec (vec ψ'ᵀ) (star (vec ψ'ᵀ)))}
      (fidelity ρ ρ') := by
  simpa [star_vec_dotProduct_vec, conjTranspose_transpose_eq_transpose_conjTranspose, hψ] using
    isGreatest_norm_trace_conjTranspose_mul ψ h

end Arealaw
