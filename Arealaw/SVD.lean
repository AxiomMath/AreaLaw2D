import Arealaw.Fidelity

/-!
# The trace norm is attained by a unitary

A square matrix with orthogonal columns is a unitary times the diagonal of their lengths.
Applied to `A Q` for `Q` diagonalizing `AᴴA`, this is the singular value decomposition, and it
gives a unitary `U` with `tr(U A) = ‖A‖₁`.

## Implementation notes

Physlib has both as `Matrix.exists_svd_sqrt_eigenvalues` and `Matrix.traceNorm_eq_max_re_tr_U`,
`ℂ`-only; nothing in the argument needs `ℂ`.  The singular value decomposition itself is not
stated: `exists_mem_unitaryGroup_eq_mul_diagonal` is the step it is made of.
-/

namespace Arealaw

open Matrix
open scoped ComplexOrder InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- **Unitary completion**: a matrix with orthogonal columns, `MᴴM = diag d`, is a unitary
times `diag √d`. -/
theorem exists_mem_unitaryGroup_eq_mul_diagonal {M : Matrix n n 𝕜} {d : n → ℝ}
    (hM : Mᴴ * M = diagonal (RCLike.ofReal ∘ d)) :
    ∃ V ∈ unitaryGroup n 𝕜, M = V * diagonal (fun j ↦ (√(d j) : 𝕜)) := by
  let c : n → EuclideanSpace 𝕜 n := fun j ↦ WithLp.toLp 2 (Mᵀ j)
  have hc (i j : n) : ⟪c i, c j⟫_𝕜 = if i = j then (d i : 𝕜) else 0 := by
    simp [c, inner_matrix_col_col, hM, diagonal_apply]
  have hd (j : n) : d j = ‖c j‖ ^ 2 :=
    mod_cast ((hc j j).trans (if_pos rfl)).symm.trans (inner_self_eq_norm_sq_to_K _)
  let u : n → EuclideanSpace 𝕜 n := fun j ↦ ((√(d j) : 𝕜))⁻¹ • c j
  have hu : Orthonormal 𝕜 ({j | d j ≠ 0}.domRestrict u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.domRestrict_apply, u, inner_smul_left, inner_smul_right, hc, Subtype.mk.injEq]
    split_ifs <;> simp_all [field]
  obtain ⟨b, hb⟩ := hu.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨_, (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  ext i j
  by_cases hj : d j = 0
  · have : c j = 0 := by simp_all
    simpa [hj, c] using congr(($this).ofLp i)
  · simp_all [Module.Basis.toMatrix_apply, u, c, field]

/-- **The trace norm is attained**: some unitary `U` has `tr(U A) = ‖A‖₁`. -/
theorem exists_mem_unitaryGroup_trace_mul_eq_traceNorm (A : Matrix n n 𝕜) :
    ∃ U ∈ unitaryGroup n 𝕜, (U * A).trace = A.traceNorm := by
  have hA := posSemidef_conjTranspose_mul_self A
  let Q := hA.isHermitian.eigenvectorUnitary
  obtain ⟨V, hV, hAQ⟩ := exists_mem_unitaryGroup_eq_mul_diagonal (M := A * Q.1)
    (d := hA.isHermitian.eigenvalues) (by
      simpa [mul_assoc, star_eq_conjTranspose] using
        hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary)
  refine ⟨Q.1 * star V, mul_mem Q.2 (Unitary.star_mem hV), ?_⟩
  simp [mul_assoc, trace_mul_comm, hAQ, Matrix.traceNorm, re_trace_cfcSqrt hA,
    Unitary.star_mul_self_of_mem hV]

end Arealaw
