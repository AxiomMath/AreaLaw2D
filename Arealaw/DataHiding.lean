import Arealaw.OpNorm
import Arealaw.TraceNorm

/-!
# Data hiding

`lemma20`: an operator on `d ⊗ D` whose expectation against every product of contractions is at
most `c` has trace norm at most `d² c`, so an operator that product measurements barely detect
is small in trace norm.  The proof takes the unitary `M` maximizing `re (Tr[M L])`, whose maximum is
the trace norm, and expands it in the matrix units of the first factor,
`M = ∑ i, ∑ j, |i⟩⟨j| ⊗ Mᵢⱼ`; each block `Mᵢⱼ` is a contraction, so each of the `d²` terms is
one of the product expectations the hypothesis bounds.

## Implementation notes

The paper reads `‖Mᵢⱼ‖ ≤ 1` off the variational form of the operator norm, `‖X‖` being the
maximum of `⟨ψ|X|φ⟩` over unit vectors: restricting that maximum for `M` to the product vectors
`|i⟩ ⊗ |ψ'⟩` and `|j⟩ ⊗ |φ'⟩` leaves the maximum of `‖Mᵢⱼ‖`, which is therefore no larger.
Here the block `Mᵢⱼ` is the submatrix of `M` along the injections `Prod.mk i` and `Prod.mk j`,
so `Arealaw.l2_opNorm_submatrix_le` gives the bound.

The paper takes `M` anywhere in the unit ball with `Tr[M L] = ‖L‖₁`; Physlib supplies the
maximum over unitaries instead, so the `M` here is unitary and the trace it maximizes is a real
part.  `lemma20` is pinned to `ℂ` by that characterization, `Matrix.traceNorm_eq_max_re_tr_U`,
which Physlib states for complex matrices only; `Matrix.traceNorm` and the lemmas the proof uses
are `RCLike`-generic.

The paper also assumes `dim d ≤ dim D`; the proof never uses it, so `lemma20` drops it.
-/

namespace Arealaw

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

/-- A matrix on a product index type is the sum, over matrix units of the first factor, of
their Kronecker products with the corresponding blocks. -/
theorem sum_single_kronecker_submatrix {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m]
    [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix (m × p) (n × q) 𝕜) :
    ∑ i, ∑ j, single i j (1 : 𝕜) ⊗ₖ M.submatrix (Prod.mk i) (Prod.mk j) = M := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp [Matrix.sum_apply, single_apply, ite_and]

variable {d D : Type*} [Fintype d] [Fintype D] [DecidableEq d] [DecidableEq D]

/-- **Lemma 20** (data hiding): if every product of contractions has expectation at most `c`
against `L`, then `L` has trace norm at most `(dim d)² c`. -/
theorem lemma20 (L : Matrix (d × D) (d × D) ℂ) {c : ℝ}
    (hc : ∀ (X : Matrix d d ℂ) (Y : Matrix D D ℂ), ‖X‖ ≤ 1 → ‖Y‖ ≤ 1 →
      ‖((X ⊗ₖ Y) * L).trace‖ ≤ c) :
    L.traceNorm ≤ (Fintype.card d : ℝ) ^ 2 * c := by
  obtain ⟨M, hM⟩ := (Matrix.traceNorm_eq_max_re_tr_U L).1
  have hMnorm : ‖M.val‖ ≤ 1 :=
    l2_opNorm_le_one_of_mem_unitaryGroup (fun _ _ => Classical.propDecidable _) M.2
  calc L.traceNorm = Complex.re ((M.val * L).trace) := hM.symm
    _ = ∑ i, ∑ j, Complex.re
          (((single i j (1 : ℂ) ⊗ₖ M.val.submatrix (Prod.mk i) (Prod.mk j)) * L).trace) := by
        conv_lhs => rw [← sum_single_kronecker_submatrix M.val]
        simp [Finset.sum_mul]
    _ ≤ ∑ _i : d, ∑ _j : d, c := by
        gcongr with i _ j _
        refine (Complex.re_le_norm _).trans (hc _ _ ?_ ?_)
        · simp
        · exact (l2_opNorm_submatrix_le _ (Prod.mk_right_injective i)
            (Prod.mk_right_injective j)).trans hMnorm
    _ = (Fintype.card d : ℝ) ^ 2 * c := by simp [sq, mul_assoc]

end Arealaw
