/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
`QICLean/Representation/SchurLabelEstimates.lean`.
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.BranchProbability

/-!
# Lemma 6.1, parts 1 and 6, on `(ℂ^q)^{⊗k}`

This file assembles, for the copy permutations of `Q^{⊗k}` with `Q = ℂ^q`, the statements of
Lemma 6.1 (`lem:schur`) of the area-law paper (*A two-dimensional area law from a global
spectral gap*, `05-replicas.tex`, lines 85–151) that concern the identification of the
labels with partitions:

* part 1: the labels occurring in `Q^{⊗k}` are the partitions with at most `q` rows; for
  them `d_λ = k! ∏_{i<j}(l_i - l_j)/∏_i l_i!` with `l_i = λ_i + q - 1 - i` (rows indexed
  from `0`), and `|log d_λ - k H(λ/k)| ≤ (q² + q + 1)(log(k + q + 2) + 1)`;
* part 6: the full label `λ` and the first-`(k-1)` label `ν` are compatible precisely along
  the removable-row branches `ν = λ - e_i`; in any permutation-invariant state, conditional
  on `λ`, the branch has probability `d_ν / d_λ = (l_i/k) ∏_{j ≠ i} (l_i - 1 - l_j)/(l_i - l_j)
  ≤ 2^q l_i / k`; and the star operator has eigenvalue `(λ_i - 1 - i)/k` on the branch.

The remaining assertion of part 1, `dim V^{(q)}_λ = ∏_{i<j} (l_i - l_j)/(j - i)`, is
`TensorPower.schur_multiplicity_eq_weylFormula`; the polynomial bounds on the number of
labels and on the total multiplicity are `TensorPower.card_labelProj_ne_zero_le` and
`TensorPower.sum_multiplicity_le`.

## Main declarations

* `TensorPower.labelPart_eq_zero_of_labelProj_ne_zero` — at most `q` rows.
* `TensorPower.schur_dim_eq_hookFormula`, `TensorPower.schur_abs_log_dim_sub_le`.
* `TensorPower.schur_branch_compatible_iff`, `TensorPower.schur_branch_probability`,
  `TensorPower.schur_starOp_eigenvalue`.
-/

open Finset Matrix PermutationRepresentation

namespace TensorPower

variable {q k m : ℕ}

/-- A label occurring in `(ℂ^q)^{⊗k}` has at most `q` rows. -/
theorem labelPart_eq_zero_of_labelProj_ne_zero {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : labelProj (copyPerm (Fin q) k) l ≠ 0) : ∀ a, q ≤ a → labelPart l a = 0 := by
  intro a ha
  rw [labelProj_ne_zero_iff] at hl
  simp only [labelPart]
  split_ifs with hak
  · exact hl ⟨a, hak⟩ ha
  · rfl

end TensorPower
