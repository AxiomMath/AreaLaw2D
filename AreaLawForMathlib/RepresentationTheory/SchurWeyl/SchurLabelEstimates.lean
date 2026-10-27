/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.BranchProbability

/-!
# Lemma 6.1, parts 1 and 6, on `(ℂ^q)^{⊗k}`

Extends `Mathlib/RepresentationTheory/Irreducible.lean`.

The labels are the partitions with at most `q` rows, with the dimension, entropy and branch
statements (*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`, lines
85–151).

Ported from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
`QICLean/Representation/SchurLabelEstimates.lean`.
-/

open Finset Matrix PermutationRepresentation

namespace TensorPower

variable {q k m : ℕ}

/-- A label occurring in `(ℂ^q)^{⊗k}` has at most `q` rows. -/
theorem labelPart_eq_zero_of_labelProj_ne_zero {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : labelProj (copyPerm (Fin q) k) l ≠ 0) : ∀ a, q ≤ a → labelPart l a = 0 := fun a ha => by
  rw [labelProj_ne_zero_iff] at hl
  simp only [labelPart]
  split_ifs with hak; exacts [hl ⟨a, hak⟩ ha, rfl]

end TensorPower
