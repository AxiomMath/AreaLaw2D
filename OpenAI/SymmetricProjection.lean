/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Extracted from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
`QICLean/Representation/CoherentSymbol.lean`.
-/
import OpenAI.TrivialLabel

/-!
# The symmetric projector

The averaging projector onto the copy-permutation invariant subspace is an
orthogonal projection.  This narrow file isolates the two facts needed by the
replica-transport metric, without importing the unrelated coherent-symbol and
injection-polynomial calculus.
-/

open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

/-- The symmetric projector is idempotent. -/
theorem symProj_mul_symProj :
    symProj (copyPerm Ω k) * symProj (copyPerm Ω k) = symProj (copyPerm Ω k) := by
  obtain ⟨l₀, hl₀⟩ := exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k)) (X := Fin k → Ω)
  rw [← hl₀, labelProj_mul_self]

/-- The symmetric projector is Hermitian. -/
theorem isHermitian_symProj : (symProj (copyPerm Ω k)).IsHermitian := by
  obtain ⟨l₀, hl₀⟩ := exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k)) (X := Fin k → Ω)
  rw [← hl₀]
  exact isHermitian_labelProj _ l₀

end TensorPower
