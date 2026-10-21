import AreaLawForMathlib.RepresentationTheory.SchurWeyl.TensorPowerAction
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# §6 Symmetric replicas: systems, copies and Schur labels (D6.1, D6.3)

Digest `digest/06-replicas.md` §6.0, paper `paper/sections/05-replicas.tex` lines 13–77.

The system `𝒱 = ⨂_{f : I} ℂ^{ι f}` has an arbitrary finite set `I` of tensor factors (site
type `I`; a region `Reg loc V` of §2 is the case `I = V`, `ι = loc`). Basis vectors of
`𝒱^{⊗k}` are `Config ι k = Fin k → (f : I) → ι f`. The Schur labels `λ ⊢ k` are the
irreducible-representation labels `IrrepLabel (Equiv.Perm (Fin k))` of `S_k`; their
identification with partitions is Schur–Weyl duality (D6.2).
-/

namespace AreaLaw.Replicas

open Matrix MonoidAlgebra PermutationRepresentation
open scoped ComplexOrder

variable {I : Type*} [DecidableEq I] (ι : I → Type*) (k : ℕ)

/-! ## D6.1 Systems, symmetric subspaces, subsystems -/

/-- D6.1. The basis configurations of `𝒱^{⊗k}`, `𝒱 = ⨂_{f : I} ℂ^{ι f}`. -/
abbrev Config := TensorPower.Config k ι

/-- D6.1. The permutation of the `k` copies of the subsystem `Q`, fixing the other factors;
its permutation operator is `U_Q(π)`. -/
abbrev copyPerm (Q : Finset I) : Equiv.Perm (Fin k) →* Equiv.Perm (Config ι k) :=
  TensorPower.subsystemPerm k ι Q

@[simp]
theorem copyPerm_apply (Q : Finset I) (π : Equiv.Perm (Fin k)) (x : Config ι k) (j : Fin k)
    (f : I) : copyPerm ι k Q π x j f = if f ∈ Q then x (π⁻¹ j) f else x j f := rfl

theorem commute_copyPerm_of_disjoint {Q Q' : Finset I} (h : Disjoint Q Q')
    (π π' : Equiv.Perm (Fin k)) : Commute (copyPerm ι k Q π) (copyPerm ι k Q' π') :=
  TensorPower.commute_subsystemPerm_of_disjoint k ι h π π'

theorem copyPerm_union {Q Q' : Finset I} (h : Disjoint Q Q') (π : Equiv.Perm (Fin k)) :
    copyPerm ι k (Q ∪ Q') π = copyPerm ι k Q π * copyPerm ι k Q' π :=
  TensorPower.subsystemPerm_union k ι h π

variable [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- D6.1. `U_Q(π)` permutes the `k` copies of `Q`; operators on `Q^{⊗k}` are extended by
the identity. -/
noncomputable def U (Q : Finset I) (π : Equiv.Perm (Fin k)) :
    Matrix (Config ι k) (Config ι k) ℂ :=
  permOp (copyPerm ι k Q) π

/-- D6.1. `U(π) = U_𝒱(π)` permutes whole copies, and `U(π) = U_Q(π) U_{Q^c}(π)`. -/
theorem U_univ_eq_mul (Q : Finset I) (π : Equiv.Perm (Fin k)) :
    U ι k Finset.univ π = U ι k Q π * U ι k Qᶜ π := by
  rw [U, U, U, permOp_apply, permOp_apply, permOp_apply, ← Finset.union_compl Q,
    copyPerm_union ι k disjoint_compl_right, _root_.mul_inv_rev, permMatrix_mul]

/-- D6.1. The symmetric subspace `𝒮_k = Sym^k 𝒱`. -/
noncomputable def S : Submodule ℂ (Config ι k → ℂ) := invariantSubspace (copyPerm ι k .univ)

/-- D6.1. The orthogonal projector `Π_k = (k!)⁻¹ ∑_π U(π)` onto `𝒮_k`. -/
noncomputable def projS : Matrix (Config ι k) (Config ι k) ℂ := symProj (copyPerm ι k .univ)

/-- D6.1. `D_k = dim 𝒮_k`. -/
noncomputable def D : ℕ := Module.finrank ℂ (S ι k)

/-! ## D6.3 Label projectors and the label observable -/

/-- D6.3. The label projector `π^λ_{Q,k}` onto the `[λ] ⊗ V_λ` block of `Q^{⊗k}`, the image
of the central idempotent of the label `λ` of `S_k`. -/
noncomputable def π (Q : Finset I) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Matrix (Config ι k) (Config ι k) ℂ :=
  labelProj (copyPerm ι k Q) l

/-- D6.3. `F_{Q,k} = ∑_{λ ⊢ k} (log d_λ) π^λ_{Q,k}`. -/
noncomputable def F (Q : Finset I) : Matrix (Config ι k) (Config ι k) ℂ :=
  labelObservable (copyPerm ι k Q) fun l => Real.log l.dim

/-- D6.3. `F_{Q,k}` is self-adjoint. -/
theorem isHermitian_F (Q : Finset I) : (F ι k Q).IsHermitian :=
  isHermitian_labelObservable _ _

/-- D6.3. `F_{Q,k} ≥ 0`, since `d_λ ≥ 1`. -/
theorem posSemidef_F (Q : Finset I) : (F ι k Q).PosSemidef := by
  refine Finset.sum_induction _ PosSemidef (fun _ _ ha hb => ha.add hb) PosSemidef.zero
    fun l _ => (posSemidef_labelProj _ l).smul ?_
  exact_mod_cast Real.log_nonneg (by exact_mod_cast l.dim_pos)

/-- D6.3. `F_{Q,0} = 0`. -/
theorem F_zero (Q : Finset I) : F ι 0 Q = 0 := by
  simp [F, labelObservable, IrrepLabel.dim_eq_one]

end AreaLaw.Replicas
