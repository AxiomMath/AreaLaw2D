import Mathlib.Analysis.Matrix.Order
import AreaLawForMathlib.Analysis.Matrix.WeylTwirl

/-!
# A positive semidefinite matrix is dominated by its partial trace

Extends `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` / `Mathlib/Analysis/Matrix/Order.lean`:
for `M ≥ 0` on `S × C`, `M ≤ (dim C) • (Tr_C M ⊗ 1)` in the Loewner order. Proof: the
complementary Weyl twirl `d⁻² ∑_{a,b} (1 ⊗ W_{ab}) M (1 ⊗ W_{ab})*` equals `d⁻¹ Tr_C M ⊗ 1`
and contains the term `M` (`W_{00} = 1`).
-/

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder

variable {S C : Type*} [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
theorem weyl_zero_zero {d : ℕ} [NeZero d] (ζ : ℂ) : weyl (d := d) ζ 0 0 = 1 := by
  simp [weyl]

omit [Fintype C] in
theorem reindexedWeyl_zero_zero {d : ℕ} [NeZero d] (e : C ≃ ZMod d) (ζ : ℂ) :
    reindexedWeyl e ζ 0 0 = 1 := by
  simp [reindexedWeyl, weyl_zero_zero]

/-- `M ≤ (dim C) • (Tr_C M ⊗ 1)` for `M ≥ 0` on `S × C`. -/
theorem PosSemidef.le_smul_traceRight_kronecker_one [Finite S] {M : Matrix (S × C) (S × C) ℂ}
    (hM : M.PosSemidef) : M ≤ (Fintype.card C : ℂ) • (M.traceRight ⊗ₖ (1 : Matrix C C ℂ)) := by
  classical
  have := Fintype.ofFinite S
  rcases isEmpty_or_nonempty C with hC | hC
  · have : M = 0 := by ext ⟨_, c⟩; exact (IsEmpty.false c).elim
    simp [this]
  set d := Fintype.card C
  have : NeZero d := ⟨Fintype.card_ne_zero⟩
  let e : C ≃ ZMod d := (Fintype.equivFin C).trans (ZMod.finEquiv d).toEquiv
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / d)) d :=
    Complex.isPrimitiveRoot_exp _ (NeZero.ne d)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / d)
  have htw := complementaryWeylTwirl_eq_smul_traceRight_kronecker_one e hζ M
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hsum : (d : ℂ) • (M.traceRight ⊗ₖ (1 : Matrix C C ℂ)) =
      ∑ a : ZMod d, ∑ b : ZMod d, ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b) * M *
        ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b)ᴴ := by
    have h2 : ((d : ℂ) ^ 2) • complementaryWeylTwirl e ζ M = ∑ a : ZMod d, ∑ b : ZMod d,
        ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b) * M *
          ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b)ᴴ := by
      rw [complementaryWeylTwirl, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hd), one_smul]
    rw [← h2, htw, smul_kronecker, smul_smul, sq, mul_assoc, mul_inv_cancel₀ hd, mul_one]
  rw [hsum]
  have hnn : ∀ a b : ZMod d, 0 ≤ ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b) * M *
      ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b)ᴴ := fun a b =>
    (hM.mul_mul_conjTranspose_same _).nonneg
  calc M = ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ 0 0) * M *
        ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ 0 0)ᴴ := by
        simp [reindexedWeyl_zero_zero]
    _ ≤ ∑ b : ZMod d, ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ 0 b) * M *
        ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ 0 b)ᴴ :=
        Finset.single_le_sum (fun b _ => hnn 0 b) (Finset.mem_univ 0)
    _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b : ZMod d,
        ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b) * M *
          ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ a b)ᴴ)
        (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) (Finset.mem_univ 0)

end Matrix
