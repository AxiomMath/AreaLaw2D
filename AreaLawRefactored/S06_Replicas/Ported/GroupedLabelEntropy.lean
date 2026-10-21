/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.GroupedCopies
import AreaLawRefactored.S06_Replicas.Ported.SchurSurprisal

/-!
# Label observables under a split of the copies

The label entropies of a split of the copies satisfy
\(F_g + F_b \le F_w \le F_g + F_b + \log\binom{k}{r}\,I\) (Lemma 6.1(4), `05-replicas.tex`,
lines 116–123).
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

/-- Lemma 6.1(4): the subgroup label entropies bound the whole label entropy, with additive
error \(\log\binom{k}{r}\). -/
theorem groupedCopies_labelEntropy_bounds {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    {X : Type*} [Fintype X] [DecidableEq X] (φ : Equiv.Perm (Fin k) →* Equiv.Perm X) :
    labelEntropy (φ.comp (groupHom₁ e)) + labelEntropy (φ.comp (groupHom₂ e)) ≤
      labelEntropy φ ∧
    labelEntropy φ ≤ labelEntropy (φ.comp (groupHom₁ e)) +
      labelEntropy (φ.comp (groupHom₂ e)) + (Real.log (k.choose r) : ℂ) • 1 := by
  classical
  have hc : ∀ α β, Commute (labelProj (φ.comp (groupHom₁ e)) α)
      (labelProj (φ.comp (groupHom₂ e)) β) := fun α β =>
    commute_groupAlgebraRep_of_commute _ _ (comp_commute φ (groupHom_commute e)) _ _
  let hG := isOrthogonalResolution_labelProj (φ.comp (groupHom₁ e))
  let hB := isOrthogonalResolution_labelProj (φ.comp (groupHom₂ e))
  let hW := isOrthogonalResolution_labelProj φ
  let hGB := hG.prod hB hc
  have hcW : ∀ (p : IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin r)))
      (l : IrrepLabel (Equiv.Perm (Fin k))), Commute
      (labelProj (φ.comp (groupHom₁ e)) p.1 * labelProj (φ.comp (groupHom₂ e)) p.2)
      (labelProj φ l) := fun p l =>
    ((groupedCopies_commute e φ p.1 p.2 l).1).mul_left
      (groupedCopies_commute e φ p.1 p.2 l).2
  let R := hGB.prod hW hcW
  have hHerm : ∀ (p : (IrrepLabel (Equiv.Perm (Fin m)) ×
      IrrepLabel (Equiv.Perm (Fin r))) × IrrepLabel (Equiv.Perm (Fin k))),
      ((labelProj (φ.comp (groupHom₁ e)) p.1.1 *
      labelProj (φ.comp (groupHom₂ e)) p.1.2) * labelProj φ p.2).IsHermitian :=
    fun p => (((isHermitian_labelProj _ p.1.1).commute_iff
      (isHermitian_labelProj _ p.1.2)).mp (hc p.1.1 p.1.2)).commute_iff
        (isHermitian_labelProj _ p.2) |>.mp (hcW p.1 p.2)
  have hGood : R.hom (fun p => (Real.log p.1.1.dim : ℂ)) =
      labelEntropy (φ.comp (groupHom₁ e)) :=
    (hGB.prod_hom_fst hW R (fun p => (Real.log p.1.dim : ℂ))).trans
      ((hG.prod_hom_fst hB hGB (fun α => (Real.log α.dim : ℂ))).trans
        (labelObservable_eq_hom _ (fun α => Real.log α.dim)).symm)
  have hBad : R.hom (fun p => (Real.log p.1.2.dim : ℂ)) =
      labelEntropy (φ.comp (groupHom₂ e)) :=
    (hGB.prod_hom_fst hW R (fun p => (Real.log p.2.dim : ℂ))).trans
      ((hG.prod_hom_snd hB hGB (fun β => (Real.log β.dim : ℂ))).trans
        (labelObservable_eq_hom _ (fun β => Real.log β.dim)).symm)
  have hWhole : R.hom (fun p => (Real.log p.2.dim : ℂ)) = labelEntropy φ :=
    (hGB.prod_hom_snd hW R (fun l => (Real.log l.dim : ℂ))).trans
      (labelObservable_eq_hom _ (fun l => Real.log l.dim)).symm
  have hk : m + r = k := by simpa using Fintype.card_congr e
  have hchoose : (0 : ℝ) < k.choose r := mod_cast Nat.choose_pos (show r ≤ k by omega)
  have hLog : ∀ (p : (IrrepLabel (Equiv.Perm (Fin m)) ×
      IrrepLabel (Equiv.Perm (Fin r))) × IrrepLabel (Equiv.Perm (Fin k))),
      labelProj (φ.comp (groupHom₁ e)) p.1.1 *
        labelProj (φ.comp (groupHom₂ e)) p.1.2 * labelProj φ p.2 ≠ 0 →
      Real.log p.1.1.dim + Real.log p.1.2.dim ≤ Real.log p.2.dim ∧
      Real.log p.2.dim ≤ Real.log p.1.1.dim + Real.log p.1.2.dim +
        Real.log (k.choose r) := by
    intro p hp
    have hd := groupedCopies_dim e φ hp
    have ha : (0 : ℝ) < p.1.1.dim := Nat.cast_pos.mpr p.1.1.dim_pos
    have hb : (0 : ℝ) < p.1.2.dim := Nat.cast_pos.mpr p.1.2.dim_pos
    have hw : (0 : ℝ) < p.2.dim := Nat.cast_pos.mpr p.2.dim_pos
    constructor
    · simpa only [Real.log_mul ha.ne' hb.ne'] using Real.log_le_log (mul_pos ha hb)
        (show (p.1.1.dim : ℝ) * p.1.2.dim ≤ p.2.dim by exact_mod_cast hd.1)
    · simpa only [Real.log_mul hchoose.ne' (mul_pos ha hb).ne',
        Real.log_mul ha.ne' hb.ne', add_comm (Real.log (k.choose r))] using Real.log_le_log hw
          (show (p.2.dim : ℝ) ≤ (k.choose r : ℝ) * ((p.1.1.dim : ℝ) * p.1.2.dim)
            by exact_mod_cast hd.2)
  have hConst : R.hom (fun _ => (Real.log (k.choose r) : ℂ)) =
      (Real.log (k.choose r) : ℂ) • 1 := by
    rw [IsOrthogonalResolution.hom_apply, ← Finset.smul_sum, R.sum_eq]
  constructor
  · rw [Matrix.le_iff, ← hWhole, ← hGood, ← hBad, ← map_add, ← map_sub]
    simpa only [Pi.sub_def, Pi.add_def, Complex.ofReal_sub, Complex.ofReal_add] using
      R.posSemidef_hom_of_ne_zero hHerm
        (f := fun p => Real.log p.2.dim - (Real.log p.1.1.dim + Real.log p.1.2.dim))
        (fun p hp => sub_nonneg.mpr (hLog p hp).1)
  · rw [Matrix.le_iff, ← hWhole, ← hGood, ← hBad, ← hConst,
      ← map_add, ← map_add, ← map_sub]
    simpa only [Pi.sub_def, Pi.add_def, Complex.ofReal_sub, Complex.ofReal_add] using
      R.posSemidef_hom_of_ne_zero hHerm
        (f := fun p => Real.log p.1.1.dim + Real.log p.1.2.dim +
          Real.log (k.choose r) - Real.log p.2.dim)
        (fun p hp => sub_nonneg.mpr (hLog p hp).2)

end TensorPower
