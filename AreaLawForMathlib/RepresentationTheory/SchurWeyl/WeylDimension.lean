/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.SchurLabelEstimates
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.WeylRecursion
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.JucysRecursion

/-!
# The Weyl dimension formula for the multiplicity spaces

Extends `Mathlib/RepresentationTheory/Character.lean`.

`m_λ = ∏_{i<j} (l_i - l_j)/(j - i)` (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, equation `replicas:dimensions`).

Ported from `LionSR/QICLean`, `QICLean/Representation/WeylDimension.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/

open Finset Matrix PermutationRepresentation

namespace TensorPower

variable {q m k : ℕ}

/-- The scalar `s_λ = k! m_λ / d_λ` of the fixed-point sum on the label `λ`. -/
noncomputable def fixScalar (q : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) : ℂ :=
  (k.factorial : ℂ) * multiplicity (copyPerm (Fin q) k) l / l.dim

theorem fixSum_eq_sum : fixSum q k = ∑ l, fixScalar q l • IrrepLabel.centralIdem l := by
  rw [fixSum_eq_characterSum, characterSum_eq, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem fixSum_mul_centralIdem (l : IrrepLabel (Equiv.Perm (Fin k))) :
    fixSum q k * IrrepLabel.centralIdem l = fixScalar q l • IrrepLabel.centralIdem l := by
  rw [fixSum_eq_sum, sum_mul, sum_eq_single l]
  · rw [smul_mul_assoc, IrrepLabel.centralIdem_mul_self]
  · intro μ _ hμ; rw [smul_mul_assoc, IrrepLabel.centralIdem_mul_centralIdem_of_ne hμ, smul_zero]
  · simp

/-- On a branch `ν = λ - e_i`, `s_λ = (q + λ_i - 1 - i) s_ν`. -/
theorem fixScalar_eq_of_branch {l : IrrepLabel (Equiv.Perm (Fin (m + 1)))}
    {n : IrrepLabel (Equiv.Perm (Fin m))} {i : ℕ}
    (h : labelPart l = Function.update (labelPart n) i (labelPart n i + 1)) :
    fixScalar q l = ((q : ℂ) + labelPart l i - 1 - i) * fixScalar q n := by
  set P := IrrepLabel.centralIdem l *
    IrrepLabel.restrictHom (firstCopies m) (IrrepLabel.centralIdem n)
  have hP : P ≠ 0 := fun h0 => by
    have hb := congrArg (IrrepLabel.block l) h0
    rw [IrrepLabel.block_centralIdem_mul, if_pos rfl] at hb
    simp only [IrrepLabel.block, map_zero, Pi.zero_apply] at hb
    exact (block_restrict_centralIdem_eq_zero_iff l n).mp hb ⟨i, h⟩
  have h1 : fixSum q (m + 1) * P = fixScalar q l • P := by
    rw [← mul_assoc, fixSum_mul_centralIdem, smul_mul_assoc]
  have h2 : fixSum q (m + 1) * P = (((q : ℂ) + labelPart l i - 1 - i) * fixScalar q n) • P := by
    rw [fixSum_succ, mul_assoc]
    have e1 : IrrepLabel.restrictHom (firstCopies m) (fixSum q m) * P =
        fixScalar q n • P := by
      rw [← mul_assoc, ← IrrepLabel.centralIdem_mul_comm l, mul_assoc, ← map_mul,
        fixSum_mul_centralIdem, map_smul, mul_smul_comm]
    rw [e1, mul_smul_comm, add_mul, smul_mul_assoc, one_mul,
      IrrepLabel.starElement_mul_centralIdem_mul, casimir_sub_casimir h, ← add_smul, smul_smul]
    congr 1
    ring
  exact smul_left_injective ℂ hP (h1.symm.trans h2)

/-- **The Weyl dimension formula** (`05-replicas.tex`, Lemma 6.1(1), equation
`replicas:dimensions`): for a label `λ` of `S_k` with at most `q` rows, the multiplicity
`m_λ = dim V^{(q)}_λ` of `λ` in `(ℂ^q)^{⊗k}` is `∏_{i<j} (l_i - l_j)/(j - i)` with
`l_i = λ_i + q - 1 - i`. -/
theorem multiplicity_eq_weylFormula : ∀ {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))),
    (∀ a, q ≤ a → labelPart l a = 0) →
      (multiplicity (copyPerm (Fin q) k) l : ℝ) = Partition.weylFormula (part q l)
  | 0, l, hrows => by
    have hpart : part q l = 0 := funext fun a => labelPart_of_le l (Nat.zero_le _)
    rw [hpart, Partition.weylFormula_zero]
    have htr := trace_groupAlgebraRep (copyPerm (Fin q) 0) 1
    simp only [map_one, Matrix.trace_one, IrrepLabel.block, Pi.one_apply, Fintype.card_fin,
      Fintype.card_pi, prod_const, card_univ, pow_zero] at htr
    have hd : l.dim = 1 := by
      exact_mod_cast (dim_eq_hookFormula l).trans
        (by simp [Partition.hookFormula, Partition.rowPairs] : Partition.hookFormula (part 0 l) = 1)
    have h'' : ∑ l', l'.dim * multiplicity (copyPerm (Fin q) 0) l' = 1 := by
      exact_mod_cast htr.symm
    have hle : l.dim * multiplicity (copyPerm (Fin q) 0) l ≤ 1 := by
      rw [← h'']
      exact single_le_sum (f := fun l' => l'.dim * multiplicity (copyPerm (Fin q) 0) l')
        (fun _ _ => Nat.zero_le _) (mem_univ l)
    have hm : multiplicity (copyPerm (Fin q) 0) l ≠ 0 := fun h0 =>
      ((multSpace_ne_bot_iff l).mpr fun i hi => by simpa [labelPart, i.2] using hrows i hi)
        (Submodule.finrank_eq_zero.mp h0)
    rw [hd, one_mul] at hle
    rw [show multiplicity (copyPerm (Fin q) 0) l = 1 by omega]; simp
  | m + 1, l, hrows => by
    obtain ⟨n, hn⟩ : ∃ n, IrrepLabel.branchMult (firstCopies m) l n ≠ 0 := by
      by_contra! hall
      have := IrrepLabel.dim_eq_sum_branchMult (firstCopies m) l
      rw [sum_eq_zero fun n _ => by rw [hall n, zero_mul]] at this
      exact l.dim_pos.ne' this
    obtain ⟨i, h⟩ := exists_branch l n hn
    have hli : labelPart l i = labelPart n i + 1 := by rw [h, Function.update_self]
    have hi : i < q := by
      by_contra hiq
      rw [hrows i (not_lt.mp hiq)] at hli
      omega
    have hrowsn : ∀ a, q ≤ a → labelPart n a = 0 := fun a ha => by
      have := hrows a ha
      rwa [h, Function.update_of_ne (by omega : a ≠ i)] at this
    have ih := multiplicity_eq_weylFormula n hrowsn
    have hs := fixScalar_eq_of_branch (q := q) h
    simp only [fixScalar] at hs
    have hdd := dim_div_dim_eq h hrows hi
    set p := part q n
    set i' : Fin q := ⟨i, hi⟩
    have hpl : part q l = Function.update p i' (p i' + 1) := by
      funext a
      by_cases ha : a = i'
      · subst ha; simp [p, part, i', hli]
      · have ha' : (a : ℕ) ≠ i := fun e => ha (Fin.ext e)
        simp [p, part, Function.update_of_ne ha, h, Function.update_of_ne ha']
    have hW := Partition.weylFormula_update_add_mul p i'
    rw [← hpl] at hW
    have hshift : ∀ j, (Partition.shiftedPart (part q l) j : ℝ) =
        Function.update (fun j => (Partition.shiftedPart p j : ℝ)) i'
          ((Partition.shiftedPart p i' : ℝ) + 1) j := fun j => by
      rw [hpl, Partition.shiftedPart_update]
      by_cases hj : j = i'
      · subst hj; simp [Partition.shiftedPart]; ring
      · simp [hj]
    set A := ∏ j ∈ univ.erase i', ((Partition.shiftedPart p i' : ℝ) - Partition.shiftedPart p j)
    set B := ∏ j ∈ univ.erase i',
      ((Partition.shiftedPart p i' : ℝ) + 1 - Partition.shiftedPart p j)
    have hA : ∏ j ∈ univ.erase i', ((Partition.shiftedPart (part q l) i' : ℝ) - 1 -
        Partition.shiftedPart (part q l) j) = A := prod_congr rfl fun j hj => by
      rw [hshift, hshift, Function.update_self, Function.update_of_ne (mem_erase.mp hj).1]; ring
    have hB : ∏ j ∈ univ.erase i', ((Partition.shiftedPart (part q l) i' : ℝ) -
        Partition.shiftedPart (part q l) j) = B := prod_congr rfl fun j hj => by
      rw [hshift, hshift, Function.update_self, Function.update_of_ne (mem_erase.mp hj).1]
    rw [prod_div_distrib, hA, hB] at hdd
    have hLval : (Partition.shiftedPart (part q l) i' : ℝ) = q + labelPart l i - 1 - i := by
      simp only [Partition.shiftedPart, part, i']
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    have hpn : Antitone p := fun a b hab => labelPart_antitone n hab
    have hinjn := Partition.shiftedPart_injective hpn
    have hpl' : Antitone (part q l) := fun a b hab => labelPart_antitone l hab
    have hinjl := Partition.shiftedPart_injective hpl'
    have hA0 : A ≠ 0 := prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr fun e => (mem_erase.mp hj).1 (hinjn e).symm
    have hB0 : B ≠ 0 := hB ▸ prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr fun e => (mem_erase.mp hj).1 (hinjl e).symm
    have hdl : (l.dim : ℝ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
    have hdn : (n.dim : ℝ) ≠ 0 := by exact_mod_cast n.dim_pos.ne'
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have E1 : ((m + 1).factorial : ℝ) * multiplicity (copyPerm (Fin q) (m + 1)) l * n.dim =
        ((q : ℝ) + labelPart l i - 1 - i) * m.factorial *
          multiplicity (copyPerm (Fin q) m) n * l.dim := by
      have hs'' : ((m + 1).factorial : ℝ) * multiplicity (copyPerm (Fin q) (m + 1)) l / l.dim =
          ((q : ℝ) + labelPart l i - 1 - i) *
            (m.factorial * multiplicity (copyPerm (Fin q) m) n / n.dim) := by
        apply Complex.ofReal_injective; push_cast; rw [hs]
      field_simp at hs''
      linear_combination hs''
    have E2 : (n.dim : ℝ) * ((m + 1 : ℕ) : ℝ) * B =
        l.dim * (Partition.shiftedPart (part q l) i' : ℝ) * A := by
      field_simp at hdd
      linear_combination hdd
    rw [hLval] at E2
    have E5 : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have key : (((m + 1).factorial : ℝ) * n.dim * A) *
        ((multiplicity (copyPerm (Fin q) (m + 1)) l : ℝ) - Partition.weylFormula (part q l)) =
        0 := by
      push_cast at E2 E5 ⊢
      linear_combination A * E1 - (m.factorial : ℝ) * (multiplicity (copyPerm (Fin q) m) n) * E2
        - (n.dim : ℝ) * A * Partition.weylFormula (part q l) * E5
        - ((m : ℝ) + 1) * m.factorial * n.dim * hW
        + ((m : ℝ) + 1) * m.factorial * n.dim * B * ih
    have hK : ((m + 1).factorial : ℝ) * n.dim * A ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by positivity) hdn) hA0
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hK)

end TensorPower
