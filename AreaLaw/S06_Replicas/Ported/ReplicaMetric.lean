/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.Analysis.Matrix.OrthogonalResolutionCfc
import AreaLaw.S06_Replicas.Ported.ReplicaWeight
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.SubsystemTransport
import AreaLaw.S06_Replicas.Ported.SchurSurprisal
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.SchurLabelCommutation

/-!
# The replica metrics

`W_{Q,k} = ∑_λ w_k(λ) π^λ_{Q,k}`: positivity, centrality, `W_{Q,0} = I` and the comparison
`poly(k)⁻¹ e^{-t F_{Q,k}} ≤ W_{Q,k} ≤ poly(k) e^{-t F_{Q,k}}` (`05-replicas.tex`, Lemma 6.2).

Ported from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
`QICLean/Representation/ReplicaMetric.lean`.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

/-- A label observable is the image of a central element of the group algebra. -/
theorem labelObservable_eq_groupAlgebraRep (φ : G →* Equiv.Perm X) (f : IrrepLabel G → ℝ) :
    labelObservable φ f = groupAlgebraRep φ (∑ l, (f l : ℂ) • IrrepLabel.centralIdem l) := by
  rw [labelObservable, map_sum]
  simp only [map_smul, labelProj]

omit [Fintype X] [DecidableEq X] in
theorem sum_smul_centralIdem_mem_center (f : IrrepLabel G → ℝ) :
    ∑ l, (f l : ℂ) • IrrepLabel.centralIdem l ∈
      Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  Subalgebra.sum_mem _ fun l _ =>
    Subalgebra.smul_mem _ (IrrepLabel.centralIdem_mem_center l) _

end PermutationRepresentation

namespace TensorPower

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-- The dimension `d = dim V` of the whole one-copy system. -/
abbrev replicaDim : ℕ := Fintype.card ((f : F) → ι f)

/-- The common label function `w_k(λ)`, with `λ` padded to the full dimension `d`
(`05-replicas.tex`, equation `replicas:w-definition`). -/
noncomputable def replicaLabelWeight (t : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) :
    ℝ :=
  Partition.replicaWeight t (part (replicaDim ι) l)

/-- The replica metric `W_{Q,k} = ∑_λ w_k(λ) π^λ_{Q,k}` (`05-replicas.tex`, equation
`replicas:w-definition`). -/
noncomputable def replicaMetric (t : ℝ) (k : ℕ) (Q : Finset F) :
    Matrix (Config k ι) (Config k ι) ℂ :=
  labelObservable (subsystemPerm k ι Q) (replicaLabelWeight ι t)

theorem replicaMetric_eq_hom (t : ℝ) (k : ℕ) (Q : Finset F) :
    replicaMetric ι t k Q = (isOrthogonalResolution_labelProj (subsystemPerm k ι Q)).hom
      fun l => (replicaLabelWeight ι t l : ℂ) :=
  labelObservable_eq_hom _ _

omit [∀ f, DecidableEq (ι f)] in
theorem replicaDim_pos [∀ f, Nonempty (ι f)] : 0 < replicaDim ι := Fintype.card_pos

omit [∀ f, DecidableEq (ι f)] in
theorem replicaLabelWeight_pos [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (l : IrrepLabel (Equiv.Perm (Fin k))) : 0 < replicaLabelWeight ι t l :=
  Partition.replicaWeight_pos (replicaDim_pos ι) ht _

/-- **Lemma 6.2, positivity** (`05-replicas.tex`, line 306): `W_{Q,k}` is positive
definite. -/
theorem posDef_replicaMetric [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (Q : Finset F) : (replicaMetric ι t k Q).PosDef := by
  set hP := isOrthogonalResolution_labelProj (subsystemPerm k ι Q)
  set w := replicaLabelWeight (k := k) ι t
  have hne : (Finset.univ : Finset (IrrepLabel (Equiv.Perm (Fin k)))).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := IrrepLabel.sum_centralIdem (G := Equiv.Perm (Fin k))
    rw [h, Finset.sum_empty] at this
    exact zero_ne_one this
  set m := Finset.univ.inf' hne w
  have hm : 0 < m := (Finset.lt_inf'_iff hne).mpr fun l _ => replicaLabelWeight_pos ι ht l
  have hsplit : replicaMetric ι t k Q =
      (m : ℂ) • 1 + hP.hom fun l => ((w l - m : ℝ) : ℂ) := by
    rw [replicaMetric_eq_hom, ← hP.hom_const, ← map_add]
    congr 1
    ext l
    simp [w]
  rw [hsplit]
  refine (PosDef.one.smul (by exact_mod_cast hm)).add_posSemidef ?_
  exact hP.posSemidef_hom (isHermitian_labelProj _) fun l =>
    sub_nonneg.mpr (Finset.inf'_le _ (Finset.mem_univ l))

/-- `W_{Q,0} = I` (`05-replicas.tex`, line 299). -/
theorem replicaMetric_zero [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (Q : Finset F) :
    replicaMetric ι t 0 Q = 1 := by
  have hw : ∀ l : IrrepLabel (Equiv.Perm (Fin 0)), replicaLabelWeight ι t l = 1 := by
    intro l
    have : part (replicaDim ι) l = 0 := by
      funext a
      simp [labelPart]
    rw [replicaLabelWeight, this, Partition.replicaWeight_zero (replicaDim_pos ι) ht]
  simp only [replicaMetric, labelObservable, hw, Complex.ofReal_one, one_smul]
  exact sum_labelProj _

/-- **Lemma 6.2, centrality** (`05-replicas.tex`, line 306): `W_{Q,k}` commutes with the copy
permutations of `Q`. -/
theorem commute_replicaMetric_permOp (t : ℝ) (k : ℕ) (Q : Finset F) (σ : Equiv.Perm (Fin k)) :
    Commute (replicaMetric ι t k Q) (permOp (subsystemPerm k ι Q) σ) :=
  Commute.sum_left _ _ _ fun l _ => (commute_labelProj_permOp _ l σ).smul_left _

/-- The labelwise comparison behind `replicas:W-comparison`: for a label occurring on a
subsystem, `|log w_k(λ) + t log d_λ| ≤ C log(k + 2)` with `C` depending only on `d` and `t`. -/
theorem exists_abs_log_replicaLabelWeight_add_le [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 < t) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (Q : Finset F) (l : IrrepLabel (Equiv.Perm (Fin k))),
      labelProj (subsystemPerm k ι Q) l ≠ 0 →
        |Real.log (replicaLabelWeight ι t l) + t * Real.log l.dim| ≤
          C * Real.log ((k : ℝ) + 2) := by
  set d := replicaDim ι
  obtain ⟨C₁, hC₁⟩ := Partition.exists_abs_log_replicaWeight_add_le (replicaDim_pos ι) ht
  set C₂ : ℝ := (d ^ 2 + d + 1) * ((Real.log (d + 2) + 1) / Real.log 2 + 1)
  have hC₂ : 0 ≤ C₂ := by
    have : 0 ≤ Real.log ((d : ℝ) + 2) := Real.log_nonneg (by linarith [(d.cast_nonneg : (0:ℝ) ≤ d)])
    have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  refine ⟨|C₁| + t * C₂, by positivity, fun k Q l hl => ?_⟩
  have hrows : ∀ a, d ≤ a → labelPart l a = 0 := fun a ha =>
    labelPart_eq_zero_of_subsystemPerm ι k Q hl a ((card_subConfig_le ι Q).trans ha)
  have hsum : ∑ a : Fin d, part d l a = k := sum_labelPart_of_rows l hrows
  have hdim : (l.dim : ℝ) = Partition.hookFormula (part d l) := dim_eq_hookFormula_of_rows l hrows
  have hanti : Antitone (part d l) := fun a b hab => labelPart_antitone l hab
  have h1 := hC₁ (part d l)
  have h2 := Partition.abs_log_hookFormula_sub_le_mul_log hanti
  rw [hsum] at h1 h2
  rw [← hdim] at h2
  have hL : 0 ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_nonneg (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have h3 : |t * (Real.log l.dim - Partition.entropyTerm (part d l))| ≤
      t * (C₂ * Real.log ((k : ℝ) + 2)) := by
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left h2 ht.le
  have hid : Real.log (replicaLabelWeight ι t l) + t * Real.log l.dim =
      (Real.log (Partition.replicaWeight t (part d l)) + t * Partition.entropyTerm (part d l)) +
        t * (Real.log l.dim - Partition.entropyTerm (part d l)) := by
    rw [replicaLabelWeight]; ring
  rw [hid]
  calc _ ≤ |Real.log (Partition.replicaWeight t (part d l)) + t * Partition.entropyTerm (part d l)|
        + |t * (Real.log l.dim - Partition.entropyTerm (part d l))| := abs_add_le _ _
    _ ≤ |C₁| * Real.log ((k : ℝ) + 2) + t * (C₂ * Real.log ((k : ℝ) + 2)) :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hL)) h3
    _ = (|C₁| + t * C₂) * Real.log ((k : ℝ) + 2) := by ring


/-- Lemma 6.2, equation `replicas:W-comparison`:
`(k + 2)^{-C} e^{-t F_{Q,k}} ≤ W_{Q,k} ≤ (k + 2)^C e^{-t F_{Q,k}}`. -/
theorem exists_replicaMetric_comparison [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, ∀ (k : ℕ) (Q : Finset F),
      ((((k : ℝ) + 2) ^ (-C) : ℝ) : ℂ) •
          cfc (fun x => Real.exp (-t * x)) (labelEntropy (subsystemPerm k ι Q)) ≤
        replicaMetric ι t k Q ∧
      replicaMetric ι t k Q ≤
        ((((k : ℝ) + 2) ^ C : ℝ) : ℂ) •
          cfc (fun x => Real.exp (-t * x)) (labelEntropy (subsystemPerm k ι Q)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨C, fun k Q => ?_⟩
  set hP := isOrthogonalResolution_labelProj (subsystemPerm k ι Q)
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hE : cfc (fun x => Real.exp (-t * x)) (labelEntropy (subsystemPerm k ι Q)) =
      hP.hom fun l => (Real.exp (-t * Real.log l.dim) : ℂ) := by
    rw [labelEntropy, labelObservable_eq_hom,
      IsOrthogonalResolution.cfc_hom _ (isHermitian_labelProj _)]
  have hsmul : ∀ (c : ℝ) (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ),
      (c : ℂ) • hP.hom (fun l => (g l : ℂ)) = hP.hom fun l => ((c * g l : ℝ) : ℂ) := by
    intro c g
    rw [← map_smul]
    congr 1
    ext l
    simp
  rw [hE, replicaMetric_eq_hom, hsmul, hsmul]
  have hlab : ∀ l, labelProj (subsystemPerm k ι Q) l ≠ 0 →
      ((k : ℝ) + 2) ^ (-C) * Real.exp (-t * Real.log l.dim) ≤ replicaLabelWeight ι t l ∧
        replicaLabelWeight ι t l ≤ ((k : ℝ) + 2) ^ C * Real.exp (-t * Real.log l.dim) := by
    intro l hl
    have hw := replicaLabelWeight_pos ι ht.le l
    have h := abs_le.mp (hC k Q l hl)
    rw [Real.rpow_def_of_pos hk2, Real.rpow_def_of_pos hk2, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_log hw, Real.exp_le_exp, Real.exp_le_exp]
    constructor <;> nlinarith
  have key (f g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ)
      (h : ∀ l, labelProj (subsystemPerm k ι Q) l ≠ 0 → g l ≤ f l) :
      (hP.hom fun l => (g l : ℂ)) ≤ hP.hom fun l => (f l : ℂ) := by
    rw [Matrix.le_iff, ← map_sub]
    rw [show (fun l => (f l : ℂ)) - (fun l => (g l : ℂ)) = fun l => ((f l - g l : ℝ) : ℂ) by
      ext l; simp]
    exact hP.posSemidef_hom_of_ne_zero (isHermitian_labelProj _)
      (fun l hl => sub_nonneg.mpr (h l hl))
  exact ⟨key _ _ fun l hl => (hlab l hl).1, key _ _ fun l hl => (hlab l hl).2⟩

end TensorPower
