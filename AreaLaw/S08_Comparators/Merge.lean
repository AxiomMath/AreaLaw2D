import AreaLaw.S08_Comparators.Components
import AreaLaw.S06_Replicas.Ported.MergeExponential
import AreaLawForMathlib.Analysis.MeanInequalitiesFinProd

/-!
# §8.4 Merge deficits, merge moments and the component inverse (D8.28–D8.30)

Digest `digest/08-comparators.md` D8.28–D8.30, paper `paper/sections/07-comparators.tex`
495–575. D8.28 and D8.29 are stated for an arbitrary finite family of tensor factors and an
arbitrary split of the copies; D8.30 for the system `𝒱` of §8 (no geometry).
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

set_option synthInstance.maxSize 256

/-! ## D8.28 Merge deficits and decomposition -/

section MergeGeneral

variable {I : Type*} [DecidableEq I] [Fintype I] (ι : I → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {k m : ℕ} (θ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin k))

/-- D8.28 (`comparator:merge-decomposition`). On the good group put `Q = XU_{j,g}`, `V = V_{j,g}`,
`Y = Y_{j,g}` and `D_C = F_Q + F_C - F_{QC}`, `D_R = F_V + F_R - F_{VR}`,
`G_phys = F_Q + F_V - F_Y`. All commute with `F_C, F_R` and each other; `D_C, D_R ≥ 0`; and
`G^good = G_phys + F_C + F_R - D_C - D_R`. Physical good copies lie in
`𝖩 = 𝟏_{[0,∞)}(G_phys)`; `𝖩` commutes with `D_C, D_R`. -/
theorem step_8_28 {Q V Y C R : Finset I} (hQC : Disjoint Q C) (hVR : Disjoint V R)
    (hQV : Disjoint Q V) (hY : Disjoint Y (Q ∪ V)) :
    labelEntropy ((Replicas.copyPerm ι k (Q ∪ C)).comp θ) +
        labelEntropy ((Replicas.copyPerm ι k (V ∪ R)).comp θ) -
        labelEntropy ((Replicas.copyPerm ι k Y).comp θ) =
      (labelEntropy ((Replicas.copyPerm ι k Q).comp θ) +
          labelEntropy ((Replicas.copyPerm ι k V).comp θ) -
          labelEntropy ((Replicas.copyPerm ι k Y).comp θ)) +
        labelEntropy ((Replicas.copyPerm ι k C).comp θ) +
        labelEntropy ((Replicas.copyPerm ι k R).comp θ) -
        (labelEntropy ((Replicas.copyPerm ι k Q).comp θ) +
          labelEntropy ((Replicas.copyPerm ι k C).comp θ) -
          labelEntropy ((Replicas.copyPerm ι k (Q ∪ C)).comp θ)) -
        (labelEntropy ((Replicas.copyPerm ι k V).comp θ) +
          labelEntropy ((Replicas.copyPerm ι k R).comp θ) -
          labelEntropy ((Replicas.copyPerm ι k (V ∪ R)).comp θ)) ∧
    (labelEntropy ((Replicas.copyPerm ι k Q).comp θ) +
        labelEntropy ((Replicas.copyPerm ι k C).comp θ) -
        labelEntropy ((Replicas.copyPerm ι k (Q ∪ C)).comp θ)).PosSemidef ∧
    (labelEntropy ((Replicas.copyPerm ι k V).comp θ) +
        labelEntropy ((Replicas.copyPerm ι k R).comp θ) -
        labelEntropy ((Replicas.copyPerm ι k (V ∪ R)).comp θ)).PosSemidef ∧
    ∀ w ∈ invariantSubspace ((Replicas.copyPerm ι k (Y ∪ (Q ∪ V))).comp θ),
      ∀ a b c : IrrepLabel (Equiv.Perm (Fin m)),
        (labelProj ((Replicas.copyPerm ι k Q).comp θ) a *
          labelProj ((Replicas.copyPerm ι k V).comp θ) b *
            labelProj ((Replicas.copyPerm ι k Y).comp θ) c) *ᵥ w ≠ 0 →
        c.dim ≤ a.dim * b.dim := by
  refine ⟨by abel, ?_, ?_, fun w hw a b c h => dim_le_mul_of_mulVec_ne_zero ι θ hQV hY hw h⟩
  -- D8.28.2
  · exact posSemidef_mergeDeficit
      (fun g h => TensorPower.commute_subsystemPerm_of_disjoint k ι hQC (θ g) (θ h))
      (fun g => TensorPower.subsystemPerm_union k ι hQC (θ g))
  · exact posSemidef_mergeDeficit
      (fun g h => TensorPower.commute_subsystemPerm_of_disjoint k ι hVR (θ g) (θ h))
      (fun g => TensorPower.subsystemPerm_union k ι hVR (θ g))

end MergeGeneral

/-! ## D8.29 Merge moments -/

section MergeMoments

variable {I : Type*} [DecidableEq I] [Fintype I] (ι : I → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)

/-- The merge-deficit exponential `e^{b D}` of `Q, C` on the first group of copies,
`D = F_Q + F_C - F_{QC}`, as a product of the three label functions. -/
noncomputable def mergeExp (Q C : Finset I) (b : ℝ) :
    Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  labelObservable ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₁ e))
      (fun l => Real.exp (b * Real.log l.dim)) *
    labelObservable ((Replicas.copyPerm ι k C).comp (TensorPower.groupHom₁ e))
      (fun l => Real.exp (b * Real.log l.dim)) *
    labelObservable ((Replicas.copyPerm ι k (Q ∪ C)).comp (TensorPower.groupHom₁ e))
      (fun l => Real.exp (-(b * Real.log l.dim)))

omit [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
private theorem subtype_eq_compl {S Q C : Finset I} (hS : S = Q ∪ C) (hQC : Disjoint Q C) :
    (Q.subtype (· ∈ S))ᶜ = C.subtype (· ∈ S) := by
  ext ⟨f, hf⟩
  simp only [Finset.mem_compl, Finset.mem_subtype]
  rw [hS, Finset.mem_union] at hf
  constructor
  · intro h; exact hf.resolve_left h
  · intro h hq; exact Finset.disjoint_left.mp hQC hq h

omit [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
private theorem subtype_self (S : Finset I) : S.subtype (· ∈ S) = Finset.univ := by
  ext ⟨f, hf⟩
  simp

/-- `Tr(A L(f) B) = ∑_λ f(λ) Tr(A π^λ B)` for a real label function. -/
private theorem re_trace_mul_labelObservable_mul {G X : Type*} [Group G] [Fintype G]
    [Fintype X] [DecidableEq X] (A B : Matrix X X ℂ) (φ : G →* Equiv.Perm X)
    (f : IrrepLabel G → ℝ) :
    (A * labelObservable φ f * B).trace.re = ∑ l, f l * (A * labelProj φ l * B).trace.re := by
  simp only [labelObservable, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    trace_sum, trace_smul, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul]

/-- `Tr(ρ L₁(f₁) L₂(f₂) L₃(f₃)) = ∑ f₁ f₂ f₃ Tr(ρ π π π)` for real label functions. -/
private theorem re_trace_mul_labelObservable₃ {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq X] (ρ : Matrix X X ℂ) (φ₁ φ₂ φ₃ : G →* Equiv.Perm X)
    (f₁ f₂ f₃ : IrrepLabel G → ℝ) :
    (ρ * (labelObservable φ₁ f₁ * labelObservable φ₂ f₂ * labelObservable φ₃ f₃)).trace.re =
      ∑ l, ∑ μ, ∑ ν, f₁ l * f₂ μ * f₃ ν *
        (ρ * (labelProj φ₁ l * labelProj φ₂ μ * labelProj φ₃ ν)).trace.re := by
  have e : ρ * (labelObservable φ₁ f₁ * labelObservable φ₂ f₂ * labelObservable φ₃ f₃) =
      ρ * labelObservable φ₁ f₁ * (labelObservable φ₂ f₂ * labelObservable φ₃ f₃) := by
    simp only [mul_assoc]
  rw [e, re_trace_mul_labelObservable_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e2 : ρ * labelProj φ₁ l * (labelObservable φ₂ f₂ * labelObservable φ₃ f₃) =
      ρ * labelProj φ₁ l * labelObservable φ₂ f₂ * labelObservable φ₃ f₃ := by
    simp only [mul_assoc]
  rw [e2, re_trace_mul_labelObservable_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← mul_one (ρ * labelProj φ₁ l * labelProj φ₂ μ * labelObservable φ₃ f₃),
    re_trace_mul_labelObservable_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [mul_one, mul_assoc]

/-- D8.29 (`comparator:merge-moments`). For `0 ≤ b ≤ 1`,
`E_{u_B/‖u_B‖} e^{b D_C} ≤ poly(k)`, `E_{u_B/‖u_B‖} e^{b D_R} ≤ poly(k)`. No iid hypothesis on the
auxiliary marginal.

Here for regions `Q, C` of the first group of copies of a vector `w` invariant under the
first-group permutations of `Q ∪ T₂` and of `C ∪ T₃` (`T₂, T₃` disjoint from `QC`):
`⟨w, e^{b D} w⟩ ≤ (m + 1)^{(dim 𝓗_{QC})²} ‖w‖²`. -/
theorem step_8_29 {Q C T₂ T₃ : Finset I} (hQC : Disjoint Q C) (h2 : Disjoint T₂ (Q ∪ C))
    (h3 : Disjoint T₃ (Q ∪ C)) {w : Replicas.Config ι k → ℂ}
    (hw₂ : w ∈ invariantSubspace ((Replicas.copyPerm ι k (Q ∪ T₂)).comp
      (TensorPower.groupHom₁ e)))
    (hw₃ : w ∈ invariantSubspace ((Replicas.copyPerm ι k (C ∪ T₃)).comp
      (TensorPower.groupHom₁ e)))
    {b : ℝ} (hb1 : b ≤ 1) :
    (star w ⬝ᵥ (mergeExp ι e Q C b *ᵥ w)).re ≤
      ((m + 1) ^ (Fintype.card (TensorPower.SubConfig ι (Q ∪ C)) ^ 2) : ℕ) *
        (star w ⬝ᵥ w).re := by
  classical
  set S := Q ∪ C with hS
  set Φ := TensorPower.goodSplit ι e S
  set ι' := fun f : {f // f ∈ S} => ι f
  set Q' := Q.subtype (· ∈ S)
  set C' := C.subtype (· ∈ S)
  have hQ' : ∀ l, reindex Φ Φ (labelProj ((Replicas.copyPerm ι k Q).comp
      (TensorPower.groupHom₁ e)) l) = labelProj (TensorPower.subsystemPerm m ι' Q') l ⊗ₖ
        (1 : Matrix _ _ ℂ) := fun l =>
    TensorPower.labelProj_goodSplit_eq ι e Finset.subset_union_left l
  have hC' : ∀ l, reindex Φ Φ (labelProj ((Replicas.copyPerm ι k C).comp
      (TensorPower.groupHom₁ e)) l) = labelProj (TensorPower.subsystemPerm m ι' C') l ⊗ₖ
        (1 : Matrix _ _ ℂ) := fun l =>
    TensorPower.labelProj_goodSplit_eq ι e Finset.subset_union_right l
  have hS' : ∀ l, reindex Φ Φ (labelProj ((Replicas.copyPerm ι k S).comp
      (TensorPower.groupHom₁ e)) l) =
        labelProj (TensorPower.copyPerm ((f : {f // f ∈ S}) → ι' f) m) l ⊗ₖ
        (1 : Matrix _ _ ℂ) := fun l => by
    rw [TensorPower.labelProj_goodSplit_eq ι e le_rfl l, subtype_self,
      TensorPower.subsystemPerm_univ]
  -- the operator `e^{b D}` acts on the first factor
  set M₁ := labelObservable (TensorPower.subsystemPerm m ι' Q')
      (fun l => Real.exp (b * Real.log l.dim)) *
    labelObservable (TensorPower.subsystemPerm m ι' C')
      (fun l => Real.exp (b * Real.log l.dim)) *
    labelObservable (TensorPower.copyPerm ((f : {f // f ∈ S}) → ι' f) m)
      (fun l => Real.exp (-(b * Real.log l.dim)))
  have hM : reindex Φ Φ (mergeExp ι e Q C b) = M₁ ⊗ₖ (1 : Matrix _ _ ℂ) := by
    rw [mergeExp, reindex_mul_reindex, reindex_mul_reindex, reindex_labelObservable_eq Φ hQ',
      reindex_labelObservable_eq Φ hC', reindex_labelObservable_eq Φ hS', ← mul_kronecker_mul,
      ← mul_kronecker_mul, one_mul, one_mul]
  rw [dotProduct_mulVec_eq_trace_reducedVec Φ w hM]
  set ρ := reducedVec Φ w
  have hρ : ρ.PosSemidef := posSemidef_reducedVec Φ w
  have htr : ρ.trace = star w ⬝ᵥ w := trace_reducedVec Φ w
  -- `ρ` is invariant under the copy permutations of `Q` and of `C` separately
  have hρQ : ∀ g, Commute (permOp (TensorPower.subsystemPerm m ι' Q') g) ρ := fun g =>
    commute_permOp_of_apply_eq _ g fun a a' => reducedVec_apply_perm Φ _ _
      (fun x z => TensorPower.goodSplit_apply_perm ι e Finset.subset_union_left h2 hw₂ g x z) a a'
  have hρC : ∀ g, Commute (permOp (TensorPower.subsystemPerm m ι' Q'ᶜ) g) ρ := by
    rw [subtype_eq_compl hS hQC]
    exact fun g => commute_permOp_of_apply_eq _ g fun a a' => reducedVec_apply_perm Φ _ _
      (fun x z => TensorPower.goodSplit_apply_perm ι e Finset.subset_union_right h3
        hw₃ g x z) a a'
  -- D8.29.1–D8.29.4: the merge moment of the reduced state
  have hnn : 0 ≤ star w ⬝ᵥ w := dotProduct_star_self_nonneg w
  have hreal : star w ⬝ᵥ w = ((star w ⬝ᵥ w).re : ℂ) :=
    Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hnn).2.symm)
  set t := (star w ⬝ᵥ w).re
  have ht0 : 0 ≤ t := (Complex.nonneg_iff.mp hnn).1
  rcases ht0.eq_or_lt with ht | ht
  · have hw0 : w = 0 := dotProduct_star_self_eq_zero.mp (by rw [hreal, ← ht, Complex.ofReal_zero])
    subst hw0
    have h0 : ρ = 0 := by ext a b; simp [ρ, reducedVec_apply]
    rw [h0, zero_mul, trace_zero, Complex.zero_re]
    exact mul_nonneg (by positivity) ht0
  set ρ' := ((t : ℂ)⁻¹) • ρ
  have hρ' : ρ'.PosSemidef := hρ.smul (by
    rw [← Complex.ofReal_inv]; exact_mod_cast (inv_pos.mpr ht).le)
  have htr' : ρ'.trace = 1 := by
    rw [trace_smul, htr, hreal, smul_eq_mul, inv_mul_cancel₀ (by exact_mod_cast ht.ne')]
  have hmm := TensorPower.merge_moment_le (ι := ι') Q' hρ' htr'
    (fun g => (hρQ g).smul_right _) (fun g => (hρC g).smul_right _) hb1
  have hρρ : ρ = (t : ℂ) • ρ' := by
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast ht.ne'), one_smul]
  have hexp : (ρ * M₁).trace.re = t * ∑ l, ∑ μ, ∑ ν,
      (ρ' * (labelProj (TensorPower.subsystemPerm m ι' Q') l *
        labelProj (TensorPower.subsystemPerm m ι' Q'ᶜ) μ *
          labelProj (TensorPower.copyPerm ((f : {f // f ∈ S}) → ι' f) m) ν)).trace.re *
        (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b := by
    rw [subtype_eq_compl hS hQC, re_trace_mul_labelObservable₃, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hl : (0 : ℝ) < l.dim := by exact_mod_cast l.dim_pos
    have hμ : (0 : ℝ) < μ.dim := by exact_mod_cast μ.dim_pos
    have hν : (0 : ℝ) < ν.dim := by exact_mod_cast ν.dim_pos
    have hpow : (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b = Real.exp (b * Real.log l.dim) *
        Real.exp (b * Real.log μ.dim) * Real.exp (-(b * Real.log ν.dim)) := by
      have hlμ : (0 : ℝ) < ((l.dim * μ.dim : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos l.dim_pos μ.dim_pos
      rw [Real.rpow_def_of_pos (div_pos hlμ hν), Real.log_div hlμ.ne' hν.ne', Nat.cast_mul,
        Real.log_mul hl.ne' hμ.ne', ← Real.exp_add, ← Real.exp_add]
      ring_nf
    rw [hpow, hρρ, smul_mul_assoc, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    ring
  rw [hexp]
  calc t * _ ≤ t * ((m + 1) ^ (Fintype.card ((f : {f // f ∈ S}) → ι' f) ^ 2) : ℕ) :=
        mul_le_mul_of_nonneg_left hmm ht.le
    _ = _ := by rw [mul_comm]

end MergeMoments

/-! ## The joint labels of a band on the two groups of copies -/

/-- The five pairwise disjoint regions `XU, V, Y, C, R` of a band; `P = XU ∪ C`, `F = V ∪ R`. -/
structure Band (I : Type*) where
  /-- `Q = XU_{j,g}`. -/
  Q : Finset I
  /-- `V_{j,g}`. -/
  V : Finset I
  /-- `Y_{j,g}`. -/
  Y : Finset I
  /-- The auxiliary factor `C`. -/
  C : Finset I
  /-- The auxiliary factor `R`. -/
  R : Finset I
  hQV : Disjoint Q V
  hQY : Disjoint Q Y
  hQC : Disjoint Q C
  hQR : Disjoint Q R
  hVY : Disjoint V Y
  hVC : Disjoint V C
  hVR : Disjoint V R
  hYC : Disjoint Y C
  hYR : Disjoint Y R
  hCR : Disjoint C R

section Joint

variable {I : Type*} [DecidableEq I] [Fintype I] (ι : I → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)

/-- The label projector of the label `α` of the copy permutations `θ` of the region `T`. -/
noncomputable abbrev gl {H : Type} [Group H] [Fintype H] (θ : H →* Equiv.Perm (Fin k))
    (T : Finset I) (α : IrrepLabel H) : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  labelProj ((Replicas.copyPerm ι k T).comp θ) α

/-- Labels of nested or disjoint regions on one group of copies commute. -/
theorem commute_gl {n : ℕ} (θ : Equiv.Perm (Fin n) →* Equiv.Perm (Fin k)) {T T' : Finset I}
    (h : T ⊆ T' ∨ Disjoint T T') (α β : IrrepLabel (Equiv.Perm (Fin n))) :
    Commute (gl ι θ T α) (gl ι θ T' β) := by
  rcases h with h | h
  · have hprod : ∀ g, ((Replicas.copyPerm ι k T').comp θ) g =
        ((Replicas.copyPerm ι k T).comp θ) g * ((Replicas.copyPerm ι k (T' \ T)).comp θ) g :=
      fun g => by
        simp only [MonoidHom.comp_apply]
        rw [← TensorPower.subsystemPerm_union k ι Finset.disjoint_sdiff,
          Finset.union_sdiff_of_subset h]
    exact commute_groupAlgebraRep_of_eq_mul ((Replicas.copyPerm ι k T).comp θ)
      ((Replicas.copyPerm ι k (T' \ T)).comp θ) ((Replicas.copyPerm ι k T').comp θ) hprod
      (fun g g' => TensorPower.commute_subsystemPerm_of_disjoint k ι Finset.disjoint_sdiff
        (θ g) (θ g')) (IrrepLabel.centralIdem_mem_center α) (IrrepLabel.centralIdem β)
  · exact commute_groupAlgebraRep_of_commute ((Replicas.copyPerm ι k T).comp θ)
      ((Replicas.copyPerm ι k T').comp θ)
      (fun g g' => TensorPower.commute_subsystemPerm_of_disjoint k ι h (θ g) (θ g'))
      (IrrepLabel.centralIdem α) (IrrepLabel.centralIdem β)

/-- Labels of the two groups of copies commute, for any regions. -/
theorem commute_gl_good_bad (T T' : Finset I) (α : IrrepLabel (Equiv.Perm (Fin m)))
    (β : IrrepLabel (Equiv.Perm (Fin r))) :
    Commute (gl ι (TensorPower.groupHom₁ e) T α) (gl ι (TensorPower.groupHom₂ e) T' β) :=
  commute_groupAlgebraRep_of_commute ((Replicas.copyPerm ι k T).comp (TensorPower.groupHom₁ e))
    ((Replicas.copyPerm ι k T').comp (TensorPower.groupHom₂ e))
    (fun g g' => TensorPower.commute_subsystemPerm_of_commute ι k T T'
      (TensorPower.groupHom_commute e g g')) (IrrepLabel.centralIdem α) (IrrepLabel.centralIdem β)

variable {ι} (b : Band I)

/-- The joint label index: good labels of `XU, V, Y, C, R, P, F` and bad labels of `P, F, Y`. -/
abbrev Band.Idx (_b : Band I) (m r : ℕ) :=
  (((((IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin m))) ×
    IrrepLabel (Equiv.Perm (Fin m))) × IrrepLabel (Equiv.Perm (Fin m))) ×
    IrrepLabel (Equiv.Perm (Fin m))) ×
    (IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin m)))) ×
  ((IrrepLabel (Equiv.Perm (Fin r)) × IrrepLabel (Equiv.Perm (Fin r))) ×
    IrrepLabel (Equiv.Perm (Fin r)))

/-- `P = XU ∪ C`. -/
abbrev Band.P : Finset I := b.Q ∪ b.C

/-- `F = V ∪ R`. -/
abbrev Band.F : Finset I := b.V ∪ b.R

end Joint

/-! ### Region relations of a band -/

namespace Band

variable {I : Type*} [DecidableEq I] (b : Band I)

theorem hQF : Disjoint b.Q b.F := Finset.disjoint_union_right.mpr ⟨b.hQV, b.hQR⟩
theorem hVP : Disjoint b.V b.P := Finset.disjoint_union_right.mpr ⟨b.hQV.symm, b.hVC⟩
theorem hYP : Disjoint b.Y b.P := Finset.disjoint_union_right.mpr ⟨b.hQY.symm, b.hYC⟩
theorem hYF : Disjoint b.Y b.F := Finset.disjoint_union_right.mpr ⟨b.hVY.symm, b.hYR⟩
theorem hCF : Disjoint b.C b.F := Finset.disjoint_union_right.mpr ⟨b.hVC.symm, b.hCR⟩
theorem hRP : Disjoint b.R b.P := Finset.disjoint_union_right.mpr ⟨b.hQR.symm, b.hCR.symm⟩
theorem hPF : Disjoint b.P b.F := Finset.disjoint_union_left.mpr ⟨b.hQF, b.hCF⟩

end Band

section JointRes

variable {I : Type*} [DecidableEq I] [Fintype I] {ι : I → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (b : Band I)

/-- Good labels of `XU, V`. -/
noncomputable def Band.f1 (p : IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin m))) :
    Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  gl ι (TensorPower.groupHom₁ e) b.Q p.1 * gl ι (TensorPower.groupHom₁ e) b.V p.2

/-- Good labels of `XU, V, Y`. -/
noncomputable def Band.f2 (p : (IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin m))) ×
    IrrepLabel (Equiv.Perm (Fin m))) : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  b.f1 e p.1 * gl ι (TensorPower.groupHom₁ e) b.Y p.2

/-- Good labels of `XU, V, Y, C`. -/
noncomputable def Band.f3 (p : ((IrrepLabel (Equiv.Perm (Fin m)) ×
    IrrepLabel (Equiv.Perm (Fin m))) × IrrepLabel (Equiv.Perm (Fin m))) ×
    IrrepLabel (Equiv.Perm (Fin m))) : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  b.f2 e p.1 * gl ι (TensorPower.groupHom₁ e) b.C p.2

/-- Good labels of `XU, V, Y, C, R`. -/
noncomputable def Band.f4 (p : (((IrrepLabel (Equiv.Perm (Fin m)) ×
    IrrepLabel (Equiv.Perm (Fin m))) × IrrepLabel (Equiv.Perm (Fin m))) ×
    IrrepLabel (Equiv.Perm (Fin m))) × IrrepLabel (Equiv.Perm (Fin m))) :
    Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  b.f3 e p.1 * gl ι (TensorPower.groupHom₁ e) b.R p.2

/-- Good labels of `P, F`. -/
noncomputable def Band.f5 (p : IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin m))) :
    Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  gl ι (TensorPower.groupHom₁ e) b.P p.1 * gl ι (TensorPower.groupHom₁ e) b.F p.2

/-- All good labels. -/
noncomputable def Band.f6 (p : ((((IrrepLabel (Equiv.Perm (Fin m)) ×
    IrrepLabel (Equiv.Perm (Fin m))) × IrrepLabel (Equiv.Perm (Fin m))) ×
    IrrepLabel (Equiv.Perm (Fin m))) × IrrepLabel (Equiv.Perm (Fin m))) ×
    (IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin m)))) :
    Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  b.f4 e p.1 * b.f5 e p.2

/-- Bad labels of `P, F`. -/
noncomputable def Band.g1 (p : IrrepLabel (Equiv.Perm (Fin r)) × IrrepLabel (Equiv.Perm (Fin r))) :
    Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  gl ι (TensorPower.groupHom₂ e) b.P p.1 * gl ι (TensorPower.groupHom₂ e) b.F p.2

/-- Bad labels of `P, F, Y`. -/
noncomputable def Band.g2 (p : (IrrepLabel (Equiv.Perm (Fin r)) × IrrepLabel (Equiv.Perm (Fin r))) ×
    IrrepLabel (Equiv.Perm (Fin r))) : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  b.g1 e p.1 * gl ι (TensorPower.groupHom₂ e) b.Y p.2

/-- The joint projector of all good and bad labels of a band. -/
noncomputable def Band.jp (p : b.Idx m r) : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ :=
  b.f6 e p.1 * b.g2 e p.2

local notation "G₁" => gl ι (TensorPower.groupHom₁ e)
local notation "G₂" => gl ι (TensorPower.groupHom₂ e)

theorem Band.res (θ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin k)) (T : Finset I) :
    IsOrthogonalResolution (gl ι θ T) := isOrthogonalResolution_labelProj _

theorem Band.resB (T : Finset I) :
    IsOrthogonalResolution (gl ι (TensorPower.groupHom₂ e) T) := isOrthogonalResolution_labelProj _

theorem Band.c2C (i) (j) : Commute (b.f2 e i) (G₁ b.C j) :=
  ((commute_gl ι _ (Or.inr b.hQC) _ _).mul_left (commute_gl ι _ (Or.inr b.hVC) _ _)).mul_left
    (commute_gl ι _ (Or.inr b.hYC) _ _)

theorem Band.c3R (i) (j) : Commute (b.f3 e i) (G₁ b.R j) :=
  (((commute_gl ι _ (Or.inr b.hQR) _ _).mul_left (commute_gl ι _ (Or.inr b.hVR) _ _)).mul_left
    (commute_gl ι _ (Or.inr b.hYR) _ _)).mul_left (commute_gl ι _ (Or.inr b.hCR) _ _)

theorem Band.c4P (i) (j) : Commute (b.f4 e i) (G₁ b.P j) :=
  ((((commute_gl ι _ (Or.inl Finset.subset_union_left) _ _).mul_left
    (commute_gl ι _ (Or.inr b.hVP) _ _)).mul_left (commute_gl ι _ (Or.inr b.hYP) _ _)).mul_left
    (commute_gl ι _ (Or.inl Finset.subset_union_right) _ _)).mul_left
    (commute_gl ι _ (Or.inr b.hRP) _ _)

theorem Band.c4F (i) (j) : Commute (b.f4 e i) (G₁ b.F j) :=
  ((((commute_gl ι _ (Or.inr b.hQF) _ _).mul_left
    (commute_gl ι _ (Or.inl Finset.subset_union_left) _ _)).mul_left
    (commute_gl ι _ (Or.inr b.hYF) _ _)).mul_left (commute_gl ι _ (Or.inr b.hCF) _ _)).mul_left
    (commute_gl ι _ (Or.inl Finset.subset_union_right) _ _)

theorem Band.c6g (i) (T : Finset I) (j) : Commute (b.f6 e i) (G₂ T j) :=
  (((((commute_gl_good_bad ι e _ _ _ _).mul_left (commute_gl_good_bad ι e _ _ _ _)).mul_left
    (commute_gl_good_bad ι e _ _ _ _)).mul_left (commute_gl_good_bad ι e _ _ _ _)).mul_left
    (commute_gl_good_bad ι e _ _ _ _)).mul_left
    ((commute_gl_good_bad ι e _ _ _ _).mul_left (commute_gl_good_bad ι e _ _ _ _))

theorem Band.res1 : IsOrthogonalResolution (b.f1 (ι := ι) e) :=
  (Band.res (ι := ι) (TensorPower.groupHom₁ e) _).prod
    (Band.res (ι := ι) (TensorPower.groupHom₁ e) _) fun i j => commute_gl ι _ (Or.inr b.hQV) i j

theorem Band.res2 : IsOrthogonalResolution (b.f2 (ι := ι) e) :=
  (b.res1 e).prod (Band.res (ι := ι) (TensorPower.groupHom₁ e) _) fun _ _ =>
    (commute_gl ι _ (Or.inr b.hQY) _ _).mul_left (commute_gl ι _ (Or.inr b.hVY) _ _)

theorem Band.res3 : IsOrthogonalResolution (b.f3 (ι := ι) e) :=
  (b.res2 e).prod (Band.res (ι := ι) (TensorPower.groupHom₁ e) _) (b.c2C e)

theorem Band.res4 : IsOrthogonalResolution (b.f4 (ι := ι) e) :=
  (b.res3 e).prod (Band.res (ι := ι) (TensorPower.groupHom₁ e) _) (b.c3R e)

theorem Band.res5 : IsOrthogonalResolution (b.f5 (ι := ι) e) :=
  (Band.res (ι := ι) (TensorPower.groupHom₁ e) _).prod
    (Band.res (ι := ι) (TensorPower.groupHom₁ e) _) fun i j => commute_gl ι _ (Or.inr b.hPF) i j

theorem Band.res6 : IsOrthogonalResolution (b.f6 (ι := ι) e) :=
  (b.res4 e).prod (b.res5 e) fun i j => (b.c4P e i j.1).mul_right (b.c4F e i j.2)

theorem Band.resg1 : IsOrthogonalResolution (b.g1 (ι := ι) e) :=
  (Band.resB e _).prod (Band.resB e _) fun i j => commute_gl ι _ (Or.inr b.hPF) i j

theorem Band.resg2 : IsOrthogonalResolution (b.g2 (ι := ι) e) :=
  (b.resg1 e).prod (Band.resB e _) fun _ _ =>
    (commute_gl ι _ (Or.inr b.hYP.symm) _ _).mul_left (commute_gl ι _ (Or.inr b.hYF.symm) _ _)

/-- The joint resolution of the good labels of `XU, V, Y, C, R, P, F` and the bad labels of
`P, F, Y`. -/
theorem Band.resJ : IsOrthogonalResolution (b.jp (ι := ι) e) :=
  (b.res6 e).prod (b.resg2 e) fun i _ =>
    ((b.c6g e i _ _).mul_right (b.c6g e i _ _)).mul_right (b.c6g e i _ _)

end JointRes

/-! ### Coordinates, positivity and supports of the joint resolution -/

section JointCoord

variable {I : Type*} [DecidableEq I] [Fintype I] {ι : I → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (b : Band I)

local notation "θ₁" => TensorPower.groupHom₁ e
local notation "θ₂" => TensorPower.groupHom₂ e

theorem Band.hom_Q (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.1.1.1.1.1.1 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.Q).comp θ₁) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_fst (b.resg2 e) (b.resJ e)
    (fun q => ((f q.1.1.1.1.1 : ℝ) : ℂ))).trans (((b.res4 e).prod_hom_fst (b.res5 e) (b.res6 e)
    (fun q => ((f q.1.1.1.1 : ℝ) : ℂ))).trans (((b.res3 e).prod_hom_fst (Band.res θ₁ b.R)
    (b.res4 e) (fun q => ((f q.1.1.1 : ℝ) : ℂ))).trans (((b.res2 e).prod_hom_fst
    (Band.res θ₁ b.C) (b.res3 e) (fun q => ((f q.1.1 : ℝ) : ℂ))).trans (((b.res1 e).prod_hom_fst
    (Band.res θ₁ b.Y) (b.res2 e) (fun q => ((f q.1 : ℝ) : ℂ))).trans
    ((Band.res θ₁ b.Q).prod_hom_fst (Band.res θ₁ b.V) (b.res1 e) (fun l => ((f l : ℝ) : ℂ)))))))

theorem Band.hom_V (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.1.1.1.1.1.2 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.V).comp θ₁) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_fst (b.resg2 e) (b.resJ e)
    (fun q => ((f q.1.1.1.1.2 : ℝ) : ℂ))).trans (((b.res4 e).prod_hom_fst (b.res5 e) (b.res6 e)
    (fun q => ((f q.1.1.1.2 : ℝ) : ℂ))).trans (((b.res3 e).prod_hom_fst (Band.res θ₁ b.R)
    (b.res4 e) (fun q => ((f q.1.1.2 : ℝ) : ℂ))).trans (((b.res2 e).prod_hom_fst
    (Band.res θ₁ b.C) (b.res3 e) (fun q => ((f q.1.2 : ℝ) : ℂ))).trans (((b.res1 e).prod_hom_fst
    (Band.res θ₁ b.Y) (b.res2 e) (fun q => ((f q.2 : ℝ) : ℂ))).trans
    ((Band.res θ₁ b.Q).prod_hom_snd (Band.res θ₁ b.V) (b.res1 e) (fun l => ((f l : ℝ) : ℂ)))))))

theorem Band.hom_Y (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.1.1.1.1.2 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.Y).comp θ₁) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_fst (b.resg2 e) (b.resJ e)
    (fun q => ((f q.1.1.1.2 : ℝ) : ℂ))).trans (((b.res4 e).prod_hom_fst (b.res5 e) (b.res6 e)
    (fun q => ((f q.1.1.2 : ℝ) : ℂ))).trans (((b.res3 e).prod_hom_fst (Band.res θ₁ b.R)
    (b.res4 e) (fun q => ((f q.1.2 : ℝ) : ℂ))).trans (((b.res2 e).prod_hom_fst
    (Band.res θ₁ b.C) (b.res3 e) (fun q => ((f q.2 : ℝ) : ℂ))).trans
    ((b.res1 e).prod_hom_snd (Band.res θ₁ b.Y) (b.res2 e) (fun l => ((f l : ℝ) : ℂ))))))

theorem Band.hom_C (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.1.1.1.2 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.C).comp θ₁) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_fst (b.resg2 e) (b.resJ e)
    (fun q => ((f q.1.1.2 : ℝ) : ℂ))).trans (((b.res4 e).prod_hom_fst (b.res5 e) (b.res6 e)
    (fun q => ((f q.1.2 : ℝ) : ℂ))).trans (((b.res3 e).prod_hom_fst (Band.res θ₁ b.R)
    (b.res4 e) (fun q => ((f q.2 : ℝ) : ℂ))).trans
    ((b.res2 e).prod_hom_snd (Band.res θ₁ b.C) (b.res3 e) (fun l => ((f l : ℝ) : ℂ)))))

theorem Band.hom_R (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.1.1.2 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.R).comp θ₁) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_fst (b.resg2 e) (b.resJ e)
    (fun q => ((f q.1.2 : ℝ) : ℂ))).trans (((b.res4 e).prod_hom_fst (b.res5 e) (b.res6 e)
    (fun q => ((f q.2 : ℝ) : ℂ))).trans
    ((b.res3 e).prod_hom_snd (Band.res θ₁ b.R) (b.res4 e) (fun l => ((f l : ℝ) : ℂ))))

theorem Band.hom_P (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.1.2.1 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.P).comp θ₁) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_fst (b.resg2 e) (b.resJ e)
    (fun q => ((f q.2.1 : ℝ) : ℂ))).trans (((b.res4 e).prod_hom_snd (b.res5 e) (b.res6 e)
    (fun q => ((f q.1 : ℝ) : ℂ))).trans
    ((Band.res θ₁ b.P).prod_hom_fst (Band.res θ₁ b.F) (b.res5 e) (fun l => ((f l : ℝ) : ℂ))))

theorem Band.hom_F (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.1.2.2 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.F).comp θ₁) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_fst (b.resg2 e) (b.resJ e)
    (fun q => ((f q.2.2 : ℝ) : ℂ))).trans (((b.res4 e).prod_hom_snd (b.res5 e) (b.res6 e)
    (fun q => ((f q.2 : ℝ) : ℂ))).trans
    ((Band.res θ₁ b.P).prod_hom_snd (Band.res θ₁ b.F) (b.res5 e) (fun l => ((f l : ℝ) : ℂ))))

theorem Band.hom_bP (f : IrrepLabel (Equiv.Perm (Fin r)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.2.1.1 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.P).comp θ₂) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_snd (b.resg2 e) (b.resJ e)
    (fun q => ((f q.1.1 : ℝ) : ℂ))).trans (((b.resg1 e).prod_hom_fst (Band.resB e b.Y)
    (b.resg2 e) (fun q => ((f q.1 : ℝ) : ℂ))).trans
    ((Band.resB e b.P).prod_hom_fst (Band.resB e b.F) (b.resg1 e) (fun l => ((f l : ℝ) : ℂ))))

theorem Band.hom_bF (f : IrrepLabel (Equiv.Perm (Fin r)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.2.1.2 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.F).comp θ₂) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_snd (b.resg2 e) (b.resJ e)
    (fun q => ((f q.1.2 : ℝ) : ℂ))).trans (((b.resg1 e).prod_hom_fst (Band.resB e b.Y)
    (b.resg2 e) (fun q => ((f q.2 : ℝ) : ℂ))).trans
    ((Band.resB e b.P).prod_hom_snd (Band.resB e b.F) (b.resg1 e) (fun l => ((f l : ℝ) : ℂ))))

theorem Band.hom_bY (f : IrrepLabel (Equiv.Perm (Fin r)) → ℝ) :
    (b.resJ (ι := ι) e).hom (fun p => ((f p.2.2 : ℝ) : ℂ)) =
      labelObservable ((Replicas.copyPerm ι k b.Y).comp θ₂) f := by
  rw [labelObservable_eq_hom]
  exact ((b.res6 e).prod_hom_snd (b.resg2 e) (b.resJ e)
    (fun q => ((f q.2 : ℝ) : ℂ))).trans
    ((b.resg1 e).prod_hom_snd (Band.resB e b.Y) (b.resg2 e) (fun l => ((f l : ℝ) : ℂ)))

end JointCoord

/-! ### Positivity, weights and supports -/

section JointWeights

variable {I : Type*} [DecidableEq I] [Fintype I] {ι : I → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (b : Band I)

local notation "θ₁" => TensorPower.groupHom₁ e
local notation "θ₂" => TensorPower.groupHom₂ e

omit [DecidableEq I] [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
/-- The quadratic form of a function of an orthogonal resolution is the weighted sum. -/
theorem re_dotProduct_hom_ofReal {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    [DecidableEq κ] {P : κ → Matrix n n ℂ} (hP : IsOrthogonalResolution P) (f : κ → ℝ)
    (z : n → ℂ) :
    (star z ⬝ᵥ (hP.hom (fun i => (f i : ℂ)) *ᵥ z)).re =
      ∑ i, f i * IsOrthogonalResolution.weight (P := P) z i := by
  rw [hP.hom_apply]
  simp only [sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, Complex.re_sum,
    smul_eq_mul, Complex.re_ofReal_mul, IsOrthogonalResolution.weight, RCLike.re_to_complex]

theorem Band.cQVY_P (i) (j) : Commute (b.f2 (ι := ι) e i) (gl ι θ₁ b.P j) :=
  ((commute_gl ι _ (Or.inl Finset.subset_union_left) _ _).mul_left
    (commute_gl ι _ (Or.inr b.hVP) _ _)).mul_left (commute_gl ι _ (Or.inr b.hYP) _ _)

theorem Band.cQVY_F (i) (j) : Commute (b.f2 (ι := ι) e i) (gl ι θ₁ b.F j) :=
  ((commute_gl ι _ (Or.inr b.hQF) _ _).mul_left
    (commute_gl ι _ (Or.inl Finset.subset_union_left) _ _)).mul_left
    (commute_gl ι _ (Or.inr b.hYF) _ _)

theorem Band.cQVY_R (i) (j) : Commute (b.f2 (ι := ι) e i) (gl ι θ₁ b.R j) :=
  ((commute_gl ι _ (Or.inr b.hQR) _ _).mul_left (commute_gl ι _ (Or.inr b.hVR) _ _)).mul_left
    (commute_gl ι _ (Or.inr b.hYR) _ _)

theorem Band.c2bad (i) (T : Finset I) (j) : Commute (b.f2 (ι := ι) e i) (gl ι θ₂ T j) :=
  ((commute_gl_good_bad ι e _ _ _ _).mul_left (commute_gl_good_bad ι e _ _ _ _)).mul_left
    (commute_gl_good_bad ι e _ _ _ _)

theorem Band.cg2 (i : b.Idx m r) (X : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ)
    (h : ∀ (T : Finset I) j, Commute X (gl ι θ₂ T j)) : Commute X (b.g2 e i.2) :=
  ((h _ _).mul_right (h _ _)).mul_right (h _ _)

private theorem absorb {n : Type*} [Fintype n] {X Y F : Matrix n n ℂ}
    (hX : X * F = X) (h : Commute Y F) : X * Y * F = X * Y := by
  rw [mul_assoc, h.eq, ← mul_assoc, hX]

/-- The joint projector absorbs the good labels of `XU, V, Y`. -/
theorem Band.jp_mul_f2 (p : b.Idx m r) : b.jp (ι := ι) e p * b.f2 e p.1.1.1.1 = b.jp e p := by
  have h0 : b.f2 (ι := ι) e p.1.1.1.1 * b.f2 e p.1.1.1.1 = b.f2 e p.1.1.1.1 :=
    (b.res2 e).mul_self _
  have h1 := absorb h0 (b.c2C e p.1.1.1.1 p.1.1.1.2).symm
  have h2 := absorb h1 (b.cQVY_R e p.1.1.1.1 p.1.1.2).symm
  have h3 := absorb h2 (show Commute (b.f5 e p.1.2) (b.f2 e p.1.1.1.1) from
    ((b.cQVY_P e p.1.1.1.1 p.1.2.1).mul_right (b.cQVY_F e p.1.1.1.1 p.1.2.2)).symm)
  exact absorb h3 (b.cg2 e p _ (b.c2bad e p.1.1.1.1)).symm

/-- The joint projector absorbs the good label of `C`. -/
theorem Band.jp_mul_C (p : b.Idx m r) :
    b.jp (ι := ι) e p * gl ι θ₁ b.C p.1.1.1.2 = b.jp e p := by
  have h0 : b.f3 (ι := ι) e p.1.1.1 * gl ι θ₁ b.C p.1.1.1.2 = b.f3 e p.1.1.1 := by
    rw [Band.f3, mul_assoc, labelProj_mul_self]
  have h2 := absorb h0 (commute_gl ι θ₁ (Or.inr b.hCR) p.1.1.1.2 p.1.1.2).symm
  have h3 := absorb h2 (show Commute (b.f5 e p.1.2) (gl ι θ₁ b.C p.1.1.1.2) from
    ((commute_gl ι θ₁ (Or.inl (Finset.subset_union_right : b.C ⊆ b.P)) p.1.1.1.2 p.1.2.1).mul_right
      (commute_gl ι θ₁ (Or.inr b.hCF) p.1.1.1.2 p.1.2.2)).symm)
  exact absorb h3 (b.cg2 e p _ fun T j => commute_gl_good_bad ι e _ _ _ _).symm

/-- The joint projector absorbs the good label of `R`. -/
theorem Band.jp_mul_R (p : b.Idx m r) :
    b.jp (ι := ι) e p * gl ι θ₁ b.R p.1.1.2 = b.jp e p := by
  have h0 : b.f4 (ι := ι) e p.1.1 * gl ι θ₁ b.R p.1.1.2 = b.f4 e p.1.1 := by
    rw [Band.f4, mul_assoc, labelProj_mul_self]
  have h3 := absorb h0 (show Commute (b.f5 e p.1.2) (gl ι θ₁ b.R p.1.1.2) from
    ((commute_gl ι θ₁ (Or.inr b.hRP) p.1.1.2 p.1.2.1).mul_right
      (commute_gl ι θ₁ (Or.inl (Finset.subset_union_right : b.R ⊆ b.F)) p.1.1.2 p.1.2.2)).symm)
  exact absorb h3 (b.cg2 e p _ fun T j => commute_gl_good_bad ι e _ _ _ _).symm

/-- The joint projector absorbs the bad labels of `P, F, Y`. -/
theorem Band.jp_mul_g2 (p : b.Idx m r) : b.jp (ι := ι) e p * b.g2 e p.2 = b.jp e p := by
  rw [Band.jp, mul_assoc, (b.resg2 e).mul_self]

theorem Band.isHermitian_jp (p : b.Idx m r) : (b.jp (ι := ι) e p).IsHermitian := by
  have H : ∀ {n : ℕ} (θ : Equiv.Perm (Fin n) →* Equiv.Perm (Fin k)) T j,
      (gl ι θ T j).IsHermitian := fun θ T j => isHermitian_labelProj _ _
  have h1 : (b.f1 (ι := ι) e p.1.1.1.1.1).IsHermitian :=
    ((H _ _ _).commute_iff (H _ _ _)).mp (commute_gl ι _ (Or.inr b.hQV) _ _)
  have h2 : (b.f2 (ι := ι) e p.1.1.1.1).IsHermitian :=
    (h1.commute_iff (H _ _ _)).mp ((commute_gl ι _ (Or.inr b.hQY) _ _).mul_left
      (commute_gl ι _ (Or.inr b.hVY) _ _))
  have h3 : (b.f3 (ι := ι) e p.1.1.1).IsHermitian :=
    (h2.commute_iff (H _ _ _)).mp (b.c2C e _ _)
  have h4 : (b.f4 (ι := ι) e p.1.1).IsHermitian :=
    (h3.commute_iff (H _ _ _)).mp (b.c3R e _ _)
  have h5 : (b.f5 (ι := ι) e p.1.2).IsHermitian :=
    ((H _ _ _).commute_iff (H _ _ _)).mp (commute_gl ι _ (Or.inr b.hPF) _ _)
  have h6 : (b.f6 (ι := ι) e p.1).IsHermitian :=
    (h4.commute_iff h5).mp ((b.c4P e _ _).mul_right (b.c4F e _ _))
  have g1 : (b.g1 (ι := ι) e p.2.1).IsHermitian :=
    ((H _ _ _).commute_iff (H _ _ _)).mp (commute_gl ι _ (Or.inr b.hPF) _ _)
  have g2 : (b.g2 (ι := ι) e p.2).IsHermitian :=
    (g1.commute_iff (H _ _ _)).mp ((commute_gl ι _ (Or.inr b.hYP.symm) _ _).mul_left
      (commute_gl ι _ (Or.inr b.hYF.symm) _ _))
  exact (h6.commute_iff g2).mp (b.cg2 e p _ (b.c6g e p.1))

/-- A factor absorbed by a joint projector of positive weight does not annihilate the vector. -/
theorem Band.mulVec_ne_zero_of_weight_ne_zero {u : Replicas.Config ι k → ℂ} {p : b.Idx m r}
    (hw : IsOrthogonalResolution.weight (P := b.jp e) u p ≠ 0)
    {M : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ} (hM : b.jp e p * M = b.jp e p) :
    M *ᵥ u ≠ 0 := by
  intro h
  apply hw
  rw [IsOrthogonalResolution.weight, ← hM, ← mulVec_mulVec, h, mulVec_zero, dotProduct_zero,
    map_zero]

end JointWeights

/-! ## D8.30 on the system of §8 -/

section SiteBand

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {K : ℕ} {St : Type v} {X : Finset σ}
  (Γ : Statuses σ K St X) (s : St) (g : Fin K)

/-- The band `(XU_{j,g}, V_{j,g}, Y_{j,g}, C, R)` of a status. -/
def Statuses.band : Band (Site σ) where
  Q := physReg (X ∪ Γ.U s g)
  V := physReg (Γ.V s g)
  Y := Γ.Yr s g
  C := {Site.C}
  R := {Site.R}
  hQV := physReg_disjoint.mpr (disjoint_XU_V Γ s g)
  hQY := physReg_disjoint.mpr (disjoint_XU_Y Γ s g)
  hQC := Finset.disjoint_singleton_right.mpr (C_not_mem_physReg _)
  hQR := Finset.disjoint_singleton_right.mpr (R_not_mem_physReg _)
  hVY := physReg_disjoint.mpr (Γ.disjoint_YV s g).symm
  hVC := Finset.disjoint_singleton_right.mpr (C_not_mem_physReg _)
  hVR := Finset.disjoint_singleton_right.mpr (R_not_mem_physReg _)
  hYC := Finset.disjoint_singleton_right.mpr (C_not_mem_physReg _)
  hYR := Finset.disjoint_singleton_right.mpr (R_not_mem_physReg _)
  hCR := by simp

theorem Statuses.band_P : (Γ.band s g).P = Γ.P s g := (P_eq Γ s g).symm

theorem Statuses.band_F : (Γ.band s g).F = Γ.F s g := (F_eq Γ s g).symm

end SiteBand

section SiteInvariance

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} (D : PhysData n) (d : ℕ)

/-- `u_B` is invariant under the good permutations of the physical factors. -/
theorem mem_invariant_phys_compProj {k : ℕ} (B : Finset (Fin k))
    (u : Transport.Config (dims n d) k → ℂ) :
    compProj D d k B *ᵥ u ∈ invariantSubspace
      ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg Finset.univ)).comp
        (TensorPower.groupHom₁ (split B))) := fun a =>
  physPerm_mulVec_compProj D d k B (fun _ hj => groupHom₁_split_of_mem a hj) u

/-- `u_B` is invariant under the good permutations of all factors, and of the bad copies. -/
theorem mem_invariant_univ_compProj (τ : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k)))
    {u : Transport.Config (dims n d) k → ℂ} (hu : lowProj D d τ k l *ᵥ u = u)
    (B : Finset (Fin k)) :
    compProj D d k B *ᵥ u ∈ invariantSubspace
        ((Replicas.copyPerm (fun f => Fin (dims n d f)) k Finset.univ).comp
          (TensorPower.groupHom₁ (split B))) ∧
      compProj D d k B *ᵥ u ∈ invariantSubspace
        ((Replicas.copyPerm (fun f => Fin (dims n d f)) k Finset.univ).comp
          (TensorPower.groupHom₂ (split B))) := by
  obtain ⟨-, -, hB⟩ := step_8_24 D d τ k l hu
  obtain ⟨hgood, hbad, -⟩ := hB B
  have hU : Replicas.copyPerm (fun f => Fin (dims n d f)) k Finset.univ =
      TensorPower.copyPerm (SiteConfig (dims n d)) k := TensorPower.subsystemPerm_univ k _
  exact ⟨fun a => by rw [hU]; exact hgood a, fun b => by rw [hU]; exact hbad b⟩

/-- `u_B` is invariant under the good permutations of the auxiliary pair `CR`. -/
theorem mem_invariant_aux_compProj (τ : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k)))
    {u : Transport.Config (dims n d) k → ℂ} (hu : lowProj D d τ k l *ᵥ u = u)
    (B : Finset (Fin k)) :
    compProj D d k B *ᵥ u ∈ invariantSubspace
      ((Replicas.copyPerm (fun f => Fin (dims n d f)) k ({Site.C} ∪ {Site.R})).comp
        (TensorPower.groupHom₁ (split B))) := by
  have hdis : Disjoint (physReg (Finset.univ : Finset σ)) ({Site.C} ∪ {Site.R}) := by simp
  have hcov : physReg (Finset.univ : Finset σ) ∪ ({Site.C} ∪ {Site.R}) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    rintro (v | _ | _) <;> simp
  intro a
  have hall := (mem_invariant_univ_compProj D d τ l hu B).1 a
  have hph := mem_invariant_phys_compProj D d B u a
  rw [← hcov] at hall
  rw [permOp_of_eq_mul ((Replicas.copyPerm (fun f => Fin (dims n d f)) k
      (physReg Finset.univ)).comp (TensorPower.groupHom₁ (split B)))
    ((Replicas.copyPerm (fun f => Fin (dims n d f)) k ({Site.C} ∪ {Site.R})).comp
      (TensorPower.groupHom₁ (split B)))
    ((Replicas.copyPerm (fun f => Fin (dims n d f)) k
      (physReg Finset.univ ∪ ({Site.C} ∪ {Site.R}))).comp (TensorPower.groupHom₁ (split B)))
    (fun g => TensorPower.subsystemPerm_union k _ hdis (TensorPower.groupHom₁ (split B) g)) a,
    ← mulVec_mulVec] at hall
  set φ := (Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg Finset.univ)).comp
    (TensorPower.groupHom₁ (split B))
  set χ := (Replicas.copyPerm (fun f => Fin (dims n d f)) k ({Site.C} ∪ {Site.R})).comp
    (TensorPower.groupHom₁ (split B))
  set w := compProj D d k B *ᵥ u
  clear_value w
  have h1 : permOp χ a *ᵥ w = permOp φ a⁻¹ *ᵥ (permOp φ a *ᵥ (permOp χ a *ᵥ w)) := by
    rw [mulVec_mulVec, permOp_inv_mul_self, one_mulVec]
  rw [h1, hall]
  conv_lhs => rw [← hph]
  rw [mulVec_mulVec, permOp_inv_mul_self, one_mulVec]

end SiteInvariance

/-! ### D8.30 The component inverse -/

section ComponentInverse

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
  (d : ℕ) [NeZero d] {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)

omit [Fintype σ] [DecidableEq σ] [∀ v, NeZero (n v)] [NeZero d] in
/-- D8.30.1–D8.30.3, pointwise: on the support,
`e^{-aG^good - aG^bad} ≤ e^{-2aθ} e^{aD_C} e^{aD_R}` (rough). -/
private theorem rough_pointwise {a θ lQ lV lY lC lR lP lF bP bF bY : ℝ} (ha : 0 < a)
    (hb : bY ≤ bP + bF) (hY : lY ≤ lQ + lV) (hC : θ ≤ lC) (hR : θ ≤ lR) :
    Real.exp (-a * (lP + lF - lY + (bP + bF - bY))) ≤
      Real.exp (-(2 * a * θ)) *
        (Real.exp (a * (lQ + lC - lP)) * Real.exp (a * (lV + lR - lF))) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith

omit [Fintype σ] [DecidableEq σ] [∀ v, NeZero (n v)] [NeZero d] in
private theorem re_dotProduct_smul_mulVec {N : Type*} [Fintype N] (x : N → ℂ) (c : ℝ)
    (M : Matrix N N ℂ) : (star x ⬝ᵥ ((c • M) *ᵥ x)).re = c * (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]

omit [∀ v, NeZero (n v)] [NeZero d] in
/-- The physical regions of a band in the order `XU, V ∪ Y` cover the physical factors. -/
private theorem band_phys_cover (s : St) (g : Fin K) :
    (Γ.band s g).Q ∪ ((Γ.band s g).V ∪ (Γ.band s g).Y) = physReg Finset.univ := by
  rw [← Yr_union_XU_union_V Γ s g]
  simp only [Statuses.band]
  ext f
  simp only [Finset.mem_union]
  tauto

omit [∀ v, NeZero (n v)] [NeZero d] in
private theorem band_phys_cover' (s : St) (g : Fin K) :
    (Γ.band s g).V ∪ ((Γ.band s g).Q ∪ (Γ.band s g).Y) = physReg Finset.univ := by
  rw [← band_phys_cover Γ s g]
  ext f
  simp only [Finset.mem_union]
  tauto

/-- D8.29 applied to `u_B` for `D_C`: `⟨u_B, e^{2aD_C} u_B⟩ ≤ (k + 2)^{dim(𝒱)²} ‖u_B‖²`, and the
same for `D_R`. -/
theorem merge_moments_compProj (τ : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k)))
    {u : Transport.Config (dims n d) k → ℂ} (hu : lowProj D d τ k l *ᵥ u = u)
    (B : Finset (Fin k)) (s : St) (g : Fin K) {b : ℝ} (hb1 : b ≤ 1) :
    (star (compProj D d k B *ᵥ u) ⬝ᵥ (mergeExp (fun f => Fin (dims n d f)) (split B)
        (Γ.band s g).Q (Γ.band s g).C b *ᵥ (compProj D d k B *ᵥ u))).re ≤
      ((k : ℝ) + 2) ^ (Fintype.card (SiteConfig (dims n d)) ^ 2) *
        (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re ∧
    (star (compProj D d k B *ᵥ u) ⬝ᵥ (mergeExp (fun f => Fin (dims n d f)) (split B)
        (Γ.band s g).V (Γ.band s g).R b *ᵥ (compProj D d k B *ᵥ u))).re ≤
      ((k : ℝ) + 2) ^ (Fintype.card (SiteConfig (dims n d)) ^ 2) *
        (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re := by
  set bd := Γ.band s g
  have hph := mem_invariant_phys_compProj D d B u
  have haux := mem_invariant_aux_compProj D d τ l hu B
  have hnn : 0 ≤ (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re :=
    (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1
  have hpoly : ∀ S : Finset (Site σ),
      (((Bᶜ.card + 1) ^ (Fintype.card (TensorPower.SubConfig (fun f => Fin (dims n d f)) S) ^ 2)
        : ℕ) : ℝ) ≤ ((k : ℝ) + 2) ^ (Fintype.card (SiteConfig (dims n d)) ^ 2) := fun S => by
    have hm : Bᶜ.card ≤ k := (Finset.card_le_univ _).trans (by simp)
    have hq := TensorPower.card_subConfig_le (fun f => Fin (dims n d f)) S
    push_cast
    calc ((Bᶜ.card : ℝ) + 1) ^ (Fintype.card (TensorPower.SubConfig _ S) ^ 2)
        ≤ ((k : ℝ) + 2) ^ (Fintype.card (TensorPower.SubConfig _ S) ^ 2) := by
          gcongr
          have : (Bᶜ.card : ℝ) ≤ k := by exact_mod_cast hm
          linarith
      _ ≤ ((k : ℝ) + 2) ^ (Fintype.card (SiteConfig (dims n d)) ^ 2) := by
          gcongr
          linarith
  constructor
  · have h := step_8_29 (fun f => Fin (dims n d f)) (split B) (Q := bd.Q) (C := bd.C)
      (T₂ := bd.V ∪ bd.Y) (T₃ := bd.R) bd.hQC
      (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨bd.hQV.symm, bd.hVC⟩,
        Finset.disjoint_union_right.mpr ⟨bd.hQY.symm, bd.hYC⟩⟩)
      (Finset.disjoint_union_right.mpr ⟨bd.hQR.symm, bd.hCR.symm⟩)
      (by rw [band_phys_cover Γ s g]; exact hph) haux hb1
    exact h.trans (mul_le_mul_of_nonneg_right (hpoly _) hnn)
  · have h := step_8_29 (fun f => Fin (dims n d f)) (split B) (Q := bd.V) (C := bd.R)
      (T₂ := bd.Q ∪ bd.Y) (T₃ := bd.C) bd.hVR
      (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨bd.hQV, bd.hQR⟩,
        Finset.disjoint_union_right.mpr ⟨bd.hVY.symm, bd.hYR⟩⟩)
      (Finset.disjoint_union_right.mpr ⟨bd.hVC.symm, bd.hCR⟩)
      (by rw [band_phys_cover' Γ s g]; exact hph)
      (by rw [Finset.union_comm]; exact haux) hb1
    exact h.trans (mul_le_mul_of_nonneg_right (hpoly _) hnn)

end ComponentInverse

/-! ### The exponentials of D8.26 and D8.29 as functions of the joint labels -/

section JointExp

variable {I : Type*} [DecidableEq I] [Fintype I] {ι : I → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (b : Band I)

local notation "θ₁" => TensorPower.groupHom₁ e
local notation "θ₂" => TensorPower.groupHom₂ e

/-- D8.26: `exp{-a(G^good + G^bad)}` is the function
`exp{-a(log d_P + log d_F - log d_Y + log d_P' + log d_F' - log d_Y')}` of the joint labels. -/
theorem Band.exp_eq_hom (a : ℝ) :
    NormedSpace.exp ((-a) •
      ((labelEntropy ((Replicas.copyPerm ι k b.P).comp θ₁) +
          labelEntropy ((Replicas.copyPerm ι k b.F).comp θ₁) -
          labelEntropy ((Replicas.copyPerm ι k b.Y).comp θ₁)) +
        (labelEntropy ((Replicas.copyPerm ι k b.P).comp θ₂) +
          labelEntropy ((Replicas.copyPerm ι k b.F).comp θ₂) -
          labelEntropy ((Replicas.copyPerm ι k b.Y).comp θ₂)))) =
      (b.resJ e).hom (fun p => ((Real.exp (-a * (Real.log p.1.2.1.dim + Real.log p.1.2.2.dim -
        Real.log p.1.1.1.1.2.dim + (Real.log p.2.1.1.dim + Real.log p.2.1.2.dim -
          Real.log p.2.2.dim))) : ℝ) : ℂ)) := by
  simp only [labelEntropy]
  rw [← b.hom_P e, ← b.hom_F e, ← b.hom_Y e, ← b.hom_bP e, ← b.hom_bF e, ← b.hom_bY e,
    ← map_add, ← map_sub, ← map_add, ← map_sub, ← map_add, ← Complex.coe_smul, ← map_smul,
    (b.resJ e).exp_hom]
  congr 1
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

/-- D8.29: `e^{c D_C} = e^{c(log d_Q + log d_C - log d_P)}` as a function of the joint labels. -/
theorem Band.hom_mergeC (c : ℝ) :
    (b.resJ e).hom (fun p => ((Real.exp (c * (Real.log p.1.1.1.1.1.1.dim +
        Real.log p.1.1.1.2.dim - Real.log p.1.2.1.dim)) : ℝ) : ℂ)) =
      mergeExp ι e b.Q b.C c := by
  have h : (fun p : b.Idx m r => ((Real.exp (c * (Real.log p.1.1.1.1.1.1.dim +
      Real.log p.1.1.1.2.dim - Real.log p.1.2.1.dim)) : ℝ) : ℂ)) =
      (fun p => ((Real.exp (c * Real.log p.1.1.1.1.1.1.dim) : ℝ) : ℂ)) *
        (fun p => ((Real.exp (c * Real.log p.1.1.1.2.dim) : ℝ) : ℂ)) *
        (fun p => ((Real.exp (-(c * Real.log p.1.2.1.dim)) : ℝ) : ℂ)) := by
    funext p
    simp only [Pi.mul_apply]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  rw [h, map_mul, map_mul, b.hom_Q e (fun l => Real.exp (c * Real.log l.dim)),
    b.hom_C e (fun l => Real.exp (c * Real.log l.dim)),
    b.hom_P e (fun l => Real.exp (-(c * Real.log l.dim)))]
  rfl

/-- D8.29: `e^{c D_R} = e^{c(log d_V + log d_R - log d_F)}` as a function of the joint labels. -/
theorem Band.hom_mergeR (c : ℝ) :
    (b.resJ e).hom (fun p => ((Real.exp (c * (Real.log p.1.1.1.1.1.2.dim +
        Real.log p.1.1.2.dim - Real.log p.1.2.2.dim)) : ℝ) : ℂ)) =
      mergeExp ι e b.V b.R c := by
  have h : (fun p : b.Idx m r => ((Real.exp (c * (Real.log p.1.1.1.1.1.2.dim +
      Real.log p.1.1.2.dim - Real.log p.1.2.2.dim)) : ℝ) : ℂ)) =
      (fun p => ((Real.exp (c * Real.log p.1.1.1.1.1.2.dim) : ℝ) : ℂ)) *
        (fun p => ((Real.exp (c * Real.log p.1.1.2.dim) : ℝ) : ℂ)) *
        (fun p => ((Real.exp (-(c * Real.log p.1.2.2.dim)) : ℝ) : ℂ)) := by
    funext p
    simp only [Pi.mul_apply]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  rw [h, map_mul, map_mul, b.hom_V e (fun l => Real.exp (c * Real.log l.dim)),
    b.hom_R e (fun l => Real.exp (c * Real.log l.dim)),
    b.hom_F e (fun l => Real.exp (-(c * Real.log l.dim)))]
  rfl

end JointExp

/-! ### D8.30, rough -/

section ComponentRough

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
  (d : ℕ) [NeZero d] {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)

/-- D8.30.1: `⟨u_B, A^{-1} u_B⟩ ≤ poly(k) binom(k, r)^a ∑_p e^{-a(G^good + G^bad)(p)} w_p`, the
weights `w_p` of `u_B` in the joint labels of the band. -/
theorem component_inverse_weights {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (u : Transport.Config (dims n d) k → ℂ) (B : Finset (Fin k))
      (s : St) (g : Fin K),
      (star (compProj D d k B *ᵥ u) ⬝ᵥ ((Replicas.A (fun f => Fin (dims n d f)) (a / 2) k
          (Γ.P s g) (Γ.Yr s g) (Γ.F s g))⁻¹ *ᵥ (compProj D d k B *ᵥ u))).re ≤
        ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ a *
          ∑ p, Real.exp (-a * (Real.log p.1.2.1.dim + Real.log p.1.2.2.dim -
            Real.log p.1.1.1.1.2.dim + (Real.log p.2.1.1.dim + Real.log p.2.1.2.dim -
              Real.log p.2.2.dim))) *
            IsOrthogonalResolution.weight (P := (Γ.band s g).jp (ι := fun f => Fin (dims n d f))
              (split B)) (compProj D d k B *ᵥ u) p := by
  obtain ⟨C, hC, h26⟩ := step_8_26 (n := n) d Γ ha
  refine ⟨C, hC, fun k u B s g => ?_⟩
  have h1 := re_dotProduct_le_of_le (h26 k B s g) (compProj D d k B *ᵥ u)
  rw [re_dotProduct_smul_mulVec] at h1
  have hEx := (Γ.band s g).exp_eq_hom (ι := fun f => Fin (dims n d f)) (split B) a
  rw [Statuses.band_P, Statuses.band_F, show (Γ.band s g).Y = Γ.Yr s g from rfl] at hEx
  rw [hEx, re_dotProduct_hom_ofReal] at h1
  exact h1

omit [∀ v, NeZero (n v)] [NeZero d] in
/-- D8.30.1, D8.27, D8.28.3: on the support of `u_B`, the bad labels satisfy `G^bad ≥ 0`, the
physical good labels `G_phys ≥ 0`, and the good auxiliary labels are at least
`θ = log d_{λ_k} - r log d_* - log binom(k, r)`. -/
theorem support_compProj (τ : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k)))
    {u : Transport.Config (dims n d) k → ℂ} (hu : lowProj D d τ k l *ᵥ u = u)
    (B : Finset (Fin k)) (s : St) (g : Fin K) (p : (Γ.band s g).Idx Bᶜ.card B.card)
    (hw : IsOrthogonalResolution.weight (P := (Γ.band s g).jp (ι := fun f => Fin (dims n d f))
      (split B)) (compProj D d k B *ᵥ u) p ≠ 0) :
    Real.log p.2.2.dim ≤ Real.log p.2.1.1.dim + Real.log p.2.1.2.dim ∧
    Real.log p.1.1.1.1.2.dim ≤ Real.log p.1.1.1.1.1.1.dim + Real.log p.1.1.1.1.1.2.dim ∧
    Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card) ≤
      Real.log p.1.1.1.2.dim ∧
    Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card) ≤
      Real.log p.1.1.2.dim := by
  have h27 := step_8_27 d Γ D τ l hu B
  have hlog : ∀ {a b c : ℕ}, 0 < a → 0 < b → 0 < c → c ≤ a * b →
      Real.log c ≤ Real.log a + Real.log b := fun ha hb hc h => by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by exact_mod_cast hc) (by exact_mod_cast h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hne := (Γ.band s g).mulVec_ne_zero_of_weight_ne_zero (split B) hw
      ((Γ.band s g).jp_mul_g2 (split B) p)
    have h := h27.2.2 s g p.2.1.1 p.2.1.2 p.2.2
    rw [← Statuses.band_P, ← Statuses.band_F] at h
    exact hlog p.2.1.1.dim_pos p.2.1.2.dim_pos p.2.2.dim_pos (h hne)
  · have hne := (Γ.band s g).mulVec_ne_zero_of_weight_ne_zero (split B) hw
      ((Γ.band s g).jp_mul_f2 (split B) p)
    have h28 := (step_8_28 (fun f => Fin (dims n d f)) (TensorPower.groupHom₁ (split B))
      (Γ.band s g).hQC (Γ.band s g).hVR (Γ.band s g).hQV
      (Finset.disjoint_union_right.mpr ⟨(Γ.band s g).hQY.symm, (Γ.band s g).hVY.symm⟩)).2.2.2
    have hinv := mem_invariant_phys_compProj D d B u
    rw [← Yr_union_XU_union_V Γ s g] at hinv
    exact hlog p.1.1.1.1.1.1.dim_pos p.1.1.1.1.1.2.dim_pos p.1.1.1.1.2.dim_pos
      (h28 _ hinv _ _ _ hne)
  · exact h27.1 _ ((Γ.band s g).mulVec_ne_zero_of_weight_ne_zero (split B) hw
      ((Γ.band s g).jp_mul_C (split B) p))
  · exact h27.2.1 _ ((Γ.band s g).mulVec_ne_zero_of_weight_ne_zero (split B) hw
      ((Γ.band s g).jp_mul_R (split B) p))

end ComponentRough

section ComponentRoughBound

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
  (d : ℕ) [NeZero d] {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)

omit [Fintype σ] [DecidableEq σ] [∀ v, NeZero (n v)] [NeZero d] in
/-- `√A √B ≤ MT` from `A, B ≤ MT`, written with `^ 2⁻¹`. -/
private theorem rpow_half_mul_le {A B M : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ M)
    (hB : B ≤ M) : A ^ ((2 : ℝ)⁻¹) * B ^ ((2 : ℝ)⁻¹) ≤ M := by
  have hM0 : 0 ≤ M := hA0.trans hA
  rw [← one_div, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  calc √A * √B ≤ √M * √M := mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = M := Real.mul_self_sqrt hM0

/-- D8.30 (rough). `⟨u_B, A_{j,g}^{-1} u_B⟩/‖u_B‖² ≤ poly(k) exp{-2a θ + a log binom(k, r)}` with
`θ = log d_{λ_k} - r log d_* - log binom(k, r)`. -/
theorem component_inverse_rough {a : ℝ} (ha : 0 < a) (ha1 : 2 * a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k)))
      (u : Transport.Config (dims n d) k → ℂ), lowProj D d τ k l *ᵥ u = u →
      ∀ (B : Finset (Fin k)) (s : St) (g : Fin K),
      (star (compProj D d k B *ᵥ u) ⬝ᵥ ((Replicas.A (fun f => Fin (dims n d f)) (a / 2) k
          (Γ.P s g) (Γ.Yr s g) (Γ.F s g))⁻¹ *ᵥ (compProj D d k B *ᵥ u))).re ≤
        Real.exp (C * Real.log ((k : ℝ) + 2) -
          2 * a * (Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card)) +
            a * Real.log (k.choose B.card)) *
          (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re := by
  obtain ⟨C, hC, hweights⟩ := component_inverse_weights D d Γ ha
  set Q₀ := Fintype.card (SiteConfig (dims n d))
  refine ⟨C + (Q₀ ^ 2 : ℕ), by positivity, fun τ k l u hu B s g => ?_⟩
  set uB := compProj D d k B *ᵥ u
  set θ := Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card)
  set W := IsOrthogonalResolution.weight (P := (Γ.band s g).jp (ι := fun f => Fin (dims n d f))
    (split B)) uB
  have hW0 : ∀ p, 0 ≤ W p := fun p => IsOrthogonalResolution.weight_nonneg
    ((Γ.band s g).resJ (split B)) ((Γ.band s g).isHermitian_jp (split B)) uB p
  set T := (star uB ⬝ᵥ uB).re
  have hT : 0 ≤ T := (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1
  set XC : (Γ.band s g).Idx Bᶜ.card B.card → ℝ := fun p => Real.exp (a * (Real.log
    p.1.1.1.1.1.1.dim + Real.log p.1.1.1.2.dim - Real.log p.1.2.1.dim))
  set XR : (Γ.band s g).Idx Bᶜ.card B.card → ℝ := fun p => Real.exp (a * (Real.log
    p.1.1.1.1.1.2.dim + Real.log p.1.1.2.dim - Real.log p.1.2.2.dim))
  -- D8.30.1–D8.30.3 pointwise
  have hpt : ∀ p, Real.exp (-a * (Real.log p.1.2.1.dim + Real.log p.1.2.2.dim -
      Real.log p.1.1.1.1.2.dim + (Real.log p.2.1.1.dim + Real.log p.2.1.2.dim -
        Real.log p.2.2.dim))) * W p ≤ Real.exp (-(2 * a * θ)) * (W p * (XC p * XR p)) := by
    intro p
    by_cases hw : W p = 0
    · rw [hw]; simp
    obtain ⟨h1, h2, h3, h4⟩ := support_compProj D d Γ τ l hu B s g p hw
    have := rough_pointwise (lP := Real.log p.1.2.1.dim) (lF := Real.log p.1.2.2.dim) ha h1 h2 h3 h4
    calc _ ≤ Real.exp (-(2 * a * θ)) * (XC p * XR p) * W p :=
          mul_le_mul_of_nonneg_right this (hW0 p)
      _ = _ := by ring
  -- D8.30.3: Cauchy–Schwarz
  have hCS := sum_mul_prod_le_prod_rpow_sum (κ := Fin 2) (by simp) Finset.univ W ![XC, XR]
    (fun p _ => hW0 p) (fun j p _ => by fin_cases j <;> exact (Real.exp_pos _).le)
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.card_fin,
    Nat.cast_ofNat] at hCS
  -- D8.29 at `2a`
  have hmm := merge_moments_compProj D d Γ τ l hu B s g (b := 2 * a) ha1
  have hsq : ∀ (z : ℝ), Real.exp (a * z) ^ 2 = Real.exp (2 * a * z) := fun z => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hMC : ∑ p, W p * XC p ^ 2 ≤ ((k : ℝ) + 2) ^ Q₀ ^ 2 * T := by
    have h := (Γ.band s g).hom_mergeC (ι := fun f => Fin (dims n d f)) (split B) (2 * a)
    have hq := re_dotProduct_hom_ofReal ((Γ.band s g).resJ (split B)) (fun p => Real.exp (2 * a *
      (Real.log p.1.1.1.1.1.1.dim + Real.log p.1.1.1.2.dim - Real.log p.1.2.1.dim))) uB
    rw [h] at hq
    refine le_trans (le_of_eq ?_) (hq ▸ hmm.1)
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [XC, hsq, mul_comm (W p)]
    rfl
  have hMR : ∑ p, W p * XR p ^ 2 ≤ ((k : ℝ) + 2) ^ Q₀ ^ 2 * T := by
    have h := (Γ.band s g).hom_mergeR (ι := fun f => Fin (dims n d f)) (split B) (2 * a)
    have hq := re_dotProduct_hom_ofReal ((Γ.band s g).resJ (split B)) (fun p => Real.exp (2 * a *
      (Real.log p.1.1.1.1.1.2.dim + Real.log p.1.1.2.dim - Real.log p.1.2.2.dim))) uB
    rw [h] at hq
    refine le_trans (le_of_eq ?_) (hq ▸ hmm.2)
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [XR, hsq, mul_comm (W p)]
    rfl
  have hhalf := rpow_half_mul_le
    (Finset.sum_nonneg fun p _ => mul_nonneg (hW0 p) (by positivity)) hMC hMR
  -- D8.30.5: combine
  have hsum : ∑ p, Real.exp (-a * (Real.log p.1.2.1.dim + Real.log p.1.2.2.dim -
      Real.log p.1.1.1.1.2.dim + (Real.log p.2.1.1.dim + Real.log p.2.1.2.dim -
        Real.log p.2.2.dim))) * W p ≤ Real.exp (-(2 * a * θ)) * (((k : ℝ) + 2) ^ Q₀ ^ 2 * T) := by
    calc _ ≤ ∑ p, Real.exp (-(2 * a * θ)) * (W p * (XC p * XR p)) := Finset.sum_le_sum fun p _ =>
          hpt p
      _ = Real.exp (-(2 * a * θ)) * ∑ p, W p * (XC p * XR p) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hCS.trans hhalf) (Real.exp_pos _).le
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hch : (0 : ℝ) < k.choose B.card := by
    exact_mod_cast Nat.choose_pos ((Finset.card_le_univ B).trans (by simp))
  calc _ ≤ ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ a * (Real.exp (-(2 * a * θ)) *
        (((k : ℝ) + 2) ^ Q₀ ^ 2 * T)) := (hweights k u B s g).trans
          (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by
        rw [Real.rpow_def_of_pos hk2, Real.rpow_def_of_pos hch, ← Real.rpow_natCast,
          Real.rpow_def_of_pos hk2]
        rw [show Real.exp (Real.log ((k : ℝ) + 2) * C) *
            Real.exp (Real.log (k.choose B.card) * a) * (Real.exp (-(2 * a * θ)) *
              (Real.exp (Real.log ((k : ℝ) + 2) * ((Q₀ ^ 2 : ℕ) : ℝ)) * T)) =
            Real.exp (Real.log ((k : ℝ) + 2) * C + Real.log (k.choose B.card) * a +
              -(2 * a * θ) + Real.log ((k : ℝ) + 2) * ((Q₀ ^ 2 : ℕ) : ℝ)) * T by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring]
        congr 2
        ring

end ComponentRoughBound

/-! ### D8.30.4 The physical good-copy factors are in the iid state `Ω̃^{⊗k'}` -/

section PhysicalMoments

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} (D : PhysData n) (d : ℕ)

/-- `x` on `T` glued with `w` on `Tᶜ`. -/
def joinT {T : Finset σ} (a : Reg (fun v => Fin (n v)) T)
    (w : TensorPower.ComplConfig (fun v => Fin (n v)) T) : SiteConfig n :=
  fun v => if h : v ∈ T then a ⟨v, h⟩ else w ⟨v, h⟩

/-- `ρ_T(a, b) = ∑_w Ω̃(a w) Ω̃(b w)^*`. -/
theorem PhysData.ρ_apply (T : Finset σ) (a b : Reg (fun v => Fin (n v)) T) :
    D.ρ T a b = ∑ w : TensorPower.ComplConfig (fun v => Fin (n v)) T,
      D.Ω (joinT a w) * star (D.Ω (joinT b w)) := by
  let e : Reg (fun v => Fin (n v)) (Finset.univ \ T) ≃
      TensorPower.ComplConfig (fun v => Fin (n v)) T :=
    { toFun := fun z f => z ⟨f.1, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, f.2⟩⟩
      invFun := fun w f => w ⟨f.1, (Finset.mem_sdiff.1 f.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hj : ∀ (a : Reg (fun v => Fin (n v)) T) (z : Reg (fun v => Fin (n v)) (Finset.univ \ T)),
      univEquiv (glue a z) = joinT a (e z) := fun a z => by
    funext v
    by_cases hv : v ∈ T <;> simp [univEquiv_apply, glue, joinT, hv, e]
  simp only [PhysData.ρ, marg, ptrace, of_apply, vecMulVec_apply, Function.comp_apply,
    Pi.star_apply]
  exact Fintype.sum_equiv e _ _ fun z => by rw [hj, hj]

/-- One copy split: the good copies' physical configurations, their auxiliary pairs, the bad
copies. -/
noncomputable def physSplit {k : ℕ} (B : Finset (Fin k)) :
    Transport.Config (dims n d) k ≃ (Fin Bᶜ.card → SiteConfig n) ×
      ((Fin Bᶜ.card → Fin d × Fin d) × Transport.Config (dims n d) B.card) :=
  (TensorPower.copySplit (fun f => Fin (dims n d f)) (split B)).trans
    ((Equiv.prodCongr ((Equiv.arrowCongr (Equiv.refl _) (siteSplit d)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem physSplit_apply_fst {k : ℕ} (B : Finset (Fin k)) (x : Transport.Config (dims n d) k)
    (i : Fin Bᶜ.card) : (physSplit d B x).1 i = physPart (x (split B (.inl i))) := by
  simp [physSplit, Equiv.arrowCongr_apply, Equiv.arrowProdEquivProdArrow]

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem physSplit_apply_aux {k : ℕ} (B : Finset (Fin k)) (x : Transport.Config (dims n d) k)
    (i : Fin Bᶜ.card) :
    (physSplit d B x).2.1 i = (x (split B (.inl i)) .C, x (split B (.inl i)) .R) := by
  simp [physSplit, Equiv.arrowCongr_apply, Equiv.arrowProdEquivProdArrow]
  rfl

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem physSplit_apply_bad {k : ℕ} (B : Finset (Fin k)) (x : Transport.Config (dims n d) k)
    (j : Fin B.card) : (physSplit d B x).2.2 j = x (split B (.inr j)) := by
  simp [physSplit]

omit [Fintype σ] in
/-- The good permutations of a physical region `T` act on the good physical factor. -/
theorem physSplit_copyPerm {k : ℕ} (B : Finset (Fin k)) (T : Finset σ)
    (a : Equiv.Perm (Fin Bᶜ.card)) (x : Transport.Config (dims n d) k) :
    physSplit d B (Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg T)
        (TensorPower.groupHom₁ (split B) a) x) =
      PermutationRepresentation.prodLeft _ (TensorPower.subsystemPerm Bᶜ.card
        (fun v => Fin (n v)) T) a (physSplit d B x) := by
  have h1 : ∀ i, (TensorPower.groupHom₁ (split B) a)⁻¹ (split B (.inl i)) =
      split B (.inl (a⁻¹ i)) := fun i => by rw [← map_inv, TensorPower.groupHom₁_apply_inl]
  have h2 : ∀ j, (TensorPower.groupHom₁ (split B) a)⁻¹ (split B (.inr j)) = split B (.inr j) :=
    fun j => by rw [← map_inv, TensorPower.groupHom₁_apply_inr]
  refine Prod.ext (funext fun i => funext fun v => ?_) (Prod.ext (funext fun i => ?_)
    (funext fun j => ?_))
  · simp only [physSplit_apply_fst, PermutationRepresentation.prodLeft_apply,
      TensorPower.subsystemPerm_apply]
    change Replicas.copyPerm _ k _ _ x _ (Site.phys v) = _
    rw [Replicas.copyPerm_apply, h1]
    by_cases hv : v ∈ T <;> simp [hv, physPart]
  · simp only [physSplit_apply_aux, PermutationRepresentation.prodLeft_apply,
      Replicas.copyPerm_apply, C_not_mem_physReg, R_not_mem_physReg, if_false]
    rfl
  · simp only [physSplit_apply_bad, PermutationRepresentation.prodLeft_apply]
    funext f
    rw [Replicas.copyPerm_apply, h2]
    split_ifs <;> rfl

end PhysicalMoments

section PhysicalMoments2

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  (D : PhysData n) (d : ℕ)

omit [∀ v, NeZero (n v)] in
/-- The good labels of a physical region are those of the region on `(𝓗_phys)^{⊗k'}`. -/
theorem labelObservable_physSplit {k : ℕ} (B : Finset (Fin k)) (T : Finset σ)
    (f : IrrepLabel (Equiv.Perm (Fin Bᶜ.card)) → ℝ) :
    reindex (physSplit d B) (physSplit d B) (labelObservable ((Replicas.copyPerm
        (fun f => Fin (dims n d f)) k (physReg T)).comp (TensorPower.groupHom₁ (split B))) f) =
      labelObservable (TensorPower.subsystemPerm Bᶜ.card (fun v => Fin (n v)) T) f ⊗ₖ
        (1 : Matrix _ _ ℂ) := by
  refine reindex_labelObservable_eq _ (fun l => ?_) f
  rw [← labelProj_prodLeft, labelProj_of_intertwine (φ := (Replicas.copyPerm
    (fun f => Fin (dims n d f)) k (physReg T)).comp (TensorPower.groupHom₁ (split B)))
    (physSplit d B) (fun a x => (physSplit_copyPerm d B T a x).symm)]

/-- D8.24.2 in the split coordinates: `u_B(p, z) = Ω̃^{⊗k'}(p) φ(z)`. -/
theorem compProj_physSplit_symm {k : ℕ} (B : Finset (Fin k))
    (u : Transport.Config (dims n d) k → ℂ) (p : Fin Bᶜ.card → SiteConfig n)
    (z : (Fin Bᶜ.card → Fin d × Fin d) × Transport.Config (dims n d) B.card) :
    (compProj D d k B *ᵥ u) ((physSplit d B).symm (p, z)) = (∏ i, D.Ω (p i)) *
      goodRest D d k B u ((physSplit d B).symm (fun _ v => (0 : Fin (n v)), z)) := by
  have hprod : ∏ j ∈ Bᶜ, D.Ω (physPart ((physSplit d B).symm (p, z) j)) = ∏ i, D.Ω (p i) := by
    rw [← Finset.prod_coe_sort Bᶜ]
    refine Fintype.prod_equiv ((Bᶜ.equivFin).trans (Equiv.refl _)) _ _ fun j => ?_
    have hj : split B (.inl (Bᶜ.equivFin j)) = (j : Fin k) := by
      simp [split]
    have := physSplit_apply_fst d B ((physSplit d B).symm (p, z)) (Bᶜ.equivFin j)
    rw [Equiv.apply_symm_apply, hj] at this
    simp only [Equiv.trans_apply, Equiv.refl_apply]
    rw [← this]
  have hrest : goodRest D d k B u ((physSplit d B).symm (p, z)) =
      goodRest D d k B u ((physSplit d B).symm (fun _ v => (0 : Fin (n v)), z)) := by
    refine goodRest_congr D d k B u (fun j hj => ?_) fun j => ?_
    · obtain ⟨y, rfl⟩ := (split B).surjective j
      rcases y with i | i
      · exact absurd hj (split_inl B i)
      · have h1 := physSplit_apply_bad d B ((physSplit d B).symm (p, z)) i
        have h2 := physSplit_apply_bad d B
          ((physSplit d B).symm (fun _ v => (0 : Fin (n v)), z)) i
        rw [Equiv.apply_symm_apply] at h1 h2
        rw [← h1, ← h2]
    · obtain ⟨y, rfl⟩ := (split B).surjective j
      rcases y with i | i
      · have h1 := physSplit_apply_aux d B ((physSplit d B).symm (p, z)) i
        have h2 := physSplit_apply_aux d B
          ((physSplit d B).symm (fun _ v => (0 : Fin (n v)), z)) i
        rw [Equiv.apply_symm_apply] at h1 h2
        have h := h1.symm.trans h2
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · have h1 := physSplit_apply_bad d B ((physSplit d B).symm (p, z)) i
        have h2 := physSplit_apply_bad d B
          ((physSplit d B).symm (fun _ v => (0 : Fin (n v)), z)) i
        rw [Equiv.apply_symm_apply] at h1 h2
        rw [← h1, ← h2]
        exact ⟨rfl, rfl⟩
  rw [compProj_mulVec_apply, hprod, hrest]

end PhysicalMoments2

section PhysicalMoments3

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  (D : PhysData n) (d : ℕ)

omit [Fintype σ] [DecidableEq σ] [∀ v, NeZero (n v)] in
private theorem trace_vecMulVec_mul {N : Type*} [Fintype N] (ψ : N → ℂ) (M : Matrix N N ℂ) :
    (vecMulVec ψ (star ψ) * M).trace = star ψ ⬝ᵥ (M *ᵥ ψ) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [∀ v, NeZero (n v)] in
/-- `‖Ω̃^{⊗m}‖ = 1`. -/
private theorem norm_tensorVec_Ω (m : ℕ) :
    star (fun p : Fin m → SiteConfig n => ∏ i, D.Ω (p i)) ⬝ᵥ
      (fun p : Fin m → SiteConfig n => ∏ i, D.Ω (p i)) = 1 := by
  simp only [dotProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun _ q => star (D.Ω q) * D.Ω q)]
  have h : ∑ q, star (D.Ω q) * D.Ω q = 1 := D.norm_Ω
  simp only [h, Finset.prod_const_one]

omit [∀ v, NeZero (n v)] in
/-- The reduced state of `Ω̃^{⊗m}` on `T^{⊗m}` is `ρ_T^{⊗m}`. -/
private theorem reducedVec_tensorVec_Ω (m : ℕ) (T : Finset σ) :
    reducedVec (TensorPower.splitEquiv (fun v => Fin (n v)) m T)
        (fun p : Fin m → SiteConfig n => ∏ i, D.Ω (p i)) =
      TensorPower.tensorPow (k := m) (D.ρ T) := by
  ext a b
  rw [reducedVec_apply, TensorPower.tensorPow, TensorPower.partialTensor_univ_apply]
  simp only [D.ρ_apply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun z => ?_
  rw [star_prod, ← Finset.prod_mul_distrib]
  rfl

/-- D8.30.4. The physical good-copy factors of `u_B` are in the iid state `Ω̃^{⊗k'}`:
`⟨u_B, L_T(f) u_B⟩ = ‖u_B‖² Tr(ρ_T^{⊗k'} L(f))` for every label function of the good labels of
a physical region `T`. -/
theorem phys_moment {k : ℕ} (B : Finset (Fin k)) (u : Transport.Config (dims n d) k → ℂ)
    (T : Finset σ) (f : IrrepLabel (Equiv.Perm (Fin Bᶜ.card)) → ℝ) :
    (star (compProj D d k B *ᵥ u) ⬝ᵥ (labelObservable ((Replicas.copyPerm
        (fun f => Fin (dims n d f)) k (physReg T)).comp (TensorPower.groupHom₁ (split B))) f *ᵥ
          (compProj D d k B *ᵥ u))).re =
      (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re *
        (TensorPower.tensorPow (k := Bᶜ.card) (D.ρ T) *
          labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) T) Bᶜ.card)
            f).trace.re := by
  set uB := compProj D d k B *ᵥ u
  set ψ : (Fin Bᶜ.card → SiteConfig n) → ℂ := fun p => ∏ i, D.Ω (p i)
  set φ := fun z => goodRest D d k B u ((physSplit d B).symm (fun _ v => (0 : Fin (n v)), z))
  have hprod : ∀ p z, uB ((physSplit d B).symm (p, z)) = ψ p * φ z :=
    compProj_physSplit_symm D d B u
  have hρ := reducedVec_of_prod (physSplit d B) hprod
  have hψ : star ψ ⬝ᵥ ψ = 1 := norm_tensorVec_Ω D Bᶜ.card
  -- the normalization `‖u_B‖² = ‖φ‖²`
  have hn : star uB ⬝ᵥ uB = star φ ⬝ᵥ φ := by
    rw [← trace_reducedVec (physSplit d B), hρ, trace_smul, trace_vecMulVec,
      dotProduct_comm ψ, hψ, smul_eq_mul, mul_one]
  -- the second reduction to `T^{⊗k'}`
  have hM := reindex_labelObservable_eq (TensorPower.splitEquiv (fun v => Fin (n v)) Bᶜ.card T)
    (fun l => TensorPower.labelProj_subsystemPerm_eq (fun v => Fin (n v)) Bᶜ.card T l) f
  have h2 := dotProduct_mulVec_eq_trace_reducedVec _ ψ hM
  rw [reducedVec_tensorVec_Ω] at h2
  rw [dotProduct_mulVec_eq_trace_reducedVec (physSplit d B) uB (labelObservable_physSplit d B T f),
    hρ, smul_mul_assoc, trace_smul, trace_vecMulVec_mul, h2, hn, smul_eq_mul]
  have hφ : star φ ⬝ᵥ φ = ((star φ ⬝ᵥ φ).re : ℂ) := by
    have hnn := dotProduct_star_self_nonneg φ
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hnn).2.symm)
  rw [hφ, Complex.re_ofReal_mul]
  rfl

end PhysicalMoments3

/-! ### D8.30.4 The physical factors through D8.10 -/

section PhysicalBound

/-- `L(c f) = c L(f)`. -/
theorem labelObservable_const_mul {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    (φ : G →* Equiv.Perm X) (c : ℝ) (f : IrrepLabel G → ℝ) :
    labelObservable φ (fun l => c * f l) = (c : ℂ) • labelObservable φ f := by
  simp only [labelObservable, Finset.smul_sum, smul_smul, Complex.ofReal_mul]

/-- `g(L(f)) = L(g ∘ f)` for the continuous functional calculus. -/
theorem cfc_labelObservable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    (φ : G →* Equiv.Perm X) (g : ℝ → ℝ) (f : IrrepLabel G → ℝ) :
    cfc g (labelObservable φ f) = labelObservable φ (fun l => g (f l)) := by
  rw [labelObservable_eq_hom, labelObservable_eq_hom,
    (isOrthogonalResolution_labelProj φ).cfc_hom (isHermitian_labelProj φ)]

/-- `log x ≤ B ⇒ x ≤ e^B`. -/
theorem le_exp_of_log_le {x B : ℝ} (h : Real.log x ≤ B) : x ≤ Real.exp B := by
  rcases le_or_gt x 0 with hx | hx
  · exact hx.trans (Real.exp_pos _).le
  · rw [← Real.exp_log hx]
    exact Real.exp_le_exp.mpr h

end PhysicalBound

section PhysicalBoundSite

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  (D : PhysData n) (d : ℕ)

/-- D8.30.4, with D8.10: for a physical region `T` whose marginal satisfies `comparator:mgf-data`,
`⟨u_B, e^{ε b F_T} u_B⟩ ≤ ‖u_B‖² exp{ε b k' S(T) + 2 C₀ k' 𝓑 b² + C + N log(k' + 1)}`. -/
theorem phys_bound {C₀ c₀ c : ℝ}
    (hP : ∀ {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef),
      ρ.trace = 1 → ∀ 𝓑 S : ℝ, 1 ≤ 𝓑 →
      (∀ u : ℝ, |u| ≤ c₀ / Real.sqrt 𝓑 → Real.log (trPowPos ρ hρ.isHermitian u) ≤
        u * S + C₀ * 𝓑 * u ^ 2) →
      ∃ Cp Np : ℝ, ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ c / Real.sqrt 𝓑 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        Real.log (trace (TensorPower.tensorPow (k := k) ρ *
            cfc (fun x => Real.exp (ε * u * (x - k * S)))
              (labelObservable (TensorPower.copyPerm Ω k) fun l => Real.log l.dim))).re ≤
          2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1))
    {𝓑 : ℝ} (h𝓑 : 1 ≤ 𝓑) (T : Finset σ)
    (hmgf : ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt 𝓑 → Real.log (D.trPow T u) ≤ u * D.S T + C₀ * 𝓑 * u ^ 2) :
    ∃ Cp Np : ℝ, ∀ (k : ℕ) (B : Finset (Fin k)) (u : Transport.Config (dims n d) k → ℂ) (b : ℝ),
      0 ≤ b → b ≤ c / Real.sqrt 𝓑 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (star (compProj D d k B *ᵥ u) ⬝ᵥ (labelObservable ((Replicas.copyPerm
          (fun f => Fin (dims n d f)) k (physReg T)).comp (TensorPower.groupHom₁ (split B)))
            (fun l => Real.exp (ε * b * Real.log l.dim)) *ᵥ (compProj D d k B *ᵥ u))).re ≤
        (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re *
          Real.exp (ε * b * Bᶜ.card * D.S T + 2 * C₀ * Bᶜ.card * 𝓑 * b ^ 2 + Cp +
            Np * Real.log (Bᶜ.card + 1)) := by
  have htr : (D.ρ T).trace = 1 := by
    rw [PhysData.ρ, trace_marg, D.norm_Ω_univEquiv]
  obtain ⟨Cp, Np, h⟩ := hP (D.ρ T) (posSemidef_marg _ _) htr 𝓑 (D.S T) h𝓑 hmgf
  refine ⟨Cp, Np, fun k B u b hb0 hb ε hε => ?_⟩
  set m := Bᶜ.card
  have hlog := h m b hb0 hb ε hε
  rw [cfc_labelObservable] at hlog
  have hexp := le_exp_of_log_le hlog
  have hsplit : (fun l : IrrepLabel (Equiv.Perm (Fin m)) => Real.exp (ε * b * Real.log l.dim)) =
      fun l => Real.exp (ε * b * m * D.S T) *
        Real.exp (ε * b * (Real.log l.dim - m * D.S T)) := by
    funext l
    rw [← Real.exp_add]
    congr 1
    ring
  rw [phys_moment D d B u T, hsplit, labelObservable_const_mul, mul_smul_comm, trace_smul,
    smul_eq_mul, Complex.re_ofReal_mul]
  have hT : 0 ≤ (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re :=
    (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1
  refine mul_le_mul_of_nonneg_left ?_ hT
  rw [show ε * b * m * D.S T + 2 * C₀ * m * 𝓑 * b ^ 2 + Cp + Np * Real.log (m + 1) =
    ε * b * m * D.S T + (2 * C₀ * m * 𝓑 * b ^ 2 + Cp + Np * Real.log (m + 1)) by ring,
    Real.exp_add]
  exact mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le

end PhysicalBoundSite

end AreaLaw.Comparators
