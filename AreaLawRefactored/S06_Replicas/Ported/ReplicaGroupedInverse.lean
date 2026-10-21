/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.Analysis.Matrix.CommutingExponentialOrder
import AreaLawRefactored.S06_Replicas.Ported.GroupedLabelEntropy
import AreaLawRefactored.S06_Replicas.Ported.ReplicaWholeInverse

/-!
# The inverse replica metric after splitting the copies

Splitting the copies into good and bad groups costs exactly `choose(k,r)^{2t}` in the inverse
squared replica metric (`07-comparators.tex`, lines 454--476).
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

private theorem commute_whole_subgroup_labelEntropy
    {H : Type*} [Group H] [Fintype H] (k : ℕ)
    (θ : H →* Equiv.Perm (Fin k)) (S T : Finset V)
    (hST : S = T ∨ Disjoint S T) :
    Commute (labelEntropy (subsystemPerm k ι S))
      (labelEntropy ((subsystemPerm k ι T).comp θ)) := by
  rcases hST with rfl | hST
  · exact (Commute.sum_left _ _ _ fun ell _ => Commute.sum_right _ _ _ fun ell' _ =>
      ((commute_labelProj_comp _ θ ell ell').smul_left _).smul_right _).symm
  · exact commute_labelObservable_of_commute _ _
      (fun σ τ => commute_subsystemPerm_of_disjoint k ι hST σ (θ τ)) _ _

/-- The whole signed label exponential is bounded by the grouped exponential with the
binomial loss. -/
theorem exp_neg_whole_labelEntropy_le_exp_grouped
    {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (P Y F : Finset V) (hPY : Disjoint P Y) (hPF : Disjoint P F)
    (hYF : Disjoint Y F) {a : ℝ} (ha : 0 ≤ a) :
    let L := fun S => labelEntropy (subsystemPerm k ι S)
    let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
    let Lb := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₂ e))
    NormedSpace.exp ((-a) • (L P + L F - L Y)) ≤
      (k.choose r : ℝ) ^ a • NormedSpace.exp
        ((-a) • ((Lg P + Lg F - Lg Y) + (Lb P + Lb F - Lb Y))) := by
  intro L Lg Lb
  let D := fun S => Lg S + Lb S
  let Gw := L P + L F - L Y
  let Gs := D P + D F - D Y
  let q := Real.log (k.choose r : ℝ)
  have horder : Gs - q • (1 : Matrix (Config k ι) (Config k ι) ℂ) ≤ Gw := by
    have hP := (groupedCopies_labelEntropy_bounds e (subsystemPerm k ι P)).1
    have hF := (groupedCopies_labelEntropy_bounds e (subsystemPerm k ι F)).1
    have hY := (groupedCopies_labelEntropy_bounds e (subsystemPerm k ι Y)).2
    simpa only [Gs, Gw, D, L, Lg, Lb, q, Complex.coe_smul, sub_add_eq_sub_sub] using
      sub_le_sub (add_le_add hP hF) hY
  have hc (S T : Finset V) (hST : S = T ∨ Disjoint S T) : Commute (L S) (D T) :=
    (commute_whole_subgroup_labelEntropy ι k (groupHom₁ e) S T hST).add_right
      (commute_whole_subgroup_labelEntropy ι k (groupHom₂ e) S T hST)
  have hrow (S : Finset V) (hSP : S = P ∨ Disjoint S P)
      (hSF : S = F ∨ Disjoint S F) (hSY : S = Y ∨ Disjoint S Y) :
      Commute (L S) Gs :=
    ((hc S P hSP).add_right (hc S F hSF)).sub_right (hc S Y hSY)
  have hcomm : Commute Gw Gs :=
    ((hrow P (Or.inl rfl) (Or.inr hPF) (Or.inr hPY)).add_left
      (hrow F (Or.inr hPF.symm) (Or.inl rfl) (Or.inr hYF.symm))).sub_left
        (hrow Y (Or.inr hPY.symm) (Or.inr hYF) (Or.inl rfl))
  have hL (S : Finset V) : (L S).IsHermitian := isHermitian_labelObservable _ _
  have hD (S : Finset V) : (D S).IsHermitian :=
    (isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)
  have hGw : Gw.IsHermitian := ((hL P).add (hL F)).sub (hL Y)
  have hGs : Gs.IsHermitian := ((hD P).add (hD F)).sub (hD Y)
  have hscaled : (-a) • Gw ≤ (a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) +
      (-a) • Gs := by
    simpa only [sub_eq_add_neg, smul_add, smul_neg, smul_smul,
      neg_add_rev, neg_neg, neg_smul] using neg_le_neg (smul_le_smul_of_nonneg_left horder ha)
  have hleft : ((-a) • Gw).IsHermitian := hGw.smul (by simp [IsSelfAdjoint])
  have hright : ((a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) +
      (-a) • Gs).IsHermitian :=
    (isHermitian_one.smul (by simp [IsSelfAdjoint])).add
      (hGs.smul (by simp [IsSelfAdjoint]))
  have hscaledcomm : Commute ((-a) • Gw)
      ((a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) + (-a) • Gs) :=
    ((Commute.one_right _).smul_right _).add_right
      ((hcomm.smul_left _).smul_right _)
  have hexp := hleft.exp_le_exp_of_commute hright hscaledcomm hscaled
  have hscalar : NormedSpace.exp ((a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ)) =
      Real.exp (a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ)
        (𝔸 := Matrix (Config k ι) (Config k ι) ℂ) (a * q)).symm
  have hk : m + r = k := by simpa using Fintype.card_congr e
  have hscalar' : Real.exp (a * q) = (k.choose r : ℝ) ^ a := by
    rw [Real.rpow_def_of_pos (mod_cast Nat.choose_pos (show r ≤ k by omega)), mul_comm]
  rw [Matrix.exp_add_of_commute _ _
    ((Commute.one_left ((-a) • Gs)).smul_left (a * q)),
    hscalar, hscalar', smul_mul_assoc, one_mul] at hexp
  have hGs' : Gs = (Lg P + Lg F - Lg Y) + (Lb P + Lb F - Lb Y) := by dsimp only [Gs, D]; abel
  simpa only [Gw, hGs'] using hexp

variable [∀ v, Nonempty (ι v)]

/-- The inverse squared replica metric admits the grouped-copy bound with binomial power `2t`
(`07-comparators.tex`, `comparator:whole-inverse`). -/
theorem exists_replicaMetric_inv_square_le_grouped_exp {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m r k : ℕ) (e : Fin m ⊕ Fin r ≃ Fin k)
      (P Y F : Finset V), Disjoint P Y → Disjoint P F → Disjoint Y F →
      let W := replicaMetric ι t k
      let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
      let Lb := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₂ e))
      (((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2)⁻¹ ≤
        (((k : ℝ) + 2) ^ C * (k.choose r : ℝ) ^ (2 * t)) •
          NormedSpace.exp ((-(2 * t)) •
            ((Lg P + Lg F - Lg Y) + (Lb P + Lb F - Lb Y))) := by
  obtain ⟨C, hC, hwhole⟩ := exists_replicaMetric_inv_square_le_exp ι ht
  refine ⟨C, hC, fun m r k e P Y F hPY hPF hYF => ?_⟩
  have h := smul_le_smul_of_nonneg_left (exp_neg_whole_labelEntropy_le_exp_grouped ι e P Y F
    hPY hPF hYF (show 0 ≤ 2 * t by positivity))
    (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ) + 2) C)
  have hwhole' := hwhole k P Y F hPY hPF hYF
  simp only [Complex.coe_smul] at hwhole'
  exact hwhole'.trans (by simpa only [smul_smul] using h)

end TensorPower
