/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLaw.S06_Replicas.Ported.ReplicaSpectralLaw
import AreaLaw.S06_Replicas.Ported.ReplicaMetric
import AreaLawForMathlib.Analysis.Matrix.TraceCompression
import AreaLawForMathlib.Analysis.Matrix.MatrixPowers

/-!
# The integral representation of the replica metrics

`W_{Q,k} = ∫ (τ^t)^{⊗k}` for a random positive definite subdensity `τ` on `Q` independent of `k`
(`05-replicas.tex`, equation `replicas:W-integral`).

Ported from `LionSR/QICLean`, `QICLean/Representation/ReplicaIntegral.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/

open MeasureTheory Matrix Finset PermutationRepresentation Partition
open scoped MatrixOrder ComplexOrder Kronecker

namespace TensorPower

/-- Restriction of the group algebra action along an injection of one-copy spaces. -/
theorem groupAlgebraRep_comp_embedding {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] (j : Ω' ↪ Ω) {k : ℕ}
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (b b' : Fin k → Ω') :
    groupAlgebraRep (copyPerm Ω k) a (j ∘ b) (j ∘ b') =
      groupAlgebraRep (copyPerm Ω' k) a b b' := by
  rw [groupAlgebraRep_eq_sum, groupAlgebraRep_eq_sum, Matrix.sum_apply, Matrix.sum_apply]
  refine sum_congr rfl fun g _ => ?_
  simp only [Matrix.smul_apply, permOp_apply_apply]
  congr 2
  rw [show copyPerm Ω k g (j ∘ b') = j ∘ copyPerm Ω' k g b' from rfl]
  exact propext (j.injective.comp_left).eq_iff

variable {d : ℕ}

/-- The compressed sample `τ = (E† σ^t E)^{1/t}` on the coordinates in the range of `j`. -/
noncomputable def subSample {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (j : Ω' ↪ Fin d)
    (t : ℝ) (ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ) : Matrix Ω' Ω' ℂ :=
  ((specSample ω.1 ω.2 ^ t).submatrix j j) ^ (1 / t)

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-- An injection of the configurations of a subsystem into `Fin d`, `d = dim V`. -/
noncomputable def subEmbedding [∀ f, Nonempty (ι f)] (Q : Finset F) :
    SubConfig ι Q ↪ Fin (replicaDim ι) :=
  (Fintype.equivFin (SubConfig ι Q)).toEmbedding.trans (Fin.castLEEmb (card_subConfig_le ι Q))

/-- Lemma 6.2: for `0 < t ≤ 1` there is a random positive definite subdensity `τ` on `Q`,
independent of `k`, with `W_{Q,k} = ∫ (τ^t)^{⊗k} ⊗ 1` for every `k`. -/
theorem exists_replicaMetric_integral [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (Q : Finset F) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ τ : Ω → Matrix (SubConfig ι Q) (SubConfig ι Q) ℂ,
        (∀ᵐ ω ∂P, (τ ω).PosDef ∧ (τ ω).trace.re ≤ 1) ∧
        (∀ (k : ℕ) (a b : Fin k → SubConfig ι Q),
          Integrable (fun ω => tensorPow (k := k) (τ ω ^ t) a b) P) ∧
        ∀ k : ℕ, reindex (splitEquiv ι k Q) (splitEquiv ι k Q) (replicaMetric ι t k Q) =
          (Matrix.of fun a b => ∫ ω, tensorPow (k := k) (τ ω ^ t) a b ∂P) ⊗ₖ
            (1 : Matrix (Fin k → ComplConfig ι Q) (Fin k → ComplConfig ι Q) ℂ) := by
  set d := replicaDim ι
  have hd : 0 < d := replicaDim_pos ι
  set j := subEmbedding ι Q
  have hprob := isProbabilityMeasure_specMeasure hd ht0
  have hC {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) (U : unitaryGroup (Fin d) ℂ) :
      ((specSample x U ^ t).submatrix j j).PosDef :=
    ((specSample_posDef hd hx U).rpow t).submatrix j.injective
  have hentry : ∀ (k : ℕ) (a b : Fin k → SubConfig ι Q),
      (fun ω => tensorPow (k := k) (subSample j t ω ^ t) a b) =ᵐ[(specMeasure d t).prod
        (unitaryHaar (Fin d))] fun ω => tensorPow (k := k) (specSample ω.1 ω.2 ^ t) (j ∘ a)
          (j ∘ b) := fun k a b => by
    filter_upwards [ae_prod_pos] with ω hω
    rw [subSample, (hC hω ω.2).rpow_rpow, one_div, inv_mul_cancel₀ ht0.ne', (hC hω ω.2).rpow_one]
    simp [tensorPow_apply]
  refine ⟨(Fin d → ℝ) × unitaryGroup (Fin d) ℂ, inferInstance,
    (specMeasure d t).prod (unitaryHaar (Fin d)), inferInstance, subSample j t, ?_, ?_, ?_⟩
  · filter_upwards [ae_prod_pos] with ω hω
    refine ⟨(hC hω ω.2).rpow _, ?_⟩
    have hσ := specSample_posDef hd hω ω.2
    have h := re_trace_rpow_submatrix_le (hσ.rpow t).posSemidef j
      (by rw [le_div_iff₀ ht0]; linarith : 1 ≤ 1 / t)
    rwa [hσ.rpow_rpow, mul_one_div_cancel ht0.ne', hσ.rpow_one, trace_specSample hd hω ω.2,
      Complex.one_re] at h
  · exact fun k a b => ((integral_specSample_tensorPow hd ht0 (j ∘ a) (j ∘ b)).1).congr
      (hentry k a b).symm
  intro k
  have hW : reindex (splitEquiv ι k Q) (splitEquiv ι k Q) (replicaMetric ι t k Q) =
      (∑ l, ((replicaLabelWeight ι t l : ℝ) : ℂ) • labelProj (copyPerm (SubConfig ι Q) k) l) ⊗ₖ
        (1 : Matrix (Fin k → ComplConfig ι Q) (Fin k → ComplConfig ι Q) ℂ) := by
    ext p p'
    simp only [replicaMetric, labelObservable, reindex_apply, submatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply, kroneckerMap_apply, Finset.sum_mul, smul_eq_mul]
    refine sum_congr rfl fun l _ => ?_
    have h := congrFun (congrFun (labelProj_subsystemPerm_eq ι k Q l) p) p'
    simp only [reindex_apply, submatrix_apply, kroneckerMap_apply] at h
    rw [h, mul_assoc]
  rw [hW]
  congr 1
  ext a b
  rw [of_apply, integral_congr_ae (hentry k a b),
    (integral_specSample_tensorPow hd ht0 (j ∘ a) (j ∘ b)).2, Matrix.sum_apply]
  refine sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, show labelProj (copyPerm (Fin d) k) l (j ∘ a) (j ∘ b) =
    labelProj (copyPerm (SubConfig ι Q) k) l a b from groupAlgebraRep_comp_embedding j _ a b]
  rfl

end TensorPower
