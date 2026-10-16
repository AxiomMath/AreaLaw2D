/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Representation/ReplicaTransport/SymmetricMetricFloor.lean` (Apache 2.0).
Imports resolved to the repo's ports. The repo's `OpenAI.ReplicaSymmetricMetricFloor` omits
QICLean's `TensorPower.exists_replicaMetric_symmetric_floor`, which the first theorem uses; it
is added here with the source's statement and a new proof from
`TensorPower.exists_replicaMetric_symProj_inverse_bound_and_floor` and
`Matrix.identity_extension_floor`, so the unported `ReplicaSymmetricSupport` is not needed.
In `exists_symBandMetric_floor`, `mul_assoc` is written `_root_.mul_assoc`: inside
`TensorPower` it resolves to Mathlib's `TensorPower.mul_assoc`.
-/
import OpenAI.ReplicaSymmetricMetricFloor
import OpenAI.ReplicaTransportSymmetricMetric
import OpenAI.FiniteMeanTree
import OpenAI.FloorPin
import OpenAI.PosSemidefCommute

/-!
# Uniform floors for symmetric band metrics and their mean trees

The symmetric band metric is the existing partition metric on complete
symmetric copies, extended by the identity on their orthogonal complement.
A single polynomial exponent bounds these matrices below, uniformly in the
copy number and the partition. Monotonicity gives the same floor for any
finite mean tree of such matrices.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
`05-replicas.tex`, equations `replicas:leaf-metric` and
`replicas:leaf-floor`, lines 452–465; `06-transport.tex`,
`transport:band-metric`, lines 251–258, and `transport:means`, lines 40–62;
`07-comparators.tex`, lines 603–621.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
  [∀ v, Nonempty (ι v)]

/-- The same polynomial exponent gives the compressed inverse bound,
the symmetric-sector floor, and the floor after identity extension.
The exponent is uniform in the copy number and in the partition.
This is the symmetric restriction of the inverse comparison in OpenAI,
`07-comparators.tex`, lines 454–476, using complementary labels and merge
dimensions from `05-replicas.tex`, Lemma 6.1(2–3), lines 99–115.
-/
theorem exists_replicaMetric_symmetric_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V),
      Disjoint P Y → Disjoint P F → Disjoint Y F →
      P ∪ Y ∪ F = Finset.univ →
      let S := symProj (copyPerm ((v : V) → ι v) k)
      let W := replicaMetric ι t k
      let A := ((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2
      let c : ℝ := ((k : ℝ) + 2) ^ (-C)
      0 < c ∧ c ≤ 1 ∧
        S * A⁻¹ * S ≤ ((c⁻¹ : ℝ) : ℂ) • S ∧
        (c : ℂ) • S ≤ S * A * S ∧
        (c : ℂ) • (1 : Matrix _ _ ℂ) ≤ S * A * S + (1 - S) := by
  obtain ⟨C, hC, hmetric⟩ := exists_replicaMetric_symProj_inverse_bound_and_floor ι ht
  refine ⟨C, hC, ?_⟩
  intro k P Y F hPY hPF hYF hcover S W A c
  obtain ⟨hinv, hfloorA⟩ := hmetric k P Y F hPY hPF hYF hcover
  have hSproj : IsStarProjection S := isStarProjection_symProj _
  have hc : 0 < c ∧ c ≤ 1 :=
    ⟨Real.rpow_pos_of_pos (by positivity) (-C),
      Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) (neg_nonpos.mpr hC)⟩
  have hcinv : c⁻¹ = ((k : ℝ) + 2) ^ C := by
    simp only [c, Real.rpow_neg (by positivity : 0 ≤ (k : ℝ) + 2), inv_inv]
  have hfloor : c • S ≤ S * A * S := by
    have h : S * (c • S) * S ≤ S * A * S :=
      hSproj.isSelfAdjoint.conjugate_le_conjugate hfloorA
    rwa [Matrix.mul_smul, Matrix.smul_mul, hSproj.isIdempotentElem.eq,
      hSproj.isIdempotentElem.eq] at h
  have hext := Matrix.identity_extension_floor hSproj.le_one hc.2 hfloor
  refine ⟨hc.1, hc.2, ?_, ?_, ?_⟩
  · simpa only [hcinv, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hinv
  · simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hfloor
  · simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hext

end TensorPower

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V]
  (n : V → ℕ) [∀ v, NeZero (n v)]

/-- The identity extension of every actual partition metric has one
polynomial floor, with the exponent chosen before the copy number or the
partition. OpenAI, `05-replicas.tex`, `replicas:leaf-floor`, lines 452–465;
`06-transport.tex`, `transport:band-metric`, lines 251–258. -/
theorem exists_symBandMetric_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (π : PYF V), π.IsPartition →
      ((k : ℝ) + 2) ^ (-C) •
        (1 : Matrix (Config k fun v => Fin (n v))
          (Config k fun v => Fin (n v)) ℂ) ≤ symBandMetric n t k π := by
  obtain ⟨C, hC, hbound⟩ :=
    TensorPower.exists_replicaMetric_symmetric_floor (fun v => Fin (n v)) ht
  refine ⟨C, hC, ?_⟩
  rintro k π ⟨hPY, hPF, hYF, hcover⟩
  have hfloor := (hbound k π.P π.Y π.F hPY hPF hYF hcover).2.2.2.2
  change _ ≤
    symProj (copyPerm (Entropy.SiteConfig n) k) * bandMetric n t k π *
      symProj (copyPerm (Entropy.SiteConfig n) k) +
        (1 - symProj (copyPerm (Entropy.SiteConfig n) k)) at hfloor
  rw [_root_.mul_assoc, ← (commute_symProj_bandMetric (n := n) t k π).eq,
    ← _root_.mul_assoc, symProj_mul_symProj] at hfloor
  simpa only [symBandMetric, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hfloor

/-- Every finite mean tree of actual symmetric partition metrics has a
polynomial floor uniform in its copy number, partitions and interpolation
parameters. The exponent is chosen before the label type and tree.
OpenAI, `06-transport.tex`, `transport:means`, lines 40–62, and
`07-comparators.tex`, lines 603–621.
-/
theorem exists_meanTree_symBandMetric_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) {J : Type*} (π : J → PYF V),
      (∀ j, (π j).IsPartition) → ∀ T : Matrix.MeanTree J,
      ((k : ℝ) + 2) ^ (-C) •
        (1 : Matrix (Config k fun v => Fin (n v))
          (Config k fun v => Fin (n v)) ℂ) ≤
            T.eval (fun j => symBandMetric n t k (π j)) := by
  obtain ⟨C, hC, hfloor⟩ := exists_symBandMetric_floor n ht
  refine ⟨C, hC, ?_⟩
  intro k J π hπ T
  have hc : 0 < ((k : ℝ) + 2) ^ (-C) :=
    Real.rpow_pos_of_pos (by positivity) (-C)
  have hI : (((k : ℝ) + 2) ^ (-C) •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ)).PosDef := PosDef.one.smul hc
  simpa only [T.eval_const hI] using
    T.eval_mono (fun _ => hI) (fun j => hfloor k (π j) (hπ j))

/-- A fixed number of commuting band factors has a polynomial lower bound
uniform over all finite mean trees, copy counts, partitions and parameters.
Auxiliary product estimate for OpenAI, `05-replicas.tex`, `replicas:leaf-floor`,
lines 452--465, and `06-transport.tex`, `transport:means`, lines 40--62. -/
theorem exists_meanTree_symBandMetric_prod_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K k : ℕ) {J : Type*} (π : J → Fin K → PYF V),
      (∀ j g, (π j g).IsPartition) →
      (∀ j, (List.ofFn fun g => symBandMetric n t k (π j g)).Pairwise
        fun A B => Commute A B) → ∀ T : Matrix.MeanTree J,
      ((k : ℝ) + 2) ^ (-(C * (K : ℝ))) •
        (1 : Matrix (Config k fun v => Fin (n v))
          (Config k fun v => Fin (n v)) ℂ) ≤
            T.eval (fun j => (List.ofFn fun g => symBandMetric n t k (π j g)).prod) := by
  classical
  obtain ⟨C, hC, hfloor⟩ := exists_symBandMetric_floor n ht
  refine ⟨C, hC, ?_⟩
  intro K k J π hπ hcomm T
  have hleaf : ∀ j, (((k : ℝ) + 2) ^ (-C)) ^ K •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ) ≤
      (List.ofFn fun g => symBandMetric n t k (π j g)).prod := fun j => by
    simpa only [List.length_ofFn] using Matrix.pow_smul_one_le_list_prod
      (Real.rpow_nonneg (by positivity) (-C))
      (List.forall_mem_ofFn_iff.mpr fun g => hfloor k (π j g) (hπ j g))
      (hcomm j)
  have hinput : ∀ j, ((k : ℝ) + 2) ^ (-(C * (K : ℝ))) •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ) ≤
      (List.ofFn fun g => symBandMetric n t k (π j g)).prod := fun j => by
    simpa only [← Real.rpow_mul_natCast (show 0 ≤ (k : ℝ) + 2 by positivity),
      neg_mul] using hleaf j
  have hI : (((k : ℝ) + 2) ^ (-(C * (K : ℝ))) •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ)).PosDef :=
    PosDef.one.smul (Real.rpow_pos_of_pos (by positivity) _)
  simpa only [T.eval_const hI] using T.eval_mono (fun _ => hI) hinput

end TensorPower.ReplicaTransport
