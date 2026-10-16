/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/AugmentedReceivingRegions.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. TNLean's `Site Λ` is written
`↥(Λ : Set (ℤ × ℤ))`, following `OpenAI.Scan.ReceivingRegions`.
-/
import OpenAI.Scan.ReceivingRegions
import OpenAI.Scan.AugmentedPartition

/-!
# Augmented receiving regions of finite collar histories

Let X be the intersection of the chosen color with the target. For a completed
history, or immediately after its next fill and before its charge, let U be the
positive-depth part of the physical near region and Y the physical middle. The
augmented near region is C together with X ∪ U, the augmented middle is Y, and
the augmented far region is R together with the physical complement of
X ∪ (U ∪ Y). The physical sites enter the augmented domain by the left inclusion;
C and R are the two right-inclusion sites labelled false and true.

## Main statements

- `OpenAI.Scan.CollarScan.state_augmentedPartition_eq_target_near_middle`: the three
  augmented regions after a completed history.
- `OpenAI.Scan.CollarScan.oldChargeState_augmentedPartition_eq_target_near_middle`: the
  regions after the next fill and before its charge.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 21–24 and 83–98, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI.Scan.CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The full augmented partition of an actual completed history consists of the
chosen-color target and positive near region with C, the actual middle, and their
physical complement with R. Source: OpenAI, A two-dimensional area law from a global
spectral gap, 08-scanner.tex, lines 21–24 and 83–98, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem state_augmentedPartition_eq_target_near_middle
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Λ : Set (ℤ × ℤ)) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X : Finset (↥(Λ : Set (ℤ × ℤ))) := S.A.filter fun x ↦ x.val ∈ T
    let σ : PhysicalPartition (↥(Λ : Set (ℤ × ℤ))) := S.state h g
    let U : Finset (↥(Λ : Set (ℤ × ℤ))) := positiveNear S.depth σ
    let Y : Finset (↥(Λ : Set (ℤ × ℤ))) := middle σ
    augmentedPartition σ =
      ({ P := insert (Sum.inr false)
           ((X ∪ U).image
             (Sum.inl : ↥(Λ : Set (ℤ × ℤ)) → ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool))
         Y := Y.image (Sum.inl : ↥(Λ : Set (ℤ × ℤ)) → ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool)
         F := insert (Sum.inr true)
           (((X ∪ (U ∪ Y))ᶜ).image
             (Sum.inl : ↥(Λ : Set (ℤ × ℤ)) → ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool)) } :
        TensorPower.ReplicaTransport.PYF (↥(Λ : Set (ℤ × ℤ)) ⊕ Bool)) := by
  simpa only [←(state_receiving_regions hT S hdepth h g).1,
    ←Finset.union_assoc, (state_receiving_regions hT S hdepth h g).2.1,
    ←(state_receiving_regions hT S hdepth h g).2.2] using
      (augmentedPartition_eq_images (S.state h g))

/-- The full augmented partition after an actual fill and before its charge consists
of the chosen-color target and positive near region with C, the actual middle, and their
physical complement with R. Source: OpenAI, A two-dimensional area law from a global
spectral gap, 08-scanner.tex, lines 21–24 and 83–98, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem oldChargeState_augmentedPartition_eq_target_near_middle
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Λ : Set (ℤ × ℤ)) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X : Finset (↥(Λ : Set (ℤ × ℤ))) := S.A.filter fun x ↦ x.val ∈ T
    let σ : PhysicalPartition (↥(Λ : Set (ℤ × ℤ))) := S.oldChargeState h g
    let U : Finset (↥(Λ : Set (ℤ × ℤ))) := positiveNear S.depth σ
    let Y : Finset (↥(Λ : Set (ℤ × ℤ))) := middle σ
    augmentedPartition σ =
      ({ P := insert (Sum.inr false)
           ((X ∪ U).image
             (Sum.inl : ↥(Λ : Set (ℤ × ℤ)) → ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool))
         Y := Y.image (Sum.inl : ↥(Λ : Set (ℤ × ℤ)) → ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool)
         F := insert (Sum.inr true)
           (((X ∪ (U ∪ Y))ᶜ).image
             (Sum.inl : ↥(Λ : Set (ℤ × ℤ)) → ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool)) } :
        TensorPower.ReplicaTransport.PYF (↥(Λ : Set (ℤ × ℤ)) ⊕ Bool)) := by
  simpa only [←(oldChargeState_receiving_regions hT S hdepth h g).1,
    ←Finset.union_assoc, (oldChargeState_receiving_regions hT S hdepth h g).2.1,
    ←(oldChargeState_receiving_regions hT S hdepth h g).2.2] using
      (augmentedPartition_eq_images (S.oldChargeState h g))

end OpenAI.Scan.CollarScan
