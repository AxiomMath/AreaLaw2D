/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/ActualChargeEnergyBound.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to this project's
encodings, as in `OpenAI.Scan.ActualScanMeasures`: TNLean's `Site Λ` and `domainGraph Λ` are
`↥(Λ : Set (ℤ × ℤ))` and `(hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))`,
`Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, the labels
`AdmissibleSupport Λ R` are `↥(supports Λ R)`, the state space `StateSpace Λ q` is
`EuclideanSpace ℂ (Reg (Qudits q) Λ)`, and the bundled `LocalHamiltonian Λ q R J` is an
interaction `Φ`, so `S.actualEnergyTerms h Ω Δ L aux` is `S.actualEnergyTerms Φ Ω J Δ L aux`.
The bound uses no admissibility of `Φ`, so none is assumed. The source's pointer to
`docs/paper-gaps/arealaw2d_scanner_inputs.tex` is kept as a reference to TNLean.
-/
import OpenAI.Scan.ActualRoundSplits
import OpenAI.Scan.EnergyBalance
import OpenAI.Scan.SplitEntropyBound
import OpenAI.Scan.SplitCounting
import OpenAI.Scan.TransportDimension

/-!
# Actual charge energy from the literal entropy defect

The actual charge trees and their Fourier–coherent leaf measures satisfy the
energy Hölder estimate. Geometry supplies labelled split counts and unconditional
dilution. Physical-only support dimensions supply the entropy cap independently
of both auxiliary dimensions. The old and new measures each have mass one half,
derived for the same nonzero symmetric supplied vector.

The bound retains the classical bad-old-history probability, the interpolation
factors, and the literal charge defect. No positive band count or split capacity
is imposed, and no capacity is divided out. This is a supplied-vector one-round
estimate; it does not identify the physical prevector or construct the scanner.

## Implementation notes

`OpenAI.Scan.CollarScan.actualCharge_energyError_le_domainGraph` assumes the numerical margin
`4 * (D + 2 * r₀) ≤ m`, which the source does not state for one round; it is used only for
the labelled split count. At the final rounded scanner scales the margin is derived in
`OpenAI.Scan.exists_badOldHistory_threshold`. TNLean records the restriction in
`docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  `08-scanner.tex`, lines 416–440 and 492–511, at `openai/math@adc7f124`.
-/

open scoped BigOperators Matrix
open MeasureTheory Set Arealaw TensorPower TensorPower.ReplicaTransport Entropy SimpleGraph

noncomputable section

namespace OpenAI.Scan

namespace CollarScan

open Classical in
/-- The literal charge energy is controlled by its actual entropy defect and
classical bad-old mass. The split capacity and replica count may be zero. -/
theorem actualCharge_energyError_le_domainGraph
    {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
    [LinearOrder (supports Λ R)]
    (hT : T.Nonempty) (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ)
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (Δ : ℝ)
    {s L μ : ℕ} (hn : 2 ≤ S.n) (hs : s + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L) (hC : 0 < S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : (r : ℕ) → Config r
      (fun v ↦ Fin (augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux v)) → ℂ)
    (hsym : pre k ∈ symmetricSubspace k
      (fun v ↦ Fin (augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux v)))
    (hpre : pre k ≠ 0) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hm : 0 < S.m := by omega
    let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
    let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux
    let E := S.actualEnergyTerms Φ Ω J Δ L aux
    let A : ℝ := 10 * S.K * S.n * S.D * μ
    let ℓ := transportLogDimBound q S.r₀
    let b := ∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else historyWeight hist
    (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
      (10 * (S.D : ℝ) / S.m) *
        ((1 - p) * A ^ (7 / 8 : ℝ) *
          (S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) p) ^ (1 / 8 : ℝ) +
          A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * ((1 - p) * b + p)) := by
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
  let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux
  let E := S.actualEnergyTerms Φ Ω J Δ L aux
  let D := S.actualChargeData hm hM s
  let Rd := S.actualChargeScanRound hm hM s n E a pre
  let A : ℝ := 10 * S.K * S.n * S.D * μ
  let ℓ := transportLogDimBound q S.r₀
  have hD : 4 * S.D ≤ S.m := by omega
  have hm2 : 2 ≤ S.m := by omega
  have hq : 1 ≤ q := NeZero.pos q
  have hℓ : 0 ≤ ℓ := (zero_le_one.trans (one_le_transportLogDimBound hq S.r₀))
  have hA : 0 ≤ A := by positivity
  have hp' : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩ := fun _ ↦ rfl
  have hcompat : D.SupportCompatible E :=
    S.chargeTransportData_supportCompatible_domainGraph hT hgraph hdepth
      (historyMeanTree S.K S.m S.M hm hM s) (fun _ ↦ chargeChoiceTree S.K S.M hM)
      (by omega) hs hr hDpos hD hL hrows hclear n E hsupport
  have hsupp : ∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ :=
    S.chargeTransportData_logDim_support_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s) (fun _ ↦ chargeChoiceTree S.K S.M hM)
      n hq (fun _ ↦ rfl) hL E hsupport
  have hadm : D.IsAdmissible := S.actualChargeData_isAdmissible hm hM s
  have hcardOld (hist : Rd.H) :
      ((Finset.univ.filter fun i ↦ Rd.splitOld i hist).card : ℝ) ≤ A :=
    S.actualChargeScanRound_card_splitOld_le hT hm hM n E a pre hgraph hdepth hsupport
      hn hm2 hs hr hDpos hmargin hL hrows hclear hmult hist
  have hcardNew (hist : Rd.H) (c : Rd.Ch hist) :
      ((Finset.univ.filter fun i ↦ Rd.splitNew i hist c).card : ℝ) ≤ A :=
    S.actualChargeScanRound_card_splitNew_le hT hm hM n E a pre hgraph hdepth hsupport
      hn hm2 hs hr hDpos hmargin hL hrows hclear hmult hist c
  have hw (hist : Rd.H) : Rd.w hist = historyWeight hist :=
    historyMeanTree_weight S.K S.m S.M hm hM s hist
  have hc (hist : Rd.H) (c : Rd.Ch hist) : Rd.q hist c = chargeWeight c :=
    chargeChoiceTree_weight S.K S.M hM c
  have hsplit (i : supports Λ R) : Rd.splitWeight p i ≤ 10 * (S.D : ℝ) / S.m :=
    S.actualChargeScanRound_splitWeight_le hT hm hM n E a pre hgraph hdepth hsupport hC
      (by omega) hs hr hDpos hD hL hrows hclear hp' i
  have hη0 (i : supports Λ R)
      (j : Σ _ : History S.K S.m S.M s, Option (ChargeChoices S.K S.M))
      (θ : CoherentSphere (SiteConfig n)) : 0 ≤ D.splitEta E i j θ.1 :=
    D.splitEta_nonneg n E hadm i j θ.1
  have hηB (i : supports Λ R)
      (j : Σ _ : History S.K S.m S.M s, Option (ChargeChoices S.K S.M))
      (θ : CoherentSphere (SiteConfig n)) : D.splitEta E i j θ.1 ≤ 2 * ℓ :=
    D.splitEta_le_two_mul_of_logDim_le n E hadm hcompat hℓ hsupp i j θ
  let : ∀ hist : Rd.H, IsFiniteMeasure (Rd.μOld k p hist) := fun hist ↦
    D.isFiniteMeasure_transportLeafMeasure n (a / 2) k (pre k) p ⟨hist, none⟩
  let : ∀ (hist : Rd.H) (c : Rd.Ch hist), IsFiniteMeasure (Rd.μNew k p hist c) :=
    fun hist c ↦ D.isFiniteMeasure_transportLeafMeasure n (a / 2) k (pre k) p ⟨hist, some c⟩
  have hmass := S.actualChargeScanRound_mass hm hM s n E a pre ha k hsym hpre hp
  have hbound := Rd.energySum_le_of_leaf_bounds (B := 2 * ℓ) (N := A)
    (d := 10 * (S.D : ℝ) / S.m) k hp'
    (fun hist ↦ by rw [hw]; exact historyWeight_nonneg hist)
    (by simp_rw [hw]; exact sum_historyWeight S.K s hm hM)
    (fun hist c ↦ by rw [hc]; exact chargeWeight_nonneg c)
    (fun hist ↦ by simp_rw [hc]; exact sum_chargeWeight S.K hM)
    (fun hist ↦ (hmass hist).1) (fun hist c ↦ (hmass hist).2 c)
    (fun i hist ↦ D.measurable_splitEta_sphere n E i ⟨hist, none⟩)
    (fun i hist θ ↦ hη0 i ⟨hist, none⟩ θ)
    (fun i hist c θ ↦ hη0 i ⟨hist, some c⟩ θ)
    (mul_nonneg (by norm_num) hℓ) hA (by positivity)
    (fun i hist θ ↦ hηB i ⟨hist, none⟩ θ)
    (fun i hist c θ ↦ hηB i ⟨hist, some c⟩ θ) hcardOld hcardNew hsplit
  have hbad : Rd.badWeight = ∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else historyWeight hist := by
    change (∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else
        (historyMeanTree S.K S.m S.M hm hM s).weight hist) = _
    simp only [historyMeanTree_weight]
  rw [S.actualChargeScanRound_energySum hm hM s n E a pre ha k hp',
    S.actualChargeScanRound_chargeDefect hm hM s n E a pre ha k p, hbad] at hbound
  exact hbound

end CollarScan
end OpenAI.Scan
