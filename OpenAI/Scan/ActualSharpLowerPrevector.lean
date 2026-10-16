/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 576d1624411e36a16cfc84aba9883f91416bcd32,
`TNLean/PEPS/AreaLaw/Scan/ActualSharpLowerPrevector.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to the encodings of
`OpenAI.Scan.ActualSharpLower` and `OpenAI.Scan.ActualSharpPrevector`: TNLean's `Site Λ` is
`↥(Λ : Set (ℤ × ℤ))`, the labels `AdmissibleSupport Λ R` are `↥(supports Λ R)`, the state space
`StateSpace Λ q` is `EuclideanSpace ℂ (Reg (Qudits q) Λ)`, and the bundled
`LocalHamiltonian Λ q R J` is an interaction `Φ` with `hΦ : OpenAI.IsAdmissible Λ R J Φ`, so
`S.truncatedEnergyTerm h Ω Δ L` and `S.actualEnergyTerms h Ω Δ L aux` are
`S.truncatedEnergyTerm Φ Ω J Δ L` and `S.actualEnergyTerms Φ Ω J Δ L aux`. TNLean's
`reducedState Λ q Ωt Q` and `regionalEntropy Λ q Ωt Q` in the moment hypothesis are the
restriction and `regionEntropy` of `OpenAI.pureState` to `Q.map (Function.Embedding.subtype _)`,
whose normalization comes from `‖Ωt‖ = 1` by `OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one`;
the bridge to the finite-product form is `OpenAI.surprisalMoment_restrict_pureState_eq_finiteProduct`
(`OpenAI.Scan.ActualSharpUpper`) with `OpenAI.regionalEntropy_eq_finiteProduct`, replacing the
import of `TNLean/PEPS/AreaLaw/TwoFamilies.lean`. `Entropy.surprisalMoment` is
`OpenAI.surprisalMoment`.
-/
import OpenAI.Scan.ActualSharpLower
import OpenAI.Scan.ActualSharpLowerRemainder
import OpenAI.Scan.AugmentedReplicaPrevectorProperties
import OpenAI.Scan.StatusMarginalMoments
import OpenAI.Scan.ActualSharpUpper

/-!
# The same supplied physical sequence in the sharp lower estimate

The nonzero, norm and label-dimension conclusions of the physical prevector
construction are consumed for the supplied sequence. Its symmetry and both
original auxiliary labels are derived for the literal augmented prevector.
The actual fill and charge lower rates retain their actual energy defects;
the polynomial and label remainder vanishes for this same sequence.
There is no new label choice and no small-energy assumption.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
`comparator:sharp-lower`, lines 130–153, 255–281 and 550–651; `08-scanner.tex`,
lines 400–474, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

namespace OpenAI.Scan.CollarScan

open ActualTerminals
open Arealaw (Reg)

private theorem sharp_lower_rate_of_finite_copy {G k : ℕ}
    {a err Nsq : ℝ} (ha : 0 < a) (hk : 0 < k) (rate : Fin G → ℝ)
    (h : (1 / 2) * (∑ g, (a * (k : ℝ) * rate g - err)) ≤ -Real.log Nsq) :
    (a / 2) * (∑ g, (rate g - err / (a * (k : ℝ)))) ≤
      -Real.log Nsq / (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hkpos).2
  calc
    ((a / 2) * (∑ g, (rate g - err / (a * (k : ℝ))))) * (k : ℝ) =
        (1 / 2) * (∑ g, (a * (k : ℝ) * rate g - err)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      field_simp [ha.ne', hkpos.ne']
    _ ≤ -Real.log Nsq := h

open Classical in
/-- A regional moment bound uses the same reduced matrix in finite-product coordinates. -/
private theorem sharpLower_marginalMoment_finiteProduct
    {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (hΩ : star (WithLp.ofLp Ωt) ⬝ᵥ WithLp.ofLp Ωt = 1)
    (U : Finset ↥(Λ : Set (ℤ × ℤ))) (Kmom u : ℝ)
    (h : Real.log (surprisalMoment
      ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).restrict
        (map_embeddingSubtype_subset (T := Λ) U)).psd.isHermitian.eigenvalues u) ≤
      u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).regionEntropy
        (map_embeddingSubtype_subset (T := Λ) U) + Kmom * u ^ 2) :
    Real.log (surprisalMoment
      (FiniteProduct.reducedPure_posSemidef
        (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt U).isHermitian.eigenvalues u) ≤
      u * FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt U +
        Kmom * u ^ 2 := by
  rw [← surprisalMoment_restrict_pureState_eq_finiteProduct Ωt hΩ U u,
    ← regionalEntropy_eq_finiteProduct Λ q Ωt hΩ U]
  exact h

open Classical in
/-- Completed and pre-charge status moments supply all three original physical marginals. -/
private theorem actualTerminal_sharpLower_moments
    {Λ : Finset (ℤ × ℤ)} {q : ℕ} {I : Type} [Fintype I] [LinearOrder I]
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (hΩ : star (WithLp.ofLp Ωt) ⬝ᵥ WithLp.ofLp Ωt = 1) (Kmom rMom : ℝ)
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ rMom →
          Real.log (surprisalMoment
            ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).restrict
              (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
            u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).regionEntropy
              (map_embeddingSubtype_subset (T := Λ) Q) + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ rMom →
            Real.log (surprisalMoment
              ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).restrict
                (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
              u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) Q) + Kmom * u ^ 2)) :
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    ∀ j g (b : Fin 3) (u : ℝ), |u| ≤ rMom →
      let U := FiniteProduct.regionalPhysicalRegion (Q j g) (Y j g) b
      Real.log (surprisalMoment
        (FiniteProduct.reducedPure_posSemidef β Ωt U).isHermitian.eigenvalues u) ≤
          u * FiniteProduct.entropy β Ωt U + Kmom * u ^ 2 := by
  classical
  intro β σ Q Y
  have hfar (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K) :
      receiving (σ j g) true = (Q j g ∪ Y j g)ᶜ := by
    ext x
    cases hx : σ j g x with
    | none => simp [Q, Y, receiving, middle, hx]
    | some side => cases side <;> simp [Q, Y, receiving, middle, hx]
  have hmomStatus : ∀ j g (U : Finset ↥(Λ : Set (ℤ × ℤ))),
      U ∈ statusMarginalRegions S.depth (σ j g) →
      ∀ u : ℝ, |u| ≤ rMom →
        Real.log (surprisalMoment
          ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).restrict
            (map_embeddingSubtype_subset (T := Λ) U)).psd.isHermitian.eigenvalues u) ≤
          u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt) hΩ).regionEntropy
            (map_embeddingSubtype_subset (T := Λ) U) + Kmom * u ^ 2 := fun
    | Sum.inl ⟨s, hist⟩, g, U, hU, u, hu =>
      (hmom s.val hist g).1 (Nat.le_of_lt_succ s.isLt) U hU u hu
    | Sum.inr ⟨s, hist⟩, g, U, hU, u, hu =>
      (hmom s.val hist g).2 (Nat.succ_le_of_lt s.isLt) U hU u hu
  intro j g b u hu U
  have hmem : U ∈ statusMarginalRegions S.depth (σ j g) := by
    fin_cases b
    · simp [U, FiniteProduct.regionalPhysicalRegion, statusMarginalRegions, Q]
    · simp [U, FiniteProduct.regionalPhysicalRegion, statusMarginalRegions, Y]
    · change (Q j g ∪ Y j g)ᶜ ∈ statusMarginalRegions S.depth (σ j g)
      rw [← hfar]
      simp [statusMarginalRegions]
  exact sharpLower_marginalMoment_finiteProduct Ωt hΩ U Kmom u
    (hmomStatus j g U hmem u hu)

open Classical in
/-- The fixed supplied prevector keeps its norm, symmetry and both auxiliary labels. -/
private theorem sharpLower_suppliedPrevector_properties
    {Λ : Finset (ℤ × ℤ)} (q d k : ℕ) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (hpre :
      let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
      let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k ell ∘
        globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      ξ ≠ 0 ∧ ‖ξ‖ ≤ 1) :
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ => d)
    let pre : Config k (fun v => Fin (n v)) → ℂ :=
      replicaPrevector Ωt d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    let e := augmentedReplicaConfigurationEquiv (V := ↥(Λ : Set (ℤ × ℤ))) q d k
    let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
    pre ≠ 0 ∧ ‖WithLp.toLp 2 pre‖ ≤ 1 ∧
      symProj (copyPerm ((v : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool) → Fin (n v)) k) *ᵥ pre = pre ∧
      labelProj (subsystemPerm k ι₀ {some none}) ell *ᵥ (pre ∘ e) = pre ∘ e ∧
      labelProj (subsystemPerm k ι₀ {none}) ell *ᵥ (pre ∘ e) = pre ∘ e := by
  classical
  intro β n pre e ι₀
  have hpreEq : pre ∘ e = replicaPrevector Ωt d k ell ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, e, Equiv.symm_comp_self, Function.comp_id, β]
  have hprenonzero : pre ≠ 0 := by
    intro hz
    apply hpre.1
    change WithLp.toLp 2 (replicaPrevector Ωt d k ell ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k) = 0
    rw [← hpreEq, hz]
    rfl
  have hprenorm : ‖WithLp.toLp 2 pre‖ ≤ 1 := by
    have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
      (WithLp.toLp 2 pre)
    have hno : ‖WithLp.toLp 2 (pre ∘ e)‖ ≤ 1 := by
      rw [hpreEq]
      exact hpre.2
    exact hn.symm.trans_le hno
  have hsym : symProj (copyPerm ((v : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool) → Fin (n v)) k) *ᵥ
      pre = pre :=
    symProj_mulVec_augmentedReplicaPrevector q d k Ωt ell
  have haux := labelProj_globalReplicaCopiesEquiv_auxiliary β (Fin d) (Fin d)
    k ell ell
  have hfixed := replicaPrevector_auxiliary_label_fixed Ωt d k ell
  have hC : labelProj (subsystemPerm k ι₀ {some none}) ell *ᵥ
      (pre ∘ e) = pre ∘ e := by
    rw [hpreEq, ← haux.1]
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v => v ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k) hfixed.1
  have hR : labelProj (subsystemPerm k ι₀ {none}) ell *ᵥ
      (pre ∘ e) = pre ∘ e := by
    rw [hpreEq, ← haux.2]
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v => v ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k) hfixed.2
  exact ⟨hprenonzero, hprenorm, hsym, hC, hR⟩

open Classical in
/-- **The sharp lower comparison for a supplied label sequence** [OAI265, Proposition 8.1,
`comparator:sharp-lower`]. The supplied Schmidt–Bell label sequence satisfies the actual
sharp lower rate at every fill and charge root with a vanishing replica remainder. The two
sequence premises are the nonzero/norm and little-o conclusions of the physical prevector
theorem; the auxiliary and symmetry equations are derived. All physical marginal moments
concern the same unit state used in the gap, and the actual energy defect remains explicit at
every interpolation. Source: `07-comparators.tex`, lines 130–153, 255–281 and 550–651;
`08-scanner.tex`, lines 400–474, revision adc7f124. -/
theorem exists_actualScan_suppliedPrevector_sharp_lower
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (supports Λ R)]
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
    (hm : 0 < S.m) (hM : 0 < S.M)
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ)
    (hΦ : IsAdmissible Λ R J Φ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (Δ : ℝ) (L : ℕ)
    (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (e₀ gap : ℝ) (hΩt : ‖Ωt‖ = 1)
    (hgap : ((∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) - (e₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef)
    (hgap_pos : 0 < gap)
    (a Kmom rMom : ℝ) (ha : 0 < a) (har : 10 * a ≤ rMom)
    (haone : 10 * a ≤ 1) (hK : 0 ≤ Kmom)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hpre : ∀ k : ℕ, 0 < k →
      let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
      let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
        globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      ξ ≠ 0 ∧ ‖ξ‖ ≤ 1)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ)))
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ rMom →
          Real.log (surprisalMoment
            ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
              (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
            u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
              (map_embeddingSubtype_subset (T := Λ) Q) + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ rMom →
            Real.log (surprisalMoment
              ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
              u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) Q) + Kmom * u ^ 2)) :
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ => d)
    let pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ := fun k =>
      replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    let entropyGap := fun j g =>
      FiniteProduct.entropy β Ωt (Q j g) +
        FiniteProduct.entropy β Ωt (Q j g ∪ Y j g)ᶜ -
        FiniteProduct.entropy β Ωt (Y j g)
    let gaps := (Finset.univ :
      Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
        (fun j => entropyGap j.1 j.2)
    let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      Tendsto (sharpLowerRemainder a c Cf ell Sent) atTop (𝓝 0) ∧
      ∀ k : ℕ, 0 < k → ∀ (s : Fin (S.n * S.m)) (p : ℝ),
        let lower := fun (Nsq μ : ℝ)
            (T : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) =>
          0 < Nsq ∧ 0 ≤ (μ - e₀) / gap ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
              let rate := fun g => 2 * Sent +
                (1 - τ) * (∑ j, T.weight j * entropyGap j g) -
                  τ * (2 * Real.log (d : ℝ)) -
                  (3 + 1 / a) * Real.binEntropy τ - 25 * Kmom * a
              (a / 2) * (∑ g,
                (rate g - (μ - e₀) / gap / τ * max 0 (2 * Sent + gmax) -
                  sharpLowerRemainder a c Cf ell Sent k)) ≤
                -Real.log Nsq / (k : ℝ)
        let Dfill := S.actualFillData hm hM s.val
        let Dcharge := S.actualChargeData hm hM s.val
        let Tfill := (Dfill.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
          (fillTerminalIndex S.K S.m S.M (S.n * S.m) s)
        let Tcharge := (Dcharge.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
          (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dfill.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dfill.rootPath n (a / 2) k p) (pre k))
            ((S.actualFillScanRound hm hM s.val n
              (S.actualEnergyTerms Φ Ω J Δ L (fun _ => d)) a pre).meanEnergy k p) Tfill) ∧
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dcharge.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dcharge.rootPath n (a / 2) k p) (pre k))
            ((S.actualChargeScanRound hm hM s.val n
              (S.actualEnergyTerms Φ Ω J Δ L (fun _ => d)) a pre).meanEnergy k p) Tcharge) := by
  classical
  intro β n pre σ Q Y entropyGap gaps gmax
  obtain ⟨c, Cf, hc, hCf, hlower⟩ :=
    exists_actualScan_sharp_lower_norm (Λ := Λ) (q := q) (d := d) (R := R) (J := J) a ha
  refine ⟨c, Cf, hc, hCf,
    tendsto_sharpLowerRemainder_of_label_dimension ell Sent hdim a c Cf, ?_⟩
  have hmomQ := actualTerminal_sharpLower_moments S Ωt
    (star_dotProduct_self_eq_one_of_norm_eq_one hΩt) Kmom rMom hmom
  intro k hk s p lower Dfill Dcharge Tfill Tcharge
  obtain ⟨hprenonzero, hprenorm, hsym, hC, hR⟩ :=
    sharpLower_suppliedPrevector_properties q d k Ωt (ell k) (hpre k hk)
  obtain ⟨⟨hfnorm, hfpos, hfδ, hf⟩, ⟨hcnorm, hcpos, hcδ, hcharge⟩⟩ :=
    hlower S hm hM (S.n * S.m) Φ hΦ Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos
      Kmom rMom hmomQ har haone hK pre k hk hprenonzero hprenorm hsym
      (ell k) (ell k) Sent (sharpLowerLabelDefect ell Sent k) hC hR
      (sharpLowerLabelDefect_label_bound ell Sent k).2 s p
  refine ⟨⟨hfnorm, hfpos, hfδ, ?_⟩, ⟨hcnorm, hcpos, hcδ, ?_⟩⟩
  · intro τ hτ hτhalf
    simpa only [sharpLowerRemainder] using
      sharp_lower_rate_of_finite_copy ha hk _ (hf τ hτ hτhalf)
  · intro τ hτ hτhalf
    simpa only [sharpLowerRemainder] using
      sharp_lower_rate_of_finite_copy ha hk _ (hcharge τ hτ hτhalf)

end OpenAI.Scan.CollarScan
