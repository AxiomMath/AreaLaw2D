import OpenAI.Scan.SourceScanScales
import OpenAI.Scan.SchmidtBellAugmentedPrevector
import OpenAI.Scan.ActualTransportEstimates
import OpenAI.Scan.ActualChargeEnergyBound
import OpenAI.Scan.ActualScanMeasures
import OpenAI.Scan.ActualChargeEnergyCoefficients

/-!
# The defect energy of the collar scan at a charge point

The energy step of Proposition 9.2 of [OAI265] (`08-scanner.tex`, lines 492–520) for the
collar scan and the replica prevector of a supplied Schmidt–Bell label sequence.  At every
charge round and every `p ∈ [ε/2, ε]`, the energy clause of Proposition 7.4 and the Hölder
estimate over split terms bound the defect energy of the normalized transported vector by
`C n^ℓ D² W² (log n)^{C_l} ((𝒬(p)/(KnD))^{1/8} + ε + n^{-100}) + C n^{-1000} + ρ_k`, where
`𝒬(p)` is the charge entropy defect at that point and `ρ_k → 0`, uniformly over the round and
the parameter.

## Main statements

* `OpenAI.Scan.ScanRound.energySum_nonneg`: the energy sum of a round is nonnegative.
* `OpenAI.Scan.exists_sourceScan_energy_le`: the defect energy at a charge point.
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph MeasureTheory
open TensorPower.ReplicaTransport
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

open Classical in
/-- The energy sum of a scan round with nonnegative history and choice weights is
nonnegative on the closed interpolation interval. -/
theorem ScanRound.energySum_nonneg {ι Θ : Type} [MeasurableSpace Θ] [Fintype ι]
    (R : ScanRound ι Θ) (k : ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ h, 0 ≤ R.w h) (hq : ∀ h c, 0 ≤ R.q h c) : 0 ≤ R.energySum k p := by
  have h1p : 0 ≤ 1 - p := by linarith [hp.2]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ ?_
  · refine add_nonneg (Finset.sum_nonneg fun h _ => ?_)
      (Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun c _ => ?_)
    · split_ifs
      · exact mul_nonneg h1p (hw h)
      · exact le_rfl
    · split_ifs
      · exact mul_nonneg (mul_nonneg hp.1 (hw h)) (hq h c)
      · exact le_rfl
  · refine add_nonneg (Finset.sum_nonneg fun h _ => ?_)
      (Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun c _ => ?_)
    · split_ifs
      · exact mul_nonneg (mul_nonneg h1p (hw h))
          (integral_nonneg fun θ => rpow_one_div_eight_nonneg _)
      · exact le_rfl
    · split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg hp.1 (hw h)) (hq h c))
          (integral_nonneg fun θ => rpow_one_div_eight_nonneg _)
      · exact le_rfl

/-- The actual charge energy error is nonnegative on the closed interpolation interval. -/
theorem CollarScan.actualChargeData_energyError_nonneg
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
    {a : ℝ} (ha : 0 ≤ a) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ) (k : ℕ)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p := by
  rw [← S.actualChargeScanRound_energySum hm hM s n E a pre ha k hp]
  refine ScanRound.energySum_nonneg _ k hp (fun h => ?_) (fun h c => ?_)
  · exact le_of_le_of_eq (historyWeight_nonneg h)
      (historyMeanTree_weight S.K S.m S.M hm hM s h).symm
  · exact le_of_le_of_eq (chargeWeight_nonneg c) (chargeChoiceTree_weight S.K S.M hM c).symm

/-- The coefficient of the charge energy estimate, with the rate written as `a = W / K` and the
capacity `A = 10 K n D μ`, in the form `W² (n D² / (m K)) (c₁ ℓ^{e} (1-p) (Q/(KnD))^{1/8}
+ c₂ ℓ^{e + 1/8} z)`. -/
theorem chargeEnergyCoefficient_eq {K m n D ℓ μ Q : ℝ} (hK : 0 < K) (hm : 0 < m)
    (hB : 0 < K * n * D) (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) (hQ : 0 ≤ Q) (W p z Cen een : ℝ) :
    |Cen| * (W / K) ^ 2 * ℓ ^ een * ((10 * D / m) *
      ((1 - p) * (10 * K * n * D * μ) ^ (7 / 8 : ℝ) * Q ^ (1 / 8 : ℝ) +
        (10 * K * n * D * μ) * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * z)) =
      W ^ 2 * (n * D ^ 2 / (m * K)) *
        ((10 * (10 * μ) ^ (7 / 8 : ℝ) * |Cen| * ℓ ^ een) *
          ((1 - p) * (Q / (K * n * D)) ^ (1 / 8 : ℝ)) +
          (50 * μ * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen| * ℓ ^ (een + 1 / 8)) * z) := by
  have hA : (10 * K * n * D * μ) ^ (7 / 8 : ℝ) =
      (10 * μ) ^ (7 / 8 : ℝ) * (K * n * D) ^ (7 / 8 : ℝ) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 10 * μ) hB.le]
    congr 1
    ring
  have hQroot : Q ^ (1 / 8 : ℝ) =
      (K * n * D) ^ (1 / 8 : ℝ) * (Q / (K * n * D)) ^ (1 / 8 : ℝ) := by
    rw [← Real.mul_rpow hB.le (div_nonneg hQ hB.le), _root_.mul_div_cancel₀ Q hB.ne']
  have hBroot : (K * n * D) ^ (7 / 8 : ℝ) * (K * n * D) ^ (1 / 8 : ℝ) = K * n * D := by
    rw [← Real.rpow_add hB]
    norm_num
  have hgood : (10 * K * n * D * μ) ^ (7 / 8 : ℝ) * Q ^ (1 / 8 : ℝ) =
      (10 * μ) ^ (7 / 8 : ℝ) * (K * n * D) * (Q / (K * n * D)) ^ (1 / 8 : ℝ) := by
    rw [hA, hQroot]
    calc
      _ = (10 * μ) ^ (7 / 8 : ℝ) *
          ((K * n * D) ^ (7 / 8 : ℝ) * (K * n * D) ^ (1 / 8 : ℝ)) *
          (Q / (K * n * D)) ^ (1 / 8 : ℝ) := by ring
      _ = _ := by rw [hBroot]
  rw [_root_.mul_assoc (1 - p) _ (Q ^ (1 / 8 : ℝ)), hgood,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hℓ.le, Real.rpow_add hℓ]
  field_simp [hK.ne', hm.ne']; ring

/-- Dividing the defect energy by the gap: if `x ≤ 2e + Z + r` with `e ≤ P`, `r ≤ r'` and
`Z, P, r' ≥ 0`, then `(x - e)/gap ≤ Z/g₀ + C P + r'/g₀` whenever `0 < g₀ ≤ gap` and
`1/g₀ ≤ C`. -/
theorem sub_div_gap_le {x e Z r r' gap g₀ C P : ℝ} (hg₀ : 0 < g₀) (hgap : g₀ ≤ gap)
    (hx : x ≤ 2 * e + Z + r) (he : e ≤ P) (hP : 0 ≤ P) (hZ : 0 ≤ Z) (hr : r ≤ r')
    (hr' : 0 ≤ r') (hC : 1 / g₀ ≤ C) :
    (x - e) / gap ≤ Z / g₀ + C * P + r' / g₀ := by
  have hY : x - e ≤ P + Z + r' := by linarith
  have hY0 : 0 ≤ P + Z + r' := by positivity
  have hgap0 : 0 < gap := hg₀.trans_le hgap
  calc (x - e) / gap ≤ (P + Z + r') / gap := div_le_div_of_nonneg_right hY hgap0.le
    _ ≤ (P + Z + r') / g₀ := div_le_div_of_nonneg_left hY0 hg₀ hgap
    _ = Z / g₀ + (1 / g₀) * P + r' / g₀ := by ring
    _ ≤ Z / g₀ + C * P + r' / g₀ := by gcongr

open Classical in
/-- **The defect energy at a charge point** [OAI265, §9.2, lines 492–520]: for the collar scan
at every large scale and the replica prevector of a Schmidt–Bell label sequence of the
truncated Hamiltonian with eigenvalue `e ≤ n^{-1000}`, at every charge round and every
`p ∈ [ε/2, ε]` the defect energy is at most
`C n^ℓ D² W² (log n)^{C_l} ((𝒬(p)/(KnD))^{1/8} + ε + n^{-100}) + C n^{-1000} + ρ_k`,
with one remainder `ρ_k → 0` for all rounds and parameters. -/
theorem exists_sourceScan_energy_le (X : ScannerExponents) (q R : ℕ) [NeZero q]
    {J Δ Ctr CT g₀ ω : ℝ} (hΔ : 0 < Δ) (hCtr : 0 < Ctr) (hCT : 0 ≤ CT) (hg₀ : 0 < g₀)
    (hω : ω < 1 - X.ell - X.mu) :
    ∃ C Cl : ℝ, 0 ≤ C ∧ 0 ≤ Cl ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hT : T.Nonempty), A ⊆ Λ →
      (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2 →
      (∀ d : ℕ, 1 ≤ d → d ≤ X.L n →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) →
      (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
        ((2 * X.L n + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) < ambientSupDistance t z) →
    let S := sourceScan X Ctr R Λ A T hT n
    ∃ (hm : 0 < S.m) (hM : 0 < S.M),
    ∀ (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ),
      IsAdmissible Λ R J Φ →
    ∀ (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
    ∀ (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (e gap : ℝ),
      e ≤ (n : ℝ) ^ (-1000 : ℝ) → g₀ ≤ gap →
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let Xs := S.A.filter fun x => x.val ∈ T
    ∀ (E : Finset (FiniteProduct.Configuration β Xs)) [NeZero E.card]
      (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))),
      IsSchmidtBellLabels (∑ i, S.truncatedEnergyTerm Φ Ω J Δ (X.L n) i) Ωt e Xs E ell →
    ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ ω →
      let d := E.card
      let a := W / (S.K : ℝ)
      let nA := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ => d)
      let pre : (k : ℕ) → Config k (fun v => Fin (nA v)) → ℂ := fun k =>
        replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
      let ε := (n : ℝ) ^ (-X.nu)
      ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
      ∀ k : ℕ, 0 < k → ∀ s : Fin (S.n * S.m), ∀ p ∈ Set.Icc (ε / 2) ε,
        ((S.actualChargeScanRound hm hM s.val nA
            (S.actualEnergyTerms Φ Ω J Δ (X.L n) (fun _ => d)) a pre).meanEnergy k p - e) /
            gap ≤
          C * (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
              ((S.actualChargeEntropyDefect hm hM s.val nA
                  (S.actualEnergyTerms Φ Ω J Δ (X.L n) (fun _ => d)) (a / 2) k (pre k) p /
                  ((S.K : ℝ) * n * S.D)) ^ (1 / 8 : ℝ) + ε + (n : ℝ) ^ (-100 : ℝ)) +
            C * (n : ℝ) ^ (-1000 : ℝ) + ρ k := by
  obtain ⟨c₀, _Cent, _eent, Cen, een, hc₀, htr⟩ := CollarScan.actualCharge_transport_domainGraph
  set μR : ℝ := (anchorMultiplicityBound R : ℝ) with hμR
  obtain ⟨Cd, Cl, hCd, hCl, hcoef⟩ := exists_transport_coefficients_log_bound (q := q)
    NeZero.one_le hCtr.le (10 * (10 * μR) ^ (7 / 8 : ℝ) * |Cen|) een
    (50 * μR * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen|) (een + 1 / 8)
  obtain ⟨C₁, hC₁⟩ := eventually_scaleFacts X
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((((hC₁.and (eventually_sourceScan_scales X hCtr.le)).and
    (eventually_div_bandCount_mul_transportLogDimBound_le X q hCtr.le hω hc₀)).and hlog).and
    (eventually_sourceScan_badOldHistory_le X hCtr hCT R 100))
  refine ⟨max (C₁ * Cd / g₀) (1 / g₀), Cl, le_trans (by positivity) (le_max_right _ _), hCl,
    N, ?_⟩
  intro n hn Λ A T _ hT hA hTcard hrows hclear S
  obtain ⟨⟨⟨⟨hF, hn2, hr, h2r, hD1, hmargin, hL⟩, hsmall⟩, hlogn⟩, hbad⟩ := hN n hn
  have hm : 0 < S.m := hF.one_le_m
  have hCpos : (0 : ℝ) < S.C₁ := by
    change (0 : ℝ) < 3 * μR; rw [hμR, anchorMultiplicityBound]; positivity
  have hM : 0 < S.M := chargeSlotCount_pos hCpos (by change 1 ≤ n; omega) hD1
  refine ⟨hm, hM, ?_⟩
  intro Φ hΦ Ω hΩ Ωt e gap he hgap β Xs E _ ell hSB W hW1 hWω d a nA pre ε
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hKpos : (0 : ℝ) < S.K := by
    have : (1 : ℝ) ≤ X.K n := by exact_mod_cast hF.one_le_K
    change (0 : ℝ) < X.K n; linarith
  have hmR : (0 : ℝ) < S.m := by exact_mod_cast hm
  have hDR : (0 : ℝ) < S.D := by
    have : (1 : ℝ) ≤ X.D n := by exact_mod_cast hD1
    change (0 : ℝ) < X.D n; linarith
  have ha : 0 < a := div_pos (by linarith) hKpos
  have haℓ : a * transportLogDimBound q S.r₀ ≤ c₀ := hsmall W (by linarith) hWω
  have hclear' : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * X.L n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
    rw [sourceScan_cutEndpoints X Ctr R hA hT n]; exact hclear
  have hD4 : 4 * S.D ≤ S.m := by change 4 * X.D n ≤ X.m n; omega
  have hmargin' : 4 * (S.D + 2 * S.r₀) ≤ S.m := hmargin
  have hεs := fun s : Fin (S.n * S.m) => htr (fun _ => d) Φ hΦ Ω S hT rfl rfl
    supportAnchor_mem hΔ hΩ (s := s.val) (L := X.L n) (show 0 < S.n by change 0 < n; omega)
    s.isLt hr hD1 hD4 hL hCpos hrows hclear' ha haℓ
  choose βs εs hβs hεs0 hεsb using hεs
  clear htr hN hβs
  refine ⟨fun k => (∑ s, |εs s k|) / g₀, ?_, ?_⟩
  · have h := (tendsto_finsetSum (Finset.univ : Finset (Fin (S.n * S.m)))
      (fun s _ => (hεs0 s).abs)).div_const g₀
    simpa only [abs_zero, Finset.sum_const_zero, zero_div] using h
  intro k hk s p hp
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := hF.eps_lt_one
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  obtain ⟨hsymk, hnek, -, heig⟩ := hSB.augmentedPrevector hk
  have hE1 := ((hεsb s k (pre k) hsymk hnek).1 p hp').2.2 e heig
  clear hεsb
  set EnT := S.actualEnergyTerms Φ Ω J Δ (X.L n) (fun _ => d) with hEnT
  set ℓ := transportLogDimBound q S.r₀ with hℓdef
  set EE := (S.actualChargeData hm hM s.val).energyError EnT (a / 2) k (pre k) p with hEEdef
  set Q := S.actualChargeEntropyDefect hm hM s.val nA EnT (a / 2) k (pre k) p with hQdef
  have hmean : (S.actualChargeScanRound hm hM s.val nA EnT a pre).meanEnergy k p ≤
      2 * e + Cen * a ^ 2 * ℓ ^ een * EE + εs s k := by
    rw [CollarScan.actualChargeScanRound_meanEnergy]; exact hE1
  have hℓ1 : 1 ≤ ℓ := one_le_transportLogDimBound NeZero.one_le _
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hQ0 : 0 ≤ Q := S.actualChargeEntropyDefect_nonneg hm hM s.val nA EnT ha.le k pre p
  have hEE0 : 0 ≤ EE := CollarScan.actualChargeData_energyError_nonneg S hm hM s.val nA EnT
    ha.le pre k ⟨hp'.1.le, hp'.2.le⟩
  have hEEle := S.actualCharge_energyError_le_domainGraph (J := J) hT rfl rfl (fun _ => d) Φ Ω
    Δ (s := s.val) (L := X.L n) (μ := anchorMultiplicityBound R) hn2 s.isLt hr hD1 hmargin' hL
    hCpos hrows (sourceScan_anchor_card_le X Ctr R Λ A T hT n) hclear' ha.le k pre hsymk hnek
    hp'
  have hb := hbad Λ A T hT hA hTcard hrows hclear s.val s.isLt.le
  clear hbad
  generalize hbdef : (∑ hist : History S.K S.m S.M s.val,
    if S.IsGoodOldHistory hist then 0 else historyWeight hist) = b at hEEle hb
  obtain ⟨hc1, hc2⟩ := hcoef n hlogn ℓ hℓ1 le_rfl
  set q8 := (Q / ((S.K : ℝ) * n * S.D)) ^ (1 / 8 : ℝ) with hq8
  have hq80 : 0 ≤ q8 := Real.rpow_nonneg (div_nonneg hQ0 (by positivity)) _
  have h1p : 0 ≤ 1 - p := by linarith [hp'.2]
  have hU : (1 - p) * q8 ≤ q8 := mul_le_of_le_one_left hq80 (by linarith [hp'.1])
  have hP100 : (0 : ℝ) ≤ (n : ℝ) ^ (-100 : ℝ) := by positivity
  have hZb : (1 - p) * b + p ≤ (n : ℝ) ^ (-100 : ℝ) + ε := by
    have h1 := mul_le_mul_of_nonneg_left hb h1p
    have h2 : (1 - p) * (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-100 : ℝ) :=
      mul_le_of_le_one_left hP100 (by linarith [hp'.1])
    have h3 : p ≤ ε := hp.2
    linarith
  have hU0 : 0 ≤ (1 - p) * q8 := mul_nonneg h1p hq80
  have hZb0 : 0 ≤ (1 - p) * b + p := by
    have : 0 ≤ b := by
      rw [← hbdef]
      exact Finset.sum_nonneg fun h _ => by
        split_ifs
        · exact le_rfl
        · exact historyWeight_nonneg h
    exact add_nonneg (mul_nonneg h1p this) hp'.1.le
  have hcoefS : (n : ℝ) * (S.D : ℝ) ^ 2 / (S.m * S.K) ≤
      C₁ * (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 := hF.coefficient_le
  have hC₁ : 0 ≤ C₁ := by linarith [hF.one_le_C₁]
  set Lg := Real.log n ^ Cl with hLg
  have hLg0 : 0 ≤ Lg := Real.rpow_nonneg (by linarith) _
  have hEnergy : Cen * a ^ 2 * ℓ ^ een * EE ≤
      C₁ * Cd * ((n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 * Lg *
        (q8 + ε + (n : ℝ) ^ (-100 : ℝ))) := by
    have hpos : 0 ≤ a ^ 2 * ℓ ^ een * EE := by positivity
    calc Cen * a ^ 2 * ℓ ^ een * EE ≤ |Cen| * a ^ 2 * ℓ ^ een * EE := by
          have := mul_le_mul_of_nonneg_right (le_abs_self Cen) hpos
          linarith
      _ ≤ |Cen| * (W / S.K) ^ 2 * ℓ ^ een * ((10 * (S.D : ℝ) / S.m) *
            ((1 - p) * (10 * (S.K : ℝ) * n * S.D * μR) ^ (7 / 8 : ℝ) * Q ^ (1 / 8 : ℝ) +
              (10 * (S.K : ℝ) * n * S.D * μR) * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 *
                ((1 - p) * b + p))) :=
          mul_le_mul_of_nonneg_left hEEle (by positivity)
      _ = W ^ 2 * ((n : ℝ) * (S.D : ℝ) ^ 2 / (S.m * S.K)) *
            ((10 * (10 * μR) ^ (7 / 8 : ℝ) * |Cen| * ℓ ^ een) * ((1 - p) * q8) +
              (50 * μR * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen| * ℓ ^ (een + 1 / 8)) *
                ((1 - p) * b + p)) :=
          chargeEnergyCoefficient_eq hKpos hmR (by positivity) hℓ0 (by positivity) hQ0 W p
            ((1 - p) * b + p) Cen een
      _ ≤ W ^ 2 * (C₁ * (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2) *
            (Cd * Lg * ((1 - p) * q8) + Cd * Lg * ((1 - p) * b + p)) := by
          gcongr
      _ ≤ W ^ 2 * (C₁ * (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2) *
            (Cd * Lg * (q8 + ε + (n : ℝ) ^ (-100 : ℝ))) := by
          gcongr
          have := mul_le_mul_of_nonneg_left (add_le_add hU hZb)
            (show 0 ≤ Cd * Lg by positivity)
          linarith
      _ = _ := by ring
  set Zs := (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 * Lg * (q8 + ε + (n : ℝ) ^ (-100 : ℝ))
    with hZs
  have hZs0 : 0 ≤ Zs := by positivity
  have hx : (S.actualChargeScanRound hm hM s.val nA EnT a pre).meanEnergy k p ≤
      2 * e + C₁ * Cd * Zs + εs s k :=
    hmean.trans (by gcongr)
  have hr' : εs s k ≤ ∑ s, |εs s k| := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun s => |εs s k|) (fun s _ => abs_nonneg _)
      (Finset.mem_univ s))
  have hfin := sub_div_gap_le hg₀ hgap hx he (Real.rpow_nonneg hn0.le _)
    (mul_nonneg (mul_nonneg hC₁ (by linarith)) hZs0) hr'
    (Finset.sum_nonneg fun s _ => abs_nonneg _) (le_max_right (C₁ * Cd / g₀) (1 / g₀))
  refine hfin.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  calc C₁ * Cd * Zs / g₀ = C₁ * Cd / g₀ * Zs := by ring
    _ ≤ max (C₁ * Cd / g₀) (1 / g₀) * Zs :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hZs0
    _ = _ := by rw [hZs]; ring

end OpenAI.Scan
