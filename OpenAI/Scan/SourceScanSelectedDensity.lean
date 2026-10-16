import OpenAI.Scan.SourceScanScales
import OpenAI.Scan.SchmidtBellAugmentedPrevector
import OpenAI.Scan.ActualChargeSelectionBound
import OpenAI.Scan.ActualInitialRootNorm
import OpenAI.Scan.ActualRoughUpper
import OpenAI.Scan.FillTransportEndpoints

/-!
# The selected charge density of the collar scan

The selection step of Proposition 9.2 of [OAI265] (`08-scanner.tex`, lines 442–490) for the
collar scan and the replica prevector of a supplied Schmidt–Bell label sequence.  The charge
entropy gains integrated over all `2nm` rounds telescope to the initial and final logarithmic
norms; the initial one is bounded by the leaf floor and the final one by the rough upper
comparison at the last charge root, `-k⁻¹ log N² ≤ C W n^{1+e} + o_k(1)`.  Averaging the
charge defects over the charge rounds and over `p ∈ [ε/2, ε]` then gives, at each large `k`,
a charge round and a parameter with
`𝒬(p)/(KnD) ≤ C ε⁻¹ (n^{e-μ} + a^{1/4} (log n)^{C_l}) + o_k(1)` (eq. (9.6)).

## Main statements

* `OpenAI.Scan.exists_sourceScan_selected_density`: the selected density.
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- The normalization of the averaged charge defect: the selection threshold
`B / (k a (c / (n D)) (n m) (ε - ε/2))`, divided by `K n D`, is `B / (k c W n m ε / 2)` when
`a K = W`. -/
theorem div_le_of_le_selectionThreshold {Q B k a c n D m K W ε : ℝ} (hk : 0 < k)
    (ha : 0 < a) (hc : 0 < c) (hn : 0 < n) (hD : 0 < D) (hm : 0 < m) (hK : 0 < K)
    (hε : 0 < ε) (haK : a * K = W)
    (hQ : Q ≤ B / (k * a * (c / (n * D)) * (n * m) * (ε - ε / 2))) :
    Q / (K * n * D) ≤ B / (k * c * W * n * m * ε / 2) := by
  have hX : k * a * (c / (n * D)) * (n * m) * (ε - ε / 2) =
      (k * c * W * n * m * ε / 2) / (K * n * D) := by
    rw [← haK]; field_simp; norm_num
  rw [hX, div_div_eq_mul_div] at hQ
  rw [div_le_iff₀ (by positivity)]
  calc Q ≤ B * (K * n * D) / (k * c * W * n * m * ε / 2) := hQ
    _ = B / (k * c * W * n * m * ε / 2) * (K * n * D) := by ring

/-- The main term of the rough upper comparison at the last charge root is at most
`W n m C_m C₁ n^{e-μ}`, with `C_m = 6 |C_e| + 2 + 3 C₁ log q`. -/
theorem roughUpper_main_le {d z W Ce n L D e mu lq C₁ m : ℝ} (hz : 1 / 2 ≤ z)
    (hd : Real.log d ≤ Ce * n ^ (1 + e)) (hW : 1 ≤ W) (hn : 1 ≤ n) (hL0 : 0 ≤ L)
    (hLn : L ≤ n) (he : 0 ≤ e) (hD : D ≤ C₁ * n ^ e) (hlq : 0 ≤ lq)
    (hm : 0 < m) (hnm : n ^ e / m ≤ C₁ * n ^ (e - mu)) :
    2 * Real.log d - Real.log z + W * (Ce * (n * L ^ e + n) / z + (1 + 3 * n * D * lq)) ≤
      W * n * m * ((6 * |Ce| + 2 + 3 * C₁ * lq) * C₁ * n ^ (e - mu)) := by
  have hn0 : 0 < n := by linarith
  have hz0 : 0 < z := by linarith
  have hne : 1 ≤ n ^ e := Real.one_le_rpow hn he
  have hn1e : n ^ (1 + e) = n * n ^ e := by rw [Real.rpow_add hn0, Real.rpow_one]
  have hLe : L ^ e ≤ n ^ e := Real.rpow_le_rpow hL0 hLn he
  have hC₁ : 0 ≤ C₁ := by
    have : 0 < n ^ e / m := by positivity
    have : 0 < C₁ * n ^ (e - mu) := by linarith
    exact (pos_of_mul_pos_left this (by positivity)).le
  have hlogz : -Real.log z ≤ 1 := by
    have : Real.log (1 / 2) ≤ Real.log z := Real.log_le_log (by norm_num) hz
    rw [one_div, Real.log_inv] at this
    linarith [Real.log_two_lt_d9]
  have hsh : Ce * (n * L ^ e + n) / z ≤ 4 * |Ce| * (n * n ^ e) := by
    rw [div_le_iff₀ hz0]
    have h1 : Ce * (n * L ^ e + n) ≤ |Ce| * (n * L ^ e + n) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h2 : n * L ^ e + n ≤ 2 * (n * n ^ e) := by nlinarith
    have h3 : 0 ≤ |Ce| := abs_nonneg _
    have h4 : 0 ≤ |Ce| * (n * n ^ e) * (2 * z - 1) :=
      mul_nonneg (mul_nonneg h3 (by positivity)) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hDl : 3 * n * D * lq ≤ 3 * C₁ * lq * (n * n ^ e) := by
    have := mul_le_mul_of_nonneg_left hD (show 0 ≤ 3 * n * lq by positivity)
    nlinarith
  have hpow : n * n ^ e ≤ n * m * (C₁ * n ^ (e - mu)) := by
    rw [div_le_iff₀ hm] at hnm
    nlinarith
  have hd' : 2 * Real.log d ≤ 2 * |Ce| * (n * n ^ e) := by
    rw [← hn1e]
    nlinarith [le_abs_self Ce, show 0 ≤ n ^ (1 + e) by positivity]
  have hbody : 2 * Real.log d - Real.log z +
      W * (Ce * (n * L ^ e + n) / z + (1 + 3 * n * D * lq)) ≤
      W * ((6 * |Ce| + 2 + 3 * C₁ * lq) * (n * n ^ e)) := by
    have hX : 1 ≤ n * n ^ e := by nlinarith
    have hW0 : 0 ≤ W := by linarith
    have hA : 0 ≤ |Ce| := abs_nonneg _
    have h4 : W * (Ce * (n * L ^ e + n) / z + (1 + 3 * n * D * lq)) ≤
        W * (4 * |Ce| * (n * n ^ e) + (n * n ^ e) + 3 * C₁ * lq * (n * n ^ e)) :=
      mul_le_mul_of_nonneg_left (by linarith) hW0
    have h5 : 2 * |Ce| * (n * n ^ e) + 1 ≤ W * ((2 * |Ce| + 1) * (n * n ^ e)) := by
      nlinarith [mul_nonneg hA (show 0 ≤ n * n ^ e by positivity)]
    nlinarith
  calc _ ≤ W * ((6 * |Ce| + 2 + 3 * C₁ * lq) * (n * n ^ e)) := hbody
    _ ≤ W * ((6 * |Ce| + 2 + 3 * C₁ * lq) * (n * m * (C₁ * n ^ (e - mu)))) := by
      gcongr
    _ = _ := by ring

/-- The numerator of the selection threshold, bounded by the leaf floor `log N₀² ≤ C log(k+2)`,
the rough upper comparison `-log N_end² ≤ k (B + r_k)` and the entropy-error coefficients,
is `(k c W n m ε / 2) (δ + ρ_k)` with `δ = C ε⁻¹ (n^{e-μ} + a^{1/4} L)` and `ρ_k` the
normalized replica remainder. -/
theorem selectionNumerator_le {k n m W ε cs a K A4 Lg Pe Cd Cβ Cinit Cm C₁ lk logN0 negLogN
    Bmain rem Cent ℓe βk : ℝ}
    (hk : 0 < k) (hn : 0 < n) (hm : 0 < m) (hW : 0 < W) (hε : 0 < ε) (hcs : 0 < cs)
    (hA4 : 0 ≤ A4) (haK : a * K = W) (hPe : 0 ≤ Pe) (hLg : 0 ≤ Lg)
    (h0 : logN0 ≤ Cinit * lk) (hend : negLogN ≤ k * (Bmain + rem))
    (hmain : Bmain ≤ W * n * m * (Cm * C₁ * Pe)) (hcent : Cent * ℓe ≤ Cd * Lg)
    (hβ : βk ≤ Cβ * lk) :
    logN0 + negLogN + 2 * n * m * (Cent * k * a * K * A4 * ℓe + βk) ≤
      (k * cs * W * n * m * ε / 2) *
        (2 / cs * max (Cm * C₁) (2 * Cd) * ε⁻¹ * (Pe + A4 * Lg) +
          2 / (cs * W * n * m * ε) *
            (Cinit * (lk / k) + |rem| + 2 * n * m * Cβ * (lk / k))) := by
  set M := max (Cm * C₁) (2 * Cd)
  have hM1 : Cm * C₁ ≤ M := le_max_left _ _
  have hM2 : 2 * Cd ≤ M := le_max_right _ _
  have e1 : (k * cs * W * n * m * ε / 2) *
      (2 / cs * M * ε⁻¹ * (Pe + A4 * Lg) +
        2 / (cs * W * n * m * ε) * (Cinit * (lk / k) + |rem| + 2 * n * m * Cβ * (lk / k))) =
      k * W * n * m * M * Pe + k * W * n * m * M * (A4 * Lg) +
        (Cinit * lk + k * |rem| + 2 * n * m * Cβ * lk) := by
    field_simp
  have t1 : Cent * k * a * K * A4 * ℓe = (Cent * ℓe) * (k * W * A4) := by rw [← haK]; ring
  have hkWA : 0 ≤ k * W * A4 := by positivity
  have hnm : 0 ≤ 2 * n * m := by positivity
  have hkWnm : 0 ≤ k * W * n * m := by positivity
  have a1 : k * Bmain ≤ k * W * n * m * M * Pe := by
    have := mul_le_mul_of_nonneg_left hmain hk.le
    have h2 : k * (W * n * m * (Cm * C₁ * Pe)) ≤ k * W * n * m * M * Pe := by
      have := mul_le_mul_of_nonneg_right hM1 hPe
      have := mul_le_mul_of_nonneg_left this hkWnm
      nlinarith
    linarith
  have a2 : 2 * n * m * ((Cent * ℓe) * (k * W * A4)) ≤ k * W * n * m * M * (A4 * Lg) := by
    have h1 := mul_le_mul_of_nonneg_right hcent hkWA
    have h2 := mul_le_mul_of_nonneg_left h1 hnm
    have h3 : 2 * n * m * (Cd * Lg * (k * W * A4)) ≤ k * W * n * m * M * (A4 * Lg) := by
      have := mul_le_mul_of_nonneg_right hM2 (show 0 ≤ k * W * n * m * (A4 * Lg) by positivity)
      nlinarith
    linarith
  have a3 : 2 * n * m * βk ≤ 2 * n * m * (Cβ * lk) := mul_le_mul_of_nonneg_left hβ hnm
  have a4 : k * rem ≤ k * |rem| := mul_le_mul_of_nonneg_left (le_abs_self _) hk.le
  rw [e1, t1]
  nlinarith

open Classical in
/-- **The selected density** [OAI265, eq. (9.6)]: for the collar scan at every large scale and
the replica prevector of a Schmidt–Bell label sequence, at every large replica count `k` some
charge round and some `p ∈ [ε/2, ε]` have
`𝒬(p)/(KnD) ≤ C ε⁻¹ (n^{e-μ} + a^{1/4} (log n)^{C_l}) + ρ_k`, with `ρ_k ≥ 0`, `ρ_k → 0`. -/
theorem exists_sourceScan_selected_density (X : ScannerExponents) (q R : ℕ) [NeZero q]
    {J Δ Ctr Ce ω : ℝ} (hΔ : 0 < Δ) (hCtr : 0 < Ctr) (hω : ω < 1 - X.ell - X.mu) :
    ∃ C Cl : ℝ, 0 ≤ C ∧ 0 ≤ Cl ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hT : T.Nonempty), A ⊆ Λ →
      (∀ d : ℕ, 1 ≤ d → d ≤ X.L n →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) →
      (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
        ((2 * X.L n + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) < ambientSupDistance t z) →
    let S := sourceScan X Ctr R Λ A T hT n
    ∃ (hm : 0 < S.m) (hM : 0 < S.M),
    ∀ (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ),
      IsAdmissible Λ R J Φ →
    ∀ (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
    ∀ (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ωt‖ = 1 →
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let Xs := S.A.filter fun x => x.val ∈ T
    ∀ (E : Finset (FiniteProduct.Configuration β Xs)) [NeZero E.card],
      1 / 2 ≤
        (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E →
      Real.log E.card ≤ Ce * (n : ℝ) ^ (1 + X.e) →
      (∀ j : Fin (X.L n + 1),
        FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
          Ce * ((n : ℝ) * (X.L n : ℝ) ^ X.e + n)) →
    ∀ (H : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ) (E₀ : ℝ)
      (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))),
      IsSchmidtBellLabels H Ωt E₀ Xs E ell →
    ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ ω →
      let d := E.card
      let a := W / (S.K : ℝ)
      let nA := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ => d)
      let pre : (k : ℕ) → Config k (fun v => Fin (nA v)) → ℂ := fun k =>
        replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
      let ε := (n : ℝ) ^ (-X.nu)
      ∃ ρ : ℕ → ℝ, (∀ k, 0 ≤ ρ k) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc (ε / 2) ε,
        S.actualChargeEntropyDefect hm hM s.val nA
            (S.actualEnergyTerms Φ Ω J Δ (X.L n) (fun _ => d)) (a / 2) k (pre k) p /
            ((S.K : ℝ) * n * S.D) ≤
          C * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl) + ρ k := by
  obtain ⟨c₀, Cent, eent, hc₀, hsel⟩ := CollarScan.actualCharges_selection_domainGraph
  obtain ⟨Cd, Cl, hCd, hCl, hcoef⟩ :=
    exists_transport_coefficients_log_bound (q := q) NeZero.one_le hCtr.le Cent eent 0 0
  obtain ⟨C₁, hC₁⟩ := eventually_scaleFacts X
  set μR : ℝ := (anchorMultiplicityBound R : ℝ) with hμR
  set cs : ℝ := 1 / (2 * (3 * μR + 1)) with hcs
  have hcspos : 0 < cs := by rw [hcs]; positivity
  set Cm : ℝ := 6 * |Ce| + 2 + 3 * C₁ * Real.log q with hCm
  set Mx : ℝ := max (Cm * C₁) (2 * Cd) with hMx
  have hMx0 : 0 ≤ Mx := le_trans (by linarith) (le_max_right _ _)
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (((hC₁.and (eventually_sourceScan_scales X hCtr.le)).and
    (eventually_div_bandCount_mul_transportLogDimBound_le X q hCtr.le hω hc₀)).and hlog)
  refine ⟨2 / cs * Mx, Cl, by positivity, hCl, N, ?_⟩
  intro n hn Λ A T _ hT hA hrows hclear S
  obtain ⟨⟨⟨hF, hn2, hr, h2r, hD1, hmargin, hL⟩, hsmall⟩, hlogn⟩ := hN n hn
  have hm : 0 < S.m := hF.one_le_m
  have hCpos : (0 : ℝ) < S.C₁ := by
    change (0 : ℝ) < 3 * μR; rw [hμR, anchorMultiplicityBound]; positivity
  have hM : 0 < S.M := chargeSlotCount_pos hCpos (by change 1 ≤ n; omega) hD1
  refine ⟨hm, hM, ?_⟩
  intro Φ hΦ Ω hΩ Ωt hΩt β Xs E _ hz hlogE hsh H E₀ ell hSB W hW1 hWω d a nA pre ε
  have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
                               linarith
  have hKpos : (0 : ℝ) < S.K := by
    have : (1 : ℝ) ≤ X.K n := by exact_mod_cast hF.one_le_K
    change (0 : ℝ) < X.K n; linarith
  have ha : 0 < a := div_pos (by linarith) hKpos
  have haK : a * S.K = W := div_mul_cancel₀ _ hKpos.ne'
  have haℓ : a * transportLogDimBound q S.r₀ ≤ c₀ := hsmall W (by linarith) hWω
  have hclear' : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * X.L n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
    rw [sourceScan_cutEndpoints X Ctr R hA hT n]; exact hclear
  have hD4 : 4 * S.D ≤ S.m := by change 4 * X.D n ≤ X.m n; omega
  obtain ⟨βs, Cβ, hCβ, hβ0, hβ, hsum⟩ := hsel (fun _ => d) Φ hΦ Ω S hT rfl rfl
    supportAnchor_mem hΔ hΩ (L := X.L n) (μ := anchorMultiplicityBound R) hn2 h2r hD1 hD4 hL
    hCpos le_rfl hrows (sourceScan_anchor_card_le X Ctr R Λ A T hT n) hclear' ha haℓ
  obtain ⟨Cinit, hCinit, hinit⟩ :=
    S.exists_actualFillData_initial_log_filteredNormSq_bound hm hM nA ha
  have hzpos : 0 <
      (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E := by
    linarith
  obtain ⟨c, hc, hrem, hru⟩ := S.eventually_actualScan_suppliedPrevector_rough_upper hT rfl rfl
    hm hM a ha (by change 0 < n; omega) hr hD1 hD4 (X.L n) hL hrows Ωt hΩt E ell _ hsh
    hzpos hSB.2.1
  have hmR : (0 : ℝ) < X.m n := by exact_mod_cast hm
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := hF.eps_lt_one
  have hlk (k : ℕ) : 0 ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
  have hlkk (k : ℕ) : 0 ≤ Real.log ((k : ℝ) + 2) / k := div_nonneg (hlk k) k.cast_nonneg
  have hY0 : 0 < cs * W * n * X.m n * ε := by
    have : (0 : ℝ) < W := by linarith
    positivity
  refine ⟨fun k => 2 / (cs * W * n * X.m n * ε) *
      (Cinit * (Real.log ((k : ℝ) + 2) / k) + |Real.bellOverlapRemainder d c S.K k| +
        2 * n * X.m n * Cβ * (Real.log ((k : ℝ) + 2) / k)), fun k => ?_, ?_, ?_⟩
  · have : 0 ≤ Cinit * (Real.log ((k : ℝ) + 2) / k) + |Real.bellOverlapRemainder d c S.K k| +
        2 * n * X.m n * Cβ * (Real.log ((k : ℝ) + 2) / k) := by
      have := hlkk k
      have : 0 ≤ 2 * n * X.m n * Cβ := by positivity
      positivity
    positivity
  · have h := (((tendsto_log_div_nat.const_mul Cinit).add hrem.abs).add
      (tendsto_log_div_nat.const_mul (2 * n * X.m n * Cβ))).const_mul
      (2 / (cs * W * n * X.m n * ε))
    simpa only [mul_zero, abs_zero, add_zero] using h
  filter_upwards [hru, eventually_ge_atTop 1] with k hk hk1
  have hkpos : 0 < k := hk1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  obtain ⟨hsymk, hnek, hnormk, -⟩ := hSB.augmentedPrevector hkpos
  obtain ⟨s, p, hp, hQ⟩ := hsum k (pre k) hkpos hsymk hnek (ε / 2) ε (by positivity)
    (by linarith) hε1.le
  refine ⟨s, p, hp, ?_⟩
  have h0 := hinit k (pre k) hnormk
  obtain ⟨t, ht⟩ : ∃ t, S.n * S.m = t + 1 :=
    ⟨S.n * S.m - 1, by
      have : 0 < S.n * S.m := Nat.mul_pos (show 0 < S.n by change 0 < n; omega) hm
      omega⟩
  obtain ⟨-, hNc, hch⟩ := hk t (by omega) 1
  have hNend : Transport.filteredNormSq
      ((S.actualFillData hm hM (S.n * S.m)).rootPath nA (a / 2) k 0) (pre k) =
      Transport.filteredNormSq ((S.actualChargeData hm hM t).rootPath nA (a / 2) k 1)
        (pre k) := by
    rw [ht]
    exact congrArg (fun M => Transport.filteredNormSq M (pre k))
      (S.charge_rootPath_one_eq_actualFillData_zero hm hM t nA (half_pos ha).le k).symm
  have hch' := (div_le_iff₀ hkR).1 hch
  have hn1 : (1 : ℝ) ≤ n := by linarith [show (2 : ℝ) ≤ n by exact_mod_cast hn2]
  have hLn : (X.L n : ℝ) ≤ n := by exact_mod_cast hF.L_le_n
  have hDR : (0 : ℝ) < S.D := by
    have : (1 : ℝ) ≤ X.D n := by exact_mod_cast hD1
    change (0 : ℝ) < X.D n; linarith
  have hmain := roughUpper_main_le (m := (X.m n : ℝ)) hz hlogE hW1 hn1 (Nat.cast_nonneg _) hLn
    X.e_pos.le hF.D_le (Real.log_natCast_nonneg q) hmR hF.pow_e_div_m_le
  have hcent := (hcoef n hlogn (transportLogDimBound q S.r₀)
    (one_le_transportLogDimBound NeZero.one_le _) le_rfl).1
  have hnum := selectionNumerator_le (k := (k : ℝ)) (n := (n : ℝ)) (m := (X.m n : ℝ))
    (ε := ε) (cs := cs) (a := a) (K := (S.K : ℝ)) (A4 := a ^ (1 / 4 : ℝ))
    (Lg := Real.log n ^ Cl) (Pe := (n : ℝ) ^ (X.e - X.mu)) (Cinit := Cinit)
    (lk := Real.log ((k : ℝ) + 2)) (rem := Real.bellOverlapRemainder d c S.K k)
    (logN0 := Real.log (Transport.filteredNormSq
      ((S.actualFillData hm hM 0).rootPath nA (a / 2) k 0) (pre k)))
    (negLogN := -Real.log (Transport.filteredNormSq
      ((S.actualFillData hm hM (S.n * S.m)).rootPath nA (a / 2) k 0) (pre k)))
    (βk := βs k) hkR hn0 hmR (by linarith) hε0 hcspos (by positivity) haK (by positivity)
    (by positivity) h0 (by rw [hNend, mul_comm, ← haK]; exact hch') hmain hcent (hβ k)
  have hcastnm : ((S.n * S.m : ℕ) : ℝ) = (n : ℝ) * X.m n := by push_cast; rfl
  have hcast2 : ((2 * S.n * S.m : ℕ) : ℝ) = 2 * (n : ℝ) * X.m n := by push_cast; rfl
  rw [hcastnm, hcast2] at hQ
  have hQ' := div_le_of_le_selectionThreshold (c := cs) hkR ha hcspos hn0 hDR hmR hKpos hε0
    haK hQ
  have hY : 0 < (k : ℝ) * cs * W * n * X.m n * ε / 2 := by
    have : (0 : ℝ) < W := by linarith
    positivity
  refine hQ'.trans ((div_le_iff₀ hY).2 ?_)
  linarith

end OpenAI.Scan
