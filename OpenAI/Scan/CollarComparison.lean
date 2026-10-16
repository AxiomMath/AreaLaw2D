import OpenAI.Scan.ScannerSelection
import OpenAI.Scan.FinalCollarScales
import OpenAI.Scan.ActualSharpLowerPrevector
import OpenAI.Scan.SourceScanScales
import OpenAI.Scan.TerminalEntropyGapBound
import OpenAI.Scan.SharpComparisonSubtraction
import OpenAI.Scan.CollarErrorAbsorption
import OpenAI.SelectedSchmidtEntropyBounds

/-!
# The sharp collar comparison

The core of the proof of Proposition 9.6 [OAI265, §9.5]: at the final parameters of
eq. (9.17), with total metric weight `W = n^ω`, `ω = 1/20000`, the sharp upper and lower
comparisons of Proposition 8.1 at the interpolation selected by Proposition 9.2 bound
`2 S(X) + ⟨g_pre - g_post⟩_leaf` by `C n^{1-ε}`, `ε = 10⁻⁵`, for the truncated ground state.
Here `⟨·⟩_leaf` is the terminal-tree and uniform band average, and at each leaf with physical
partition `X, U, Y, V`, `g_pre = S(XU) + S(V) - S(Y)` and `g_post = S(U) + S(UY) - S(Y)`
(eqs. (9.18)–(9.20) and the table after eq. (9.20)).

The proof follows the paper.  At a fixed scale, Proposition 9.2
(`OpenAI.Scan.exists_sourceScan_selection`) with the final energy estimate
(`OpenAI.Scan.eventually_final_energy_le`) selects, for every `η > 0` and all large replica
counts `k`, a charge round and an interpolation parameter whose defect energy is at most
`n^{-1/2000} + η`.  At that charge root the sharp lower comparison
(`OpenAI.Scan.CollarScan.exists_actualScan_suppliedPrevector_sharp_lower`) and the sharp upper
comparison (`OpenAI.Scan.CollarScan.eventually_actualScan_suppliedPrevector_sharp_upper`) bound
the same `-log N² / k`; subtracting them
(`OpenAI.Scan.two_mul_add_inv_mul_sum_sub_le_of_sharp_comparisons`), the uniform bound
`g_pre ≤ C n^{1+e_*}` (`OpenAI.Scan.CollarScan.terminalPartition_entropyGap_le`), the typical
entropies `S'`, `log d` within `n^{3/5} - log z` of `S(X)` and the error table
(`OpenAI.Scan.eventually_final_collar_errors_le`) give the bound up to a remainder; choosing
`η` and then `k` makes the remainder at most one.

## Main statements

* `OpenAI.Scan.sourceScan_collar_leaf_bound`: the sharp collar comparison.
* `OpenAI.Scan.eventually_final_collar_scales`: the scale facts at the final exponents.
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- The scale facts used at the final exponents [OAI265, eqs. (9.1), (9.17)–(9.19)]: at every
large `n`, the scale separations of the collar scan, the window `n^{ω-1} ≤ a ≤ n^{-0.7499}`
for `a = n^ω / K`, the final energy estimate (9.18) and the error table after (9.20) for the
given constants, and the smallness of `n^{-100}`, `τ = n^{-1/4000}`, `n^{-0.7499}`, `1/log n`
and `1/(C_b n)`. -/
theorem eventually_final_collar_scales (Ctr Cb C₂ Cl c : ℝ) (hCtr : 0 ≤ Ctr) (hC₂ : 0 ≤ C₂)
    (hc0 : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop,
      (2 ≤ n ∧ roundedLogRadius Ctr n ≤ finalExponents.D n ∧
        2 * roundedLogRadius Ctr n ≤ finalExponents.D n ∧ 1 ≤ finalExponents.D n ∧
        4 * (finalExponents.D n + 2 * roundedLogRadius Ctr n) ≤ finalExponents.m n ∧
        8 * finalExponents.K n * finalExponents.m n ≤ finalExponents.L n) ∧
      (1 ≤ n ∧ (n : ℝ) ^ ((Exponents.scannerOmega : ℝ) - 1) ≤
          (n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ) ∧
        (n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ) ≤
          (n : ℝ) ^ (-(7499 / 10000 : ℝ))) ∧
      (C₂ * (n : ℝ) ^ finalExponents.ell * (finalExponents.D n : ℝ) ^ 2 *
          ((n : ℝ) ^ (Exponents.scannerOmega : ℝ)) ^ 2 * Real.log n ^ Cl *
          ((C₂ * ((n : ℝ) ^ (-finalExponents.nu))⁻¹ *
            ((n : ℝ) ^ (finalExponents.e - finalExponents.mu) +
              ((n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ)) ^ (1 / 4 : ℝ) *
                Real.log n ^ Cl)) ^ (1 / 8 : ℝ) +
            (n : ℝ) ^ (-finalExponents.nu) + (n : ℝ) ^ (-100 : ℝ)) +
          C₂ * (n : ℝ) ^ (-1000 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2000 : ℝ))) ∧
      c * ((((n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) + 1) /
            (n : ℝ) ^ (Exponents.scannerOmega : ℝ) + (n : ℝ) ^ (3 / 5 : ℝ) +
          ((n : ℝ) ^ (-(1 / 4000 : ℝ)) + (n : ℝ) ^ (-(1 / 2000 : ℝ)) /
            (n : ℝ) ^ (-(1 / 4000 : ℝ))) * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) +
          Real.binEntropy ((n : ℝ) ^ (-(1 / 4000 : ℝ))) /
            ((n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ)) +
          (n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ) * n *
            (finalExponents.D n : ℝ) * Real.log n ^ (12 : ℝ) +
          (n : ℝ) ^ (-100 : ℝ) /
            ((n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (finalExponents.K n : ℝ)))) ≤
        (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) ∧
      (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 ∧ (n : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 / 2 ∧
      1 ≤ Real.log n ∧ 1 / Cb ≤ n ∧ (n : ℝ) ^ (-(7499 / 10000 : ℝ)) ≤ 1 / 10 := by
  have hsmall : ∀ r : ℝ, r < 0 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ r ≤ ε := fun r hr ε hε ↦
    ((tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp tendsto_natCast_atTop_atTop).eventually
      (Iic_mem_nhds hε) |>.mono fun n hn ↦ by simpa using hn
  filter_upwards [eventually_sourceScan_scales finalExponents hCtr, eventually_final_bandWeight_mem,
    eventually_final_energy_le C₂ C₂ Cl hC₂ hC₂, eventually_final_collar_errors_le c 12 hc0,
    hsmall (-100) (by norm_num) (1 / 2) (by norm_num),
    hsmall (-(1 / 4000)) (by norm_num) (1 / 2) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_ge_atTop ⌈1 / Cb⌉₊,
    hsmall (-(7499 / 10000)) (by norm_num) (1 / 10) (by norm_num)]
    with n h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, Nat.ceil_le.mp h8, h9⟩

/-- At the final exponents, `2 S + 2 C_e (n L^{e_*} + n) + 6 n D log q ≤ C₁ n^{1+e_*}` with
`C₁ = 6 max(C_e, 0) + 12 log q`, for `S ≤ max(C_e, 0) n^{1+e_*}`: the right side of the uniform
bound on `g_pre` (`OpenAI.Scan.CollarScan.terminalPartition_entropyGap_le`) at the final
scales. -/
theorem final_entropyGap_bound_le (q : ℕ) {n : ℕ} (hn : 1 ≤ n) {Ce Sx : ℝ}
    (hSx : Sx ≤ max Ce 0 * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ))) :
    2 * Sx + 2 * (Ce * ((n : ℝ) * (finalExponents.L n : ℝ) ^ (Exponents.boxError : ℝ) + n)) +
        2 * ((3 * n * finalExponents.D n : ℕ) : ℝ) * Real.log q ≤
      (6 * max Ce 0 + 12 * Real.log q) * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  set X := finalExponents
  set P := (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) with hP_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hCeP0 : 0 ≤ max Ce 0 := le_max_right _ _
  have hℓ : X.ell = 1 / 100000 := by norm_num [X, finalExponents, Exponents.scannerEll]
  have hκ : X.kappa = 1 / 1000000 := by norm_num [X, finalExponents, Exponents.scannerKappa]
  have hLn : (X.L n : ℝ) ≤ n := by
    have : X.L n ≤ n := Nat.floor_le_of_le (by
      simpa using Real.rpow_le_rpow_of_exponent_le hn1
        (by rw [hℓ]; norm_num : 1 - X.ell ≤ 1))
    exact_mod_cast this
  have hLe : (X.L n : ℝ) ^ (Exponents.boxError : ℝ) ≤ (n : ℝ) ^ (Exponents.boxError : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hLn (by norm_num [Exponents.boxError])
  have hnLe : (n : ℝ) * (X.L n : ℝ) ^ (Exponents.boxError : ℝ) ≤ P := by
    rw [hP_def, Real.rpow_add hn0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hLe hn0.le
  have hnP : (n : ℝ) ≤ P := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1
      (show (1 : ℝ) ≤ 1 + (Exponents.boxError : ℝ) by norm_num [Exponents.boxError])
  have hCe : Ce * ((n : ℝ) * (X.L n : ℝ) ^ (Exponents.boxError : ℝ) + n) ≤ max Ce 0 * (2 * P) :=
    mul_le_mul (le_max_left _ _) (by linarith only [hnLe, hnP]) (by positivity) hCeP0
  have hD : (X.D n : ℝ) ≤ 2 * (n : ℝ) ^ (Exponents.boxError : ℝ) := by
    have hceil : (X.D n : ℝ) < (n : ℝ) ^ X.kappa + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le _)
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ X.kappa := Real.one_le_rpow hn1 (by rw [hκ]; norm_num)
    have h2 : (n : ℝ) ^ X.kappa ≤ (n : ℝ) ^ (Exponents.boxError : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hκ]; norm_num [Exponents.boxError])
    linarith only [hceil, h1, h2]
  have hnD : ((3 * n * X.D n : ℕ) : ℝ) ≤ 6 * P := by
    push_cast
    rw [hP_def, Real.rpow_add hn0, Real.rpow_one]
    have := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 3 * n)
    linarith only [this]
  have h3 := mul_le_mul_of_nonneg_right hnD hlogq
  calc _ ≤ 2 * (max Ce 0 * P) + 2 * (max Ce 0 * (2 * P)) + 2 * (6 * P * Real.log q) := by
        linarith only [hSx, hCe, h3]
    _ = _ := by ring

open Classical in
/-- **The sharp collar comparison for a supplied truncated ground state** [OAI265, proof of
Proposition 9.6, eqs. (9.17)–(9.20) and the table of error exponents].  At the final exponents
and `W = n^{1/20000}`, at every large scale, for the collar scan of a target obeying the test
geometry and every unit ground vector `Ωt` of the truncated Hamiltonian with energy at most
`n^{-1000}`, gap at least `g₀`, the marginal moment bound of Lemma 3.1 on every status region
with parameter `𝓑 = C_b n D log¹² n`, a spectral set `E` of its target marginal of mass at least
`1 - n^{-100}` in the window of width `n^{3/5}`, target entropy at most `C_e n^{1+e_*}`, every
positive-depth prefix of entropy at most `C_e (n L^{e_*} + n)`, and a Schmidt–Bell label
sequence: some terminal mean tree of the actual scan gives
`2 S(X) + K⁻¹ ∑_g ∑_j w_j (g_pre - g_post) ≤ C n^{1-10⁻⁵}`, all entropies of `Ωt`.  The tree is
that of the charge root selected by Proposition 9.2 at a large replica count. -/
theorem sourceScan_collar_leaf_bound (q R : ℕ) [NeZero q]
    {J Δ Ctr CT Ce g₀ ϑ Cb : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) (hCtr : 0 < Ctr) (hCT : 0 ≤ CT)
    (hg₀ : 0 < g₀) (hϑ : 0 ≤ ϑ) (hCb : 0 < Cb) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hA : A ⊆ Λ)
      (hT : T.Nonempty),
      let L := finalExponents.L n
      (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2 →
      (∀ d : ℕ, 1 ≤ d → d ≤ L →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) →
      (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
        ((2 * L + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) < ambientSupDistance t z) →
    let S := sourceScan finalExponents Ctr R Λ A T hT n
    ∀ (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ),
      IsAdmissible Λ R J Φ →
    ∀ (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
    ∀ (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (e gap : ℝ) (hΩt : ‖Ωt‖ = 1),
      (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ Ωt.ofLp = (e : ℂ) • Ωt.ofLp →
      ((∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) - (e : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 ≤ e → e ≤ (n : ℝ) ^ (-1000 : ℝ) → g₀ ≤ gap →
    let B := Cb * (n : ℝ) * (S.D : ℝ) * Real.log n ^ 12
    (∀ (s : ℕ) (hist : History S.K S.m S.M s) (g' : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g'),
        ∀ u : ℝ, |u| ≤ tailRadius ϑ B →
          Real.log (surprisalMoment
            ((pureState Ωt.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
              (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
            u * (pureState Ωt.ofLp
                (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) Q) +
              512 * Real.exp 1 * ϑ * B * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g'),
        ∀ u : ℝ, |u| ≤ tailRadius ϑ B →
          Real.log (surprisalMoment
            ((pureState Ωt.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
              (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
            u * (pureState Ωt.ofLp
                (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) Q) +
              512 * Real.exp 1 * ϑ * B * u ^ 2)) →
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let Xs := S.A.filter fun x => x.val ∈ T
    ∀ (E : Finset (FiniteProduct.Configuration β Xs)) [NeZero E.card],
      1 - (n : ℝ) ^ (-100 : ℝ) ≤
        (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E →
      (∀ i ∈ E,
        Real.exp (-FiniteProduct.entropy β Ωt Xs - (n : ℝ) ^ (3 / 5 : ℝ)) ≤
            (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues i ∧
          (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues i ≤
            Real.exp (-FiniteProduct.entropy β Ωt Xs + (n : ℝ) ^ (3 / 5 : ℝ))) →
      FiniteProduct.entropy β Ωt Xs ≤ Ce * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) →
      (∀ j : Fin (L + 1),
        FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + n)) →
    ∀ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      IsSchmidtBellLabels (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) Ωt e Xs E ell →
    ∃ Tr : MeanTree (CollarScan.ActualTerminals.terminalFamily S.K S.m S.M (S.n * S.m)),
      let σ := CollarScan.ActualTerminals.terminalPartition S (S.n * S.m)
      let ent := FiniteProduct.entropy β Ωt
      let gpre := fun j g => ent (receiving (σ j g) false) +
        ent (receiving (σ j g) false ∪ middle (σ j g))ᶜ - ent (middle (σ j g))
      let gpost := fun j g => ent (positiveNear S.depth (σ j g)) +
        ent (positiveNearMiddle S.depth (σ j g)) - ent (middle (σ j g))
      2 * ent Xs + (S.K : ℝ)⁻¹ * ∑ g, ∑ j, Tr.weight j * (gpre j g - gpost j g) ≤
        C * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by
  classical
  have hω : (Exponents.scannerOmega : ℝ) < 1 - finalExponents.ell - finalExponents.mu := by
    norm_num [finalExponents, Exponents.scannerOmega, Exponents.scannerEll, Exponents.scannerMu]
  obtain ⟨C₂, Cl, hC₂, N₂, hsel⟩ := exists_sourceScan_selection finalExponents q R
    (Ce := max Ce 0 + 3) hJ hΔ hCtr hCT hg₀ hω
  set X := finalExponents with hXdef
  set CeP := max Ce 0 with hCeP
  have hCeP0 : 0 ≤ CeP := le_max_right _ _
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  set C₁ : ℝ := 6 * CeP + 12 * Real.log q with hC₁
  have hC₁0 : 0 ≤ C₁ := add_nonneg (mul_nonneg (by norm_num) hCeP0) (mul_nonneg (by norm_num) hlogq)
  have h37 : 0 ≤ 37 * (512 * Real.exp 1 * ϑ * Cb) := mul_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hϑ) hCb.le)
  set c : ℝ := C₁ + 4 * CeP + 10 + 37 * (512 * Real.exp 1 * ϑ * Cb) with hc
  have hc0 : 0 ≤ c := by linarith only [hC₁0, hCeP0, h37]
  have hmargin : (Exponents.scannerOmega : ℝ) + (1 + X.kappa) / 2 < 1 - X.ell - X.mu := by
    have := final_scanner_moment_margin
    change (Exponents.scannerOmega : ℝ) + (1 + (Exponents.scannerKappa : ℝ)) / 2 <
      1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ)
    linarith
  obtain ⟨N₃, -, hrad⟩ := X.exists_a_le_moment_radius (A := 10)
    (c := 1 / (32 * Real.sqrt (1 + ϑ))) hmargin hCb.le (by norm_num) (by positivity)
  have hev := eventually_final_collar_scales Ctr Cb C₂ Cl c hCtr.le hC₂ hc0
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp hev
  refine ⟨2, max N₂ (max N₃ N₄), ?_⟩
  intro n hn Λ A T _ hA hT L hTcard hrows hclear S Φ hΦ Ω hΩ Ωt e gap hΩt heig hpsd he0 he1
    hgap B hmom β Xs E _ hz hEw hSx hsh ell hSB
  obtain ⟨⟨hn2, hr, -, hDpos, hmD, hL⟩, ⟨-, -, haUp⟩, hEn, hErr, hν, hτhalf, hlogn, hnCb,
    ha10⟩ := hN₄ n (le_of_max_le_right (le_of_max_le_right hn))
  obtain ⟨hK1, hradn⟩ := hrad n (le_of_max_le_left (le_of_max_le_right hn))
  obtain ⟨hm, hM, hsel'⟩ := hsel n (le_of_max_le_left hn) Λ A T hA hT hTcard hrows hclear
  -- scalar facts at the scale `n`
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  set W : ℝ := (n : ℝ) ^ (Exponents.scannerOmega : ℝ) with hW
  have hW1 : 1 ≤ W := Real.one_le_rpow hn1 (by norm_num [Exponents.scannerOmega])
  have hK0 : 0 < S.K := hK1
  have hK0' : (0 : ℝ) < S.K := by exact_mod_cast hK0
  set a : ℝ := W / (S.K : ℝ) with ha_def
  have ha0 : 0 < a := div_pos (by linarith only [hW1]) hK0'
  have haK : a * S.K = W := by rw [ha_def]; field_simp
  have ha1 : 10 * a ≤ 1 := by
    have : a ≤ 1 / 10 := haUp.trans ha10
    linarith only [this]
  have hB1 : 1 ≤ B := by
    have hD1 : (1 : ℝ) ≤ S.D := by exact_mod_cast hDpos
    have hl : (1 : ℝ) ≤ Real.log n ^ 12 := one_le_pow₀ hlogn
    have h1 : 1 ≤ Cb * (n : ℝ) := by
      rw [div_le_iff₀ hCb] at hnCb; linarith only [hnCb]
    calc (1 : ℝ) ≤ Cb * (n : ℝ) * 1 * 1 := by rw [_root_.mul_one, _root_.mul_one]; exact h1
      _ ≤ Cb * (n : ℝ) * (S.D : ℝ) * Real.log n ^ 12 := by
        have : 0 ≤ Cb * (n : ℝ) := mul_nonneg hCb.le hn0.le
        gcongr
  set Kmom : ℝ := 512 * Real.exp 1 * ϑ * B with hKmom
  have hKmom0 : 0 ≤ Kmom := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hϑ) (by linarith only [hB1])
  set rM : ℝ := tailRadius ϑ B with hrM
  have h10ar : 10 * a ≤ rM := by
    have h := hradn W B (by linarith only [hW1]) le_rfl hB1 le_rfl
    have hsq : Real.sqrt ((1 + ϑ) * B) = Real.sqrt (1 + ϑ) * Real.sqrt B :=
      Real.sqrt_mul (by linarith only [hϑ]) B
    calc 10 * a = 10 * X.a W n := rfl
      _ ≤ 1 / (32 * Real.sqrt (1 + ϑ)) / Real.sqrt B := h
      _ = rM := by rw [hrM, tailRadius, hsq]; field_simp
  -- the typical mass and the typical entropies
  set ν : ℝ := (n : ℝ) ^ (-100 : ℝ) with hν_def
  have hν0 : 0 ≤ ν := Real.rpow_nonneg hn0.le _
  set z := (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E
    with hz_def
  have hz0 : 0 < z := by linarith only [hz, hν]
  have hz1 : z ≤ 1 := (FiniteProduct.reducedPure_posSemidef β Ωt Xs).spectralRestrictionMass_le_one
    (FiniteProduct.trace_reducedPure β Ωt hΩt Xs) E
  set ζ : ℝ := -Real.log z with hζ_def
  have hζ0 : 0 ≤ ζ := neg_nonneg.mpr (Real.log_nonpos hz0.le hz1)
  have hζ : ζ ≤ 2 * ν := by
    have h1 : ζ ≤ z⁻¹ - 1 := by
      rw [hζ_def, ← Real.log_inv]; exact Real.log_le_sub_one_of_pos (inv_pos.mpr hz0)
    have h2 : z⁻¹ - 1 ≤ 2 * ν := by
      rw [inv_eq_one_div, div_sub_one hz0.ne', div_le_iff₀ hz0]
      have hz2 : 1 / 2 ≤ z := by linarith only [hz, hν]
      have := mul_le_mul_of_nonneg_left hz2 (mul_nonneg zero_le_two hν0)
      linarith only [this, hz]
    linarith only [h1, h2]
  set w : ℝ := (n : ℝ) ^ (3 / 5 : ℝ) with hw_def
  have hw0 : 0 ≤ w := Real.rpow_nonneg hn0.le _
  set Sx := FiniteProduct.entropy β Ωt Xs with hSx_def
  have hSx0 : 0 ≤ Sx := FiniteProduct.entropy_nonneg β Ωt hΩt Xs
  set P : ℝ := (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) with hP_def
  have hP1 : 1 ≤ P := Real.one_le_rpow hn1 (by norm_num [Exponents.boxError])
  have hwP : w ≤ P := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num [Exponents.boxError])
  have hSxP : Sx ≤ CeP * P := hSx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (by linarith only [hP1]))
  have hbounds := OpenAI.abs_log_card_and_selectedSchmidtEntropy_sub_le Ωt hΩt Xs E w hz0 hEw
  simp only at hbounds
  obtain ⟨hlogd, hS'⟩ := hbounds
  rw [abs_le] at hlogd hS'
  -- the selection of Proposition 9.2
  have hz2 : 1 / 2 ≤ z := by linarith only [hz, hν]
  have hlogE : Real.log E.card ≤ (max Ce 0 + 3) * (n : ℝ) ^ (1 + X.e) := by
    have : Real.log E.card ≤ Sx + w + ζ := by linarith only [hlogd.2, hζ_def]
    change Real.log E.card ≤ (CeP + 3) * P
    linarith only [this, hSxP, hwP, hζ, hν, hP1]
  have hsh' : ∀ j : Fin (X.L n + 1),
      FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
        (max Ce 0 + 3) * ((n : ℝ) * (X.L n : ℝ) ^ X.e + n) := fun j ↦
    (hsh j).trans (mul_le_mul_of_nonneg_right (by linarith only [le_max_left Ce 0])
      (add_nonneg (mul_nonneg hn0.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hn0.le))
  have hselη := hsel' Φ hΦ Ω hΩ Ωt e gap hΩt heig he0 he1 hgap E hz2 hlogE hsh' ell hSB W hW1
    le_rfl
  -- the sharp lower and upper comparisons at every charge root
  have hgap0 : 0 < gap := hg₀.trans_le hgap
  obtain ⟨cL, Cf, -, -, hremL, hlow⟩ :=
    CollarScan.exists_actualScan_suppliedPrevector_sharp_lower (d := E.card) S hm hM Φ hΦ Ω Δ L
      Ωt e gap hΩt hpsd hgap0 a Kmom rM ha0 h10ar ha1 hKmom0 ell _
      (fun k hk ↦ ⟨(hSB.1 k hk).1, (hSB.1 k hk).2.1⟩) hSB.2.2 hmom
  obtain ⟨cU, -, hremU, hup⟩ :=
    CollarScan.eventually_actualScan_suppliedPrevector_sharp_upper hT S rfl hm hM a Kmom rM ha0
      (by linarith only [h10ar, ha0]) (by linarith only [ha1, ha0]) L hL Ωt hΩt E ell hmom hz0
      hSB.2.1
  -- the uniform bound on `g_pre`
  have hgapb := fun j g ↦ CollarScan.terminalPartition_entropyGap_le hT S rfl rfl
    (by change 0 < n; omega) hr hDpos
    (by change 4 * finalExponents.D n ≤ finalExponents.m n; omega) hL hrows Ωt hΩt hsh j g
  have hGb : 2 * Sx + 2 * (Ce * ((n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + n)) +
      2 * ((3 * S.n * S.D : ℕ) : ℝ) * Real.log q ≤ C₁ * P :=
    final_entropyGap_bound_le q (n := n) (by omega) hSxP
  -- the replica count and the selected charge root
  obtain ⟨Mb, hMb⟩ : ∃ x : ℝ, x = (2 * CeP + 4 + C₁) * P := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := hMb ▸ mul_nonneg (by linarith only [hCeP0, hC₁0]) (by linarith only [hP1])
  set τ : ℝ := (n : ℝ) ^ (-(1 / 4000 : ℝ)) with hτ_def
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hn0 _
  obtain ⟨η, hη_def⟩ : ∃ x : ℝ, x = τ / (2 * (Mb + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := hη_def ▸ div_pos hτ0 (by linarith only [hMb0])
  obtain ⟨k, ⟨s, p, -, hEk⟩, hupk, hremLk, hremUk, hk1⟩ :=
    ((hselη η hη0).and (hup.and ((hremL.eventually (Iic_mem_nhds
      (by norm_num : (0 : ℝ) < 1 / 4))).and ((hremU.eventually (Iic_mem_nhds
      (by norm_num : (0 : ℝ) < 1 / 8))).and (eventually_ge_atTop 1))))).exists
  obtain ⟨-, -, -, hlowk⟩ := (hlow k hk1 s p).2
  have hlowτ := hlowk τ hτ0 hτhalf
  have hupτ := ((hupk s.val s.isLt p).2).2
  let Tr := ((S.actualChargeData hm hM s.val).tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
    (CollarScan.ActualTerminals.chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
  refine ⟨Tr, ?_⟩
  intro σ ent gpre gpost
  simp only [regionalEntropy_eq_finiteProduct] at hupτ
  have hsub := two_mul_add_inv_mul_sum_sub_le_of_sharp_comparisons hK0 ha0
    (fun g ↦ ∑ j, Tr.weight j * gpre j g) (fun g ↦ ∑ j, Tr.weight j * gpost j g) hlowτ hupτ
  -- the uniform bound enters the average and the maximal gap
  have hpre_le : ∀ j g, gpre j g ≤ C₁ * P := fun j g ↦ (hgapb j g).trans hGb
  have hG : (S.K : ℝ)⁻¹ * ∑ g, ∑ j, Tr.weight j * gpre j g ≤ C₁ * P := by
    have hrow : ∀ g, ∑ j, Tr.weight j * gpre j g ≤ C₁ * P := fun g ↦ by
      calc ∑ j, Tr.weight j * gpre j g ≤ ∑ j, Tr.weight j * (C₁ * P) :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left (hpre_le j g) (Tr.weight_nonneg j)
        _ = C₁ * P := by rw [← Finset.sum_mul, Tr.sum_weight, _root_.one_mul]
    calc (S.K : ℝ)⁻¹ * ∑ g, ∑ j, Tr.weight j * gpre j g ≤ (S.K : ℝ)⁻¹ * ∑ _g : Fin S.K, C₁ * P :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ ↦ hrow g) (inv_nonneg.mpr hK0'.le)
      _ = C₁ * P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← _root_.mul_assoc, inv_mul_cancel₀ hK0'.ne', _root_.one_mul]
  have hgmax : ∀ y ∈ insert (0 : ℝ) ((Finset.univ : Finset
      (CollarScan.ActualTerminals.terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
        fun j ↦ gpre j.1 j.2), y ≤ C₁ * P := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hy0 | hy
    · rw [hy0]; exact mul_nonneg hC₁0 (by linarith only [hP1])
    · obtain ⟨⟨j, g⟩, -, hyj⟩ := Finset.mem_image.mp hy
      rw [← hyj]; exact hpre_le j g
  -- the errors of eq. (9.19)
  have hQ : ∑ g, ∑ j, Tr.weight j * (gpre j g - gpost j g) =
      ∑ g, ((fun g ↦ ∑ j, Tr.weight j * gpre j g) g -
        (fun g ↦ ∑ j, Tr.weight j * gpost j g) g) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hQ]
  have hηM : ∀ M : ℝ, M ≤ Mb → η / τ * M ≤ 1 / 2 := fun M hM ↦ by
    have hητ : η / τ = 1 / (2 * (Mb + 1)) := by rw [hη_def]; field_simp
    calc η / τ * M ≤ η / τ * Mb := mul_le_mul_of_nonneg_left hM (div_nonneg hη0.le hτ0.le)
      _ = Mb / (2 * (Mb + 1)) := by rw [hητ]; ring
      _ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith only [hMb0])]; linarith only [hMb0]
  have hbell : 2 / W * Real.bellOverlapRemainder E.card cU S.K k ≤ 1 / 4 := by
    calc 2 / W * Real.bellOverlapRemainder E.card cU S.K k ≤ 2 / W * (1 / 8) :=
          mul_le_mul_of_nonneg_left hremUk (div_nonneg zero_le_two (by linarith only [hW1]))
      _ ≤ 1 / 4 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith only [hW1])]
          linarith only [hW1]
  have hKe : Kmom = 512 * Real.exp 1 * ϑ * (Cb * n * (X.D n : ℝ) * Real.log n ^ 12) := rfl
  refine (two_mul_add_le_of_subtracted_comparison (Sx := Sx) (logz := Real.log z) (ν := ν)
    (w := w) (P := P) (E₀ := (n : ℝ) ^ (-(1 / 2000 : ℝ))) (η := η)
    (aB := a * n * (X.D n : ℝ) * Real.log n ^ (12 : ℝ)) (Ce := CeP) (C₁ := C₁) (c := c)
    hτ0 ha0 (by linarith only [ha1, ha0]) (by linarith only [hW1]) haK hP1 hw0 hwP
    (Real.log_nonpos hz0.le hz1) hζ hν hCeP0 hC₁0 hSxP ?_ ?_ ?_ hG (le_max_left _ _) ?_ ?_
    (Real.rpow_nonneg hn0.le _) (Real.binEntropy_nonneg hτ0.le (by linarith only [hτhalf]))
    ?_ ?_ hsub ?_).trans ?_
  · linarith only [hS'.1]
  · linarith only [hS'.2]
  · linarith only [hlogd.2]
  · exact max_le_max le_rfl (add_le_add le_rfl (Finset.max'_le _ _ _ hgmax))
  · exact hEk.trans (add_le_add hEn le_rfl)
  · rw [Real.rpow_ofNat, hKe]
    have h37' : 37 * (512 * Real.exp 1 * ϑ * Cb) ≤ c := by
      rw [hc]; linarith only [hC₁0, hCeP0]
    calc 37 * (512 * Real.exp 1 * ϑ * (Cb * n * (X.D n : ℝ) * Real.log n ^ 12)) * a =
          37 * (512 * Real.exp 1 * ϑ * Cb) * (a * n * (X.D n : ℝ) * Real.log n ^ 12) := by ring
      _ ≤ c * (a * n * (X.D n : ℝ) * Real.log n ^ 12) :=
          mul_le_mul_of_nonneg_right h37' (mul_nonneg (mul_nonneg (mul_nonneg ha0.le hn0.le)
            (Nat.cast_nonneg _)) (pow_nonneg (by linarith only [hlogn]) _))
  · rw [hc]
    linarith only [h37]
  · refine le_trans (add_le_add (add_le_add (hηM _ ?_) hremLk) hbell) (by norm_num)
    refine (max_le_max le_rfl (add_le_add le_rfl (Finset.max'_le _ _ _ hgmax))).trans
      (max_le hMb0 ?_)
    rw [hMb]
    linarith only [hS'.2, hSxP, hwP, hζ, hζ_def, hν, hP1]
  · have hfin : c * ((P + 1) / W + w + (τ + (n : ℝ) ^ (-(1 / 2000 : ℝ)) / τ) * P +
        Real.binEntropy τ / a + a * n * (X.D n : ℝ) * Real.log n ^ (12 : ℝ) + ν / a) ≤
        (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := hErr
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := Real.one_le_rpow hn1 (by norm_num)
    linarith only [hfin, h1]

end OpenAI.Scan
