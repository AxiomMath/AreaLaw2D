import OpenAI.Scan.SourceScan
import OpenAI.Scan.ActualRoughUpper
import OpenAI.Scan.SourceScanSelectedDensity
import OpenAI.Scan.SourceScanSelectedEnergy

/-!
# The scanner estimate for the collar scan

Proposition 9.2 of [OAI265] for the collar scan `OpenAI.Scan.sourceScan` and the replica
prevector of a supplied Schmidt–Bell label sequence: at every large scale, for every large
replica count, some charge round and some interpolation parameter `p ∈ [ε/2, ε]`,
`ε = n^{-ν}`, give the normalized transported vector a defect energy at most
`C n^ℓ D² W² (log n)^C (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000}`, up to any fixed `η > 0`.

The supplied state is any unit ground vector of the truncated Hamiltonian with small ground
energy; the comparator inputs (the typical mass `z ≥ 1/2`, the typical dimension
`log d ≤ C_e n^{1+e}`, and the shell bound `B_sh ≤ C_e (n L^e + n)` on every positive-depth
prefix) are hypotheses on it.  Their supply for the actual truncated ground state is
`OpenAI.Scan.exists_sourceScan_truncation` with Lemma 9.4.

The proof selects the point by averaging the charge defects
(`OpenAI.Scan.exists_sourceScan_selected_density`) and bounds the defect energy there through
the transport energy clause and the Hölder estimate (`OpenAI.Scan.exists_sourceScan_energy_le`);
the eighth root of the replica remainder of the selected density joins `η`.

## Implementation notes

The replica remainder `o_k(1)` of eq. (9.5) is the `η` of the conclusion: for every `η > 0`
the bound holds at all large `k`.  The selected round and parameter may depend on `k`, as in the
paper (line 395).
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

open Classical in
/-- **Proposition 9.2, the scanner estimate** [OAI265, §9.2, eqs. (9.5) and (9.6)], for the
collar scan at the source scales.  The constants and the threshold depend on the exponents, the
Hamiltonian parameters, `C_tr`, `C_T`, the entropy-input constant `C_e`, a lower bound `g₀` for
the truncated gap and the weight-growth exponent `ω < 1 - ℓ - μ`; they precede the domain, the
interaction, the supplied state and labels, the weight `1 ≤ W ≤ n^ω` and the replica count.
The defect energy is `(⟨v, \bar{H̃} v⟩ - Ẽ₀) / g̃` for the actual charge root at round `s` and
parameter `p`, with `a = W / K`. -/
theorem exists_sourceScan_selection (X : ScannerExponents) (q R : ℕ) [NeZero q]
    {J Δ Ctr CT Ce g₀ ω : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) (hCtr : 0 < Ctr) (hCT : 0 ≤ CT)
    (hg₀ : 0 < g₀) (hω : ω < 1 - X.ell - X.mu) :
    ∃ C Cl : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hA : A ⊆ Λ)
      (hT : T.Nonempty),
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
    ∀ (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (e gap : ℝ), ‖Ωt‖ = 1 →
      (∑ i, S.truncatedEnergyTerm Φ Ω J Δ (X.L n) i) *ᵥ Ωt.ofLp = (e : ℂ) • Ωt.ofLp →
      0 ≤ e → e ≤ (n : ℝ) ^ (-1000 : ℝ) → g₀ ≤ gap →
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let Xs := S.A.filter fun x => x.val ∈ T
    ∀ (E : Finset (FiniteProduct.Configuration β Xs)) [NeZero E.card],
      1 / 2 ≤
        (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E →
      Real.log E.card ≤ Ce * (n : ℝ) ^ (1 + X.e) →
      (∀ j : Fin (X.L n + 1),
        FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
          Ce * ((n : ℝ) * (X.L n : ℝ) ^ X.e + n)) →
    ∀ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      IsSchmidtBellLabels (∑ i, S.truncatedEnergyTerm Φ Ω J Δ (X.L n) i) Ωt e Xs E ell →
    ∀ W : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ ω →
      let d := E.card
      let a := W / (S.K : ℝ)
      let nA := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ => d)
      let pre : (k : ℕ) → Config k (fun v => Fin (nA v)) → ℂ := fun k =>
        replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
      let ε := (n : ℝ) ^ (-X.nu)
      let δ := C * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl)
      ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc (ε / 2) ε,
        ((S.actualChargeScanRound hm hM s.val nA
            (S.actualEnergyTerms Φ Ω J Δ (X.L n) (fun _ => d)) a pre).meanEnergy k p - e) /
            gap ≤
          C * (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
              (δ ^ (1 / 8 : ℝ) + ε + (n : ℝ) ^ (-100 : ℝ)) +
            C * (n : ℝ) ^ (-1000 : ℝ) + η := by
  obtain ⟨C₁, Cl₁, hC₁, hCl₁, N₁, hden⟩ :=
    exists_sourceScan_selected_density X q R (J := J) (Ce := Ce) hΔ hCtr hω
  obtain ⟨C₂, Cl₂, hC₂, hCl₂, N₂, hen⟩ :=
    exists_sourceScan_energy_le X q R (J := J) hΔ hCtr hCT hg₀ hω
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hlog
  refine ⟨max C₁ C₂, max Cl₁ Cl₂, le_max_of_le_left hC₁, max N₁ (max N₂ N₃), ?_⟩
  intro n hn Λ A T _ hA hT hTcard hrows hclear S
  have hlogn : (1 : ℝ) ≤ Real.log n := hN₃ n (le_of_max_le_right (le_of_max_le_right hn))
  obtain ⟨hm, hM, hden'⟩ := hden n (le_of_max_le_left hn) Λ A T hT hA hrows hclear
  obtain ⟨_hm', _hM', hen'⟩ :=
    hen n (le_of_max_le_left (le_of_max_le_right hn)) Λ A T hT hA hTcard hrows hclear
  refine ⟨hm, hM, ?_⟩
  intro Φ hΦ Ω hΩ Ωt e gap hΩt _ _ he hgap β Xs E _ hz hlogE hsh ell hSB W hW1 hWω
    d a nA pre ε δ η hη
  obtain ⟨ρ₁, hρ₁0, hρ₁, hsel⟩ :=
    hden' Φ hΦ Ω hΩ Ωt hΩt E hz hlogE hsh _ e ell hSB W hW1 hWω
  obtain ⟨ρ₂, hρ₂, hbound⟩ := hen' Φ hΦ Ω hΩ Ωt e gap he hgap E ell hSB W hW1 hWω
  clear hden hen hden' hen'
  set X₂ : ℝ := (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl₂ with hX₂
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) < Real.log n := by linarith
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) n.cast_nonneg
    simp_all
  have hX₂0 : 0 ≤ X₂ := by positivity
  have hρ8 : Tendsto (fun k ↦ ρ₁ k ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa [Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0)] using
      hρ₁.rpow_const (p := (1 / 8 : ℝ)) (Or.inr (by norm_num))
  have hlim : Tendsto (fun k ↦ C₂ * X₂ * ρ₁ k ^ (1 / 8 : ℝ) + ρ₂ k) atTop (𝓝 0) := by
    simpa using (hρ8.const_mul (C₂ * X₂)).add hρ₂
  filter_upwards [hsel, hlim.eventually (gt_mem_nhds hη), eventually_ge_atTop 1]
    with k hk hηk hk1
  obtain ⟨s, p, hp, hQ⟩ := hk
  refine ⟨s, p, hp, ?_⟩
  have hb := hbound k hk1 s p hp
  clear hbound hsel
  -- The density, its eighth root, and the comparison with the frozen `δ`.
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hn0 _
  have hA4 : 0 ≤ a ^ (1 / 4 : ℝ) := Real.rpow_nonneg (div_nonneg (by linarith)
    (Nat.cast_nonneg _)) _
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hδ₁0 : 0 ≤ C₁ * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl₁) := by
    have := Real.rpow_nonneg hlog0 Cl₁
    have := Real.rpow_nonneg hn0.le (X.e - X.mu)
    positivity
  have hδle : C₁ * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl₁) ≤ δ := by
    have hl : Real.log n ^ Cl₁ ≤ Real.log n ^ (max Cl₁ Cl₂) :=
      Real.rpow_le_rpow_of_exponent_le hlogn (le_max_left _ _)
    have h1 : (n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl₁ ≤
        (n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ (max Cl₁ Cl₂) := by
      gcongr
    have h2 : 0 ≤ (n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl₁ := by
      have := Real.rpow_nonneg hlog0 Cl₁
      have := Real.rpow_nonneg hn0.le (X.e - X.mu)
      positivity
    calc _ ≤ max C₁ C₂ * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl₁) := by
          gcongr; exact le_max_left _ _
      _ ≤ δ := by
          have : 0 ≤ max C₁ C₂ * ε⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left h1 this
  set Q := (S.actualChargeEntropyDefect hm hM s.val nA
    (S.actualEnergyTerms Φ Ω J Δ (X.L n) (fun _ => d)) (a / 2) k (pre k) p /
    ((S.K : ℝ) * n * S.D)) with hQdef
  have hq8 : Q ^ (1 / 8 : ℝ) ≤ δ ^ (1 / 8 : ℝ) + ρ₁ k ^ (1 / 8 : ℝ) := by
    have hQ0 : 0 ≤ Q := by
      rw [hQdef]
      exact div_nonneg (S.actualChargeEntropyDefect_nonneg hm hM s.val nA _
        (div_nonneg (by linarith) (Nat.cast_nonneg _)) k pre p) (by positivity)
    calc Q ^ (1 / 8 : ℝ)
        ≤ (C₁ * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl₁) +
            ρ₁ k) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow hQ0 hQ (by norm_num)
      _ ≤ (C₁ * ε⁻¹ * ((n : ℝ) ^ (X.e - X.mu) + a ^ (1 / 4 : ℝ) * Real.log n ^ Cl₁)) ^
            (1 / 8 : ℝ) + ρ₁ k ^ (1 / 8 : ℝ) :=
          Real.rpow_add_le_add_rpow hδ₁0 (hρ₁0 k) (by norm_num) (by norm_num)
      _ ≤ δ ^ (1 / 8 : ℝ) + ρ₁ k ^ (1 / 8 : ℝ) := by
          gcongr
  -- The energy coefficient at the common constants.
  have hX : C₂ * X₂ ≤ max C₁ C₂ * (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 *
      Real.log n ^ (max Cl₁ Cl₂) := by
    have hl : Real.log n ^ Cl₂ ≤ Real.log n ^ (max Cl₁ Cl₂) :=
      Real.rpow_le_rpow_of_exponent_le hlogn (le_max_right _ _)
    rw [hX₂]
    have h0 : 0 ≤ (n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 := by positivity
    calc C₂ * ((n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl₂)
        ≤ max C₁ C₂ * ((n : ℝ) ^ X.ell * (S.D : ℝ) ^ 2 * W ^ 2 * Real.log n ^ (max Cl₁ Cl₂)) :=
          mul_le_mul (le_max_right _ _) (mul_le_mul_of_nonneg_left hl h0) hX₂0
            (le_max_of_le_left hC₁)
      _ = _ := by ring
  have hT0 : 0 ≤ δ ^ (1 / 8 : ℝ) + ε + (n : ℝ) ^ (-100 : ℝ) := by
    have := Real.rpow_nonneg (le_trans hδ₁0 hδle) (1 / 8 : ℝ)
    have := Real.rpow_nonneg hn0.le (-100 : ℝ)
    positivity
  have hP : C₂ * (n : ℝ) ^ (-1000 : ℝ) ≤ max C₁ C₂ * (n : ℝ) ^ (-1000 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hn0.le _)
  have hmain : C₂ * X₂ * (Q ^ (1 / 8 : ℝ) + ε + (n : ℝ) ^ (-100 : ℝ)) ≤
      C₂ * X₂ * (δ ^ (1 / 8 : ℝ) + ε + (n : ℝ) ^ (-100 : ℝ)) +
        C₂ * X₂ * ρ₁ k ^ (1 / 8 : ℝ) := by
    have := mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add_right hq8 ε)
      ((n : ℝ) ^ (-100 : ℝ))) (mul_nonneg hC₂ hX₂0)
    linarith
  have hmain2 := mul_le_mul_of_nonneg_right hX hT0
  have hb' : ((S.actualChargeScanRound hm hM s.val nA
      (S.actualEnergyTerms Φ Ω J Δ (X.L n) (fun _ => d)) a pre).meanEnergy k p - e) / gap ≤
      C₂ * X₂ * (Q ^ (1 / 8 : ℝ) + ε + (n : ℝ) ^ (-100 : ℝ)) +
      C₂ * (n : ℝ) ^ (-1000 : ℝ) + ρ₂ k := by
    refine hb.trans (le_of_eq ?_)
    rw [hX₂]; ring
  linarith

end OpenAI.Scan
