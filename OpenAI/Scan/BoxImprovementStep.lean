import OpenAI.Scan.RectangleBootstrap
import OpenAI.Scan.RectangleTestGeometry
import OpenAI.Scan.RectangleShellEntropy
import OpenAI.Scan.SourceScanTruncation

/-!
# One step of the safe-box bootstrap

The one-step improvement in the proof of Proposition 9.5 [OAI265, §9.4]: a box bound with
exponent `e_* < e ≤ e₀` gives, for every large safe rectangle, the exponent `(1 - ℓ) e`.
A safe rectangle `Q` of size `s₀` is scanned at `n = 8 s₀` with the bootstrap exponents of `e₀`.
The truncated ground state of the scan supplies the scanner inputs: its target entropy is
`O(n^{1+e})` by the box bound on `Q` itself, and its positive-depth prefixes, the shells
`A ∩ (Q_j \ Q)`, have entropy `O(n L^e)` by the shell estimate.  The bootstrap comparison bounds
the truncated target entropy by `C n^{1+(1-ℓ)e}`, and the entropy transfer returns to `Ω`.

## Implementation notes

The scan needs a linear order on the admissible supports of `Λ`; any one serves, and the proof
takes the well-ordering of `WellOrderingRel`.
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- The sites of a cut `A ⊆ Λ` lying in `T`, read back in `ℤ²`, are `A ∩ T`. -/
theorem map_subtype_filter_mem_eq_inter {Λ A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ)
    (T : Finset (ℤ × ℤ)) :
    ((A.subtype (· ∈ (Λ : Set (ℤ × ℤ)))).filter fun x => x.val ∈ T).map
      (Function.Embedding.subtype _) = A ∩ T := by
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_subtype, Finset.mem_inter,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨y, ⟨hyA, hyT⟩, rfl⟩
    exact ⟨hyA, hyT⟩
  · rintro ⟨hxA, hxT⟩
    exact ⟨⟨x, hA hxA⟩, ⟨hxA, hxT⟩, rfl⟩

/-- The positive-depth prefix of depth `j` of the collar scan of a target `T`, read back in
`ℤ²`, is the shell `A ∩ (T_j \ T)`. -/
theorem map_positiveDepthPrefix_sourceScan (X : ScannerExponents) (Ctr : ℝ) (R : ℕ)
    {Λ A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (n j : ℕ) :
    (positiveDepthPrefix (sourceScan X Ctr R Λ A T hT n).A
        (sourceScan X Ctr R Λ A T hT n).depth (j : ℤ)).map (Function.Embedding.subtype _) =
      A ∩ (ambientDilation T j \ T) := by
  have hSA : (sourceScan X Ctr R Λ A T hT n).A = A.subtype (· ∈ (Λ : Set (ℤ × ℤ))) := rfl
  have hSd : (sourceScan X Ctr R Λ A T hT n).depth = fun x => ambientDepth T hT x.val := rfl
  rw [hSA, hSd]
  ext x
  have h0 := ambientDepth_le_iff_mem_dilation T hT x 0
  have hj := ambientDepth_le_iff_mem_dilation T hT x j
  rw [ambientDilation_zero] at h0
  simp only [Nat.cast_zero] at h0
  simp only [positiveDepthPrefix, Finset.mem_map, Finset.mem_filter, Finset.mem_subtype,
    Finset.mem_inter, Finset.mem_sdiff, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨y, ⟨hyA, hy0, hyj⟩, rfl⟩
    exact ⟨hyA, hj.mp hyj, fun h => absurd (h0.mpr h) (not_le.mpr hy0)⟩
  · rintro ⟨hxA, hxj, hxT⟩
    exact ⟨⟨x, hA hxA⟩, ⟨hxA, not_le.mp fun h => hxT (h0.mp h), hj.mpr hxj⟩, rfl⟩

/-- The finite-product entropy of a set of sites of `Λ` is the region entropy of its image
in `ℤ²`. -/
theorem finiteProduct_entropy_eq_regionEntropy {q : ℕ} {Λ : Finset (ℤ × ℤ)}
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩ : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1)
    {Y' : Finset ↥(Λ : Set (ℤ × ℤ))} {Y : Finset (ℤ × ℤ)}
    (hY' : Y'.map (Function.Embedding.subtype _) = Y) (hY : Y ⊆ Λ) :
    FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ω Y' =
      (pureState (WithLp.ofLp Ω) hΩ).regionEntropy hY := by
  rw [← regionalEntropy_eq_finiteProduct Λ q Ω hΩ Y']
  exact (pureState (WithLp.ofLp Ω) hΩ).toSubState.regionEntropy_congr hY' _ hY

/-- **One step of the safe-box bootstrap** [OAI265, proof of Proposition 9.5, lines 707–790].
For `e_* < e ≤ e₀ < 1`, if `F_box(r) ≤ C_e r^{1+e}` for `r ≥ 1`, there are `C` and a size
threshold, uniform over `D₀ > 2R + 10`, the domain, the Hamiltonian and the cut, such that every
safe rectangle `Q` of size `s₀` beyond the threshold has `S_Ω(A ∩ Q) ≤ C s₀^{1+(1-ℓ)e}`, with
`ℓ = ν/100` the improvement fraction of eq. (9.13). -/
theorem isSafe_regionEntropy_le_of_boxEntropy_le (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q)
    (hJ : 0 < J) (hΔ : 0 < Δ) {e₀ : ℝ} (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1)
    {e : ℝ} (he : (Exponents.boxError : ℝ) < e) (hee₀ : e ≤ e₀) {Ce : ℝ}
    (hF : ∀ r : ℕ, 1 ≤ r → boxEntropy ℂ q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e)) :
    ∃ (C : ℝ) (N : ℕ), ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ)), IsIntRect Q → IsSafe D₀ Λ A Q →
      N ≤ boxSize Q →
      (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ≤
        C * (boxSize Q : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
  classical
  have : NeZero q := ⟨by omega⟩
  set X := bootstrapExponents e₀ he₀ he₀₁ with hXdef
  have hepos : 0 < e := lt_trans (by norm_num [Exponents.boxError]) he
  have he1 : e < 1 := hee₀.trans_lt he₀₁
  have hℓ0 : 0 < X.ell := X.ell_pos
  have hℓ1 : X.ell < 1 := X.ell_lt_one
  have hXell : X.ell = BootstrapParameters.ell e₀ := rfl
  obtain ⟨Ctr, hCtr, Ct, -, htrunc⟩ :=
    exists_sourceScan_truncation X q R hJ hΔ (CT := 1) zero_le_one
  obtain ⟨Csh, hsh⟩ := isSafe_shell_regionEntropy_le (𝕜 := ℂ) q R J Δ hepos he1 hF
  set g := Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J with hgdef
  have hg : 0 < g := div_pos hΔ (SpectralFilter.positiveNormalization_pos 1 (Δ / 2) J)
  set Ce' := max Ce 0 + max Csh 0 + 1 with hCe'def
  obtain ⟨Cb, Nb, hb⟩ := sourceScan_bootstrap_entropy_le q R hJ hΔ hCtr (CT := 1) zero_le_one
    (g₀ := g / 2) (Ce := Ce') (half_pos hg) he₀ he₀₁ he hee₀
  obtain ⟨Ng, hgeo⟩ := isSafe_test_geometry (C₂ := 8) (ℓ := X.ell) (Ctr := Ctr) (by norm_num)
    hℓ0 hℓ1 hCtr.le
  obtain ⟨Nt, hNt⟩ := eventually_atTop.mp htrunc
  refine ⟨64 * max Cb 0 + 1, max (max Ng Nb) (max Nt 1), ?_⟩
  intro D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q hQ hsafe hN
  set s₀ := boxSize Q with hs₀
  have hs₁ : 1 ≤ s₀ := le_of_max_le_right (le_of_max_le_right hN)
  set n := ⌈(8 : ℝ) * (s₀ : ℝ)⌉₊ with hndef
  have hn : n = 8 * s₀ := by
    rw [hndef, show (8 : ℝ) * (s₀ : ℝ) = ((8 * s₀ : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
  have hns : s₀ ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := one_pos.trans_le hn1
  have hD₀' : (10 : ℝ) ≤ D₀ := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  -- The test geometry of eq. (9.2).
  obtain ⟨hQcard, hrows, h2L, hclear⟩ := hgeo s₀
    ((le_max_left _ _).trans (le_of_max_le_left hN)) D₀ hD₀' Λ A Q hQ hsafe rfl
  set L := X.L n with hLdef
  have hL1 : 1 ≤ L := by
    refine Nat.le_floor ?_
    rw [Nat.cast_one]
    exact Real.one_le_rpow hn1 (by linarith)
  have hT : Q.Nonempty := by
    obtain ⟨a, b, hab, rfl⟩ := hQ
    exact ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  let _ : LinearOrder (supports Λ R) := IsWellOrder.linearOrder WellOrderingRel
  -- The truncated ground state and its inputs.
  set Ωe : EuclideanSpace ℂ (Reg (Qudits q) Λ) := WithLp.toLp 2 Ω with hΩedef
  have hΩe : ‖Ωe‖ = 1 := (norm_toLp_eq_one_iff Ω).2 hΩ
  have hnt : Nt ≤ n := (le_of_max_le_left (le_of_max_le_right hN)).trans hns
  have hQcard' : (Q.card : ℝ) ≤ 1 * (n : ℝ) ^ 2 := by rw [_root_.one_mul]; exact hQcard
  obtain ⟨et, Ωt, hΩt, heigt, het0, het, hgapt, -, hent, -, E, hmass, hwin⟩ :=
    hNt n hnt Λ A Q hA hT Φ hΦ Ωe hΩe E₀ hE hgap hQcard' hrows hclear
  have hpow200 : (n : ℝ) ^ (-200 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hpow100 : (n : ℝ) ^ (-100 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn2) (by norm_num)
  have hz := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1 - (n : ℝ) ^ (-100 : ℝ)) hmass
  have : NeZero E.card := ⟨by
    intro h0
    rw [Finset.card_eq_zero] at h0
    subst h0
    simp only [Matrix.IsHermitian.spectralRestrictionMass, Finset.sum_empty,
      lt_self_iff_false] at hz⟩
  obtain ⟨ell, hell⟩ := exists_isSchmidtBellLabels _ Ωt et hΩt heigt _ E hz
  have hΩt1 := star_dotProduct_self_eq_one_of_norm_eq_one hΩt
  -- Entropy of a region of `S₀` for `Ωt` within `1` of that for `Ω`.
  have htransfer : ∀ (Y : Finset (ℤ × ℤ)) (hY : Y ⊆ A ∩ ambientDilation Q L),
      (pureState Ωt.ofLp hΩt1).regionEntropy (hY.trans (Finset.inter_subset_left.trans hA)) ≤
        (pureState Ω hΩ).regionEntropy (hY.trans (Finset.inter_subset_left.trans hA)) + 1 ∧
      (pureState Ω hΩ).regionEntropy (hY.trans (Finset.inter_subset_left.trans hA)) ≤
        (pureState Ωt.ofLp hΩt1).regionEntropy (hY.trans (Finset.inter_subset_left.trans hA)) +
          1 := by
    intro Y hY
    have h := abs_le.mp ((hent Y hY).trans hpow200)
    constructor <;> linarith [h.1, h.2]
  have hfp : ∀ (Y' : Finset ↥(Λ : Set (ℤ × ℤ))) (Y : Finset (ℤ × ℤ))
      (hY' : Y'.map (Function.Embedding.subtype _) = Y) (hYΛ : Y ⊆ Λ),
      FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt Y' =
        (pureState Ωt.ofLp hΩt1).regionEntropy hYΛ := fun Y' Y hY' hYΛ =>
    finiteProduct_entropy_eq_regionEntropy Ωt hΩt1 hY' hYΛ
  have hXs : ((sourceScan X Ctr R Λ A Q hT n).A.filter fun x => x.val ∈ Q).map
      (Function.Embedding.subtype _) = A ∩ Q := map_subtype_filter_mem_eq_inter hA Q
  have hQL : A ∩ Q ⊆ A ∩ ambientDilation Q L :=
    Finset.inter_subset_inter_left (subset_ambientDilation Q L)
  -- The target entropy input.
  have hpow1e : (1 : ℝ) ≤ (n : ℝ) ^ (1 + e) := Real.one_le_rpow hn1 (by linarith)
  have hsn : (s₀ : ℝ) ^ (1 + e) ≤ (n : ℝ) ^ (1 + e) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hns) (by linarith)
  have htarget : FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt
      ((sourceScan X Ctr R Λ A Q hT n).A.filter fun x => x.val ∈ Q) ≤ Ce' * (n : ℝ) ^ (1 + e) := by
    rw [hfp _ (A ∩ Q) hXs (hQL.trans (Finset.inter_subset_left.trans hA))]
    have h1 := (htransfer (A ∩ Q) hQL).1
    have h2 := (regionEntropy_le_boxEntropy hD₀ hΦ hΩ hE hgap hA hQ hsafe le_rfl).trans
      (hF s₀ hs₁)
    have h3 : Ce * (s₀ : ℝ) ^ (1 + e) ≤ max Ce 0 * (n : ℝ) ^ (1 + e) :=
      mul_le_mul (le_max_left _ _) hsn (by positivity) (le_max_right _ _)
    have h4 : (max Ce 0 + 1) * (n : ℝ) ^ (1 + e) ≤ Ce' * (n : ℝ) ^ (1 + e) :=
      mul_le_mul_of_nonneg_right (by rw [hCe'def]; linarith [le_max_right Csh 0])
        (by positivity)
    nlinarith
  -- The shell entropy input.
  have hprefix : ∀ j : Fin (L + 1),
      FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt
        (positiveDepthPrefix (sourceScan X Ctr R Λ A Q hT n).A
          (sourceScan X Ctr R Λ A Q hT n).depth (j.val : ℤ)) ≤
        Ce' * ((n : ℝ) * (L : ℝ) ^ e + n) := by
    intro j
    have hjL : j.val ≤ L := Nat.lt_succ_iff.mp j.isLt
    have hYsub : A ∩ (ambientDilation Q j.val \ Q) ⊆ A ∩ ambientDilation Q L :=
      Finset.inter_subset_inter_left (Finset.sdiff_subset.trans
        (ambientDilation_mono Q hjL))
    rw [hfp _ (A ∩ (ambientDilation Q j.val \ Q))
      (map_positiveDepthPrefix_sourceScan X Ctr R hA Q hT n j.val)
      (hYsub.trans (Finset.inter_subset_left.trans hA))]
    have h1 := (htransfer _ hYsub).1
    have h2 := hsh D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA Q hQ hsafe L j.val hL1 h2L hjL
    have hLe : 0 ≤ (L : ℝ) ^ e := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h3 : Csh * s₀ * (L : ℝ) ^ e ≤ max Csh 0 * ((n : ℝ) * (L : ℝ) ^ e) := by
      rw [_root_.mul_assoc]
      exact mul_le_mul (le_max_left _ _)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hns) hLe) (by positivity)
        (le_max_right _ _)
    have hnL : 0 ≤ (n : ℝ) * (L : ℝ) ^ e := by positivity
    have h4 : max Csh 0 * ((n : ℝ) * (L : ℝ) ^ e) + 1 ≤ Ce' * ((n : ℝ) * (L : ℝ) ^ e + n) := by
      have hc : max Csh 0 ≤ Ce' := by rw [hCe'def]; linarith [le_max_right Ce 0]
      have hc1 : 1 ≤ Ce' := by rw [hCe'def]; linarith [le_max_right Ce 0, le_max_right Csh 0]
      nlinarith
    linarith
  -- The bootstrap comparison.
  have hbn : Nb ≤ n :=
    ((le_max_right _ _).trans (le_of_max_le_left hN)).trans hns
  have hmain := hb n hbn Λ A Q hA hT hQcard' hrows hclear Φ hΦ Ωe hΩe Ωt et (g / 2) hΩt
    heigt hgapt het0 het le_rfl E hmass hwin htarget hprefix ell hell
  replace hmain :=
    (hfp _ (A ∩ Q) hXs (hQL.trans (Finset.inter_subset_left.trans hA))).symm.trans_le hmain
  -- Transfer back to `Ω` and `n = 8 s₀`.
  have hback := (htransfer (A ∩ Q) hQL).2
  clear hb hNt htrunc hgeo hsh hprefix htarget hent hwin hell
  obtain ⟨p, hpdef⟩ : ∃ p, p = 1 + (1 - BootstrapParameters.ell e₀) * e := ⟨_, rfl⟩
  rw [← hpdef] at hmain ⊢
  have hℓe : 0 ≤ (1 - BootstrapParameters.ell e₀) * e :=
    mul_nonneg (by rw [← hXell]; linarith) hepos.le
  have hℓe' : (1 - BootstrapParameters.ell e₀) * e ≤ 1 :=
    (mul_le_mul (by rw [← hXell]; linarith) he1.le hepos.le zero_le_one).trans_eq (_root_.one_mul 1)
  have hp1 : 1 ≤ p := by rw [hpdef]; linarith
  have hp2 : p ≤ 2 := by rw [hpdef]; linarith
  have hsp : (1 : ℝ) ≤ (s₀ : ℝ) ^ p := Real.one_le_rpow (by exact_mod_cast hs₁) (by linarith)
  have hnp : (n : ℝ) ^ p ≤ 64 * (s₀ : ℝ) ^ p := by
    rw [hn, Nat.cast_mul, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
    have h8 : ((8 : ℕ) : ℝ) ^ p ≤ 64 := by
      calc ((8 : ℕ) : ℝ) ^ p ≤ ((8 : ℕ) : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
        _ = 64 := by rw [Real.rpow_two]; norm_num
    exact mul_le_mul_of_nonneg_right h8 (by positivity)
  have hCb : Cb * (n : ℝ) ^ p ≤ 64 * max Cb 0 * (s₀ : ℝ) ^ p := by
    calc Cb * (n : ℝ) ^ p ≤ max Cb 0 * (n : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Cb 0 * (64 * (s₀ : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hnp (le_max_right _ _)
      _ = 64 * max Cb 0 * (s₀ : ℝ) ^ p := by ring
  calc (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ)
      ≤ Cb * (n : ℝ) ^ p + 1 := hback.trans (add_le_add_left hmain 1)
    _ ≤ 64 * max Cb 0 * (s₀ : ℝ) ^ p + (s₀ : ℝ) ^ p := add_le_add hCb hsp
    _ = (64 * max Cb 0 + 1) * (s₀ : ℝ) ^ p := by ring

end OpenAI.Scan
