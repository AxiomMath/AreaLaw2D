import OpenAI.Scan.SourceScan
import OpenAI.Scan.ScanTruncationInputs
import OpenAI.Scan.StatusMarginalMoments

/-!
# The truncated ground state of the collar scan

Proposition 4.5 with Lemmas 2.1 and 3.1 at the source scales [OAI265, §9.1, lines 49–59, and the
proof of Proposition 9.2, lines 400–414]: the truncated Hamiltonian of the collar scan has a unit
ground vector close to the original one, whose entropies, status marginal moments and target
typical window are those Proposition 9.2 uses.
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- The entropy transfer error of Lemma 2.1 at trace distance `a n^{-500}`, on a region of
`b n²` sites (with `b` absorbing `log q`), is eventually at most `n^{-200}`. -/
theorem eventually_four_mul_sqrt_mul_le_rpow {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      4 * Real.sqrt (a * (n : ℝ) ^ (-500 : ℝ)) * (1 + b * (n : ℝ) ^ 2) ≤
        (n : ℝ) ^ (-200 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 48)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * Real.sqrt a * (1 + b))]
    with n hn hc
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsq : Real.sqrt (a * (n : ℝ) ^ (-500 : ℝ)) = Real.sqrt a * (n : ℝ) ^ (-250 : ℝ) := by
    rw [Real.sqrt_mul ha, show (-500 : ℝ) = -250 * 2 by norm_num, Real.rpow_mul hn0.le,
      Real.rpow_two, Real.sqrt_sq (by positivity)]
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have h2 : 1 + b * (n : ℝ) ^ 2 ≤ (1 + b) * (n : ℝ) ^ 2 := by nlinarith
  have hsplit : (n : ℝ) ^ (48 : ℝ) * ((n : ℝ) ^ (-250 : ℝ) * (n : ℝ) ^ 2) =
      (n : ℝ) ^ (-200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    norm_num
  calc 4 * Real.sqrt (a * (n : ℝ) ^ (-500 : ℝ)) * (1 + b * (n : ℝ) ^ 2)
      ≤ 4 * (Real.sqrt a * (n : ℝ) ^ (-250 : ℝ)) * ((1 + b) * (n : ℝ) ^ 2) := by
        rw [hsq]; gcongr
    _ = (4 * Real.sqrt a * (1 + b)) * ((n : ℝ) ^ (-250 : ℝ) * (n : ℝ) ^ 2) := by ring
    _ ≤ (n : ℝ) ^ (48 : ℝ) * ((n : ℝ) ^ (-250 : ℝ) * (n : ℝ) ^ 2) := by
        gcongr; exact hc
    _ = (n : ℝ) ^ (-200 : ℝ) := hsplit

open Classical in
/-- **The truncated ground state and its scanner inputs** [OAI265, §9.1, lines 49–59, and the
proof of Proposition 9.2, lines 400–414; Proposition 4.5; Lemmas 2.1 and 3.1].  For fixed
exponents and target-size coefficient `C_T` there are a truncation-radius coefficient `C_tr`
and a constant `C` such that at every large scale `n`, under the test geometry of eq. (9.2)
(`|T| ≤ C_T n²`, at most `n` sites in each of the first `L` depth layers, and clearance
`dist_∞(T, Z_A) > 2L + 10 r₀`), the Hamiltonian truncated near `S₀ = A ∩ T_L` at radius `r₀`
has a unit ground vector `Ωt` with energy `0 ≤ Ẽ₀ ≤ n^{-1000}` and gap `g/2`
(`g = Δ / c_*` the positive-replacement gap), at trace distance at most `C n^{-500}` from `Ω`;
every entropy of a subset of `S₀` moves by at most `n^{-200}`; every completed or pre-charge
status region of the scan obeys the marginal moment bound of Lemma 3.1 with parameter
`𝓑 = C n D log¹² n`; and the target marginal has a spectral set of mass at least
`1 - n^{-100}` in the window of width `n^{3/5}` about its entropy. -/
theorem exists_sourceScan_truncation (X : ScannerExponents) (q R : ℕ) [NeZero q]
    {J Δ CT : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) (hCT : 0 ≤ CT) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hA : A ⊆ Λ)
      (hT : T.Nonempty)
      (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ),
      IsAdmissible Λ R J Φ →
    ∀ (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩ : ‖Ω‖ = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω.ofLp = (E₀ : ℂ) • Ω.ofLp →
      HasGlobalGap (hamiltonian Λ Φ) Ω.ofLp E₀ Δ →
      (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2 →
      (∀ d : ℕ, 1 ≤ d → d ≤ X.L n →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) →
      (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ A,
        ((2 * X.L n + 10 * roundedLogRadius Ctr n : ℕ) : ℤ) < ambientSupDistance t z) →
      let S := sourceScan X Ctr R Λ A T hT n
      let Ht := ∑ i, S.truncatedEnergyTerm Φ Ω J Δ (X.L n) i
      let g := Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J
      let B := C * (n : ℝ) * (X.D n : ℝ) * Real.log n ^ 12
      let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
      let Xs := S.A.filter fun x => x.val ∈ T
      ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩt : ‖Ωt‖ = 1),
        Ht *ᵥ Ωt.ofLp = (e : ℂ) • Ωt.ofLp ∧ 0 ≤ e ∧ e ≤ (n : ℝ) ^ (-1000 : ℝ) ∧
        (Ht - (e : ℂ) • 1 -
          ((g / 2 : ℝ) : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef ∧
        (pureState Ωt.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).toSubState.D₁
            (pureState Ω.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).toSubState ≤
          C * (n : ℝ) ^ (-500 : ℝ) ∧
        (∀ (Y : Finset (ℤ × ℤ)) (hY : Y ⊆ A ∩ ambientDilation T (X.L n)),
          |(pureState Ωt.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
              (hY.trans (Finset.inter_subset_left.trans hA)) -
            (pureState Ω.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
              (hY.trans (Finset.inter_subset_left.trans hA))| ≤ (n : ℝ) ^ (-200 : ℝ)) ∧
        (∀ (s : ℕ) (hist : History S.K S.m S.M s) (g' : Fin S.K),
          (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g'),
            ∀ u : ℝ, |u| ≤ tailRadius (2 / g) B →
              Real.log (surprisalMoment
                ((pureState Ωt.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                  (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
                u * (pureState Ωt.ofLp
                    (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                    (map_embeddingSubtype_subset (T := Λ) Q) +
                  512 * Real.exp 1 * (2 / g) * B * u ^ 2) ∧
          (s + 1 ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g'),
            ∀ u : ℝ, |u| ≤ tailRadius (2 / g) B →
              Real.log (surprisalMoment
                ((pureState Ωt.ofLp (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                  (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
                u * (pureState Ωt.ofLp
                    (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                    (map_embeddingSubtype_subset (T := Λ) Q) +
                  512 * Real.exp 1 * (2 / g) * B * u ^ 2)) ∧
        ∃ E : Finset (FiniteProduct.Configuration β Xs),
          1 - (n : ℝ) ^ (-100 : ℝ) ≤
            (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass E ∧
          ∀ i ∈ E,
            Real.exp (-FiniteProduct.entropy β Ωt Xs - (n : ℝ) ^ (3 / 5 : ℝ)) ≤
                (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues i ∧
              (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues i ≤
                Real.exp (-FiniteProduct.entropy β Ωt Xs + (n : ℝ) ^ (3 / 5 : ℝ)) := by
  classical
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨Ctr, _, hCtr, _, Nt, _, htarget⟩ :=
    CollarScan.exists_truncated_target_typical_window hq R hJ.le hΔ hCT
  obtain ⟨CB, -, hbudget⟩ := CollarScan.exists_statusMarginal_cutBudget_le_log hq R hCtr.le
  have hg : 0 < Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (SpectralFilter.positiveNormalization_pos 1 (Δ / 2) J)
  set C := max (max 1 (Real.sqrt (2 / (Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J))))
    CB with hC
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCg : Real.sqrt (2 / (Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J)) ≤ C :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hCB : CB ≤ C := le_max_right _ _
  refine ⟨Ctr, hCtr, C, hC1, ?_⟩
  filter_upwards [eventually_status_scale_separation (ell := X.ell) hCtr.le X.kappa_pos
      X.kappa_lt_mu, eventually_ge_atTop Nt,
    eventually_four_mul_sqrt_mul_le_rpow (a := C) (by linarith) ((CT + 1) * Real.log q)]
    with n hscales hnN hent
  intro Λ A T _ hA hT Φ hΦ Ω hΩ E₀ heig hgap hsize hrows hclear S Ht g B β Xs
  obtain ⟨hn2, hr, hDpos, hDm, hKL⟩ := hscales
  have hSA : S.A.map (Function.Embedding.subtype _) = A := by
    change (A.subtype (· ∈ (Λ : Set (ℤ × ℤ)))).map (Function.Embedding.subtype _) = A
    rw [Finset.subtype_map]
    exact Finset.filter_true_of_mem fun x hx => hA hx
  have hclear' : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * X.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
    rw [hSA]; exact hclear
  obtain ⟨hcard, -, -, e, Ωt, hΩt, heigt, hgapt, he0, he, -, htrace, -, -, -, -, hwin⟩ :=
    htarget Λ Φ hΦ S E₀ Ω X T hT hΩ heig hgap rfl (fun i => supportAnchor_mem i) hnN rfl hsize
      rfl hrows hclear'
  obtain ⟨-, hstatus⟩ := hbudget Λ T hT S rfl rfl (fun i => supportAnchor_mem i) (X.L n) hn2
    rfl hr hDpos hDm hKL hrows hclear'
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have htr : (vecMulVec Ωt.ofLp (star Ωt.ofLp) - vecMulVec Ω.ofLp (star Ω.ofLp)).traceNorm / 2 ≤
      C * (n : ℝ) ^ (-500 : ℝ) :=
    htrace.trans ((sqrt_truncationError_le hg n).trans
      (mul_le_mul_of_nonneg_right hCg (by positivity)))
  have hBle : CB * ((n : ℝ) * (X.D n : ℝ) * Real.log n ^ 12) ≤ B := by
    have h0 : 0 ≤ (n : ℝ) * (X.D n : ℝ) * Real.log n ^ 12 := by positivity
    calc _ ≤ C * ((n : ℝ) * (X.D n : ℝ) * Real.log n ^ 12) := mul_le_mul_of_nonneg_right hCB h0
      _ = B := by change _ = C * (n : ℝ) * (X.D n : ℝ) * Real.log n ^ 12; ring
  refine ⟨e, Ωt, hΩt, heigt, he0, he.trans (min_le_left _ _), ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hgapt)
  · rw [MState.D₁_eq_traceNorm_div_two, pureState_M, pureState_M]
    exact htr
  · intro Y hY
    have hYΛ : Y ⊆ Λ := hY.trans (Finset.inter_subset_left.trans hA)
    set Y' : Finset ↥(Λ : Set (ℤ × ℤ)) := Y.subtype (· ∈ (Λ : Set (ℤ × ℤ))) with hY'def
    have hY' : Y'.map (Function.Embedding.subtype _) = Y := by
      rw [hY'def, Finset.subtype_map]
      exact Finset.filter_true_of_mem fun x hx => hYΛ hx
    have hY'sub : Y' ⊆ S.truncationSet (X.L n) := by
      intro x hx
      have hx' := Finset.mem_inter.mp (hY (Finset.mem_subtype.mp hx))
      change x ∈ S.A.filter fun x ↦ S.depth x ≤ X.L n
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_subtype.mpr hx'.1,
        (ambientDepth_le_iff_mem_dilation T hT x.val (X.L n)).mpr hx'.2⟩
    have hY'card : (Y'.card : ℝ) ≤ (CT + 1) * (n : ℝ) ^ 2 :=
      (by exact_mod_cast Finset.card_le_card hY'sub : (Y'.card : ℝ) ≤ _).trans hcard
    have key := abs_regionalEntropy_sub_le_sqrt_traceDistance Λ q Ωt Ω hΩt hΩ Y'
    rw [(pureState Ωt.ofLp
        (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).toSubState.regionEntropy_congr
        hY' (map_embeddingSubtype_subset (T := Λ) Y') hYΛ,
      (pureState Ω.ofLp
        (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).toSubState.regionEntropy_congr
        hY' (map_embeddingSubtype_subset (T := Λ) Y') hYΛ] at key
    refine key.trans (le_trans ?_ hent)
    calc 4 * Real.sqrt ((vecMulVec Ωt.ofLp (star Ωt.ofLp) -
            vecMulVec Ω.ofLp (star Ω.ofLp)).traceNorm / 2) * (1 + (Y'.card : ℝ) * Real.log q)
        ≤ 4 * Real.sqrt (C * (n : ℝ) ^ (-500 : ℝ)) * (1 + (CT + 1) * (n : ℝ) ^ 2 * Real.log q) := by
          gcongr
      _ = 4 * Real.sqrt (C * (n : ℝ) ^ (-500 : ℝ)) *
          (1 + (CT + 1) * Real.log q * (n : ℝ) ^ 2) := by ring
  · intro s hist g'
    constructor
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common Φ Ω hΦ
        (fun i => supportAnchor_mem i) hΔ hΩ (X.L n) hΩt heigt hgapt Q
        (((hstatus s hist g').1 hs Q hQ).trans hBle)
        (by rw [← tailRadius_eq_div_sqrt (by positivity)]; exact hu)
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common Φ Ω hΦ
        (fun i => supportAnchor_mem i) hΔ hΩ (X.L n) hΩt heigt hgapt Q
        (((hstatus s hist g').2 hs Q hQ).trans hBle)
        (by rw [← tailRadius_eq_div_sqrt (by positivity)]; exact hu)
  · exact ⟨_, hwin.2.1, fun i hi => (hwin.2.2.2.2.2 i hi).2⟩

end OpenAI.Scan
