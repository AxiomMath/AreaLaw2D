/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 576d1624411e36a16cfc84aba9883f91416bcd32,
`TNLean/PEPS/AreaLaw/Scan/SourceTargetSharpUpper.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to the encodings of
`OpenAI.Scan.TargetTypicalWindow` and `OpenAI.Scan.ActualSharpUpper`: `Site Λ` is
`↥(Λ : Set (ℤ × ℤ))`, `AdmissibleSupport Λ R` is `↥(supports Λ R)`, the bundled
`LocalHamiltonian` is an interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ`,
`IsGappedGroundState` is the norm, eigenvector and `OpenAI.HasGlobalGap` conditions (the norm
of the truncated vector a named witness), TNLean's graph `cutBudget` is the square-lattice
`OpenAI.cutBudget` of the images in `ℤ²`, `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, the unordered
`edgeBoundary Λ X` is the ordered `OpenAI.edgeBoundary Λ (X.map (Function.Embedding.subtype _))`,
and `Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`. The cutwise moments and
tails and the post-split entropies are those of the regional states of `OpenAI.pureState`; the
target tail, typical set and mass are those of the finite-product reduction
`FiniteProduct.reducedPure β Ωt X` about `FiniteProduct.entropy β Ωt X`, the encoding in which
`OpenAI.Scan.CollarScan.eventually_actualScan_suppliedPrevector_sharp_upper` reads them. TNLean's
identification `reducedState_eq_finiteProduct` of the two target matrices is definitional here.
-/
import OpenAI.Scan.ActualSharpUpper
import OpenAI.Scan.TargetTypicalWindow
import OpenAI.Scan.StatusMarginalMoments
import OpenAI.Scan.StatusScaleSeparation
import OpenAI.Scan.SharpMomentScale

/-!
# The actual sharp upper estimate at the source target scales

One target-window construction supplies the truncated physical ground vector,
its target spectral restriction, and the quantitative energy, phase and trace
estimates. Geometric status budgets supply the common marginal moments of that
same vector. The literal rounded scales and an explicit positive exponent
margin place six times the per-band weight in the common moment interval.

The truncation, target-budget and status-budget constants precede the scanner
exponents and every physical instance. The integer threshold may depend on the
fixed exponent margin. The supplied label sequence uses the same physical
spectral restriction throughout the actual fill and charge estimates.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, `comparator:sharp-upper`, lines 383–418;
`08-scanner.tex`, lines 32–58, 400–474 and 859–865, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace OpenAI.Scan.CollarScan

open Arealaw SpectralFilter SimpleGraph ActualTerminals

attribute [local instance] sharpTreeRegionDecidableEq sharpTreeSiteDecidableEq
  sharpTreeConfigDecidableEq

open Classical in
/-- The source target window and common physical status moments give the actual
sharp upper estimate for every supplied label sequence with the physical mass
bound. There is one truncated vector and one target set. The same fixed
physical instance has a remainder tending to zero, uniformly over scan times
and interpolation parameters.

The strict margin is explicit: ordinary scanner exponents alone do not imply
it. The number of bands retains its natural-number division, the collar and
history lengths retain their floors, and the separation retains its ceiling.
Source: `07-comparators.tex`, `comparator:sharp-upper`, lines 383–418;
`08-scanner.tex`, lines 32–58, 400–474 and 859–865. -/
theorem exists_truncated_target_actualSharpUpper {q : ℕ} [NeZero q]
    (hq : 1 ≤ q) (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) :
    ∃ Ctr Ctarget CB : ℝ, 0 < Ctr ∧ 0 < Ctarget ∧ 0 < CB ∧
      ∀ (F : ScannerExponents) (ω : ℝ),
        ω + (1 + F.kappa) / 2 < 1 - F.ell - F.mu →
        ∃ N : ℕ, 2 ≤ N ∧
          ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)]
            (hT : T.Nonempty)
            (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ),
            IsAdmissible Λ R J Φ →
            ∀ (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
            (hM : 0 < S.M) (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)),
            ‖Ω‖ = 1 → hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
            HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
            S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
            (∀ i, (S.anchor i).1 ∈ i.val) → N ≤ S.n →
            S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
            S.m = ⌊(S.n : ℝ) ^ F.mu⌋₊ →
            S.D = ⌈(S.n : ℝ) ^ F.kappa⌉₊ →
            S.K = F.L S.n / (8 * S.m) →
            (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
            S.depth = (fun x ↦ ambientDepth T hT x.val) →
            (∀ d : ℕ, 1 ≤ d → d ≤ F.L S.n →
              (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
            (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
              ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
            let L := F.L S.n
            let X := S.A.filter fun x ↦ x.val ∈ T
            let g := Δ / positiveNormalization 1 (Δ / 2) J
            let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
            let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
            let δ := (S.n : ℝ) ^ (-100 : ℝ)
            let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
            let C₀ := 512 * Real.exp 1 * (2 / g)
            let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
            let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q
            let BY : Finset (↥(Λ : Set (ℤ × ℤ))) → ℝ := fun Y =>
              cutBudget q Λ ((S.truncationSet L).map (Function.Embedding.subtype _)) S.r₀
                (fun i => (S.anchor i).1) (Y.map (Function.Embedding.subtype _))
            1 ≤ S.K ∧ 1 ≤ B ∧ 0 < C₀ ∧ 0 < c₀ ∧
            ((S.truncationSet L).card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 ∧
            X ⊆ S.truncationSet L ∧
            (edgeBoundary Λ (X.map (Function.Embedding.subtype _))).card ≤ 4 * S.n ∧
            ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩt : ‖Ωt‖ = 1),
              (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ WithLp.ofLp Ωt =
                (e : ℂ) • WithLp.ofLp Ωt ∧
              HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) (WithLp.ofLp Ωt) e
                (g / 2) ∧
              0 ≤ e ∧ e ≤ ε ∧
              (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤
                2 * Real.sqrt (ε / g)) ∧
              (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
                  vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ≤
                Real.sqrt (2 * ε / g) ∧
              (∀ (Y : Finset (↥(Λ : Set (ℤ × ℤ)))) (u : ℝ),
                |u| ≤ tailRadius (2 / g) (BY Y) →
                Real.log (surprisalMoment
                    ((pureState (WithLp.ofLp Ωt)
                      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                        (map_embeddingSubtype_subset (T := Λ) Y)).psd.isHermitian.eigenvalues
                    u) ≤
                  u * (pureState (WithLp.ofLp Ωt)
                      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                      (map_embeddingSubtype_subset (T := Λ) Y) +
                    C₀ * BY Y * u ^ 2) ∧
              (∀ (Y : Finset (↥(Λ : Set (ℤ × ℤ)))) (v : ℝ),
                surprisalTail
                    ((pureState (WithLp.ofLp Ωt)
                      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                        (map_embeddingSubtype_subset (T := Λ) Y)).psd.isHermitian.eigenvalues
                    ((pureState (WithLp.ofLp Ωt)
                      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                      (map_embeddingSubtype_subset (T := Λ) Y)) v ≤
                  min 1 (2 * Real.exp (Real.exp 1 / 2) *
                    Real.exp (-(v / (32 * Real.sqrt ((1 + 2 / g) * BY Y)))))) ∧
              BY X ≤ Ctarget * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
              surprisalTail (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.eigenvalues
                (FiniteProduct.entropy β Ωt X) w ≤ δ ∧
              let p := (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.eigenvalues
              let E := Entropy.typicalSet p (FiniteProduct.entropy β Ωt X) w
              let z :=
                (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E
              (0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
                ∀ i ∈ E, 0 < p i ∧
                  Real.exp (-FiniteProduct.entropy β Ωt X - w) ≤ p i ∧
                  p i ≤ Real.exp (-FiniteProduct.entropy β Ωt X + w)) ∧
              ∃ hmpos : 0 < S.m, ∀ W : ℝ, 0 < W → W ≤ (S.n : ℝ) ^ ω →
                let a := W / (S.K : ℝ)
                let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
                  (FiniteProduct.splitEquiv β X) Ωt
                let d := E.card
                let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ ↦ d)
                ∀ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
                  let pre : (k : ℕ) → Config k (fun v ↦ Fin (n v)) → ℂ := fun k ↦
                    replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
                  let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
                    compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
                  (∀ᶠ k : ℕ in atTop,
                    (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
                      ‖WithLp.toLp 2
                        (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
                          (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
                          labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
                          (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                            (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
                  ∃ c : ℝ, 0 ≤ c ∧
                    Tendsto (Real.bellOverlapRemainder d c S.K) atTop (𝓝 0) ∧
                    ∀ᶠ k : ℕ in atTop, ∀ (s : ℕ) (hs : s + 1 ≤ S.n * S.m) (p : ℝ),
                      let σ := terminalPartition S (S.n * S.m)
                      let gpost := fun j g ↦
                        (pureState (WithLp.ofLp Ωt)
                            (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                          (map_embeddingSubtype_subset (T := Λ) (positiveNear S.depth (σ j g))) +
                          (pureState (WithLp.ofLp Ωt)
                              (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                            (map_embeddingSubtype_subset (T := Λ)
                              (positiveNearMiddle S.depth (σ j g))) -
                          (pureState (WithLp.ofLp Ωt)
                              (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                            (map_embeddingSubtype_subset (T := Λ) (middle (σ j g)))
                      let p₀ := Set.projIcc (0 : ℝ) 1 zero_le_one p
                      let bound :=
                        fun (tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) ↦
                          2 * Real.log (d : ℝ) - Real.log z +
                            (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
                              6 * (S.K : ℝ) * (C₀ * B) * a ^ 2 - (S.K : ℝ) / 2 * Real.log z +
                                Real.bellOverlapRemainder d c S.K k
                      let step : Fin (S.n * S.m) := ⟨s, Nat.lt_of_succ_le hs⟩
                      let Nfill := Matrix.Transport.filteredNormSq
                        ((S.actualFillData hmpos hM s).rootPath n (a / 2) k p) (pre k)
                      let Ncharge := Matrix.Transport.filteredNormSq
                        ((S.actualChargeData hmpos hM s).rootPath n (a / 2) k p) (pre k)
                      (0 < Nfill ∧ -Real.log Nfill / (k : ℝ) ≤
                        bound (((S.actualFillData hmpos hM s).tree p₀).map
                          (fillTerminalIndex S.K S.m S.M (S.n * S.m) step))) ∧
                      (0 < Ncharge ∧ -Real.log Ncharge / (k : ℝ) ≤
                        bound (((S.actualChargeData hmpos hM s).tree p₀).map
                          (chargeTerminalIndex S.K S.m S.M (S.n * S.m) step))) := by
  classical
  obtain ⟨Ctr, Ctarget, hCtr, hCtarget, Nt, hNt, htarget⟩ :=
    exists_truncated_target_typical_window hq R hJ hΔ hC_T
  obtain ⟨CB, hCB, hbudget⟩ := exists_statusMarginal_cutBudget_le_log hq R hCtr.le
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hc₀ : 0 < 1 / (32 * Real.sqrt
      (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J))) := by positivity
  refine ⟨Ctr, Ctarget, CB, hCtr, hCtarget, hCB, ?_⟩
  intro F ω hmargin
  obtain ⟨Na, _, hNa⟩ := F.exists_a_le_moment_radius (A := 6) hmargin hCB.le
    (by norm_num) (lt_min hc₀ zero_lt_one)
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp
    (eventually_status_scale_separation (ell := F.ell) hCtr.le
      F.kappa_pos F.kappa_lt_mu)
  refine ⟨max Nt (max Na Ns), hNt.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT Φ hΦ S hM E₀ Ω hΩ heig hgap hgraph hanchor hn hr hm hD hK hsize hdepth
    hrows hclear L X g ε w δ B C₀ c₀ β BY
  have hnT : Nt ≤ S.n := (le_max_left _ _).trans hn
  have hnA : Na ≤ S.n := (le_max_left Na Ns).trans ((le_max_right _ _).trans hn)
  have hnS : Ns ≤ S.n := (le_max_right Na Ns).trans ((le_max_right _ _).trans hn)
  have hmF : S.m = F.m S.n := hm
  have hDF : S.D = F.D S.n := hD
  have hKF : S.K = F.K S.n := by
    change S.K = F.L S.n / (8 * F.m S.n)
    rw [← hmF]
    exact hK
  have hscales := hNs S.n hnS
  change 2 ≤ S.n ∧ ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ ≤ F.D S.n ∧
    1 ≤ F.D S.n ∧ 4 * F.D S.n ≤ F.m S.n ∧
      8 * F.K S.n * F.m S.n ≤ F.L S.n at hscales
  rw [← hmF, ← hDF, ← hKF, ← hr] at hscales
  obtain ⟨hn2, hrD, hDpos, hDm, hKL⟩ := hscales
  obtain ⟨hKpos, hsmall⟩ := hNa S.n hnA
  rw [← hKF] at hKpos
  have hmpos : 0 < S.m := by omega
  obtain ⟨hB, hcut⟩ := hbudget Λ T hT S hgraph hdepth hanchor L hn2 hr
    hrD hDpos hDm hKL hrows hclear
  obtain ⟨hcard, hX, hboundary, e, Ωt, hΩt, heigt, hgapt, he0, he, hphase, htrace,
      hmoment, halltail, hBX, htail, hwindow⟩ :=
    htarget Λ Φ hΦ S E₀ Ω F T hT hΩ heig hgap hgraph hanchor hnT hr hsize hdepth hrows hclear
  refine ⟨hKpos, hB, by dsimp [C₀, g]; positivity, hc₀, hcard, hX, hboundary,
    e, Ωt, hΩt, heigt, hgapt, he0, he, hphase, htrace, hmoment, halltail, hBX, htail, ?_⟩
  intro p E z
  refine ⟨hwindow, hmpos, ?_⟩
  intro W hW hWle a ΩX d n ell pre ψ hmass
  have hBupper : B ≤ CB * (S.n : ℝ) * (F.D S.n : ℝ) *
      Real.log (S.n : ℝ) ^ 12 := by
    dsimp only [B]
    rw [← hDF]
    exact le_of_eq (by ring)
  have ha : 0 < a := div_pos hW (by exact_mod_cast (show 0 < S.K by omega))
  have hsmall' : 6 * a ≤ min c₀ 1 / Real.sqrt B := by
    simpa only [ScannerExponents.a, ← hKF] using
      hsmall W B hW.le hWle hB hBupper
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr (zero_lt_one.trans_le hB)
  have hsqrt1 : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hprod : 6 * a * Real.sqrt B ≤ min c₀ 1 := (le_div_iff₀ hsqrt).mp hsmall'
  have haRadius : 6 * a ≤ c₀ / Real.sqrt B :=
    (le_div_iff₀ hsqrt).mpr (hprod.trans (min_le_left _ _))
  have haOne : 6 * a ≤ 1 := calc
    6 * a ≤ 6 * a * Real.sqrt B := le_mul_of_one_le_right (by positivity) hsqrt1
    _ ≤ min c₀ 1 := hprod
    _ ≤ 1 := min_le_right _ _
  have hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (band : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
        ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
          Real.log (surprisalMoment
            ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
              (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
            u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
              (map_embeddingSubtype_subset (T := Λ) Q) + (C₀ * B) * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
          ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
            Real.log (surprisalMoment
              ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues u) ≤
              u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) Q) + (C₀ * B) * u ^ 2) := by
    intro s hist band
    constructor
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common Φ Ω hΦ hanchor hΔ hΩ L hΩt
        heigt hgapt Q ((hcut s hist band).1 hs Q hQ) hu
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common Φ Ω hΦ hanchor hΔ hΩ L hΩt
        heigt hgapt Q ((hcut s hist band).2 hs Q hQ) hu
  exact eventually_actualScan_suppliedPrevector_sharp_upper hT S hdepth
    hmpos hM a (C₀ * B) (c₀ / Real.sqrt B) ha haRadius haOne L hKL Ωt hΩt
    E ell hmom hwindow.2.2.1 hmass

end OpenAI.Scan.CollarScan
