/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 576d1624411e36a16cfc84aba9883f91416bcd32,
`TNLean/PEPS/AreaLaw/Scan/SourceStatusMarginalMoments.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to the encodings of
`OpenAI.Scan.StatusMarginalMoments`: `Site Λ` is `↥(Λ : Set (ℤ × ℤ))`, the bundled
`LocalHamiltonian` is an interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ`,
`IsGappedGroundState` is the norm, eigenvector and `OpenAI.HasGlobalGap` conditions (the norm
of the truncated vector a named witness), the regional states and entropies are those of
`OpenAI.pureState` on `Q.map (Function.Embedding.subtype _)`, `Geometry.boundaryEndpoints Λ S.A`
is `OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`,
and `Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`.
-/
import OpenAI.Scan.StatusMarginalMoments
import OpenAI.Scan.StatusScaleSeparation
import OpenAI.Scan.CompactCollarCounting
import OpenAI.Scan.BadChargeRatioBound

/-!
# Physical status moments at the literal source scales

The actual target-size and ambient-layer bounds give the quadratic volume
needed by truncation. The rounded source powers supply every scale inequality
used by the five physical cuts, including a positive integer band count.
The threshold depends on the fixed exponents and truncation coefficient, and
is chosen before the local dimension and every physical scanner.

The resulting ground vector is the same vector in the spectral, energy,
phase, trace-distance and all completed/pre-charge marginal moment estimates.
No compact-volume bound, status boundary bound or moment bound is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 21–58 and 400–414; `07-comparators.tex`, lines 70–85,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace OpenAI.Scan.CollarScan

open Arealaw SpectralFilter SimpleGraph

/-- The source geometry and rounded scales give a single quantitative truncated
vector and a common marginal moment budget at every physical status. The radius
coefficient and integer threshold precede the local dimension. The budget
coefficient may depend on that dimension, but precedes every physical instance.
The threshold is allowed to depend on the fixed exponent gaps.

Source: `08-scanner.tex`, lines 21–58 and 400–414. -/
theorem exists_source_statusMarginal_moment_bounds
    (R : ℕ) {J Δ Ct ell kappa mu : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCt : 0 ≤ Ct) (hell : 0 < ell)
    (hkappa : 0 < kappa) (hkm : kappa < mu) (hmuL : mu < 1 - ell) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ (q : ℕ) [NeZero q],
      ∃ CB : ℝ, 0 < CB ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hT : T.Nonempty)
          (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
          IsAdmissible Λ R J Φ →
          ∀ (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
          (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)),
          ‖Ω‖ = 1 → hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
          HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
          S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ i, (S.anchor i).1 ∈ i.val) →
          ∀ L : ℕ, N ≤ S.n →
          L = ⌊(S.n : ℝ) ^ (1 - ell)⌋₊ →
          S.m = ⌊(S.n : ℝ) ^ mu⌋₊ →
          S.D = ⌈(S.n : ℝ) ^ kappa⌉₊ →
          S.K = L / (8 * S.m) →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          (T.card : ℝ) ≤ Ct * (S.n : ℝ) ^ 2 →
          (∀ d : ℕ, 1 ≤ d → d ≤ L →
            (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
          (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
            ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          1 ≤ S.K ∧
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let C₀ := 512 * Real.exp 1 * (2 / g)
          let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
          0 < C₀ ∧ 0 < c₀ ∧
          ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩt : ‖Ωt‖ = 1) (B : ℝ),
            1 ≤ B ∧ B ≤ CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) ∧
            (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ WithLp.ofLp Ωt =
              (e : ℂ) • WithLp.ofLp Ωt ∧
            HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) (WithLp.ofLp Ωt) e (g / 2) ∧
            0 ≤ e ∧ e ≤ ε ∧
            (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
            (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
                vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ≤
              Real.sqrt (2 * ε / g) ∧
            ∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
              (k ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (surprisalMoment
                        ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                            (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues
                        u) ≤
                      u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                          (map_embeddingSubtype_subset (T := Λ) Q) + C₀ * B * u ^ 2) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (surprisalMoment
                        ((pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                            (map_embeddingSubtype_subset (T := Λ) Q)).psd.isHermitian.eigenvalues
                        u) ≤
                      u * (pureState (ι := Reg (Qudits q) Λ) (WithLp.ofLp Ωt)
                          (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                          (map_embeddingSubtype_subset (T := Λ) Q) + C₀ * B * u ^ 2) := by
  classical
  obtain ⟨Ctr, hCtr, hstatus⟩ := exists_truncated_statusMarginal_moment_bounds R hJ hΔ
    (show 0 ≤ Ct + 1 by linarith)
  have hscales := (eventually_status_scale_separation (ell := ell) hCtr.le hkappa hkm).and
    (eventually_one_le_source_bandCount (hkappa.trans hkm) hmuL)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hscales
  refine ⟨Ctr, hCtr, max N 2, le_max_right _ _, ?_⟩
  intro q _
  obtain ⟨CB, hCB, hstatusq⟩ := hstatus q
  refine ⟨CB, hCB, ?_⟩
  intro Λ T _ hT Φ hΦ S E₀ Ω hΩ heig hgap hgraph hdepth hanchor L hn hL hm hD hK hradius
    hsize hrows hclear
  obtain ⟨hscales, hKpos⟩ := hN S.n ((le_max_left N 2).trans hn)
  dsimp only [roundedLogRadius] at hscales
  rw [← hL, ← hm, ← hD, ← hK, ← hradius] at hscales
  rw [← hL, ← hm, ← hK] at hKpos
  obtain ⟨hn2, hr, hDpos, hDm, hKL⟩ := hscales
  have hLn : L ≤ S.n := by
    rw [hL]
    exact (source_lengths_le (n := S.n) (mu := mu) (by omega) hell.le (by linarith)).1
  have hcard : ((S.truncationSet L).card : ℝ) ≤ (Ct + 1) * (S.n : ℝ) ^ 2 := by
    simpa only [truncationSet, hdepth] using
      card_compact_collar_le_quadratic hT S.A hLn hsize hrows
  exact ⟨hKpos, hstatusq Λ T hT Φ hΦ S E₀ Ω hΩ heig hgap hgraph hdepth hanchor L hn2 hradius
    hcard hr hDpos hDm hKL hrows hclear⟩

end OpenAI.Scan.CollarScan
