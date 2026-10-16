/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/PositivePrefixEntropyTransfer.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. TNLean's `Site Λ` is
`↥(Λ : Set (ℤ × ℤ))`, its `StateSpace Λ q` is `EuclideanSpace ℂ (Reg (Qudits q) Λ)`, and its
`regionalEntropy Λ q Ω B` is the `regionEntropy` of `OpenAI.pureState` on the region
`B.map (Function.Embedding.subtype _)`, with the normalization supplied from `‖Ω‖ = 1` by
`OpenAI.star_dotProduct_self_eq_one_of_norm_eq_one`; the unit-norm hypotheses are therefore
named binders. QICLean's `Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`.
The import of `TNLean.PEPS.AreaLaw.TwoFamilies` is covered by `OpenAI.RegionalEntropyContinuity`.
-/
import OpenAI.Scan.PrefixComparison
import OpenAI.Scan.Budgets
import OpenAI.RegionalEntropyContinuity

/-!
# Entropy transfer on positive-depth prefixes

An entropy bound for the original vector on every whole-row positive-depth prefix transfers to
the same supplied truncated vector. The compact-region cardinality bound and the quantitative
truncation estimate give one threshold before the domain, vectors, depth function and prefixes.

The original entropy bound is an explicit hypothesis, as in the scanner proposition. No
Hamiltonian, truncated vector or comparison family is chosen here.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `08-scanner.tex`, `scanner:entropy-input`, lines 353--357, and its continuity argument,
  lines 399--404; `01-preliminaries.tex`, Lemma 2.1, lines 33--46; revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Arealaw Matrix

noncomputable section

namespace OpenAI.Scan

/-- A single large-scale threshold transfers the original entropy bound to
every positive-depth prefix in the same truncated vector. The global trace distance retains
the normalized gap coefficient, and the dimension bound concerns only the compact region. The
threshold is independent of the entropy coefficient and exponent as well as the finite system.
Source: `08-scanner.tex`, lines 353--357 and 399--404. -/
theorem eventually_regionalEntropy_positiveDepthPrefix_le
    (q : ℕ) (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (Λ : Finset (ℤ × ℤ)) (Ω Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ))
      (hΩ : ‖Ω‖ = 1) (hΩt : ‖Ωt‖ = 1)
      (A : Finset ↥(Λ : Set (ℤ × ℤ))) (depth : ↥(Λ : Set (ℤ × ℤ)) → ℤ) (L : ℕ),
      ((depthPrefix A depth (L : ℤ)).card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
      (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
          vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ≤
        Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
      ∀ Ce e : ℝ,
      (∀ j : ℕ, j ≤ L →
        (pureState (WithLp.ofLp Ω) (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
            (map_embeddingSubtype_subset (T := Λ) (positiveDepthPrefix A depth (j : ℤ))) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n)) →
      ∀ j : ℕ, j ≤ L →
        (pureState (WithLp.ofLp Ωt)
            (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
            (map_embeddingSubtype_subset (T := Λ) (positiveDepthPrefix A depth (j : ℤ))) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ) := by
  classical
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have key := eventually_continuityCost_le_of_fixed_coefficient
    (Real.sqrt (2 / g)) (max 4 Cvol) (Real.log q)
    (Real.sqrt_nonneg _) (le_trans (by norm_num) (le_max_left _ _))
    (Real.log_nonneg hq')
  filter_upwards [key] with
    n hcost Λ Ω Ωt hΩ hΩt A depth L hcard hdist Ce e hentropy j hj
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  set R := positiveDepthPrefix A depth (j : ℤ) with hR
  -- Entropy continuity in the regional dimension.
  have hcont := abs_regionalEntropy_sub_le_sqrt_traceDistance Λ q Ωt Ω hΩt hΩ R
  set t := (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 with ht
  -- The region is contained in the full prefix, so its volume is controlled.
  have hsub : R ⊆ depthPrefix A depth (L : ℤ) := by
    rw [hR]
    intro x hx
    simp only [positiveDepthPrefix, Finset.mem_filter] at hx
    simp only [depthPrefix, Finset.mem_filter]
    exact ⟨hx.1, hx.2.2.trans (by exact_mod_cast hj)⟩
  have hcardle : (R.card : ℝ) ≤ (max 4 Cvol) * (n : ℝ) ^ 2 := by
    have hcard1 : (R.card : ℝ) ≤ ((depthPrefix A depth (L : ℤ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    refine hcard1.trans (hcard.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right 4 Cvol) (by positivity)
  -- The actual trace distance stays below the threshold of the continuity estimate.
  have hhalf : Real.sqrt ((n : ℝ) ^ (-1000 : ℝ)) = (n : ℝ) ^ (-500 : ℝ) := by
    have h1 : (n : ℝ) ^ (-1000 : ℝ) = ((n : ℝ) ^ (-500 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-500 : ℝ)) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      norm_num
    rw [h1, Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have htbound : t ≤ Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
    refine hdist.trans ?_
    have hmin : min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) ≤ (n : ℝ) ^ (-1000 : ℝ) := min_le_left _ _
    have h2g : (0 : ℝ) ≤ 2 / g := div_nonneg (by norm_num) hg.le
    have hle : 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g ≤ 2 * (n : ℝ) ^ (-1000 : ℝ) / g := by
      rw [show 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g
            = (2 / g) * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) by ring,
        show 2 * (n : ℝ) ^ (-1000 : ℝ) / g = (2 / g) * (n : ℝ) ^ (-1000 : ℝ) by ring]
      exact mul_le_mul_of_nonneg_left hmin h2g
    calc Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g)
        ≤ Real.sqrt (2 * (n : ℝ) ^ (-1000 : ℝ) / g) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
          rw [show 2 * (n : ℝ) ^ (-1000 : ℝ) / g = (2 / g) * (n : ℝ) ^ (-1000 : ℝ) by ring,
            Real.sqrt_mul h2g, hhalf]
  -- The continuity cost on this region is at most `n^{-247}`.
  have hBcost : 4 * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q) ≤ (n : ℝ) ^ (-247 : ℝ) := by
    refine le_trans ?_ (hcost t htbound)
    have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have h4C : (4 : ℝ) ≤ max 4 Cvol := le_max_left 4 Cvol
    have hC0 : (0 : ℝ) ≤ max 4 Cvol := le_trans (by norm_num) h4C
    have hfacpos : (0 : ℝ) ≤ 1 + (R.card : ℝ) * Real.log q := by
      have := mul_nonneg (Nat.cast_nonneg R.card) hlq; linarith
    have hfac1 : 1 + (R.card : ℝ) * Real.log q ≤
        1 + (max 4 Cvol) * (n : ℝ) ^ 2 * Real.log q := by
      have := mul_le_mul_of_nonneg_right hcardle hlq; linarith
    calc 4 * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q)
        ≤ (max 4 Cvol) * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4C hst) hfacpos
      _ ≤ (max 4 Cvol) * Real.sqrt t * (1 + (max 4 Cvol) * (n : ℝ) ^ 2 * Real.log q) :=
          mul_le_mul_of_nonneg_left hfac1 (mul_nonneg hC0 hst)
  -- Combine with the continuity difference and the original prefix bound.
  have heΩ := hentropy j hj
  rw [← hR] at heΩ
  set St := (pureState (WithLp.ofLp Ωt)
    (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
      (map_embeddingSubtype_subset (T := Λ) R)
  set S := (pureState (WithLp.ofLp Ω)
    (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
      (map_embeddingSubtype_subset (T := Λ) R)
  have hupper : St ≤ S + 4 * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q) := by
    have habs := le_abs_self (St - S)
    linarith [hcont, habs]
  linarith [heΩ, hupper, hBcost]

end OpenAI.Scan
