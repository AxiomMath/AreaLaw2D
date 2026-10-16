/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 576d1624411e36a16cfc84aba9883f91416bcd32,
`TNLean/PEPS/AreaLaw/Scan/ScanTruncationInputs.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to the encodings of
`OpenAI.Scan.TargetTypicalWindow`: `Site Λ` is `↥(Λ : Set (ℤ × ℤ))`, the bundled
`LocalHamiltonian` is an interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ`,
`AdmissibleSupport Λ R` is `↥(supports Λ R)`, `IsGappedGroundState` is the norm, eigenvector
and `OpenAI.HasGlobalGap` conditions (the norms of `Ω` and of the truncated vector are named,
because their pure states need them), TNLean's graph `cutBudget` is the square-lattice
`OpenAI.cutBudget` of the images in `ℤ²`, `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, and
`Matrix.traceDistance ρ σ` is written `(ρ - σ).traceNorm / 2`. The regional entropies
`regionalEntropy Λ q Ω Y` and the moment bound are those of `OpenAI.pureState` on
`Y.map (Function.Embedding.subtype _)`; the target typical set and its mass are those of the
finite-product reduction `FiniteProduct.reducedPure β Ωt X` about `FiniteProduct.entropy β Ωt X`,
as in `OpenAI.Scan.CollarScan.exists_truncated_target_typical_window`.
-/
import OpenAI.Scan.TargetTypicalWindow
import OpenAI.Scan.StatusMarginalBudget
import OpenAI.Scan.StatusScaleSeparation
import OpenAI.RegionalEntropyContinuity

/-!
# The truncated ground state and its entropy inputs

For one physical system at scale `n` (a gapped Hamiltonian with ground vector `Ω`, a
target and a collar scan at the source scales, under the source test geometry and the
entropy inputs of Proposition 9.2) a single truncated ground vector `Ωt` supplies every
field of `ScanTruncation`: the ground energy and gap of the truncated Hamiltonian
(Proposition 4.5), the transfer of the target and shell entropies from `Ω` to `Ωt`
(Lemma 2.1), the target typical window of width `n^{3/5}` (Lemma 3.1), and a common
marginal-tail parameter bounding the cut parameter of every status region of the scan.
The same vector also satisfies the marginal moment bound of Lemma 3.1 at every region.

## Main definitions

* `OpenAI.Scan.CollarScan.target`, `OpenAI.Scan.CollarScan.shell`: the target `X = A ∩ T` and
  the shells `Q_j = A ∩ (T_j \ T)`.

## Main statements

* `OpenAI.Scan.abs_log_card_sub_le_of_window`: the typical-entropy estimate
  `comparator:typical-entropies`.
* `OpenAI.Scan.CollarScan.exists_scanTruncation`: the construction.

## Implementation notes

**Local fix (retained trace-distance coefficient):** the source's estimate `t = O(n^(-500))`
(`08-scanner.tex`, lines 400–403) is supplied as `t ≤ C n^(-500)` with the common scanner
constant `C ≥ √(2/g)` rather than with coefficient one, as recorded in TNLean's
`docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `08-scanner.tex`, lines 21–59 and 349–414; Lemma 2.1 (`lem:continuity`),
  `01-preliminaries.tex`, lines 33–46; Lemma 3.1 (`lem:tail`), `02-initial.tex`,
  lines 34–69; `07-comparators.tex`, lines 37–53. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace OpenAI.Scan

open Arealaw

/-- **Typical entropies** (`comparator:typical-entropies`, `07-comparators.tex`,
lines 37–53). If every weight of a nonempty set lies in `[e^{-S-w}, e^{-S+w}]`, then the
logarithm of its size is within `w + |log z|` of `S`, where `z` is its total weight. -/
theorem abs_log_card_sub_le_of_window {ι : Type*} (p : ι → ℝ) (E : Finset ι)
    (hE : E.Nonempty) {S w : ℝ}
    (hp : ∀ i ∈ E, Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) :
    |Real.log E.card - S| ≤ w + |Real.log (∑ i ∈ E, p i)| := by
  have hcard : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
  have hlow : (E.card : ℝ) * Real.exp (-S - w) ≤ ∑ i ∈ E, p i := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum fun i hi ↦ (hp i hi).1
  have hhigh : ∑ i ∈ E, p i ≤ (E.card : ℝ) * Real.exp (-S + w) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum fun i hi ↦ (hp i hi).2
  have hpos : 0 < (E.card : ℝ) * Real.exp (-S - w) := by positivity
  have h1 := Real.log_le_log hpos hlow
  have h2 := Real.log_le_log (hpos.trans_le hlow) hhigh
  rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
  rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (∑ i ∈ E, p i)),
    neg_abs_le (Real.log (∑ i ∈ E, p i))]

namespace CollarScan

variable {Λ : Finset (ℤ × ℤ)} {I : Type*} (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)

/-- The target `X = A ∩ T` (`08-scanner.tex`, line 23). -/
def target (T : Finset (ℤ × ℤ)) : Finset (↥(Λ : Set (ℤ × ℤ))) := S.A.filter fun x ↦ x.val ∈ T

/-- The shell `Q_j = A ∩ (T_j \ T)` with `T_j = T + [-j, j]²` (`08-scanner.tex`,
line 22). -/
def shell (T : Finset (ℤ × ℤ)) (j : ℕ) : Finset (↥(Λ : Set (ℤ × ℤ))) :=
  S.A.filter fun x ↦ x.val ∈ ambientDilation T j ∧ x.val ∉ T

/-- A shell of depth at most `L` lies in the compact truncation set `A ∩ T_L`. -/
theorem shell_subset_truncationSet {T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {j L : ℕ} (hj : j ≤ L) :
    S.shell T j ⊆ S.truncationSet L := by
  intro x hx
  obtain ⟨hxA, hxj, -⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxA, ?_⟩
  rw [hdepth]
  exact ((ambientDepth_le_iff_mem_dilation T hT x.val j).mpr hxj).trans (by exact_mod_cast hj)

end CollarScan

/-- `√(2 min(n^{-1000}, g/4) / g) ≤ √(2/g) n^{-500}`: the trace-distance estimate of
`08-scanner.tex`, lines 400–403, with its fixed coefficient. -/
theorem sqrt_truncationError_le {g : ℝ} (hg : 0 < g) (n : ℕ) :
    Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) ≤
      Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
  have hhalf : Real.sqrt ((n : ℝ) ^ (-1000 : ℝ)) = (n : ℝ) ^ (-500 : ℝ) := by
    rw [show (-1000 : ℝ) = (-500) * 2 by norm_num, Real.rpow_mul (Nat.cast_nonneg n),
      Real.rpow_two, Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have h2g : (0 : ℝ) ≤ 2 / g := div_nonneg (by norm_num) hg.le
  calc Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g)
      ≤ Real.sqrt ((2 / g) * (n : ℝ) ^ (-1000 : ℝ)) := by
        apply Real.sqrt_le_sqrt
        rw [show 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g =
          (2 / g) * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) by ring]
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) h2g
    _ = Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by rw [Real.sqrt_mul h2g, hhalf]

namespace CollarScan

open SpectralFilter SimpleGraph

open Classical in
/-- **The truncated ground state and its entropy inputs at scale `n`.** The truncation
radius coefficient `C_tr` is fixed by the Hamiltonian parameters and the target-size
coefficient; then a constant `C₀` is fixed by the local dimension `q`. For every scan
constants `κ` with local dimension `q`, normalized gap `g = Δ / max(1, J(‖f‖₁ + 1))` and
`κ.C ≥ C₀`, and every sufficiently large `n`: every gapped physical system with a collar
scan at the source scales, under the source test geometry and the source entropy inputs
`S_Ω(X) ≤ C_e n^{1+e}` and `S_Ω(Q_j) ≤ C_e(nL^e + n)` (`scanner:entropy-input`), has one
ground vector `Ωt` of the truncated Hamiltonian, with gap `g/2`, satisfying the marginal
moment bound of Lemma 3.1 at every region, together with a `ScanTruncation` whose energy,
gap, entropies, trace distance, typical mass and typical dimension are those of `Ω` and
`Ωt`, and whose marginal-tail parameter bounds the cut parameter of every completed and
pre-charge status region of the scan.

Source: `08-scanner.tex`, lines 21–59 and 399–414; Lemma 2.1, Lemma 3.1 and
`07-comparators.tex`, lines 37–53. -/
theorem exists_scanTruncation (X : ScannerExponents) (R : ℕ) {J Δ CT : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCT : 0 ≤ CT) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q], ∃ C₀ : ℝ, ∀ κ : ScanConstants, κ.q = q →
      κ.g = Δ / positiveNormalization 1 (Δ / 2) J → C₀ ≤ κ.C →
      ∀ᶠ n : ℕ in atTop,
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hT : T.Nonempty)
        (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ),
        IsAdmissible Λ R J Φ →
        ∀ (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R))
        (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩ : ‖Ω‖ = 1),
        hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, (S.anchor i).1 ∈ i.val) →
        S.n = n → S.m = X.m n → S.K = X.K n → S.D = X.D n →
        S.r₀ = ⌈Ctr * Real.log (n : ℝ) ^ 2⌉₊ →
        (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2 →
        (∀ d : ℕ, 1 ≤ d → d ≤ X.L n →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
          ((2 * X.L n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        (pureState (WithLp.ofLp Ω) (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
            (map_embeddingSubtype_subset (T := Λ) (S.target T)) ≤
          κ.Ce * (n : ℝ) ^ (1 + X.e) →
        (∀ j ≤ X.L n,
          (pureState (WithLp.ofLp Ω) (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
              (map_embeddingSubtype_subset (T := Λ) (S.shell T j)) ≤
            κ.Ce * (n * (X.L n : ℝ) ^ X.e + n)) →
        let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q
        let B : Finset (↥(Λ : Set (ℤ × ℤ))) → ℝ := fun Y ↦
          cutBudget q Λ ((S.truncationSet (X.L n)).map (Function.Embedding.subtype _)) S.r₀
            (fun i => (S.anchor i).1) (Y.map (Function.Embedding.subtype _))
        ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩt : ‖Ωt‖ = 1),
          (∑ i, S.truncatedEnergyTerm Φ Ω J Δ (X.L n) i) *ᵥ WithLp.ofLp Ωt =
            (e : ℂ) • WithLp.ofLp Ωt ∧
          HasGlobalGap (∑ i, S.truncatedEnergyTerm Φ Ω J Δ (X.L n) i) (WithLp.ofLp Ωt) e
            (κ.g / 2) ∧
          (∀ (Y : Finset (↥(Λ : Set (ℤ × ℤ)))) (u : ℝ),
            |u| ≤ tailRadius (2 / κ.g) (B Y) →
            Real.log (surprisalMoment
                ((pureState (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).restrict
                    (map_embeddingSubtype_subset (T := Λ) Y)).psd.isHermitian.eigenvalues u) ≤
              u * (pureState (WithLp.ofLp Ωt)
                  (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                  (map_embeddingSubtype_subset (T := Λ) Y) +
                512 * Real.exp 1 * (2 / κ.g) * B Y * u ^ 2) ∧
          ∃ Tr : ScanTruncation X κ n,
            Tr.E0 = e ∧ Tr.gap = κ.g / 2 ∧
            Tr.SX = (pureState (WithLp.ofLp Ω)
              (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) (S.target T)) ∧
            Tr.SXt = (pureState (WithLp.ofLp Ωt)
              (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) (S.target T)) ∧
            Tr.SQ = (fun j ↦ (pureState (WithLp.ofLp Ω)
              (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) (S.shell T j))) ∧
            Tr.SQt = (fun j ↦ (pureState (WithLp.ofLp Ωt)
              (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
                (map_embeddingSubtype_subset (T := Λ) (S.shell T j))) ∧
            Tr.traceDist = (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
              vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ∧
            Tr.z = (FiniteProduct.reducedPure_posSemidef β Ωt
                (S.target T)).isHermitian.spectralRestrictionMass (Entropy.typicalSet
                (FiniteProduct.reducedPure_posSemidef β Ωt (S.target T)).isHermitian.eigenvalues
                (FiniteProduct.entropy β Ωt (S.target T)) Tr.width) ∧
            Tr.dstar = (Entropy.typicalSet
              (FiniteProduct.reducedPure_posSemidef β Ωt (S.target T)).isHermitian.eigenvalues
                (FiniteProduct.entropy β Ωt (S.target T)) Tr.width).card ∧
            ∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
              (k ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band), B Q ≤ Tr.Bmarg) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  B Q ≤ Tr.Bmarg) := by
  classical
  obtain ⟨Ctr, hCtr, hroot⟩ := exists_truncated_reducedState_moment_tail_bounds R hJ hΔ
    (show 0 ≤ CT + 1 by linarith)
  refine ⟨Ctr, hCtr, ?_⟩
  intro q _
  have hq : 1 ≤ q := NeZero.pos q
  obtain ⟨Clat, hClat, hlat⟩ := exists_latticeCutBudget_le_log hq R hCtr.le
    (show (0 : ℝ) ≤ 4 by norm_num)
  obtain ⟨CB, hCB, hstat⟩ := exists_statusMarginal_cutBudget_le_log hq R hCtr.le
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  refine ⟨max (max 4 (CT + 1))
    (max (Real.sqrt (2 / (Δ / positiveNormalization 1 (Δ / 2) J))) CB), ?_⟩
  intro κ hκq hκg hκC
  have hC4 : 4 ≤ κ.C := (le_max_left _ _).trans ((le_max_left _ _).trans hκC)
  have hCT1 : CT + 1 ≤ κ.C := (le_max_right _ _).trans ((le_max_left _ _).trans hκC)
  have hCg : Real.sqrt (2 / κ.g) ≤ κ.C := by
    rw [hκg]; exact (le_max_left _ _).trans ((le_max_right _ _).trans hκC)
  have hCB' : CB ≤ κ.C := (le_max_right _ _).trans ((le_max_right _ _).trans hκC)
  obtain ⟨N₁, -, hscalar⟩ := Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg.le)
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 Clat))
  filter_upwards [eventually_status_scale_separation (ell := X.ell) hCtr.le X.kappa_pos
    X.kappa_lt_mu, eventually_ge_atTop N₁] with n hscales hnN
  intro Λ T _ hT Φ hΦ S E₀ Ω hΩ heig hgap hgraph hdepth hanchor hSn hSm hSK hSD hSr hsize
    hrows hclear hinX hinQ β B
  subst hSn
  dsimp only [roundedLogRadius] at hscales
  obtain ⟨hn2, hr, hDpos, hDm, hKL⟩ := hscales
  have hr' : S.r₀ ≤ S.D := by rw [hSr, hSD]; exact hr
  have hDpos' : 1 ≤ S.D := by rw [hSD]; exact hDpos
  have hDm' : 4 * S.D ≤ S.m := by rw [hSD, hSm]; exact hDm
  have hKL' : 8 * S.K * S.m ≤ X.L S.n := by rw [hSK, hSm]; exact hKL
  obtain ⟨hcard, hXsub, hbdry⟩ := S.source_target_geometry X T hT (by omega) hsize hdepth
    hrows hclear
  obtain ⟨e, Ωt, hΩt, heigt, hgapt, he0, he, -, htrace, hmom, htail⟩ :=
    hroot (q := q) Λ Φ hΦ S E₀ Ω hΩ heig hgap hgraph hanchor (X.L S.n) hn2 hSr hcard
  -- The target window of width `n^{3/5}`.
  set Xs := S.target T with hXs
  have hBX : B Xs ≤ max 1 Clat * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 := by
    have hb := hlat Λ (fun i => (S.anchor i).1) hanchor
      ((S.truncationSet (X.L S.n)).map (Function.Embedding.subtype _))
      (Xs.map (Function.Embedding.subtype _)) (Finset.map_subset_map.mpr hXsub)
      (S.n : ℝ) 1 (by exact_mod_cast hn2) le_rfl
      (by simpa only [mul_one] using
        (show ((edgeBoundary Λ (Xs.map (Function.Embedding.subtype _))).card : ℝ) ≤ 4 * S.n by
          exact_mod_cast hbdry))
    simp only [B]
    rw [hSr]
    calc _ ≤ Clat * ((S.n : ℝ) * Real.log (S.n : ℝ) ^ 12) := by simpa only [mul_one] using hb
      _ ≤ max 1 Clat * ((S.n : ℝ) * Real.log (S.n : ℝ) ^ 12) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = _ := by ring
  have hBXpos : 0 < B Xs := lt_of_lt_of_le zero_lt_one (one_le_cutBudget q Λ _ S.r₀ _ _)
  have htypical :
      surprisalTail (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues
      (FiniteProduct.entropy β Ωt Xs) ((S.n : ℝ) ^ ((3 : ℝ) / 5)) ≤ (S.n : ℝ) ^ (-100 : ℝ) := by
    rw [← surprisalTail_restrict_pureState_eq_finiteProduct Ωt
      (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)]
    exact (htail Xs _).trans ((min_le_right _ _).trans (hscalar S.n hnN (B Xs) hBXpos hBX))
  have hδ : (S.n : ℝ) ^ (-100 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < S.n by omega))
      (by norm_num)
  obtain ⟨-, hz1, hzpos, hzle, hEne, hwin⟩ := target_typicalSet_bounds Ωt hΩt Xs htypical hδ
  -- Trace distance and entropy continuity.
  set t := (vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)) -
    vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 with ht
  have ht0 : 0 ≤ t := div_nonneg (traceNorm_nonneg _) zero_le_two
  have htle : t ≤ κ.C * (S.n : ℝ) ^ (-500 : ℝ) := by
    refine htrace.trans ((sqrt_truncationError_le hg S.n).trans ?_)
    rw [← hκg]
    exact mul_le_mul_of_nonneg_right hCg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hcont (Y : Finset (↥(Λ : Set (ℤ × ℤ)))) (hY : Y ⊆ S.truncationSet (X.L S.n)) :
      |(pureState (WithLp.ofLp Ωt) (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) Y) -
        (pureState (WithLp.ofLp Ω) (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) Y)| ≤
        κ.C * √t * (1 + κ.C * S.n ^ 2 * Real.log κ.q) := by
    have hYc : (Y.card : ℝ) ≤ κ.C * S.n ^ 2 :=
      (by exact_mod_cast Finset.card_le_card hY : (Y.card : ℝ) ≤ _).trans
        (hcard.trans (mul_le_mul_of_nonneg_right hCT1 (by positivity)))
    refine (abs_regionalEntropy_sub_le_sqrt_traceDistance Λ q Ωt Ω hΩt hΩ Y).trans ?_
    rw [hκq]
    gcongr
  refine ⟨e, Ωt, hΩt, heigt, by rw [hκg]; exact hgapt, by rw [hκg]; exact hmom, ?_⟩
  obtain ⟨-, hstatus⟩ := hstat Λ T hT S hgraph hdepth hanchor (X.L S.n) hn2 hSr hr' hDpos' hDm'
    hKL' hrows hclear
  set Etyp := Entropy.typicalSet
    (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.eigenvalues
    (FiniteProduct.entropy β Ωt Xs) ((S.n : ℝ) ^ ((3 : ℝ) / 5)) with hEtyp
  have hlogd : |Real.log (Etyp.card : ℝ) -
      (pureState (WithLp.ofLp Ωt) (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
        (map_embeddingSubtype_subset (T := Λ) Xs)| ≤
      (S.n : ℝ) ^ ((3 : ℝ) / 5) +
        |Real.log
          ((FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass
            Etyp)| := by
    rw [regionalEntropy_eq_finiteProduct Λ q Ωt]
    exact abs_log_card_sub_le_of_window _ Etyp hEne
      fun i hi ↦ ⟨(hwin i hi).2.1, (hwin i hi).2.2⟩
  refine ⟨{
      E0 := e
      gap := κ.g / 2
      E0_nonneg := he0
      E0_le := he.trans (min_le_left _ _)
      half_g_le_gap := le_rfl
      SX := (pureState (WithLp.ofLp Ω)
        (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) Xs)
      SXt := (pureState (WithLp.ofLp Ωt)
        (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) Xs)
      SQ := fun j ↦ (pureState (WithLp.ofLp Ω)
        (star_dotProduct_self_eq_one_of_norm_eq_one hΩ)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) (S.shell T j))
      SQt := fun j ↦ (pureState (WithLp.ofLp Ωt)
        (star_dotProduct_self_eq_one_of_norm_eq_one hΩt)).regionEntropy
          (map_embeddingSubtype_subset (T := Λ) (S.shell T j))
      entropy_input_X := hinX
      entropy_input_Q := hinQ
      traceDist := t
      traceDist_nonneg := ht0
      traceDist_le := htle
      continuity_X := hcont Xs hXsub
      continuity_Q := fun j hj ↦ hcont _ (S.shell_subset_truncationSet hT hdepth hj)
      dstar := Etyp.card
      z := (FiniteProduct.reducedPure_posSemidef β Ωt Xs).isHermitian.spectralRestrictionMass Etyp
      width := (S.n : ℝ) ^ ((3 : ℝ) / 5)
      width_eq := rfl
      dstar_pos := by exact_mod_cast hEne.card_pos
      z_pos := hzpos
      z_le_one := hzle
      one_sub_le_z := hz1
      log_dstar_le := hlogd
      Bmarg := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
      Bmarg_le := by
        rw [hSD]
        have : (0 : ℝ) ≤ (S.n : ℝ) * X.D S.n * Real.log (S.n : ℝ) ^ 12 := by positivity
        nlinarith },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k hist band ↦ hstatus k hist band⟩

end CollarScan

end OpenAI.Scan
