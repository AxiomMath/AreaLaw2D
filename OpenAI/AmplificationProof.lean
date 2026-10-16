/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/AmplificationProof.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations:
* TNLean's `amplificationBound` proves `AmplificationBound q R J Δ` through
  `amplificationBound_of_radius_output`; here its conclusion is restated as
  `OpenAI.amplificationOutput_complex`, the frozen `OpenAI.AmplificationOutput ℂ` (Proposition
  10.2 without its cut-clearance clause), from which `OpenAI.amplification_of_amplificationOutput`
  gives the frozen statement.  TNLean fixes `p = 10⁶` (`Exponents.amplificationPower`); here `p`
  is any natural number with `1 - 10⁻⁶ < p / (p + 1)`, of which the proof uses only `1 ≤ p`.
  The radius exponent `(1 - ε) / α` is written out with `ε = 1 / 100000` and
  `α = kernelExponent p`, as in the frozen statement.
* Statement encodings: the frozen statement takes a cut `A ⊆ Λ` and a target `T` as finite
  subsets of `ℤ × ℤ`, `X = A ∩ T`, `S₀ = A ∩ ambientDilation T (collarWidth n)`, a vector
  `Ω : Reg (Qudits q) Λ → ℂ` with `star Ω ⬝ᵥ Ω = 1`, the mutual information
  `(pureState Ω hΩ).mutualInfo` and the neighborhood `graphNbhd Λ S₀ (2 * r)`.  The proof runs
  in TNLean's encoding: the cuts `X.subtype (· ∈ ↑Λ)` of the sites, the vector
  `WithLp.toLp 2 Ω`, and `FiniteProduct.mutualInformation`, related to the frozen quantities by
  the added `OpenAI.mutualInfo_pureState_eq_finiteProduct`.
* The degenerate case `q = 0 ∨ J < 0` of the source proof is excluded by the hypotheses
  `1 ≤ q` and `0 < J` and is not ported.  The anchors `a : supports Λ R → ℤ × ℤ` are chosen in
  each support, as in `OpenAI.LatticeConstraints`.
* `uniformAreaLaw_of_collar_twoFamilies` (conditional on Propositions 9.6 and 11.2) is not
  ported.
-/
import OpenAI.AmplificationCutClearance
import OpenAI.AmplificationProofSteps
import OpenAI.Amplification.ConstraintWordLists
import OpenAI.Amplification.ConstraintWordTruncation
import OpenAI.Amplification.LatticeChannelSpatialOmission
import OpenAI.Amplification.LatticeExcitedDecay
import OpenAI.Amplification.RadiusBound
import OpenAI.Amplification.TypicalProjectors
import OpenAI.Scan.DomainFiniteProduct

/-!
# Proposition 10.2: amplification

This module proves Proposition 10.2 of the two-dimensional area-law manuscript
(`prop:amplification`) over `ℂ`, without its cut-clearance clause: under the collar
hypotheses, at every large scale there is a radius `r ≤ C_M n^((1-ε)/α)` such that every
part of the target `X = A ∩ T` has mutual information at most `C_M n^(-M)` with every
physical set avoiding the graph neighborhood `N_{2r}(S₀)`.

The proof follows the source. At the scale `n`, the typical projections of `X`, `Y = S₀ \ X`
and `S₀` give the restoring operator `R₀` and the column operator `B₀` on the physical system
and two ancillary copies `s', e'` of `X`, with `‖R₀‖, ‖B₀‖ ≤ M₀ = e^{(𝓘+3w)/2}`. The clocks run
for the time `t_*` and the radius `r` of `eq:amplification-time-choice`. On one clock
realization, the excited-state decay bounds the excited component of `R₀ φ`, the omission
estimate of the local-products lemma, applied through the column identity `R₀ φ = B₀ (Ω ⊗ ξ)`,
bounds the omitted events, and the truncation estimate bounds the radius truncation. Markov's
inequality and a union bound select a realization on which all three are at most `n^{-K}`.
The polar correction of `L' R₀` then gives a unitary acting on `s'` and `N_{2r}(S₀)` that
moves `φ` to within `9 n^{-K/2}` of the restored vector `η`. On the sites enlarged by the two
copies, `φ` carries the original reduction of the target on `e'`, and `η` has no mutual
information between `e'` and any physical set. Continuity of mutual information then gives
the output bound, with `K = 4(M + 2)`.

## Main statements

* `OpenAI.mutualInfo_pureState_eq_finiteProduct`: the mutual information of a pure state
  between two regions of `Λ` is the finite-product mutual information of the cuts of the sites
  they define.
* `OpenAI.amplificationOutput_complex`: Proposition 10.2 over `ℂ`, without its cut-clearance
  clause.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 261–296 (statement)
  and 298–576 (proof); Lemma 10.1 (`lem:amplification-local-products`), lines 42–72, and
  `eq:amplification-excited-decay`, lines 237–253.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix MeasureTheory SpectralFilter Arealaw
open scoped Kronecker NNReal ComplexOrder MatrixOrder InnerProductSpace Matrix.Norms.L2Operator

namespace OpenAI

/-- The mutual information of the pure state of `Ω` between two regions `X', Y' ⊆ Λ` is the
finite-product mutual information of `Ω` between cuts of the sites of `Λ` with these images. -/
theorem mutualInfo_pureState_eq_finiteProduct {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) {X Y : Finset ↥(Λ : Set (ℤ × ℤ))}
    {X' Y' : Finset (ℤ × ℤ)} (hXX : X.map (Function.Embedding.subtype _) = X')
    (hYY : Y.map (Function.Embedding.subtype _) = Y') (hX : X' ⊆ Λ) (hY : Y' ⊆ Λ) :
    (pureState Ω hΩ).mutualInfo hX hY =
      FiniteProduct.mutualInformation (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q)
        (WithLp.toLp 2 Ω) X Y := by
  have hent : ∀ {Z : Finset ↥(Λ : Set (ℤ × ℤ))} {Z' : Finset (ℤ × ℤ)}
      (hZZ : Z.map (Function.Embedding.subtype _) = Z') (hZ : Z' ⊆ Λ),
      (pureState Ω hΩ).regionEntropy hZ =
        FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) (WithLp.toLp 2 Ω) Z := by
    rintro Z _ rfl hZ
    exact regionalEntropy_eq_finiteProduct Λ q (WithLp.toLp 2 Ω) hΩ Z
  rw [FiniteProduct.mutualInformation, ← hent hXX hX, ← hent hYY hY,
    ← hent (by rw [Finset.map_union, hXX, hYY]) (Finset.union_subset hX hY)]
  rfl

/-- The square root of `(n^K)⁻¹` is `n^(-K/2)`. -/
private theorem sqrt_inv_pow_eq_rpow (n K : ℕ) :
    √(((n : ℝ) ^ K)⁻¹) = (n : ℝ) ^ (-(K : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg n),
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  ring_nf

/-- The square root of `n^(-2K)` is `(n^K)⁻¹`. -/
private theorem sqrt_rpow_neg_two_mul' (n K : ℕ) :
    √((n : ℝ) ^ (-(2 * K : ℝ))) = ((n : ℝ) ^ K)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n),
    show (2 * K : ℝ) = ((2 * K : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul',
    ← inv_pow, Real.sqrt_sq (by positivity)]

/-- A unit blank vector on a nonempty finite set. -/
private theorem norm_toLp_single_eq_one {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ‖WithLp.toLp 2 (fun x : α => if x = a then (1 : ℂ) else 0)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The final scale estimate: `4ε + √(14ε + 9ε²) ≤ 9 √ε` for `0 ≤ ε ≤ 1`. -/
private theorem unitary_error_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (3 * ε + ε) + √(2 * (3 * ε + ε) + 6 * ε + 9 * ε ^ 2) ≤ 9 * √ε := by
  have hs : ε ≤ √ε := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq : √(2 * (3 * ε + ε) + 6 * ε + 9 * ε ^ 2) ≤ 5 * √ε := by
    rw [show (5 : ℝ) * √ε = √(25 * ε) by
      rw [Real.sqrt_mul (by norm_num), show √(25 : ℝ) = 5 by
        rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- `p / (p + 1) > 1 - 10⁻⁶` forces `p ≥ 1`. -/
private theorem one_le_of_lt_div {p : ℕ} (hp : 1 - (1 / 1000000 : ℝ) < (p : ℝ) / (p + 1)) :
    1 ≤ p := by
  rcases Nat.eq_zero_or_pos p with rfl | h
  · norm_num at hp
  · exact h

/-- **Proposition 10.2 over `ℂ`, without its cut-clearance clause** (`prop:amplification`,
`09-amplification.tex` lines 261–296, proof at lines 298–576), for `q ≥ 1`, `J > 0`, `Δ > 0`
and `α = p / (p + 1) > 1 - 10⁻⁶`.  Fix `C₀ > 0` and an integer `M ≥ 1`.  Beyond a threshold
chosen before the domain, the Hamiltonian, the cut and the target, the collar hypotheses give an
integer radius `r ≤ C_M n^((1-ε)/α)` such that every part of `X = A ∩ T` has mutual information
at most `C_M n^(-M)` with every set avoiding `N_{2r}(S₀)`. -/
theorem amplificationOutput_complex (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) (hp : 1 - (1 / 1000000 : ℝ) < (p : ℝ) / (p + 1)) :
    AmplificationOutput ℂ q R J Δ p := by
  intro C₀ hC₀ M hM
  have : NeZero q := ⟨by omega⟩
  have hpw : 1 ≤ p := one_le_of_lt_div hp
  -- The exponent `α = p / (p + 1)` and the integer `K = 4 (M + 2)`.
  set α := kernelExponent p with hαdef
  have hα : 0 < α := kernelExponent_pos hpw
  set K := 4 * (M + 2) with hKdef
  have hK1 : 1 ≤ K := by omega
  -- Constants of the local-products lemma, the gap and the scales.
  obtain ⟨Ct, ct, hCt, hct, htr⟩ := exists_latticeConstraintWord_truncation hpw R hJ.le hΔ
  obtain ⟨Ao, vo, γ, hAo, hvo, hγ, hom⟩ :=
    exists_latticeConstraintWord_omission.{0} hpw R hJ.le hΔ
  obtain ⟨Cpc, cpc, -, -, hpos⟩ := exists_latticePositiveConstraints hpw R hJ.le hΔ
  set cs := positiveNormalization p (Δ / 2) J with hcsdef
  have hcs : 0 < cs := positiveNormalization_pos p _ J
  set g := Δ / cs with hgdef
  have hg : 0 < g := div_pos hΔ hcs
  set c := min ct γ with hcdef
  have hc : 0 < c := lt_min hct hγ
  set Cg := Ct + Ao with hCgdef
  have hCg : 0 ≤ Cg := add_nonneg hCt hAo
  obtain ⟨C', hC', Ng, hNg2, hgood⟩ :=
    exists_good_realization.{0} (C₀ := C₀) hg hvo.le hc hCg hC₀.le hα hK1
  obtain ⟨Nt, hNt1, hNt⟩ := exists_typicalProjectors_three_cuts (J := J) hq R hJ.le hΔ hC₀.le K
  obtain ⟨Crad, hCrad, hrad⟩ := exists_amplificationRadius_le (ε := (1 / 100000 : ℝ))
    hg hC'.le hC₀.le hα (by norm_num) (by norm_num) K
  set C₂ := C₀ * Real.log q with hC₂def
  have hC₂ : 0 ≤ C₂ := mul_nonneg hC₀.le (Real.log_nonneg (by exact_mod_cast hq))
  refine ⟨max Crad (8 * √9 * (1 + C₂)), max Ng Nt, ?_⟩
  intro Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n hn2 hnN hcard hXcut hYcut hScut hI
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- The vector in the Euclidean space, and the regions of Proposition 10.2 as cuts.
  set Ωe : EuclideanSpace ℂ (Reg (Qudits q) Λ) := WithLp.toLp 2 Ω with hΩedef
  have hΩe : ‖Ωe‖ = 1 := (norm_toLp_eq_one_iff Ω).2 hΩ
  set Xr := A ∩ T with hXrdef
  set Sr := A ∩ ambientDilation T (collarWidth n) with hSrdef
  have hXrΛ : Xr ⊆ Λ := Finset.inter_subset_left.trans hA
  have hSrΛ : Sr ⊆ Λ := Finset.inter_subset_left.trans hA
  have hXSr : Xr ⊆ Sr :=
    Finset.inter_subset_inter_left (subset_ambientDilation T (collarWidth n))
  set X : Finset ↥(Λ : Set (ℤ × ℤ)) := Xr.subtype (· ∈ (Λ : Set (ℤ × ℤ))) with hXdef
  set S₀ : Finset ↥(Λ : Set (ℤ × ℤ)) := Sr.subtype (· ∈ (Λ : Set (ℤ × ℤ))) with hS₀def
  set Y := S₀ \ X with hYdef
  have hXmap : X.map (Function.Embedding.subtype _) = Xr :=
    Finset.subtype_map_of_mem fun x hx => hXrΛ hx
  have hS₀map : S₀.map (Function.Embedding.subtype _) = Sr :=
    Finset.subtype_map_of_mem fun x hx => hSrΛ hx
  have hXS : X ⊆ S₀ := fun x hx => Finset.mem_subtype.2 (hXSr (Finset.mem_subtype.1 hx))
  have hXY : Disjoint X Y := Finset.disjoint_sdiff
  have hXYS : X ∪ Y = S₀ := Finset.union_sdiff_of_subset hXS
  have hYmap : Y.map (Function.Embedding.subtype _) = Sr \ Xr := by
    rw [hYdef, Finset.map_sdiff, hS₀map, hXmap]
  have hXYmap : (X ∪ Y).map (Function.Embedding.subtype _) = Sr := by rw [hXYS, hS₀map]
  have hcompl : ((X ∪ Y)ᶜ).map (Function.Embedding.subtype _) = Λ \ Sr := by
    rw [← hXYmap]
    ext x
    simp only [Finset.mem_map, Finset.mem_compl, Function.Embedding.coe_subtype,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun ⟨y', hy', h⟩ => hy (Subtype.ext h ▸ hy')⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, fun h => hx' ⟨_, h, rfl⟩, rfl⟩
  -- The scales `w = n^{3/5}`, `t_*` and `r`.
  set w : ℝ := (n : ℝ) ^ ((3 : ℝ) / 5) with hwdef
  have hw0 : 0 ≤ w := Real.rpow_nonneg hn0.le _
  set I := FiniteProduct.mutualInformation (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωe X
    (X ∪ Y)ᶜ with hIdef
  have hII : I ≤ C₀ * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by
    rw [hIdef, ← mutualInfo_pureState_eq_finiteProduct Ω hΩ hXmap
      hcompl hXrΛ Finset.sdiff_subset]
    exact hI
  have hI0 : 0 ≤ I := FiniteProduct.mutualInformation_nonneg _ Ωe hΩe _ _
    (disjoint_compl_right.mono_left Finset.subset_union_left)
  set t : ℝ := amplificationTime g I w K n with htdef
  have hKlog : 0 ≤ (K : ℝ) * Real.log n :=
    mul_nonneg (Nat.cast_nonneg K) (Real.log_nonneg (by exact_mod_cast hn1))
  have ht0 : 0 ≤ t :=
    mul_nonneg (div_nonneg (by norm_num) hg.le) (add_nonneg (add_nonneg hI0 hw0) hKlog)
  set r := amplificationRadius C' α t K n with hrdef
  set M₀ := Real.exp ((I + 3 * w) / 2) with hM₀def
  have hM₀ : 1 ≤ M₀ := Real.one_le_exp (by positivity)
  refine ⟨r, ?_, ?_⟩
  · exact (hrad n hn1 I hI0 hII).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  intro X' hX' Jset hJset
  -- The cuts of the part of the target and of the far set.
  set X'' : Finset ↥(Λ : Set (ℤ × ℤ)) := X'.subtype (· ∈ (Λ : Set (ℤ × ℤ))) with hX''def
  set J' : Finset ↥(Λ : Set (ℤ × ℤ)) := Jset.subtype (· ∈ (Λ : Set (ℤ × ℤ))) with hJ'def
  set N : Finset ↥(Λ : Set (ℤ × ℤ)) :=
    (graphNbhd Λ Sr (2 * r)).subtype (· ∈ (Λ : Set (ℤ × ℤ))) with hNdef
  have hX''X : X'' ⊆ X := fun x hx => Finset.mem_subtype.2 (hX' (Finset.mem_subtype.1 hx))
  have hJN : Disjoint J' N := by
    rw [Finset.disjoint_left]
    intro x hx hxN
    exact (Finset.mem_sdiff.1 (hJset (Finset.mem_subtype.1 hx))).2 (Finset.mem_subtype.1 hxN)
  have hS₀N : S₀ ⊆ N := by
    intro x hx
    refine Finset.mem_subtype.2 (mem_graphNbhd_iff_walk.2 ⟨x.2, x, Finset.mem_subtype.1 hx, x.2,
      SimpleGraph.Walk.nil, by simp⟩)
  rw [mutualInfo_pureState_eq_finiteProduct Ω hΩ
    (Finset.subtype_map_of_mem fun x hx => hXrΛ (hX' hx))
    (Finset.subtype_map_of_mem fun x hx => (Finset.mem_sdiff.1 (hJset hx)).1)]
  -- The typical projections and the restoring operator, with the ancillas as spectators.
  have hfail := hNt n ((le_max_right _ _).trans hnN) Λ Φ hΦ E₀ Ωe hΩe hE hgap X Y (X ∪ Y)
    (by rw [hXmap]; exact hXcut) (by rw [hYmap]; exact hYcut) (by rw [hXYmap]; exact hScut)
  let x₀ : RegionalConfiguration q X := fun _ => 0
  let blank : RegionalConfiguration q X → ℂ := fun x => if x = x₀ then 1 else 0
  have hblank : ‖WithLp.toLp 2 blank‖ = 1 := norm_toLp_single_eq_one x₀
  let U := restoringEigenbasis Ωe X
  obtain ⟨hU, hU'⟩ := restoringEigenbasis_unitary Ωe X
  let 𝒲 := restoringTransport Ωe X Y hXY
  let pX := (FiniteProduct.reducedPure_posSemidef (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωe
    X).isHermitian.eigenvalues
  let E := Entropy.typicalSet pX (FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q)
    Ωe X) w
  let Tq := typicalProjection Λ q Ωe Y w
  let Q := restoringCutProjection Ωe X Y hXY w
  let ψ := restoringVector Ωe X Y hXY
  let Rp := 𝒲 * Entropy.restoringGlobal (Z := RegionalConfiguration q (X ∪ Y)ᶜ) E pX blank
    blank Q Tq * 𝒲ᴴ
  let Bp := 𝒲 * Entropy.restoringColumnGlobal (Z := RegionalConfiguration q (X ∪ Y)ᶜ) E pX
    blank blank Q Tq * 𝒲ᴴ
  let φ := 𝒲 *ᵥ (Entropy.restoringCopy blank blank ψ).ofLp
  let η := 𝒲 *ᵥ (Entropy.restoringRestored pX ψ).ofLp
  let ξb : RegionalConfiguration q X × RegionalConfiguration q X → ℂ :=
    fun c => blank c.1 * (U *ᵥ blank) c.2
  obtain ⟨hφ1, hη1, hRn, hBn, hcol, hgr, hadj⟩ := restoringTransport_estimates Ωe hΩe X Y hXY w
    ((n : ℝ) ^ (-(2 * K : ℝ))) (hfail X (by simp)).2.2.2 (hfail Y (by simp)).2.2.2
    (hfail (X ∪ Y) (by simp)).2.2.2 blank blank blank hblank hblank hblank
  have hφ1 : ‖WithLp.toLp 2 φ‖ = 1 := hφ1
  have hη1 : ‖WithLp.toLp 2 η‖ = 1 := hη1
  have hRn : ‖Rp‖ ≤ M₀ := hRn
  have hBn : ‖Bp‖ ≤ M₀ := hBn
  have hcol : Rp *ᵥ φ = Bp *ᵥ fun c => Ω c.1 * ξb c.2 := hcol
  rw [sqrt_rpow_neg_two_mul'] at hadj
  -- The supports of `B₀` and `R₀`.
  obtain ⟨PB, AB, hPB, hBsum⟩ :=
    restoringTransport_restoringColumnGlobal_eq_sum Ωe X Y hXY E pX blank blank Q Tq
  have hBsum : Bp = ∑ i ∈ E ×ˢ Finset.univ, PB i ⊗ₖ AB i := hBsum
  have hBblocks : ∀ x y : RegionalConfiguration q X × RegionalConfiguration q X,
      IsSupportedOn hSrΛ (Matrix.of fun σ τ => Bp (σ, x) (τ, y)) := by
    intro x y
    rw [hBsum]
    exact (isSupportedOn_block_of_eq_sum _ _ hPB AB x y).mono hXYmap.le hSrΛ
  obtain ⟨PR, hPR, hRsum⟩ :=
    restoringTransport_restoringGlobal_eq_sum Ωe X Y hXY E pX blank blank Q Tq
  have hRsum : Rp = ∑ x ∈ E, PR x ⊗ₖ (Entropy.basisColumn x blank ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)) := hRsum
  -- Anchors and the exact positive constraints.
  let a : supports Λ R → ℤ × ℤ := fun Z => (mem_supports_iff.1 Z.2).2.1.choose
  have ha : ∀ Z : supports Λ R, a Z ∈ Z.1 := fun Z => (mem_supports_iff.1 Z.2).2.1.choose_spec
  let k := fun i : supports Λ R => positiveConstraint cs
    (centeredFilter p (Δ / 2) (hamiltonian Λ Φ) Ωe (extendId (subset_of_mem_supports i.2)
      (Φ i)))
  obtain ⟨-, hk, -⟩ := hpos Λ Φ hΦ a ha E₀ Ωe hΩe hE hgap
  have hk : ∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ωe = 0 := hk
  let Pr := fun i : supports Λ R => a i ∈ graphNbhd Λ Sr r
  let tt : ℝ≥0 := ⟨t, ht0⟩
  let μ := PoissonWord.measure (supports Λ R) tt
  -- The vector `ζ = R₀ φ`, its excited component and the blank pair `ξ`.
  let ζ : Reg (Qudits q) Λ × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ :=
    Rp *ᵥ φ
  let Pg := vecMulVec (WithLp.ofLp Ωe) (star (WithLp.ofLp Ωe))
  let I₂ := (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
    (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)
  let ξe : EuclideanSpace ℂ (Reg (Qudits q) Λ × (RegionalConfiguration q X ×
      RegionalConfiguration q X)) :=
    toEuclideanLin ((1 - Pg) ⊗ₖ I₂) (WithLp.toLp 2 ζ)
  have hζn : ‖WithLp.toLp 2 ζ‖ ≤ M₀ := by
    have h := Rp.l2_opNorm_mulVec (WithLp.toLp 2 φ)
    rw [hφ1, mul_one] at h
    exact h.trans hRn
  have hPg : IsStarProjection Pg :=
    Entropy.blankOuterProduct_isStarProjection _ (by simpa using hΩe)
  have hξen : ‖ξe‖ ≤ M₀ := by
    have h := ((1 - Pg) ⊗ₖ I₂).l2_opNorm_mulVec (WithLp.toLp 2 ζ)
    have h1 : ‖(1 - Pg) ⊗ₖ I₂‖ ≤ 1 :=
      (l2_opNorm_kronecker_one_le _).trans hPg.one_sub.norm_le
    calc ‖ξe‖ ≤ _ := h
      _ ≤ 1 * M₀ := mul_le_mul h1 hζn (norm_nonneg _) zero_le_one
      _ = M₀ := one_mul _
  have hξb : ‖WithLp.toLp 2 ξb‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron (WithLp.toLp 2 blank) (WithLp.toLp 2 (U *ᵥ blank))
    have hUb : ‖WithLp.toLp 2 (U *ᵥ blank)‖ = 1 := by
      rw [norm_toLp_mulVec_of_conjTranspose_mul_self hU', hblank]
    rw [hblank, hUb, mul_one] at h
    exact h
  -- The three random variables on one clock realization.
  let Xrv : PoissonWord.Word (supports Λ R) → ℝ := fun u =>
    ‖toEuclideanLin (contractionWord k u.1 u.2 ⊗ₖ I₂) ξe‖
  let Dl : List (supports Λ R) → Reg (Qudits q) Λ × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ := fun l =>
    ((l.reverse.map fun i => CFC.sqrt (1 - k i)).prod ⊗ₖ I₂) *ᵥ
        (Bp *ᵥ fun x => WithLp.ofLp Ωe x.1 * ξb x.2)
  let Yrv : PoissonWord.Word (supports Λ R) → ℝ := fun u =>
    ‖WithLp.toLp 2 (Dl (List.ofFn u.2) - Dl ((List.ofFn u.2).filter fun i => decide (Pr i)))‖
  let Dret : PoissonWord.Word (supports Λ R) →
      Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ := fun u =>
    contractionWord (fun i : {i // Pr i} => k i) (PoissonWord.partitionWords Pr u).1.1
      (PoissonWord.partitionWords Pr u).1.2
  let kr := fun i : {i // Pr i} => condExpect (graphNbhd_subset Λ {a i} r) (k i)
  let Lt : PoissonWord.Word (supports Λ R) →
      Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ := fun u =>
    contractionWord kr (PoissonWord.partitionWords Pr u).1.1
      (PoissonWord.partitionWords Pr u).1.2
  let Zrv : PoissonWord.Word (supports Λ R) → ℝ := fun u => M₀ * ‖Dret u - Lt u‖
  obtain ⟨hXint, hXle⟩ := latticeConstraintWord_excitedProjection_decay hpw R hJ.le hΔ Λ Φ hΦ
    E₀ Ωe hΩe hE hgap (WithLp.toLp 2 ζ) tt
  have hXint : Integrable (fun u => Xrv u ^ 2) μ := hXint
  have hXle : (∫ u, Xrv u ^ 2 ∂μ) ≤ Real.exp (-(Δ / cs) * t) * ‖ξe‖ ^ 2 := hXle
  obtain ⟨hYint, hYle⟩ := hom Λ Φ hΦ a ha E₀ Ωe hΩe hE hgap _ Sr hSrΛ Bp hBblocks ξb hξb r tt
  have hYint : Integrable Yrv μ := hYint
  have hYle : (∫ u, Yrv u ∂μ) ≤ Ao * t * Sr.card * ‖Bp‖ *
      Real.exp (vo * t - γ * (r : ℝ) ^ α) := hYle
  obtain ⟨hZint, hZle, hLt⟩ := htr Λ Φ hΦ a ha E₀ Ωe hΩe hE hgap Sr r tt
  have hZint : Integrable (fun u => ‖Dret u - Lt u‖) μ := hZint
  have hZle : (∫ u, ‖Dret u - Lt u‖ ∂μ) ≤ Ct * t * Sr.card * (1 + (r : ℝ)) ^ 2 *
      Real.exp (-(ct * (r : ℝ) ^ α)) := hZle
  have hLt : ∀ u, ‖Lt u‖ ≤ 1 ∧ IsSupportedOn (graphNbhd_subset Λ Sr (2 * r)) (Lt u) := hLt
  -- Markov's inequality and a union bound: a good realization.
  have hrα : 0 ≤ (r : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg r) α
  have hS0 : (0 : ℝ) ≤ Sr.card := Nat.cast_nonneg _
  have hM₀0 : 0 ≤ M₀ := (Real.exp_pos _).le
  obtain ⟨u0, hXu, hYu, hZu⟩ := hgood n ((le_max_left _ _).trans hnN) I w hI0 hw0 Sr.card
    hcard μ Xrv Yrv Zrv hXint (Filter.Eventually.of_forall fun u => norm_nonneg _) hYint
    (Filter.Eventually.of_forall fun u => mul_nonneg hM₀0 (norm_nonneg _))
    (hZint.const_mul M₀)
    (by
      have h1 : Real.exp (-(Δ / cs) * t) * ‖ξe‖ ^ 2 ≤ Real.exp (-(g * t)) * M₀ ^ 2 := by
        rw [neg_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξen 2)
          (Real.exp_pos _).le
      exact (hXle.trans h1).trans_eq (mul_comm _ _))
    (by
      have hCgt : 0 ≤ Cg * t * Sr.card := mul_nonneg (mul_nonneg hCg ht0) hS0
      have e1 : Real.exp (vo * t - γ * (r : ℝ) ^ α) ≤ Real.exp (vo * t - c * (r : ℝ) ^ α) :=
        Real.exp_le_exp.mpr
          (sub_le_sub_left (mul_le_mul_of_nonneg_right (min_le_right ct γ) hrα) _)
      have e2 : Ao * t * Sr.card * ‖Bp‖ ≤ Cg * t * Sr.card * M₀ :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hCt) ht0)
          hS0) hBn (norm_nonneg _) hCgt
      exact hYle.trans (mul_le_mul e2 e1 (Real.exp_pos _).le (mul_nonneg hCgt hM₀0)))
    (by
      rw [integral_const_mul]
      have hr2 : (0 : ℝ) ≤ (1 + (r : ℝ)) ^ 2 := sq_nonneg _
      have hCgt : 0 ≤ Cg * t * Sr.card * (1 + (r : ℝ)) ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg hCg ht0) hS0) hr2
      have e1 : Real.exp (-(ct * (r : ℝ) ^ α)) ≤ Real.exp (-(c * (r : ℝ) ^ α)) :=
        Real.exp_le_exp.mpr
          (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left ct γ) hrα))
      have e2 : Ct * t * Sr.card * (1 + (r : ℝ)) ^ 2 ≤ Cg * t * Sr.card * (1 + (r : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hAo) ht0) hS0) hr2
      have e3 := mul_le_mul_of_nonneg_left (hZle.trans (mul_le_mul e2 e1 (Real.exp_pos _).le
        hCgt)) hM₀0
      exact e3.trans_eq (by ring))
  let ε : ℝ := ((n : ℝ) ^ K)⁻¹
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hn1))
  -- The enlarged sites and the transported operators and vectors.
  let sp := ancillaSplit q X
  have hsubk (A B : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ) :
      (A - B) ⊗ₖ I₂ = A ⊗ₖ I₂ - B ⊗ₖ I₂ := by
    ext i j
    simp only [kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  let Dfull := contractionWord k u0.1 u0.2
  have hkle : ∀ i, k i ≤ 1 := fun i => (hk i).2.1
  have hkΩ : ∀ i, k i *ᵥ WithLp.ofLp Ωe = 0 := fun i => (hk i).2.2
  have hR₀supp : IsSupportedOn (Finset.subset_univ (N.disjSum (Finset.univ.disjSum ∅) :
      Finset (AncillaSites Λ X))) ((Rp.submatrix sp sp).submatrix univEquiv univEquiv) := by
    rw [hRsum]
    exact (isSupportedOn_sum_kronecker_submatrix_ancillaSplit E hPR _).mono
      (Finset.disjSum_mono (hXYS ▸ hS₀N) le_rfl) (Finset.subset_univ _)
  obtain ⟨U₁, hU₁supp, hU₁unit, hU₁err⟩ := exists_ancilla_unitary_of_good_realization hR₀supp
    (hLt u0).2.subtype_map (D := Dfull) (Dret := Dret u0) (g := (Pg ⊗ₖ I₂) *ᵥ ζ) (M₀ := M₀)
    (ε := ε) (a := 3 * ε + ε) hφ1 hη1 hζn
    (by
      rw [mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul,
        contractionWord_mul_vecMulVec_self k hkle hkΩ])
    hgr
    (by
      have hsub : Rp *ᵥ φ - (Pg ⊗ₖ I₂) *ᵥ ζ = ((1 - Pg) ⊗ₖ I₂) *ᵥ ζ := by
        rw [hsubk, sub_mulVec, one_kronecker_one, one_mulVec]
      rw [hsub]
      exact hXu)
    (by
      rw [hsubk, sub_mulVec, hcol]
      have h1 : Dfull = ((List.ofFn u0.2).reverse.map fun i => CFC.sqrt (1 - k i)).prod :=
        contractionWord_eq_prod_reverse k _ _
      have h2 : Dret u0 = (((List.ofFn u0.2).filter fun i => decide (Pr i)).reverse.map
          fun i => CFC.sqrt (1 - k i)).prod := contractionWord_partitionWords_fst Pr k u0
      rw [h1, h2]
      exact hYu)
    hZu
    (by
      have hfix : toEuclideanCLM (𝕜 := ℂ) (Dret u0)ᴴ Ωe = Ωe := by
        apply WithLp.ofLp_injective 2
        rw [ofLp_toEuclideanCLM]
        exact conjTranspose_contractionWord_mulVec_self (fun i : {i // Pr i} => k i)
          (fun i => hkle i) (fun i => hkΩ i) _ _
      have hLΩ := norm_truncated_adjoint_sub_le (L' := Lt u0) hfix hΩe.le hM₀ hZu
      have h := hadj (Lt u0)
      have hLΩ' : ‖WithLp.toLp 2 ((Lt u0)ᴴ *ᵥ WithLp.ofLp Ωe) - Ωe‖ ≤ ε := hLΩ
      linarith only [h, hLΩ'])
  -- The entropy comparison on the enlarged sites.
  have hδ : ‖WithLp.toLp 2 (U₁ *ᵥ (φ ∘ sp)) - WithLp.toLp 2 (η ∘ sp)‖ ≤
      9 * (n : ℝ) ^ (-(K : ℝ) / 2) := by
    rw [← sqrt_inv_pow_eq_rpow]
    exact hU₁err.trans (unitary_error_le hε0 hε1)
  have hdim : (X.card : ℝ) * Real.log q ≤ C₂ * (n : ℝ) ^ 2 := by
    have hXc : (X.card : ℝ) ≤ C₀ * (n : ℝ) ^ 2 := by
      rw [← Finset.card_map (Function.Embedding.subtype _), hXmap]
      exact (Nat.cast_le.mpr (Finset.card_le_card hXSr)).trans hcard
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    calc (X.card : ℝ) * Real.log q ≤ C₀ * (n : ℝ) ^ 2 * Real.log q :=
          mul_le_mul_of_nonneg_right hXc hlogq
      _ = C₂ * (n : ℝ) ^ 2 := by rw [hC₂def]; ring
  refine (mutualInformation_le_of_ancilla_unitary hΩe hXY (hXS.trans hS₀N) hJN hblank hblank
    hφ1 hη1 hU₁supp hU₁unit hn1 le_rfl hδ hdim X'' hX''X).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end OpenAI
