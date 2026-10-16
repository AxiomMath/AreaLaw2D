/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/TypicalProjectors.lean` (Apache 2.0).  Namespace
`TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  TNLean's `Site Λ` is `↥(Λ : Set (ℤ × ℤ))`, its
`StateSpace Λ q` is `EuclideanSpace ℂ (Reg (Qudits q) Λ)`, the bundled `LocalHamiltonian` is an
interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ` (operator `hamiltonian Λ Φ`), and
`IsGappedGroundState` is `‖Ω‖ = 1`, the eigenvector equation and `OpenAI.HasGlobalGap`.  The
unordered `edgeBoundary Λ Y` of a cut `Y` of the sites is the ordered
`OpenAI.edgeBoundary Λ (Y.map (Function.Embedding.subtype _))`.  TNLean's
`reducedState Λ q Ω Y` and `regionalEntropy Λ q Ω Y` are the finite-product reduction
`FiniteProduct.reducedPure β Ω Y` and its entropy `FiniteProduct.entropy β Ω Y`, with
`β = fun _ ↦ Fin q`: this is the encoding in which the restoring operator of
`TNLean/PEPS/AreaLaw/Amplification/LatticeRestoring.lean` takes partial traces between the
cuts `X`, `Y`, `X ∪ Y` (there TNLean rewrites every regional state by
`reducedState_eq_finiteProduct`), and the encoding of `OpenAI.Scan.TargetTypicalWindow`.  The
lattice tail bound of `OpenAI.Scan.MarginalTailsBridge`, stated for `OpenAI.pureState`, is
transported by `OpenAI.surprisalTail_restrict_pureState_eq_finiteProduct`.  TNLean's
`trace_reducedState` (`ZeroBoundary.lean`) is `FiniteProduct.trace_reducedPure`, and that import
is dropped.  The finite-product reduction is `ℂ`-only, so the projections are over `ℂ`;
`trace_mul_spectralSelection` is stated over any `RCLike` field.
-/
import OpenAI.TailParameter
import OpenAI.Scan.TargetTypicalWindow
import OpenAI.TypicalDensity

/-!
# Typical projectors of the amplification proposition

The proof of the amplification proposition begins with three spectral projections
`P_X, T_Y, Q_{S_0}`, one for each of the cuts `X, Y, S_0`.  Each projects onto the positive
eigenvalues of the regional state of the original ground vector whose surprisal lies within
`w = n^(3/5)` of the regional entropy.  This module constructs them from Lemma 3.1
(`lem:tail`).  A cut with at most `C₀ n` crossing edges has tail parameter at most a constant
times `n`, so the failure probability `1 - tr(ρ P)` of its projection is at most
`C exp(-c n^(1/10))`.  For every fixed integer `K`, this is at most `δ = n^(-2K)` beyond a
threshold.

The constants and the threshold depend only on the local dimension, the range, the interaction
bound, the gap, `C₀` and `K`.  They are chosen before the domain, the Hamiltonian, the ground
vector and the cut.  Selected eigenvalues are positive, so no invertibility of a marginal is
assumed.

## Main definitions

* `OpenAI.typicalProjection`: the spectral projection of a regional state onto its typical
  positive spectrum.

## Main statements

* `OpenAI.typicalProjection_failure_le_surprisalTail`: the failure probability of a typical
  projection is at most the surprisal tail, together with its projection and eigenvalue-window
  properties.
* `OpenAI.exists_typicalProjection_failure_le_stretchedExp`: failure probability at most
  `C exp(-c n^(1/10))` at width `n^(3/5)`.
* `OpenAI.exists_typicalProjection_failure_le_inv_pow`: failure probability at most
  `n^(-2K)`, `eq:amplification-typical-error`.
* `OpenAI.exists_typicalProjectors_three_cuts`: the three projections of the proof, with their
  common error `δ = n^(-2K)`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026, proof of
  Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 304–322,
  `eq:amplification-typical-error`; Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69, and
  `eq:initial-local-tail-parameter`, lines 202–206.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix Filter Topology
open scoped ComplexOrder

namespace OpenAI

open Arealaw

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- The spectral projection of the regional state of `Ω` on `Y` onto the positive
eigenvalues whose surprisal lies within `w` of the regional entropy, such as
`P_X, T_Y, Q_{S_0}` in the proof of the amplification proposition.
Source: `09-amplification.tex`, lines 304–313. -/
noncomputable def typicalProjection (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (Y : Finset ↥(Λ : Set (ℤ × ℤ))) (w : ℝ) :
    Matrix (FiniteProduct.Configuration (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Y)
      (FiniteProduct.Configuration (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Y) ℂ :=
  (FiniteProduct.reducedPure_posSemidef (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω
      Y).isHermitian.spectralSelection
    (Entropy.typicalSet (FiniteProduct.reducedPure_posSemidef
        (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Y).isHermitian.eigenvalues
      (FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Y) w)

/-- The probability that a selected spectral projection succeeds is the mass of the
selected eigenvalues. -/
theorem trace_mul_spectralSelection {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {ρ : Matrix n n 𝕜} (hρ : ρ.IsHermitian) (E : Finset n) :
    (ρ * hρ.spectralSelection E).trace = (hρ.spectralRestrictionMass E : 𝕜) := by
  conv_lhs => arg 1; arg 1; rw [hρ.spectral_theorem]
  rw [IsHermitian.spectralSelection, ← map_mul, Unitary.conjStarAlgAut_apply,
    trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, diagonal_mul_diagonal,
    trace_diagonal, IsHermitian.spectralRestrictionMass]
  push_cast
  simp only [Function.comp_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Typical projection of one cut.** For a unit vector `Ω`, a region `Y` and a width
`w`, the typical projection is an orthogonal projection commuting with the regional
state.  Its selected eigenvalues are positive and lie in `[e^{-S-w}, e^{-S+w}]`, and its
failure probability `1 - tr(ρ_Y P)` is at most the surprisal tail at `w`.
Source: `09-amplification.tex`, lines 304–313 and 319–321. -/
theorem typicalProjection_failure_le_surprisalTail (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
    (hΩ : ‖Ω‖ = 1) (Y : Finset ↥(Λ : Set (ℤ × ℤ))) (w : ℝ) :
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q
    let p := (FiniteProduct.reducedPure_posSemidef β Ω Y).isHermitian.eigenvalues
    let S := FiniteProduct.entropy β Ω Y
    IsStarProjection (typicalProjection Λ q Ω Y w) ∧
      Commute (typicalProjection Λ q Ω Y w) (FiniteProduct.reducedPure β Ω Y) ∧
      (∀ i ∈ Entropy.typicalSet p S w,
        0 < p i ∧ Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) ∧
      1 - (FiniteProduct.reducedPure β Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤
        surprisalTail p S w := by
  intro β p S
  have hρ := FiniteProduct.reducedPure_posSemidef β Ω Y
  refine ⟨hρ.isHermitian.isStarProjection_spectralSelection _,
    hρ.isHermitian.commute_spectralSelection _,
    fun i hi ↦ ⟨(Entropy.mem_typicalSet.mp hi).1, Entropy.exp_le_of_mem_typicalSet hi⟩, ?_⟩
  have hsum : ∑ i, p i = 1 := by
    have h := hρ.isHermitian.trace_eq_sum_eigenvalues
    rw [FiniteProduct.trace_reducedPure β Ω hΩ Y] at h
    simpa [p] using (congrArg Complex.re h).symm
  have hm := Entropy.one_sub_surprisalTail_le_typicalMass hρ.eigenvalues_nonneg hsum S w
  rw [typicalProjection, trace_mul_spectralSelection, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re]
  change 1 - Entropy.typicalMass _ _ _ ≤ _
  linarith

/-- The constant `c = (32 √((1 + J/Δ) C (1 + C₀)))⁻¹` of the stretched-exponential
failure bound, with `C = tailParameterConstant q R`. -/
private noncomputable def failureRate (q R : ℕ) (J Δ C₀ : ℝ) : ℝ :=
  (32 * Real.sqrt ((1 + J / Δ) * (tailParameterConstant q R * (1 + C₀))))⁻¹

/-- **Failure probability of a typical projection.** There are constants `C, c > 0`,
depending only on `q, R, J, Δ` and `C₀`, such that for every scale `n ≥ 1`, every
gapped ground vector `Ω` of a finite-range Hamiltonian on a finite domain and every cut
`Y` with at most `C₀ n` crossing edges, the typical projection at width `n^(3/5)` fails
with probability at most `C exp(-c n^(1/10))`.
Source: `09-amplification.tex`, lines 304–317, from Lemma 3.1, `02-initial.tex`,
lines 64–69, and `eq:initial-local-tail-parameter`, lines 202–206. -/
theorem exists_typicalProjection_failure_le_stretchedExp (hq : 1 ≤ q) (R : ℕ)
    (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ → ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)),
        ‖Ω‖ = 1 → hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        ∀ Y : Finset ↥(Λ : Set (ℤ × ℤ)),
          ((edgeBoundary Λ (Y.map (Function.Embedding.subtype _))).card : ℝ) ≤ C₀ * n →
          1 - (FiniteProduct.reducedPure (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Y *
              typicalProjection Λ q Ω Y ((n : ℝ) ^ ((3 : ℝ) / 5))).trace.re ≤
            C * Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 10))) := by
  have hT := one_le_tailParameterConstant hq R
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  refine ⟨2 * Real.exp (Real.exp 1 / 2), failureRate q R J Δ C₀, by positivity,
    by unfold failureRate; positivity, ?_⟩
  intro n hn Λ Φ hΦ E₀ Ω hΩ heig hgap Y hY
  set w : ℝ := (n : ℝ) ^ ((3 : ℝ) / 5)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨-, -, -, hfail⟩ := typicalProjection_failure_le_surprisalTail Ω hΩ Y w
  have hΩ' := star_dotProduct_self_eq_one_of_norm_eq_one hΩ
  have htail := (hΦ.surprisalTail_reducedState_le hJ hΩ' hΔ heig hgap
    (map_embeddingSubtype_subset (T := Λ) Y) w).trans (min_le_right _ _)
  rw [surprisalTail_restrict_pureState_eq_finiteProduct Ω hΩ' Y w] at htail
  refine hfail.trans (htail.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  rw [Real.exp_le_exp, neg_le_neg_iff]
  -- the tail parameter is at most `C (1 + C₀) n`
  set B := latticeCutLogBudget Λ q R (Y.map (Function.Embedding.subtype _))
  have hB1 : 1 ≤ B := one_le_latticeCutLogBudget _ _ _ _
  have hBn : B ≤ tailParameterConstant q R * (1 + C₀) * n := by
    refine (cutLogBudget_le_edgeBoundary hq R _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith
  set D := Real.sqrt ((1 + J / Δ) * (tailParameterConstant q R * (1 + C₀)))
  have hD : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hsqrt : Real.sqrt ((1 + J / Δ) * B) ≤ D * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt
      ((mul_le_mul_of_nonneg_left hBn (by positivity)).trans_eq (by ring))
  have hpow : (n : ℝ) ^ ((1 : ℝ) / 10) * (n : ℝ) ^ ((1 : ℝ) / 2) = w := by
    rw [← Real.rpow_add hn0]; norm_num [w]
  have hpos : 0 < Real.sqrt ((1 + J / Δ) * B) := Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ (by positivity), failureRate, ← hpow]
  calc (32 * D)⁻¹ * (n : ℝ) ^ ((1 : ℝ) / 10) * (32 * Real.sqrt ((1 + J / Δ) * B))
      ≤ (32 * D)⁻¹ * (n : ℝ) ^ ((1 : ℝ) / 10) * (32 * (D * (n : ℝ) ^ ((1 : ℝ) / 2))) := by
        gcongr
    _ = (n : ℝ) ^ ((1 : ℝ) / 10) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        field_simp

/-- A stretched exponential `C exp(-c n^(1/10))` is eventually at most `n^(-s)`. -/
private theorem eventually_stretchedExp_le_rpow_neg {C c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 10))) ≤ (n : ℝ) ^ (-s) := by
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * s) c hc).comp hx
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 * s) * Real.exp (-c * (n : ℝ) ^ ((1 : ℝ) / 10)) ≤
        (max C 1)⁻¹ :=
    hlim.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : ((n : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 * s) = (n : ℝ) ^ s := by
    rw [← Real.rpow_mul hn0.le]; ring_nf
  rw [hpow, neg_mul] at hn
  have hs : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hn0 s
  have hC : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set e := Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 10)))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hone : max C 1 * ((n : ℝ) ^ s * e) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hn hC.le).trans_eq (mul_inv_cancel₀ hC.ne')
  have hCe : C * ((n : ℝ) ^ s * e) ≤ max C 1 * ((n : ℝ) ^ s * e) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hs.le he)
  rw [Real.rpow_neg hn0.le, ← one_div, le_div_iff₀ hs]
  nlinarith

/-- **Typical error of one cut, `eq:amplification-typical-error`.** For every integer
`K`, there is a threshold, depending only on `q, R, J, Δ, C₀` and `K`, beyond which the
typical projection at width `n^(3/5)` of every cut with at most `C₀ n` crossing edges
fails with probability at most `δ = n^(-2K)`.
Source: `09-amplification.tex`, lines 304–318, `eq:amplification-typical-error`. -/
theorem exists_typicalProjection_failure_le_inv_pow (hq : 1 ≤ q) (R : ℕ)
    (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ), N ≤ n → ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ → ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)),
        ‖Ω‖ = 1 → hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        ∀ Y : Finset ↥(Λ : Set (ℤ × ℤ)),
          ((edgeBoundary Λ (Y.map (Function.Embedding.subtype _))).card : ℝ) ≤ C₀ * n →
          1 - (FiniteProduct.reducedPure (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Y *
              typicalProjection Λ q Ω Y ((n : ℝ) ^ ((3 : ℝ) / 5))).trace.re ≤
            (n : ℝ) ^ (-(2 * K : ℝ)) := by
  obtain ⟨C, c, -, hc, hfail⟩ :=
    exists_typicalProjection_failure_le_stretchedExp (J := J) hq R hJ hΔ hC₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((eventually_stretchedExp_le_rpow_neg (C := C) hc (2 * K)).and (eventually_ge_atTop 1))
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro n hn Λ Φ hΦ E₀ Ω hΩ heig hgap Y hY
  obtain ⟨hle, hn1⟩ := hN n ((le_max_left _ _).trans hn)
  exact (hfail n hn1 Λ Φ hΦ E₀ Ω hΩ heig hgap Y hY).trans hle

/-- **The three typical projectors of the amplification proposition.** For every
integer `K`, beyond a threshold depending only on `q, R, J, Δ, C₀` and `K`, the
following holds for every gapped ground vector `Ω` of a finite-range Hamiltonian on a
finite domain and every three cuts `X, Y, S₀` with at most `C₀ n` crossing edges each.
The typical projections `P_X, T_Y, Q_{S₀}` at width `w = n^(3/5)` are orthogonal
projections commuting with their regional states, their selected eigenvalues are
positive and lie within `e^{±w}` of `e^{-S}`, and each fails with probability at most
`δ = n^(-2K)`.
Source: `09-amplification.tex`, lines 304–322, `eq:amplification-typical-error`. -/
theorem exists_typicalProjectors_three_cuts (hq : 1 ≤ q) (R : ℕ)
    (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ), N ≤ n → ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ → ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)),
        ‖Ω‖ = 1 → hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        ∀ X Y S₀ : Finset ↥(Λ : Set (ℤ × ℤ)),
          ((edgeBoundary Λ (X.map (Function.Embedding.subtype _))).card : ℝ) ≤ C₀ * n →
          ((edgeBoundary Λ (Y.map (Function.Embedding.subtype _))).card : ℝ) ≤ C₀ * n →
          ((edgeBoundary Λ (S₀.map (Function.Embedding.subtype _))).card : ℝ) ≤ C₀ * n →
          ∀ Z ∈ ({X, Y, S₀} : Finset (Finset ↥(Λ : Set (ℤ × ℤ)))),
            let w := (n : ℝ) ^ ((3 : ℝ) / 5)
            let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q
            let p := (FiniteProduct.reducedPure_posSemidef β Ω Z).isHermitian.eigenvalues
            let S := FiniteProduct.entropy β Ω Z
            IsStarProjection (typicalProjection Λ q Ω Z w) ∧
              Commute (typicalProjection Λ q Ω Z w) (FiniteProduct.reducedPure β Ω Z) ∧
              (∀ i ∈ Entropy.typicalSet p S w,
                0 < p i ∧ Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) ∧
              1 - (FiniteProduct.reducedPure β Ω Z * typicalProjection Λ q Ω Z w).trace.re ≤
                (n : ℝ) ^ (-(2 * K : ℝ)) := by
  classical
  obtain ⟨N, hN1, hN⟩ := exists_typicalProjection_failure_le_inv_pow (J := J) hq R hJ hΔ hC₀ K
  refine ⟨N, hN1, ?_⟩
  intro n hn Λ Φ hΦ E₀ Ω hΩ heig hgap X Y S₀ hX hY hS Z hZ
  have hZb : ((edgeBoundary Λ (Z.map (Function.Embedding.subtype _))).card : ℝ) ≤ C₀ * n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl | rfl <;> assumption
  obtain ⟨hproj, hcomm, hwin, -⟩ :=
    typicalProjection_failure_le_surprisalTail Ω hΩ Z ((n : ℝ) ^ ((3 : ℝ) / 5))
  exact ⟨hproj, hcomm, hwin, hN n hn Λ Φ hΦ E₀ Ω hΩ heig hgap Z hZb⟩

end OpenAI
