/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/AmplificationCutClearance.lean` and the declarations of
`TNLean/PEPS/AreaLaw/Amplification/RadiusScales.lean` (Apache 2.0).
Namespaces `TNLean.PEPS.AreaLaw` and `TNLean.PEPS.AreaLaw.Exponents` renamed to `OpenAI` and
`OpenAI.Exponents`.  Adaptations:
* RadiusScales: TNLean fixes `α = 10⁶ / (10⁶ + 1)` and names the radius exponent
  `radiusExponent : ℚ`; here `α` is any real with `1 - 10⁻⁶ < α` and the exponent is written
  out as `(1 - 10⁻⁵) / α`, the expression of `OpenAI.Amplification`, so no `radiusExponent`
  is defined.  `amplificationEpsilon` and `beta` are written as the reals `1 / 100000` and
  `1 - 2 / 1000000`, and `⌊n^(1-ε)⌋₊` as `OpenAI.collarWidth n`.  `radius_exponent_gaps`
  takes `α < 1`; the other declarations need only `1 - 10⁻⁶ < α`.  Added
  `radiusExponent_lt_beta`.
* `exists_threshold_graphNeighborhood_collar_subset` is stated for a general `p` with
  `1 - 10⁻⁶ < p / (p + 1)` (TNLean: `p = 10⁶`), in the frozen form of the last clause of
  `OpenAI.Amplification`: the clearance is `ENNReal.ofReal (L + n^β) < ambientEDist T Z_A`
  in place of TNLean's pointwise `L + n^β < ambientSupDistance t z`, regions are
  `Finset (ℤ × ℤ)` and `graphNeighborhood Λ (2r) S` is `OpenAI.graphNbhd Λ S (2 * r)`.
* `amplificationBound_of_radius_output` is renamed `amplification_of_amplificationOutput`; its
  hypothesis, TNLean's inline radius-and-output statement, is the definition
  `OpenAI.AmplificationOutput`, and its conclusion TNLean's `AmplificationBound` (over `ℂ`, at
  `p = 10⁶`) is `OpenAI.Amplification 𝕜 q R J Δ p` for every `RCLike 𝕜` and every `p` as above.
-/
import OpenAI.GraphNeighborhoodCutClearance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The cut-clearance clause of the amplification proposition

The last assertion of Proposition 10.2 says that the graph neighborhood `N_{2r}(S₀)` of the
collar `S₀ = A ∩ T_L` stays inside the cut `A` once the ambient target `T` is far from the cut
endpoints `Z_A`.  A walk of length at most `2r` from `S₀` that leaves `A` crosses the cut at an
endpoint within ambient distance `L + 2r` of `T`; with the explicit clearance
`L + 2r < dist_∞(T, Z_A)` this is `OpenAI.graphNeighborhood_subset_of_lt_ambientEDist`.  For
`α > 1 - 10⁻⁶` the radius exponent `(1 - ε) / α` is below `β = 1 - 2 · 10⁻⁶`, so the collar
width `L = ⌊n^{1-ε}⌋` plus twice any radius `r ≤ C n^{(1-ε)/α}` is `o(n^β)`, and the source
clearance `L + n^β` gives the explicit one at all large scales, uniformly in the domain, the
cut and the target.  Consequently the amplification proposition reduces to its radius and
information bounds.

## Main definitions

* `OpenAI.AmplificationOutput`: Proposition 10.2 without its cut-clearance clause.

## Main statements

* `OpenAI.Exponents.exists_collar_radius_threshold`: `L + 2r < η n^β` beyond a threshold
  depending only on `C` and `η`.
* `OpenAI.exists_threshold_graphNeighborhood_collar_subset`: the cut-clearance clause of
  Proposition 10.2 for every radius obeying the radius bound.
* `OpenAI.amplification_of_amplificationOutput`: the radius and output bounds of
  Proposition 10.2 imply `OpenAI.Amplification`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 10.2 (`prop:amplification`), `09-amplification.tex` lines 261–296,
  `eq:amplification-exponents`, `eq:amplification-radius`,
  `eq:amplification-cut-clearance`, and the last paragraph of its proof, lines 563–575.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter
open scoped Topology

namespace OpenAI.Exponents

/-- For `α > 1 - 10⁻⁶` the radius exponent `(1 - ε) / α` is below the separation exponent
`β = 1 - 2 · 10⁻⁶`.  Source: the last paragraph of the proof of Proposition 10.2. -/
theorem radiusExponent_lt_beta {α : ℝ} (hα : 1 - (1 / 1000000 : ℝ) < α) :
    (1 - (1 / 100000 : ℝ)) / α < 1 - (2 / 1000000 : ℝ) := by
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The parameters leave a strict gap between both collar exponents and the geometric
separation exponent.  The middle inequality needs `α < 1`, which holds for `α = p / (p + 1)`.
Source: the last paragraph of the proof of Proposition 10.2, `eq:amplification-radius`. -/
theorem radius_exponent_gaps {α : ℝ} (hα : 1 - (1 / 1000000 : ℝ) < α) (hα1 : α < 1) :
    0 < (1 - (1 / 100000 : ℝ)) / α ∧ 1 - (1 / 100000 : ℝ) < (1 - (1 / 100000 : ℝ)) / α ∧
      (1 - (1 / 100000 : ℝ)) / α < 1 - (2 / 1000000 : ℝ) := by
  have hα0 : 0 < α := by linarith
  refine ⟨div_pos (by norm_num) hα0, ?_, radiusExponent_lt_beta hα⟩
  rw [lt_div_iff₀ hα0]
  nlinarith

private theorem tendsto_powerRatio_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a / (n : ℝ) ^ b) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  simpa only [Function.comp_apply, neg_sub] using Real.rpow_sub hn' a b

/-- The sum of the collar scale and twice the radius scale is negligible relative to the
geometric separation scale.  Source: Proposition 10.2, `eq:amplification-radius`, and the last
paragraph of its proof. -/
theorem collar_radius_scale_tendsto_zero {α : ℝ} (hα : 1 - (1 / 1000000 : ℝ) < α) (C : ℝ) :
    Tendsto (fun n : ℕ ↦
      ((n : ℝ) ^ (1 - (1 / 100000 : ℝ)) +
        2 * C * (n : ℝ) ^ ((1 - (1 / 100000 : ℝ)) / α)) / (n : ℝ) ^ (1 - (2 / 1000000 : ℝ)))
      atTop (𝓝 0) := by
  have ha : 1 - (1 / 100000 : ℝ) < 1 - (2 / 1000000 : ℝ) := by norm_num
  simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
    (tendsto_powerRatio_zero ha).add
      ((tendsto_powerRatio_zero (radiusExponent_lt_beta hα)).const_mul (2 * C))

/-- One threshold controls the collar width and every radius with the given power bound.  The
threshold depends only on `C` and `η`.  Source: Proposition 10.2, `eq:amplification-radius`,
final paragraph of its proof. -/
theorem exists_collar_radius_threshold {α : ℝ} (hα : 1 - (1 / 1000000 : ℝ) < α)
    (C η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ r : ℕ,
      (r : ℝ) ≤ C * (n : ℝ) ^ ((1 - (1 / 100000 : ℝ)) / α) →
      (collarWidth n : ℝ) + 2 * r < η * (n : ℝ) ^ (1 - (2 / 1000000 : ℝ)) := by
  have he := (collar_radius_scale_tendsto_zero hα C).eventually_lt_const hη
  obtain ⟨N, hN⟩ := he.exists_forall_of_atTop
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn r hr
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ))
      ((le_max_right N 2).trans hn)
  have hscale := (div_lt_iff₀ (Real.rpow_pos_of_pos hn' (1 - (2 / 1000000 : ℝ)))).mp
    (hN n ((le_max_left N 2).trans hn))
  have hfloor := Nat.floor_le
    (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (1 / 100000 : ℝ)))
  rw [← collarWidth] at hfloor
  linarith only [hscale, hfloor, hr]

/-- The collar width plus twice any eventually admissible radius is of smaller order than the
separation scale.  Source: Proposition 10.2, `eq:amplification-radius`, final paragraph of its
proof. -/
theorem collar_add_radius_isLittleO {α : ℝ} (hα : 1 - (1 / 1000000 : ℝ) < α) (C : ℝ)
    (r : ℕ → ℕ)
    (hr : ∀ᶠ n : ℕ in atTop, (r n : ℝ) ≤ C * (n : ℝ) ^ ((1 - (1 / 100000 : ℝ)) / α)) :
    (fun n : ℕ ↦ (collarWidth n : ℝ) + 2 * r n)
      =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 - (2 / 1000000 : ℝ))) := by
  refine Asymptotics.IsLittleO.of_bound fun η hη ↦ ?_
  obtain ⟨N, _, hN⟩ := exists_collar_radius_threshold hα C η hη
  filter_upwards [eventually_ge_atTop N, hr] with n hn hrn
  have hnonneg : 0 ≤ (collarWidth n : ℝ) + 2 * r n := by positivity
  simpa only [Real.norm_of_nonneg hnonneg,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (2 / 1000000 : ℝ)))] using
    (hN n hn (r n) hrn).le

end OpenAI.Exponents

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder
open Matrix

/-- **The cut-clearance clause of Proposition 10.2.**  For every radius constant `C` there is a
threshold such that, at every scale `n` beyond it and for every radius `r ≤ C n^((1-ε)/α)`,
`α = p / (p + 1)`, the clearance `dist_∞(T, Z_A) > L + n^β` of
`eq:amplification-cut-clearance` gives `N_{2r}(S₀) ⊆ A`, where `L = ⌊n^(1-ε)⌋` and
`S₀ = A ∩ T_L`.  The threshold depends only on `C` and `p`, not on the domain, the cut or the
target.  Source: `09-amplification.tex`, lines 289–295 and 563–575. -/
theorem exists_threshold_graphNeighborhood_collar_subset {p : ℕ}
    (hp : 1 - (1 / 1000000 : ℝ) < (p : ℝ) / (p + 1)) (C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : ℕ,
      (r : ℝ) ≤ C * (n : ℝ) ^ ((1 - (1 / 100000 : ℝ)) / ((p : ℝ) / (p + 1))) →
      ∀ Λ A T : Finset (ℤ × ℤ),
        ENNReal.ofReal (collarWidth n + (n : ℝ) ^ (1 - (2 / 1000000 : ℝ)))
            < ambientEDist T (cutEndpoints Λ A) →
          graphNbhd Λ (A ∩ ambientDilation T (collarWidth n)) (2 * r) ⊆ A := by
  obtain ⟨N, -, hN⟩ := Exponents.exists_collar_radius_threshold hp C 1 one_pos
  refine ⟨N, fun n hn r hr Λ A T hclear ↦
    (graphNeighborhood_subset_of_lt_ambientEDist Λ T A _ (2 * r) ?_).trans
      Finset.inter_subset_left⟩
  refine lt_of_le_of_lt ?_ hclear
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsmall := hN n hn r hr
  push_cast
  linarith only [hsmall]

/-- Proposition 10.2 without its cut-clearance clause [OAI265, §10.2, eqs. (10.15)–(10.17)]:
the radius bound and the output bound `I_Ω(X' : J) ≤ C_M n^{-M}` of `OpenAI.Amplification`,
under the same hypotheses. -/
def AmplificationOutput (𝕜 : Type*) [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (p : ℕ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ M : ℕ, 1 ≤ M → ∃ C_M : ℝ, ∃ n₀ : ℕ,
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n : ℕ), 2 ≤ n → n₀ ≤ n →
      ((A ∩ ambientDilation T (collarWidth n)).card : ℝ) ≤ C₀ * n ^ 2 →
      ((edgeBoundary Λ (A ∩ T)).card : ℝ) ≤ C₀ * n →
      ((edgeBoundary Λ ((A ∩ ambientDilation T (collarWidth n)) \ (A ∩ T))).card : ℝ) ≤
        C₀ * n →
      ((edgeBoundary Λ (A ∩ ambientDilation T (collarWidth n))).card : ℝ) ≤ C₀ * n →
      (pureState Ω hΩ).mutualInfo (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ)
          (Finset.sdiff_subset :
            Λ \ (A ∩ ambientDilation T (collarWidth n)) ⊆ Λ) ≤
        C₀ * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) →
      ∃ r : ℕ, (r : ℝ) ≤ C_M * (n : ℝ) ^ ((1 - (1 / 100000 : ℝ)) / ((p : ℝ) / (p + 1))) ∧
        (∀ (X' : Finset (ℤ × ℤ)) (hX' : X' ⊆ A ∩ T) (J : Finset (ℤ × ℤ))
            (hJ : J ⊆ Λ \ graphNbhd Λ (A ∩ ambientDilation T (collarWidth n)) (2 * r)),
          (pureState Ω hΩ).mutualInfo (hX'.trans (Finset.inter_subset_left.trans hA))
              (hJ.trans Finset.sdiff_subset) ≤ C_M * ((n : ℝ) ^ M)⁻¹)

/-- **Reduction of Proposition 10.2 to its radius and output bounds.**  For `α = p / (p + 1)`
above `1 - 10⁻⁶`, the cut-clearance clause of `OpenAI.Amplification` follows from the radius
bound by `exists_threshold_graphNeighborhood_collar_subset`.  Source: `09-amplification.tex`,
lines 261–296 and 563–575. -/
theorem amplification_of_amplificationOutput {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ}
    {p : ℕ} (hp : 1 - (1 / 1000000 : ℝ) < (p : ℝ) / (p + 1))
    (h : AmplificationOutput 𝕜 q R J Δ p) : Amplification 𝕜 q R J Δ p := by
  intro C₀ hC₀ M hM
  obtain ⟨C, N₁, hC⟩ := h C₀ hC₀ M hM
  obtain ⟨N₂, hN₂⟩ := exists_threshold_graphNeighborhood_collar_subset hp C
  refine ⟨C, max N₁ N₂, fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n hn2 hn hcard hX hY hS hI ↦ ?_⟩
  obtain ⟨r, hr, hout⟩ :=
    hC Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n hn2 (le_of_max_le_left hn) hcard hX hY hS hI
  exact ⟨r, hr, hout, hN₂ n (le_of_max_le_right hn) r hr Λ A T⟩

end OpenAI
