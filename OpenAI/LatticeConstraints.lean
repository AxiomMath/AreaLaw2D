/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 576d1624411e36a16cfc84aba9883f91416bcd32,
`TNLean/PEPS/AreaLaw/LatticeConstraints.lean` (Apache 2.0). Namespace `TNLean.PEPS.AreaLaw`
renamed to `OpenAI`. Adapted to this project's encodings: TNLean's bundled
`LocalHamiltonian Λ q R J` is an interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ`, its
operator `hamiltonian Λ Φ` and its term `h.term X` being `extendId _ (Φ X)`; the anchors
`a : AdmissibleSupport Λ R → Site Λ` are maps `supports Λ R → ℤ × ℤ` with `a X ∈ X`, and the
truncation set, cuts and supports are finite subsets of `ℤ²`; `IsGappedGroundState Λ q H E₀ Ω Δ`
is `‖Ω‖ = 1`, `H *ᵥ ofLp Ω = E₀ • ofLp Ω` and `OpenAI.HasGlobalGap H (ofLp Ω) E₀ Δ`
(`OpenAI.normalized_eigen_hasGlobalGap_iff_euclidean`); the graph-ball site expectation
`siteExpectation q (graphBall (domainGraph Λ) x l)` is `OpenAI.condExpect` on
`OpenAI.graphNbhd Λ {x} l`; `supportedOperators q {x | Reachable (a i) x}` is
`OpenAI.IsSupportedOn` on `OpenAI.domainComponent Λ (a i)`; the graph `cutBudget`,
`crossingLabels`, `designatedSupport` and `truncatedConstraint` are the square-lattice
`OpenAI.cutBudget`, `OpenAI.crossingLabels`, `OpenAI.designatedSupport` and
`OpenAI.truncatedConstraint`; the unordered `edgeBoundary Λ` is the ordered
`OpenAI.edgeBoundary Λ`, of the same cardinality. `Matrix.traceDistance ρ σ` is written
`(ρ - σ).traceNorm / 2`. The anchor multiplicity is the box count `2 ^ (2R + 1)²` of
`OpenAI.card_anchor_fiber_le` rather than the diamond count. Only Proposition 4.3, the first
part of Proposition 4.5 and its crossing and cut-budget parts are ported; Lemma 4.4
(`exists_latticeQuasilocalRoots`, stated with TNLean's `LocalRootChannels`) and the uniqueness
form `exists_latticeFiniteSetTruncation_eigenspace_eq_span` are omitted. The identity
`cutBudget_eq_cutLogBudget` and the complement invariance `cutBudget_compl` (here
`cutBudget_sdiff`) of `TNLean/PEPS/AreaLaw/CrossingBudget.lean`, which `OpenAI.CrossingBudget`
does not carry, are added here.
-/
import OpenAI.CrossingBudget
import OpenAI.CutTerms
import OpenAI.PositiveConstraints

/-!
# Positive constraints and truncation on an induced lattice domain

Proposition 4.3 and Proposition 4.5 of the area-law manuscript, stated for the model of
Theorem 1.1: an arbitrary finite domain `Λ ⊂ ℤ²` with its induced nearest-neighbour graph, an
admissible interaction of range `R` and strength `J ≥ 0`, an anchor `aᵢ ∈ Xᵢ` for every
support, and a gapped ground vector `Ω` of `H` with gap `Δ`. Every constant is chosen before
the local dimension, the domain, the interaction, the anchors and the ground vector: those of
Proposition 4.3 depend only on `p, R, J, Δ`, the constant `C₁` of Proposition 4.5 only on
`R, J, Δ, C₀`, and the crossing constant only on `q, R`.

## Main statements

* `OpenAI.exists_latticePositiveConstraints`: Proposition 4.3.
* `OpenAI.exists_latticeFiniteSetTruncation`: Proposition 4.5, truncation and ground-state part.
* `OpenAI.exists_latticeCrossingBudget`, `OpenAI.exists_latticeCutBudget_le_log`:
  Proposition 4.5, crossing count and cut budget.

## Implementation notes

The case `J = 0` is not covered by the Lieb–Robinson estimate of
`OpenAI.LiebRobinson.norm_heisenberg_sub_condExpect_graphNbhd_le`; there every term vanishes, so
the localization hypothesis of the spectral-filter tail holds trivially. The velocity is taken
one larger than the square-lattice velocity, which is positive for every `J ≥ 0`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`) and Proposition 4.5 (`prop:truncation`), section file
  `03-quasilocal.tex`, lines 220–534.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix SpectralFilter

/-! ## The cut budget as a marginal-tail budget -/

section CutBudget

variable {κ : Type*} [Fintype κ]

/-- The geometric cut budget is exactly the designated-support budget of the marginal-tail
bound (Lemma 3.1, `02-initial.tex`, lines 47–55). -/
theorem cutBudget_eq_cutLogBudget (q : ℕ) (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : κ → ℤ × ℤ)
    (X : Finset (ℤ × ℤ)) :
    cutBudget q Λ S₀ r₀ a X =
      cutLogBudget (crossingTerms (fun i => designatedSupport Λ S₀ r₀ (a i)) X)
        (fun i => Fintype.card (Reg (Qudits q) (designatedSupport Λ S₀ r₀ (a i)))) := by
  classical
  have hcross : crossingLabels Λ S₀ r₀ a X =
      crossingTerms (fun i => designatedSupport Λ S₀ r₀ (a i)) X := by
    ext i
    simp only [crossingLabels, crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.Nonempty, Finset.mem_inter, Finset.mem_sdiff]
  simp only [cutBudget, cutLogBudget, hcross, Reg, Qudits, Fintype.card_pi, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Fintype.card_coe, Nat.cast_pow]

/-- The cut budget is invariant under exchanging the two sides of a cut of `Λ`. -/
@[simp] theorem cutBudget_sdiff (q : ℕ) (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : κ → ℤ × ℤ)
    (X : Finset (ℤ × ℤ)) :
    cutBudget q Λ S₀ r₀ a (Λ \ X) = cutBudget q Λ S₀ r₀ a X := by
  classical
  have hcross : crossingLabels Λ S₀ r₀ a (Λ \ X) = crossingLabels Λ S₀ r₀ a X := by
    ext i
    have hD := designatedSupport_subset Λ S₀ r₀ (a i)
    simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨x, hx, -, hxX⟩, y, hy, hyX⟩
      exact ⟨⟨y, hy, by_contra fun h => hyX ⟨hD hy, h⟩⟩, x, hx, hxX⟩
    · rintro ⟨⟨x, hx, hxX⟩, y, hy, hyX⟩
      exact ⟨⟨y, hy, hD hy, hyX⟩, x, hx, fun h => h.2 hxX⟩
  simp only [cutBudget, hcross]

end CutBudget

/-! ## Proposition 4.3 -/

/-- **Positive replacement of the Hamiltonian on a lattice domain** (Proposition 4.3,
`prop:positive`, `03-quasilocal.tex`, lines 220–246). For `p ≥ 1`, `R`, `J ≥ 0` and `Δ > 0`
there are `C ≥ 0`, `c > 0` such that for every `q ≥ 1`, every finite domain `Λ`, every
admissible interaction of range `R` and strength `J`, every choice of anchors `aᵢ ∈ Xᵢ`, and
every gapped ground vector `Ω` of `H` with gap `Δ`: with `δ = Δ / 2`, `c_* > 0` and
`kᵢ = |Mᵢ| / c_*`, one has `0 ≤ kᵢ ≤ I`, `kᵢ Ω = 0`,
`∑ᵢ kᵢ ≥ c_*⁻¹ (H - E₀ I) ≥ (Δ / c_*) (I - |Ω⟩⟨Ω|)` (`eq:quasilocal-positive`); the ball
expectations `k_{i,l} = E_{N_l(aᵢ)}(kᵢ)` lie in `[0, I]` with
`‖kᵢ - k_{i,l}‖ ≤ C e^{-c l^α}`, `α = p / (p + 1)` (`eq:quasilocal-positive-tail`); and `kᵢ`
acts on the connected component of `aᵢ`. -/
theorem exists_latticePositiveConstraints {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ →
        ∀ (a : supports Λ R → ℤ × ℤ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
          hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
          HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        let cs := positiveNormalization p (Δ / 2) J
        let k := fun i : supports Λ R => positiveConstraint cs
          (centeredFilter p (Δ / 2) (hamiltonian Λ Φ) Ω (extendId (subset_of_mem_supports i.2)
            (Φ i)))
        0 < cs ∧
        (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) ∧
        cs⁻¹ • (hamiltonian Λ Φ - (E₀ : ℂ) • 1) ≤ ∑ i, k i ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          cs⁻¹ • (hamiltonian Λ Φ - (E₀ : ℂ) • 1) ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          ∑ i, k i ∧
        (∀ i (l : ℕ), 0 ≤ condExpect (graphNbhd_subset Λ {a i} l) (k i) ∧
          condExpect (graphNbhd_subset Λ {a i} l) (k i) ≤ 1 ∧
          ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
            C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))) ∧
        (∀ i, IsSupportedOn (domainComponent_subset Λ (a i)) (k i)) := by
  have hv : 0 < LiebRobinson.localizationVelocity R J + 1 := by
    have : 0 ≤ LiebRobinson.localizationVelocity R J := by
      unfold LiebRobinson.localizationVelocity
      positivity
    linarith
  obtain ⟨C, c, hC, hc, htail⟩ := exists_norm_positiveConstraint_sub_map_le hp
    (C := LiebRobinson.localizationPrefactor R) (c := 1) hΔ hJ
    (LiebRobinson.localizationPrefactor_nonneg R) hv one_pos
  refine ⟨C, c, hC, hc, ?_⟩
  intro q _ Λ Φ hΦ a ha E₀ Ω hΩ heig hgap cs k
  classical
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let term : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun X => extendId (subset_of_mem_supports X.2) (Φ X)
  let anchor : Finset (ℤ × ℤ) → ℤ × ℤ := fun Y =>
    if hY : Y ∈ supports Λ R then a ⟨Y, hY⟩ else (0, 0)
  have hanchor : ∀ Y ∈ supports Λ R, anchor Y ∈ Y := fun Y hY => by
    simpa only [anchor, dif_pos hY] using ha ⟨Y, hY⟩
  have hai : ∀ i : supports Λ R, anchor i.1 = a i := fun i => by
    simp only [anchor, dif_pos i.2]
  have hspectral := SpectralFilter.positive_replacement (E₀ := E₀) (J := J) hp hΔ hΩ heig
    (Matrix.le_iff.mp hgap) term (fun X => hΦ.isHermitian_extendId X)
    (fun X => hΦ.norm_extendId_le X) hΦ.hamiltonian_eq_sum_supports.symm
  refine ⟨positiveNormalization_pos p _ J, hspectral.1, hspectral.2.1, hspectral.2.2,
    hspectral.2.2.trans hspectral.2.1, fun i l => ?_, fun i => ?_⟩
  · let hN := graphNbhd_subset Λ {a i} l
    have hk := hspectral.1 i
    refine ⟨condExpect_nonneg hN hk.1, condExpect_le_one hN hk.2.1, ?_⟩
    have hloc : ∀ t : ℝ,
        ‖hermitianUnitaryPath (hamiltonian Λ Φ) t * term i *
            hermitianUnitaryPath (hamiltonian Λ Φ) (-t) -
          condExpectₗ hN (hermitianUnitaryPath (hamiltonian Λ Φ) t * term i *
            hermitianUnitaryPath (hamiltonian Λ Φ) (-t))‖ ≤
        ‖term i‖ * min 2 (LiebRobinson.localizationPrefactor R *
          Real.exp ((LiebRobinson.localizationVelocity R J + 1) * |t| - 1 * (l : ℝ))) := by
      intro t
      rcases hJ.eq_or_lt with hJ0 | hJpos
      · have h0 : term i = 0 := norm_le_zero_iff.mp (hJ0 ▸ hΦ.norm_extendId_le i)
        simp only [h0, mul_zero, zero_mul, map_zero, sub_zero, norm_zero, le_refl]
      · have hlr := LiebRobinson.norm_heisenberg_sub_condExpect_graphNbhd_le
          hq hJpos hΦ anchor hanchor i l t
        rw [hai] at hlr
        refine (by simpa only [term, condExpectₗ_apply] using hlr : _ ≤ _).trans ?_
        refine mul_le_mul_of_nonneg_left (min_le_min_left _ ?_) (norm_nonneg _)
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (LiebRobinson.localizationPrefactor_nonneg R)
        nlinarith [abs_nonneg t]
    have hraw := htail (n := Reg (Qudits q) Λ) (H := hamiltonian Λ Φ) (Ω := Ω) (h := term i)
      hΦ.isHermitian_hamiltonian hΩ (hΦ.isHermitian_extendId i) (hΦ.norm_extendId_le i)
      (condExpectₗ hN) (norm_condExpect_le hN) (condExpect_one hN)
      (fun Y hY => isHermitian_condExpect hN hY)
      (condExpect_cfcAbs_condExpect hN
        (centeredFilter p (Δ / 2) (hamiltonian Λ Φ) Ω (term i)))
      (show 0 ≤ (l : ℝ) by positivity) hloc
    simpa only [condExpectₗ_apply] using hraw
  · have hs := positiveConstraint_isSupportedOn_domainComponent hp (half_pos hΔ) hq hΦ anchor
      hanchor Ω cs i
    rw [hai] at hs
    exact hs

/-! ## Proposition 4.5 -/

/-- **Truncation near a finite set on a lattice domain** (Proposition 4.5, `prop:truncation`,
first part, `03-quasilocal.tex`, lines 405–433 and 457–505). Take `p = 1` in
`exists_latticePositiveConstraints`, so `α = 1/2`, and fix `R`, `J ≥ 0`, `Δ > 0`, `C₀ ≥ 0`.
There is `C₁ > 0`, depending only on `R, J, Δ, C₀`, such that for every lattice instance,
every real `n ≥ 2` and every `S₀` with `|S₀| ≤ C₀ n²`, with `r₀ = ⌈C₁ (log n)²⌉`,
`g = Δ / c_*` and `ε_n = min {n^{-1000}, g/4}`: each truncated constraint acts on its
designated support (`eq:quasilocal-variable-radius`) and is a positive contraction,
`‖H' - H_F‖ ≤ ε_n` for the truncated sum `H'` (`eq:quasilocal-truncation-error`), and `H'` has
a unit ground vector `Ω₀` with ground energy in `[0, ε_n]`, gap at least `g/2`,
`‖Ω₀ - e^{iθ} Ω‖ ≤ 2 √(ε_n / g)` for some phase and trace distance at most `√(2 ε_n / g)` from
`Ω` (`eq:quasilocal-ground-distance`). The source assumes `S₀` nonempty; the statement holds
without that assumption. -/
theorem exists_latticeFiniteSetTruncation (R : ℕ) {J Δ C₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC₀ : 0 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ →
        ∀ (a : supports Λ R → ℤ × ℤ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
          hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
          HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset (ℤ × ℤ), (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
        let cs := positiveNormalization 1 (Δ / 2) J
        let g := Δ / cs
        let k := fun i : supports Λ R => positiveConstraint cs
          (centeredFilter 1 (Δ / 2) (hamiltonian Λ Φ) Ω (extendId (subset_of_mem_supports i.2)
            (Φ i)))
        let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
        let ε := min (n ^ (-1000 : ℝ)) (g / 4)
        let Ht := ∑ i, truncatedConstraint q Λ S₀ r₀ (a i) (k i)
        (∀ i, IsSupportedOn (designatedSupport_subset Λ S₀ r₀ (a i))
          (truncatedConstraint q Λ S₀ r₀ (a i) (k i))) ∧
        (∀ i, 0 ≤ truncatedConstraint q Λ S₀ r₀ (a i) (k i) ∧
          truncatedConstraint q Λ S₀ r₀ (a i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
          HasGlobalGap Ht (WithLp.ofLp Ω₀) e (g / 2) ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          (vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)) -
              vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ≤
            Real.sqrt (2 * ε / g) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints le_rfl R hJ hΔ
  obtain ⟨C₁, hC₁, htr⟩ := exists_finiteSetTruncation (C := C) (c := c)
    (g := Δ / positiveNormalization 1 (Δ / 2) J) (μ := ((2 ^ (2 * R + 1) ^ 2 : ℕ) : ℝ))
    (Kb := 4) (C₀ := C₀) hC hc (div_pos hΔ (positiveNormalization_pos 1 _ J))
    (Nat.cast_nonneg _) (by norm_num) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro q _ Λ Φ hΦ a ha E₀ Ω hΩ heig hgap n hn S₀ hS₀ cs g k r₀ ε Ht
  obtain ⟨-, hk, -, -, hgapk, htail, hsupp⟩ := hpos Λ Φ hΦ a ha E₀ Ω hΩ heig hgap
  have htail' : ∀ i (l : ℕ), ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ))) := by
    intro i l
    have ht := (htail i l).2.2
    norm_num only [kernelExponent, Nat.cast_one, one_add_one_eq_two] at ht
    exact ht
  obtain ⟨hIcc, herr, e, Ω₀, hΩ₀, hHΩ₀, he₀, heε, hgap₀, hθ, htd⟩ :=
    htr Λ a k Ω hΩ hk (Matrix.le_iff.mp hgapk) htail' (card_graphNbhd_singleton_le_four Λ)
      (fun x => by exact_mod_cast card_anchor_fiber_le Λ R a ha x) n hn S₀ hS₀
  exact ⟨fun i => truncatedConstraint_isSupportedOn Λ S₀ r₀ (a i) (hsupp i), hIcc, herr, e, Ω₀,
    hΩ₀, hHΩ₀, he₀, heε, Matrix.le_iff.mpr hgap₀, hθ, htd⟩

/-- **Crossing count and cut budget on a lattice domain** (Proposition 4.5, `prop:truncation`,
`eq:quasilocal-crossing-count` and `eq:quasilocal-cut-budget`, `03-quasilocal.tex`,
lines 434–451 and 505–518). For `q ≥ 1` and `R` there is `C ≥ 0`, depending only on `q` and
`R`, such that for every domain, every choice of anchors, every `S₀`, every `r₀` and every
`X ⊆ S₀`, with `b_X = |∂_Λ X|`: every designated support meeting both `X` and its complement
is the ball of radius `r₀` about its anchor, `|𝒞_X| ≤ C b_X (r₀ + 1)²`,
`log dᵢ ≤ C (r₀ + 1)²` for `i ∈ 𝒞_X`, and `ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶`. -/
theorem exists_latticeCrossingBudget {q : ℕ} (hq : 1 ≤ q) (R : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (a : supports Λ R → ℤ × ℤ), (∀ X, a X ∈ X.1) →
      ∀ (S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (X : Finset (ℤ × ℤ)), X ⊆ S₀ →
        (∀ i ∈ crossingLabels Λ S₀ r₀ a X,
          designatedSupport Λ S₀ r₀ (a i) = graphNbhd Λ {a i} r₀) ∧
        ((crossingLabels Λ S₀ r₀ a X).card : ℝ) ≤
          C * (edgeBoundary Λ X).card * ((r₀ : ℝ) + 1) ^ 2 ∧
        (∀ i ∈ crossingLabels Λ S₀ r₀ a X,
          Real.log ((q : ℝ) ^ (designatedSupport Λ S₀ r₀ (a i)).card) ≤
            C * ((r₀ : ℝ) + 1) ^ 2) ∧
        cutBudget q Λ S₀ r₀ a X ≤ C * (1 + (edgeBoundary Λ X).card) * ((r₀ : ℝ) + 1) ^ 6 := by
  set μ : ℝ := ((2 ^ (2 * R + 1) ^ 2 : ℕ) : ℝ)
  have hμ : 0 ≤ μ := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  set K := max 1 (2 * μ * 4 * (1 + 4 * Real.log q) ^ 2)
  refine ⟨max (max (2 * μ * 4) (4 * Real.log q)) K, by positivity, ?_⟩
  intro Λ a ha S₀ r₀ X hX
  have hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ := fun x => by
    simp only [μ]; exact_mod_cast card_anchor_fiber_le Λ R a ha x
  have h1 : 2 * μ * 4 ≤ max (max (2 * μ * 4) (4 * Real.log q)) K :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h2 : 4 * Real.log q ≤ max (max (2 * μ * 4) (4 * Real.log q)) K :=
    (le_max_right _ _).trans (le_max_left _ _)
  have h3 : K ≤ max (max (2 * μ * 4) (4 * Real.log q)) K := le_max_right _ _
  refine ⟨fun i hi => (truncationRadius_eq_of_mem_crossingLabels hX hi).2.2, ?_,
    fun i hi => ?_, ?_⟩
  · refine (card_crossingLabels_le Λ S₀ r₀ a hX hμ (card_graphNbhd_singleton_le_four Λ)
      hMult).trans ?_
    rw [mul_right_comm]
    gcongr
  · refine (log_dim_le_of_mem_crossingLabels hq hX (card_graphNbhd_singleton_le_four Λ)
      hi).trans ?_
    gcongr
  · refine (cutBudget_le hq Λ S₀ r₀ a hX (by norm_num) hμ (card_graphNbhd_singleton_le_four Λ)
      hMult).trans ?_
    gcongr

/-- **The cut budget in terms of `n` on a lattice domain** (Proposition 4.5, last sentence,
`03-quasilocal.tex`, lines 452–455 and 519–520). For `q ≥ 1`, `R`, `C₁ ≥ 0` and `C₂ ≥ 0` there
is `C ≥ 0` such that, with `r₀ = ⌈C₁ (log n)²⌉`, every `X ⊆ S₀` with `b_X ≤ C₂ n D`, `n ≥ 2`
and `D ≥ 1` has `ℬ_X ≤ C n D (log n)¹²`. -/
theorem exists_latticeCutBudget_le_log {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (a : supports Λ R → ℤ × ℤ), (∀ X, a X ∈ X.1) →
      ∀ (S₀ X : Finset (ℤ × ℤ)), X ⊆ S₀ → ∀ n D : ℝ, 2 ≤ n → 1 ≤ D →
        ((edgeBoundary Λ X).card : ℝ) ≤ C₂ * n * D →
        cutBudget q Λ S₀ ⌈C₁ * Real.log n ^ 2⌉₊ a X ≤ C * (n * D * Real.log n ^ 12) := by
  obtain ⟨C, hC, hcross⟩ := exists_latticeCrossingBudget hq R
  refine ⟨C * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ 6, by positivity, ?_⟩
  intro Λ a ha S₀ X hX n D hn hD hb
  exact le_of_cutBudget_le hC hC₁ hC₂ hn hD hb (hcross Λ a ha S₀ _ X hX).2.2.2

end OpenAI
