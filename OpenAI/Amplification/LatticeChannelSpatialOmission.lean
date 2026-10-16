/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/LatticeChannelSpatialOmission.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adapted to this project's encodings, as
`OpenAI.Amplification.ConstraintWordTruncation` is: TNLean's `Site Λ` and
`Configuration Λ q` are points of `ℤ × ℤ` and `Reg (Qudits q) Λ`, anchors are maps
`a : κ → ℤ × ℤ` (for the lattice theorem `supports Λ R → ℤ × ℤ` with `a X ∈ X`), the support
`S` of `B` is a finite subset of `ℤ²` with `hS : S ⊆ Λ`, and the block hypothesis
`Matrix.of (fun σ τ => B (σ, x) (τ, y)) ∈ supportedOperators q (S : Set (Site Λ))` is
`OpenAI.IsSupportedOn hS (Matrix.of fun σ τ => B (σ, x) (τ, y))`;
`siteExpectation q (graphBall (domainGraph Λ) x l)` is
`OpenAI.condExpect (graphNbhd_subset Λ {x} l)`, `(domainGraph Λ).edist` is
`OpenAI.domainEDist Λ`, `graphNeighborhood Λ r S` is `OpenAI.graphNbhd Λ S r`;
`StateSpace Λ q` is `EuclideanSpace ℂ (Reg (Qudits q) Λ)`; `LocalHamiltonian Λ q R J` is an
interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ`, its operator `hamiltonian Λ Φ` and its term
`h.term X` being `extendId _ (Φ X)`, and `IsGappedGroundState` is `‖Ω‖ = 1`, the eigen-equation
and `OpenAI.HasGlobalGap`; `AdmissibleSupport Λ R` is `supports Λ R`.  The lattice theorem uses
`OpenAI.exists_latticePositiveConstraints` and the anchor multiplicity
`OpenAI.card_anchor_fiber_le_two_pow`; the ball count `card_graphBall_domainGraph_le` is
`OpenAI.card_graphNbhd_singleton_le_two_mul`.  Declaration names are kept.
-/
import OpenAI.LatticeConstraints
import OpenAI.Amplification.ChannelGroundVectors
import OpenAI.Amplification.ConstraintWordTruncation
import OpenAI.Amplification.GraphChannelSpatialOmission

/-!
# Omitting distant events on finite lattice domains

The omission clause of Lemma 10.1 on a finite domain `Λ ⊂ ℤ²` with its induced graph.  For
positive contractions `k_i` anchored at `a_i` with bounded multiplicity and stretched-exponential
localization tails, run the full Poisson word and keep the events whose anchors lie within
distance `r` of `S`.  The channel words, and on a common zero vector `Ω` of the constraints the
products of the roots `(I - k_i)^{1/2}`, differ in expectation by at most
`A t |S| ‖B‖ e^{v t - γ r^α}` [OAI265, Lemma 10.1, eq. (10.5),
`eq:amplification-product-omission`].  The constants depend only on the tail constants and the
multiplicity bound.  The last theorem specializes to the exact positive constraints of a gapped
lattice Hamiltonian.

## Main statements

* `OpenAI.exists_domainConstraintWord_omission`: the omission estimate for general constraints
  with a root tail.
* `OpenAI.exists_latticeConstraintWord_omission`: the omission estimate for the positive
  constraints of a gapped lattice Hamiltonian.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 10.1 (`lem:amplification-local-products`), `09-amplification.tex`, lines 42–72, proof
  at lines 188–226.  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory
open scoped ENNReal NNReal Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix SpectralFilter

/-- The Euclidean norm of a product vector is the product of the two norms. -/
private theorem norm_toLp_prod_vector {n m : Type*} [Fintype n] [Fintype m]
    (Ω : n → ℂ) (ξ : m → ℂ) :
    ‖WithLp.toLp 2 (fun p : n × m => Ω p.1 * ξ p.2)‖ =
      ‖WithLp.toLp 2 Ω‖ * ‖WithLp.toLp 2 ξ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp [mul_pow]

/-- A site outside the graph neighbourhood of radius `r` of `S` is at extended distance more
than `r` from every site of `S`. -/
private theorem lt_edist_of_notMem_graphNeighborhood {Λ S : Finset (ℤ × ℤ)} {r : ℕ}
    {y : ℤ × ℤ} (hy : y ∉ graphNbhd Λ S r) :
    ∀ s ∈ S, ENNReal.ofReal (r : ℝ) < (domainEDist Λ y s : ℝ≥0∞) := by
  intro s hs
  rw [ENNReal.ofReal_natCast]
  by_contra hle
  rw [not_lt] at hle
  have hle' : domainEDist Λ y s ≤ r := by exact_mod_cast hle
  apply hy
  have hyΛ : y ∈ Λ := by
    by_contra hyΛ
    rw [domainEDist_of_not_mem_left hyΛ] at hle'
    exact absurd hle' (by simp)
  simp only [graphNbhd, Finset.mem_filter]
  exact ⟨hyΛ, (iInf₂_le s hs).trans hle'⟩

/-- **Expected channel omission on a lattice domain** [OAI265, §10.1, eq. (10.12),
`eq:amplification-channel-omission`, `09-amplification.tex`, lines 203–215].  For tail constants
`C ≥ 0`, `c > 0`, `0 < α ≤ 1` and a multiplicity bound `μ` there are `A ≥ 0` and `v, γ > 0` with
the following property.  Let `k_i` be positive contractions on a finite domain `Λ`, anchored at
`a_i` with at most `μ` labels per site, with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all
`l`.  Let `B` act on `S ⊆ Λ` and a finite spectator, and let every label outside `P` be at
distance more than `r` from `S`.  Then the norm of the difference of the full channel word and
its retained subword, on the same Poisson realization, is integrable with expectation at most
`A t |S| ‖B‖ e^{v t - γ r^α}`. -/
theorem exists_domain_integrable_and_integral_channelWordOmissionDefect_le
    {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ A v γ : ℝ, 0 ≤ A ∧ 0 < v ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → ℤ × ℤ) (k : κ → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (P : κ → Prop) [DecidablePred P]
          (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (ℤ × ℤ)) (hS : S ⊆ Λ)
          (B : Matrix (Reg (Qudits q) Λ × Aux) (Reg (Qudits q) Λ × Aux) ℂ),
          (∀ x y : Aux, IsSupportedOn hS (Matrix.of fun σ τ => B (σ, x) (τ, y))) →
          ∀ (r : ℝ), 0 ≤ r →
            (∀ i, ¬ P i → ∀ s ∈ S, ENNReal.ofReal r < (domainEDist Λ (a i) s : ℝ≥0∞)) →
            ∀ t : ℝ≥0,
              Integrable (fun w : PoissonWord.Word κ =>
                channelWordOmissionDefect k P (List.ofFn w.2) B) (PoissonWord.measure κ t) ∧
              (∫ w : PoissonWord.Word κ,
                channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ t) ≤
                A * t * S.card * ‖B‖ * Real.exp (v * t - γ * r ^ α) := by
  obtain ⟨A, v, γ, hA, hv, hγ, -, hbound⟩ :=
    exists_integrable_and_integral_channelWordOmissionDefect_le hC (K := 2) zero_le_two
      hμ hc hα hα₁
  refine ⟨A, v, γ, hA, hv, hγ, ?_⟩
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail P _ Aux _ _ S hS B hB r hr hfar t
  let N := Finset.univ.sup fun i : κ => Λ.sup fun x => (domainEDist Λ (a i) x).toNat
  have hN (i : κ) : Λ.sup (fun x => (domainEDist Λ (a i) x).toNat) ≤ N :=
    Finset.le_sup (f := fun j : κ => Λ.sup fun x => (domainEDist Λ (a j) x).toNat)
      (Finset.mem_univ i)
  have h := hbound κ Aux (Qudits q) Λ a k hk₀ hk₁
    (fun i => mem_supportedOperators_reachable_of_forall_tail _ _ hc hα (htail i))
    (card_graphNbhd_singleton_le_two_mul Λ) hfiber N hN (fun i l _ => htail i l)
  exact h _ _ _ _ hB _ hr hfar _

/-- **Omission of distant events from constraint products on a lattice domain**
[OAI265, Lemma 10.1, eq. (10.5), `eq:amplification-product-omission`,
`09-amplification.tex`, lines 42–72, proof at lines 188–226].  For tail constants `C ≥ 0`,
`c > 0`, `0 < α ≤ 1` and a multiplicity bound `μ` there are `A ≥ 0` and `v, γ > 0` with the
following property.  Let `k_i` be positive contractions on a finite domain `Λ`, anchored at
`a_i` with at most `μ` labels per site, with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all
`l`, and `k_i Ω = 0` for a unit vector `Ω`.  Retain the labels with `d_Λ(a_i, S) ≤ r`.  On each
realization `w` of the full Poisson word let `D(w)` be the chronological product of the roots
`(I - k_i)^{1/2}` over all events, later factors on the left, and `D_ret(w)` the same product
over the retained events.  If `B` acts on `S ⊆ Λ` and a finite spectator, then for every unit
spectator vector `ξ` the norm `‖(D - D_ret) B (Ω ⊗ ξ)‖` is integrable with expectation at most
`A t |S| ‖B‖ e^{v t - γ r^α}`.  The source assumes `S` nonempty and `r ≥ 1`; neither is needed
here. -/
theorem exists_domainConstraintWord_omission
    {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ A v γ : ℝ, 0 ≤ A ∧ 0 < v ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → ℤ × ℤ) (k : κ → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
          (∀ i, k i *ᵥ WithLp.ofLp Ω = 0) →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (ℤ × ℤ)) (hS : S ⊆ Λ)
          (B : Matrix (Reg (Qudits q) Λ × Aux) (Reg (Qudits q) Λ × Aux) ℂ),
          (∀ x y : Aux, IsSupportedOn hS (Matrix.of fun σ τ => B (σ, x) (τ, y))) →
          ∀ (ξ : Aux → ℂ), ‖WithLp.toLp 2 ξ‖ = 1 → ∀ (r : ℕ) (t : ℝ≥0),
            let P := fun i : κ => a i ∈ graphNbhd Λ S r
            let D := fun u : List κ =>
              ((u.reverse.map fun i => CFC.sqrt (1 - k i)).prod ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ
                (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)
            let F := fun w : PoissonWord.Word κ =>
              ‖WithLp.toLp 2 (D (List.ofFn w.2) -
                D ((List.ofFn w.2).filter fun i => decide (P i)))‖
            Integrable F (PoissonWord.measure κ t) ∧
            (∫ w, F w ∂PoissonWord.measure κ t) ≤
              A * t * S.card * ‖B‖ * Real.exp (v * t - γ * (r : ℝ) ^ α) := by
  obtain ⟨A, v, γ, hA, hv, hγ, hbound⟩ :=
    exists_domain_integrable_and_integral_channelWordOmissionDefect_le hC hμ hc hα hα₁
  refine ⟨A, v, γ, hA, hv, hγ, ?_⟩
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail Ω hΩ hkΩ Aux _ _ S hS B hB ξ hξ r t P Dw F
  obtain ⟨hint, hle⟩ := hbound Λ κ a k hk₀ hk₁ hfiber htail P Aux S hS B hB (r : ℝ)
    (Nat.cast_nonneg r) (fun i hi => lt_edist_of_notMem_graphNeighborhood hi) t
  have hunit : ‖WithLp.toLp 2 (fun x : Reg (Qudits q) Λ × Aux =>
      WithLp.ofLp Ω x.1 * ξ x.2)‖ = 1 := by
    rw [norm_toLp_prod_vector, hξ, mul_one]
    exact hΩ
  have hpt (w : PoissonWord.Word κ) :
      F w ≤ channelWordOmissionDefect k P (List.ofFn w.2) B := by
    have := norm_rootProduct_sub_le_channelWord_sub k hk₀ hk₁ hkΩ
      (List.ofFn w.2) ((List.ofFn w.2).filter fun i => decide (P i)) ξ B
    rwa [hunit, mul_one] at this
  have hFint : Integrable F (PoissonWord.measure κ t) :=
    hint.mono' Measurable.of_discrete.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hpt w)
  exact ⟨hFint, (integral_mono hFint hint hpt).trans hle⟩

/-- **Omission of distant events for the exact positive constraints** [OAI265, Lemma 10.1,
eq. (10.5), `eq:amplification-product-omission`, applied to the constraints of
`eq:amplification-positive-system`; `09-amplification.tex`, lines 17–30, 42–72 and 188–226].
For `p ≥ 1`, `R`, `J ≥ 0` and `Δ > 0` there are `A ≥ 0` and `v, γ > 0` such that, for the exact
positive constraints `k_i` of every gapped lattice Hamiltonian with ground state `Ω`, every
anchoring `a_i ∈ X_i`, finite spectator, set `S ⊆ Λ`, radius `r`, time `t`, operator `B` acting
on `S` and the spectator, and unit spectator vector `ξ`, the expected norm of
`(D - D_ret) B (Ω ⊗ ξ)` is at most `A t |S| ‖B‖ e^{v t - γ r^α}` with `α = p / (p + 1)`.  The
retained events are those with `d_Λ(a_i, S) ≤ r`. -/
theorem exists_latticeConstraintWord_omission {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ A v γ : ℝ, 0 ≤ A ∧ 0 < v ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ →
        ∀ (a : supports Λ R → ℤ × ℤ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
          hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
          HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (ℤ × ℤ)) (hS : S ⊆ Λ)
          (B : Matrix (Reg (Qudits q) Λ × Aux) (Reg (Qudits q) Λ × Aux) ℂ),
          (∀ x y : Aux, IsSupportedOn hS (Matrix.of fun σ τ => B (σ, x) (τ, y))) →
          ∀ (ξ : Aux → ℂ), ‖WithLp.toLp 2 ξ‖ = 1 → ∀ (r : ℕ) (t : ℝ≥0),
            let P := fun i : supports Λ R => a i ∈ graphNbhd Λ S r
            let k := fun i : supports Λ R => positiveConstraint
              (positiveNormalization p (Δ / 2) J)
              (centeredFilter p (Δ / 2) (hamiltonian Λ Φ) Ω
                (extendId (subset_of_mem_supports i.2) (Φ i)))
            let D := fun u : List (supports Λ R) =>
              ((u.reverse.map fun i => CFC.sqrt (1 - k i)).prod ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ
                (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)
            let F := fun w : PoissonWord.Word (supports Λ R) =>
              ‖WithLp.toLp 2 (D (List.ofFn w.2) -
                D ((List.ofFn w.2).filter fun i => decide (P i)))‖
            Integrable F (PoissonWord.measure (supports Λ R) t) ∧
            (∫ w, F w ∂PoissonWord.measure (supports Λ R) t) ≤
              A * t * S.card * ‖B‖ * Real.exp (v * t - γ * (r : ℝ) ^ kernelExponent p) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  obtain ⟨A, v, γ, hA, hv, hγ, hbound⟩ :=
    exists_domainConstraintWord_omission hC
      (μ := ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)
      hc (kernelExponent_pos hp) (kernelExponent_le_one p)
  refine ⟨A, v, γ, hA, hv, hγ, ?_⟩
  intro q _ Λ Φ hΦ a ha E₀ Ω hΩ heig hgap Aux _ _ S hS B hB ξ hξ r t
  obtain ⟨-, hk, -, -, -, htail, -⟩ := hpos Λ Φ hΦ a ha E₀ Ω hΩ heig hgap
  exact hbound Λ (supports Λ R) a _ (fun i => (hk i).1) (fun i => (hk i).2.1)
    (fun x => by exact_mod_cast card_anchor_fiber_le_two_pow a ha x)
    (fun i l => (htail i l).2.2) Ω hΩ (fun i => (hk i).2.2) Aux S hS B hB ξ hξ r t

end OpenAI
