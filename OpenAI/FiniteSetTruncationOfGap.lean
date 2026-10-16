/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit
fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/FiniteSetTruncationGap.lean`. Apache 2.0; instantiated with the frozen
`OpenAI.PositiveReplacement` theorem and square-lattice counting lemmas.
-/
import OpenAI.CrossingBudget
import OpenAI.PositiveReplacement

/-!
# Finite-set truncation from the physical global gap

The assembled first part of Proposition 4.5 of OAI265 over `ℂ`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw

/-- Proposition 4.3 at `p = 1`, followed by finite-set truncation and gap stability. -/
theorem exists_finiteSetTruncation_of_gap (q R : ℕ) (J Δ : ℝ)
    (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ g : ℝ, 0 < g ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ Λ : Finset (ℤ × ℤ),
      ∀ Φ : (X : Finset (ℤ × ℤ)) →
        Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ,
        IsAdmissible Λ R J Φ →
      ∀ (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
        hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω →
        HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
      ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset (ℤ × ℤ),
        (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
      let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
      let ε := min (n ^ (-1000 : ℝ)) (g / 4)
      ∃ (anchor : supports Λ R → ℤ × ℤ)
        (k : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ),
        (∀ X, anchor X ∈ X.1) ∧
        let Ht := ∑ i, truncatedConstraint q Λ S₀ r₀ (anchor i) (k i)
        (∀ i, IsSupportedOn (designatedSupport_subset Λ S₀ r₀ (anchor i))
          (truncatedConstraint q Λ S₀ r₀ (anchor i) (k i))) ∧
        (∀ i, 0 ≤ truncatedConstraint q Λ S₀ r₀ (anchor i) (k i) ∧
          truncatedConstraint q Λ S₀ r₀ (anchor i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧
          0 ≤ e ∧ e ≤ ε ∧
          (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
            (1 - Matrix.vecMulVec (WithLp.ofLp Ω₀)
              (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • WithLp.toLp 2 Ω‖ ≤
            2 * Real.sqrt (ε / g)) ∧
          (Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)) -
            Matrix.vecMulVec Ω (star Ω)).traceNorm / 2 ≤
              Real.sqrt (2 * ε / g) := by
  classical
  obtain ⟨cstar, hcstar, C, c, hc, hPR⟩ :=
    positive_replacement (𝕜 := ℂ) q R J Δ 1 hq hJ hΔ (by norm_num)
  let C' := max 0 C
  let μ : ℝ := ((2 ^ (2 * R + 1) ^ 2 : ℕ) : ℝ)
  have hC' : 0 ≤ C' := by simp [C']
  have hμ : 0 ≤ μ := by positivity
  letI : NeZero q := ⟨by omega⟩
  obtain ⟨C₁, hC₁, htr⟩ :=
    exists_finiteSetTruncation (C := C') (c := c) (g := Δ / cstar)
      (μ := μ) (Kb := 4) (C₀ := C₀) hC' hc (div_pos hΔ hcstar) hμ
      (by norm_num) hC₀
  refine ⟨Δ / cstar, div_pos hΔ hcstar, C₁, hC₁, ?_⟩
  intro Λ Φ hΦ Ω hΩ E₀ hHΩ hgap n hn S₀ hS₀ r₀ ε
  let anchor : supports Λ R → ℤ × ℤ := fun X =>
    ((mem_supports_iff.1 X.2).2.1).choose
  have hanchor : ∀ X, anchor X ∈ X.1 := fun X =>
    ((mem_supports_iff.1 X.2).2.1).choose_spec
  let anchorTotal : Finset (ℤ × ℤ) → ℤ × ℤ := fun X =>
    if hX : X ∈ supports Λ R then anchor ⟨X, hX⟩ else (0, 0)
  have hanchorTotal : ∀ X ∈ supports Λ R, anchorTotal X ∈ X := by
    intro X hX
    simpa only [anchorTotal, dif_pos hX] using hanchor ⟨X, hX⟩
  let a : supports Λ R → ℤ × ℤ := fun X => anchorTotal X.1
  have ha : ∀ X, a X ∈ X.1 := fun X => hanchorTotal X.1 X.2
  obtain ⟨kAll, hkAll, hsum, hgapbase, htail, hsupp⟩ :=
    hPR Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchorTotal hanchorTotal
  let k : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun X => kAll X.1
  have hk : ∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧
      k i *ᵥ WithLp.ofLp (WithLp.toLp 2 Ω) = 0 := by
    intro i
    simpa only [k, WithLp.ofLp_toLp] using hkAll i.1 i.2
  have hgapF : ((∑ i, k i) - (((Δ / cstar : ℝ) : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp (WithLp.toLp 2 Ω))
        (star (WithLp.ofLp (WithLp.toLp 2 Ω)))))).PosSemidef := by
    rw [← Matrix.le_iff]
    calc
      ((Δ / cstar : ℝ) : ℂ) • (1 - Matrix.vecMulVec Ω (star Ω)) ≤
          (cstar : ℂ)⁻¹ • (hamiltonian Λ Φ - (E₀ : ℂ) • 1) := hgapbase
      _ ≤ ∑ X ∈ supports Λ R, kAll X := hsum
      _ = ∑ i, k i := by
        rw [← Finset.sum_attach, Finset.attach_eq_univ]
  have htail' : ∀ i (l : ℕ),
      ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
        C' * Real.exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ))) := by
    intro i l
    have ht := (htail i.1 i.2 l).2.2
    norm_num only [Nat.cast_one, one_add_one_eq_two] at ht
    calc
      ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ))) := by
        simpa only [k, a, neg_mul] using ht
      _ ≤ C' * Real.exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ))) := by
        exact mul_le_mul_of_nonneg_right (le_max_right 0 C) (Real.exp_pos _).le
  have hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ := by
    intro x
    dsimp only [μ]
    exact_mod_cast card_anchor_fiber_le Λ R a ha x
  let ΩE : EuclideanSpace ℂ (Reg (Qudits q) Λ) := WithLp.toLp 2 Ω
  have hΩE : ‖ΩE‖ = 1 := (norm_toLp_eq_one_iff Ω).2 hΩ
  have hresult := htr Λ a k ΩE hΩE hk hgapF htail'
    (card_graphNbhd_singleton_le_four Λ) hMult n hn S₀ hS₀
  refine ⟨a, k, ha, ?_⟩
  dsimp only
  refine ⟨fun i => ?_, ?_⟩
  · exact truncatedConstraint_isSupportedOn Λ S₀ r₀ (a i)
      (by
        simpa only [k, a] using hsupp i.1 i.2)
  · simpa only [ΩE, WithLp.ofLp_toLp] using hresult

end OpenAI
