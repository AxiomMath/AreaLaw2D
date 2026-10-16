/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit
fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/FiniteSetTruncationGap.lean`. Apache 2.0; adapted to the frozen
`OpenAI.condExpect`, square-lattice `graphNbhd`, and `Reg (Qudits q) Λ` interfaces.
-/
import OpenAI.FiniteSetTruncation
import OpenAI.GapPerturbation
import OpenAI.TruncationRadius

/-!
# The finite-set truncation retains a spectral gap

This is the spectral part of Proposition 4.5 of OAI265 on the frozen square-lattice model.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw

/-- Each truncated constraint is a positive contraction. -/
theorem truncatedConstraint_mem_Icc {q : ℕ} [NeZero q]
    (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : ℤ × ℤ)
    {k : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) :
    0 ≤ truncatedConstraint q Λ S₀ r₀ a k ∧
      truncatedConstraint q Λ S₀ r₀ a k ≤ 1 := by
  unfold truncatedConstraint
  split_ifs
  · exact ⟨hk₀, hk₁⟩
  · exact ⟨condExpect_nonneg _ hk₀, condExpect_le_one _ hk₁⟩

/-- Truncating a uniformly quasilocal positive family near `S₀` changes its sum by at most
`ε = min(n⁻¹⁰⁰⁰,g/4)` and retains a `g/2` spectral gap. -/
theorem exists_finiteSetTruncation {C c g μ Kb C₀ : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hg : 0 < g) (hμ : 0 ≤ μ)
    (hKb : 0 ≤ Kb) (hC₀ : 0 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
        {κ : Type*} [Fintype κ] (a : κ → ℤ × ℤ)
        (k : κ → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ)
        (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω‖ = 1 →
        (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) →
        ((∑ i, k i) - (g : ℂ) •
          (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
        (∀ i (l : ℕ),
          ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
            C * Real.exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ)))) →
        (∀ x (d : ℕ), ((graphNbhd Λ {x} d).card : ℝ) ≤
          Kb * ((d : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) →
        ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset (ℤ × ℤ),
          (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
        let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
        let ε := min (n ^ (-1000 : ℝ)) (g / 4)
        let Ht := ∑ i, truncatedConstraint q Λ S₀ r₀ (a i) (k i)
        (∀ i, 0 ≤ truncatedConstraint q Λ S₀ r₀ (a i) (k i) ∧
          truncatedConstraint q Λ S₀ r₀ (a i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : EuclideanSpace ℂ (Reg (Qudits q) Λ)), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧
          0 ≤ e ∧ e ≤ ε ∧
          (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
            (1 - Matrix.vecMulVec (WithLp.ofLp Ω₀)
              (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤
            2 * Real.sqrt (ε / g)) ∧
          (Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)) -
            Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).traceNorm / 2 ≤
              Real.sqrt (2 * ε / g) := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_sum_shell_le hc (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨C₁, hC₁, hrad⟩ :=
    exists_truncationConstant (B := C * μ * Kb * A) (C₀ := C₀)
      (by positivity) hC₀ hc hg
  refine ⟨C₁, hC₁, ?_⟩
  intro q _ Λ κ _ a k Ω hΩ hk hgap htail hBall hMult n hn S₀ hS₀ r₀ ε Ht
  have hHt := truncatedConstraint_mem_Icc (q := q) Λ S₀ r₀
  have herr : ‖Ht - ∑ i, k i‖ ≤ ε := by
    refine (norm_sum_truncatedConstraint_sub_le Λ S₀ a k hC hKb hμ htail
      hBall hMult hA r₀).trans ?_
    have h := hrad n hn S₀.card (Nat.cast_nonneg _) hS₀
    calc
      C * μ * Kb * S₀.card * A *
          Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) =
          C * μ * Kb * A * S₀.card *
            Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) := by
        ring
      _ ≤ ε := h
  refine ⟨fun i => hHt (a i) (hk i).1 (hk i).2.1, herr, ?_⟩
  have hHtpsd : Ht.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact Finset.sum_nonneg fun i _ => (hHt (a i) (hk i).1 (hk i).2.1).1
  have hHFΩ : (∑ i, k i) *ᵥ WithLp.ofLp Ω = 0 := by
    rw [Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => (hk i).2.2
  have hε : ε ≤ g / 4 := min_le_right _ _
  exact Matrix.exists_posSemidef_gap_of_norm_sub_le hΩ hg hε hgap hHFΩ hHtpsd herr

end OpenAI
