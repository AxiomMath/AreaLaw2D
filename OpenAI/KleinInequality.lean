/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/QICLean commit e44381d9054ba5c42c720624cb690b251ad21533,
`QICLean/Analysis/KleinInequality.lean` (Apache 2.0). Only the eigen-expansion helpers
`trace_diag_conj`, `trace_mul_cfc_eq_double_sum`, `re_trace_mul_cfc_eq_double_sum` and
`row_sum_normSq_eq_one` are ported; Klein's inequality itself is Physlib's
`inner_log_sub_log_nonneg`.
-/
import OpenAI.HermitianCfcSpectral

/-!
# Eigen-expansion of `tr (ρ f(σ))`

For Hermitian `ρ` and `σ` with eigenvector unitaries `Uρ`, `Uσ`, the trace
`tr (ρ f(σ))` is the double sum `∑ᵢⱼ pᵢ f(qⱼ) |Wᵢⱼ|²` over the eigenvalues, weighted by the
overlap matrix `W = Uρ⋆ Uσ`, whose rows have unit `ℓ²` norm. These are the trace
identities behind Klein's inequality.

## Implementation notes

The statements are over `ℂ`, as is the Hermitian spectral form `Matrix.IsHermitian.cfc_form`
they rest on.
-/

open scoped Matrix ComplexOrder

namespace TNLean.Klein

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of `diagonal p * W * diagonal d * star W` as a double sum over the
overlap entries `W i j`. -/
theorem trace_diag_conj (p d : n → ℂ) (W : Matrix n n ℂ) :
    Matrix.trace (Matrix.diagonal p * W * Matrix.diagonal d * star W)
      = ∑ i, ∑ j, p i * d j * (W i j * star (W i j)) := by
  have hA : Matrix.diagonal p * W = Matrix.of (fun i j => p i * W i j) := by
    ext i j; simp [Matrix.diagonal_mul]
  have hB : Matrix.diagonal d * star W = Matrix.of (fun j k => d j * star (W k j)) := by
    ext j k; simp [Matrix.diagonal_mul, Matrix.star_apply]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Trace of `ρ * (hσ.cfc f)` as a double sum over the eigenvalues weighted by
the overlap matrix `W = star Uρ * Uσ` of the two eigenvector unitaries. -/
theorem trace_mul_cfc_eq_double_sum {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (ρ * hσ.cfc f)
      = ∑ i, ∑ j, (hρ.eigenvalues i : ℂ) * ((f (hσ.eigenvalues j) : ℝ) : ℂ)
          * (((star (hρ.eigenvectorUnitary : Matrix n n ℂ))
                * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j
            * star (((star (hρ.eigenvectorUnitary : Matrix n n ℂ))
                * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j)) := by
  set Vρ : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hVρ
  set Vσ : Matrix n n ℂ := (hσ.eigenvectorUnitary : Matrix n n ℂ)
  set dp : n → ℂ := fun i => ((hρ.eigenvalues i : ℝ) : ℂ)
  set dm : n → ℂ := fun j => ((f (hσ.eigenvalues j) : ℝ) : ℂ)
  set W : Matrix n n ℂ := star Vρ * Vσ with hW
  have hρ_eq : ρ = Vρ * Matrix.diagonal dp * star Vρ := hρ.spectral_form
  have hcfc_eq : hσ.cfc f = Vσ * Matrix.diagonal dm * star Vσ := hσ.cfc_form f
  conv_lhs => rw [hρ_eq, hcfc_eq]
  -- Reduce the conjugated product to `diagonal dp * W * diagonal dm * star W`
  -- via trace cyclicity, then apply `trace_diag_conj`.
  have hstarW : star W = star Vσ * Vρ := by rw [hW, star_mul, star_star]
  rw [← trace_diag_conj dp dm W, hstarW,
    show (Vρ * Matrix.diagonal dp * star Vρ * (Vσ * Matrix.diagonal dm * star Vσ))
        = Vρ * (Matrix.diagonal dp * (star Vρ * Vσ) * Matrix.diagonal dm * star Vσ) by
      simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm Vρ _, ← hW]
  simp only [Matrix.mul_assoc]

/-- Real part of `trace (ρ * hσ.cfc f)` as a real double sum weighted by the
doubly stochastic overlap matrix `P i j = |W i j|²`. -/
theorem re_trace_mul_cfc_eq_double_sum {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (ρ * hσ.cfc f)).re
      = ∑ i, ∑ j, hρ.eigenvalues i * f (hσ.eigenvalues j)
          * Complex.normSq (((star (hρ.eigenvectorUnitary : Matrix n n ℂ))
              * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  rw [trace_mul_cfc_eq_double_sum hρ hσ f, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set W : Matrix n n ℂ := (star (hρ.eigenvectorUnitary : Matrix n n ℂ))
    * (hσ.eigenvectorUnitary : Matrix n n ℂ)
  have hnsq : W i j * star (W i j) = ((Complex.normSq (W i j) : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [hnsq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- For a unitary matrix `W` (`W * star W = 1`), the row sums of `|W i j|²`
equal one. -/
theorem row_sum_normSq_eq_one {W : Matrix n n ℂ} (hW : W * star W = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h1 : (W * star W) i i = 1 := by rw [hW, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have hsum : ∑ j, W i j * (star W) j i = ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self, mul_comm]
  rw [hsum] at h1
  exact_mod_cast h1

end TNLean.Klein
