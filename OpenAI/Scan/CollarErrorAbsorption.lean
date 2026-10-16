import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorbing the errors of the subtracted sharp comparison

The scalar bookkeeping after eq. (9.19) of [OAI265, proof of Proposition 9.6]: the subtracted
sharp comparison bounds `2 S' + ⟨g_pre - g_post⟩` by the errors of eq. (9.19) in terms of
`log d`, `S'`, the band average of `g_pre` and the maximal gap `M`.  Replacing `S'` and
`log d` by `S(X)` up to `w - log z`, the average of `g_pre` and `M` by the uniform bound
`C₁ n^{1+e}`, and the defect energy by `E₀ + η`, every term is a fixed multiple of one of the
six error terms of the table after eq. (9.20), apart from a remainder that vanishes as
`η → 0` and `k → ∞`.  Here `P` stands for `n^{1+e}`, `ν` for `n^{-100}` and `aB` for
`a n D (log n)^{12}`.
-/

namespace OpenAI.Scan

/-- **Error absorption for the subtracted sharp comparison** [OAI265, eq. (9.19) and the table
after eq. (9.20)].  If `2 S' + Q` is at most the subtracted sharp comparison bound, with
`aK = W`, `|S' - S(X)|, |log d - S(X)| ≤ w - log z`, `-log z ≤ 2ν`, the band average of
`g_pre` at most `C₁ P`, the maximal gap `M ≤ max 0 (2 S' + C₁ P)`, the defect energy at
most `E₀ + η`, and the remainder `η M / τ + r + 2 r' / W` at most one, then `2 S(X) + Q` is
at most `c ((P + 1)/W + w + (τ + E₀/τ) P + h/a + aB + ν/a) + 1`. -/
theorem two_mul_add_le_of_subtracted_comparison
    {Sx S' logd logz ν w P τ h a K W Gavg M Edef E₀ η rem rem' Kmom aB Ce C₁ c Q : ℝ}
    (hτ : 0 < τ) (ha : 0 < a) (ha1 : a ≤ 1) (hW : 0 < W) (haK : a * K = W) (hP : 1 ≤ P)
    (hw0 : 0 ≤ w) (hwP : w ≤ P) (hz0 : logz ≤ 0) (hz : -logz ≤ 2 * ν) (hν : ν ≤ 1 / 2)
    (hCe : 0 ≤ Ce) (hC₁ : 0 ≤ C₁) (hSx : Sx ≤ Ce * P)
    (hS'lo : Sx - S' ≤ w - logz) (hS'up : S' ≤ Sx + w - logz) (hd : logd ≤ Sx + w - logz)
    (hG : Gavg ≤ C₁ * P) (hM0 : 0 ≤ M) (hM : M ≤ max 0 (2 * S' + C₁ * P))
    (hE : Edef ≤ E₀ + η) (hE₀ : 0 ≤ E₀) (hh : 0 ≤ h)
    (hKmom : 37 * Kmom * a ≤ c * aB) (hc : C₁ + 4 * Ce + 10 ≤ c)
    (hmain : 2 * S' + Q ≤ τ * Gavg + 2 * τ * logd + (3 + 1 / a) * h + 37 * Kmom * a +
      Edef / τ * M + rem + 2 / (a * K) * (2 * logd - logz + rem') - logz / a)
    (hrem : η / τ * M + rem + 2 / W * rem' ≤ 1) :
    2 * Sx + Q ≤ c * ((P + 1) / W + w + (τ + E₀ / τ) * P + h / a + aB + ν / a) + 1 := by
  rw [haK] at hmain
  have hν0 : 0 ≤ ν := by linarith
  have hζP : -logz ≤ P := by linarith
  -- the separate terms
  have hT1 : τ * Gavg ≤ τ * (C₁ * P) := mul_le_mul_of_nonneg_left hG hτ.le
  have hdP : logd ≤ (Ce + 2) * P := by linarith only [hd, hSx, hwP, hζP]
  have hT2 : 2 * τ * logd ≤ 2 * τ * ((Ce + 2) * P) :=
    mul_le_mul_of_nonneg_left hdP (by positivity)
  have hha : h ≤ h / a := by
    rw [le_div_iff₀ ha]; exact mul_le_of_le_one_right hh ha1
  have hT3 : (3 + 1 / a) * h ≤ 4 * (h / a) := by
    have : (3 + 1 / a) * h = 3 * h + h / a := by field_simp
    rw [this]; linarith only [hha]
  have hMP : M ≤ (2 * Ce + 4 + C₁) * P :=
    hM.trans (max_le (by positivity) (by linarith only [hS'up, hSx, hwP, hζP]))
  have hT5 : Edef / τ * M ≤ E₀ / τ * ((2 * Ce + 4 + C₁) * P) + η / τ * M := by
    have h1 : Edef / τ * M ≤ (E₀ + η) / τ * M :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE hτ.le) hM0
    have h2 : E₀ / τ * M ≤ E₀ / τ * ((2 * Ce + 4 + C₁) * P) :=
      mul_le_mul_of_nonneg_left hMP (div_nonneg hE₀ hτ.le)
    have h3 : (E₀ + η) / τ * M = E₀ / τ * M + η / τ * M := by ring
    linarith
  have hT7 : 2 / W * (2 * logd - logz + rem') ≤ (4 * Ce + 10) * ((P + 1) / W) + 2 / W * rem' := by
    have h1 : 2 * logd - logz ≤ (4 * Ce + 10) / 2 * (P + 1) := by
      linarith only [hdP, hζP, hCe]
    have h2 : 2 / W * (2 * logd - logz) ≤ 2 / W * ((4 * Ce + 10) / 2 * (P + 1)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 / W * ((4 * Ce + 10) / 2 * (P + 1)) = (4 * Ce + 10) * ((P + 1) / W) := by
      field_simp
    have h4 : 2 / W * (2 * logd - logz + rem') = 2 / W * (2 * logd - logz) + 2 / W * rem' := by
      ring
    linarith
  have hνa : ν ≤ ν / a := by
    rw [le_div_iff₀ ha]; exact mul_le_of_le_one_right hν0 ha1
  have hT8 : -(logz / a) ≤ 2 * (ν / a) := by
    rw [← neg_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hz ha.le
  -- the coefficients are at most `c`
  have hP0 : 0 ≤ (P + 1) / W := by positivity
  have hτP : 0 ≤ τ * P := by positivity
  have hEP : 0 ≤ E₀ / τ * P := by positivity
  have hhA : 0 ≤ h / a := by positivity
  have hνA : 0 ≤ ν / a := by positivity
  have hsplit : c * ((P + 1) / W + w + (τ + E₀ / τ) * P + h / a + aB + ν / a) =
      c * ((P + 1) / W) + c * w + c * (τ * P) + c * (E₀ / τ * P) + c * (h / a) + c * aB +
        c * (ν / a) := by ring
  have hc1 : (4 * Ce + 10) * ((P + 1) / W) ≤ c * ((P + 1) / W) :=
    mul_le_mul_of_nonneg_right (by linarith) hP0
  have hc2 : 2 * w ≤ c * w := mul_le_mul_of_nonneg_right (by linarith) hw0
  have hc3 : τ * (C₁ * P) + 2 * τ * ((Ce + 2) * P) ≤ c * (τ * P) := by
    have : τ * (C₁ * P) + 2 * τ * ((Ce + 2) * P) = (C₁ + 2 * Ce + 4) * (τ * P) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right (by linarith) hτP
  have hc4 : E₀ / τ * ((2 * Ce + 4 + C₁) * P) ≤ c * (E₀ / τ * P) := by
    have : E₀ / τ * ((2 * Ce + 4 + C₁) * P) = (2 * Ce + 4 + C₁) * (E₀ / τ * P) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right (by linarith) hEP
  have hc5 : 4 * (h / a) ≤ c * (h / a) := mul_le_mul_of_nonneg_right (by linarith) hhA
  have hc6 : 6 * (ν / a) ≤ c * (ν / a) := mul_le_mul_of_nonneg_right (by linarith) hνA
  have hgap : 2 * Sx ≤ 2 * S' + 2 * w + 4 * (ν / a) := by
    linarith only [hS'lo, hz, hνa]
  linarith only [hmain, hT1, hT2, hT3, hKmom, hT5, hT7, hT8, hrem, hsplit, hc1, hc2, hc3, hc4,
    hc5, hc6, hgap]

end OpenAI.Scan
