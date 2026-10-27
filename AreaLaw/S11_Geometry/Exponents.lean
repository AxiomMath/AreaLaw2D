import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §11.2 The exponents of the geometric construction

Digest `digest/11-geometry.md` D11.2 (`geometry:exponents`, `geometry:exponent-gaps`).
-/

namespace AreaLaw

/-! ## 11.2 The exponents -/

namespace Geometry

/-- D10.1. `β = 1 - 2·10⁻⁶`, the exponent of Proposition 10.2 (`OpenAI.Amplification`). -/
noncomputable def β : ℝ := 1 - 2 / 1000000

/-- The exponent `p` of Propositions 4.3 and 10.2: `α = p/(p+1) > 1 - 10⁻⁶` (D10.1). -/
def p : ℕ := 1000000

/-- D11.2. `δ₀ = 2·10⁻⁷`. -/
noncomputable def δ₀ : ℝ := 2 / 10000000

/-- D11.2. `ζ = 1 - δ₀/2`. -/
noncomputable def ζ : ℝ := 1 - δ₀ / 2

/-- D11.2. `ρ₀ = (1 + β)/2`. -/
noncomputable def ρ₀ : ℝ := (1 + β) / 2

/-- D11.2. `ℓ = 10⁻⁵`, the collar exponent of Proposition 9.6 (`OpenAI.collarWidth`). -/
noncomputable def ℓ : ℝ := 1 / 100000

/-- D11.2 (`geometry:exponent-gaps`).
`(1+2δ₀)β < ζ < 1`, `(1+2δ₀)(1-ℓ) < 1`, `1-ℓ < β < ρ₀ < 1`. -/
theorem eq_exponent_gaps :
    (1 + 2 * δ₀) * β < ζ ∧ ζ < 1 ∧ (1 + 2 * δ₀) * (1 - ℓ) < 1 ∧
      1 - ℓ < β ∧ β < ρ₀ ∧ ρ₀ < 1 := by
  simp only [δ₀, ζ, β, ρ₀, ℓ]
  -- D11.2.1–D11.2.3
  norm_num

end Geometry

end AreaLaw
