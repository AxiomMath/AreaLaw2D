/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.NormNum

/-!
# Exact exponents for Proposition 11.2

Adapted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/Exponents.lean` (Apache 2.0), for the frozen
`OpenAI.TwoFamilyDecomposition` statement.  The proof is independently
formalized there from [OAI265, §11, `geometry:exponents` and
`geometry:exponent-gaps`].
-/

namespace OpenAI.Exponents

/-- Final safe-box error exponent `e_* = 2·10⁻⁶`. -/
def boxError : ℚ := 2 / 1000000

/-- Amplification exponent `β = 1 - 2·10⁻⁶`. -/
def beta : ℚ := 1 - boxError

/-- Geometric exponent `δ₀ = 2·10⁻⁷`. -/
def geometryDelta : ℚ := 2 / 10000000

/-- Geometric exponent `ζ = 1 - δ₀/2`. -/
def zeta : ℚ := 1 - geometryDelta / 2

/-- Repair exponent `ρ₀ = (1 + β)/2`. -/
def rho : ℚ := (1 + beta) / 2

/-- Geometric collar exponent loss `ℓ = 10⁻⁵`. -/
def geometryEll : ℚ := 1 / 100000

/-- The geometric exponent gaps of [OAI265, eq. `geometry:exponent-gaps`]. -/
theorem geometry_gaps :
    (1 + 2 * geometryDelta) * beta < zeta ∧ zeta < 1 ∧
    (1 + 2 * geometryDelta) * (1 - geometryEll) < 1 ∧
    1 - geometryEll < beta ∧ beta < rho ∧ rho < 1 := by
  norm_num [geometryDelta, beta, boxError, zeta, geometryEll, rho]

end OpenAI.Exponents
