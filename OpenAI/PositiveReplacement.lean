import OpenAI.ComplexWitnessTransfer

/-!
# Positive replacement

Proposition 4.3 of [OAI265, §4.2].  The analytic construction is carried out over `ℂ` in
`OpenAI.PositiveConstraints`; `OpenAI.ComplexWitnessTransfer` transports its existential
witnesses to an arbitrary `RCLike` field.
-/

namespace OpenAI

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Proposition 4.3** for every integer `p ≥ 1` [OAI265, §4.2]. -/
theorem positive_replacement (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) (hp : 1 ≤ p) : PositiveReplacement 𝕜 q R J Δ p :=
  positiveReplacement_of_complex q R J Δ p
    (positive_replacement_complex q R J Δ p hq hJ hΔ hp)

end OpenAI
