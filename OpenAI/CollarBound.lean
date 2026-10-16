import OpenAI.CollarInformation

/-!
# The collar bound

Proposition 9.6 of [OAI265, §9.5].  The mutual-information inequality is
`OpenAI.collarInformationBound`, proved over `ℂ` and transported to every `RCLike` field; the
size and boundary assertions follow from it by `OpenAI.collarBound_of_collarInformationBound`.
-/

namespace OpenAI

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Proposition 9.6** [OAI265, §9.5]. -/
theorem collar_bound (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    CollarBound 𝕜 q R J Δ :=
  collarBound_of_collarInformationBound (collarInformationBound q R J Δ hq hJ hΔ)

end OpenAI
