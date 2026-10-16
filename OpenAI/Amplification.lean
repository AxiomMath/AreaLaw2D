import OpenAI.AmplificationProof
import OpenAI.Embedding

/-!
# The amplification proposition

Proposition 10.2 of [OAI265, §10.2].  The radius and output bounds are
`OpenAI.amplificationOutput_complex`, proved over `ℂ` and transported to every `RCLike` field
by `OpenAI.amplificationOutput`; the cut-clearance clause follows from the radius bound by
`OpenAI.amplification_of_amplificationOutput`.

## Implementation notes

The output bound is proved only over `ℂ`: the finite-product reductions and entropies, the
restoring operators and the positive constraints it rests on are `ℂ`-only.
`OpenAI.amplificationOutput` transfers it to `𝕜` through `OpenAI.toComplex`, which preserves
admissibility, the eigenvector equation, the gap and every mutual information.
-/

namespace OpenAI

open Arealaw Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Proposition 10.2 without its cut-clearance clause [OAI265, §10.2], over every `RCLike`
field: the statement over `ℂ` applied to the embedded Hamiltonian and vector. -/
theorem amplificationOutput (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) (hp : 1 - (1 / 1000000 : ℝ) < (p : ℝ) / (p + 1)) :
    AmplificationOutput 𝕜 q R J Δ p := by
  intro C₀ hC₀ M hM
  obtain ⟨C, n₀, h⟩ := amplificationOutput_complex q R J Δ p hq hJ hΔ hp C₀ hC₀ M hM
  refine ⟨C, n₀, fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n hn2 hn hcard hX hY hS hI => ?_⟩
  have hE' : hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)) *ᵥ
      (fun i => toComplex 𝕜 (Ω i)) = (E₀ : ℂ) • (fun i => toComplex 𝕜 (Ω i)) := by
    rw [hamiltonian_map_toComplex, ← toComplex_ofReal (𝕜 := 𝕜)]
    exact (mulVec_map_toComplex_eq_smul_iff _ _ _).2 hE
  have hgap' : HasGlobalGap (hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)))
      (fun i => toComplex 𝕜 (Ω i)) E₀ Δ := by
    rw [hamiltonian_map_toComplex]
    exact (hasGlobalGap_map_toComplex_iff _ _ _ _).2 hgap
  obtain ⟨r, hr, hout⟩ := h Λ (fun X => (Φ X).map (toComplex 𝕜))
    ((isAdmissible_map_toComplex_iff Λ R J Φ).2 hΦ) (fun i => toComplex 𝕜 (Ω i))
    (star_dotProduct_comp_toComplex_eq_one hΩ) E₀ hE' hgap' A hA T n hn2 hn hcard hX hY hS
    (by
      rw [← pureState_toComplex Ω hΩ]
      simpa only [MState.toSubState_toComplex, SubState.mutualInfo_toComplex] using hI)
  refine ⟨r, hr, fun X' hX' J' hJ' => ?_⟩
  have key := hout X' hX' J' hJ'
  rw [← pureState_toComplex Ω hΩ] at key
  simpa only [MState.toSubState_toComplex, SubState.mutualInfo_toComplex] using key

/-- **Proposition 10.2** [OAI265, §10.2]. -/
theorem amplification (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ)
    (hp : 1 - (1 / 1000000 : ℝ) < (p : ℝ) / (p + 1)) : Amplification 𝕜 q R J Δ p :=
  amplification_of_amplificationOutput hp (amplificationOutput q R J Δ p hq hJ hΔ hp)

end OpenAI
