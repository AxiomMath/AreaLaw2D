import OpenAI.Statements
import AreaLawForMathlib.Analysis.RCLike.ToComplex

/-!
# Region operations under the embedding into `ℂ`

Extends `Arealaw/PTrace.lean` and the region operations `OpenAI.condExpect`,
`OpenAI.IsSupportedOn` of `OpenAI/Statements.lean`: the partial trace, extension by the
identity and the conditional expectation commute with the entrywise embedding
`RCLike.toComplex` and with the entrywise real part `Matrix.realProjection`, and support in a
subregion is preserved by `Matrix.realProjection` and `Matrix.complexPullback`.

Some declarations here come from the v1 file `OpenAI/ConditionalExpectation.lean`, whose header
records it as ported or adapted from `LionSR/QICLean` and `LionSR/TNLean` (see `NOTICE`).
-/

open Matrix RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ] {loc : σ → Type*} {S T : Finset σ}

namespace Arealaw

theorem ptrace_map_toComplex [∀ i, Fintype (loc i)]
    (h : S ⊆ T) (A : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    ptrace h (A.map (toComplex 𝕜)) = (ptrace h A).map (toComplex 𝕜) := by
  ext; simp [ptrace, map_sum]

theorem extendId_map_toComplex [∀ i, DecidableEq (loc i)]
    (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (A.map (toComplex 𝕜)) = (extendId h A).map (toComplex 𝕜) := by
  ext
  simp only [extendId, of_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem realProjection_ptrace [∀ i, Fintype (loc i)]
    (h : S ⊆ T) (A : Matrix (Reg loc T) (Reg loc T) ℂ) :
    realProjection (𝕜 := 𝕜) (ptrace h A) = ptrace h (realProjection A) := by
  ext; simp [realProjection, ptrace]

theorem realProjection_extendId [∀ i, DecidableEq (loc i)]
    (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) ℂ) :
    realProjection (𝕜 := 𝕜) (extendId h A) = extendId h (realProjection A) := by
  ext
  simp only [realProjection_apply, extendId, of_apply]
  split_ifs <;> simp

end Arealaw

namespace OpenAI

open Arealaw

section condExpect

variable [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

theorem condExpect_map_toComplex (h : S ⊆ T) (A : Matrix (Reg loc T) (Reg loc T) 𝕜) :
    (condExpect h A).map (toComplex 𝕜) = condExpect h (A.map (toComplex 𝕜)) := by
  simp only [condExpect, map_toComplex_smul, extendId_map_toComplex, ptrace_map_toComplex]
  simp

theorem realProjection_condExpect (h : S ⊆ T) (A : Matrix (Reg loc T) (Reg loc T) ℂ) :
    realProjection (𝕜 := 𝕜) (condExpect h A) = condExpect h (realProjection A) := by
  have := realProjection_ofReal_smul (𝕜 := 𝕜) (Fintype.card (Reg loc (T \ S)) : ℝ)⁻¹
    (extendId h (ptrace h A))
  push_cast at this
  rw [condExpect, condExpect, this, realProjection_extendId, realProjection_ptrace]

end condExpect

variable [∀ i, DecidableEq (loc i)]

theorem IsSupportedOn.realProjection (h : S ⊆ T) {A : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hA : IsSupportedOn h A) : IsSupportedOn h (realProjection (𝕜 := 𝕜) A) := by
  obtain ⟨B, rfl⟩ := hA
  exact ⟨Matrix.realProjection B, realProjection_extendId h B⟩

theorem IsSupportedOn.complexPullback (hI : im (I : 𝕜) = 1) (h : S ⊆ T)
    {A : Matrix (Reg loc T) (Reg loc T) ℂ} (hA : IsSupportedOn h A) :
    IsSupportedOn h (complexPullback hI A) := by
  obtain ⟨B, rfl⟩ := hA
  refine ⟨Matrix.complexPullback hI B, map_toComplex_injective ?_⟩
  dsimp only
  rw [← extendId_map_toComplex, complexPullback_map_toComplex, complexPullback_map_toComplex]

end OpenAI
