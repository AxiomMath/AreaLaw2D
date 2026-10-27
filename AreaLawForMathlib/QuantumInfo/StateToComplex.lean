import AreaLawForMathlib.QuantumInfo.RegionToComplex
import AreaLawForMathlib.QuantumInfo.Region.TraceDistance

/-!
# States and entropies under the embedding into `ℂ`

Extends `Arealaw/Mixed.lean`, `Arealaw/TraceDist.lean` and `OpenAI.pureState`: a
(sub)normalized state over an `RCLike` field `𝕜`, embedded entrywise into `ℂ` along
`RCLike.toComplex`, is again a (sub)normalized state.  The embedding commutes with restriction
to a subregion and preserves the eigenvalue multiset, so it preserves the von Neumann entropy,
every region entropy, the mutual information of two regions and the trace distance; the pure
state of a unit vector embeds to the pure state of the embedded vector.

## Main statements

* `Arealaw.SubState.toComplex`, `Arealaw.MState.toComplex`: the embedded states.
* `Arealaw.SubState.regionEntropy_toComplex`, `Arealaw.SubState.mutualInfo_toComplex`,
  `Arealaw.SubState.D₁_toComplex`: invariance of the entropic quantities.
* `OpenAI.pureState_toComplex`: the embedded pure state.
-/

open Matrix RCLike
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

namespace Matrix

variable {n : Type*} [Fintype n]

theorem trace_map_toComplex (A : Matrix n n 𝕜) :
    (A.map (toComplex 𝕜)).trace = toComplex 𝕜 A.trace := by
  simp [trace, map_sum]

/-- A sum of a function of the eigenvalues of a Hermitian matrix is unchanged by the
embedding into `ℂ`. -/
theorem IsHermitian.sum_eigenvalues_map_toComplex [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f ((isHermitian_map_toComplex_iff.2 hA).eigenvalues i) = ∑ i, f (hA.eigenvalues i) :=
  Arealaw.sum_eq_of_multiset_map_eq f hA.eigenvalues_map_toComplex

/-- The embedding into `ℂ` preserves the trace norm of a Hermitian matrix. -/
theorem IsHermitian.traceNorm_map_toComplex {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A.map (toComplex 𝕜)).traceNorm = A.traceNorm := by
  classical
  rw [traceNorm_Hermitian_eq_sum_abs_eigenvalues (isHermitian_map_toComplex_iff.2 hA),
    traceNorm_Hermitian_eq_sum_abs_eigenvalues hA]
  exact hA.sum_eigenvalues_map_toComplex abs

end Matrix

namespace Arealaw

variable {ι : Type*} [Fintype ι]

namespace SubState

/-- A subnormalized state over `𝕜`, embedded entrywise into `ℂ`. -/
noncomputable def toComplex (ρ : SubState ι 𝕜) : SubState ι ℂ where
  M := ρ.M.map (RCLike.toComplex 𝕜)
  psd := posSemidef_map_toComplex_iff.2 ρ.psd
  tr_le_one := by simpa [trace_map_toComplex] using ρ.tr_le_one

@[simp] theorem toComplex_M (ρ : SubState ι 𝕜) :
    ρ.toComplex.M = ρ.M.map (RCLike.toComplex 𝕜) := rfl

/-- The embedding into `ℂ` preserves the eigenvalue multiset of a state. -/
theorem eigenvalues_toComplex [DecidableEq ι] (ρ : SubState ι 𝕜) :
    Finset.univ.val.map ρ.toComplex.psd.isHermitian.eigenvalues =
      Finset.univ.val.map ρ.psd.isHermitian.eigenvalues :=
  ρ.psd.isHermitian.eigenvalues_map_toComplex

/-- The embedding into `ℂ` preserves the von Neumann entropy. -/
@[simp] theorem entropy_toComplex [DecidableEq ι] (ρ : SubState ι 𝕜) :
    ρ.toComplex.entropy = ρ.entropy := by
  rw [entropy_eq_H, entropy_eq_H]
  exact H_eq_of_multiset_eq ρ.eigenvalues_toComplex

/-- The embedding into `ℂ` preserves the trace distance. -/
@[simp] theorem D₁_toComplex (ρ τ : SubState ι 𝕜) : ρ.toComplex.D₁ τ.toComplex = ρ.D₁ τ := by
  classical
  rw [D₁_def, D₁_def, toComplex_M, toComplex_M, ← map_toComplex_sub,
    (ρ.psd.isHermitian.sub τ.psd.isHermitian).traceNorm_map_toComplex, trace_map_toComplex,
    trace_map_toComplex]
  simp

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  {S T U X Y : Finset σ}

/-- Restriction to a subregion commutes with the embedding into `ℂ`. -/
theorem toComplex_restrict (h : S ⊆ T) (ρ : SubState (Reg loc T) 𝕜) :
    (ρ.restrict h).toComplex = ρ.toComplex.restrict h :=
  SubState.ext (ptrace_map_toComplex h ρ.M).symm

variable [∀ i, DecidableEq (loc i)]

/-- The embedding into `ℂ` preserves every region entropy. -/
@[simp] theorem regionEntropy_toComplex (ρ : SubState (Reg loc U) 𝕜) (h : X ⊆ U) :
    ρ.toComplex.regionEntropy h = ρ.regionEntropy h := by
  rw [regionEntropy_def, regionEntropy_def, ← toComplex_restrict, entropy_toComplex]

/-- The embedding into `ℂ` preserves the mutual information of two regions. -/
@[simp] theorem mutualInfo_toComplex (ρ : SubState (Reg loc U) 𝕜) (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.toComplex.mutualInfo hX hY = ρ.mutualInfo hX hY := by
  simp only [mutualInfo_def, regionEntropy_toComplex]

end SubState

namespace MState

/-- A normalized state over `𝕜`, embedded entrywise into `ℂ`. -/
noncomputable def toComplex (ρ : MState ι 𝕜) : MState ι ℂ :=
  ⟨ρ.toSubState.toComplex, by simpa [trace_map_toComplex] using ρ.tr_eq_one⟩

@[simp] theorem toSubState_toComplex (ρ : MState ι 𝕜) :
    ρ.toComplex.toSubState = ρ.toSubState.toComplex := rfl

@[simp] theorem toComplex_M (ρ : MState ι 𝕜) : ρ.toComplex.M = ρ.M.map (RCLike.toComplex 𝕜) :=
  rfl

end MState

end Arealaw

namespace OpenAI

open Arealaw

variable {ι : Type*} [Fintype ι]

theorem star_dotProduct_comp_toComplex {Ω : ι → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1) :
    star (fun i => toComplex 𝕜 (Ω i)) ⬝ᵥ (fun i => toComplex 𝕜 (Ω i)) = 1 := by
  rw [star_comp_toComplex]
  simpa [dotProduct, map_sum] using congrArg (toComplex 𝕜) hΩ

/-- The pure state of a unit vector over `𝕜`, embedded into `ℂ`, is the pure state of the
embedded vector. -/
theorem pureState_toComplex (Ω : ι → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) :
    (pureState Ω hΩ).toComplex =
      pureState (fun i => toComplex 𝕜 (Ω i)) (star_dotProduct_comp_toComplex hΩ) := by
  ext : 1
  simp only [MState.toComplex_M, pureState, MState.mk'_M, star_comp_toComplex,
    vecMulVec_comp_toComplex]

end OpenAI
