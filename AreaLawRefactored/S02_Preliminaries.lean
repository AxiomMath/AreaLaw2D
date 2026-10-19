import OpenAI.Statements
import Arealaw.Subadditivity

/-!
# §2 Entropy and induced-graph locality

Digest `digest/02-preliminaries.md`, paper `paper/sections/01-preliminaries.tex`.
-/

namespace AreaLaw

open Arealaw OpenAI
open scoped ComplexOrder MatrixOrder

/-! ## D2.1 Conditional entropy and conditional mutual information -/

section Entropy

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U D E F : Finset σ}

/-- D2.1. `S(D|E)_ρ = S(DE)_ρ - S(E)_ρ`. -/
noncomputable def condEntropy (ρ : SubState (Reg loc U) ℂ) (hD : D ⊆ U) (hE : E ⊆ U) : ℝ :=
  ρ.regionEntropy (Finset.union_subset hD hE) - ρ.regionEntropy hE

/-- D2.1. `I(D:F|E)_ρ = S(DE)_ρ + S(EF)_ρ - S(E)_ρ - S(DEF)_ρ`.  The mutual information
`I(D:E)_ρ = S(D)_ρ + S(E)_ρ - S(DE)_ρ` is `Arealaw.SubState.mutualInfo`. -/
noncomputable def condMutualInfo (ρ : SubState (Reg loc U) ℂ) (hD : D ⊆ U) (hE : E ⊆ U)
    (hF : F ⊆ U) : ℝ :=
  ρ.regionEntropy (Finset.union_subset hD hE) + ρ.regionEntropy (Finset.union_subset hE hF) -
    ρ.regionEntropy hE - ρ.regionEntropy (Finset.union_subset (Finset.union_subset hD hE) hF)

end Entropy

/-! ## D2.3 Binary entropy and trace distance -/

/-- D2.3. Trace distance of states `ρ, σ`: `δ = ½‖ρ - σ‖₁`.  The binary entropy
`h(u) = -u log u - (1-u) log(1-u)` is Mathlib's `Real.binEntropy`. -/
noncomputable abbrev traceDist {ι : Type*} [Fintype ι] (ρ τ : MState ι ℂ) : ℝ :=
  ρ.toSubState.D₁ τ.toSubState

/-- D2.4.4. `C_h = 1 + 2/e`, the constant of `h(u) ≤ C_h √u`. -/
noncomputable def C_h : ℝ := 1 + 2 / Real.exp 1

/-! ## D2.6 Balls, graph neighborhoods, ambient dilations -/

/-- D2.6. `B_Λ(x,r) = {y ∈ Λ : d_Λ(x,y) ≤ r}`.  The neighbourhood `N^Λ_r(D)` is
`OpenAI.graphNbhd Λ D r` and the ambient dilation `T_j` is `OpenAI.ambientDilation T j`. -/
noncomputable abbrev ball (Λ : Finset (ℤ × ℤ)) (x : ℤ × ℤ) (r : ℕ) : Finset (ℤ × ℤ) :=
  graphNbhd Λ {x} r

/-- D2.7. `v_r = 1 + 2r(r+1)`. -/
def v (r : ℕ) : ℕ := 1 + 2 * r * (r + 1)

/-- D2.8. `μ_R = 2^(v_R - 1)`. -/
def μ (R : ℕ) : ℕ := 2 ^ (v R - 1)

end AreaLaw
