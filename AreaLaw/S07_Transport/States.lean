import AreaLaw.S07_Transport.Histories
import AreaLaw.S07_Transport.Fourier
import AreaLawForMathlib.Analysis.Matrix.FilteredNorm

/-!
# §7.4 The objects of Proposition 7.4

Digest `digest/07-transport.md` D7.14 (displays `transport:filtered-vector`,
`transport:states`): `N(p)`, `v(p)`, the states `σ_{j,u}`, and the three right-hand sides of
Proposition 7.4. No geometry.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix MeasureTheory Entropy

namespace AreaLaw.Transport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

variable (n) in
/-- `ρ` is a density matrix on `𝒮_k`: positive semidefinite, trace one, supported on `𝒮_k`. -/
def IsSymDensity {k : ℕ} (ρ : Matrix (Config n k) (Config n k) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1 ∧ ∀ π, Replicas.U (fun v => Fin (n v)) k Finset.univ π * ρ = ρ

namespace Round

variable {K : ℕ} {H : Type*} {C : H → Type*} (R : Round V K H C) (n)

/-- D7.14 (`transport:filtered-vector`). `N(p)² = ‖𝓜(p)^{-s} pre‖²`, `s = 1/4`. -/
noncomputable def normSq (t : ℝ) (k : ℕ) (pre : Config n k → ℂ) (p : ℝ) : ℝ :=
  Matrix.Transport.filteredNormSq (R.root n t k p) pre

/-- D7.14 (`transport:filtered-vector`). `v(p) = 𝓜(p)^{-s} pre / N(p)`, `s = 1/4`. -/
noncomputable def v (t : ℝ) (k : ℕ) (pre : Config n k → ℂ) (p : ℝ) : Config n k → ℂ :=
  Matrix.Transport.filteredVector (R.root n t k p) pre

variable [DecidableEq H] [∀ h, DecidableEq (C h)]

/-- D7.14 (`transport:states`). For `0 < p < 1`, `Φ_j` the normalized map of leaf `j` to
`𝓜(p)` (Lemma 7.2) and `u ∈ ℝ`: `σ_{j,u} = Φ_j^*(|𝓜(p)^{-iu} v(p)⟩⟨𝓜(p)^{-iu} v(p)|)`, with
`Tr(Φ_j^*(σ) Z) = Tr(σ Φ_j(Z))`. -/
noncomputable def state (t : ℝ) (k : ℕ) (pre : Config n k → ℂ) (p : I) (j : Leaf H C) (u : ℝ) :
    Matrix (Config n k) (Config n k) ℂ :=
  let w := Matrix.Transport.imagPow (R.root n t k p) u *ᵥ R.v n t k pre p
  (R.tree p).leafDual (R.input n t k) j (vecMulVec w (star w))

/-- D7.14 (a), right side: `∑_h w_h ∫ m_s(u) Tr(σ_{h,u} log C_h) du`. -/
noncomputable def exactDerivative [Fintype H] (t : ℝ) (k : ℕ) (pre : Config n k → ℂ) (p : I) :
    ℝ :=
  ∑ h, R.histTree.weight h * ∫ u, m (1 / 4) u *
    (R.state n t k pre p ⟨h, none⟩ u * CFC.log (R.relRatio n t k h)).trace.re

variable [∀ v, NeZero (n v)]

/-- D7.14 (b), the gain: `∑_{h,g} w_h ∫ m_s(u) ∫ ∑_{c ∈ 𝓒_h} q_{c|h} η_{h,c,g}(θ)
dμ_{σ_{h,u}}(θ) du` (without the factor `k a`). -/
noncomputable def entropyGain [Fintype H] [∀ h, Fintype (C h)] (t : ℝ) (k : ℕ)
    (pre : Config n k → ℂ) (p : I) : ℝ :=
  ∑ h, ∑ g, R.histTree.weight h * ∫ u, m (1 / 4) u *
    ∫ θ, (∑ c, (R.choiceTree h).weight c * R.eta h c g θ.1)
      ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p ⟨h, none⟩ u))

/-- D7.14 (c), the energy error: `∑_i W_i(p) ∑_{j ∈ 𝒥_i} π_j ∫ m_s(u) ∫ η_{i,j}(θ)^{1/8}
dμ_{σ_{j,u}}(θ) du` (without the factor `C a² ℓ^C`; the split weight occurs twice). -/
noncomputable def energyError [Fintype H] [∀ h, Fintype (C h)] {ι : Type*} [Fintype ι]
    (E : EnergyTerms V n ι) (t : ℝ) (k : ℕ) (pre : Config n k → ℂ) (p : I) : ℝ :=
  ∑ i, R.splitWeight E i p * ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j *
    ∫ u, m (1 / 4) u * ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ)
      ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u))

end Round

end AreaLaw.Transport
