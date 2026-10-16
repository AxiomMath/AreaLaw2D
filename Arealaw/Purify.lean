import Arealaw.Mixed
import Arealaw.State
import QuantumInfo.ForMathlib.Isometry

/-!
# Purification

Every subnormalized state is the reduced state of a pure one, explicitly and without choice:
for positive semidefinite `ρ` the coefficient matrix is the operator square root, since
`rhoA (√ρ) = √ρ · (√ρ)ᴴ = √ρ · √ρ = ρ`.  The purifying system is a copy of the same index
type, which is what lets the ancilla become one extra site of a chain in
`Arealaw.PurifyChain`.

`exists_purification_of_card_le` moves a purification onto any larger purifying system.

`rhoA_purifyMat` holds for every positive semidefinite matrix, so the subnormalized case
needs no new type; only `MState.purify` needs normalization, a subnormalized purifying vector
not being a unit vector.  Absent deliberately: a subnormalized vector type, since the planned
channel layer's failure-flag construction handles subnormalization instead.
-/

namespace Arealaw

open scoped ComplexOrder MatrixOrder
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]

/-! ## The purifying coefficient matrix -/

section

omit [Fintype ι] [DecidableEq ι]

/-- A reduced density operator `ρ_A = M Mᴴ` is positive semidefinite. -/
theorem posSemidef_rhoA [Finite ι] {κ : Type*} [Fintype κ] (M : Matrix ι κ 𝕜) :
    (rhoA M).PosSemidef :=
  posSemidef_self_mul_conjTranspose M

/-- A coisometry `U Uᴴ = 1` on the purifying system, a unitary in particular, does not change
the reduced state. -/
theorem rhoA_mul_of_mul_conjTranspose_eq_one {κ μ : Type*} [Fintype κ] [Fintype μ] [DecidableEq κ]
    (M : Matrix ι κ 𝕜) {U : Matrix κ μ 𝕜} (hU : U * Uᴴ = 1) : rhoA (M * U) = rhoA M := by
  simp [rhoA, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU]

end

/-- The coefficient matrix of the canonical purification of `ρ`: its operator square
root. -/
noncomputable def purifyMat (ρ : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 := CFC.sqrt ρ

/-- The purifying matrix is positive semidefinite, in particular Hermitian. -/
theorem posSemidef_purifyMat (ρ : Matrix ι ι 𝕜) : (purifyMat ρ).PosSemidef :=
  (CFC.sqrt_nonneg ρ).posSemidef

/-- **`√ρ` purifies `ρ`**: the reduced density operator of the pure state with coefficient
matrix `√ρ` is `ρ` itself. -/
theorem rhoA_purifyMat {ρ : Matrix ι ι 𝕜} (hρ : ρ.PosSemidef) : rhoA (purifyMat ρ) = ρ := by
  rw [rhoA, (posSemidef_purifyMat ρ).isHermitian, purifyMat, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

/-- The purifying matrix has the same total weight as `ρ`, so it is a unit vector exactly
when `ρ` is normalized. -/
theorem sum_normSq_purifyMat {ρ : Matrix ι ι 𝕜} (hρ : ρ.PosSemidef) :
    ((∑ a, ∑ b, ‖purifyMat ρ a b‖ ^ 2 : ℝ) : 𝕜) = ρ.trace := by
  rw [← trace_rhoA, rhoA_purifyMat hρ]

omit [DecidableEq ι] in
/-- **Purification on a larger system**: any purifying system at least as large as the state's
own index type carries a purification. -/
theorem exists_purification_of_card_le {κ : Type*} [Fintype κ] {B : Matrix ι ι 𝕜}
    (hB : B.PosSemidef) (h : Fintype.card ι ≤ Fintype.card κ) : ∃ Y : Matrix ι κ 𝕜, rhoA Y = B := by
  classical
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le h
  have hV := Matrix.submatrix_one_isometry (R := 𝕜) Function.bijective_id emb.injective
  refine ⟨purifyMat B * ((1 : Matrix κ κ 𝕜).submatrix id emb)ᴴ, ?_⟩
  rw [rhoA_mul_of_mul_conjTranspose_eq_one _ (by rwa [conjTranspose_conjTranspose]),
    rhoA_purifyMat hB]

/-! ## Purifying a state -/

namespace SubState

/-- The reduced state of a bipartite pure state with coefficient matrix `ψ.M`, i.e.
`tr_B |ψ⟩⟨ψ|`. -/
noncomputable def reducedOfPure (ψ : PureState 𝕜 ι ι) : SubState ι 𝕜 where
  M := rhoA ψ.M
  psd := posSemidef_rhoA ψ.M
  tr_le_one := by simp [trace_rhoA_pureState ψ]

omit [DecidableEq ι] in
/-- The density matrix of a reduced state is `rhoA` of the coefficient matrix. -/
@[simp] theorem reducedOfPure_M (ψ : PureState 𝕜 ι ι) : (reducedOfPure ψ).M = rhoA ψ.M := rfl

/-- The purifying coefficient matrix of a subnormalized state. -/
noncomputable def purifyMat (ρ : SubState ι 𝕜) : Matrix ι ι 𝕜 := Arealaw.purifyMat ρ.M

/-- `√ρ` purifies a subnormalized `ρ` too. -/
@[simp] theorem rhoA_purifyMat (ρ : SubState ι 𝕜) : rhoA ρ.purifyMat = ρ.M :=
  Arealaw.rhoA_purifyMat ρ.psd

/-- The purifying vector of a subnormalized state has squared norm `tr ρ`; it is a unit
vector exactly when `ρ` is normalized. -/
theorem sum_normSq_purifyMat (ρ : SubState ι 𝕜) :
    ((∑ a, ∑ b, ‖ρ.purifyMat a b‖ ^ 2 : ℝ) : 𝕜) = ρ.M.trace :=
  Arealaw.sum_normSq_purifyMat ρ.psd

end SubState

namespace MState

/-- **Purification of a normalized state**: the pure state on `ι × ι` whose coefficient
matrix is `√ρ`. -/
noncomputable def purify (ρ : MState ι 𝕜) : PureState 𝕜 ι ι where
  M := purifyMat ρ.M
  normalized := by
    rw [← ρ.tr_eq_one, ← sum_normSq_purifyMat ρ.psd, RCLike.ofReal_re]

/-- The coefficient matrix of the purification is `√ρ`. -/
@[simp] theorem purify_M (ρ : MState ι 𝕜) : (purify ρ).M = purifyMat ρ.M := rfl

/-- **The purification specification**: reducing the purification of `ρ` recovers `ρ`. -/
theorem rhoA_purify (ρ : MState ι 𝕜) : rhoA (purify ρ).M = ρ.M :=
  rhoA_purifyMat ρ.psd

/-- Reducing the purification of `ρ` gives back the density matrix of `ρ`. -/
theorem reduced_purify (ρ : MState ι 𝕜) : (SubState.reducedOfPure (purify ρ)).M = ρ.M :=
  rhoA_purify ρ

end MState

end Arealaw
