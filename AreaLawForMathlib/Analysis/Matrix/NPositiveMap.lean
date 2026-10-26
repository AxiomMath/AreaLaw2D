/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI

Ported and specialized from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Channel/KrausCPTP.lean`,
`QICLean/Channel/Schwarz/TwoPositive.lean`, and
`QICLean/Channel/NPositiveIntegral.lean`.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Composition
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.Matrix

/-!
# Matrix k-positive maps

Extends `QuantumInfo/Channels/MatrixMap.lean`.

This file contains the small part of the finite-dimensional positive-map API needed
for the Fréchet derivatives in Section 7: blockwise `k`-positivity, sandwich maps,
and closure under zero, nonnegative scaling, composition, and Bochner integration.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

variable {n n' : Type*}

/-- The blockwise amplification of a linear map by `k × k` matrices. -/
def nPositiveAmpliation (k : ℕ) (E : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) :
    Matrix (n × Fin k) (n × Fin k) ℂ →ₗ[ℂ]
      Matrix (n' × Fin k) (n' × Fin k) ℂ where
  toFun X := Matrix.of fun (ip : n' × Fin k) (jq : n' × Fin k) =>
    E (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) ip.1 jq.1
  map_add' X Y := by
    ext ip jq
    change E ((Matrix.of fun i j => X (i, ip.2) (j, jq.2)) +
        (Matrix.of fun i j => Y (i, ip.2) (j, jq.2))) ip.1 jq.1 =
      (E (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) +
        E (Matrix.of fun i j => Y (i, ip.2) (j, jq.2))) ip.1 jq.1
    rw [map_add]
  map_smul' c X := by
    ext ip jq
    change E (c • (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1 =
      (c • E (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1
    rw [map_smul]

/-- A linear map is `k`-positive when its blockwise amplification preserves positive
semidefinite matrices. -/
def IsNPositiveMap (k : ℕ) (E : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) : Prop :=
  ∀ X : Matrix (n × Fin k) (n × Fin k) ℂ,
    X.PosSemidef → (nPositiveAmpliation k E X).PosSemidef

/-- A linear map on matrices is **completely positive** if its entrywise action on every matrix
amplification preserves positive semidefinite matrices. -/
def IsCompletelyPositive (E : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) : Prop :=
  ∀ k, IsNPositiveMap k E

/-- The single-sandwich linear map `X ↦ V X Vᴴ`. -/
noncomputable def singleKrausMap [Fintype n]
    (V : Matrix n' n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem singleKrausMap_apply [Fintype n]
    (V : Matrix n' n ℂ) (X : Matrix n n ℂ) :
    singleKrausMap V X = V * X * Vᴴ :=
  rfl

/-- The zero map is `k`-positive. -/
theorem IsNPositiveMap.zero (k : ℕ) :
    IsNPositiveMap k (0 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := by
  intro X hX
  convert (Matrix.PosSemidef.zero : (0 : Matrix (n × Fin k) (n × Fin k) ℂ).PosSemidef)
    using 1
  ext ip jq
  simp [nPositiveAmpliation]

/-- The sum of two `k`-positive maps is `k`-positive. -/
theorem IsNPositiveMap.add {E F : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {k : ℕ}
    (hE : IsNPositiveMap k E) (hF : IsNPositiveMap k F) : IsNPositiveMap k (E + F) := by
  intro X hX
  convert Matrix.PosSemidef.add (hE X hX) (hF X hX) using 1
  ext ip jq
  simp [nPositiveAmpliation]

/-- A nonnegative real multiple of a `k`-positive map is `k`-positive. -/
theorem IsNPositiveMap.smul_nonneg {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {k : ℕ}
    {c : ℝ} (hc : 0 ≤ c) (hE : IsNPositiveMap k E) : IsNPositiveMap k ((c : ℂ) • E) := by
  intro X hX
  have hcC : 0 ≤ (c : ℂ) := by
    exact_mod_cast hc
  convert (hE X hX).smul hcC using 1
  ext ip jq
  simp [nPositiveAmpliation]

/-- Composition preserves `k`-positivity. -/
theorem IsNPositiveMap.comp {n'' : Type*}
    {E : Matrix n' n' ℂ →ₗ[ℂ] Matrix n'' n'' ℂ}
    {F : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ} {k : ℕ}
    (hE : IsNPositiveMap k E) (hF : IsNPositiveMap k F) : IsNPositiveMap k (E ∘ₗ F) := by
  intro X hX
  exact hE _ (hF X hX)

/-- A sandwich map is `k`-positive for every `k`. -/
theorem isNPositiveMap_singleKrausMap [Fintype n]
    (V : Matrix n n ℂ) (k : ℕ) : IsNPositiveMap k (singleKrausMap V) := by
  classical
  intro X hX
  let e : n × Fin k ≃ Fin k × n := Equiv.prodComm n (Fin k)
  let Xswap : Matrix (Fin k × n) (Fin k × n) ℂ := Matrix.reindex e e X
  have hXswap : Xswap.PosSemidef := by
    simpa [Xswap, Matrix.reindex_apply] using hX.submatrix e.symm
  let Xblk : Matrix (Fin k) (Fin k) (Matrix n n ℂ) :=
    (Matrix.compRingEquiv (Fin k) n ℂ).symm Xswap
  let D : Matrix (Fin k) (Fin k) (Matrix n n ℂ) :=
    Matrix.diagonal fun _ => V
  let F := Matrix.compRingEquiv (Fin k) n ℂ
  have hcomp_conjTranspose (M : Matrix (Fin k) (Fin k) (Matrix n n ℂ)) :
      F Mᴴ = (F M)ᴴ := by
    ext ip jq
    rcases ip with ⟨p, i⟩
    rcases jq with ⟨q, j⟩
    rfl
  have hYswap : (F (D * Xblk * Dᴴ)).PosSemidef := by
    let L : Matrix (Fin k × n) (Fin k × n) ℂ := F D
    have hL : F (D * Xblk * Dᴴ) = L * Xswap * Lᴴ := by
      calc
        F (D * Xblk * Dᴴ) = F (D * Xblk) * F Dᴴ := by rw [F.map_mul]
        _ = (F D * F Xblk) * (F D)ᴴ := by rw [F.map_mul, hcomp_conjTranspose]
        _ = L * (Xswap * Lᴴ) := by simp [F, L, Xblk, Matrix.mul_assoc]
        _ = L * Xswap * Lᴴ := by simp [Matrix.mul_assoc]
    simpa [hL] using hXswap.mul_mul_conjTranspose_same (B := L)
  have hDterm :
      D * Xblk * Dᴴ = Matrix.of fun p q => V * Xblk p q * Vᴴ := by
    ext p q i j
    simp [D, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  have hXblk_apply (p q : Fin k) :
      Xblk p q = Matrix.of fun i j => X (i, p) (j, q) := by
    ext i j
    simp [Xblk, Xswap, e, Matrix.reindex_apply]
  have hY : (Matrix.reindex e.symm e.symm (F (D * Xblk * Dᴴ))).PosSemidef := by
    simpa [Matrix.reindex_apply] using hYswap.submatrix e
  convert hY using 1
  ext ip jq
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  change singleKrausMap V (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) ip.1 jq.1 =
      (F (D * Xblk * Dᴴ)) (ip.2, ip.1) (jq.2, jq.1)
  rw [hDterm]
  simp only [singleKrausMap_apply]
  change (V * Matrix.of (fun i j => X (i, ip.2) (j, jq.2)) * Vᴴ) ip.1 jq.1 =
      (V * Xblk ip.2 jq.2 * Vᴴ) ip.1 jq.1
  rw [hXblk_apply]

/-- Evaluation of the blockwise amplification at a fixed matrix, as a continuous
linear map on the finite-dimensional space of continuous linear maps. -/
noncomputable def nPositiveEval [Fintype n] [Fintype n'] (k : ℕ)
    (X : Matrix (n × Fin k) (n × Fin k) ℂ) :
    (Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) →L[ℂ]
      Matrix (n' × Fin k) (n' × Fin k) ℂ :=
  let eval : (Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) →ₗ[ℂ]
      Matrix (n' × Fin k) (n' × Fin k) ℂ :=
    { toFun := fun E => Matrix.of fun (ip : n' × Fin k) (jq : n' × Fin k) =>
        E (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) ip.1 jq.1
      map_add' := fun E G => by ext; simp
      map_smul' := fun c E => by ext; simp }
  ⟨eval, LinearMap.continuous_of_finiteDimensional _⟩

@[simp] theorem nPositiveEval_apply [Fintype n] [Fintype n'] (k : ℕ)
    (X : Matrix (n × Fin k) (n × Fin k) ℂ)
    (E : Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) :
    nPositiveEval k X E = Matrix.of fun (ip : n' × Fin k) (jq : n' × Fin k) =>
      E (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) ip.1 jq.1 :=
  rfl

theorem nPositiveEval_eq_ampliation [Fintype n] [Fintype n'] (k : ℕ)
    (X : Matrix (n × Fin k) (n × Fin k) ℂ)
    (E : Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) :
    nPositiveEval k X E = nPositiveAmpliation k E.toLinearMap X :=
  rfl

namespace Matrix.PosSemidef

/-- A Bochner integral of almost everywhere positive semidefinite complex matrices is
positive semidefinite. -/
theorem integral_of_ae {m α : Type*} [Fintype m] [DecidableEq m]
    [MeasurableSpace α] {μ : Measure α} {G : α → Matrix m m ℂ}
    (hG : Integrable G μ) (hpos : ∀ᵐ a ∂μ, (G a).PosSemidef) :
    (∫ a, G a ∂μ).PosSemidef := by
  have hentry (i j : m) :
      (∫ a, G a ∂μ) i j = ∫ a, G a i j ∂μ := by
    let entryEval : Matrix m m ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M i j
        map_add' := fun A B => by simp
        map_smul' := fun c A => by simp }
    let entryEvalL : Matrix m m ℂ →L[ℂ] ℂ :=
      ⟨entryEval, LinearMap.continuous_of_finiteDimensional _⟩
    exact (entryEvalL.integral_comp_comm hG).symm
  have hHerm : (∫ a, G a ∂μ).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply]
    rw [hentry j i, hentry i j]
    calc
      star (∫ a, (G a) j i ∂μ) = ∫ a, star ((G a) j i) ∂μ :=
        (integral_conj (f := fun a => (G a) j i)).symm
      _ = ∫ a, (G a) i j ∂μ := by
        apply integral_congr_ae
        filter_upwards [hpos] with a ha
        exact ha.isHermitian.apply i j
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, ?_⟩
  intro x
  let quadEval : Matrix m m ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
      map_add' := fun A B => by
        rw [Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun c A => by
        rw [Matrix.smul_mulVec, dotProduct_smul]
        rfl }
  let quadEvalL : Matrix m m ℂ →L[ℂ] ℂ :=
    ⟨quadEval, LinearMap.continuous_of_finiteDimensional _⟩
  have hq : Integrable (fun a => quadEvalL (G a)) μ := quadEvalL.integrable_comp hG
  have hqint : ∫ a, quadEvalL (G a) ∂μ = quadEvalL (∫ a, G a ∂μ) :=
    quadEvalL.integral_comp_comm hG
  change 0 ≤ quadEvalL (∫ a, G a ∂μ)
  rw [← hqint, Complex.nonneg_iff]
  constructor
  · change 0 ≤ RCLike.re (∫ a, quadEvalL (G a) ∂μ)
    rw [← integral_re hq]
    exact integral_nonneg_of_ae (hpos.mono fun a ha =>
      (Complex.nonneg_iff.mp (ha.dotProduct_mulVec_nonneg x)).1)
  · change 0 = RCLike.im (∫ a, quadEvalL (G a) ∂μ)
    rw [← integral_im hq]
    symm
    calc
      (∫ a, (quadEvalL (G a)).im ∂μ) = ∫ _a, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hpos] with a ha
        exact (Complex.nonneg_iff.mp (ha.dotProduct_mulVec_nonneg x)).2.symm
      _ = 0 := by simp

/-- The positive-semidefinite integral conclusion without a separate integrability
hypothesis. In the nonintegrable case the Bochner integral is zero by definition. -/
theorem integral_of_ae' {m α : Type*} [Fintype m] [DecidableEq m]
    [MeasurableSpace α] {μ : Measure α} {G : α → Matrix m m ℂ}
    (hpos : ∀ᵐ a ∂μ, (G a).PosSemidef) : (∫ a, G a ∂μ).PosSemidef := by
  by_cases hG : Integrable G μ
  · exact integral_of_ae hG hpos
  · rw [integral_undef hG]
    exact Matrix.PosSemidef.zero

end Matrix.PosSemidef

private theorem nPositiveEval_integral_pos [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n']
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ} (hF : Integrable F μ)
    {k : ℕ} (X : Matrix (n × Fin k) (n × Fin k) ℂ)
    (hpos : ∀ᵐ a ∂μ, (nPositiveEval k X (F a)).PosSemidef) :
    (nPositiveEval k X (∫ a, F a ∂μ)).PosSemidef := by
  have heval : ∫ a, nPositiveEval k X (F a) ∂μ =
      nPositiveEval k X (∫ a, F a ∂μ) :=
    ContinuousLinearMap.integral_comp_comm
      (E := Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) (μ := μ) (nPositiveEval k X) hF
  rw [← heval]
  exact Matrix.PosSemidef.integral_of_ae' (m := n' × Fin k) (μ := μ)
    (G := fun a => nPositiveEval k X (F a)) hpos

/-- A Bochner integral of almost everywhere `k`-positive continuous linear maps is
`k`-positive. -/
theorem IsNPositiveMap.integral [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ}
    (hF : Integrable F μ) {k : ℕ}
    (hpos : ∀ᵐ a ∂μ, IsNPositiveMap k (F a).toLinearMap) :
    IsNPositiveMap k (∫ a, F a ∂μ).toLinearMap := by
  intro X hX
  rw [← nPositiveEval_eq_ampliation]
  apply nPositiveEval_integral_pos hF X
  filter_upwards [hpos] with a ha
  rw [nPositiveEval_eq_ampliation]
  exact ha X hX
