/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI

Ported and specialized from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Algebra/MatrixAux.lean`, `QICLean/Channel/Basic.lean`,
`QICLean/Channel/Schwarz/PositiveMapProperties.lean`, and
`QICLean/Channel/Schwarz/TwoPositive.lean`.
-/
import AreaLawForMathlib.LinearAlgebra.Matrix.TracePairing
import AreaLawForMathlib.Analysis.Matrix.NPositiveMap
import Mathlib.Analysis.Matrix.Spectrum
import QuantumInfo.Channels.Dual

/-!
# Positive matrix maps and trace adjoints

Extends `QuantumInfo/Channels/MatrixMap.lean`.

This file supplies the minimal positive-map API needed to turn the normalized
leaf maps of a mean tree into density matrices.  It relates one-positivity to
ordinary positivity, proves self-duality of the positive semidefinite cone for
the trace pairing, and shows that the trace-pairing adjoint of a positive map
is positive.
-/

open scoped Matrix ComplexOrder MatrixOrder

variable {m n : Type*}

/-- A complex-linear matrix map is positive when it preserves positive semidefiniteness. -/
def IsPositiveMap (E : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ X : Matrix n n ℂ, X.PosSemidef → (E X).PosSemidef

/-- A positive matrix map, viewed as an order-preserving linear map. -/
noncomputable def IsPositiveMap.toPositiveLinearMap [Finite m] [Finite n]
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hE : IsPositiveMap E) :
    Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ := by
  classical
  letI := Fintype.ofFinite m
  letI := Fintype.ofFinite n
  exact
    { toLinearMap := E
      monotone' := by
        intro A B hAB
        rw [Matrix.le_iff] at hAB ⊢
        simpa [map_sub] using hE (B - A) hAB }

/-- Positive maps preserve adjoints. -/
theorem IsPositiveMap.map_conjTranspose [Finite m] [Finite n]
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hE : IsPositiveMap E)
    (X : Matrix n n ℂ) : E Xᴴ = (E X)ᴴ := by
  classical
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  let := Classical.decEq m
  let := Classical.decEq n
  change hE.toPositiveLinearMap Xᴴ = (hE.toPositiveLinearMap X)ᴴ
  simpa [Matrix.star_eq_conjTranspose] using map_star hE.toPositiveLinearMap X

/-- One-positive maps are exactly positive maps. -/
theorem isNPositiveMap_one_iff_isPositiveMap
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    IsNPositiveMap 1 E ↔ IsPositiveMap E := by
  constructor
  · intro hE X hX
    let X' : Matrix (n × Fin 1) (n × Fin 1) ℂ :=
      Matrix.of fun ip jq => X ip.1 jq.1
    have hX' : X'.PosSemidef := by
      convert hX.submatrix (fun ip : n × Fin 1 => ip.1) using 1
      ext ip jq
      rfl
    have hY := hE X' hX'
    let emb : m → m × Fin 1 := fun i => (i, 0)
    convert hY.submatrix emb using 1
    ext i j
    simp only [emb, X', Matrix.submatrix_apply]
    change E X i j = E (Matrix.of fun a b => X a b) i j
    rw [show (Matrix.of fun i j => X i j) = X by ext i j; rfl]
  · intro hE X hX
    let eIn : n × Fin 1 ≃ n := Equiv.prodUnique n (Fin 1)
    let eOut : m × Fin 1 ≃ m := Equiv.prodUnique m (Fin 1)
    have hY : (Matrix.of fun (ip : m × Fin 1) (jq : m × Fin 1) =>
        E (Matrix.of fun i j => X (i, 0) (j, 0)) ip.1 jq.1).PosSemidef := by
      have hblock : (Matrix.of fun i j => X (i, 0) (j, 0)).PosSemidef := by
        convert hX.submatrix eIn.symm using 1
        ext i j
        simp [eIn]
      have hEblock := hE _ hblock
      convert hEblock.submatrix eOut using 1
      ext ip jq
      simp [eOut]
    convert hY using 1
    ext ip jq
    have hip : ip.2 = 0 := Subsingleton.elim ip.2 0
    have hjq : jq.2 = 0 := Subsingleton.elim jq.2 0
    simp [nPositiveAmpliation, hip, hjq]

namespace Matrix.PosSemidef

/-- The positive semidefinite cone is self-dual for the trace pairing. -/
theorem of_forall_trace_mul_nonneg [Fintype n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian)
    (h : ∀ B : Matrix n n ℂ, B.PosSemidef → 0 ≤ Matrix.trace (A * B)) :
    A.PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA ?_
  intro x
  have hB : (Matrix.vecMulVec x (star x)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star x
  have htrace := h (Matrix.vecMulVec x (star x)) hB
  simpa [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] using htrace

end Matrix.PosSemidef

private theorem traceAdjointMap_map_isHermitian_of_isPositiveMap
    [Finite n] [Fintype m] {E : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hE : IsPositiveMap E) {X : Matrix m m ℂ} (hX : X.IsHermitian) :
    (Matrix.traceAdjointMap E X).IsHermitian := by
  let := Fintype.ofFinite n
  classical
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  calc
    (starRingEnd ℂ) (Matrix.trace (X * E (Matrix.single i j 1))) =
        Matrix.trace ((X * E (Matrix.single i j 1))ᴴ) := by
          simpa using (Matrix.trace_conjTranspose (X * E (Matrix.single i j 1))).symm
    _ = Matrix.trace ((E (Matrix.single i j 1))ᴴ * Xᴴ) := by
          rw [Matrix.conjTranspose_mul]
    _ = Matrix.trace (E (Matrix.single j i 1) * X) := by
          rw [hX.eq, ← hE.map_conjTranspose]
          simp
    _ = Matrix.trace (X * E (Matrix.single j i 1)) := by
          rw [Matrix.trace_mul_comm]

/-- The trace-pairing adjoint of a positive map between finite matrix algebras is positive. -/
theorem IsPositiveMap.traceAdjointMap [Finite n] [Fintype m]
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hE : IsPositiveMap E) :
    IsPositiveMap (Matrix.traceAdjointMap E) := by
  classical
  let := Fintype.ofFinite n
  intro X hX
  refine Matrix.PosSemidef.of_forall_trace_mul_nonneg
    (traceAdjointMap_map_isHermitian_of_isPositiveMap hE hX.1) ?_
  intro B hB
  rw [Matrix.trace_traceAdjointMap_mul]
  exact Matrix.PosSemidef.trace_mul_nonneg hX (hE B hB)
