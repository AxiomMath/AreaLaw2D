/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI

Ported and specialized from LionSR/QICLean commit
5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Channel/Schwarz/PositiveMapProperties.lean` and
`QICLean/Channel/Schwarz/TwoPositive.lean`.
-/
import AreaLawForMathlib.Analysis.Matrix.PositiveMap
import Mathlib.Data.Matrix.Block

/-!
# Kadison--Schwarz for two-positive matrix maps

This file contains the minimal two-positive Schwarz result required by the
Section 7 transport estimate.  It is stated directly using the existing
`IsNPositiveMap 2` predicate rather than importing a parallel channel hierarchy.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {m n : Type*}

/-- A block diagonal matrix with positive semidefinite diagonal blocks is positive
semidefinite. -/
theorem Matrix.PosSemidef.fromBlocks_diag
    [Finite m] [Finite n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B : Matrix (m ⊕ n) (m ⊕ n) ℂ).PosSemidef := by
  classical
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  obtain ⟨CA, hCA⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
    ((Matrix.nonneg_iff_posSemidef).mpr hA)
  obtain ⟨CB, hCB⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
    ((Matrix.nonneg_iff_posSemidef).mpr hB)
  have hCA' : A = CA * CAᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using hCA
  have hCB' : B = CB * CBᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using hCB
  let C : Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks CA 0 0 CB
  have hC : Matrix.fromBlocks A 0 0 B = C * Cᴴ := by
    simp [C, hCA', hCB', Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
  rw [hC]
  exact Matrix.posSemidef_self_mul_conjTranspose C

/-- The equivalence `α × Fin 2 ≃ α ⊕ α` used to express a two-positive
ampliation as a two-by-two block matrix. -/
noncomputable def finTwoSumEquiv (α : Type*) : α × Fin 2 ≃ α ⊕ α :=
  ((Equiv.prodCongr (Equiv.refl α) finTwoEquiv).trans (Equiv.prodComm α Bool)).trans
    (Equiv.boolProdEquivSum α)

@[simp] theorem finTwoSumEquiv_apply_zero {α : Type*} (a : α) :
    finTwoSumEquiv α (a, 0) = Sum.inl a := by
  simp [finTwoSumEquiv, finTwoEquiv]

@[simp] theorem finTwoSumEquiv_apply_one {α : Type*} (a : α) :
    finTwoSumEquiv α (a, 1) = Sum.inr a := by
  simp [finTwoSumEquiv, finTwoEquiv]

@[simp] theorem finTwoSumEquiv_symm_inl {α : Type*} (a : α) :
    (finTwoSumEquiv α).symm (Sum.inl a) = (a, 0) := by
  rw [Equiv.symm_apply_eq]
  exact finTwoSumEquiv_apply_zero a

@[simp] theorem finTwoSumEquiv_symm_inr {α : Type*} (a : α) :
    (finTwoSumEquiv α).symm (Sum.inr a) = (a, 1) := by
  rw [Equiv.symm_apply_eq]
  exact finTwoSumEquiv_apply_one a

/-- Two-positive maps are positive. -/
theorem IsNPositiveMap.isPositiveMap_two
    [Finite m] [Finite n]
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : IsNPositiveMap 2 E) : IsPositiveMap E := by
  intro X hX
  let e : n × Fin 2 ≃ n ⊕ n := finTwoSumEquiv n
  let X' : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
    Matrix.reindex e.symm e.symm (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ))
  have hX' : X'.PosSemidef := by
    have hdiag : (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ)).PosSemidef :=
      hX.fromBlocks_diag Matrix.PosSemidef.zero
    simpa [X', Matrix.reindex_apply] using hdiag.submatrix e
  have hY' := h X' hX'
  let emb : m → m × Fin 2 := fun i => (i, 0)
  convert hY'.submatrix emb using 1
  ext i j
  simp [emb, X', Matrix.reindex_apply, e]
  rfl

/-- Kadison--Schwarz for a unital two-positive map. -/
theorem kadison_schwarz_twoPositive
    [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h2pos : IsNPositiveMap 2 E) (hUnital : E 1 = 1)
    (X : Matrix n n ℂ) :
    (E (Xᴴ * X) - (E X)ᴴ * E X).PosSemidef := by
  let e : n × Fin 2 ≃ n ⊕ n := finTwoSumEquiv n
  let P : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks (Xᴴ * X) Xᴴ X 1
  have hP : P.PosSemidef := by
    let A : Matrix (n ⊕ n) (n ⊕ Fin 0) ℂ :=
      Matrix.fromBlocks Xᴴ 0 1 0
    simpa [A, P, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      using Matrix.posSemidef_self_mul_conjTranspose A
  let P' : Matrix (n × Fin 2) (n × Fin 2) ℂ := Matrix.reindex e.symm e.symm P
  have hP' : P'.PosSemidef := by
    simpa [P', Matrix.reindex_apply] using hP.submatrix e
  have hY' := h2pos P' hP'
  have hPos : IsPositiveMap E := h2pos.isPositiveMap_two
  have hP'Block (p q : Fin 2) :
      Matrix.of (fun i j => P' (i, p) (j, q)) =
        match p, q with
        | 0, 0 => Xᴴ * X
        | 0, 1 => Xᴴ
        | 1, 0 => X
        | 1, 1 => (1 : Matrix n n ℂ) := by
    fin_cases p <;> fin_cases q <;>
      ext a b <;> simp [P', Matrix.reindex_apply, P, e]
  have hEBlock (p q : Fin 2) :
      E (Matrix.of fun i j => P' (i, p) (j, q)) =
        match p, q with
        | 0, 0 => E (Xᴴ * X)
        | 0, 1 => (E X)ᴴ
        | 1, 0 => ((E X)ᴴ)ᴴ
        | 1, 1 => (1 : Matrix n n ℂ) := by
    fin_cases p <;> fin_cases q
    · simpa using congrArg E (hP'Block 0 0)
    · exact (congrArg E (hP'Block 0 1)).trans (hPos.map_conjTranspose X)
    · exact (congrArg E (hP'Block 1 0)).trans (by simp)
    · exact (congrArg E (hP'Block 1 1)).trans (by simpa using hUnital)
  have hBlock :
      Matrix.reindex e e
        (Matrix.of fun (ip : n × Fin 2) (jq : n × Fin 2) =>
          (E (Matrix.of fun i j => P' (i, ip.2) (j, jq.2))) ip.1 jq.1) =
        Matrix.fromBlocks (E (Xᴴ * X)) ((E X)ᴴ)
          (((E X)ᴴ)ᴴ) (1 : Matrix n n ℂ) := by
    ext ip jq
    rcases ip with i | i <;> rcases jq with j | j
    · convert congr_fun (congr_fun (hEBlock 0 0) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
    · convert congr_fun (congr_fun (hEBlock 0 1) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
    · convert congr_fun (congr_fun (hEBlock 1 0) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
    · convert congr_fun (congr_fun (hEBlock 1 1) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
  have hBlockPsD :
      (Matrix.fromBlocks (E (Xᴴ * X)) ((E X)ᴴ)
        (((E X)ᴴ)ᴴ) (1 : Matrix n n ℂ)).PosSemidef := by
    have hYsum : (Matrix.reindex e e
        (Matrix.of fun (ip : n × Fin 2) (jq : n × Fin 2) =>
          (E (Matrix.of fun i j => P' (i, ip.2) (j, jq.2))) ip.1 jq.1)).PosSemidef := by
      simpa [nPositiveAmpliation, Matrix.reindex_apply] using hY'.submatrix e.symm
    simpa [hBlock] using hYsum
  have : Invertible (1 : Matrix n n ℂ) := invertibleOne
  simpa [inv_one, Matrix.mul_assoc, conjTranspose_conjTranspose] using
    (Matrix.PosDef.fromBlocks₂₂ (A := E (Xᴴ * X)) (B := (E X)ᴴ)
      (D := (1 : Matrix n n ℂ)) Matrix.PosDef.one).1 hBlockPsD
