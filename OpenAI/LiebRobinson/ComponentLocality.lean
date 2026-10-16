/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
TNLean/Circuit/LiebRobinson/ComponentLocality.lean. Apache 2.0; adapted to the
`OpenAI.IsSupportedOn` finite-region support predicate and Lean/Mathlib 4.33.
-/
import OpenAI.LiebRobinson.CommutatorRecursion
import OpenAI.HermitianUnitaryPath
import OpenAI.RegionLift

/-!
# Exact locality on interaction-closed regions

If every interaction support lies inside a region or is disjoint from it, Heisenberg
evolution preserves exact commutation with observables on a disjoint region.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Arealaw NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

namespace OpenAI.LiebRobinson

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  {U C D : Finset σ}

/-- If every interaction support lies inside `C` or is disjoint from `C`, the
Heisenberg evolution of an operator supported on `C` commutes with every operator
supported on a disjoint region `D`, at every time. -/
theorem commute_heisenbergEvolution_of_closed {κ : Type*} [Fintype κ]
    (hC : C ⊆ U) (hD : D ⊆ U)
    (h : κ → Matrix (Reg loc U) (Reg loc U) ℂ)
    (T : κ → Finset σ) (hT : ∀ j, T j ⊆ U)
    (hSupport : ∀ j, OpenAI.IsSupportedOn (hT j) (h j))
    (hClosed : ∀ j, T j ⊆ C ∨ Disjoint (T j) C) (hCD : Disjoint C D)
    {A B : Matrix (Reg loc U) (Reg loc U) ℂ}
    (hA : OpenAI.IsSupportedOn hC A) (hB : OpenAI.IsSupportedOn hD B) (t : ℝ) :
    Commute (Matrix.hermitianUnitaryPath (∑ j, h j) t * A *
      Matrix.hermitianUnitaryPath (∑ j, h j) (-t)) B := by
  classical
  let : NormedAlgebra ℚ (Matrix (Reg loc U) (Reg loc U) ℂ) :=
    .restrictScalars ℚ ℝ (Matrix (Reg loc U) (Reg loc U) ℂ)
  let HC := ∑ j, if T j ⊆ C then h j else 0
  let HO := ∑ j, if T j ⊆ C then 0 else h j
  let SC : Submodule ℂ (Matrix (Reg loc U) (Reg loc U) ℂ) :=
    { carrier := {M | OpenAI.IsSupportedOn hC M}
      zero_mem' := OpenAI.isSupportedOn_zero hC
      add_mem' := fun hM hN => hM.add hN
      smul_mem' := fun c _ hM => hM.smul c }
  have hHC : HC ∈ SC := by
    refine Submodule.sum_mem _ fun j _ => ?_
    split_ifs with hj
    · exact (hSupport j).mono hj hC
    · exact Submodule.zero_mem _
  have hHOcomm : ∀ M ∈ SC, Commute HO M := by
    intro M hM
    refine Commute.sum_left _ _ _ fun j _ => ?_
    split_ifs with hj
    · exact Commute.zero_left _
    · exact (hSupport j).commute hM ((hClosed j).resolve_left hj)
  have hSplit : ∑ j, h j = HC + HO := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hCO : Commute HC HO := (hHOcomm HC hHC).symm
  have hpath (s : ℝ) : Matrix.hermitianUnitaryPath (∑ j, h j) s =
      Matrix.hermitianUnitaryPath HC s * Matrix.hermitianUnitaryPath HO s := by
    unfold Matrix.hermitianUnitaryPath
    rw [hSplit, smul_add, smul_add]
    exact exp_add_of_commute
      ((hCO.smul_left _).smul_right _ |>.smul_left _ |>.smul_right _)
  have hOA (s : ℝ) : Commute (Matrix.hermitianUnitaryPath HO s) A := by
    unfold Matrix.hermitianUnitaryPath
    exact (((hHOcomm A hA).smul_left Complex.I).smul_left s).exp_left
  have hCB : Commute HC B := hHC.commute hB hCD
  have hCB' (s : ℝ) : Commute (Matrix.hermitianUnitaryPath HC s) B := by
    unfold Matrix.hermitianUnitaryPath
    exact ((hCB.smul_left Complex.I).smul_left s).exp_left
  have hAB : Commute A B := hA.commute hB hCD
  have hEq : Matrix.hermitianUnitaryPath (∑ j, h j) t * A *
      Matrix.hermitianUnitaryPath (∑ j, h j) (-t) =
      Matrix.hermitianUnitaryPath HC t * A * Matrix.hermitianUnitaryPath HC (-t) := by
    rw [hpath, hpath]
    have hcancel : Matrix.hermitianUnitaryPath HO t *
        Matrix.hermitianUnitaryPath HO (-t) = 1 := by
      rw [← Matrix.hermitianUnitaryPath_add]
      simp
    calc
      Matrix.hermitianUnitaryPath HC t * Matrix.hermitianUnitaryPath HO t * A *
          (Matrix.hermitianUnitaryPath HC (-t) * Matrix.hermitianUnitaryPath HO (-t)) =
          Matrix.hermitianUnitaryPath HC t * A *
            (Matrix.hermitianUnitaryPath HO t * Matrix.hermitianUnitaryPath HO (-t)) *
              Matrix.hermitianUnitaryPath HC (-t) := by
        rw [mul_assoc (Matrix.hermitianUnitaryPath HC t), (hOA t).eq]
        have hc : Commute (Matrix.hermitianUnitaryPath HC (-t))
            (Matrix.hermitianUnitaryPath HO (-t)) := by
          unfold Matrix.hermitianUnitaryPath
          exact ((((hCO.smul_left Complex.I).smul_right Complex.I).smul_left (-t)).smul_right
            (-t)).exp
        rw [hc.eq]
        noncomm_ring
      _ = _ := by rw [hcancel, mul_one]
  rw [hEq]
  exact ((hCB' t).mul_left hAB).mul_left (hCB' (-t))

end OpenAI.LiebRobinson
