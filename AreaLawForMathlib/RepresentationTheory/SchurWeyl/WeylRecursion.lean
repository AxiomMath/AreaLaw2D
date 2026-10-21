/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.HookRecursion

/-!
# The Pieri recursion for the Weyl dimension formula

`∑_i W_{λ + e_i} = q W_λ` (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, lines 237–241).
-/

open Finset Polynomial

namespace Partition

variable {q : ℕ}

theorem weylFormula_eq_vand (p : Fin q → ℕ) :
    weylFormula p = vand (fun j => (shiftedPart p j : ℝ)) /
      ∏ ij ∈ rowPairs q, ((ij.2 : ℝ) - ij.1) := by
  rw [weylFormula, prod_div_distrib, vand]

theorem rowPairs_denom_pos : (0 : ℝ) < ∏ ij ∈ rowPairs q, ((ij.2 : ℝ) - ij.1) :=
  prod_pos fun ij hij => sub_pos.mpr (by exact_mod_cast (mem_filter.mp hij).2)

/-- The Weyl dimension formula of the empty partition is one. -/
theorem weylFormula_zero : weylFormula (0 : Fin q → ℕ) = 1 := by
  refine prod_eq_one fun ij hij => ?_
  have hlt : (ij.1 : ℕ) < ij.2 := (mem_filter.mp hij).2
  have hne : ((ij.2 : ℝ) - ij.1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hlt.ne')
  rw [div_eq_one_iff_eq hne]
  simp only [shiftedPart, Pi.zero_apply, zero_add]
  have e : ∀ a : ℕ, a < q → ((q - 1 - a : ℕ) : ℝ) = q - 1 - a := fun a ha => by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e _ ij.1.2, e _ ij.2.2]
  ring

theorem weylFormula_eq_zero_of_shiftedPart_eq (p : Fin q → ℕ) {a b : Fin q} (hab : a < b)
    (h : shiftedPart p a = shiftedPart p b) : weylFormula p = 0 := by
  rw [weylFormula, prod_eq_zero (i := (a, b)) (by simp [rowPairs, hab]) (by simp [h])]

/-- Adding a box to row `i` multiplies the Weyl formula by
`∏_{j ≠ i} (l_i + 1 - l_j)/(l_i - l_j)`, in multiplied-out form. -/
theorem weylFormula_update_add_mul (p : Fin q → ℕ) (i : Fin q) :
    weylFormula (Function.update p i (p i + 1)) *
        ∏ j ∈ univ.erase i, ((shiftedPart p i : ℝ) - shiftedPart p j) =
      weylFormula p * ∏ j ∈ univ.erase i, ((shiftedPart p i : ℝ) + 1 - shiftedPart p j) := by
  set L : Fin q → ℝ := fun j => (shiftedPart p j : ℝ)
  have hsh : (fun j => (shiftedPart (Function.update p i (p i + 1)) j : ℝ)) =
      Function.update L i (L i + 1) := by
    rw [shiftedPart_update]
    funext j
    by_cases hij : j = i
    · subst hij; simp only [Function.update_self, L, shiftedPart]; push_cast; ring
    · simp [hij, L]
  rw [weylFormula_eq_vand, weylFormula_eq_vand, hsh, div_mul_eq_mul_div, vand_update_mul,
    div_mul_eq_mul_div]

end Partition
