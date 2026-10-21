import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
# Products of commuting orthogonal projections

Extends `Mathlib/LinearAlgebra/Matrix/Hermitian.lean`. For a Hermitian idempotent `P`,
`‖x‖² = ‖P x‖² + ‖(1 - P) x‖²`, so `P` is a contraction; a product of pairwise commuting
Hermitian idempotents is again one, and `‖x‖² ≤ ‖(∏ P_i) x‖² + ∑_i ‖(1 - P_i) x‖²` (the
complement of a common range is covered by the complements of the ranges).
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `‖x‖² = ‖P x‖² + ‖(1 - P) x‖²` for a Hermitian idempotent `P`. -/
theorem IsHermitian.re_dotProduct_self_eq_of_idem {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (x : n → ℂ) :
    (star x ⬝ᵥ x).re = (star (P *ᵥ x) ⬝ᵥ (P *ᵥ x)).re +
      (star ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x)).re := by
  have hcross : star (P *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) = 0 := by
    rw [star_mulVec, hP.eq, ← dotProduct_mulVec, mulVec_mulVec, mul_sub,
      mul_one, hPP, sub_self, zero_mulVec, dotProduct_zero]
  have hcross' : star ((1 - P) *ᵥ x) ⬝ᵥ (P *ᵥ x) = 0 := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_sub, conjTranspose_one,
      hP.eq, sub_mul, one_mul, hPP, sub_self, zero_mulVec, dotProduct_zero]
  have hx : x = P *ᵥ x + (1 - P) *ᵥ x := by rw [sub_mulVec, one_mulVec]; abel
  conv_lhs => rw [hx]
  rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross, hcross', add_zero,
    zero_add, Complex.add_re]

omit [DecidableEq n] in
/-- A Hermitian idempotent is a contraction: `‖P x‖² ≤ ‖x‖²`. -/
theorem IsHermitian.re_dotProduct_mulVec_self_le_of_idem {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (x : n → ℂ) :
    (star (P *ᵥ x) ⬝ᵥ (P *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
  classical
  rw [hP.re_dotProduct_self_eq_of_idem hPP x, le_add_iff_nonneg_right]
  exact (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1

/-- A product of pairwise commuting Hermitian idempotents is a Hermitian idempotent. -/
theorem list_prod_isHermitian_idem (Ps : List (Matrix n n ℂ))
    (h : ∀ P ∈ Ps, P.IsHermitian ∧ P * P = P) (hc : ∀ P ∈ Ps, ∀ Q ∈ Ps, Commute P Q) :
    Ps.prod.IsHermitian ∧ Ps.prod * Ps.prod = Ps.prod := by
  induction Ps with
  | nil => simp [isHermitian_one]
  | cons P Qs ih =>
    obtain ⟨hQh, hQQ⟩ := ih (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ R hR => hc Q (List.mem_cons_of_mem _ hQ) R (List.mem_cons_of_mem _ hR))
    obtain ⟨hPh, hPP⟩ := h P List.mem_cons_self
    have hPQ : Commute P Qs.prod := Commute.list_prod_right _ _ fun Q hQ =>
      hc P List.mem_cons_self Q (List.mem_cons_of_mem _ hQ)
    rw [List.prod_cons]
    refine ⟨?_, ?_⟩
    · rw [IsHermitian, conjTranspose_mul, hPh.eq, hQh.eq, hPQ.eq]
    · rw [mul_assoc, ← mul_assoc Qs.prod, ← hPQ.eq, mul_assoc, hQQ, ← mul_assoc, hPP]

/-- `‖x‖² ≤ ‖(∏ P_i) x‖² + ∑_i ‖(1 - P_i) x‖²` for pairwise commuting Hermitian idempotents. -/
theorem re_dotProduct_self_le_list_prod (Ps : List (Matrix n n ℂ))
    (h : ∀ P ∈ Ps, P.IsHermitian ∧ P * P = P) (hc : ∀ P ∈ Ps, ∀ Q ∈ Ps, Commute P Q)
    (x : n → ℂ) :
    (star x ⬝ᵥ x).re ≤ (star (Ps.prod *ᵥ x) ⬝ᵥ (Ps.prod *ᵥ x)).re +
      (Ps.map fun P => (star ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x)).re).sum := by
  induction Ps with
  | nil => simp
  | cons P Qs ih =>
    have hQs : ∀ Q ∈ Qs, Q.IsHermitian ∧ Q * Q = Q := fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)
    have hcQs : ∀ Q ∈ Qs, ∀ R ∈ Qs, Commute Q R :=
      fun Q hQ R hR => hc Q (List.mem_cons_of_mem _ hQ) R (List.mem_cons_of_mem _ hR)
    obtain ⟨hQh, hQQ⟩ := list_prod_isHermitian_idem Qs hQs hcQs
    obtain ⟨hPh, hPP⟩ := h P List.mem_cons_self
    have hPQ : Commute P Qs.prod := Commute.list_prod_right _ _ fun Q hQ =>
      hc P List.mem_cons_self Q (List.mem_cons_of_mem _ hQ)
    have h1 := ih hQs hcQs
    have h2 := hPh.re_dotProduct_self_eq_of_idem hPP (Qs.prod *ᵥ x)
    have h3 : (1 - P) *ᵥ (Qs.prod *ᵥ x) = Qs.prod *ᵥ ((1 - P) *ᵥ x) := by
      rw [mulVec_mulVec, mulVec_mulVec, ((Commute.one_left _).sub_left hPQ).eq]
    have h4 := hQh.re_dotProduct_mulVec_self_le_of_idem hQQ ((1 - P) *ᵥ x)
    rw [h3] at h2
    rw [List.prod_cons, ← mulVec_mulVec, List.map_cons, List.sum_cons]
    linarith

end Matrix
