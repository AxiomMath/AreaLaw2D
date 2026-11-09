import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import AreaLawForMathlib.Analysis.CStarAlgebra.Matrix

/-!
# Hölder-1/2 continuity of the square root in a C⋆-algebra; Kraus contractions

Extends `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order`.

* `CFC.norm_sqrt_sub_sqrt_le`: `‖√a - √b‖ ≤ √‖a - b‖` for `0 ≤ a, b` in a unital
  C⋆-algebra (no dimension factor).
* `Matrix.norm_mul_mul_add_mul_mul_le`: `‖G B G + K B K‖ ≤ ‖B‖` for Hermitian `G, K` with
  `G * G + K * K = 1`, in the L2 operator norm.

Ported from LionSR/QICLean commit 5f76b263e3a1c418645102d90f7bef6b92f04cf3,
`QICLean/Analysis/SqrtHolder.lean`, as used by LionSR/TNLean commit
fc565830cec69e8226e521d56c86d39845d45576. Adapted to Lean/Mathlib 4.33.
-/

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A self-adjoint element lying between `-c` and `c` has norm at most `c`. -/
theorem norm_le_of_neg_algebraMap_le_of_le_algebraMap {x : A} {c : ℝ} (hc : 0 ≤ c)
    (h₁ : -algebraMap ℝ A c ≤ x) (h₂ : x ≤ algebraMap ℝ A c) : ‖x‖ ≤ c := by
  have hx : IsSelfAdjoint x :=
    (IsSelfAdjoint.algebraMap A (IsSelfAdjoint.all c)).neg.of_ge h₁
  have h₁' : algebraMap ℝ A (-c) ≤ x := by rwa [map_neg]
  rw [← cfc_id' ℝ x]
  refine norm_cfc_le hc fun t ht => ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(algebraMap_le_iff_le_spectrum hx).1 h₁' t ht,
    (le_algebraMap_iff_spectrum_le hx).1 h₂ t ht⟩

/-- `√(b + ε) ≤ √b + √ε` for `0 ≤ b` and `0 ≤ ε`. -/
theorem sqrt_add_algebraMap_le {b : A} (hb : 0 ≤ b) {ε : ℝ} (hε : 0 ≤ ε) :
    sqrt (b + algebraMap ℝ A ε) ≤ sqrt b + algebraMap ℝ A (Real.sqrt ε) := by
  set s := sqrt b
  set c := algebraMap ℝ A (Real.sqrt ε)
  have hs : 0 ≤ s := sqrt_nonneg b
  have hsc : 0 ≤ s * c := by
    rw [← Algebra.commutes, ← Algebra.smul_def]
    exact smul_nonneg (Real.sqrt_nonneg ε) hs
  have hsq : (s + c) * (s + c) = b + algebraMap ℝ A ε + (2 : ℝ) • (s * c) := by
    rw [add_mul, mul_add, mul_add, sqrt_mul_sqrt_self b hb, ← Algebra.commutes, ← map_mul,
      Real.mul_self_sqrt hε, two_smul]
    abel
  calc sqrt (b + algebraMap ℝ A ε) ≤ sqrt ((s + c) * (s + c)) :=
        sqrt_le_sqrt _ _ (hsq ▸ le_add_of_nonneg_right (smul_nonneg zero_le_two hsc))
    _ = s + c := sqrt_mul_self _ (add_nonneg hs (algebraMap_nonneg A (Real.sqrt_nonneg ε)))

/-- One-sided form of the square-root estimate: `√a ≤ √b + √‖a - b‖`. -/
theorem sqrt_le_sqrt_add_sqrt_norm_sub {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sqrt a ≤ sqrt b + algebraMap ℝ A (Real.sqrt ‖a - b‖) := by
  have hab : a ≤ b + algebraMap ℝ A ‖a - b‖ :=
    sub_le_iff_le_add'.1 (ha.isSelfAdjoint.sub hb.isSelfAdjoint).le_algebraMap_norm_self
  exact (sqrt_le_sqrt _ _ hab).trans (sqrt_add_algebraMap_le hb (norm_nonneg _))

/-- D4.9. For all positive semidefinite `U, V` (any dimension):
`‖U^{1/2} - V^{1/2}‖ ≤ ‖U - V‖^{1/2}`. -/
theorem norm_sqrt_sub_sqrt_le {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖sqrt a - sqrt b‖ ≤ Real.sqrt ‖a - b‖ := by
  refine norm_le_of_neg_algebraMap_le_of_le_algebraMap (Real.sqrt_nonneg _) ?_ ?_
  · rw [neg_le_sub_iff_le_add', add_comm, norm_sub_rev]
    exact sqrt_le_sqrt_add_sqrt_norm_sub hb ha
  · exact sub_le_iff_le_add'.2 (sqrt_le_sqrt_add_sqrt_norm_sub ha hb)

end CFC

open scoped Matrix Kronecker Matrix.Norms.L2Operator

namespace Matrix

open Arealaw

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Kraus contraction.** If `G` and `K` are Hermitian with `G * G + K * K = 1`, then
`B ↦ G * B * G + K * B * K` does not increase the L2 operator norm. -/
theorem norm_mul_mul_add_mul_mul_le {G K : Matrix n n ℂ} (hG : G.IsHermitian)
    (hK : K.IsHermitian) (h : G * G + K * K = 1) (B : Matrix n n ℂ) :
    ‖G * B * G + K * B * K‖ ≤ ‖B‖ := by
  let W : Fin 2 → Matrix n n ℂ := ![G, K]
  let V : Matrix (n × Fin 2) n ℂ := Matrix.of fun p j => W p.2 p.1 j
  have hsum : ∀ X : Matrix n n ℂ, G * X * G + K * X * K = ∑ c, (W c)ᴴ * X * W c := by
    intro X; simp [W, Fin.sum_univ_two, hG.eq, hK.eq]
  have hV : Vᴴ * V = 1 := by
    have h1 := hsum 1
    simp only [Matrix.mul_one] at h1
    rw [← h, h1]
    ext i j
    simp only [V, mul_apply, conjTranspose_apply, of_apply, Fintype.sum_prod_type, sum_apply]
    exact Finset.sum_comm
  have hcomp : Vᴴ * (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * V = G * B * G + K * B * K := by
    rw [hsum]
    ext i j
    simp only [V, mul_apply, conjTranspose_apply, of_apply, Fintype.sum_prod_type, sum_apply,
      kroneckerMap_apply, one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hVn : ‖V‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self hV
  rw [← hcomp]
  calc ‖Vᴴ * (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * V‖
      ≤ ‖Vᴴ‖ * ‖B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ * ‖V‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖B‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        gcongr
        exact l2_opNorm_kronecker_one_le B
    _ = ‖B‖ := by ring

end Matrix
