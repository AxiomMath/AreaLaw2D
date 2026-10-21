import AreaLawForMathlib.Analysis.Matrix.OrthogonalResolutionCfc
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vector estimates for projections, products and normalization

Extends `Mathlib/Analysis/Matrix/PosDef.lean`.

Elementary facts about complex vectors and matrices: quadratic forms of Hermitian idempotents,
invariance of a submodule under a product of matrices, absorption of a commuting idempotent
into a product, norm bounds for ordered products, normalization of a nonzero vector, a crude
entrywise bound for quadratic forms, and quadratic forms of real functions of an orthogonal
resolution. Also two limits of real sequences: `(k + 1)^a e^{-b k} → 0` and
`log (k + b) / k → 0`.
-/

open scoped Matrix ComplexOrder
open Filter Topology

namespace Real

theorem tendsto_natCast_add_one_rpow_mul_exp_neg (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ a * Real.exp (-(b * k))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a b hb).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 := h.const_mul (Real.exp b)
  rw [mul_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem tendsto_log_natCast_add_div (b : ℝ) :
    Tendsto (fun k : ℕ => Real.log ((k : ℝ) + b) / k) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-b) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right _ b tendsto_natCast_atTop_atTop)
  refine h.congr fun k => ?_
  simp only [Function.comp, pow_one, one_mul]
  ring_nf

end Real

namespace Matrix

theorem star_mulVec_dotProduct_of_idem {m : Type*} [Fintype m] {M : Matrix m m ℂ}
    (hM : M.IsHermitian) (hMM : M * M = M) (v : m → ℂ) :
    star (M *ᵥ v) ⬝ᵥ v = star (M *ᵥ v) ⬝ᵥ (M *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hM.eq, hMM]

theorem star_dotProduct_self_eq_re {m : Type*} [Fintype m] (v : m → ℂ) :
    star v ⬝ᵥ v = ((star v ⬝ᵥ v).re : ℂ) := by
  refine Complex.ext rfl ?_
  simp only [Complex.ofReal_im, dotProduct, Pi.star_apply, Complex.im_sum]
  exact Finset.sum_eq_zero fun i _ => by
    rw [Complex.star_def, mul_comm, Complex.mul_conj]; simp

theorem list_prod_mulVec_mem {m : Type*} [Fintype m] [DecidableEq m] (S : Submodule ℂ (m → ℂ))
    (Ps : List (Matrix m m ℂ)) (h : ∀ P ∈ Ps, ∀ v ∈ S, P *ᵥ v ∈ S) {v : m → ℂ} (hv : v ∈ S) :
    Ps.prod *ᵥ v ∈ S := by
  induction Ps with
  | nil => simpa using hv
  | cons P Ps ih =>
    rw [List.prod_cons, ← mulVec_mulVec]
    exact h P List.mem_cons_self _ (ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))

theorem mul_list_prod_of_mem {m : Type*} [Fintype m] [DecidableEq m] {P : Matrix m m ℂ}
    (hPP : P * P = P) (Ps : List (Matrix m m ℂ)) (hP : P ∈ Ps)
    (hc : ∀ Q ∈ Ps, Commute P Q) : P * Ps.prod = Ps.prod := by
  induction Ps with
  | nil => simp at hP
  | cons Q Qs ih =>
    rw [List.prod_cons]
    rcases List.mem_cons.mp hP with rfl | hP'
    · rw [← mul_assoc, hPP]
    · rw [← mul_assoc, (hc Q List.mem_cons_self).eq, mul_assoc,
        ih hP' fun R hR => hc R (List.mem_cons_of_mem _ hR)]

theorem listProd_ofFn_mulVec_eq {m : Type*} [Fintype m] [DecidableEq m] {K : ℕ}
    (A B : Fin K → Matrix m m ℂ) (p : (m → ℂ) → Prop)
    (hAB : ∀ g φ, p φ → A g *ᵥ φ = B g *ᵥ φ) (hB : ∀ g φ, p φ → p (B g *ᵥ φ)) :
    ∀ φ, p φ → (List.ofFn A).prod *ᵥ φ = (List.ofFn B).prod *ᵥ φ ∧
      p ((List.ofFn B).prod *ᵥ φ) := by
  induction K with
  | zero =>
    intro φ hφ
    refine ⟨by simp, by simpa using hφ⟩
  | succ K ih =>
    intro φ hφ
    obtain ⟨h1, h2⟩ := ih (fun g => A g.succ) (fun g => B g.succ) (fun g => hAB g.succ)
      (fun g => hB g.succ) φ hφ
    simp only [List.ofFn_succ, List.prod_cons, ← mulVec_mulVec]
    rw [h1, hAB 0 _ h2]
    exact ⟨rfl, hB 0 _ h2⟩

theorem listProd_ofFn_nsq_le {m : Type*} [Fintype m] [DecidableEq m] {K : ℕ}
    (B : Fin K → Matrix m m ℂ) (p : (m → ℂ) → Prop) {M : ℝ}
    (hp : ∀ g φ, p φ → p (B g *ᵥ φ))
    (hB : ∀ g φ, p φ → (star (B g *ᵥ φ) ⬝ᵥ (B g *ᵥ φ)).re ≤ M ^ 2 * (star φ ⬝ᵥ φ).re) :
    ∀ φ, p φ → (star ((List.ofFn B).prod *ᵥ φ) ⬝ᵥ ((List.ofFn B).prod *ᵥ φ)).re ≤
      (M ^ K) ^ 2 * (star φ ⬝ᵥ φ).re ∧ p ((List.ofFn B).prod *ᵥ φ) := by
  induction K with
  | zero =>
    intro φ hφ
    refine ⟨by simp, by simpa using hφ⟩
  | succ K ih =>
    intro φ hφ
    obtain ⟨h1, h2⟩ := ih (fun g => B g.succ) (fun g => hp g.succ) (fun g => hB g.succ) φ hφ
    simp only [List.ofFn_succ, List.prod_cons, ← mulVec_mulVec]
    refine ⟨(hB 0 _ h2).trans ?_, hp 0 _ h2⟩
    calc M ^ 2 * _ ≤ M ^ 2 * ((M ^ K) ^ 2 * (star φ ⬝ᵥ φ).re) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg M)
      _ = (M ^ (K + 1)) ^ 2 * (star φ ⬝ᵥ φ).re := by ring

/-- A crude bound: `⟨φ, A φ⟩ ≤ ∑_{y,y'} |A_{y y'}|` for a unit `φ`. -/
theorem re_dotProduct_mulVec_le_sum_norm {m : Type*} [Fintype m] (A : Matrix m m ℂ)
    {φ : m → ℂ} (hφ : star φ ⬝ᵥ φ = 1) : (star φ ⬝ᵥ (A *ᵥ φ)).re ≤ ∑ y, ∑ y', ‖A y y'‖ := by
  have hsum : ∑ z, ‖φ z‖ ^ 2 = 1 := by
    have h := congrArg Complex.re hφ
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.one_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  have hφy : ∀ y, ‖φ y‖ ≤ 1 := fun y => by
    have h := Finset.single_le_sum (fun z _ => sq_nonneg ‖φ z‖) (Finset.mem_univ y)
    rw [hsum] at h
    nlinarith [norm_nonneg (φ y)]
  refine (Complex.re_le_norm _).trans ?_
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul, norm_star]
  calc ‖φ y‖ * ‖∑ y', A y y' * φ y'‖ ≤ 1 * ∑ y', ‖A y y' * φ y'‖ :=
        mul_le_mul (hφy y) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ ∑ y', ‖A y y'‖ := by
        rw [one_mul]
        refine Finset.sum_le_sum fun y' _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hφy y')

/-- Normalizing a nonzero vector `y`: `φ = y/‖y‖` is a unit vector with `|⟨φ, y⟩|² = ‖y‖²`. -/
theorem normalize_spec {m : Type*} [Fintype m] (y : m → ℂ) (hy : 0 < (star y ⬝ᵥ y).re) :
    star ((((Real.sqrt (star y ⬝ᵥ y).re)⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ
        ((((Real.sqrt (star y ⬝ᵥ y).re)⁻¹ : ℝ) : ℂ) • y) = 1 ∧
      ‖star ((((Real.sqrt (star y ⬝ᵥ y).re)⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ y‖ ^ 2 =
        (star y ⬝ᵥ y).re := by
  set r := Real.sqrt (star y ⬝ᵥ y).re
  have hr : 0 < r := Real.sqrt_pos.mpr hy
  have hrr : r * r = (star y ⬝ᵥ y).re := Real.mul_self_sqrt hy.le
  constructor
  · rw [star_smul, smul_dotProduct, dotProduct_smul, star_dotProduct_self_eq_re y,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul, ← hrr]
    push_cast
    field_simp
  · rw [star_smul, smul_dotProduct, star_dotProduct_self_eq_re y, ← hrr, Complex.star_def,
      Complex.conj_ofReal, smul_eq_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), abs_of_pos (mul_pos hr hr),
      mul_pow]
    field_simp
    exact (Complex.ofReal_re _).symm

theorem exists_mul_mul_ne_zero_of_sum_eq_one {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι]
    (P R : Matrix m m ℂ) (E : ι → Matrix m m ℂ)
    (hE : ∑ μ, E μ = 1) (h : P * R ≠ 0) : ∃ μ, P * E μ * R ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [← mul_one P, ← hE, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_eq_zero fun μ _ => hc μ

/-- `⟨P v, A P v⟩ ≤ ⟨v, A v⟩` for a Hermitian idempotent `P` commuting with `A ≥ 0`. -/
theorem re_dotProduct_proj_mulVec_le {m : Type*} [Fintype m] {P A : Matrix m m ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hA : A.PosSemidef) (hc : Commute P A) (v : m → ℂ) :
    (star (P *ᵥ v) ⬝ᵥ (A *ᵥ (P *ᵥ v))).re ≤ (star v ⬝ᵥ (A *ᵥ v)).re := by
  classical
  have hQ : (1 - P).IsHermitian := isHermitian_one.sub hP
  have hcross : star (P *ᵥ v) ⬝ᵥ (A *ᵥ ((1 - P) *ᵥ v)) = 0 := by
    rw [star_mulVec, hP.eq, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hc.eq,
      mul_assoc, mul_sub, mul_one, hPP, sub_self, mul_zero, zero_mulVec, dotProduct_zero]
  have hcross' : star ((1 - P) *ᵥ v) ⬝ᵥ (A *ᵥ (P *ᵥ v)) = 0 := by
    rw [star_mulVec, hQ.eq, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
      ((Commute.one_left A).sub_left hc).eq, mul_assoc, sub_mul, one_mul, hPP, sub_self,
      mul_zero, zero_mulVec, dotProduct_zero]
  have hv : v = P *ᵥ v + (1 - P) *ᵥ v := by rw [sub_mulVec, one_mulVec]; abel
  have h0 : 0 ≤ (star ((1 - P) *ᵥ v) ⬝ᵥ (A *ᵥ ((1 - P) *ᵥ v))).re :=
    hA.re_dotProduct_nonneg ((1 - P) *ᵥ v)
  conv_rhs => rw [hv]
  rw [mulVec_add, star_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross, hcross',
    add_zero, zero_add, Complex.add_re]
  linarith

theorem re_star_smul_dotProduct_smul {m : Type*} [Fintype m] (c : ℝ) (v w : m → ℂ) :
    (star ((c : ℂ) • v) ⬝ᵥ ((c : ℂ) • w)).re = c ^ 2 * (star v ⬝ᵥ w).re := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, Complex.star_def, Complex.conj_ofReal,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul, sq]

theorem IsOrthogonalResolution.re_star_dotProduct_hom_ofReal_mulVec {m ι : Type*} [Fintype m]
    [DecidableEq m] [Fintype ι] [DecidableEq ι] {P : ι → Matrix m m ℂ}
    (hP : IsOrthogonalResolution P) (F : ι → ℝ) (v : m → ℂ) :
    (star v ⬝ᵥ (hP.hom (fun i => (F i : ℂ)) *ᵥ v)).re =
      ∑ i, F i * IsOrthogonalResolution.weight (P := P) v i := by
  rw [hP.hom_apply, sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rfl

end Matrix
