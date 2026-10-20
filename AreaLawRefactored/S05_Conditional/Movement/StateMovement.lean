import AreaLawRefactored.S05_Conditional.Movement.Setup
import AreaLawRefactored.S05_Conditional.Lemma52

/-!
# §5.1 D5.8–D5.9: phases are Hellinger-continuous, and the state movement

Digest `digest/05-conditional.md`, D5.8 and D5.9. `step_5_8_matrix` sums the termwise
`step_5_8` in the two eigenbases with the overlap weights `ovl`; `step_5_9_of` derives the
matrix-level state movement `Step_5_9` from `Step_5_2`.
-/

namespace AreaLaw

open Arealaw Matrix Complex Conditional
open scoped ComplexOrder MatrixOrder

universe u

namespace Conditional.Mov

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem ovl_swap {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    ovl hA hB i j = ovl hB hA j i := by
  simp only [ovl]
  rw [← Complex.normSq_conj, show star (hB.eigenvectorUnitary : Matrix n n ℂ) *
      (hA.eigenvectorUnitary : Matrix n n ℂ) = star (star (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.eigenvectorUnitary : Matrix n n ℂ)) by rw [star_mul, star_star], Matrix.star_apply]
  rfl

/-- `‖(f(A) − g(B)) h(B)‖₂² = ∑_{ij} |f(α_i) − g(β_j)|² |h(β_j)|² |⟨v_i, w_j⟩|²`. -/
theorem re_trace_hs_specFun {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g h : ℝ → ℂ) :
    ((((specFun hA f - specFun hB g) * specFun hB h)ᴴ *
        ((specFun hA f - specFun hB g) * specFun hB h)).trace).re =
      ∑ i, ∑ j, ‖f (hA.eigenvalues i) - g (hB.eigenvalues j)‖ ^ 2 *
        ‖h (hB.eigenvalues j)‖ ^ 2 * ovl hA hB i j := by
  set k := h * star h
  have key := trace_specFun_mul_specFun hA hB
  have key1 (ψ : ℝ → ℂ) : (specFun hB ψ).trace =
      ∑ i, ∑ j, (1 : ℝ → ℂ) (hA.eigenvalues i) * ψ (hB.eigenvalues j) * (ovl hA hB i j : ℂ) := by
    rw [← key, specFun_one, Matrix.one_mul]
  have hk : specFun hB h * (specFun hB h)ᴴ = specFun hB k := by
    rw [← star_eq_conjTranspose, star_specFun, specFun_mul]
  have e : (((specFun hA f - specFun hB g) * specFun hB h)ᴴ *
      ((specFun hA f - specFun hB g) * specFun hB h)).trace =
      (specFun hA (star f) * (specFun hA f * specFun hB k)).trace -
        (specFun hB (star g) * (specFun hA f * specFun hB k)).trace -
        ((specFun hA (star f) * (specFun hB g * specFun hB k)).trace -
          (specFun hB (star g) * (specFun hB g * specFun hB k)).trace) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      hk, conjTranspose_sub, ← star_eq_conjTranspose, ← star_eq_conjTranspose, star_specFun,
      star_specFun]
    simp only [Matrix.sub_mul, Matrix.mul_sub, trace_sub]
  have t1 : (specFun hA (star f) * (specFun hA f * specFun hB k)).trace =
      (specFun hA (star f * f) * specFun hB k).trace := by rw [← Matrix.mul_assoc, specFun_mul]
  have t2 : (specFun hB (star g) * (specFun hA f * specFun hB k)).trace =
      (specFun hA f * specFun hB (k * star g)).trace := by
    rw [trace_mul_comm, Matrix.mul_assoc, specFun_mul]
  rw [e, t1, t2, specFun_mul, specFun_mul, key, key, key, key1]
  simp only [← Finset.sum_sub_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hn : ‖f (hA.eigenvalues i) - g (hB.eigenvalues j)‖ ^ 2 * ‖h (hB.eigenvalues j)‖ ^ 2 *
      ovl hA hB i j = ((f (hA.eigenvalues i) - g (hB.eigenvalues j)) *
        (starRingEnd ℂ) (f (hA.eigenvalues i) - g (hB.eigenvalues j)) *
        (h (hB.eigenvalues j) * (starRingEnd ℂ) (h (hB.eigenvalues j))) *
        (ovl hA hB i j : ℂ)).re := by
    rw [Complex.mul_conj', Complex.mul_conj']; norm_cast
  rw [hn]
  congr 1
  simp only [k, Pi.mul_apply, Pi.star_apply, Pi.one_apply, RCLike.star_def, map_sub]
  ring

/-- `ρ̂^{ic}` at an eigenvalue `t ≥ 0` is the phase `e^{i c log t}` (`= 1` at `t = 0`). -/
theorem hfun_mul_I (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    hfun ((c : ℂ) * I) t = Complex.exp (I * ((c * Real.log t : ℝ) : ℂ)) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [hfun]
  · rw [hfun_of_pos ht]; congr 1; push_cast; ring

theorem norm_phase_sub_le (x y : ℝ) :
    ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ |x - y| ∧
      ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ 2 := by
  refine ⟨?_, (norm_sub_le _ _).trans (by
    rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num)⟩
  have : Complex.exp (I * x) - Complex.exp (I * y) =
      Complex.exp (I * y) * (Complex.exp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem norm_hs_unitary_mul {V : Matrix n n ℂ} (hV : V ∈ unitary (Matrix n n ℂ))
    (Y : Matrix n n ℂ) : ‖hs (V * Y)‖ = ‖hs Y‖ := by
  have hV' : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  rw [norm_hs, norm_hs, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV',
    Matrix.one_mul]

theorem norm_hs_unitary_sub_mul {V W : Matrix n n ℂ} (hV : V ∈ unitary (Matrix n n ℂ))
    (hW : W ∈ unitary (Matrix n n ℂ)) (Y : Matrix n n ℂ) :
    ‖hs ((V - W) * Y)‖ ≤ 2 * ‖hs Y‖ := by
  rw [Matrix.sub_mul, hs_sub, two_mul]
  exact (norm_sub_le _ _).trans (by rw [norm_hs_unitary_mul hV, norm_hs_unitary_mul hW])

theorem sq_norm_hfun_sub_le (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖hfun ((c : ℂ) * I) s - hfun ((c : ℂ) * I) t‖ ^ 2 ≤ c ^ 2 * (Real.log s - Real.log t) ^ 2 ∧
      ‖hfun ((c : ℂ) * I) s - hfun ((c : ℂ) * I) t‖ ^ 2 ≤ 4 := by
  rw [hfun_mul_I c hs, hfun_mul_I c ht]
  obtain ⟨h1, h2⟩ := norm_phase_sub_le (c * Real.log s) (c * Real.log t)
  have h1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [sq_abs] at h1
  exact ⟨h1.trans_eq (by ring), h2.trans_eq (by norm_num)⟩

/-- D5.9.5–6, pointwise: a phase `0 ≤ φ ≤ min(4, (auv)²)` is at most
`16 (1+u²) (1 − e^{2av} + 4a e^v)` for `0 < a ≤ 1/4`. -/
theorem slack_scalar {a u v φ : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hφ4 : φ ≤ 4)
    (hφ : φ ≤ (a * u * v) ^ 2) :
    φ ≤ 16 * (1 + u ^ 2) * (1 - Real.exp (2 * a * v) + 4 * a * Real.exp v) := by
  have hev := mul_pos ha (Real.exp_pos v)
  have hu2 := sq_nonneg u
  rcases le_or_gt v 0 with hv | hv
  · -- D5.9.5, `y = -2av ≥ 0`
    have hE : Real.exp (2 * a * v) * (1 + -(2 * a * v)) ≤ 1 := by
      have h2 : Real.exp (2 * a * v) * Real.exp (-(2 * a * v)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [Real.add_one_le_exp (-(2 * a * v)), Real.exp_pos (2 * a * v)]
    have h0 : 0 ≤ 1 - Real.exp (2 * a * v) := by
      linarith [Real.exp_le_one_iff.2 (by nlinarith : 2 * a * v ≤ 0)]
    have hy : 0 ≤ -(2 * a * v) := by nlinarith
    have hR : 16 * (1 - Real.exp (2 * a * v)) ≤
        16 * (1 + u ^ 2) * (1 - Real.exp (2 * a * v) + 4 * a * Real.exp v) := by
      nlinarith [mul_nonneg hu2 h0]
    rcases le_or_gt (-(2 * a * v)) 1 with hy1 | hy1
    · have h1E : -(2 * a * v) ≤ 2 * (1 - Real.exp (2 * a * v)) := by
        nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - -(2 * a * v))]
      have hy2 : (-(2 * a * v)) ^ 2 ≤ -(2 * a * v) := by nlinarith
      have : (a * u * v) ^ 2 ≤ u ^ 2 * (1 - Real.exp (2 * a * v)) := by
        nlinarith [mul_le_mul_of_nonneg_left hy2 hu2, mul_le_mul_of_nonneg_left h1E hu2]
      nlinarith [mul_nonneg (mul_nonneg hu2 h0) hu2]
    · have : 1 ≤ 2 * (1 - Real.exp (2 * a * v)) := by nlinarith
      linarith
  · -- D5.9.6
    have hcvx : Real.exp (2 * a * v) ≤ 1 - 2 * a + 2 * a * Real.exp v := by
      have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ v)
        (by linarith : (0 : ℝ) ≤ 1 - 2 * a) (by linarith : (0 : ℝ) ≤ 2 * a) (by ring)
      simpa [smul_eq_mul] using this
    have hv2 : v ^ 2 ≤ 4 * Real.exp v := by
      have h := Real.add_one_le_exp (v / 2)
      have : Real.exp v = Real.exp (v / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
      nlinarith
    have h1 : (a * u * v) ^ 2 ≤ 4 * a ^ 2 * u ^ 2 * Real.exp v := by
      have := mul_le_mul_of_nonneg_left hv2 (by positivity : 0 ≤ a ^ 2 * u ^ 2)
      linarith [show (a * u * v) ^ 2 = a ^ 2 * u ^ 2 * v ^ 2 by ring]
    have h2 : 4 * a ^ 2 * u ^ 2 * Real.exp v ≤ u ^ 2 * (a * Real.exp v) := by
      have := mul_le_mul_of_nonneg_right ha4 (mul_nonneg hu2 hev.le)
      nlinarith
    have h3 : 2 * (a * Real.exp v) ≤ 1 - Real.exp (2 * a * v) + 4 * a * Real.exp v := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 16 * (1 + u ^ 2))]

/-- D5.9.5–6 at a pair of eigenvalues `p ≥ 0` of `ξ`, `q > 0` of `τ`:
`p |q̂^{-iau} − p̂^{-iau}|² ≤ 16 (1+u²) (p − q^{2a} p^{1-2a} + 4a q)`. -/
theorem phase_slack {a u p q : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hp : 0 ≤ p) (hq : 0 < q) :
    ‖hfun (((-(a * u) : ℝ) : ℂ) * I) q - hfun (((-(a * u) : ℝ) : ℂ) * I) p‖ ^ 2 *
        ‖((√p : ℝ) : ℂ)‖ ^ 2 ≤
      16 * (1 + u ^ 2) * (p - q ^ (2 * a) * p ^ (1 - 2 * a) + 4 * a * q) := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp]
  obtain ⟨h1, h2⟩ := sq_norm_hfun_sub_le (-(a * u)) hq.le hp
  rcases hp.eq_or_lt with rfl | hp
  · simp only [Real.zero_rpow (by linarith : 1 - 2 * a ≠ 0), mul_zero, sub_zero, zero_add]
    positivity
  have hqv : 4 * a * q = 4 * a * (p * Real.exp (Real.log q - Real.log p)) := by
    rw [Real.exp_sub, Real.exp_log hq, Real.exp_log hp, mul_div_cancel₀ _ hp.ne']
  have hrpow : q ^ (2 * a) * p ^ (1 - 2 * a) =
      p * Real.exp (2 * a * (Real.log q - Real.log p)) := by
    rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hp, ← Real.exp_add,
      show p * Real.exp (2 * a * (Real.log q - Real.log p)) = Real.exp (Real.log p) *
        Real.exp (2 * a * (Real.log q - Real.log p)) by rw [Real.exp_log hp], ← Real.exp_add]
    congr 1
    ring
  have hs := slack_scalar (u := u) (v := Real.log q - Real.log p) ha ha4 h2 (h1.trans_eq (by ring))
  rw [mul_comm, hrpow, hqv]
  exact (mul_le_mul_of_nonneg_left hs hp.le).trans_eq (by ring)

end Conditional.Mov

open Conditional.Mov

/-- D5.8 (`eq:conditional-phase-hellinger`). For `A, B ≥ 0` (density matrices) and real `b`:
`‖(Â^{ib} − B̂^{ib}) √B‖₂ ≤ C (1+|b|) ‖√A − √B‖₂`, with `C = 4`. -/
theorem step_5_8_matrix {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (b : ℝ) :
    √((((hatPow A ((b : ℂ) * I) - hatPow B ((b : ℂ) * I)) * CFC.sqrt B)ᴴ *
        ((hatPow A ((b : ℂ) * I) - hatPow B ((b : ℂ) * I)) * CFC.sqrt B)).trace.re) ≤
      4 * (1 + |b|) * √(((CFC.sqrt A - CFC.sqrt B)ᴴ * (CFC.sqrt A - CFC.sqrt B)).trace.re) := by
  have e : CFC.sqrt A - CFC.sqrt B = (specFun hA.isHermitian (fun t ↦ ((√t : ℝ) : ℂ)) -
      specFun hB.isHermitian (fun t ↦ ((√t : ℝ) : ℂ))) * specFun hB.isHermitian 1 := by
    rw [specFun_one, Matrix.mul_one, sqrt_eq_specFun hA, sqrt_eq_specFun hB]
  rw [e, hatPow_eq hA.isHermitian, hatPow_eq hB.isHermitian, sqrt_eq_specFun hB,
    re_trace_hs_specFun, re_trace_hs_specFun, ← Real.sqrt_sq (by positivity : 0 ≤ 4 * (1 + |b|)),
    ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  -- D5.8.1–3, termwise
  have hα := hA.eigenvalues_nonneg i
  have hβ := hB.eigenvalues_nonneg j
  rw [hfun_mul_I b hα, hfun_mul_I b hβ, Pi.one_apply, norm_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hβ, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have := mul_le_mul_of_nonneg_right (step_5_8 hα hβ b)
    (ovl_nonneg hA.isHermitian hB.isHermitian i j)
  convert this using 1 <;> ring


/-- D5.9 (`eq:conditional-state-movement`, D5.9.1–7) with D5.8, matrix level, from D5.2
(`Step_5_2`). Universal `C`: for a conditional pair `(ρ, Q)`, a density matrix `ξ`, `τ > 0` with
`Tr τ ≤ 1`, `0 < a ≤ 1/4`, `λ ≥ 0` with `Tr τ^{2a} ξ^{[1-2a]} ≥ e^{-2λ}`, and real `u`:
`‖(τ^{-iau} − Q^{-iau}) √ρ‖₂ ≤ C (1+|u|) (√λ + √a ℓ + ‖√ρ − √ξ‖₂)`. -/
theorem step_5_9_of (h2 : Step_5_2.{u}) : Step_5_9.{u} := by
  obtain ⟨c3, C3, hc3, -, hC3, h53⟩ := step_5_3.{u}
  refine ⟨√C3 + 14, by positivity, ?_⟩
  intro n _ _ ρ Q ξ τ d hcp hξ hξ1 hτ hτ1 a lam u ha ha4 hlam hov
  have hρ := hcp.1
  have hQ := hcp.2.2.1
  have hd := hcp.2.2.2.1
  have hρh := hρ.isHermitian
  have hQh := hQ.isHermitian
  set z : ℂ := ((-(a * u) : ℝ) : ℂ) * I with hz
  rw [← norm_hs, ← norm_hs]
  -- D5.9.1
  have hsplit : hs ((hatPow τ z - hatPow Q z) * CFC.sqrt ρ) =
      hs ((hatPow τ z - hatPow ξ z) * CFC.sqrt ξ) +
        hs ((hatPow τ z - hatPow ξ z) * (CFC.sqrt ρ - CFC.sqrt ξ)) +
        hs ((hatPow ξ z - hatPow ρ z) * CFC.sqrt ρ) -
          hs ((hatPow Q z - hatPow ρ z) * CFC.sqrt ρ) := by
    rw [← hs_add, ← hs_add, ← hs_sub]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  -- D5.9.2
  have t1 : ‖hs ((hatPow Q z - hatPow ρ z) * CFC.sqrt ρ)‖ ≤ a * |u| * √C3 * ℓ d := by
    obtain ⟨hw0, hw1, hwp, hwm, -, -⟩ := h2 n ρ Q d hρh hQh hcp
    have hm := (h53 (n × n) (fun x ↦ hρh.eigenvalues x.1 *
        ovl hρh hQh x.1 x.2) (fun x ↦ Real.log (hρh.eigenvalues x.1)
          - Real.log (hQh.eigenvalues x.2)) d hd (fun x ↦ hw0 x.1 x.2)
        (by rw [Fintype.sum_prod_type]; exact hw1) (by rw [Fintype.sum_prod_type]; exact hwp)
        (by rw [Fintype.sum_prod_type]; exact hwm)).2.1 0 (by simpa using hc3.le)
    simp only [zero_mul, abs_zero, Real.exp_zero, mul_one, Fintype.sum_prod_type] at hm
    have hpt (i j : n) : ‖hfun z (hQh.eigenvalues i) -
        hfun z (hρh.eigenvalues j)‖ ^ 2 *
          ‖((√(hρh.eigenvalues j) : ℝ) : ℂ)‖ ^ 2 * ovl hQh hρh i j ≤
        (a * u) ^ 2 * (hρh.eigenvalues j * ovl hρh hQh j i *
          (Real.log (hρh.eigenvalues j) - Real.log (hQh.eigenvalues i)) ^ 2) := by
      have hp := hρ.eigenvalues_nonneg j
      obtain ⟨h1, -⟩ := sq_norm_hfun_sub_le (-(a * u)) (hQ.eigenvalues_pos i).le hp
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp,
        ovl_swap hQh hρh i j]
      have := mul_le_mul_of_nonneg_right h1
        (mul_nonneg hp (ovl_nonneg hρh hQh j i))
      exact (le_of_eq (by ring)).trans (this.trans_eq (by ring))
    rw [hatPow_eq hQh, hatPow_eq hρh, sqrt_eq_specFun hρ, norm_hs,
      re_trace_hs_specFun, Real.sqrt_le_left (mul_nonneg (by positivity)
        (by linarith [one_le_ℓ hd]))]
    calc _ ≤ ∑ i, ∑ j, (a * u) ^ 2 * (hρh.eigenvalues j *
            ovl hρh hQh j i * (Real.log (hρh.eigenvalues j) -
              Real.log (hQh.eigenvalues i)) ^ 2) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpt i j
      _ = (a * u) ^ 2 * ∑ j, ∑ i, hρh.eigenvalues j *
            ovl hρh hQh j i * (Real.log (hρh.eigenvalues j) -
              Real.log (hQh.eigenvalues i)) ^ 2 := by
          rw [Finset.sum_comm, Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ (a * u) ^ 2 * (C3 * ℓ d ^ 2) := by gcongr
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC3.le, sq_abs]; ring
  -- D5.9.3 (a)
  have t2 : ‖hs ((hatPow ξ z - hatPow ρ z) * CFC.sqrt ρ)‖ ≤
      4 * (1 + a * |u|) * ‖hs (CFC.sqrt ρ - CFC.sqrt ξ)‖ := by
    have := step_5_8_matrix hξ hρ (-(a * u))
    rw [← norm_hs, ← norm_hs, hs_sub, norm_sub_rev, ← hs_sub, abs_neg, abs_mul,
      abs_of_pos ha] at this
    exact this
  -- D5.9.3 (b)
  have t3 : ‖hs ((hatPow τ z - hatPow ξ z) * (CFC.sqrt ρ - CFC.sqrt ξ))‖ ≤
      2 * ‖hs (CFC.sqrt ρ - CFC.sqrt ξ)‖ :=
    norm_hs_unitary_sub_mul (hatPow_mul_I_mem_unitary τ _) (hatPow_mul_I_mem_unitary ξ _) _
  -- D5.9.4–7
  have t4 : ‖hs ((hatPow τ z - hatPow ξ z) * CFC.sqrt ξ)‖ ≤ 8 * (1 + |u|) * (√lam + √a) := by
    have hτh := hτ.isHermitian
    have hξh := hξ.isHermitian
    have S1 : ∑ i, ∑ j, ovl hτh hξh i j * hξh.eigenvalues j = 1 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_ovl_left, one_mul]
      have := congrArg Complex.re (hξh.trace_eq_sum_eigenvalues.symm.trans hξ1)
      simpa using this
    have S3 : ∑ i, ∑ j, ovl hτh hξh i j * hτh.eigenvalues i ≤ 1 := by
      simp_rw [← Finset.sum_mul, sum_ovl_right, one_mul]
      have := congrArg Complex.re hτh.trace_eq_sum_eigenvalues
      simp at this
      linarith
    have S2 : (bracketPow τ ((2 * a : ℝ) : ℂ) * bracketPow ξ ((1 - 2 * a : ℝ) : ℂ)).trace.re =
        ∑ i, ∑ j, hτh.eigenvalues i ^ (2 * a) * hξh.eigenvalues j ^ (1 - 2 * a) *
          ovl hτh hξh i j := by
      rw [bracketPow_eq hτh, bracketPow_eq hξh, trace_specFun_mul_specFun, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [bfun_ofReal (by positivity) (hτ.eigenvalues_pos i).le,
        bfun_ofReal (by linarith) (hξ.eigenvalues_nonneg j)]
      norm_cast
    have hpt (i j : n) : ‖hfun z (hτh.eigenvalues i) - hfun z (hξh.eigenvalues j)‖ ^ 2 *
        ‖((√(hξh.eigenvalues j) : ℝ) : ℂ)‖ ^ 2 * ovl hτh hξh i j ≤
        16 * (1 + u ^ 2) * (ovl hτh hξh i j * hξh.eigenvalues j -
          hτh.eigenvalues i ^ (2 * a) * hξh.eigenvalues j ^ (1 - 2 * a) * ovl hτh hξh i j +
          4 * a * (ovl hτh hξh i j * hτh.eigenvalues i)) :=
      (mul_le_mul_of_nonneg_right (phase_slack ha ha4 (hξ.eigenvalues_nonneg j)
        (hτ.eigenvalues_pos i)) (ovl_nonneg hτh hξh i j)).trans_eq (by ring)
    have hA : 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
    have hB : lam + a ≤ (√lam + √a) ^ 2 := by
      nlinarith [Real.sq_sqrt hlam, Real.sq_sqrt ha.le, Real.sqrt_nonneg lam, Real.sqrt_nonneg a]
    have hlam2 : 1 - Real.exp (-2 * lam) ≤ 2 * lam := by
      linarith [Real.add_one_le_exp (-2 * lam)]
    rw [hatPow_eq hτh, hatPow_eq hξh, sqrt_eq_specFun hξ, norm_hs, re_trace_hs_specFun,
      Real.sqrt_le_left (by positivity)]
    calc _ ≤ ∑ i, ∑ j, 16 * (1 + u ^ 2) * (ovl hτh hξh i j * hξh.eigenvalues j -
            hτh.eigenvalues i ^ (2 * a) * hξh.eigenvalues j ^ (1 - 2 * a) * ovl hτh hξh i j +
            4 * a * (ovl hτh hξh i j * hτh.eigenvalues i)) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpt i j
      _ = 16 * (1 + u ^ 2) * (∑ i, ∑ j, ovl hτh hξh i j * hξh.eigenvalues j -
            ∑ i, ∑ j, hτh.eigenvalues i ^ (2 * a) * hξh.eigenvalues j ^ (1 - 2 * a) *
              ovl hτh hξh i j + 4 * a * ∑ i, ∑ j, ovl hτh hξh i j * hτh.eigenvalues i) := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      _ ≤ 16 * (1 + u ^ 2) * (2 * lam + 4 * a) := by
          rw [S1, ← S2]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := mul_le_mul_of_nonneg_left S3 (by linarith : (0 : ℝ) ≤ 4 * a)
          linarith
      _ ≤ 64 * ((1 + |u|) ^ 2 * (√lam + √a) ^ 2) := by
          have := mul_le_mul hA hB (by positivity) (by positivity)
          have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + u ^ 2) hlam
          nlinarith
      _ = _ := by ring
  have hl := one_le_ℓ hd
  have hH := norm_nonneg (hs (CFC.sqrt ρ - CFC.sqrt ξ))
  have hs1 : √a ≤ 1 := by simpa using Real.sqrt_le_sqrt (by linarith : a ≤ 1)
  have hsa : a ≤ √a := calc
    a = √a * √a := (Real.mul_self_sqrt ha.le).symm
    _ ≤ √a * 1 := mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg a)
    _ = √a := mul_one _
  have hU : 0 ≤ |u| := abs_nonneg u
  have e1 : a * |u| * √C3 * ℓ d ≤ √C3 * ((1 + |u|) * (√a * ℓ d)) := by
    have : a * |u| ≤ √a * (1 + |u|) := (mul_le_mul_of_nonneg_right hsa hU).trans
      (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg a))
    have := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ √C3 * ℓ d)
    linarith
  have e2 : a * |u| * ‖hs (CFC.sqrt ρ - CFC.sqrt ξ)‖ ≤ |u| * ‖hs (CFC.sqrt ρ - CFC.sqrt ξ)‖ := by
    have := mul_le_mul_of_nonneg_right (by linarith : a ≤ 1) (mul_nonneg hU hH); linarith
  have e3 : √a ≤ √a * ℓ d := le_mul_of_one_le_right (Real.sqrt_nonneg a) hl
  have n7 : |u| * √a ≤ |u| * (√a * ℓ d) := mul_le_mul_of_nonneg_left e3 hU
  have n1 : 0 ≤ √C3 * √lam := by positivity
  have n2 : 0 ≤ √C3 * |u| * √lam := by positivity
  have n3 : 0 ≤ √C3 * ‖hs (CFC.sqrt ρ - CFC.sqrt ξ)‖ := by positivity
  have n4 : 0 ≤ √C3 * |u| * ‖hs (CFC.sqrt ρ - CFC.sqrt ξ)‖ := by positivity
  have n5 : 0 ≤ |u| * ‖hs (CFC.sqrt ρ - CFC.sqrt ξ)‖ := by positivity
  have n6 : 0 ≤ |u| * √lam := by positivity
  have n8 : 0 ≤ √lam := Real.sqrt_nonneg _
  have n9 : 0 ≤ √a * ℓ d := by positivity
  have n10 : 0 ≤ |u| * (√a * ℓ d) := by positivity
  have n11 : 0 ≤ √C3 * (√a * ℓ d) := by positivity
  rw [hsplit]
  calc _ ≤ ‖hs ((hatPow τ z - hatPow ξ z) * CFC.sqrt ξ)‖ +
        ‖hs ((hatPow τ z - hatPow ξ z) * (CFC.sqrt ρ - CFC.sqrt ξ))‖ +
        ‖hs ((hatPow ξ z - hatPow ρ z) * CFC.sqrt ρ)‖ +
        ‖hs ((hatPow Q z - hatPow ρ z) * CFC.sqrt ρ)‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

end AreaLaw
