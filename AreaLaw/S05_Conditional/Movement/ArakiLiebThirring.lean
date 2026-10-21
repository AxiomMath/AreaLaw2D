import AreaLaw.S05_Conditional.Movement.Setup
import AreaLawForMathlib.Analysis.Matrix.SpecPow
import AreaLawForMathlib.Analysis.CStarAlgebra.Matrix

/-!
# §5.1 D5.4.2–4: the Araki–Lieb–Thirring inequality

`Tr (Q^s A Q^s)^r ≤ Tr A^r Q^{2sr}` for `A ≥ 0`, `Q > 0`, real `s` and `r ≥ 1`, by Stein
interpolation of `F(z) = Q^{srz} A^{[rz/2]}` on the strip `0 ≤ Re z ≤ 1` (Hadamard three lines),
tested against the normalized dual matrices of `F(1/r)`.
-/

namespace AreaLaw

open Matrix Complex
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

universe u

namespace Conditional.ALT

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `|t^{[w]}| = t^{Re w}` for `t ≥ 0`, `Re w ≠ 0`. -/
theorem norm_bfun {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w.re ≠ 0) : ‖bfun w t‖ = t ^ w.re := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [bfun, Real.zero_rpow hw]
  · rw [bfun, if_pos ht, norm_exp, re_mul_ofReal, Real.rpow_def_of_pos ht, mul_comm]

/-- `|t^{[w]}| ≤ exp |Re w · log t|`. -/
theorem norm_bfun_le (w : ℂ) (t : ℝ) : ‖bfun w t‖ ≤ Real.exp |w.re * Real.log t| := by
  unfold bfun
  split_ifs
  · rw [norm_exp, re_mul_ofReal]; exact Real.exp_le_exp.2 (le_abs_self _)
  · simp [Real.exp_nonneg]

/-- `|t̂^w| ≤ exp |Re w · log t|`. -/
theorem norm_hfun_le (w : ℂ) (t : ℝ) : ‖hfun w t‖ ≤ Real.exp |w.re * Real.log t| := by
  unfold hfun
  split_ifs
  · rw [norm_exp, re_mul_ofReal]; exact Real.exp_le_exp.2 (le_abs_self _)
  · rw [norm_one]; exact Real.one_le_exp (abs_nonneg _)

/-- `‖g(ρ)‖ ≤ C` when `|g| ≤ C` on the spectrum. -/
theorem norm_specFun_le {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) {g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ i, ‖g (h.eigenvalues i)‖ ≤ C) : ‖specFun h g‖ ≤ C := by
  have hU : ‖(h.eigenvectorUnitary : Matrix n n ℂ)‖ ≤ 1 :=
    l2_opNorm_le_one_of_mul_conjTranspose (Unitary.coe_mul_star_self _)
  refine (l2_opNorm_mul_mul_le_of_le_one hU ?_ _).trans ?_
  · rwa [star_eq_conjTranspose, l2_opNorm_conjTranspose]
  · rw [l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hC).2 hg

omit [DecidableEq n] in
/-- On the strip, `exp |c x v_i| ≤ exp ‖c v‖` for `0 ≤ x ≤ 1`. -/
theorem exp_abs_le (c : ℝ) {x : ℝ} (v : n → ℝ) (i : n) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp |c * x * v i| ≤ Real.exp ‖fun j ↦ c * v j‖ := by
  refine Real.exp_le_exp.2 ?_
  have hi := norm_le_pi_norm (fun j ↦ c * v j) i
  rw [Real.norm_eq_abs] at hi
  calc |c * x * v i| = |c * v i| * x := by rw [mul_right_comm, abs_mul, abs_of_nonneg hx0]
    _ ≤ |c * v i| := mul_le_of_le_one_right (abs_nonneg _) hx1
    _ ≤ _ := hi

/-- Entries are bounded by the operator norm. -/
theorem norm_apply_le (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 <|
    (Finset.single_le_sum (f := fun i ↦ ‖A i j‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)).trans (sum_norm_apply_sq_le_l2_opNorm_sq A j)

/-- D5.4.3–4, Stein interpolation. For `F` entire, bounded on the strip, with `‖F(iu)‖ ≤ 1` and
`Tr F(1+iu) F(1+iu)* ≤ M`: `Tr (F(θ) F(θ)*)^{1/θ} ≤ M` for `0 < θ ≤ 1`. -/
theorem interpolation (F : ℂ → Matrix n n ℂ) (hF : ∀ i j, Differentiable ℂ fun z ↦ F z i j)
    {K : ℝ} (hK : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ K)
    (hl : ∀ z : ℂ, z.re = 0 → ‖F z‖ ≤ 1) {M : ℝ}
    (hr : ∀ z : ℂ, z.re = 1 → (F z * (F z)ᴴ).trace.re ≤ M) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) : (bracketPow (F θ * (F θ)ᴴ) (θ⁻¹ : ℝ)).trace.re ≤ M := by
  set X := F θ
  have hP := posSemidef_self_mul_conjTranspose X
  set h := hP.isHermitian
  set U : Matrix n n ℂ := ↑h.eigenvectorUnitary
  set p := h.eigenvalues
  have hp : ∀ i, 0 ≤ p i := hP.eigenvalues_nonneg
  set Z := ∑ i, p i ^ θ⁻¹
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hp i) _
  have hM : 0 ≤ M := (Complex.nonneg_iff.1
    (posSemidef_self_mul_conjTranspose (F 1)).trace_nonneg).1.trans (hr 1 (by simp))
  have hL : (bracketPow (X * Xᴴ) (θ⁻¹ : ℝ)).trace.re = Z := by
    rw [bracketPow_eq h, trace_specFun, re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [bfun_ofReal (inv_ne_zero hθ.ne') (hp i), ofReal_re]
  rw [hL]
  rcases hZ0.eq_or_lt with hZ | hZ
  · rw [← hZ]; exact hM
  -- D5.4.4: the dual test matrices `D(z) = R* diag(w^{1 - z/2}) U*`, `R = p^{-1/2} U* F(θ)`
  set w : n → ℝ := fun i ↦ p i ^ θ⁻¹ / Z
  have hw : ∀ i, 0 ≤ w i := fun i ↦ div_nonneg (Real.rpow_nonneg (hp i) _) hZ.le
  have hws : ∑ i, w i = 1 := by simp only [w, ← Finset.sum_div]; exact div_self hZ.ne'
  have hw1 : ∀ i, w i ≤ 1 := fun i ↦
    hws ▸ Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_univ i)
  have hspec : star U * (X * Xᴴ) * U = diagonal fun i ↦ (p i : ℂ) := by
    rw [← specFun_ofReal h]
    simp only [specFun, ← Matrix.mul_assoc, U, Unitary.coe_star_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  have hUU : star U * (star U)ᴴ = 1 := by
    rw [← star_eq_conjTranspose, star_star]; exact Unitary.coe_star_mul_self _
  have hUn : ‖star U‖ ≤ 1 := l2_opNorm_le_one_of_mul_conjTranspose hUU
  set s : n → ℂ := fun i ↦ ((√(p i) : ℝ) : ℂ)⁻¹
  have hsd : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [s]
  set R := diagonal s * (star U * X)
  have hRh : Rᴴ = Xᴴ * U * diagonal s := by
    simp only [R, conjTranspose_mul, hsd, star_eq_conjTranspose, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  set e : n → ℝ := fun i ↦ p i * (p i)⁻¹
  have he : ∀ i, 0 ≤ e i ∧ e i ≤ 1 := fun i ↦ by
    by_cases hpi : p i = 0 <;> simp [e, hpi]
  have hRR : R * Rᴴ = diagonal fun i ↦ (e i : ℂ) := by
    calc R * Rᴴ = diagonal s * (star U * (X * Xᴴ) * U) * diagonal s := by
          simp only [hRh, R, Matrix.mul_assoc]
      _ = _ := by
        rw [hspec, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1; funext i
        have : ((√(p i))⁻¹ * p i * (√(p i))⁻¹ : ℝ) = e i := by
          rw [mul_right_comm, ← mul_inv, Real.mul_self_sqrt (hp i), mul_comm]
        simpa [s] using congrArg (fun x : ℝ ↦ (x : ℂ)) this
  have hRn : ‖Rᴴ‖ ≤ 1 := by
    have h1 := l2_opNorm_conjTranspose_mul_self Rᴴ
    rw [conjTranspose_conjTranspose, hRR, l2_opNorm_diagonal] at h1
    have h2 : ‖fun i ↦ (e i : ℂ)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ by
      simpa [abs_of_nonneg (he i).1] using (he i).2
    nlinarith [norm_nonneg Rᴴ]
  set c : ℂ → n → ℂ := fun z i ↦ bfun (1 - z / 2) (w i)
  have hc : ∀ z i, z.re ≤ 1 → ‖c z i‖ = w i ^ (1 - z.re / 2) := fun z i hz ↦ by
    rw [norm_bfun (hw i) (by simp; linarith)]; simp
  set f : ℂ → ℂ := fun z ↦ ∑ i, c z i * (star U * F z * Rᴴ) i i
  have hfD : ∀ z, f z = (Rᴴ * diagonal (c z) * star U * F z).trace := fun z ↦ by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [f, Matrix.trace, diag_apply, diagonal_mul, Matrix.mul_assoc]
  have hfb : ∀ z, ‖f z‖ ≤ ∑ i, ‖c z i‖ * ‖F z‖ := fun z ↦
    (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_apply_le _ i i).trans
        (l2_opNorm_mul_mul_le_of_le_one hUn hRn _)) (norm_nonneg _)
  have hf : Differentiable ℂ f := by
    refine Differentiable.fun_sum fun i _ ↦ Differentiable.fun_mul ?_ ?_
    · simp only [c, bfun]; split_ifs <;> fun_prop
    · simp only [mul_apply]
      exact Differentiable.fun_sum fun k _ ↦ (Differentiable.fun_sum fun l _ ↦
        ((hF l k).const_mul _)).mul_const _
  -- D5.4.3: Hadamard three lines for `f(z) = Tr D(z) F(z)`
  have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f
    (z := (θ : ℂ)) (a := 1) (b := √M) (by simp [HadamardThreeLines.verticalClosedStrip, hθ.le,
      hθ1]) hf.diffContOnCl ⟨Fintype.card n * K, ?_⟩ (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  rotate_left
  · rintro _ ⟨z, ⟨hz0, hz1⟩, rfl⟩
    refine (hfb z).trans ((Finset.sum_le_sum fun i _ ↦ mul_le_mul (b := 1) ?_ (hK z hz0 hz1)
      (norm_nonneg _) zero_le_one).trans (by simp))
    rw [hc z i hz1]; exact Real.rpow_le_one (hw i) (hw1 i) (by linarith)
  · have hz : z.re = 0 := hz
    refine (hfb z).trans ((Finset.sum_le_sum fun i _ ↦ ?_).trans (b := ∑ i, w i) hws.le)
    rw [hc z i (by linarith), hz]
    simpa using mul_le_mul_of_nonneg_left (hl z hz) (hw i)
  · have hz : z.re = 1 := hz
    set D := Rᴴ * diagonal (c z) * star U
    have hfi : f z = ⟪hs Dᴴ, hs (F z)⟫_ℂ := by rw [inner_hs, conjTranspose_conjTranspose, hfD]
    have hDD : (D * Dᴴ).trace.re ≤ 1 := by
      have : D * Dᴴ = Rᴴ * (diagonal (c z) * diagonal (star (c z))) * R := by
        simp only [D, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star U), hUU, Matrix.one_mul]
      rw [this, Matrix.trace_mul_cycle, hRR, diagonal_mul_diagonal, diagonal_mul_diagonal,
        trace_diagonal, re_sum, ← hws]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hw2 : (w i ^ (1 - 1 / 2 : ℝ)) ^ 2 = w i := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hw i)]; norm_num
      rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, ← ofReal_mul, ofReal_re,
        Complex.normSq_eq_norm_sq, hc z i hz.le, hz, hw2]
      exact mul_le_of_le_one_left (hw i) (he i).2
    rw [hfi]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_hs, norm_hs, conjTranspose_conjTranspose, Matrix.trace_mul_comm (F z)ᴴ]
    calc _ ≤ 1 * √M := mul_le_mul ((Real.sqrt_le_sqrt hDD).trans_eq Real.sqrt_one)
          (Real.sqrt_le_sqrt (hr z hz)) (Real.sqrt_nonneg _) zero_le_one
      _ = √M := one_mul _
  -- D5.4.4: `f(θ) = Z^{θ/2}`
  have hB : star U * X * Rᴴ = diagonal fun i ↦ (p i : ℂ) * s i := by
    rw [← diagonal_mul_diagonal, ← hspec, hRh]; simp only [Matrix.mul_assoc]
  have hfθ : f θ = ((Z ^ (θ / 2) : ℝ) : ℂ) := by
    have hterm : ∀ i, c θ i * (star U * X * Rᴴ) i i =
        ((p i ^ θ⁻¹ / Z ^ (1 - θ / 2) : ℝ) : ℂ) := fun i ↦ by
      have h1 : (1 : ℂ) - (θ : ℂ) / 2 = ((1 - θ / 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hB, diagonal_apply_eq]
      simp only [c, h1, bfun_ofReal (show 1 - θ / 2 ≠ 0 by linarith) (hw i), s]
      rw [← ofReal_inv, ← ofReal_mul, ← ofReal_mul, ← div_eq_mul_inv, Real.div_sqrt]
      congr 1
      rcases (hp i).eq_or_lt with hpi | hpi
      · rw [← hpi]; simp [Real.zero_rpow (inv_ne_zero hθ.ne')]
      rw [Real.div_rpow (Real.rpow_nonneg (hp i) _) hZ.le, ← Real.rpow_mul (hp i),
        Real.sqrt_eq_rpow, div_mul_eq_mul_div, ← Real.rpow_add hpi]
      congr 2
      field_simp
      ring
    change ∑ i, c θ i * (star U * X * Rᴴ) i i = _
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← ofReal_sum, ← Finset.sum_div]
    congr 1
    rw [div_eq_iff (Real.rpow_pos_of_pos hZ _).ne', ← Real.rpow_add hZ, add_sub_cancel,
      Real.rpow_one]
  rw [hfθ, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hZ0 _), ofReal_re,
    Real.one_rpow, one_mul, Real.sqrt_eq_rpow, ← Real.rpow_mul hM, one_div_mul_eq_div] at h3
  exact (Real.rpow_le_rpow_iff hZ0 hM (by positivity)).1 h3

end Conditional.ALT

open Conditional

/-- D5.4.2–4, formal route (Araki–Lieb–Thirring). For `A ≥ 0`, `Q > 0`, real `s` and `r ≥ 1`:
`Tr (Q^s A Q^s)^r ≤ Tr A^r Q^{2sr}`. -/
theorem araki_lieb_thirring : ArakiLiebThirring.{u} := by
  intro n _ _ A Q hA hQ s r hr
  have hr0 : 0 < r := by linarith
  set F : ℂ → Matrix n n ℂ := fun z ↦
    hatPow Q (((s * r : ℝ) : ℂ) * z) * bracketPow A (((r / 2 : ℝ) : ℂ) * z)
  -- D5.4.2: the analytic family `F(z) = Q^{srz} A^{[rz/2]}`, `F(1/r) F(1/r)* = Q^s A Q^s`
  have hX : F (r⁻¹ : ℝ) = hatPow Q s * bracketPow A ((1 / 2 : ℝ) : ℂ) := by
    simp only [F, ← ofReal_mul]
    rw [show s * r * r⁻¹ = s by field_simp, show r / 2 * r⁻¹ = 1 / 2 by field_simp]
  have hFθ : F (r⁻¹ : ℝ) * (F (r⁻¹ : ℝ))ᴴ = hatPow Q s * A * hatPow Q s := by
    rw [hX, conjTranspose_mul, (isHermitian_hatPow_ofReal Q s).eq,
      (isHermitian_bracketPow_ofReal A _).eq, ← Matrix.mul_assoc, Matrix.mul_assoc (hatPow Q s),
      bracketPow_mul_bracketPow, ← ofReal_add, add_halves, ofReal_one, bracketPow_one hA]
  -- D5.4.3–4: three lines on the strip, tested against the dual matrices
  have key := ALT.interpolation F (fun i j ↦ ?_)
    (K := Real.exp ‖fun j ↦ s * r * Real.log (hQ.1.eigenvalues j)‖ *
      Real.exp ‖fun j ↦ r / 2 * Real.log (hA.1.eigenvalues j)‖) (fun z hz0 hz1 ↦ ?_)
    (fun z hz ↦ ?_) (M := (bracketPow A r * hatPow Q ((2 * s * r : ℝ) : ℂ)).trace.re)
    (fun z hz ↦ ?_) (inv_pos.2 hr0) (inv_le_one_of_one_le₀ hr)
  · rwa [hFθ, inv_inv] at key
  · simp only [F, mul_apply]
    exact Differentiable.fun_sum fun k _ ↦
      ((differentiable_hatPow_apply Q i k).comp (differentiable_id.const_mul _)).fun_mul
        ((differentiable_bracketPow_apply A k j).comp (differentiable_id.const_mul _))
  · change ‖hatPow Q _ * bracketPow A _‖ ≤ _
    rw [hatPow_eq hQ.1, bracketPow_eq hA.1]
    refine (norm_mul_le _ _).trans (mul_le_mul (ALT.norm_specFun_le _ (Real.exp_pos _).le
      fun i ↦ ?_) (ALT.norm_specFun_le _ (Real.exp_pos _).le fun i ↦ ?_) (norm_nonneg _)
      (Real.exp_pos _).le)
    · exact (ALT.norm_hfun_le _ _).trans <| by
        rw [re_ofReal_mul]
        exact ALT.exp_abs_le _ (fun j ↦ Real.log (hQ.1.eigenvalues j)) i hz0 hz1
    · exact (ALT.norm_bfun_le _ _).trans <| by
        rw [re_ofReal_mul]
        exact ALT.exp_abs_le _ (fun j ↦ Real.log (hA.1.eigenvalues j)) i hz0 hz1
  · change ‖hatPow Q _ * bracketPow A _‖ ≤ 1
    rw [hatPow_eq hQ.1, bracketPow_eq hA.1]
    refine (norm_mul_le _ _).trans (mul_le_one₀ (ALT.norm_specFun_le _ zero_le_one fun i ↦ ?_)
      (norm_nonneg _) (ALT.norm_specFun_le _ zero_le_one fun i ↦ ?_))
    · exact (ALT.norm_hfun_le _ _).trans (by simp [hz])
    · exact (ALT.norm_bfun_le _ _).trans (by simp [hz])
  · change (hatPow Q _ * bracketPow A _ * (hatPow Q _ * bracketPow A _)ᴴ).trace.re ≤ _
    have e1 : ((s * r : ℝ) : ℂ) * starRingEnd ℂ z + ((s * r : ℝ) : ℂ) * z =
        ((2 * s * r : ℝ) : ℂ) := by apply Complex.ext <;> simp [hz]; ring
    have e2 : ((r / 2 : ℝ) : ℂ) * z + ((r / 2 : ℝ) : ℂ) * starRingEnd ℂ z = (r : ℂ) := by
      apply Complex.ext <;> simp [hz]
    rw [conjTranspose_mul, conjTranspose_hatPow, conjTranspose_bracketPow, map_mul, map_mul,
      conj_ofReal, conj_ofReal, ← Matrix.mul_assoc, Matrix.mul_assoc (hatPow Q _),
      bracketPow_mul_bracketPow, e2, Matrix.trace_mul_cycle, hatPow_mul_hatPow, e1,
      Matrix.trace_mul_comm]

end AreaLaw
