import AreaLawForMathlib.Analysis.Matrix.FilteredNorm
import AreaLawForMathlib.Analysis.Matrix.TwoPositiveSchwarz
import AreaLawForMathlib.Analysis.Matrix.BlockDiagonalMean

/-!
# Functions of `ad_{log M}` and their Fourier representation

For a Hermitian `M = U diag(x) U^*` and `f : ℝ → ℂ`, `f(ad_{log M}) X` multiplies the
eigenbasis entry `(r, t)` of `X` by `f(log x_r - log x_t)`. For positive definite `M`:

* `adLogFun_exp`: `e^{a ad_{log M}} X = M^a X M^{-a}`; hence
  `2 sinh(ad_{log M}/2) L = M^{1/2} L M^{-1/2} - M^{-1/2} L M^{1/2}` and
  `(e^{s ad_{log M}} - 1) L = M^s L M^{-s} - L`;
* `star_dotProduct_adLogFun_mulVec`: if `f(z) = ∫ e^{iuz} q(u) du`, then
  `⟨y, f(ad_{log M}) X x⟩ = ∫ q(u) ⟨M^{-iu} y, X M^{-iu} x⟩ du`;
* `normSq_conj_sub_le`: if moreover `f(z) 2 sinh(z/2) = e^{sz} - 1` and
  `2 sinh(ad_{log M}/2) L = ∑_{j ∈ S} w_j G_j` with `w_j ≥ 0`, then Cauchy–Schwarz for the
  positive measure `w_j |q(u)| du` gives
  `‖(M^s L M^{-s} - L) x‖² ≤ (∑_j w_j) (∫ |q|) ∑_j w_j ∫ |q(u)| ‖G_j M^{-iu} x‖² du`.

Also: the Schwarz inequality for a unital 2-positive map in vector form, and `M^{-iu}` of a
block-diagonal matrix.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Complex

namespace Matrix.Transport

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

/-- The eigenbasis entries of `f(ad_{log M}) X`. -/
noncomputable def adLogCoeff (hM : M.IsHermitian) (f : ℝ → ℂ) (X : Matrix n n ℂ) :
    Matrix n n ℂ :=
  of fun r t => f (Real.log (hM.eigenvalues r) - Real.log (hM.eigenvalues t)) *
    (star (eigU hM) * X * eigU hM) r t

/-- `f(ad_{log M}) X`: in the eigenbasis of `M` (eigenvalues `x_r`), the entry `(r, t)` of `X`
multiplied by `f(log x_r - log x_t)`. -/
noncomputable def adLogFun (hM : M.IsHermitian) (f : ℝ → ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  eigU hM * adLogCoeff hM f X * star (eigU hM)

theorem star_eigU_mul_adLogFun_mul (hM : M.IsHermitian) (f : ℝ → ℂ) (X : Matrix n n ℂ) :
    star (eigU hM) * adLogFun hM f X * eigU hM = adLogCoeff hM f X := by
  simp only [adLogFun, ← Matrix.mul_assoc, star_eigU_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, star_eigU_mul, Matrix.mul_one]

/-- `f(ad) (g(ad) X) = (f g)(ad) X`. -/
theorem adLogFun_comp (hM : M.IsHermitian) (f g : ℝ → ℂ) (X : Matrix n n ℂ) :
    adLogFun hM f (adLogFun hM g X) = adLogFun hM (fun z => f z * g z) X := by
  have h : adLogCoeff hM f (adLogFun hM g X) = adLogCoeff hM (fun z => f z * g z) X := by
    ext r t
    rw [adLogCoeff, of_apply, star_eigU_mul_adLogFun_mul]
    simp only [adLogCoeff, of_apply]
    ring
  change eigU hM * adLogCoeff hM f (adLogFun hM g X) * star (eigU hM) = _
  rw [h]; rfl

theorem adLogFun_sub (hM : M.IsHermitian) (f g : ℝ → ℂ) (X : Matrix n n ℂ) :
    adLogFun hM (fun z => f z - g z) X = adLogFun hM f X - adLogFun hM g X := by
  have h : adLogCoeff hM (fun z => f z - g z) X = adLogCoeff hM f X - adLogCoeff hM g X := by
    ext r t; simp only [adLogCoeff, of_apply, sub_apply, sub_mul]
  simp only [adLogFun, h, Matrix.mul_sub, Matrix.sub_mul]

theorem adLogFun_const_one (hM : M.IsHermitian) (X : Matrix n n ℂ) :
    adLogFun hM (fun _ => 1) X = X := by
  have h : adLogCoeff hM (fun _ => 1) X = star (eigU hM) * X * eigU hM := by
    ext r t; simp only [adLogCoeff, of_apply, one_mul]
  rw [adLogFun, h]
  simp only [← Matrix.mul_assoc, eigU_mul_star, Matrix.one_mul]
  rw [Matrix.mul_assoc, eigU_mul_star, Matrix.mul_one]

/-- `e^{a ad_{log M}} X = M^a X M^{-a}`. -/
theorem adLogFun_exp (hM : M.PosDef) (a : ℝ) (X : Matrix n n ℂ) :
    adLogFun hM.isHermitian (fun z => ((Real.exp (a * z) : ℝ) : ℂ)) X =
      M ^ a * X * M ^ (-a) := by
  set U := eigU hM.isHermitian
  set x := hM.isHermitian.eigenvalues
  have h : adLogCoeff hM.isHermitian (fun z => ((Real.exp (a * z) : ℝ) : ℂ)) X =
      diagonal (fun r => ((x r ^ a : ℝ) : ℂ)) * (star U * X * U) *
        diagonal (fun r => ((x r ^ (-a) : ℝ) : ℂ)) := by
    ext r t
    simp only [adLogCoeff, of_apply, diagonal_mul, mul_diagonal]
    rw [Real.rpow_def_of_pos (hM.eigenvalues_pos r), Real.rpow_def_of_pos (hM.eigenvalues_pos t),
      show a * (Real.log (x r) - Real.log (x t)) = Real.log (x r) * a + Real.log (x t) * (-a) by
        ring, Real.exp_add]
    push_cast; ring
  rw [adLogFun, h, rpow_eq_eigen hM a, rpow_eq_eigen hM (-a)]
  simp only [Matrix.mul_assoc]
  rfl

/-- D7.22.4: `2 sinh(ad_{log M}/2) L = M^{1/2} L M^{-1/2} - M^{-1/2} L M^{1/2}`. -/
theorem adLogFun_two_sinh (hM : M.PosDef) (L : Matrix n n ℂ) :
    adLogFun hM.isHermitian (fun z => ((2 * Real.sinh (z / 2) : ℝ) : ℂ)) L =
      M ^ (1 / 2 : ℝ) * L * M ^ (-(1 / 2) : ℝ) - M ^ (-(1 / 2) : ℝ) * L * M ^ (1 / 2 : ℝ) := by
  have e : (fun z : ℝ => ((2 * Real.sinh (z / 2) : ℝ) : ℂ)) =
      fun z => ((Real.exp ((1 / 2) * z) : ℝ) : ℂ) - ((Real.exp (-(1 / 2) * z) : ℝ) : ℂ) := by
    funext z
    rw [Real.sinh_eq]; push_cast; ring_nf
  rw [e, adLogFun_sub, adLogFun_exp hM, adLogFun_exp hM, neg_neg]

/-- `(e^{s ad_{log M}} - 1) L = M^s L M^{-s} - L`. -/
theorem adLogFun_exp_sub_one (hM : M.PosDef) (s : ℝ) (L : Matrix n n ℂ) :
    adLogFun hM.isHermitian (fun z => ((Real.exp (s * z) - 1 : ℝ) : ℂ)) L =
      M ^ s * L * M ^ (-s) - L := by
  have e : (fun z : ℝ => ((Real.exp (s * z) - 1 : ℝ) : ℂ)) =
      fun z => ((Real.exp (s * z) : ℝ) : ℂ) - 1 := by
    funext z; push_cast; ring
  rw [e, adLogFun_sub, adLogFun_exp hM, adLogFun_const_one]

/-! ### Pairings along `u ↦ M^{-iu}` -/

omit [DecidableEq n] in
theorem star_dotProduct_conj_mulVec (U Y : Matrix n n ℂ) (x y : n → ℂ) :
    star y ⬝ᵥ ((U * Y * star U) *ᵥ x) =
      ∑ r, ∑ t, star ((star U *ᵥ y) r) * Y r t * (star U *ᵥ x) t := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_star (star y ᵥ* U),
    star_vecMul, star_star, ← star_eq_conjTranspose]
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq n] in
theorem star_mulVec_dotProduct_mulVec' (X Y : Matrix n n ℂ) (v w : n → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (Y *ᵥ w) = star v ⬝ᵥ ((Xᴴ * Y) *ᵥ w) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-- The pairing `⟨M^{-iu} y, X M^{-iu} x⟩` in the eigenbasis: a finite sum of characters
`e^{iu(log x_r - log x_t)}`. -/
theorem inner_imagPow_eq_sum (hM : M.IsHermitian) (X : Matrix n n ℂ) (x y : n → ℂ) (u : ℝ) :
    star (imagPow M u *ᵥ y) ⬝ᵥ (X *ᵥ (imagPow M u *ᵥ x)) =
      ∑ r, ∑ t, cexp (I * u *
        ((Real.log (hM.eigenvalues r) - Real.log (hM.eigenvalues t) : ℝ) : ℂ)) *
        (star ((star (eigU hM) *ᵥ y) r) * (star (eigU hM) * X * eigU hM) r t *
          (star (eigU hM) *ᵥ x) t) := by
  set U := eigU hM
  set e : n → ℂ := fun r => cexp (((-u : ℝ) : ℂ) * (I * (Real.log (hM.eigenvalues r) : ℂ)))
  have hW : imagPow M u = U * diagonal e * star U := imagPow_eq_eigen hM u
  have hWW : (imagPow M u)ᴴ * X * imagPow M u =
      U * (diagonal (star e) * (star U * X * U) * diagonal e) * star U := by
    rw [hW, conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, ← star_eq_conjTranspose,
      star_star, ← star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [star_mulVec_dotProduct_mulVec', mulVec_mulVec, hWW, star_dotProduct_conj_mulVec]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  have he : star (e r) * e t =
      cexp (I * u * ((Real.log (hM.eigenvalues r) - Real.log (hM.eigenvalues t) : ℝ) : ℂ)) := by
    simp only [e, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    congr 1; push_cast; ring
  simp only [diagonal_mul, mul_diagonal, Pi.star_apply]
  rw [← he]; ring

theorem continuous_imagPow (M : Matrix n n ℂ) : Continuous (imagPow M) :=
  (continuous_hermitianUnitaryPath _).comp continuous_neg

theorem conjTranspose_imagPow_mul_self (M : Matrix n n ℂ) (u : ℝ) :
    (imagPow M u)ᴴ * imagPow M u = 1 := by
  have h : imagPow M u * (imagPow M u)ᴴ = 1 :=
    hermitianUnitaryPath_mul_conjTranspose _ (IsSelfAdjoint.log (a := M)) _
  exact mul_eq_one_comm.mp h

theorem normSq_imagPow_mulVec (M : Matrix n n ℂ) (u : ℝ) (y : n → ℂ) :
    star (imagPow M u *ᵥ y) ⬝ᵥ (imagPow M u *ᵥ y) = star y ⬝ᵥ y := by
  rw [star_mulVec_dotProduct_mulVec', conjTranspose_imagPow_mul_self, one_mulVec]

theorem continuous_inner_imagPow (M X : Matrix n n ℂ) (x y : n → ℂ) :
    Continuous fun u : ℝ => star (imagPow M u *ᵥ y) ⬝ᵥ (X *ᵥ (imagPow M u *ᵥ x)) := by
  have h := continuous_imagPow M
  fun_prop

theorem norm_inner_imagPow_le (hM : M.IsHermitian) (X : Matrix n n ℂ) (x y : n → ℂ) :
    ∃ C, ∀ u : ℝ, ‖star (imagPow M u *ᵥ y) ⬝ᵥ (X *ᵥ (imagPow M u *ᵥ x))‖ ≤ C := by
  refine ⟨∑ r, ∑ t, ‖star ((star (eigU hM) *ᵥ y) r) * (star (eigU hM) * X * eigU hM) r t *
      (star (eigU hM) *ᵥ x) t‖, fun u => ?_⟩
  rw [inner_imagPow_eq_sum hM]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun t _ => ?_))
  rw [norm_mul, show I * (u : ℂ) * _ = ((u * (Real.log (hM.eigenvalues r) -
    Real.log (hM.eigenvalues t)) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `|q| · Re⟨M^{-iu} x, X M^{-iu} x⟩` is integrable for integrable `q`. -/
theorem integrable_norm_mul_re_inner_imagPow (hM : M.IsHermitian) {q : ℝ → ℂ}
    (hq : Integrable q) (X : Matrix n n ℂ) (x : n → ℂ) :
    Integrable fun u => ‖q u‖ * (star (imagPow M u *ᵥ x) ⬝ᵥ (X *ᵥ (imagPow M u *ᵥ x))).re := by
  obtain ⟨C, hC⟩ := norm_inner_imagPow_le hM X x x
  exact hq.norm.mul_bdd (Complex.continuous_re.comp
    (continuous_inner_imagPow M _ x x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans
      (hC u))

/-- `|q| · Re‖G M^{-iu} x‖²` is integrable for integrable `q`. -/
theorem integrable_norm_mul_normSq_imagPow (hM : M.IsHermitian) {q : ℝ → ℂ} (hq : Integrable q)
    (G : Matrix n n ℂ) (x : n → ℂ) :
    Integrable fun u => ‖q u‖ * (star (G *ᵥ (imagPow M u *ᵥ x)) ⬝ᵥ
      (G *ᵥ (imagPow M u *ᵥ x))).re := by
  have e : ∀ u, star (G *ᵥ (imagPow M u *ᵥ x)) ⬝ᵥ (G *ᵥ (imagPow M u *ᵥ x)) =
      star (imagPow M u *ᵥ x) ⬝ᵥ ((Gᴴ * G) *ᵥ (imagPow M u *ᵥ x)) := fun u =>
    star_mulVec_dotProduct_mulVec' _ _ _ _
  simp_rw [e]
  obtain ⟨C, hC⟩ := norm_inner_imagPow_le hM (Gᴴ * G) x x
  exact hq.norm.mul_bdd (Complex.continuous_re.comp
    (continuous_inner_imagPow M _ x x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans
      (hC u))

/-- **Fourier representation** (D7.23.2): if `f(z) = ∫ e^{iuz} q(u) du`, then
`⟨y, f(ad_{log M}) X x⟩ = ∫ q(u) ⟨M^{-iu} y, X M^{-iu} x⟩ du`, i.e.
`f(ad_{log M}) X = ∫ q(u) M^{iu} X M^{-iu} du`. -/
theorem star_dotProduct_adLogFun_mulVec (hM : M.IsHermitian) {f q : ℝ → ℂ} (hq : Integrable q)
    (hf : ∀ z : ℝ, ∫ u : ℝ, cexp (I * u * z) * q u = f z) (X : Matrix n n ℂ) (x y : n → ℂ) :
    star y ⬝ᵥ (adLogFun hM f X *ᵥ x) =
      ∫ u, q u * (star (imagPow M u *ᵥ y) ⬝ᵥ (X *ᵥ (imagPow M u *ᵥ x))) := by
  set U := eigU hM
  set z : n → n → ℝ := fun r t => Real.log (hM.eigenvalues r) - Real.log (hM.eigenvalues t)
  set c : n → n → ℂ := fun r t => star ((star U *ᵥ y) r) * (star U * X * U) r t *
    (star U *ᵥ x) t
  have hint : ∀ r t, Integrable fun u : ℝ => q u * (cexp (I * u * (z r t : ℂ)) * c r t) :=
    fun r t => hq.mul_bdd (by fun_prop) (c := ‖c r t‖) (Filter.Eventually.of_forall fun u => by
      rw [norm_mul, show I * (u : ℂ) * (z r t : ℂ) = ((u * z r t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul])
  simp_rw [inner_imagPow_eq_sum hM, Finset.mul_sum]
  rw [adLogFun, star_dotProduct_conj_mulVec,
    integral_finsetSum _ fun r _ => integrable_finsetSum _ fun t _ => hint r t]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_finsetSum _ fun t _ => hint r t]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : (fun u : ℝ => q u * (cexp (I * u * (z r t : ℂ)) * c r t)) =
      fun u : ℝ => cexp (I * u * (z r t : ℂ)) * q u * c r t := by funext u; ring
  change _ = ∫ u : ℝ, q u * (cexp (I * u * (z r t : ℂ)) * c r t)
  rw [e, integral_mul_const, hf]
  simp only [adLogCoeff, of_apply, c, z]
  ring

/-! ### The transported square -/

omit [DecidableEq n] in
/-- `Re(q ⟨p, g⟩) ≤ |q| (c/2 ‖p‖² + ‖g‖²/(2c))` for `c > 0`. -/
theorem re_mul_dotProduct_le (q : ℂ) (p g : n → ℂ) {c : ℝ} (hc : 0 < c) :
    (q * (star p ⬝ᵥ g)).re ≤
      ‖q‖ * (c / 2 * (star p ⬝ᵥ p).re + 1 / (2 * c) * (star g ⬝ᵥ g).re) := by
  simp only [dotProduct, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hpp : (star (p i) * p i).re = ‖p i‖ ^ 2 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]; rfl
  have hgg : (star (g i) * g i).re = ‖g i‖ ^ 2 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]; rfl
  rw [hpp, hgg]
  calc (q * (star (p i) * g i)).re ≤ ‖q * (star (p i) * g i)‖ := Complex.re_le_norm _
    _ = ‖q‖ * (‖p i‖ * ‖g i‖) := by rw [norm_mul, norm_mul, norm_star]
    _ ≤ _ := by
      gcongr
      have key : c / 2 * ‖p i‖ ^ 2 + 1 / (2 * c) * ‖g i‖ ^ 2 - ‖p i‖ * ‖g i‖ =
          (c * ‖p i‖ - ‖g i‖) ^ 2 / (2 * c) := by field_simp; ring
      nlinarith [key, div_nonneg (sq_nonneg (c * ‖p i‖ - ‖g i‖)) (by positivity : (0 : ℝ) ≤ 2 * c)]

omit [Fintype n] [DecidableEq n] in
theorem re_star_dotProduct_self_nonneg [Fintype n] (y : n → ℂ) : 0 ≤ (star y ⬝ᵥ y).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (y i).re, sq_nonneg (y i).im]

/-- The optimization over `c` closing Cauchy–Schwarz: `N ≤ c/2 N P + S/(2c)` for all `c > 0`
gives `N ≤ P S`. -/
theorem le_mul_of_forall_pos_le {N P S : ℝ} (hP : 0 ≤ P) (hS : 0 ≤ S)
    (h : ∀ c : ℝ, 0 < c → N ≤ c / 2 * N * P + 1 / (2 * c) * S) : N ≤ P * S := by
  rcases eq_or_lt_of_le hP with hP0 | hP0
  · rw [← hP0, zero_mul]
    by_contra hN'
    have hN : 0 < N := lt_of_not_ge hN'
    have := h ((S + 1) / N) (by positivity)
    rw [← hP0, mul_zero, zero_add,
      show 1 / (2 * ((S + 1) / N)) * S = N * S / (2 * (S + 1)) by field_simp,
      le_div_iff₀ (by positivity)] at this
    nlinarith
  · have := h (1 / P) (by positivity)
    rw [show 1 / P / 2 * N * P = N / 2 by field_simp,
      show 1 / (2 * (1 / P)) * S = P * S / 2 by field_simp] at this
    linarith

/-- **The transported square** (D7.23.1–D7.23.3). Let `M > 0`, `f(z) = ∫ e^{iuz} q(u) du` with
`q` integrable, `f(z) 2 sinh(z/2) = e^{sz} - 1`, and
`2 sinh(ad_{log M}/2) L = ∑_{j ∈ S} w_j G_j` with `w_j ≥ 0`. Then
`‖(M^s L M^{-s} - L) x‖² ≤ (∑_j w_j)(∫ |q|) ∑_j w_j ∫ |q(u)| ‖G_j M^{-iu} x‖² du`. -/
theorem normSq_conj_sub_le {J : Type*} (hM : M.PosDef) (L : Matrix n n ℂ) {s : ℝ}
    {f q : ℝ → ℂ} (hq : Integrable q) (hf : ∀ z : ℝ, ∫ u : ℝ, cexp (I * u * z) * q u = f z)
    (hfs : ∀ z : ℝ, f z * ((2 * Real.sinh (z / 2) : ℝ) : ℂ) = ((Real.exp (s * z) - 1 : ℝ) : ℂ))
    (S : Finset J) {w : J → ℝ} (hw : ∀ j ∈ S, 0 ≤ w j) (G : J → Matrix n n ℂ)
    (hG : adLogFun hM.isHermitian (fun z => ((2 * Real.sinh (z / 2) : ℝ) : ℂ)) L =
      ∑ j ∈ S, (w j : ℂ) • G j) (x : n → ℂ) :
    (star ((M ^ s * L * M ^ (-s) - L) *ᵥ x) ⬝ᵥ ((M ^ s * L * M ^ (-s) - L) *ᵥ x)).re ≤
      (∑ j ∈ S, w j) * (∫ u, ‖q u‖) *
        ∑ j ∈ S, w j * ∫ u, ‖q u‖ *
          (star (G j *ᵥ (imagPow M u *ᵥ x)) ⬝ᵥ (G j *ᵥ (imagPow M u *ᵥ x))).re := by
  set y := (M ^ s * L * M ^ (-s) - L) *ᵥ x
  set N := (star y ⬝ᵥ y).re
  set a : J → ℝ → ℝ := fun j u =>
    (star (G j *ᵥ (imagPow M u *ᵥ x)) ⬝ᵥ (G j *ᵥ (imagPow M u *ᵥ x))).re
  have hH := hM.isHermitian
  -- D7.23.1: `h(ad)(2 sinh(ad/2) L) = M^s L M^{-s} - L`
  have hF : M ^ s * L * M ^ (-s) - L = adLogFun hH f (∑ j ∈ S, (w j : ℂ) • G j) := by
    rw [← hG, adLogFun_comp, ← adLogFun_exp_sub_one hM]
    congr 1; funext z; exact (hfs z).symm
  have hint : ∀ j, Integrable fun u => q u *
      (star (imagPow M u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow M u *ᵥ x))) := fun j => by
    obtain ⟨C, hC⟩ := norm_inner_imagPow_le hH (G j) x y
    exact hq.mul_bdd (continuous_inner_imagPow M _ x y).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  -- D7.23.2: the Fourier representation, summand by summand
  have hN : N = ∑ j ∈ S, w j * ∫ u, (q u *
      (star (imagPow M u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow M u *ᵥ x)))).re := by
    have h := star_dotProduct_adLogFun_mulVec hH hq hf (∑ j ∈ S, (w j : ℂ) • G j) x y
    rw [← hF] at h
    change star y ⬝ᵥ y = _ at h
    simp_rw [Matrix.sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, Finset.mul_sum,
      smul_eq_mul, mul_left_comm (q _) (w _ : ℂ)] at h
    rw [integral_finsetSum _ fun j _ => (hint j).const_mul (w j : ℂ)] at h
    simp_rw [integral_const_mul] at h
    change (star y ⬝ᵥ y).re = _
    rw [h, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hre := integral_re (hint j)
    simp only [RCLike.re_to_complex] at hre
    rw [Complex.re_ofReal_mul, ← hre]
  have hqa : ∀ j, Integrable fun u => ‖q u‖ * a j u := fun j =>
    integrable_norm_mul_normSq_imagPow hH hq (G j) x
  -- D7.23.3: Cauchy–Schwarz for the measure `w_j |q(u)| du`
  refine le_mul_of_forall_pos_le (mul_nonneg (Finset.sum_nonneg hw)
    (integral_nonneg fun u => norm_nonneg _)) (Finset.sum_nonneg fun j hj => mul_nonneg (hw j hj)
      (integral_nonneg fun u => mul_nonneg (norm_nonneg _)
        (re_star_dotProduct_self_nonneg _))) fun c hc => ?_
  calc N = ∑ j ∈ S, w j * ∫ u, (q u *
        (star (imagPow M u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow M u *ᵥ x)))).re := hN
    _ ≤ ∑ j ∈ S, w j * ∫ u, (c / 2 * N * ‖q u‖ + 1 / (2 * c) * (‖q u‖ * a j u)) := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (hw j hj)
        refine integral_mono (hint j).re ((hq.norm.const_mul _).add ((hqa j).const_mul _))
          fun u => ?_
        have h1 := re_mul_dotProduct_le (q u) (imagPow M u *ᵥ y) (G j *ᵥ (imagPow M u *ᵥ x)) hc
        rw [normSq_imagPow_mulVec] at h1
        dsimp only
        nlinarith [h1, norm_nonneg (q u)]
    _ = c / 2 * N * ((∑ j ∈ S, w j) * ∫ u, ‖q u‖) +
        1 / (2 * c) * ∑ j ∈ S, w j * ∫ u, ‖q u‖ * a j u := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_add (hq.norm.const_mul _) ((hqa j).const_mul _), integral_const_mul,
          integral_const_mul]
        ring

/-! ### Schwarz inequality, blocks -/

/-- **Schwarz inequality for a unital 2-positive map** (D7.23.4, vector form):
`‖Ψ(K) y‖² ≤ ⟨y, Ψ(K^*K) y⟩`. -/
theorem re_star_mulVec_dotProduct_le_of_twoPositive {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (h2 : IsNPositiveMap 2 Φ) (h1 : Φ 1 = 1) (K : Matrix n n ℂ) (y : n → ℂ) :
    (star (Φ K *ᵥ y) ⬝ᵥ (Φ K *ᵥ y)).re ≤ (star y ⬝ᵥ (Φ (Kᴴ * K) *ᵥ y)).re := by
  have hy := (kadison_schwarz_twoPositive Φ h2 h1 K).dotProduct_mulVec_nonneg y
  rw [Matrix.sub_mulVec, dotProduct_sub] at hy
  have hyre := (Complex.nonneg_iff.mp hy).1
  rw [Complex.sub_re] at hyre
  rw [star_mulVec_dotProduct_mulVec']
  linarith

/-- `M^{-iu}` through the real functional calculus: `cos(u log M) - i sin(u log M)`. -/
theorem imagPow_eq_cfc (hM : M.IsHermitian) (u : ℝ) :
    imagPow M u = cfc (fun x => Real.cos (u * Real.log x)) M -
      I • cfc (fun x => Real.sin (u * Real.log x)) M := by
  rw [imagPow_eq_eigen hM, cfc_eq_eigen hM, cfc_eq_eigen hM]
  have hd : (diagonal fun r => cexp (((-u : ℝ) : ℂ) * (I * (Real.log (hM.eigenvalues r) : ℂ)))) =
      (diagonal fun r => ((Real.cos (u * Real.log (hM.eigenvalues r)) : ℝ) : ℂ)) -
        I • diagonal fun r => ((Real.sin (u * Real.log (hM.eigenvalues r)) : ℝ) : ℂ) := by
    ext r t
    by_cases hrt : r = t
    · subst hrt
      simp only [diagonal_apply_eq, sub_apply, smul_apply, smul_eq_mul]
      rw [show ((-u : ℝ) : ℂ) * (I * (Real.log (hM.eigenvalues r) : ℂ)) =
        ((-(u * Real.log (hM.eigenvalues r))) : ℝ) * I by push_cast; ring, Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg]; ring
    · simp [diagonal_apply_ne _ hrt]
  rw [hd]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- `M^{-iu}` of a block-diagonal Hermitian matrix acts blockwise. -/
theorem imagPow_fromBlocks_diag {m : Type*} [Fintype m] [DecidableEq m] {X : Matrix n n ℂ}
    {Y : Matrix m m ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (u : ℝ) :
    imagPow (fromBlocks X 0 0 Y) u = fromBlocks (imagPow X u) 0 0 (imagPow Y u) := by
  have hXY : (fromBlocks X 0 0 Y).IsHermitian := by
    simp [IsHermitian, fromBlocks_conjTranspose, hX.eq, hY.eq]
  rw [imagPow_eq_cfc hXY, imagPow_eq_cfc hX, imagPow_eq_cfc hY, cfc_fromBlocks_diag hX hY,
    cfc_fromBlocks_diag hX hY, fromBlocks_smul]
  simp only [smul_zero]
  ext (i | i) (j | j) <;> simp

omit [DecidableEq n] in
theorem star_sumElim_zero_dotProduct {m : Type*} [Fintype m] (w : n → ℂ)
    (Z : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    star (Sum.elim w 0) ⬝ᵥ (Z *ᵥ Sum.elim w 0) = star w ⬝ᵥ (Z.toBlocks₁₁ *ᵥ w) := by
  conv_lhs => rw [← fromBlocks_toBlocks Z]
  rw [fromBlocks_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim]
  simp

end Matrix.Transport
