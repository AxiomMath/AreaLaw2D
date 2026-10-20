import AreaLawRefactored.S02_Preliminaries
import AreaLawForMathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Schwarz

/-!
# §3.1 A marginal spectral estimate

Digest `digest/03-initial-box.md` (D3.1–D3.2), paper `paper/sections/02-initial.tex`,
lines 15–212.
-/

namespace AreaLaw

open Arealaw OpenAI Matrix Complex Filter Topology Metric
open scoped InnerProductSpace ComplexConjugate ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

/-! ## The moment generating function `M(u)` of the surprisal -/

section Scalar

variable {α : Type*} [Fintype α] {p : α → ℝ}

variable (p) in
/-- D3.1. `M(u) = ∑ⱼ pⱼ^{1-u} = E e^{uK}` for the surprisal `K = -log pⱼ` with probability
`pⱼ`. -/
noncomputable def M (u : ℝ) : ℝ := ∑ j, p j * Real.exp (u * -Real.log (p j))

theorem M_pos (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (u : ℝ) : 0 < M p u := by
  obtain ⟨j, -, hj⟩ := (Finset.sum_pos_iff_of_nonneg fun j _ ↦ hp j).1 (hs ▸ one_pos)
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (hp j) (Real.exp_pos _).le)
    ⟨j, Finset.mem_univ _, mul_pos hj (Real.exp_pos _)⟩

theorem M_eq_sum_filter (hp : ∀ j, 0 ≤ p j) (u : ℝ) :
    M p u = ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < p j), p j * Real.exp (-u * Real.log (p j)) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases (hp j).lt_or_eq with hj | hj
  · rw [if_pos hj, neg_mul, mul_neg]
  · simp [← hj]

/-- D3.1. `L = log M` has `L(0) = 0` and `L'(0) = S`. -/
theorem hasDerivAt_log_M (hs : ∑ j, p j = 1) :
    HasDerivAt (fun u ↦ Real.log (M p u)) (H p) 0 := by
  have hM0 : M p 0 = 1 := by simpa [M] using hs
  have h : HasDerivAt (M p) (H p) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun j _ ↦
      (((hasDerivAt_id (0 : ℝ)).mul_const (-Real.log (p j))).exp).const_mul (p j)
    exact this.congr_deriv (by simp [H, Real.negMulLog])
  simpa [hM0] using h.log (by simp [hM0])

/-- D3.1.12. Iterating `L(t) ≤ 2 L(t/2) + κ t²` on `|t| ≤ r` from `L(0) = 0`, `L'(0) = S`
gives `L(u) ≤ u S + 2 κ u²`. -/
theorem step_3_1_12 {L : ℝ → ℝ} {S κ r : ℝ} (hL0 : L 0 = 0) (hd : HasDerivAt L S 0)
    (hstep : ∀ t, |t| ≤ r → L t ≤ 2 * L (t / 2) + κ * t ^ 2) {u : ℝ} (hu : |u| ≤ r) :
    L u ≤ u * S + 2 * κ * u ^ 2 := by
  set g : ℝ → ℝ := fun t ↦ L t - 2 * κ * t ^ 2
  have hg : HasDerivAt g S 0 := by
    simpa using hd.fun_sub ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (2 * κ))
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [hL0]
  have hiter (n : ℕ) : g u ≤ 2 ^ n * g (u / 2 ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hstep (u / 2 ^ n) (by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
        exact (div_le_self (abs_nonneg u) (one_le_pow₀ one_le_two)).trans hu)
      calc g u ≤ 2 ^ n * g (u / 2 ^ n) := ih
        _ ≤ 2 ^ n * (2 * g (u / 2 ^ n / 2)) := by gcongr; simp only [g]; linarith
        _ = 2 ^ (n + 1) * g (u / 2 ^ (n + 1)) := by rw [pow_succ, div_div]; ring
  have ht : Tendsto (fun n : ℕ ↦ u / 2 ^ n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two), Eventually.of_forall fun n ↦ by simp [hu0]⟩
  have hl : Tendsto (fun n : ℕ ↦ 2 ^ n * g (u / 2 ^ n)) atTop (𝓝 (u * S)) := by
    refine ((hg.tendsto_slope_zero.comp ht).const_mul u).congr fun n ↦ ?_
    simp only [Function.comp, zero_add, smul_eq_mul, g, hL0]
    field_simp
    ring
  have := ge_of_tendsto hl (Eventually.of_forall hiter)
  simp only [g] at this
  linarith

/-- D3.1.13. Exponential Markov at `u = ± r`: if `log M(± r) ≤ ± r S + C`, then
`P{|K - S| > w} ≤ 2 e^C e^{-r w}`. -/
theorem step_3_1_13 (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) {S C r w : ℝ} (hr : 0 < r)
    (hplus : Real.log (M p r) ≤ r * S + C) (hminus : Real.log (M p (-r)) ≤ -r * S + C) :
    ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < p j ∧ w < |-Real.log (p j) - S|), p j ≤
      2 * Real.exp C * Real.exp (-(r * w)) := by
  have hM (v : ℝ) (hv : Real.log (M p v) ≤ v * S + C) :
      ∑ j, p j * Real.exp (v * (-Real.log (p j) - S) - r * w) ≤
        Real.exp C * Real.exp (-(r * w)) := by
    have : ∑ j, p j * Real.exp (v * (-Real.log (p j) - S) - r * w) =
        Real.exp (-(v * S) - r * w) * M p v := by
      simp only [M, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_left_comm, ← Real.exp_add]
      ring_nf
    rw [this, ← Real.exp_log (M_pos hp hs v), ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc _ ≤ ∑ j, (p j * Real.exp (r * (-Real.log (p j) - S) - r * w) +
        p j * Real.exp (-r * (-Real.log (p j) - S) - r * w)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have h1 := mul_nonneg (hp j) (Real.exp_pos (r * (-Real.log (p j) - S) - r * w)).le
        have h2 := mul_nonneg (hp j) (Real.exp_pos (-r * (-Real.log (p j) - S) - r * w)).le
        split_ifs with h
        · rcases lt_abs.1 h.2 with h' | h'
          · nlinarith [hp j, Real.one_le_exp (show 0 ≤ r * (-Real.log (p j) - S) - r * w by
              nlinarith)]
          · nlinarith [hp j, Real.one_le_exp (show 0 ≤ -r * (-Real.log (p j) - S) - r * w by
              nlinarith)]
        · positivity
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith [hM r hplus, hM (-r) hminus]

end Scalar

/-! ## Three lines and the real quadratic bound -/

section Strip

variable {f : ℂ → ℂ}

/-- D3.1.7. Three lines on `0 ≤ Re z ≤ 1/4` with bounds `c` on `Re z = 0` and `c m` on
`|Re z| ≤ 1/4`, `log m ≤ 2ℓ`, `ℓ ≥ 1`: `|f| ≤ e c` on `|Re z| ≤ 1/(8ℓ)`. -/
theorem step_3_1_7 (hf : Differentiable ℂ f) {c m ℓ : ℝ} (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hℓ : 1 ≤ ℓ) (hlog : Real.log m ≤ 2 * ℓ) (him : ∀ y : ℝ, ‖f (y * I)‖ ≤ c)
    (hstrip : ∀ z : ℂ, |z.re| ≤ 1 / 4 → ‖f z‖ ≤ c * m) {z : ℂ} (hz : |z.re| ≤ 1 / (8 * ℓ)) :
    ‖f z‖ ≤ Real.exp 1 * c := by
  have key : ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ y : ℝ, ‖g (y * I)‖ ≤ c) →
      (∀ w : ℂ, |w.re| ≤ 1 / 4 → ‖g w‖ ≤ c * m) →
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 / (8 * ℓ) → ‖g w‖ ≤ Real.exp 1 * c := by
    intro g hg him hstrip w hw0 hw
    have hw4 : w.re ≤ 1 / 4 := hw.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    rcases hc.eq_or_lt with rfl | hc
    · simpa using hstrip w (by rwa [abs_of_nonneg hw0])
    have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' (f := g)
      (by norm_num : (0 : ℝ) < 1 / 4) ⟨hw0, hw4⟩ hg.diffContOnCl
      ⟨c * m, by rintro _ ⟨v, ⟨hv0, hv1⟩, rfl⟩; exact hstrip v (by rwa [abs_of_nonneg hv0])⟩
      (fun v (hv : v.re = 0) ↦ by
        rw [show v = (v.im : ℂ) * I from Complex.ext (by simp [hv]) (by simp)]; exact him v.im)
      (fun v (hv : v.re = 1 / 4) ↦ hstrip v (by rw [hv]; norm_num))
    rw [show (w.re - 0) / (1 / 4 - 0) = 4 * w.re by ring, Real.mul_rpow hc.le (by linarith),
      ← mul_assoc, ← Real.rpow_add hc, sub_add_cancel, Real.rpow_one] at h3
    have hpow : m ^ (4 * w.re) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos (by linarith)]
      have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 8 * ℓ)
      rw [mul_one_div_cancel (by positivity)] at this
      exact Real.exp_le_exp.2 (by nlinarith [Real.log_nonneg hm])
    calc ‖g w‖ ≤ c * m ^ (4 * w.re) := h3
      _ ≤ Real.exp 1 * c := by rw [mul_comm]; gcongr
  rcases le_total 0 z.re with h0 | h0
  · exact key f hf him hstrip z h0 ((le_abs_self _).trans hz)
  · simpa using key (fun w ↦ f (-w)) (hf.comp differentiable_neg)
      (fun y ↦ by simpa [neg_mul] using him (-y)) (fun w hw ↦ hstrip (-w) (by simpa using hw))
      (-z) (by simpa using h0) (by simpa [abs_of_nonpos h0] using hz)

/-- D3.1.8. If `f(-x) = conj f(x)` for real `x` and `|f| ≤ M₀` on `|Re z| ≤ δ`, then
`|Re (f(x) - f(0))| ≤ 2 M₀ x² δ⁻²` for real `|x| < δ`. -/
theorem step_3_1_8 (hf : Differentiable ℂ f) {M₀ δ : ℝ}
    (hM : ∀ z : ℂ, |z.re| ≤ δ → ‖f z‖ ≤ M₀) (hsymm : ∀ x : ℝ, f (-(x : ℂ)) = conj (f x))
    {x : ℝ} (hx : |x| < δ) : |(f x - f 0).re| ≤ 2 * M₀ * x ^ 2 / δ ^ 2 := by
  -- the even part `k(z) = f(z) + f(-z) - 2 f(0)` vanishes to second order at `0`
  set k : ℂ → ℂ := fun w ↦ f w + f (-w) - 2 * f 0
  have hk0 : k 0 = 0 := by simp only [k, neg_zero]; ring
  have hd : HasDerivAt k 0 0 := by
    have h1 := ((hf (-0)).hasDerivAt).comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
    simp only [neg_zero, mul_neg, mul_one] at h1
    have := ((hf 0).hasDerivAt.fun_add h1).sub_const (2 * f 0)
    rwa [add_neg_cancel] at this
  have ho : (fun w ↦ k w - k 0) =o[𝓝 0] fun w ↦ ‖w - 0‖ ^ 1 := by
    simpa using (hasDerivAt_iff_isLittleO.1 hd).norm_right
  have hmaps : Set.MapsTo k (Metric.ball 0 δ) (closedBall (k 0) (4 * M₀)) := fun w hw ↦ by
    have h1 : |w.re| ≤ δ := (abs_re_le_norm w).trans (mem_ball_zero_iff.1 hw).le
    rw [mem_closedBall, hk0, dist_zero_right]
    calc ‖k w‖ ≤ ‖f w‖ + ‖f (-w)‖ + 2 * ‖f 0‖ := by
          refine (norm_sub_le _ _).trans ?_; simp [norm_add_le]
      _ ≤ 4 * M₀ := by
          linarith [hM w h1, hM (-w) (by simpa using h1),
            hM 0 (by simpa using (abs_nonneg _).trans h1)]
  have hs := dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    (show Differentiable ℂ k from
      (hf.add (hf.comp differentiable_neg)).sub_const _).differentiableOn hmaps ho
    (z := (x : ℂ)) (by simpa using hx)
  rw [hk0, dist_zero_right, dist_zero_right, norm_real, Real.norm_eq_abs] at hs
  have hre : (f x - f 0).re = (k x).re / 2 := by simp [k, hsymm]; ring
  rw [hre, abs_div, abs_two]
  calc |(k x).re| / 2 ≤ ‖k x‖ / 2 := by gcongr; exact abs_re_le_norm _
    _ ≤ 4 * M₀ * (|x| / δ) ^ (1 + 1) / 2 := by gcongr
    _ = 2 * M₀ * x ^ 2 / δ ^ 2 := by rw [div_pow, sq_abs]; ring

end Strip

/-! ## Schmidt coordinates and the modular function `f` -/

section Schmidt

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The row `Θ(j, ·)` of a vector on `α × β`. -/
noncomputable def row (Θ : EuclideanSpace ℂ (α × β)) (j : α) : EuclideanSpace ℂ β :=
  WithLp.toLp 2 fun b ↦ Θ (j, b)

/-- D3.1.1. Schmidt form `Θ = ∑ⱼ √sⱼ eⱼ ⊗ gⱼ`, in coordinates where `eⱼ` is the standard
basis: the rows of `Θ` are orthogonal with `‖Θⱼ‖² = sⱼ`, i.e. the marginal on `α` is
`diag s`. -/
def IsSchmidt (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ) : Prop :=
  ∀ j k, ⟪row Θ j, row Θ k⟫_ℂ = if j = k then (s j : ℂ) else 0

/-- The matrix element `⟨Θⱼ, X_{jk} Θₖ⟩` between two rows. -/
noncomputable def pair (Θ : EuclideanSpace ℂ (α × β)) (X : Matrix (α × β) (α × β) ℂ)
    (j k : α) : ℂ :=
  ∑ b, ∑ b', star (Θ (j, b)) * X (j, b) (k, b') * Θ (k, b')

/-- D3.1.4. `f(z) = ⟨Θ, σ^z X σ^{-z} Θ⟩ = ∑ⱼₖ e^{z (log sⱼ - log sₖ)} ⟨Θⱼ, X_{jk} Θₖ⟩` for
`σ = diag s`, powers taken on the support. -/
noncomputable def modF (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ)
    (X : Matrix (α × β) (α × β) ℂ) (z : ℂ) : ℂ :=
  ∑ j, ∑ k, exp (z * ((Real.log (s j) - Real.log (s k) : ℝ) : ℂ)) * pair Θ X j k

/-- Weight the rows of a vector on `α × β` by scalars. -/
noncomputable def rowWeight (a : α → ℂ) (Θ : EuclideanSpace ℂ (α × β)) :
    EuclideanSpace ℂ (α × β) :=
  WithLp.toLp 2 fun x ↦ a x.1 * Θ x

theorem inner_rowWeight (a c : α → ℂ) (Θ : EuclideanSpace ℂ (α × β))
    (X : Matrix (α × β) (α × β) ℂ) :
    ⟪rowWeight a Θ, toEuclideanLin X (rowWeight c Θ)⟫_ℂ =
      ∑ j, ∑ k, star (a j) * c k * pair Θ X j k := by
  simp only [rowWeight, pair, PiLp.inner_apply, RCLike.inner_apply, toLpLin_apply, mulVec,
    dotProduct, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, star_def]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun b' _ ↦ ?_
  simp only [map_mul]
  ring

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem rowWeight_one (Θ : EuclideanSpace ℂ (α × β)) : rowWeight (fun _ ↦ 1) Θ = Θ := by
  ext x; simp [rowWeight]

omit [DecidableEq α] [DecidableEq β] in
theorem inner_rowWeight_rowWeight (a c : α → ℂ) (Θ : EuclideanSpace ℂ (α × β)) :
    ⟪rowWeight a Θ, rowWeight c Θ⟫_ℂ = ∑ j, star (a j) * c j * ⟪row Θ j, row Θ j⟫_ℂ := by
  simp only [rowWeight, row, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    Finset.mul_sum, star_def, map_mul]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

omit [DecidableEq α] [DecidableEq β] in
theorem norm_sq_eq_sum_row (Θ : EuclideanSpace ℂ (α × β)) :
    ‖Θ‖ ^ 2 = ∑ j, ‖row Θ j‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  rfl

omit [DecidableEq β] in
theorem IsSchmidt.sum_eq_norm_sq {Θ : EuclideanSpace ℂ (α × β)} {s : α → ℝ}
    (hΘ : IsSchmidt Θ s) : ∑ j, s j = ‖Θ‖ ^ 2 := by
  rw [norm_sq_eq_sum_row]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (row Θ j)
  rw [hΘ, if_pos rfl] at h
  simpa using h

theorem modF_zero (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ) (X : Matrix (α × β) (α × β) ℂ) :
    modF Θ s X 0 = ⟪Θ, toEuclideanLin X Θ⟫_ℂ := by
  have h := inner_rowWeight (fun _ ↦ (1 : ℂ)) (fun _ ↦ 1) Θ X
  rw [rowWeight_one] at h
  simp [h, modF]

/-- D3.1.5. On the imaginary axis `σ^{iy}` is unitary: `|f(iy)| ≤ ‖X‖ ‖Θ‖²`. -/
theorem norm_modF_mul_I_le (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ)
    (X : Matrix (α × β) (α × β) ℂ) (y : ℝ) :
    ‖modF Θ s X (y * I)‖ ≤ ‖X‖ * ‖Θ‖ ^ 2 := by
  set a : α → ℂ := fun j ↦ exp (-(y * Real.log (s j) : ℝ) * I)
  have hn : ‖rowWeight a Θ‖ = ‖Θ‖ := by
    simp [a, rowWeight, EuclideanSpace.norm_eq, Complex.norm_exp]
  have heq : modF Θ s X (y * I) = ⟪rowWeight a Θ, toEuclideanLin X (rowWeight a Θ)⟫_ℂ := by
    rw [inner_rowWeight, modF]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    simp only [a, star_def, ← exp_conj, map_mul, conj_I, ← exp_add, map_neg, conj_ofReal]
    push_cast
    ring_nf
  rw [heq]
  calc _ ≤ ‖rowWeight a Θ‖ * ‖toEuclideanLin X (rowWeight a Θ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖rowWeight a Θ‖ * (‖X‖ * ‖rowWeight a Θ‖) := by
        gcongr; exact Matrix.l2_opNorm_mulVec X _
    _ = ‖X‖ * ‖Θ‖ ^ 2 := by rw [hn]; ring

omit [DecidableEq α] [DecidableEq β] in
/-- D3.1.8. Hermiticity: `f(-x) = conj f(x)` for real `x`. -/
theorem modF_neg {X : Matrix (α × β) (α × β) ℂ} (hX : X.IsHermitian)
    (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ) (x : ℝ) :
    modF Θ s X (-(x : ℂ)) = conj (modF Θ s X x) := by
  simp only [modF, map_sum, map_mul, ← exp_conj, conj_ofReal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  have hp : conj (pair Θ X j k) = pair Θ X k j := by
    simp only [pair, star_def, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
    rw [← hX.apply (k, b) (j, b')]
    simp only [star_def]
    ring
  rw [hp]
  congr 2
  push_cast
  ring

omit [DecidableEq α] [DecidableEq β] in
theorem differentiable_modF (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ)
    (X : Matrix (α × β) (α × β) ℂ) : Differentiable ℂ (modF Θ s X) := by
  unfold modF; fun_prop

omit [DecidableEq α] [DecidableEq β] in
theorem modF_sum {κ : Type*} (t : Finset κ) (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ)
    (X : κ → Matrix (α × β) (α × β) ℂ) (z : ℂ) :
    modF Θ s (∑ i ∈ t, X i) z = ∑ i ∈ t, modF Θ s (X i) z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [modF, pair]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [modF, pair, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

omit [Fintype α] [DecidableEq α] in
theorem pair_kronecker (Θ : EuclideanSpace ℂ (α × β)) (c : Matrix α α ℂ) (d : Matrix β β ℂ)
    (j k : α) : pair Θ (c ⊗ₖ d) j k = c j k * ⟪row Θ j, toEuclideanLin d (row Θ k)⟫_ℂ := by
  simp only [pair, row, kroneckerMap_apply, PiLp.inner_apply, RCLike.inner_apply,
    toLpLin_apply, mulVec, dotProduct, star_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b' _ ↦ by ring

omit [DecidableEq α] [DecidableEq β] in
theorem modF_eq_zero_of_diag {Θ : EuclideanSpace ℂ (α × β)} {s : α → ℝ}
    {X : Matrix (α × β) (α × β) ℂ} (h : ∀ j k, j ≠ k → pair Θ X j k = 0) (z : ℂ) :
    modF Θ s X z = modF Θ s X 0 := by
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [h j k hjk]

/-- D3.1.3. A term `A ⊗ 1` on `α` commutes with `σ = diag s`: `f` is constant. -/
theorem modF_kronecker_one {Θ : EuclideanSpace ℂ (α × β)} {s : α → ℝ} (hΘ : IsSchmidt Θ s)
    (A : Matrix α α ℂ) (z : ℂ) :
    modF Θ s (A ⊗ₖ (1 : Matrix β β ℂ)) z = modF Θ s (A ⊗ₖ (1 : Matrix β β ℂ)) 0 :=
  modF_eq_zero_of_diag (fun j k hjk ↦ by
    rw [pair_kronecker, toLpLin_one, LinearMap.id_apply, hΘ, if_neg hjk, mul_zero]) z

omit [DecidableEq β] in
/-- D3.1.3. A term `1 ⊗ A` on `β` commutes with `σ`: `f` is constant. -/
theorem modF_one_kronecker (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ) (A : Matrix β β ℂ)
    (z : ℂ) : modF Θ s ((1 : Matrix α α ℂ) ⊗ₖ A) z = modF Θ s ((1 : Matrix α α ℂ) ⊗ₖ A) 0 := by
  classical
  exact modF_eq_zero_of_diag (fun j k hjk ↦ by rw [pair_kronecker, one_apply_ne hjk, zero_mul]) z

/-! ### D3.1.6 The crude strip bound -/

/-- D3.1.6. Row/column Cauchy–Schwarz: for weights `s ≥ 0`, `∑ s = 1`, and `C`, `D` whose rows
and columns have `ℓ²`-norm at most `a`, `b`: `∑ⱼₖ (sⱼ + sₖ) Cⱼₖ Dⱼₖ ≤ 2 a b`. -/
theorem sum_add_mul_le {ι : Type*} [Fintype ι] {s : ι → ℝ} (hs : ∀ j, 0 ≤ s j)
    (hsum : ∑ j, s j = 1) {C D : ι → ι → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hCr : ∀ j, ∑ k, C j k ^ 2 ≤ a ^ 2) (hCc : ∀ k, ∑ j, C j k ^ 2 ≤ a ^ 2)
    (hDr : ∀ j, ∑ k, D j k ^ 2 ≤ b ^ 2) (hDc : ∀ k, ∑ j, D j k ^ 2 ≤ b ^ 2) :
    ∑ j, ∑ k, (s j + s k) * (C j k * D j k) ≤ 2 * (a * b) := by
  have cs (f g : ι → ℝ) (hf : ∑ i, f i ^ 2 ≤ a ^ 2) (hg : ∑ i, g i ^ 2 ≤ b ^ 2) :
      ∑ i, f i * g i ≤ a * b :=
    abs_le_of_sq_le_sq' ((Finset.sum_mul_sq_le_sq_mul_sq _ f g).trans (by
      rw [mul_pow]; exact mul_le_mul hf hg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        (sq_nonneg _))) (mul_nonneg ha hb) |>.2
  calc ∑ j, ∑ k, (s j + s k) * (C j k * D j k)
      = ∑ j, s j * ∑ k, C j k * D j k + ∑ k, s k * ∑ j, C j k * D j k := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm (f := fun j k ↦ s k * (C j k * D j k))]
    _ ≤ ∑ j, s j * (a * b) + ∑ k, s k * (a * b) := by
        gcongr with j _ k _
        exacts [hs j, cs _ _ (hCr j) (hDr j), hs k, cs _ _ (hCc k) (hDc k)]
    _ = 2 * (a * b) := by rw [← Finset.sum_mul, hsum]; ring

/-- The normalized rows `Θⱼ / √sⱼ`, `0` where `sⱼ = 0`: the Schmidt vectors `gⱼ`. -/
noncomputable def unitRow (Θ : EuclideanSpace ℂ (α × β)) (s : α → ℝ) (j : α) :
    EuclideanSpace ℂ β :=
  ((Real.sqrt (s j) : ℂ))⁻¹ • row Θ j

section Rows

variable {Θ : EuclideanSpace ℂ (α × β)} {s : α → ℝ}

omit [Fintype α] [DecidableEq β] in
theorem row_eq_smul_unitRow (hs : ∀ j, 0 ≤ s j) (hΘ : IsSchmidt Θ s) (j : α) :
    row Θ j = (Real.sqrt (s j) : ℂ) • unitRow Θ s j := by
  by_cases h : s j = 0
  · have h0 : row Θ j = 0 := by rw [← inner_self_eq_zero (𝕜 := ℂ), hΘ]; simp [h]
    simp [h0, unitRow]
  · have : (Real.sqrt (s j) : ℂ) ≠ 0 := by
      rw [Ne, ofReal_eq_zero, Real.sqrt_eq_zero (hs j)]; exact h
    simp [unitRow, smul_smul, mul_inv_cancel₀ this]

omit [Fintype α] [DecidableEq β] in
theorem inner_unitRow (hs : ∀ j, 0 ≤ s j) (hΘ : IsSchmidt Θ s) (j k : α) :
    ⟪unitRow Θ s j, unitRow Θ s k⟫_ℂ = if j = k ∧ s j ≠ 0 then 1 else 0 := by
  simp only [unitRow, inner_smul_left, inner_smul_right, hΘ j k, map_inv₀, conj_ofReal]
  by_cases hjk : j = k
  · subst hjk
    by_cases h : s j = 0
    · simp [h]
    · have hsq : (Real.sqrt (s j) : ℂ) * Real.sqrt (s j) = s j := by
        rw [← ofReal_mul, Real.mul_self_sqrt (hs j)]
      have hne : (Real.sqrt (s j) : ℂ) ≠ 0 := by
        rw [Ne, ofReal_eq_zero, Real.sqrt_eq_zero (hs j)]; exact h
      simp only [ite_true, h, ne_eq, not_false_eq_true, and_self]
      rw [← hsq]; field_simp
  · simp [hjk]

omit [Fintype α] [DecidableEq β] in
theorem norm_unitRow_le (hs : ∀ j, 0 ≤ s j) (hΘ : IsSchmidt Θ s) (j : α) :
    ‖unitRow Θ s j‖ ≤ 1 := by
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (unitRow Θ s j)
  rw [inner_unitRow hs hΘ j j] at h2
  split_ifs at h2 <;> simp at h2 <;> nlinarith [norm_nonneg (unitRow Θ s j)]

omit [DecidableEq β] in
/-- Bessel's inequality for the Schmidt vectors `gⱼ`. -/
theorem sum_norm_inner_unitRow_sq_le (hs : ∀ j, 0 ≤ s j) (hΘ : IsSchmidt Θ s)
    (v : EuclideanSpace ℂ β) : ∑ k, ‖⟪unitRow Θ s k, v⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  classical
  have hon : Orthonormal ℂ (fun k : {k // s k ≠ 0} ↦ unitRow Θ s k) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_unitRow hs hΘ]
    by_cases h : i = j
    · subst h; simp [i.2]
    · simp [h, Subtype.ext_iff.not.mp h]
  calc ∑ k, ‖⟪unitRow Θ s k, v⟫_ℂ‖ ^ 2
      = ∑ k ∈ Finset.univ.filter (fun k ↦ s k ≠ 0), ‖⟪unitRow Θ s k, v⟫_ℂ‖ ^ 2 :=
        (Finset.sum_filter_of_ne fun k _ hk h0 ↦ by simp [unitRow, h0] at hk).symm
    _ = ∑ k : {k // s k ≠ 0}, ‖⟪unitRow Θ s k, v⟫_ℂ‖ ^ 2 :=
        Finset.sum_subtype _ (by simp) (fun k ↦ ‖⟪unitRow Θ s k, v⟫_ℂ‖ ^ 2)
    _ ≤ ‖v‖ ^ 2 := hon.sum_inner_products_le (s := Finset.univ) v

/-- D3.1.6. Crude strip bound: for `X = ∑ₐ cₐ ⊗ dₐ` and `|Re z| ≤ 1/4`,
`|f(z)| ≤ 2 ∑ₐ ‖cₐ‖ ‖dₐ‖`. -/
theorem step_3_1_6 (hs : ∀ j, 0 ≤ s j) (hsum : ∑ j, s j = 1) (hΘ : IsSchmidt Θ s)
    {κ : Type*} [Fintype κ] (c : κ → Matrix α α ℂ) (d : κ → Matrix β β ℂ) {z : ℂ}
    (hz : |z.re| ≤ 1 / 4) :
    ‖modF Θ s (∑ a, c a ⊗ₖ d a) z‖ ≤ 2 * ∑ a, ‖c a‖ * ‖d a‖ := by
  rw [modF_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  set ω := unitRow Θ s
  set D : α → α → ℂ := fun j k ↦ ⟪ω j, toEuclideanLin (d a) (ω k)⟫_ℂ
  -- `|sⱼ^{1/2+z} sₖ^{1/2-z}| ≤ sⱼ + sₖ` (weighted AM–GM)
  have hw (j k : α) : Real.exp (z.re * (Real.log (s j) - Real.log (s k))) *
      (Real.sqrt (s j) * Real.sqrt (s k)) ≤ s j + s k := by
    rcases (hs j).eq_or_lt with hj | hj
    · rw [← hj]; simp; linarith [hs k]
    rcases (hs k).eq_or_lt with hk | hk
    · rw [← hk]; simp; linarith [hs j]
    have hz' := abs_le.1 hz
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hj, Real.rpow_def_of_pos hk,
      ← Real.exp_add, ← Real.exp_add]
    have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 2 + z.re) (w₂ := 1 / 2 - z.re)
      (p₁ := s j) (p₂ := s k) (by linarith) (by linarith) hj.le hk.le (by ring)
    rw [Real.rpow_def_of_pos hj, Real.rpow_def_of_pos hk, ← Real.exp_add] at this
    calc _ = Real.exp (Real.log (s j) * (1 / 2 + z.re) + Real.log (s k) * (1 / 2 - z.re)) := by
          ring_nf
      _ ≤ (1 / 2 + z.re) * s j + (1 / 2 - z.re) * s k := this
      _ ≤ s j + s k := by nlinarith
  have hterm (j k : α) : ‖exp (z * ((Real.log (s j) - Real.log (s k) : ℝ) : ℂ)) *
      pair Θ (c a ⊗ₖ d a) j k‖ ≤ (s j + s k) * (‖c a j k‖ * ‖D j k‖) := by
    rw [pair_kronecker, row_eq_smul_unitRow hs hΘ j, row_eq_smul_unitRow hs hΘ k, map_smul,
      inner_smul_left, inner_smul_right, conj_ofReal]
    have : ‖exp (z * ((Real.log (s j) - Real.log (s k) : ℝ) : ℂ)) * (c a j k *
        ((Real.sqrt (s j) : ℂ) * ((Real.sqrt (s k) : ℂ) * D j k)))‖ =
        (Real.exp (z.re * (Real.log (s j) - Real.log (s k))) *
          (Real.sqrt (s j) * Real.sqrt (s k))) * (‖c a j k‖ * ‖D j k‖) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, norm_real, norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (hw j k) (by positivity)
  calc _ ≤ ∑ j, ∑ k, (s j + s k) * (‖c a j k‖ * ‖D j k‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ hterm j k))
    _ ≤ 2 * (‖c a‖ * ‖d a‖) := by
      -- rows and columns of `(dₐ)ⱼₖ = ⟨gⱼ, dₐ gₖ⟩` by Bessel, of `cₐ` by the operator norm
      have hd (A : Matrix β β ℂ) (j : α) : ‖toEuclideanLin A (ω j)‖ ^ 2 ≤ ‖A‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((Matrix.l2_opNorm_mulVec A _).trans
          (mul_le_of_le_one_right (norm_nonneg _) (norm_unitRow_le hs hΘ j))) 2
      have hcr (j : α) : ∑ k, ‖c a j k‖ ^ 2 ≤ ‖c a‖ ^ 2 := by
        have h := sum_norm_apply_sq_le_l2_opNorm_sq (c a)ᴴ j
        rw [l2_opNorm_conjTranspose] at h
        simpa [conjTranspose_apply] using h
      have hDr (j : α) : ∑ k, ‖D j k‖ ^ 2 ≤ ‖d a‖ ^ 2 := by
        have h := (sum_norm_inner_unitRow_sq_le hs hΘ _).trans (hd (d a)ᴴ j)
        rw [l2_opNorm_conjTranspose] at h
        refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ ↦ ?_) h
        simp only [D]
        rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right,
          norm_inner_symm]
      exact sum_add_mul_le hs hsum (norm_nonneg _) (norm_nonneg _) hcr
        (sum_norm_apply_sq_le_l2_opNorm_sq (c a)) hDr
        fun k ↦ (sum_norm_inner_unitRow_sq_le hs hΘ _).trans (hd (d a) k)


end Rows

/-! ### The tilt `Θ = F Ψ / √M(u)`, `F = ρ^{-u/2}` -/

section Tilt

variable {Ψ : EuclideanSpace ℂ (α × β)} {p : α → ℝ}

/-- D3.1.1. The tilted vector `Θ = F Ψ / √M(u)`, `F = diag (p^{-u/2})` on the support. -/
noncomputable def tilt (Ψ : EuclideanSpace ℂ (α × β)) (p : α → ℝ) (u : ℝ) :
    EuclideanSpace ℂ (α × β) :=
  rowWeight (fun j ↦ ((Real.exp (-(u / 2) * Real.log (p j)) / Real.sqrt (M p u) : ℝ) : ℂ)) Ψ

/-- D3.1.1. The marginal `σ = ρ^{1-u} / M(u)` of the tilt. -/
noncomputable def tiltSchmidt (p : α → ℝ) (u : ℝ) (j : α) : ℝ :=
  p j * Real.exp (u * -Real.log (p j)) / M p u

omit [DecidableEq β] in
/-- D3.1.1. `Θ` has Schmidt form with weights `σ = ρ^{1-u} / M(u)`. -/
theorem isSchmidt_tilt (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (hrow : IsSchmidt Ψ p)
    (u : ℝ) : IsSchmidt (tilt Ψ p u) (tiltSchmidt p u) := by
  intro j k
  have hrw (i : α) : row (tilt Ψ p u) i =
      ((Real.exp (-(u / 2) * Real.log (p i)) / Real.sqrt (M p u) : ℝ) : ℂ) • row Ψ i := by
    ext b; simp [row, tilt, rowWeight]
  rw [hrw, hrw, inner_smul_left, inner_smul_right, hrow]
  split_ifs with h
  · subst h
    have hM := M_pos hp hs u
    rw [conj_ofReal, ← ofReal_mul, ← ofReal_mul, tiltSchmidt]
    congr 1
    calc _ = Real.exp (-(u / 2) * Real.log (p j)) * Real.exp (-(u / 2) * Real.log (p j)) * p j /
          (Real.sqrt (M p u) * Real.sqrt (M p u)) := by ring
      _ = _ := by rw [← Real.exp_add, Real.mul_self_sqrt hM.le]; ring_nf
  · simp

omit [DecidableEq α] in
theorem tiltSchmidt_nonneg (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (u : ℝ) (j : α) :
    0 ≤ tiltSchmidt p u j :=
  div_nonneg (mul_nonneg (hp j) (Real.exp_pos _).le) (M_pos hp hs u).le

omit [DecidableEq α] in
theorem sum_tiltSchmidt (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (u : ℝ) :
    ∑ j, tiltSchmidt p u j = 1 := by
  unfold tiltSchmidt; rw [← Finset.sum_div]; exact div_self (M_pos hp hs u).ne'

omit [DecidableEq β] in
/-- D3.1.10. `⟨Ψ, Θ⟩ = M(u/2) / √M(u)`. -/
theorem inner_tilt (hrow : IsSchmidt Ψ p) (u : ℝ) :
    ⟪Ψ, tilt Ψ p u⟫_ℂ = ((M p (u / 2) / Real.sqrt (M p u) : ℝ) : ℂ) := by
  have h := inner_rowWeight_rowWeight (fun _ ↦ (1 : ℂ))
    (fun j ↦ ((Real.exp (-(u / 2) * Real.log (p j)) / Real.sqrt (M p u) : ℝ) : ℂ)) Ψ
  rw [rowWeight_one] at h
  rw [tilt, h, show M p (u / 2) = ∑ j, p j * Real.exp (u / 2 * -Real.log (p j)) from rfl,
    Finset.sum_div]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hrow, if_pos rfl, star_one, one_mul]
  ring_nf

/-- D3.1.4. At `z_u = -u / (2(1-u))`, `σ^{z_u} = M(u)^{-z_u} F`: the scalars cancel and
`f(z_u) = ⟨Θ, F X F⁻¹ Θ⟩ = ⟨F² Ψ, X Ψ⟩ / M(u)`. -/
theorem modF_tilt (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (hrow : IsSchmidt Ψ p) {u : ℝ}
    (hu : u ≠ 1) (X : Matrix (α × β) (α × β) ℂ) :
    modF (tilt Ψ p u) (tiltSchmidt p u) X (-u / (2 * (1 - u)) : ℝ) =
      ⟪rowWeight (fun j ↦ ((Real.exp (u * -Real.log (p j)) / M p u : ℝ) : ℂ)) Ψ,
        toEuclideanLin X Ψ⟫_ℂ := by
  have hM := M_pos hp hs u
  have h := inner_rowWeight (fun j ↦ ((Real.exp (u * -Real.log (p j)) / M p u : ℝ) : ℂ))
    (fun _ ↦ 1) Ψ X
  rw [rowWeight_one] at h
  rw [h, modF]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  have hz (i : α) (hi : p i = 0) (Y : Matrix (α × β) (α × β) ℂ) (i' : α) :
      pair Ψ Y i i' = 0 ∧ pair Ψ Y i' i = 0 := by
    have h0 : ∀ b, Ψ (i, b) = 0 := fun b ↦ by
      have : row Ψ i = 0 := by rw [← inner_self_eq_zero (𝕜 := ℂ), hrow]; simp [hi]
      simpa [row] using congrArg (fun v : EuclideanSpace ℂ β ↦ v b) this
    simp [pair, h0]
  have hpair : pair (tilt Ψ p u) X j k =
      ((Real.exp (-(u / 2) * Real.log (p j)) / Real.sqrt (M p u) *
        (Real.exp (-(u / 2) * Real.log (p k)) / Real.sqrt (M p u)) : ℝ) : ℂ) * pair Ψ X j k := by
    simp only [pair, tilt, rowWeight, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
    simp only [star_mul', star_def, conj_ofReal]; push_cast; ring
  rw [hpair]
  rcases (hp j).eq_or_lt with hj | hj
  · simp [(hz j hj.symm X k).1]
  rcases (hp k).eq_or_lt with hk | hk
  · simp [(hz k hk.symm X j).2]
  have hlog (i : α) (hi : 0 < p i) :
      Real.log (tiltSchmidt p u i) = (1 - u) * Real.log (p i) - Real.log (M p u) := by
    rw [tiltSchmidt, Real.log_div (mul_pos hi (Real.exp_pos _)).ne' hM.ne',
      Real.log_mul hi.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hlog j hj, hlog k hk, star_def, conj_ofReal, mul_one, ← ofReal_mul, ← ofReal_exp,
    ← mul_assoc, ← ofReal_mul]
  congr 2
  have h1u : (1 - u) ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
  rw [div_mul_div_comm, Real.mul_self_sqrt hM.le, ← mul_div_assoc, ← Real.exp_add,
    ← Real.exp_add]
  congr 2
  field_simp
  ring

end Tilt

end Schmidt

/-- D3.1.10. The gap `H - E₀ ≥ g₀ (1 - |Ω⟩⟨Ω|)` as a quadratic form:
`g₀ (‖ψ‖² - |⟨Ω, ψ⟩|²) ≤ Re ⟨ψ, H ψ⟩ - E₀ ‖ψ‖²`. -/
theorem gap_le {n
 : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    {E₀ g₀ : ℝ} {Ω : EuclideanSpace ℂ n} (hgap : HasGlobalGap H (WithLp.ofLp Ω) E₀ g₀)
    (ψ : EuclideanSpace ℂ n) :
    g₀ * (‖ψ‖ ^ 2 - ‖⟪Ω, ψ⟫_ℂ‖ ^ 2) ≤ (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 := by
  have h := (isPositive_toEuclideanLin_iff.2 (Matrix.le_iff.1 hgap)).re_inner_nonneg_right ψ
  have hP : toEuclideanLin (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ψ =
      ⟪Ω, ψ⟫_ℂ • Ω := by
    rw [← InnerProductSpace.symm_toEuclideanLin_rankOne, LinearEquiv.apply_symm_apply]
    exact InnerProductSpace.rankOne_apply Ω Ω ψ
  have hn : ⟪Ω, ψ⟫_ℂ * ⟪ψ, Ω⟫_ℂ = ((‖⟪Ω, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm ψ Ω, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, toLpLin_one,
    LinearMap.id_apply, hP, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hn,
    RCLike.re_to_complex] at h
  simp [← Complex.ofReal_pow] at h
  linarith



/-! ## D3.1.1–D3.1.10 in Schmidt coordinates -/

section Core

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- D3.1.5–D3.1.8 for one crossing term `X = ∑ₐ cₐ ⊗ dₐ`, `‖X‖ ≤ c₀`, `‖cₐ‖ ‖dₐ‖ ≤ c₀`, at most
`dᵢ²` products, `ℓᵢ = log (e dᵢ)`, `δᵢ = 1/(8ℓᵢ)`: `|Re (f(x) - f(0))| ≤ 128 e c₀ ℓᵢ² x²` for
real `|x| ≤ δᵢ/2`. -/
theorem step_3_1_8_term {Θ : EuclideanSpace ℂ (α × β)} {s : α → ℝ} (hs : ∀ j, 0 ≤ s j)
    (hsum : ∑ j, s j = 1) (hΘ : IsSchmidt Θ s) {X : Matrix (α × β) (α × β) ℂ}
    (hX : X.IsHermitian) {c₀ : ℝ} (hXn : ‖X‖ ≤ c₀) {κ : Type*} [Fintype κ]
    (c : κ → Matrix α α ℂ) (d : κ → Matrix β β ℂ) (hdec : X = ∑ a, c a ⊗ₖ d a)
    (hcd : ∀ a, ‖c a‖ * ‖d a‖ ≤ c₀) {dᵢ : ℕ} (hd : 1 ≤ dᵢ) (hκ : Fintype.card κ ≤ dᵢ ^ 2)
    {x : ℝ} (hx : |x| ≤ 1 / (8 * Real.log (Real.exp 1 * dᵢ)) / 2) :
    |(modF Θ s X x - modF Θ s X 0).re| ≤
      128 * Real.exp 1 * c₀ * Real.log (Real.exp 1 * dᵢ) ^ 2 * x ^ 2 := by
  set ℓ := Real.log (Real.exp 1 * dᵢ)
  have hc₀ : 0 ≤ c₀ := (norm_nonneg _).trans hXn
  have hd' : (1 : ℝ) ≤ dᵢ := by exact_mod_cast hd
  have hℓ0 : ℓ = 1 + Real.log dᵢ := by
    simp only [ℓ]; rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  have hℓ : 1 ≤ ℓ := by linarith [Real.log_nonneg hd']
  have hΘn : ‖Θ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← hΘ.sum_eq_norm_sq, hsum])
  -- D3.1.5
  have him (y : ℝ) : ‖modF Θ s X (y * I)‖ ≤ c₀ :=
    (norm_modF_mul_I_le Θ s X y).trans (by rw [hΘn, one_pow, mul_one]; exact hXn)
  -- D3.1.6
  have hstrip (z : ℂ) (hz : |z.re| ≤ 1 / 4) : ‖modF Θ s X z‖ ≤ c₀ * (2 * dᵢ ^ 2) := by
    rw [hdec]
    refine (step_3_1_6 hs hsum hΘ c d hz).trans ?_
    calc 2 * ∑ a, ‖c a‖ * ‖d a‖ ≤ 2 * ∑ _a : κ, c₀ := by gcongr with a; exact hcd a
      _ = c₀ * (2 * Fintype.card κ) := by simp; ring
      _ ≤ c₀ * (2 * dᵢ ^ 2) := by gcongr; exact_mod_cast hκ
  -- D3.1.7, with `log (2 dᵢ²) ≤ 2 ℓᵢ`
  have hlog : Real.log (2 * dᵢ ^ 2) ≤ 2 * ℓ := by
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow, hℓ0]
    push_cast; linarith [Real.log_two_lt_d9]
  have hnarrow (z : ℂ) (hz : |z.re| ≤ 1 / (8 * ℓ)) : ‖modF Θ s X z‖ ≤ Real.exp 1 * c₀ :=
    step_3_1_7 (differentiable_modF Θ s X) hc₀ (by nlinarith) hℓ hlog him hstrip hz
  -- D3.1.8
  have h8 := step_3_1_8 (differentiable_modF Θ s X) hnarrow (modF_neg hX Θ s)
    (hx.trans_lt (half_lt_self (by positivity)))
  calc _ ≤ 2 * (Real.exp 1 * c₀) * x ^ 2 / (1 / (8 * ℓ)) ^ 2 := h8
    _ = _ := by field_simp; ring

/-- D3.1.1–D3.1.10. In Schmidt coordinates `ℋ_B ⊗ ℋ_{B^c} = ℂ^α ⊗ ℂ^β` (`Ψ` with Schmidt weights
`p`; non-crossing terms `A ⊗ 1` or `1 ⊗ A`; crossing terms `i ∈ Cr` sums of at most `dᵢ²`
products), for `|u| ≤ [32 √((1+ϑ)𝓑)]⁻¹`: `M(u/2)² / M(u) ≥ 1 - v`, `v = 128 e ϑ 𝓑 u²`. -/
theorem step_3_1_10 {ι : Type*} [Fintype ι] {h : ι → Matrix (α × β) (α × β) ℂ} {c₀ g₀ E₀ : ℝ}
    {Cr : Finset ι} {dim : ι → ℕ} {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {c : ∀ i, κ i → Matrix α α ℂ} {d : ∀ i, κ i → Matrix β β ℂ} {Ψ : EuclideanSpace ℂ (α × β)}
    {p : α → ℝ} (hherm : ∀ i, (h i).IsHermitian) (hc₀ : 0 ≤ c₀) (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hone : ∀ i ∉ Cr, (∃ A, h i = A ⊗ₖ 1) ∨ ∃ A, h i = 1 ⊗ₖ A)
    (hdec : ∀ i ∈ Cr, h i = ∑ a, c i a ⊗ₖ d i a) (hcd : ∀ i ∈ Cr, ∀ a, ‖c i a‖ * ‖d i a‖ ≤ c₀)
    (hκ : ∀ i ∈ Cr, Fintype.card (κ i) ≤ dim i ^ 2) (hdim : ∀ i ∈ Cr, 1 ≤ dim i)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (hrow : IsSchmidt Ψ p) (hg₀ : 0 < g₀)
    (heig : toEuclideanLin (∑ i, h i) Ψ = (E₀ : ℂ) • Ψ)
    (hgap : HasGlobalGap (∑ i, h i) (WithLp.ofLp Ψ) E₀ g₀) {u : ℝ}
    (hu : |u| ≤ (32 * Real.sqrt ((1 + c₀ / g₀) *
      (1 + ∑ i ∈ Cr, Real.log (Real.exp 1 * dim i) ^ 2)))⁻¹) :
    1 - 128 * Real.exp 1 * (c₀ / g₀) * (1 + ∑ i ∈ Cr, Real.log (Real.exp 1 * dim i) ^ 2) * u ^ 2
      ≤ M p (u / 2) ^ 2 / M p u := by
  classical
  set ℓ : ι → ℝ := fun i ↦ Real.log (Real.exp 1 * dim i)
  set 𝓑 := 1 + ∑ i ∈ Cr, ℓ i ^ 2
  have hϑ : 0 ≤ c₀ / g₀ := div_nonneg hc₀ hg₀.le
  have hR : 1 ≤ Real.sqrt ((1 + c₀ / g₀) * 𝓑) := Real.one_le_sqrt.2 (by
    nlinarith [Finset.sum_nonneg fun i (_ : i ∈ Cr) ↦ sq_nonneg (ℓ i)])
  have hu32 : |u| ≤ 1 / 32 := hu.trans (by rw [one_div]; gcongr; linarith)
  -- D3.1.9: `|z_u| ≤ |u|` and `|z_u| ≤ 1/(32 ℓᵢ) = δᵢ/4`
  set z := -u / (2 * (1 - u))
  have hu1 : u ≠ 1 := fun h1 ↦ by rw [h1] at hu32; norm_num at hu32
  have hz : |z| ≤ |u| := by
    have := abs_le.1 hu32
    rw [abs_div, abs_neg, abs_mul, abs_two, abs_of_pos (by linarith : (0 : ℝ) < 1 - u),
      div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg u]
  have hzi : ∀ i ∈ Cr, |z| ≤ 1 / (8 * ℓ i) / 2 := fun i hi ↦ by
    have hℓR : ℓ i ≤ Real.sqrt ((1 + c₀ / g₀) * 𝓑) := Real.le_sqrt_of_sq_le (by
      nlinarith [Finset.single_le_sum (fun j (_ : j ∈ Cr) ↦ sq_nonneg (ℓ j)) hi])
    have hℓ1 : 0 < ℓ i := by
      simp only [ℓ]
      rw [Real.log_mul (Real.exp_pos 1).ne' (by have := hdim i hi; positivity), Real.log_exp]
      linarith [Real.log_nonneg (by exact_mod_cast hdim i hi : (1 : ℝ) ≤ dim i)]
    refine hz.trans (hu.trans ?_)
    rw [div_div, one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  -- D3.1.1: the tilt `Θ` with marginal `σ = ρ^{1-u} / M(u)`
  set Θ := tilt Ψ p u
  set σ := tiltSchmidt p u
  have hΘ := isSchmidt_tilt hp hs hrow u
  have hσ := tiltSchmidt_nonneg hp hs u
  have hσs := sum_tiltSchmidt hp hs u
  have hΘn : ‖Θ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← hΘ.sum_eq_norm_sq, hσs])
  -- D3.1.2 and D3.1.4: `E₀ = ⟨Θ, F H F⁻¹ Θ⟩ = f_H(z_u)`
  have hE : modF Θ σ (∑ i, h i) z = E₀ := by
    have h1 := inner_rowWeight_rowWeight
      (fun j ↦ ((Real.exp (u * -Real.log (p j)) / M p u : ℝ) : ℂ)) (fun _ ↦ 1) Ψ
    rw [rowWeight_one] at h1
    have h2 : ∑ j, star (((Real.exp (u * -Real.log (p j)) / M p u : ℝ) : ℂ)) * 1 *
        ⟪row Ψ j, row Ψ j⟫_ℂ = ((∑ j, tiltSchmidt p u j : ℝ) : ℂ) := by
      rw [ofReal_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hrow, if_pos rfl, star_def, conj_ofReal, tiltSchmidt]; push_cast; ring
    rw [modF_tilt hp hs hrow hu1, heig, inner_smul_right, h1, h2, hσs, ofReal_one, mul_one]
  have hsplit : (⟪Θ, toEuclideanLin (∑ i, h i) Θ⟫_ℂ).re - E₀ =
      ∑ i, (modF Θ σ (h i) 0 - modF Θ σ (h i) z).re := by
    rw [← modF_zero Θ σ, ← ofReal_re E₀, ← hE, ← sub_re, modF_sum, modF_sum,
      ← Finset.sum_sub_distrib, re_sum]
  -- D3.1.3: non-crossing terms contribute `0`; D3.1.5–D3.1.8 for the crossing terms
  have hterm (i : ι) : (modF Θ σ (h i) 0 - modF Θ σ (h i) z).re ≤
      if i ∈ Cr then 128 * Real.exp 1 * c₀ * ℓ i ^ 2 * u ^ 2 else 0 := by
    split_ifs with hi
    · have h1 := step_3_1_8_term hσ hσs hΘ (hherm i) (hnorm i) (c i) (d i) (hdec i hi)
        (hcd i hi) (hdim i hi) (hκ i hi) (hzi i hi)
      rw [← neg_sub, neg_re]
      calc _ ≤ |(modF Θ σ (h i) z - modF Θ σ (h i) 0).re| := neg_le_abs _
        _ ≤ _ := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [← sq_abs z, ← sq_abs u]; gcongr)
          (by positivity)
    · rcases hone i hi with ⟨A, hA⟩ | ⟨A, hA⟩
      · rw [hA, modF_kronecker_one hΘ A z, sub_self, zero_re]
      · rw [hA, modF_one_kronecker Θ σ A z, sub_self, zero_re]
  -- D3.1.9: `⟨Θ, (H - E₀) Θ⟩ ≤ 128 e c₀ 𝓑 u²`
  have hexc : (⟪Θ, toEuclideanLin (∑ i, h i) Θ⟫_ℂ).re - E₀ ≤
      128 * Real.exp 1 * c₀ * 𝓑 * u ^ 2 := by
    rw [hsplit]
    calc _ ≤ ∑ i, if i ∈ Cr then 128 * Real.exp 1 * c₀ * ℓ i ^ 2 * u ^ 2 else 0 :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = 128 * Real.exp 1 * c₀ * (∑ i ∈ Cr, ℓ i ^ 2) * u ^ 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by gcongr; linarith
  -- D3.1.10: the gap converts energy into overlap, `⟨Ψ, Θ⟩ = M(u/2) / √M(u)`
  have hg := gap_le hgap Θ
  rw [hΘn, inner_tilt hrow u, norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (M_pos hp hs u).le, one_pow, mul_one] at hg
  rw [show 128 * Real.exp 1 * (c₀ / g₀) * 𝓑 * u ^ 2 = 128 * Real.exp 1 * c₀ * 𝓑 * u ^ 2 / g₀ by
    ring, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hg₀]
  nlinarith

end Core

/-! ## The cut `B | U ∖ B` in the eigenbasis of `ρ` -/

section Transport

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem hasGlobalGap_submatrix {H : Matrix n n ℂ} {Ψ : n → ℂ} {E₀ g₀ : ℝ} (e : m ≃ n)
    (hgap : HasGlobalGap H Ψ E₀ g₀) : HasGlobalGap (H.submatrix e e) (Ψ ∘ e) E₀ g₀ := by
  rw [HasGlobalGap, Matrix.le_iff] at hgap ⊢
  convert (posSemidef_submatrix_equiv e).2 hgap using 1
  ext a b
  simp [Matrix.sub_apply, Matrix.smul_apply, one_apply, vecMulVec_apply, e.injective.eq_iff]

theorem hasGlobalGap_conj {H : Matrix n n ℂ} {Ψ : n → ℂ} {E₀ g₀ : ℝ}
    (hgap : HasGlobalGap H Ψ E₀ g₀) {W : Matrix m n ℂ} (hW : W * Wᴴ = 1) :
    HasGlobalGap (W * H * Wᴴ) (W *ᵥ Ψ) E₀ g₀ := by
  rw [HasGlobalGap, Matrix.le_iff] at hgap ⊢
  convert hgap.mul_mul_conjTranspose_same W using 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hW, mul_vecMulVec, vecMulVec_mul, star_mulVec]

end Transport

section Cut

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U B D : Finset σ}

/-- D3.1.6. Across the cut `B | U ∖ B`, a term supported on `D` is `∑_{a,b} E_{ab} ⊗ h_{ab}`:
`E_{ab}` the matrix units of `ℋ_{D ∩ B}` (extended by `1` to `B`),
`h_{ab} = (⟨a| ⊗ 1) X (|b⟩ ⊗ 1)` on `U ∖ B`. -/
theorem extendId_submatrix_eq_sum (hB : B ⊆ U) (hDU : D ⊆ U)
    (Y : Matrix (Reg loc D) (Reg loc D) ℂ) (w₀ : Reg loc (B \ (D ∩ B))) :
    (extendId hDU Y).submatrix (glueEquiv hB) (glueEquiv hB) =
      ∑ ab : Reg loc (D ∩ B) × Reg loc (D ∩ B),
        extendId Finset.inter_subset_right (single ab.1 ab.2 (1 : ℂ)) ⊗ₖ
          (extendId hDU Y).submatrix (fun z ↦ glue (glue ab.1 w₀ : Reg loc B) z)
            (fun z ↦ glue (glue ab.2 w₀ : Reg loc B) z) := by
  have hC (y y' : Reg loc B) (v v' : Reg loc (U \ B)) :
      restr (S := U \ D) Finset.sdiff_subset (glue y v) = restr Finset.sdiff_subset (glue y' v') ↔
        restr (S := B \ (D ∩ B)) Finset.sdiff_subset y = restr Finset.sdiff_subset y' ∧
          restr (S := (U \ B) \ D) Finset.sdiff_subset v = restr Finset.sdiff_subset v' := by
    simp only [restr, Finset.restrict₂, funext_iff, Subtype.forall, Finset.mem_sdiff,
      Finset.mem_inter, glue, not_and]
    constructor
    · intro h
      refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
      · simpa [hi.1] using h i ⟨hB hi.1, fun hD ↦ hi.2 hD hi.1⟩
      · simpa [hi.1.2] using h i ⟨hi.1.1, hi.2⟩
    · rintro ⟨hy, hv⟩ i ⟨hiU, hiD⟩
      by_cases hiB : i ∈ B
      · simpa [hiB] using hy i ⟨hiB, fun h _ ↦ hiD h⟩
      · simpa [hiB] using hv i ⟨⟨hiU, hiB⟩, hiD⟩
  have hD (y : Reg loc B) (v : Reg loc (U \ B)) :
      restr hDU (glue (glue (restr Finset.inter_subset_right y) w₀ : Reg loc B) v) =
        restr hDU (glue y v) :=
    funext fun i ↦ by
      by_cases hi : (i : σ) ∈ B <;> simp [restr, glue, Finset.restrict₂, hi, Finset.mem_inter]
  ext ⟨x, z⟩ ⟨x', z'⟩
  have hc (ab : Reg loc (D ∩ B) × Reg loc (D ∩ B)) :
      extendId Finset.inter_subset_right (single ab.1 ab.2 (1 : ℂ)) x x' =
        if restr (S := B \ (D ∩ B)) Finset.sdiff_subset x = restr Finset.sdiff_subset x' ∧
          ab = (restr Finset.inter_subset_right x, restr Finset.inter_subset_right x')
        then 1 else 0 := by
    simp only [extendId, of_apply, single_apply, Prod.ext_iff]
    split_ifs <;> tauto
  simp only [submatrix_apply, glueEquiv_apply, Matrix.sum_apply, kroneckerMap_apply, hc,
    ite_mul, one_mul, zero_mul]
  by_cases hx : restr (S := B \ (D ∩ B)) Finset.sdiff_subset x = restr Finset.sdiff_subset x'
  · simp only [hx, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [extendId, of_apply, hD, hC, hx, restr_glue_compl, true_and]
  · simp [hx, extendId, hC]

/-- D3.1.1. Schmidt form across the cut: for `V` the eigenvector unitary of
`ρ = Tr_{U∖B} |Ψ⟩⟨Ψ|`, the vector `(V* ⊗ 1) Ψ` has Schmidt weights the eigenvalues of `ρ`. -/
theorem isSchmidt_cut (hB : B ⊆ U) (Ψ : Reg loc U → ℂ) (hΨ : star Ψ ⬝ᵥ Ψ = 1) :
    let hρ := ((pureState Ψ hΨ).toSubState.restrict hB).psd.isHermitian
    IsSchmidt (WithLp.toLp 2 (((hρ.eigenvectorUnitary : Matrix (Reg loc B) (Reg loc B) ℂ)ᴴ ⊗ₖ
      (1 : Matrix (Reg loc (U \ B)) (Reg loc (U \ B)) ℂ)) *ᵥ (Ψ ∘ glueEquiv hB)))
      hρ.eigenvalues := by
  intro hρ j k
  set V : Matrix (Reg loc B) (Reg loc B) ℂ :=
    (hρ.eigenvectorUnitary : Matrix (Reg loc B) (Reg loc B) ℂ)
  set Φ := WithLp.toLp 2 ((Vᴴ ⊗ₖ (1 : Matrix (Reg loc (U \ B)) (Reg loc (U \ B)) ℂ)) *ᵥ
    (Ψ ∘ glueEquiv hB))
  have hd := hρ.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose] at hd
  have hr (i : Reg loc B) (b : Reg loc (U \ B)) :
      row Φ i b = ∑ a, star (V a i) * Ψ (glue a b) := by
    simp [Φ, row, mulVec, dotProduct, Fintype.sum_prod_type, one_apply]
  have key : ⟪row Φ j, row Φ k⟫_ℂ =
      (Vᴴ * ((pureState Ψ hΨ).toSubState.restrict hB).M * V) k j := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, hr, mul_apply, conjTranspose_apply,
      star_def, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    change _ = _ * (∑ z, Ψ (glue b z) * star (Ψ (glue a z))) * _
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ ↦ by simp only [star_def]; ring
  rw [key, hd, diagonal_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

/-- D3.1.1 and D3.1.3. In the basis `eⱼ ⊗ (·)` of `ℋ_B ⊗ ℋ_{U∖B}`, `eⱼ` the eigenvectors of `ρ`:
the ground vector has Schmidt weights `p`, a term with `Dᵢ ⊆ B` is `A ⊗ 1`, one with
`Dᵢ ⊆ U ∖ B` is `1 ⊗ A`, every term is a sum of products over the matrix units of
`ℋ_{Dᵢ ∩ B}` (D3.1.6), and norms, eigenequation and gap are unchanged. -/
theorem step_3_1_1 (hB : B ⊆ U) {ι : Type*} [Fintype ι] {D : ι → Finset σ}
    (hD : ∀ i, D i ⊆ U) {h : ι → Matrix (Reg loc U) (Reg loc U) ℂ}
    (hsupp : ∀ i, IsSupportedOn (hD i) (h i)) (hherm : ∀ i, (h i).IsHermitian) {c₀ E₀ g₀ : ℝ}
    (hnorm : ∀ i, ‖h i‖ ≤ c₀) (Ψ : Reg loc U → ℂ) (hΨ : star Ψ ⬝ᵥ Ψ = 1)
    (heig : (∑ i, h i) *ᵥ Ψ = (E₀ : ℂ) • Ψ) (hgap : HasGlobalGap (∑ i, h i) Ψ E₀ g₀) :
    ∃ (h' : ι → Matrix (Reg loc B × Reg loc (U \ B)) (Reg loc B × Reg loc (U \ B)) ℂ)
      (Ψ' : EuclideanSpace ℂ (Reg loc B × Reg loc (U \ B))),
      (∀ i, (h' i).IsHermitian) ∧ (∀ i, ‖h' i‖ ≤ c₀) ∧
      (∀ i, ¬((D i ∩ B).Nonempty ∧ (D i \ B).Nonempty) →
        (∃ A, h' i = A ⊗ₖ 1) ∨ ∃ A, h' i = 1 ⊗ₖ A) ∧
      (∀ i, ∃ (c : Reg loc (D i ∩ B) × Reg loc (D i ∩ B) → Matrix (Reg loc B) (Reg loc B) ℂ)
        (d : Reg loc (D i ∩ B) × Reg loc (D i ∩ B) →
          Matrix (Reg loc (U \ B)) (Reg loc (U \ B)) ℂ),
        h' i = ∑ a, c a ⊗ₖ d a ∧ ∀ a, ‖c a‖ * ‖d a‖ ≤ c₀) ∧
      IsSchmidt Ψ' ((pureState Ψ hΨ).toSubState.restrict hB).psd.isHermitian.eigenvalues ∧
      toEuclideanLin (∑ i, h' i) Ψ' = (E₀ : ℂ) • Ψ' ∧
      HasGlobalGap (∑ i, h' i) (WithLp.ofLp Ψ') E₀ g₀ := by
  classical
  obtain ⟨x₀⟩ : Nonempty (Reg loc U) := by
    by_contra hU
    rw [not_nonempty_iff] at hU
    simp [dotProduct, Finset.univ_eq_empty] at hΨ
  set e := glueEquiv (loc := loc) hB
  set V : Matrix (Reg loc B) (Reg loc B) ℂ :=
    (((pureState Ψ hΨ).toSubState.restrict hB).psd.isHermitian.eigenvectorUnitary :
      Matrix (Reg loc B) (Reg loc B) ℂ)
  set T := Vᴴ ⊗ₖ (1 : Matrix (Reg loc (U \ B)) (Reg loc (U \ B)) ℂ)
  have hV : Vᴴ * V = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hV' : V * Vᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  have hVn : ‖V‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self hV
  have hT : Tᴴ * T = 1 := by simp [T, conjTranspose_kronecker, ← mul_kronecker_mul, hV']
  have hT' : T * Tᴴ = 1 := by simp [T, conjTranspose_kronecker, ← mul_kronecker_mul, hV]
  have hTn : ‖T‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self hT
  have hconj (A : Matrix (Reg loc B) (Reg loc B) ℂ) (A' : Matrix (Reg loc (U \ B)) _ ℂ) :
      T * (A ⊗ₖ A') * Tᴴ = (Vᴴ * A * V) ⊗ₖ A' := by
    simp [T, conjTranspose_kronecker, ← mul_kronecker_mul]
  have hsum : ∑ i, T * (h i).submatrix e e * Tᴴ = T * (∑ i, h i).submatrix e e * Tᴴ := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    congr 2
    ext; simp [Matrix.sum_apply]
  refine ⟨fun i ↦ T * (h i).submatrix e e * Tᴴ, WithLp.toLp 2 (T *ᵥ (Ψ ∘ e)),
    fun i ↦ isHermitian_mul_mul_conjTranspose T ((hherm i).submatrix e), fun i ↦ ?_,
    fun i hi ↦ ?_, fun i ↦ ?_, isSchmidt_cut hB Ψ hΨ, ?_, ?_⟩
  · exact (l2_opNorm_mul_mul_le_of_le_one hTn (by rwa [l2_opNorm_conjTranspose]) _).trans
      ((l2_opNorm_submatrix _ _ _).trans_le (hnorm i))
  · -- D3.1.3: a term on one side of the cut is `A ⊗ 1` or `1 ⊗ A`
    obtain ⟨Y, hY⟩ := hsupp i
    simp only [not_and_or, Finset.not_nonempty_iff_eq_empty] at hi
    rcases hi with hi | hi
    · have hDB : D i ⊆ U \ B := fun x hx ↦ Finset.mem_sdiff.2 ⟨hD i hx, fun hxB ↦ by
        simpa [hi] using Finset.mem_inter.2 ⟨hx, hxB⟩⟩
      refine Or.inr ⟨extendId hDB Y, ?_⟩
      have : (h i).submatrix e e = 1 ⊗ₖ extendId hDB Y := by
        ext ⟨x, z⟩ ⟨x', z'⟩
        simp [hY, e, extendId_glue_of_subset_sdiff hB hDB, one_apply]
      beta_reduce
      rw [this, hconj, mul_one, hV]
    · have hDB : D i ⊆ B := Finset.sdiff_eq_empty_iff_subset.1 hi
      refine Or.inl ⟨Vᴴ * extendId hDB Y * V, ?_⟩
      have : (h i).submatrix e e = extendId hDB Y ⊗ₖ 1 := by
        ext ⟨x, z⟩ ⟨x', z'⟩
        simp [hY, e, extendId_glue_of_subset hB hDB, one_apply]
      beta_reduce
      rw [this, hconj]
  · -- D3.1.6: the matrix units of `ℋ_{Dᵢ ∩ B}`
    obtain ⟨Y, hY⟩ := hsupp i
    set w₀ : Reg loc (B \ (D i ∩ B)) := restr Finset.sdiff_subset (restr hB x₀)
    refine ⟨fun ab ↦ Vᴴ * extendId Finset.inter_subset_right (single ab.1 ab.2 (1 : ℂ)) * V,
      fun ab ↦ (h i).submatrix (fun z ↦ glue (glue ab.1 w₀ : Reg loc B) z)
        (fun z ↦ glue (glue ab.2 w₀ : Reg loc B) z), ?_, fun ab ↦ ?_⟩
    · simp only
      rw [hY, extendId_submatrix_eq_sum hB (hD i) Y w₀, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun ab _ ↦ hconj _ _
    · refine (mul_le_mul ((l2_opNorm_mul_mul_le_of_le_one
        (by rwa [l2_opNorm_conjTranspose]) hVn _).trans ?_)
        (l2_opNorm_submatrix_le _ (glue_right_injective _) (glue_right_injective _))
        (norm_nonneg _) zero_le_one).trans (by simpa using hnorm i)
      rw [extendId_eq_kronecker, l2_opNorm_submatrix]
      exact (l2_opNorm_kronecker_one_le _).trans (by simp)
  · rw [hsum]
    simp only [toLpLin_apply]
    rw [← WithLp.toLp_smul, mulVec_mulVec, mul_assoc (T * _), hT, mul_one, ← mulVec_mulVec,
      submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id, heig,
      show ((E₀ : ℂ) • Ψ) ∘ e = (E₀ : ℂ) • (Ψ ∘ e) from rfl, mulVec_smul]
  · rw [hsum]
    exact hasGlobalGap_conj (hasGlobalGap_submatrix e hgap) hT'

end Cut

/-! ## Lemma 3.1 -/

/-- D3.1 **Lemma 3.1** (`lem:tail`). Let `ℋ = ⨂_{v ∈ V} ℋ_v` be finite with finite-dimensional
factors, `𝖧 = ∑_{i ∈ 𝓘} hᵢ`, `hᵢ = hᵢ*`, `‖hᵢ‖ ≤ c₀`, `hᵢ` with support `Dᵢ ⊆ V`; unit ground
vector `Ψ`, `𝖧 Ψ = E₀ Ψ`, `g₀ > 0` with `𝖧 - E₀ ≥ g₀ (1 - |Ψ⟩⟨Ψ|)`. For a bipartition
`B ⊔ Bᶜ = V`, `𝓘× = {i : Dᵢ ∩ B ≠ ∅ ≠ Dᵢ ∩ Bᶜ}`, `ρ = Tr_{Bᶜ} |Ψ⟩⟨Ψ|`,
`dᵢ = ∏_{v ∈ Dᵢ} dim ℋ_v`, `𝓑 = 1 + ∑_{i ∈ 𝓘×} log² (e dᵢ)`, `ϑ = c₀/g₀`. Let `pⱼ` be the positive
eigenvalues of `ρ`, `K = -log pⱼ` with probability `pⱼ`, `S = S(ρ)`. Then
`log E e^{uK} ≤ u S + 512 e ϑ 𝓑 u²` for `|u| ≤ [32 √((1+ϑ)𝓑)]⁻¹`, and for every `w ≥ 0`
`P{|K - S| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1+ϑ)𝓑)))}`. -/
theorem lemma_3_1 {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] : MarginalTails σ loc ℂ := by
  intro U ι _ D hD h c₀ g₀ E₀ Ψ hΨ hsupp hherm hc₀ hnorm hg₀ heig hgap B hB ρ p 𝓑
  classical
  set ϑ := c₀ / g₀
  set r := (32 * Real.sqrt ((1 + ϑ) * 𝓑))⁻¹
  have hp : ∀ j, 0 ≤ p j := ρ.psd.eigenvalues_nonneg
  have hs : ∑ j, p j = 1 := by
    have h1 := ρ.psd.isHermitian.trace_eq_sum_eigenvalues
    have h2 := ((pureState Ψ hΨ).restrict hB).tr_eq_one
    rw [show ((pureState Ψ hΨ).restrict hB).M = ρ.M from rfl, h1] at h2
    simpa using h2
  have hS : ρ.entropy = H p := ρ.entropy_eq_H
  obtain ⟨x₀⟩ : Nonempty (Reg loc U) := by
    by_contra hU
    rw [not_nonempty_iff] at hU
    simp [dotProduct, Finset.univ_eq_empty] at hΨ
  -- D3.1.1: Schmidt coordinates across the cut
  obtain ⟨h', Ψ', hherm', hnorm', hone, hdec, hrow, heig', hgap'⟩ :=
    step_3_1_1 hB hD hsupp hherm hnorm Ψ hΨ heig hgap
  choose c d hdec hcd using hdec
  have hdim (i : ι) : 1 ≤ Fintype.card (Reg loc (D i)) :=
    Fintype.card_pos_iff.2 ⟨restr (hD i) x₀⟩
  have hκ (i : ι) : Fintype.card (Reg loc (D i ∩ B) × Reg loc (D i ∩ B)) ≤
      Fintype.card (Reg loc (D i)) ^ 2 := by
    rw [Fintype.card_prod, ← sq]
    refine Nat.pow_le_pow_left (Fintype.card_le_of_surjective
      (restr (S := D i ∩ B) Finset.inter_subset_left) fun y ↦ ?_) 2
    exact ⟨glue y (restr Finset.sdiff_subset (restr (hD i) x₀)), restr_glue _ _ _⟩
  -- D3.1.2–D3.1.10 for every admissible `t`
  have key (t : ℝ) (ht : |t| ≤ r) :
      1 - 128 * Real.exp 1 * ϑ * 𝓑 * t ^ 2 ≤ M p (t / 2) ^ 2 / M p t :=
    step_3_1_10 hherm' hc₀ hnorm' (fun i hi ↦ hone i (by simpa using hi))
      (fun i _ ↦ hdec i) (fun i _ ↦ hcd i) (fun i _ ↦ hκ i) (fun i _ ↦ hdim i) hp hs hrow hg₀
      heig' hgap' ht
  have hϑ : 0 ≤ ϑ := div_nonneg hc₀ hg₀.le
  have h𝓑 : 1 ≤ 𝓑 := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hr2 : r ^ 2 = 1 / (1024 * ((1 + ϑ) * 𝓑)) := by
    simp only [r]; rw [inv_pow, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hϑ1 : ϑ / (1 + ϑ) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  -- D3.1.11: `v ≤ e ϑ / (8 (1 + ϑ)) < 1/2` and `L(t) ≤ 2 L(t/2) + κ t²`, `κ = 256 e ϑ 𝓑`
  have halving (t : ℝ) (ht : |t| ≤ r) : Real.log (M p t) ≤
      2 * Real.log (M p (t / 2)) + 256 * Real.exp 1 * ϑ * 𝓑 * t ^ 2 := by
    have hv : 128 * Real.exp 1 * ϑ * 𝓑 * t ^ 2 ≤ 1 / 2 :=
      calc _ ≤ 128 * Real.exp 1 * ϑ * 𝓑 * r ^ 2 := mul_le_mul_of_nonneg_left
            (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2) (by positivity)
        _ = Real.exp 1 * (ϑ / (1 + ϑ)) / 8 := by rw [hr2]; field_simp; ring
        _ ≤ 3 * 1 / 8 := by gcongr
        _ ≤ 1 / 2 := by norm_num
    set v := 128 * Real.exp 1 * ϑ * 𝓑 * t ^ 2
    have hv0 : 0 ≤ v := by positivity
    have hM := M_pos hp hs t
    have h1 := Real.log_le_log (by linarith) (key t ht)
    rw [Real.log_div (pow_pos (M_pos hp hs _) 2).ne' hM.ne', Real.log_pow] at h1
    have h2 : (1 - v)⁻¹ ≤ 1 + 2 * v := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; nlinarith
    have h3 := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 - v)
    push_cast at h1
    linarith
  -- D3.1.12: `L(u) ≤ u S + 2κ u² = u S + 512 e ϑ 𝓑 u²`
  have hmgf (u : ℝ) (hu : |u| ≤ r) :
      Real.log (M p u) ≤ u * ρ.entropy + 512 * Real.exp 1 * ϑ * 𝓑 * u ^ 2 := by
    have := step_3_1_12 (L := fun t ↦ Real.log (M p t)) (by simp [M, hs])
      (hasDerivAt_log_M hs) halving hu
    rw [hS]; linarith
  refine ⟨fun u hu ↦ by rw [← M_eq_sum_filter hp]; exact hmgf u hu, fun w _ ↦ ?_⟩
  -- D3.1.13: exponential Markov at `u = ± r`, quadratic term `512 e ϑ 𝓑 r² ≤ e/2`
  have hr0 : 0 < r := by positivity
  have hq : 512 * Real.exp 1 * ϑ * 𝓑 * r ^ 2 ≤ Real.exp 1 / 2 :=
    calc _ = Real.exp 1 / 2 * (ϑ / (1 + ϑ)) := by rw [hr2]; field_simp; ring
      _ ≤ Real.exp 1 / 2 * 1 := by gcongr
      _ = _ := mul_one _
  have hplus := hmgf r (by rw [abs_of_pos hr0])
  have hminus := hmgf (-r) (by rw [abs_neg, abs_of_pos hr0])
  rw [neg_sq] at hminus
  refine le_min ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun j _ _ ↦ hp j).trans hs.le) ?_
  refine (step_3_1_13 hp hs hr0 (C := Real.exp 1 / 2) (w := w) (by linarith)
    (by linarith)).trans_eq ?_
  simp only [r]
  ring_nf

/-! ## D3.2 Lattice specialization of Lemma 3.1: the budget `𝓑` -/

section D32

open Finset


/-- D3.2. `C₁ = max {1, 2 v_R μ_R (1 + v_R log q)²}`. -/
noncomputable def C₁ (q R : ℕ) : ℝ := max 1 (2 * v R * μ R * (1 + v R * Real.log q) ^ 2)

/-- D3.2.2. For a support `X`: `log (e q^{|X|})² ≤ (1 + v_R log q)²`. -/
theorem log_sq_le_of_mem_supports {Λ X : Finset (ℤ × ℤ)} {R q : ℕ} (hq : 1 ≤ q)
    (hX : X ∈ supports Λ R) :
    Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤ (1 + v R * Real.log q) ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hc : (Fintype.card (Reg (Qudits q) X) : ℝ) = (q : ℝ) ^ #X := by
    simp [Reg, Fintype.card_pi]
  have hv : (#X : ℝ) ≤ v R := by exact_mod_cast (step_2_8 Λ R 0).2.2.2 X hX
  rw [hc, Real.log_mul (Real.exp_pos 1).ne' (pow_pos hq' _).ne', Real.log_exp, Real.log_pow]
  exact pow_le_pow_left₀ (by positivity) (by gcongr) 2

/-- D3.2.1–D3.2.3. `𝓑 ≤ 1 + 2 v_R μ_R (1 + v_R log q)² |∂_Λ B|`. -/
theorem step_3_2_3' (Λ B : Finset (ℤ × ℤ)) (R q : ℕ) (hq : 1 ≤ q) :
    1 + ∑ X ∈ supports Λ R with (X ∩ B).Nonempty ∧ (X \ B).Nonempty,
        Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
      1 + 2 * v R * μ R * (1 + v R * Real.log q) ^ 2 * #(edgeBoundary Λ B) := by
  -- D3.2.2
  have h1 := sum_le_card_nsmul {X ∈ supports Λ R | (X ∩ B).Nonempty ∧ (X \ B).Nonempty}
    (fun X => Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2) _ fun X hX =>
    log_sq_le_of_mem_supports (Λ := Λ) (R := R) hq (mem_filter.1 hX).1
  -- D3.2.1
  have h2 : (#{X ∈ supports Λ R | (X ∩ B).Nonempty ∧ (X \ B).Nonempty} : ℝ) ≤
      2 * v R * μ R * #(edgeBoundary Λ B) := by exact_mod_cast eq_crossing_count Λ B R
  rw [nsmul_eq_mul] at h1
  nlinarith [sq_nonneg (1 + v R * Real.log q)]

/-- D3.2.1–D3.2.3. `𝓑 ≤ C₁ (1 + |∂_Λ B|)`. -/
theorem step_3_2_3 (Λ B : Finset (ℤ × ℤ)) (R q : ℕ) (hq : 1 ≤ q) :
    1 + ∑ X ∈ supports Λ R with (X ∩ B).Nonempty ∧ (X \ B).Nonempty,
        Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) X)) ^ 2 ≤
      C₁ q R * (1 + #(edgeBoundary Λ B)) := by
  have hb : (0 : ℝ) ≤ #(edgeBoundary Λ B) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ C₁ q R := le_max_left _ _
  have h2 := le_max_right 1 (2 * v R * μ R * (1 + v R * Real.log q) ^ 2)
  refine (step_3_2_3' Λ B R q hq).trans ?_
  rw [mul_add, mul_one]
  gcongr
  exact h2

/-- D3.2.4. `C_M = 32 (M + 2) √((1 + ϑ) C₁)`. -/
noncomputable def C_M (ϑ C₁ M : ℝ) : ℝ := 32 * (M + 2) * √((1 + ϑ) * C₁)

/-- D3.2.4. If `𝓑 ≤ C₁ (1 + b')` and the tail of Lemma 3.1 at `w = C_M √(1 + b') log(n + 2)` is
`P ≤ 2 e^{e/2} exp(-w / (32 √((1 + ϑ) 𝓑)))`, then `P ≤ (n + 2)^{-M}` for every `n ≥ 1`. -/
theorem step_3_2_4 {ϑ 𝓑 C b M P : ℝ} {n : ℕ} (hn : 1 ≤ n) (hM : 0 ≤ M) (hϑ : 0 ≤ ϑ)
    (h𝓑 : 0 < 𝓑) (hb : 0 ≤ b) (h𝓑C : 𝓑 ≤ C * (1 + b))
    (htail : P ≤ 2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(C_M ϑ C M * √(1 + b) *
      Real.log (n + 2) / (32 * √((1 + ϑ) * 𝓑))))) :
    P ≤ ((n : ℝ) + 2) ^ (-M) := by
  set L := Real.log ((n : ℝ) + 2)
  have hn' : (3 : ℝ) ≤ n + 2 := by linarith [(by exact_mod_cast hn : (1 : ℝ) ≤ n)]
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hs : 0 < √((1 + ϑ) * 𝓑) := Real.sqrt_pos.2 (by positivity)
  -- `w / (32 √((1 + ϑ) 𝓑)) ≥ (M + 2) log(n + 2)`
  have hst : √((1 + ϑ) * 𝓑) ≤ √((1 + ϑ) * C) * √(1 + b) := by
    rw [← Real.sqrt_mul (by nlinarith), mul_assoc]
    exact Real.sqrt_le_sqrt (by gcongr)
  have hw : (M + 2) * L ≤ C_M ϑ C M * √(1 + b) * L / (32 * √((1 + ϑ) * 𝓑)) := by
    rw [le_div_iff₀ (by positivity), C_M]
    have : 0 ≤ (M + 2) * L := by positivity
    nlinarith
  -- `2 e^{e/2} < 8 < 9 ≤ (n + 2)²`
  have h8 : 2 * Real.exp (Real.exp 1 / 2) ≤ Real.exp (2 * L) := by
    have h4 : Real.exp 1 / 2 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      linarith [Real.exp_one_lt_d9, Real.log_two_gt_d9]
    have h2 : Real.log ((2 : ℝ) ^ 3) ≤ Real.log ((3 : ℝ) ^ 2) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h2
    have h3 : Real.log 3 ≤ L := Real.log_le_log (by norm_num) hn'
    calc 2 * Real.exp (Real.exp 1 / 2) ≤ Real.exp (Real.log 2) * Real.exp (Real.log 4) := by
          rw [Real.exp_log (by norm_num)]; gcongr
      _ = Real.exp (Real.log 2 + Real.log 4) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (2 * L) := by
          gcongr
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast at h2 ⊢; linarith
  rw [Real.rpow_def_of_pos (by linarith)]
  calc P ≤ Real.exp (2 * L) * Real.exp (-((M + 2) * L)) :=
        htail.trans (by gcongr)
    _ = Real.exp (L * -M) := by rw [← Real.exp_add]; ring_nf

end D32

end AreaLaw
