import Arealaw.SmoothEntropy
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The quantum equipartition property

BH12 Lemma 19 (\label{QEP}): for a product state `π₁ ⊗ ⋯ ⊗ πₙ` of `d`-dimensional states, the
smooth max-entropy per site exceeds the von Neumann entropy per site by at most
`4 log₂ d · √(log₂(2/ε²) / n)`.

## Main definitions

* `MState.piProd`: the tensor product `⨂ₖ πₖ` of a finite family of states.

## Main statements

* `MState.entropy_piProd`: von Neumann entropy is additive over `⨂ₖ πₖ`.
* `MState.smoothMaxEntropy_le_log_card_of_eq_mul_diagonal_mul`: keeping the eigenvalues on a
  set `S` gives `H_max^ε ≤ log #S` once the discarded weight fits in `ε`.
* `sum_rpow_one_sub_le_exp`: the one-site moment bound
  `∑ p^(1-s) ≤ exp(s H(p) + 5 s² log² d)`.
* `sum_filter_lt_le_exp`: the Chernoff bound on the light points of a product distribution.
* `MState.smoothMaxEntropy_le_of_le_or_le_one`: the case `n ≤ 16Λ ∨ d ≤ 1`.
* `smoothMaxEntropy_piProd_le_of_lt_one_of_lt_of_two_le`: the Chernoff case.  The case
  `ε ≥ 1` is `SubState.smoothMaxEntropy_eq_bot_of_one_le`.
* `smoothMaxEntropy_piProd_le`: the quantum equipartition property in nats,
  `H_max^ε ≤ H + 4 log d · √(n log₂(2/ε²))`.
* `smoothMaxEntropy₂_piProd_le`: the quantum equipartition property, per site and in bits.

## Implementation notes

BH12 prints the error coefficient `4d`.  We prove `4 log₂ d`, which implies it since
`log₂ d ≤ d`; its one use, in the proof of \label{saturationmaxmutualinfo}, is at block
dimension `d = 2^(l/c)`, where `4d` would be exponential in `l` and only `4 log₂ d` suffices.

TCR09 and Tom12 bound the fidelity-based Rényi-1/2 max-entropy with a different constant, not
the log-rank `smoothMaxEntropy₂` of BH12 Eq. (4), so the statement does not follow from them
verbatim and is proved directly, in nats, by a Chernoff bound on the product spectrum
`λ x = ∏ₖ pₖ(xₖ)`.  With `ℓ = log d`, `Λ = log₂(2/ε²)`, `H` the entropy and `t = 4ℓ√(nΛ)`:

* `ε ≥ 1`: the zero substate is in the ball.  `n ≤ 16Λ` or `d ≤ 1`: the dimension bound
  `nℓ ≤ t` suffices.
* Otherwise keep `S = {x | e^(-(H+t)) ≤ λ x}`.  Then `#S ≤ e^(H+t)`, and Markov's inequality on
  `λ^(-s)` bounds the discarded weight by `e^(-s(H+t)) ∏ₖ ∑ pₖ^(1-s)`.
* The moment bound avoids a Taylor expansion of `log ∑ p^(1-u)`.  Pointwise
  `e^x ≤ 1 + x + x² eˣ/2` for `x ≥ 0` reduces it to `∑ p^(1-s) log² p ≤ 10 ℓ²`, and
  `θ log(1/p) ≤ p^(-θ)/e` with `θ = 1/(2(ℓ+1))` and Jensen for `x^q` give that bound, valid
  for `d ≥ 2` and `s ℓ ≤ 1/10`.  The constant `5` leaves room: any constant below
  `4 / log 2 ≈ 5.77` closes the argument.
* `s = 2u/(5nℓ)` with `u = √(nΛ)` makes the exponent `-(4/5)Λ ≤ -Λ log 2 = log(ε²/2)`, and
  `n ≥ 16Λ` is exactly `s ℓ ≤ 1/10`.

Physlib's `MState.piProd` is on its own `ℂ`-only `MState`, so we own the `RCLike 𝕜` version;
the matrix layer `Matrix.piProd`, `Matrix.trace_piProd`, `Matrix.PosSemidef.piProd` is
Physlib's, and its algebra (`piProd_mul`, `piProd_conjTranspose`, `piProd_diagonal`) is here,
Physlib having none.
-/

namespace Arealaw

open Matrix
open scoped ComplexOrder MatrixOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The algebra of `Matrix.piProd` -/

section PiProd

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} {R : Type*}

theorem piProd_mul [CommSemiring R] [DecidableEq κ] [∀ k, Fintype (ι k)]
    (A B : ∀ k, Matrix (ι k) (ι k) R) :
    Matrix.piProd A * Matrix.piProd B = Matrix.piProd fun k => A k * B k := by
  ext x z
  simp only [Matrix.piProd, mul_apply, of_apply, Fintype.prod_sum, ← Finset.prod_mul_distrib]

theorem piProd_conjTranspose [CommSemiring R] [StarRing R] (A : ∀ k, Matrix (ι k) (ι k) R) :
    (Matrix.piProd A)ᴴ = Matrix.piProd fun k => (A k)ᴴ := by
  ext x y
  simp [Matrix.piProd, star_prod]

theorem piProd_diagonal [CommSemiring R] [∀ k, DecidableEq (ι k)] (f : ∀ k, ι k → R) :
    Matrix.piProd (fun k => diagonal (f k)) = diagonal fun x => ∏ k, f k (x k) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [Matrix.piProd]
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    simp only [Matrix.piProd, of_apply, diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (diagonal_apply_ne (f k) hk)

@[simp] theorem piProd_one [CommSemiring R] [∀ k, DecidableEq (ι k)] :
    Matrix.piProd (fun k => (1 : Matrix (ι k) (ι k) R)) = 1 := by
  simpa [← diagonal_one] using piProd_diagonal (R := R) fun k (_ : ι k) => (1 : R)

end PiProd

/-! ### Conjugated real diagonals -/

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem re_trace_mul_diagonal_mul {U : Matrix ι ι 𝕜} (hU : Uᴴ * U = 1) (f : ι → ℝ) :
    RCLike.re (U * diagonal (RCLike.ofReal ∘ f) * Uᴴ).trace = ∑ i, f i := by
  rw [trace_mul_cycle, hU, one_mul, trace_diagonal]
  simp [map_sum]

theorem posSemidef_mul_diagonal_mul (U : Matrix ι ι 𝕜) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (U * diagonal (RCLike.ofReal ∘ f) * Uᴴ).PosSemidef :=
  (PosSemidef.diagonal fun i => RCLike.ofReal_nonneg.mpr (hf i)).mul_mul_conjTranspose_same U

theorem mul_diagonal_mul_mul_diagonal_mul {U : Matrix ι ι 𝕜} (hU : Uᴴ * U = 1) (f g : ι → ℝ) :
    U * diagonal (RCLike.ofReal ∘ f) * Uᴴ * (U * diagonal (RCLike.ofReal ∘ g) * Uᴴ) =
      U * diagonal (RCLike.ofReal ∘ (f * g)) * Uᴴ := by
  rw [show U * diagonal (RCLike.ofReal ∘ f) * Uᴴ * (U * diagonal (RCLike.ofReal ∘ g) * Uᴴ) =
      U * diagonal (RCLike.ofReal ∘ f) * (Uᴴ * U) * diagonal (RCLike.ofReal ∘ g) * Uᴴ by
    simp only [Matrix.mul_assoc], hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
  simp [Function.comp_def]

/-- The square root of `U diag(f) Uᴴ` is `U diag(√f) Uᴴ`. -/
theorem cfcSqrt_mul_diagonal_mul {U : Matrix ι ι 𝕜} (hU : Uᴴ * U = 1) {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) :
    CFC.sqrt (U * diagonal (RCLike.ofReal ∘ f) * Uᴴ) =
      U * diagonal (RCLike.ofReal ∘ fun i => √(f i)) * Uᴴ := by
  refine (CFC.sqrt_eq_iff _ _ (posSemidef_mul_diagonal_mul U hf).nonneg
    (posSemidef_mul_diagonal_mul U fun i => Real.sqrt_nonneg _).nonneg).mpr ?_
  rw [mul_diagonal_mul_mul_diagonal_mul hU]
  congr 3
  funext i
  simp [Real.mul_self_sqrt (hf i)]

/-- **A diagonalization computes the entropy**: if `ρ = U diag(f) Uᴴ` for unitary `U`, then
`S(ρ) = H f`.  The state form of `EE_eq_of_unitary_diag`. -/
theorem SubState.entropy_eq_H_of_eq_mul_diagonal_mul (ρ : SubState ι 𝕜) {U : Matrix ι ι 𝕜}
    (hU₁ : U * Uᴴ = 1) (hU₂ : Uᴴ * U = 1) {f : ι → ℝ}
    (hρ : ρ.M = U * diagonal (RCLike.ofReal ∘ f) * Uᴴ) : ρ.entropy = H f := by
  have hchar : ρ.M.charpoly = (diagonal (RCLike.ofReal ∘ f)).charpoly := by
    rw [hρ, ← inv_eq_right_inv hU₁, charpoly_units_conj ⟨U, Uᴴ, hU₁, hU₂⟩]
  rw [SubState.entropy_eq_H,
    (IsHermitian.eigenvalues_eq_eigenvalues_iff _ (isHermitian_diagonal_ofReal f)).mpr hchar]
  exact H_eq_of_multiset_eq (eigenvalues_diagonal_multiset f)

open scoped Classical in
/-- **Smoothing by truncating the spectrum.**  Let `ρ = U diag(f) Uᴴ`.  Keeping the eigenvalues
on `S` gives a substate at purified distance `√(1 - (∑_S f)²)` of rank at most `#S`, so
`H_max^ε(ρ) ≤ log #S` whenever that distance is at most `ε`. -/
theorem MState.smoothMaxEntropy_le_log_card_of_eq_mul_diagonal_mul (ρ : MState ι 𝕜)
    {U : Matrix ι ι 𝕜} (hU : Uᴴ * U = 1) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hρ : ρ.M = U * diagonal (RCLike.ofReal ∘ f) * Uᴴ) (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε)
    (hS : 1 - (∑ i ∈ S, f i) ^ 2 ≤ ε ^ 2) :
    ρ.toSubState.smoothMaxEntropy ε ≤ ENNReal.log (S.card : ENNReal) := by
  have hsum : ∑ i, f i = 1 := by
    rw [← re_trace_mul_diagonal_mul hU, ← hρ, ρ.tr_eq_one]
  have hg : ∀ i, 0 ≤ (S : Set ι).indicator f i := Set.indicator_nonneg fun i _ => hf i
  let τ : SubState ι 𝕜 :=
    { M := U * diagonal (RCLike.ofReal ∘ (S : Set ι).indicator f) * Uᴴ
      psd := posSemidef_mul_diagonal_mul U hg
      tr_le_one := by
        rw [re_trace_mul_diagonal_mul hU, ← hsum]
        exact Finset.sum_le_sum fun i _ => Set.indicator_le_self' (fun i _ => hf i) i }
  have hτtr : RCLike.re τ.M.trace = ∑ i ∈ S, f i := by
    rw [re_trace_mul_diagonal_mul hU, Finset.sum_indicator_subset _ (Finset.subset_univ S)]
  -- `√ρ √τ = τ`, which is positive, so the fidelity is the kept weight.
  have hfid : fidelity ρ.M τ.M = ∑ i ∈ S, f i := by
    have hmul : (fun i => √(f i)) * (fun i => √((S : Set ι).indicator f i)) =
        (S : Set ι).indicator f := by
      funext i
      by_cases hi : i ∈ S <;> simp [hi, Real.mul_self_sqrt (hf i)]
    rw [fidelity_def, hρ, cfcSqrt_mul_diagonal_mul hU hf, cfcSqrt_mul_diagonal_mul hU hg,
      mul_diagonal_mul_mul_diagonal_mul hU, hmul, ← hτtr]
    exact_mod_cast congrArg RCLike.re τ.psd.traceNorm_eq_trace
  have hball : τ ∈ ρ.toSubState.ball ε := by
    rw [SubState.mem_ball, SubState.D_def, SubState.F_def, ρ.tr_eq_one, sub_self, zero_mul,
      Real.sqrt_zero, add_zero, hfid]
    exact Real.sqrt_le_iff.mpr ⟨hε, hS⟩
  refine (ρ.toSubState.smoothMaxEntropy_le_of_mem hball).trans (ENNReal.log_monotone ?_)
  have hrank : τ.M.rank ≤ S.card := by
    refine (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans ?_)
    rw [rank_diagonal, Fintype.card_subtype]
    refine Finset.card_le_card fun i hi => ?_
    by_contra h
    simp [h] at hi
  exact_mod_cast hrank

end Diagonal

/-! ### Product states -/

namespace MState

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- The tensor product `⨂ₖ πₖ`, with entries `∏ₖ πₖ(xₖ, yₖ)`. -/
def piProd (π : ∀ k, MState (ι k) 𝕜) : MState (∀ k, ι k) 𝕜 :=
  mk' (Matrix.PosSemidef.piProd fun k => (π k).psd) <| by
    simp [Matrix.trace_piProd, trace_eq_one]

/-- The density matrix of a tensor product of states is the tensor product of their matrices. -/
@[simp] theorem piProd_M (π : ∀ k, MState (ι k) 𝕜) :
    (piProd π).M = Matrix.piProd fun k => (π k).M :=
  rfl

variable [∀ k, DecidableEq (ι k)]

/-- The product of the factors' eigenbases diagonalizes `⨂ₖ πₖ`, with eigenvalues
`∏ₖ pₖ(xₖ)`. -/
theorem exists_piProd_M_eq_mul_diagonal_mul (π : ∀ k, MState (ι k) 𝕜) :
    ∃ V : Matrix (∀ k, ι k) (∀ k, ι k) 𝕜, V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
      (piProd π).M = V *
        diagonal (RCLike.ofReal ∘ fun x => ∏ k, (π k).psd.isHermitian.eigenvalues (x k)) * Vᴴ := by
  let U k : Matrix (ι k) (ι k) 𝕜 := (π k).psd.isHermitian.eigenvectorUnitary
  have hU k : U k ∈ unitaryGroup (ι k) 𝕜 := (π k).psd.isHermitian.eigenvectorUnitary.2
  refine ⟨Matrix.piProd U, ?_, ?_, ?_⟩
  · rw [piProd_conjTranspose, piProd_mul, ← piProd_one]
    exact congrArg Matrix.piProd (funext fun k => mem_unitaryGroup_iff.mp (hU k))
  · rw [piProd_conjTranspose, piProd_mul, ← piProd_one]
    exact congrArg Matrix.piProd (funext fun k => mem_unitaryGroup_iff'.mp (hU k))
  · have hD : diagonal (RCLike.ofReal ∘ fun x => ∏ k, (π k).psd.isHermitian.eigenvalues (x k)) =
        Matrix.piProd fun k => diagonal (RCLike.ofReal ∘ (π k).psd.isHermitian.eigenvalues :
          ι k → 𝕜) := by
      simp [piProd_diagonal, Function.comp_def]
    rw [piProd_M, piProd_conjTranspose, hD, piProd_mul, piProd_mul]
    exact congrArg Matrix.piProd (funext fun k => (π k).psd.isHermitian.spectral_theorem)

/-- **Von Neumann entropy is additive over tensor products.** -/
theorem entropy_piProd (π : ∀ k, MState (ι k) 𝕜) :
    (piProd π).entropy = ∑ k, (π k).entropy := by
  obtain ⟨V, hV₁, hV₂, hρ⟩ := exists_piProd_M_eq_mul_diagonal_mul π
  rw [SubState.entropy_eq_H_of_eq_mul_diagonal_mul _ hV₁ hV₂ hρ,
    H_prod_eq_sum _ fun k => (π k).sum_eigenvalues_eq_one]
  simp [SubState.entropy_eq_H]

end MState

/-! ### Scalar inequalities -/

section Scalar

/-- `eˣ ≤ 1 + x + x² eˣ / 2` for `x ≥ 0`.  The bound fails for `x ≪ 0`. -/
theorem exp_le_one_add_add_sq_mul_exp_div_two {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp x / 2 := by
  let g : ℝ → ℝ := fun x => 1 + x + x ^ 2 * Real.exp x / 2 - Real.exp x
  have hg y : HasDerivAt g (1 + y * Real.exp y + y ^ 2 * Real.exp y / 2 - Real.exp y) y := by
    have h := (((hasDerivAt_id' y).const_add 1).add
      ((((hasDerivAt_id' y).pow 2).mul (Real.hasDerivAt_exp y)).div_const 2)).sub
        (Real.hasDerivAt_exp y)
    exact h.congr_deriv (by simp; ring)
  -- `g' ≥ 0` follows from `eʸ (1 - y) ≤ 1`, i.e. `1 - y ≤ e^(-y)`.
  have hmono : Monotone g := monotone_of_deriv_nonneg (fun y => (hg y).differentiableAt)
    fun y => by
      have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-y)) (Real.exp_pos y).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
      rw [(hg y).deriv]
      nlinarith [mul_nonneg (sq_nonneg y) (Real.exp_pos y).le]
  have := hmono hx
  simp [g] at this
  linarith

/-- Second-order expansion of `p^(1-s) = p e^(s log(1/p))`, needing `p ≤ 1` so the exponent
is nonnegative. -/
theorem rpow_one_sub_le {p s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    p ^ (1 - s) ≤ p + s * Real.negMulLog p + s ^ 2 / 2 * (p ^ (1 - s) * Real.log p ^ 2) := by
  rcases hp0.eq_or_lt with rfl | hp
  · simp [Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
  have hx : 0 ≤ s * -Real.log p := mul_nonneg hs0 (neg_nonneg.mpr (Real.log_nonpos hp.le hp1))
  have hrpow : p ^ (1 - s) = p * Real.exp (s * -Real.log p) := by
    rw [Real.rpow_def_of_pos hp, ← Real.exp_log hp, ← Real.exp_add, Real.log_exp]; ring_nf
  have h := mul_le_mul_of_nonneg_left (exp_le_one_add_add_sq_mul_exp_div_two hx) hp.le
  rw [hrpow, Real.negMulLog]
  nlinarith [h]

/-- `log² p ≤ p^(-2θ) / (θ e)²` on `(0, 1]`, from `log y ≤ y - 1` at `y = p^(-θ) / e`. -/
theorem sq_log_le_rpow {p θ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hθ : 0 < θ) :
    Real.log p ^ 2 ≤ p ^ (-(2 * θ)) / (θ * Real.exp 1) ^ 2 := by
  have h := Real.log_le_sub_one_of_pos
    (div_pos (Real.rpow_pos_of_pos hp (-θ)) (Real.exp_pos 1))
  rw [Real.log_div (Real.rpow_pos_of_pos hp _).ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_rpow hp] at h
  have hl : 0 ≤ -Real.log p := neg_nonneg.mpr (Real.log_nonpos hp.le hp1)
  have key : θ * -Real.log p ≤ p ^ (-θ) / Real.exp 1 := by linarith
  rw [show -(2 * θ) = -θ + -θ by ring, Real.rpow_add hp, le_div_iff₀ (by positivity)]
  calc Real.log p ^ 2 * (θ * Real.exp 1) ^ 2 = (θ * -Real.log p) ^ 2 * Real.exp 1 ^ 2 := by ring
    _ ≤ (p ^ (-θ) / Real.exp 1) ^ 2 * Real.exp 1 ^ 2 := by gcongr
    _ = p ^ (-θ) * p ^ (-θ) := by field_simp

/-- The numerical core of `sum_rpow_one_sub_mul_sq_log_le`, with 3% to spare at
`ℓ = log 2`. -/
private theorem four_mul_exp_mul_sq_le {ℓ : ℝ} (hℓ : Real.log 2 ≤ ℓ) :
    4 * Real.exp (1 / 10) * (ℓ + 1) ^ 2 ≤ 10 * Real.exp 1 * ℓ ^ 2 := by
  have hl := Real.log_two_gt_d9
  have he := Real.exp_one_gt_d9
  have hE : Real.exp (1 / 10) < 10 / 9 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 10) (by norm_num) (by norm_num)
    norm_num at this ⊢; linarith
  have h1 : (ℓ + 1) ^ 2 ≤ (2.443 * ℓ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hE0 := Real.exp_pos (1 / 10)
  nlinarith [sq_nonneg ℓ]

end Scalar

/-! ### The one-site moment bound -/

section Moment

variable {ι : Type*} [Fintype ι] {p : ι → ℝ}

/-- Each entry of a probability vector is at most one. -/
theorem le_one_of_sum_eq_one (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : ι) : p i ≤ 1 :=
  hsum ▸ Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)

/-- **Power-mean bound**: a probability vector on `N` points has `∑ pᵢ^q ≤ N^(1-q)` for
`0 ≤ q ≤ 1`, by Jensen for the concave `x ↦ x^q`. -/
theorem sum_rpow_le_card_rpow (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    ∑ i, p i ^ q ≤ (Fintype.card ι : ℝ) ^ (1 - q) := by
  have hN : (0 : ℝ) < Fintype.card ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · simp at hsum
    · exact_mod_cast Fintype.card_pos
  have h := (Real.concaveOn_rpow hq0 hq1).le_map_sum (t := Finset.univ)
    (w := fun _ => (Fintype.card ι : ℝ)⁻¹) (p := p) (fun _ _ => by positivity)
    (by simp [Finset.card_univ, hN.ne']) (fun i _ => hp i)
  simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one] at h
  rw [Real.inv_rpow hN.le, inv_mul_le_iff₀ hN] at h
  rwa [Real.rpow_sub hN, Real.rpow_one, div_eq_mul_inv]

/-- **Second-order expansion of the moment**: a probability vector `p` has
`∑ p^(1-s) ≤ 1 + s H(p) + (s²/2) ∑ p^(1-s) log² p` for `0 ≤ s < 1`. -/
theorem sum_rpow_one_sub_le_one_add (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∑ i, p i ^ (1 - s) ≤
      1 + s * H p + s ^ 2 / 2 * ∑ i, p i ^ (1 - s) * Real.log (p i) ^ 2 := by
  calc ∑ i, p i ^ (1 - s)
      ≤ ∑ i, (p i + s * Real.negMulLog (p i) +
          s ^ 2 / 2 * (p i ^ (1 - s) * Real.log (p i) ^ 2)) :=
        Finset.sum_le_sum fun i _ =>
          rpow_one_sub_le (hp i) (le_one_of_sum_eq_one hp hsum i) hs0 hs1
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, H]

/-- Summing `log² p ≤ p^(-2θ) / (θe)²` against `p^r`: for `0 ≤ p ≤ 1` and `θ > 0`,
`∑ p^r log² p ≤ ∑ p^(r-2θ) / (θe)²`. -/
theorem sum_rpow_mul_sq_log_le (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (r : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∑ i, p i ^ r * Real.log (p i) ^ 2 ≤ (∑ i, p i ^ (r - 2 * θ)) / (θ * Real.exp 1) ^ 2 := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases (hp i).eq_or_lt with h | h
  · rw [← h, Real.log_zero, zero_pow two_ne_zero, mul_zero]
    positivity
  · calc p i ^ r * Real.log (p i) ^ 2
        ≤ p i ^ r * (p i ^ (-(2 * θ)) / (θ * Real.exp 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (sq_log_le_rpow h (hp1 i) hθ) (by positivity)
      _ = _ := by rw [mul_div_assoc', ← Real.rpow_add h]; ring_nf

/-- The power mean at exponent `1 - s - 1/(log d + 1)`: a probability vector `p` on `d ≥ 2`
points has `∑ p^(1 - s - 1/(log d + 1)) ≤ e^(1/10) e` for `0 ≤ s` with `s log d ≤ 1/10`. -/
theorem sum_rpow_one_sub_sub_le (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {s : ℝ} (hs : 0 ≤ s)
    (hℓ : Real.log 2 ≤ Real.log (Fintype.card ι))
    (hsℓ : s * Real.log (Fintype.card ι) ≤ 1 / 10) :
    ∑ i, p i ^ (1 - s - 1 / (Real.log (Fintype.card ι) + 1)) ≤
      Real.exp (1 / 10) * Real.exp 1 := by
  set ℓ := Real.log (Fintype.card ι)
  have hl2 := Real.log_two_gt_d9
  have hℓ0 : 0 < ℓ := by linarith
  have hN : (0 : ℝ) < Fintype.card ι :=
    Nat.cast_pos.mpr <| Nat.pos_of_ne_zero fun h => by simp [ℓ, h] at hℓ0
  have hx0 : 0 < 1 / (ℓ + 1) := by positivity
  have hx : 1 / (ℓ + 1) * (ℓ + 1) = 1 := by field_simp
  have hs10 : s * 0.6931471803 ≤ 1 / 10 := le_trans (by nlinarith) hsℓ
  refine (sum_rpow_le_card_rpow hp hsum ?_ (by linarith)).trans ?_
  · nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ ℓ - 0.6931471803)]
  rw [Real.rpow_def_of_pos hN, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- **Tilted second moment**: a probability vector `p` on `d ≥ 2` points has
`∑ p^(1-s) log² p ≤ 10 log² d` for `0 ≤ s` with `s log d ≤ 1/10`.  Take
`θ = 1/(2(log d + 1))` in `sum_rpow_mul_sq_log_le` and bound the remaining sum by
`sum_rpow_one_sub_sub_le`. -/
theorem sum_rpow_one_sub_mul_sq_log_le (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {s : ℝ}
    (hs : 0 ≤ s) (hℓ : Real.log 2 ≤ Real.log (Fintype.card ι))
    (hsℓ : s * Real.log (Fintype.card ι) ≤ 1 / 10) :
    ∑ i, p i ^ (1 - s) * Real.log (p i) ^ 2 ≤ 10 * Real.log (Fintype.card ι) ^ 2 := by
  set ℓ := Real.log (Fintype.card ι)
  have hl2 := Real.log_two_gt_d9
  have hℓ1 : 0 < ℓ + 1 := by linarith
  set θ : ℝ := 1 / (2 * (ℓ + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hK := sum_rpow_mul_sq_log_le hp (le_one_of_sum_eq_one hp hsum) (1 - s) hθ0
  rw [show 2 * θ = 1 / (ℓ + 1) by rw [hθ]; field_simp] at hK
  refine hK.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hθe : (θ * Real.exp 1) ^ 2 * (4 * (ℓ + 1) ^ 2) = Real.exp 1 ^ 2 := by
    rw [hθ]; field_simp; norm_num
  have hnum := four_mul_exp_mul_sq_le hℓ
  have he := Real.exp_pos 1
  nlinarith [mul_le_mul_of_nonneg_right (sum_rpow_one_sub_sub_le hp hsum hs hℓ hsℓ) he.le,
    Real.exp_pos (1 / 10)]

/-- **One-site moment bound.**  A probability vector `p` on `d ≥ 2` points has
`∑ p^(1-s) ≤ exp(s H(p) + 5 s² log² d)` for `0 ≤ s` with `s log d ≤ 1/10`.  The constant `5`
uses `d ≥ 2`, which bounds `(log d + 1) / log d`. -/
theorem sum_rpow_one_sub_le_exp (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {s : ℝ} (hs : 0 ≤ s)
    (hℓ : Real.log 2 ≤ Real.log (Fintype.card ι))
    (hsℓ : s * Real.log (Fintype.card ι) ≤ 1 / 10) :
    ∑ i, p i ^ (1 - s) ≤
      Real.exp (s * H p + 5 * s ^ 2 * Real.log (Fintype.card ι) ^ 2) := by
  have hs1 : s < 1 := by
    nlinarith [Real.log_two_gt_d9, mul_le_mul_of_nonneg_left hℓ hs]
  have hK := sum_rpow_one_sub_mul_sq_log_le hp hsum hs hℓ hsℓ
  refine (sum_rpow_one_sub_le_one_add hp hsum hs hs1).trans
    ((?_ : _ ≤ s * H p + 5 * s ^ 2 * Real.log (Fintype.card ι) ^ 2 + 1).trans
      (Real.add_one_le_exp _))
  nlinarith [sq_nonneg s]

end Moment

/-! ### The Chernoff bound on a product distribution -/

section Chernoff

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ]

/-- At most `eᶜ` points of a product distribution have weight at least `e^(-c)`. -/
theorem card_filter_le_exp (f : κ → ι → ℝ) (hf : ∀ k i, 0 ≤ f k i)
    (hsum : ∀ k, ∑ i, f k i = 1) (c : ℝ) :
    ((Finset.univ.filter fun x : κ → ι => Real.exp (-c) ≤ ∏ k, f k (x k)).card : ℝ) ≤
      Real.exp c := by
  set S := Finset.univ.filter fun x : κ → ι => Real.exp (-c) ≤ ∏ k, f k (x k)
  have h : (S.card : ℝ) * Real.exp (-c) ≤ 1 := by
    calc (S.card : ℝ) * Real.exp (-c) = ∑ _x ∈ S, Real.exp (-c) := by simp
      _ ≤ ∑ x ∈ S, ∏ k, f k (x k) := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : κ → ι, ∏ k, f k (x k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            fun x _ _ => Finset.prod_nonneg fun k _ => hf k (x k)
      _ = 1 := by rw [← Fintype.prod_sum]; simp [hsum]
  rwa [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos c)] at h

/-- **Chernoff bound.**  For `n` probability vectors `fₖ` on `d ≥ 2` points and `0 ≤ s` with
`s log d ≤ 1/10`, the points of the product distribution with weight below `e^(-c)` carry
total weight at most `exp(s ∑ₖ H(fₖ) + n · 5 s² log² d - s c)`, by Markov's inequality on
`λ^(-s)` and the one-site moment bound. -/
theorem sum_filter_lt_le_exp (f : κ → ι → ℝ) (hf : ∀ k i, 0 ≤ f k i)
    (hsum : ∀ k, ∑ i, f k i = 1) (hℓ : Real.log 2 ≤ Real.log (Fintype.card ι)) {s : ℝ}
    (hs : 0 ≤ s) (hsℓ : s * Real.log (Fintype.card ι) ≤ 1 / 10) (c : ℝ) :
    ∑ x ∈ Finset.univ.filter (fun x : κ → ι => ∏ k, f k (x k) < Real.exp (-c)),
        ∏ k, f k (x k) ≤
      Real.exp (s * ∑ k, H (f k) + Fintype.card κ * (5 * s ^ 2 * Real.log (Fintype.card ι) ^ 2)
        - s * c) := by
  have hprod (x : κ → ι) : 0 ≤ ∏ k, f k (x k) := Finset.prod_nonneg fun k _ => hf k (x k)
  -- Markov: below the threshold, `λ ≤ e^(-sc) λ^(1-s)`.
  have hpt (x : κ → ι) (hx : ∏ k, f k (x k) < Real.exp (-c)) :
      ∏ k, f k (x k) ≤ Real.exp (-(s * c)) * (∏ k, f k (x k)) ^ (1 - s) := by
    rcases (hprod x).eq_or_lt with h | h
    · rw [← h]; positivity
    · calc ∏ k, f k (x k) = (∏ k, f k (x k)) ^ s * (∏ k, f k (x k)) ^ (1 - s) := by
            rw [← Real.rpow_add h]; simp
        _ ≤ Real.exp (-c) ^ s * (∏ k, f k (x k)) ^ (1 - s) := by gcongr
        _ = _ := by rw [← Real.exp_mul]; ring_nf
  calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : κ → ι => ∏ k, f k (x k) < Real.exp (-c)),
          Real.exp (-(s * c)) * (∏ k, f k (x k)) ^ (1 - s) :=
        Finset.sum_le_sum fun x hx => hpt x (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x : κ → ι, Real.exp (-(s * c)) * (∏ k, f k (x k)) ^ (1 - s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun x _ _ => by have := hprod x; positivity
    _ = Real.exp (-(s * c)) * ∏ k, ∑ i, f k i ^ (1 - s) := by
        rw [← Finset.mul_sum, Fintype.prod_sum]
        exact congrArg _ (Finset.sum_congr rfl fun x _ =>
          (Real.finsetProd_rpow _ _ (fun k _ => hf k (x k)) _).symm)
    _ ≤ Real.exp (-(s * c)) *
          ∏ k, Real.exp (s * H (f k) + 5 * s ^ 2 * Real.log (Fintype.card ι) ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_prod
          (fun k _ => Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf k i) _)
          fun k _ => sum_rpow_one_sub_le_exp (hf k) (hsum k) hs hℓ hsℓ) (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_sum, ← Real.exp_add, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring_nf

end Chernoff

/-! ### Logarithmic bookkeeping -/

section Logarithm

/-- `log k ≤ r` in `EReal` from `k ≤ eʳ`, including `log 0 = ⊥`. -/
theorem ennrealLog_natCast_le_of_le_exp {k : ℕ} {r : ℝ} (h : (k : ℝ) ≤ Real.exp r) :
    ENNReal.log (k : ENNReal) ≤ (r : EReal) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [show (k : ENNReal) = ENNReal.ofReal (k : ℝ) by simp,
      ENNReal.log_ofReal_of_pos (by exact_mod_cast hk), EReal.coe_le_coe_iff]
    exact (Real.log_le_iff_le_exp (by exact_mod_cast hk)).mpr h

/-- `dⁿ ≤ e^(n log d)`, with equality unless `d = 0 < n`. -/
theorem natCast_pow_le_exp_mul_log (d n : ℕ) :
    ((d ^ n : ℕ) : ℝ) ≤ Real.exp (n * Real.log d) := by
  push_cast
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Nat.cast_zero, Real.log_zero, mul_zero, Real.exp_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hd)]

theorem logb_two_div_sq_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 < Real.logb 2 (2 / ε ^ 2) :=
  Real.logb_pos one_lt_two (by rw [lt_div_iff₀ (by positivity), one_mul]; nlinarith)

/-- `e^(-(4/5) Λ) ≤ ε²/2` for `Λ = log₂(2/ε²)`, since `4/5 > log 2`. -/
theorem exp_neg_mul_logb_two_div_sq_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Real.exp (-(4 / 5 * Real.logb 2 (2 / ε ^ 2))) ≤ ε ^ 2 / 2 := by
  have hΛ := logb_two_div_sq_pos hε hε1
  have hl2 := Real.log_two_lt_d9
  have h2Λ : Real.exp (Real.logb 2 (2 / ε ^ 2) * Real.log 2) = 2 / ε ^ 2 := by
    rw [mul_comm, ← Real.rpow_def_of_pos two_pos, Real.rpow_logb two_pos (by norm_num)
      (by positivity)]
  calc Real.exp (-(4 / 5 * Real.logb 2 (2 / ε ^ 2)))
      ≤ Real.exp (-(Real.logb 2 (2 / ε ^ 2) * Real.log 2)) :=
        Real.exp_le_exp.mpr (by nlinarith)
    _ = ε ^ 2 / 2 := by rw [Real.exp_neg, h2Λ]; field_simp

end Logarithm

/-! ### The quantum equipartition property -/

section Equipartition

/-- **The equipartition bound for few or trivial sites.**  For a state on `(𝕜^d)^⊗n` with
`n ≤ 16 log₂(2/ε²)` or `d ≤ 1`, the dimension bound `H_max^ε ≤ n log d` already lies below
`H + 4 log d · √(n log₂(2/ε²))`. -/
theorem MState.smoothMaxEntropy_le_of_le_or_le_one {n d : ℕ} (ρ : MState (Fin n → Fin d) 𝕜)
    {ε : ℝ} (hε : 0 ≤ ε) (h : (n : ℝ) ≤ 16 * Real.logb 2 (2 / ε ^ 2) ∨ d ≤ 1) :
    ρ.smoothMaxEntropy ε ≤
      ((ρ.entropy + 4 * Real.log d * √(n * Real.logb 2 (2 / ε ^ 2)) : ℝ) : EReal) := by
  set Λ := Real.logb 2 (2 / ε ^ 2)
  have hH0 : 0 ≤ ρ.entropy := ρ.toSubState.entropy_nonneg
  refine (ρ.toSubState.smoothMaxEntropy_le_log_card hε).trans
    (ennrealLog_natCast_le_of_le_exp ?_)
  simp only [Fintype.card_fun, Fintype.card_fin]
  refine (natCast_pow_le_exp_mul_log d n).trans (Real.exp_le_exp.mpr ?_)
  rcases h with h | h
  · -- `n² ≤ 16 nΛ`, so `n ≤ 4√(nΛ)`.
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsq := Real.sq_sqrt (mul_nonneg hn0 (by linarith : 0 ≤ Λ))
    have : (n : ℝ) ≤ 4 * √(n * Λ) := by nlinarith [Real.sqrt_nonneg (n * Λ)]
    nlinarith [Real.log_natCast_nonneg d]
  · interval_cases d <;> simp [hH0]

/-- **Smoothing a product state by a threshold.**  If the eigenvalues `∏ₖ pₖ(xₖ)` of
`π₁ ⊗ ⋯ ⊗ πₙ` below `e^(-c)` carry weight at most `ε²/2`, then `H_max^ε ≤ c`. -/
theorem smoothMaxEntropy_piProd_le_of_sum_filter_lt_le {κ ι : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype ι] [DecidableEq ι] (π : κ → MState ι 𝕜) {ε : ℝ} (hε : 0 ≤ ε)
    (c : ℝ) (hw : ∑ x ∈ Finset.univ.filter (fun x : κ → ι =>
        ∏ k, (π k).psd.isHermitian.eigenvalues (x k) < Real.exp (-c)),
        ∏ k, (π k).psd.isHermitian.eigenvalues (x k) ≤ ε ^ 2 / 2) :
    (MState.piProd π).smoothMaxEntropy ε ≤ (c : EReal) := by
  set eig := fun k => (π k).psd.isHermitian.eigenvalues
  set lam := fun x : κ → ι => ∏ k, eig k (x k)
  obtain ⟨V, -, hV, hdiag⟩ := MState.exists_piProd_M_eq_mul_diagonal_mul π
  have heig0 k i : 0 ≤ eig k i := (π k).psd.eigenvalues_nonneg i
  have heig1 k : ∑ i, eig k i = 1 := (π k).sum_eigenvalues_eq_one
  have hlam x : 0 ≤ lam x := Finset.prod_nonneg fun k _ => heig0 k (x k)
  set w := ∑ x ∈ Finset.univ.filter (fun x : κ → ι => lam x < Real.exp (-c)), lam x
  have hw0 : 0 ≤ w := Finset.sum_nonneg fun x _ => hlam x
  set S := Finset.univ.filter fun x : κ → ι => Real.exp (-c) ≤ lam x
  have hSw : ∑ x ∈ S, lam x = 1 - w := by
    have h1 : ∑ x, lam x = 1 := by
      simp only [lam, ← Fintype.prod_sum, heig1, Finset.prod_const_one]
    rw [← h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : κ → ι => Real.exp (-c) ≤ lam x)]
    simp only [not_le, S, w]
    ring
  -- The kept weight is `1 - w ≥ 1 - ε²/2`, so `1 - (1 - w)² ≤ 2w ≤ ε²`.
  refine ((MState.piProd π).smoothMaxEntropy_le_log_card_of_eq_mul_diagonal_mul hV hlam hdiag S
    hε (by rw [hSw]; nlinarith)).trans (ennrealLog_natCast_le_of_le_exp ?_)
  exact card_filter_le_exp eig heig0 heig1 c

/-- **The equipartition bound by a Chernoff bound.**  For `ε < 1`, `n > 16Λ` with
`Λ = log₂(2/ε²)`, and `d ≥ 2`, the threshold `c = H + 4 log d · √(nΛ)` and Chernoff exponent
`s = 2√(nΛ) / (5n log d)` make the discarded weight `e^(-(4/5)Λ) ≤ ε²/2`. -/
theorem smoothMaxEntropy_piProd_le_of_lt_one_of_lt_of_two_le {n d : ℕ}
    (π : Fin n → MState (Fin d) 𝕜) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hn : 16 * Real.logb 2 (2 / ε ^ 2) < n) (hd : 2 ≤ d) :
    (MState.piProd π).smoothMaxEntropy ε ≤
      (((MState.piProd π).entropy + 4 * Real.log d * √(n * Real.logb 2 (2 / ε ^ 2)) : ℝ) :
        EReal) := by
  set Λ := Real.logb 2 (2 / ε ^ 2)
  set ℓ := Real.log d
  have hΛ : 0 < Λ := logb_two_div_sq_pos hε hε1
  have hn0 : (0 : ℝ) < n := by linarith
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log two_pos (by exact_mod_cast hd)
  have hℓpos : 0 < ℓ := (Real.log_pos one_lt_two).trans_le hℓ2
  set u := √(n * Λ)
  have hu : u ^ 2 = n * Λ := Real.sq_sqrt (by positivity)
  have h4u : 4 * u ≤ n := by nlinarith [Real.sqrt_nonneg (n * Λ)]
  set c := (MState.piProd π).entropy + 4 * ℓ * u
  set s := 2 / 5 * u / (n * ℓ)
  have hsℓ : s * Real.log (Fintype.card (Fin d)) ≤ 1 / 10 := by
    rw [Fintype.card_fin, show s * ℓ = 2 / 5 * u / n by simp only [s]; field_simp,
      div_le_iff₀ hn0]
    linarith
  have htail := sum_filter_lt_le_exp _ (fun k i => (π k).psd.eigenvalues_nonneg i)
    (fun k => (π k).sum_eigenvalues_eq_one) (by rwa [Fintype.card_fin]) (by positivity) hsℓ c
  rw [Fintype.card_fin, Fintype.card_fin] at htail
  simp only [← SubState.entropy_eq_H, ← MState.entropy_piProd] at htail
  -- The Chernoff exponent is `-(4/5) Λ`.
  have hexp : s * (MState.piProd π).entropy + n * (5 * s ^ 2 * ℓ ^ 2) - s * c = -(4 / 5 * Λ) := by
    simp only [c, s]
    field_simp
    linear_combination (-4 * ℓ) * hu
  exact smoothMaxEntropy_piProd_le_of_sum_filter_lt_le π hε.le c
    ((htail.trans_eq (by rw [hexp])).trans (exp_neg_mul_logb_two_div_sq_le hε hε1))

/-- **Quantum Equipartition Property** in nats, before dividing by `n`: for states
`π₁, …, πₙ` on `𝕜^d`, `H_max^ε(π₁ ⊗ ⋯ ⊗ πₙ) ≤ H(π₁ ⊗ ⋯ ⊗ πₙ) + 4 log d · √(n log₂(2/ε²))`.
`0 < ε` is necessary, as for `smoothMaxEntropy₂_piProd_le`. -/
theorem smoothMaxEntropy_piProd_le {n d : ℕ} (π : Fin n → MState (Fin d) 𝕜)
    {ε : ℝ} (hε : 0 < ε) :
    (MState.piProd π).smoothMaxEntropy ε ≤
      (((MState.piProd π).entropy + 4 * Real.log d * √(n * Real.logb 2 (2 / ε ^ 2)) : ℝ) :
        EReal) := by
  rcases le_or_gt 1 ε with hε1 | hε1
  · exact ((MState.piProd π).smoothMaxEntropy_eq_bot_of_one_le hε1).trans_le bot_le
  by_cases h : (n : ℝ) ≤ 16 * Real.logb 2 (2 / ε ^ 2) ∨ d ≤ 1
  · exact (MState.piProd π).smoothMaxEntropy_le_of_le_or_le_one hε.le h
  simp only [not_or, not_le] at h
  exact smoothMaxEntropy_piProd_le_of_lt_one_of_lt_of_two_le π hε hε1 h.1 h.2

/-- **Quantum Equipartition Property** (BH12, \label{QEP}).  For states `π₁, …, πₙ` on `𝕜^d`,
`(1/n) H_max^ε(π₁ ⊗ ⋯ ⊗ πₙ) ≤ (1/n) H(π₁ ⊗ ⋯ ⊗ πₙ) + 4 log₂ d · √(log₂(2/ε²) / n)`.
`0 < ε` is necessary: at `ε = 0` Lean's `2 / 0 = 0` makes the error term vanish, and `n = 1`,
`π₁ = diag(3/4, 1/4)` has `H_max = 1 > H`. -/
theorem smoothMaxEntropy₂_piProd_le {n d : ℕ} (π : Fin n → MState (Fin d) 𝕜)
    {ε : ℝ} (hε : 0 < ε) :
    (MState.piProd π).smoothMaxEntropy₂ ε / n ≤
      ((MState.piProd π).entropy₂ / n +
        4 * Real.logb 2 d * √(Real.logb 2 (2 / ε ^ 2) / n) : ℝ) := by
  set Λ := Real.logb 2 (2 / ε ^ 2)
  set ℓ := Real.log d
  set ρ := MState.piProd π
  have key : ρ.toSubState.smoothMaxEntropy ε ≤ ((ρ.entropy + 4 * ℓ * √(n * Λ) : ℝ) : EReal) :=
    smoothMaxEntropy_piProd_le π hε
  -- Convert to bits, then divide by `n`.
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key₂ : ρ.toSubState.smoothMaxEntropy₂ ε ≤
      (((ρ.entropy + 4 * ℓ * √(n * Λ)) / Real.log 2 : ℝ) : EReal) := by
    rw [SubState.smoothMaxEntropy₂, EReal.coe_div]
    exact EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hl2.le) key
  refine (EReal.div_le_div_right_of_nonneg (by positivity) key₂).trans_eq ?_
  rw [← EReal.coe_natCast, ← EReal.coe_div, SubState.entropy₂, Real.logb]
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : √(n * Λ) = n * √(Λ / n) := by
    rw [show (n : ℝ) * Λ = n ^ 2 * (Λ / n) by field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hn'.le]
  rw [hsq]
  field_simp
  ring

end Equipartition

end Arealaw
