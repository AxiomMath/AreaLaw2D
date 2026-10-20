import AreaLawRefactored.S03_InitialBox.ThreeLines
import AreaLawRefactored.S03_InitialBox.ZeroFloorPinning
import AreaLawForMathlib.QuantumInfo.Entropy.Concavity

/-!
# §3.2, D3.12.6, D3.12(c) and D3.13 of digest/03-initial-box.md: the trial-norm bound

Over an arbitrary site type: the trial filters of D3.12.6, the bound eq:initial-trial-norm
(D3.12(c)) and the Schmidt-averaged upper bound eq:initial-norm-upper (D3.13).
-/

namespace AreaLaw

open Matrix Arealaw Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ}

/-- The spectral decomposition `A = W diag(λ) Wᴴ` of a Hermitian matrix. -/
theorem IsHermitian.eq_eigenvectorUnitary_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i ↦ (hA.eigenvalues i : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]

/-- D3.12.6. Trial filters. For a unit vector `ξ`, `T ⊆ U`, `a > 0` and `0 < δ < 1`, the filter
`M = ((1 - δ) ρ_{ξ,T} + δ/dim)^{a/2}` is strictly positive, of zero floor, and
`Re ⟨ξ, log M ξ⟩ ≥ (a/2) (log (1 - δ) - S_ξ(T))`. -/
theorem step_3_12_6 {T : Finset σ} (hT : T ⊆ U) {ξ : Reg loc U → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1)
    {a : ℝ} (ha : 0 < a) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (W : Matrix (Reg loc T) (Reg loc T) ℂ) (l : Reg loc T → ℝ), Wᴴ * W = 1 ∧
      (∀ x, 0 < l x) ∧ IsFilter 0 a (W * diagonal (fun x ↦ (l x : ℂ)) * Wᴴ) ∧
      a / 2 * (Real.log (1 - δ) - (OpenAI.pureState ξ hξ).regionEntropy hT) ≤
        (⟪WithLp.toLp 2 ξ, toEuclideanLin (extendId hT
          (W * diagonal (fun x ↦ (Real.log (l x) : ℂ)) * Wᴴ)) (WithLp.toLp 2 ξ)⟫_ℂ).re := by
  set ρ := (OpenAI.pureState ξ hξ).toSubState.restrict hT
  set W : Matrix (Reg loc T) (Reg loc T) ℂ := ↑ρ.psd.isHermitian.eigenvectorUnitary
  set p := ρ.psd.isHermitian.eigenvalues
  have hW : Wᴴ * W = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hρeq : ρ.M = W * diagonal (fun x ↦ (p x : ℂ)) * Wᴴ :=
    IsHermitian.eq_eigenvectorUnitary_mul ρ.psd.isHermitian
  have hp : ∀ x, 0 ≤ p x := ρ.psd.eigenvalues_nonneg
  have hps : ∑ x, p x = 1 := ((OpenAI.pureState ξ hξ).restrict hT).sum_eigenvalues_eq_one
  have hne : Nonempty (Reg loc T) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hps
  have hd : (0 : ℝ) < Fintype.card (Reg loc T) := by exact_mod_cast Fintype.card_pos
  set y : Reg loc T → ℝ := fun x ↦ (1 - δ) * p x + δ / Fintype.card (Reg loc T)
  have hy : ∀ x, 0 < y x := fun x ↦ by
    have : 0 ≤ (1 - δ) * p x := mul_nonneg (by linarith) (hp x)
    have : 0 < δ / Fintype.card (Reg loc T) := div_pos hδ0 hd
    simp only [y]; linarith
  refine ⟨W, fun x ↦ y x ^ (a / 2), hW, fun x ↦ Real.rpow_pos_of_pos (hy x) _, ?_, ?_⟩
  · obtain ⟨V, hV, x, hx, hs, h⟩ := isFilter_floorRaise (a := a) hδ1.le hW hp hps
    exact ⟨V, hV, x, fun i ↦ (div_nonneg hδ0.le hd.le).trans (hx i), hs, h⟩
  -- D3.12.6: `⟨ξ, log M ξ⟩ = (a/2) ∑_k p_k log ((1 - δ) p_k + δ/dim)`
  have hS : (OpenAI.pureState ξ hξ).regionEntropy hT = ∑ x, Real.negMulLog (p x) :=
    ρ.entropy_eq_H
  rw [hS, inner_extendId, WithLp.ofLp_toLp,
    show ptrace hT (vecMulVec ξ (star ξ)) = ρ.M from rfl, hρeq]
  have htr : (W * diagonal (fun x ↦ (p x : ℂ)) * Wᴴ *
      (W * diagonal (fun x ↦ (Real.log (y x ^ (a / 2)) : ℂ)) * Wᴴ)).trace =
      ∑ x, ((p x * (a / 2 * Real.log (y x)) : ℝ) : ℂ) := by
    calc _ = (W * (diagonal (fun x ↦ (p x : ℂ)) * (Wᴴ * W) *
          diagonal (fun x ↦ (Real.log (y x ^ (a / 2)) : ℂ))) * Wᴴ).trace := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hW, Matrix.mul_one, trace_mul_cycle, hW, Matrix.one_mul, diagonal_mul_diagonal,
            trace_diagonal]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [Real.log_rpow (hy x)]
          push_cast
          ring
  rw [htr, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hrhs : a / 2 * (Real.log (1 - δ) - ∑ x, Real.negMulLog (p x)) =
      ∑ x, a / 2 * (p x * Real.log (1 - δ) - Real.negMulLog (p x)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, hps, one_mul]
  rw [hrhs]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  rcases (hp x).lt_or_eq with hpx | hpx
  · have hy' : (1 - δ) * p x ≤ y x := by simp only [y]; linarith [div_pos hδ0 hd]
    have hlog : Real.log ((1 - δ) * p x) ≤ Real.log (y x) :=
      Real.log_le_log (mul_pos (by linarith) hpx) hy'
    rw [Real.log_mul (by linarith) hpx.ne'] at hlog
    rw [Real.negMulLog]
    have := mul_le_mul_of_nonneg_left hlog hpx.le
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ a / 2)]
  · rw [← hpx]
    simp

/-- D3.12(c) (eq:initial-trial-norm). For a unit vector `ξ` and `T_0 ⊆ T_1 ⊆ ⋯ ⊆ U`: if every
product of zero-floor filters `M_j` on `T_j` has `‖M_{m-1} ⋯ M_0 ξ‖ ≤ B`, `B > 0`, then
`-½ ∑_j a_j S_ξ(T_j) ≤ log B`. -/
theorem eq_initial_trial_norm (T : ℕ → Finset σ) (hTU : ∀ j, T j ⊆ U)
    (hT : ∀ j, T j ⊆ T (j + 1)) {ξ : Reg loc U → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) {a : ℕ → ℝ}
    (ha : ∀ j, 0 < a j) (m : ℕ) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ M : (j : ℕ) → Matrix (Reg loc (T j)) (Reg loc (T j)) ℂ,
      (∀ j, IsFilter 0 (a j) (M j)) → ‖toEuclideanLin (filterProd hTU M m) (WithLp.toLp 2 ξ)‖ ≤ B) :
    -(∑ j ∈ Finset.range m, a j / 2 * (OpenAI.pureState ξ hξ).regionEntropy (hTU j)) ≤
      Real.log B := by
  set s := ∑ j ∈ Finset.range m, a j / 2 * (OpenAI.pureState ξ hξ).regionEntropy (hTU j)
  have hξ1 : ‖(WithLp.toLp 2 ξ : EuclideanSpace ℂ (Reg loc U))‖ = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 ξ : EuclideanSpace ℂ (Reg loc U))
    rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct_comm, hξ] at h
    have h' : ‖(WithLp.toLp 2 ξ : EuclideanSpace ℂ (Reg loc U))‖ ^ 2 = 1 :=
      Complex.ofReal_eq_one.1 (by push_cast; exact h.symm)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'
  -- D3.12.5 with the trial filters of D3.12.6, for every `δ ∈ (0, 1)`
  have hδ : ∀ δ, 0 < δ → δ < 1 →
      (∑ j ∈ Finset.range m, a j / 2) * Real.log (1 - δ) - s ≤ Real.log B := by
    intro δ hδ0 hδ1
    choose W l hW hl hM hlow using fun j ↦ step_3_12_6 (hTU j) hξ (ha j) hδ0 hδ1
    calc (∑ j ∈ Finset.range m, a j / 2) * Real.log (1 - δ) - s
        = ∑ j ∈ Finset.range m, a j / 2 *
            (Real.log (1 - δ) - (OpenAI.pureState ξ hξ).regionEntropy (hTU j)) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hlow j
      _ ≤ Real.log B := step_3_12_5 hTU hT hW hl hM m hξ1 hB0 hB
  -- D3.12.6: `δ ↓ 0`
  have hlim : Tendsto (fun δ : ℝ ↦ (∑ j ∈ Finset.range m, a j / 2) * Real.log (1 - δ) - s)
      (𝓝[>] 0) (𝓝 (-s)) := by
    have hc : ContinuousAt (fun δ : ℝ ↦ (∑ j ∈ Finset.range m, a j / 2) * Real.log (1 - δ) - s)
        0 := ((continuousAt_const.mul ((Real.continuousAt_log (by norm_num)).comp
          (by fun_prop))).sub continuousAt_const)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ'
  exact hδ δ hδ'.1 hδ'.2

end AreaLaw
