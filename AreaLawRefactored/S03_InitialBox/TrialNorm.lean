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

/-- D3.13 (eq:initial-norm-upper). For `X ⊆ U` and `T_0 ⊆ T_1 ⊆ ⋯ ⊆ U` disjoint from `X`,
weights `a_j > 0` and a unit vector `Ω`: if every product of zero-floor filters `L_j` on
`X ∪ T_j` has `‖L_{m-1} ⋯ L_0 Ω‖ ≤ B`, `B > 0`, then `-2 log B ≤ S(X) + ∑_j a_j S(T_j)`. -/
theorem eq_initial_norm_upper {X : Finset σ} (hXU : X ⊆ U) (T : ℕ → Finset σ)
    (hTU : ∀ j, T j ⊆ U) (hT : ∀ j, T j ⊆ T (j + 1)) (hXT : ∀ j, Disjoint X (T j))
    {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (m : ℕ) (Ω : Reg loc U → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ L : (j : ℕ) → Matrix (Reg loc (X ∪ T j)) (Reg loc (X ∪ T j)) ℂ,
      (∀ j, IsFilter 0 (a j) (L j)) →
      ‖toEuclideanLin (filterProd (fun j ↦ Finset.union_subset hXU (hTU j)) L m)
        (WithLp.toLp 2 Ω)‖ ≤ B) :
    -2 * Real.log B ≤ (OpenAI.pureState Ω hΩ).regionEntropy hXU +
      ∑ j ∈ Finset.range m, a j * (OpenAI.pureState Ω hΩ).regionEntropy (hTU j) := by
  set ρ := (OpenAI.pureState Ω hΩ).toSubState.restrict hXU
  set W : Matrix (Reg loc X) (Reg loc X) ℂ := ↑ρ.psd.isHermitian.eigenvectorUnitary
  set p := ρ.psd.isHermitian.eigenvalues
  have hW : Wᴴ * W = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hW' : W * Wᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  have hρeq : ptrace hXU (vecMulVec (WithLp.ofLp (WithLp.toLp 2 Ω : EuclideanSpace ℂ _))
      (star (WithLp.ofLp (WithLp.toLp 2 Ω : EuclideanSpace ℂ _)))) =
      W * diagonal (fun x ↦ (p x : ℂ)) * Wᴴ :=
    IsHermitian.eq_eigenvectorUnitary_mul ρ.psd.isHermitian
  have hp : ∀ i, 0 ≤ p i := ρ.psd.eigenvalues_nonneg
  have hps : ∑ i, p i = 1 := ((OpenAI.pureState Ω hΩ).restrict hXU).sum_eigenvalues_eq_one
  -- D3.12.2: the pinned vectors `φ_i = (|u_i⟩⟨u_i| ⊗ 1) Ω = √p_i u_i ⊗ w_i`, `‖φ_i‖² = p_i`
  set φ : Reg loc X → EuclideanSpace ℂ (Reg loc U) :=
    fun i ↦ toEuclideanLin (extendId hXU (pinProj W i)) (WithLp.toLp 2 Ω)
  have hφp : ∀ i, ‖φ i‖ ^ 2 = p i := step_3_12_2_norm hXU hW hρeq
  have hp0 : ∀ i, φ i = 0 → p i = 0 := fun i h ↦ by rw [← hφp, h, norm_zero]; ring
  -- the unit vectors `ξ_i = φ_i/‖φ_i‖` (any unit vector where `p_i = 0`)
  set ξ : Reg loc X → Reg loc U → ℂ :=
    fun i ↦ if φ i = 0 then Ω else ((‖φ i‖⁻¹ : ℝ) : ℂ) • WithLp.ofLp (φ i)
  have hξφ : ∀ i, φ i ≠ 0 → WithLp.ofLp (φ i) = ((‖φ i‖ : ℝ) : ℂ) • ξ i := fun i h ↦ by
    simp only [ξ, if_neg h, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 h), Complex.ofReal_one, one_smul]
  have hξ : ∀ i, star (ξ i) ⬝ᵥ ξ i = 1 := fun i ↦ by
    by_cases h : φ i = 0
    · simp only [ξ, if_pos h]; exact hΩ
    · have h1 : star (WithLp.ofLp (φ i)) ⬝ᵥ WithLp.ofLp (φ i) = ((‖φ i‖ ^ 2 : ℝ) : ℂ) := by
        rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
          inner_self_eq_norm_sq_to_K]
        push_cast; rfl
      have hn : ‖φ i‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [ξ, if_neg h, star_smul, smul_dotProduct, dotProduct_smul, h1, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      field_simp
  -- D3.12(b), (c) for each Schmidt index: `-2 log B ≤ -log p_i + ∑_j a_j S_{w_i}(T_j)`
  have hone : ∀ i, p i * -(∑ j ∈ Finset.range m,
      a j / 2 * (OpenAI.pureState (ξ i) (hξ i)).regionEntropy (hTU j)) ≤
      p i * Real.log B + Real.negMulLog (p i) / 2 := by
    intro i
    by_cases h0 : φ i = 0
    · simp [hp0 i h0]
    have hpos : 0 < ‖φ i‖ := norm_pos_iff.2 h0
    have hBi : ∀ M : (j : ℕ) → Matrix (Reg loc (T j)) (Reg loc (T j)) ℂ,
        (∀ j, IsFilter 0 (a j) (M j)) →
        ‖toEuclideanLin (filterProd hTU M m) (WithLp.toLp 2 (ξ i))‖ ≤ B / ‖φ i‖ := by
      intro M hM
      obtain ⟨L, hL, hle⟩ := step_3_12_2 hXU hTU hXT ha hW i hM (WithLp.toLp 2 Ω) m
      have h1 := hle.trans (hB L hL)
      have hφ' : φ i = ((‖φ i‖ : ℝ) : ℂ) • WithLp.toLp 2 (ξ i) := by
        conv_lhs => rw [show φ i = WithLp.toLp 2 (WithLp.ofLp (φ i)) from rfl, hξφ i h0,
          WithLp.toLp_smul]
      change ‖toEuclideanLin (filterProd hTU M m) (φ i)‖ ≤ B at h1
      rw [hφ', map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm] at h1
      rw [le_div_iff₀ hpos, mul_comm]
      exact h1
    have hlog := eq_initial_trial_norm T hTU hT (hξ i) ha m (div_pos hB0 hpos) hBi
    rw [Real.log_div hB0.ne' hpos.ne'] at hlog
    have hη : Real.negMulLog (p i) / 2 = -(p i * Real.log ‖φ i‖) := by
      rw [← hφp, Real.negMulLog, Real.log_pow]; push_cast; ring
    rw [hη]
    have := mul_le_mul_of_nonneg_left hlog (hp i)
    linarith
  -- D3.13.2: `ρ_{Ω,T_j} = ∑_i p_i ρ_{w_i,T_j}` and concavity
  have hconc : ∀ j, ∑ i, p i * (OpenAI.pureState (ξ i) (hξ i)).regionEntropy (hTU j) ≤
      (OpenAI.pureState Ω hΩ).regionEntropy (hTU j) := by
    intro j
    refine MState.sum_mul_entropy_le_entropy hp hps
      (fun i ↦ (OpenAI.pureState (ξ i) (hξ i)).restrict (hTU j))
      ((OpenAI.pureState Ω hΩ).restrict (hTU j)) ?_
    have hm := step_3_13_2_marginal hXU (hTU j) (hXT j) hW hW' (WithLp.toLp 2 Ω)
    rw [WithLp.ofLp_toLp] at hm
    change ptrace (hTU j) (vecMulVec Ω (star Ω)) =
      ∑ i, (p i : ℂ) • ptrace (hTU j) (vecMulVec (ξ i) (star (ξ i)))
    rw [← hm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ptrace (hTU j) (vecMulVec (WithLp.ofLp (φ i)) (star (WithLp.ofLp (φ i)))) = _
    by_cases h0 : φ i = 0
    · rw [h0, hp0 i h0]
      simp only [WithLp.ofLp_zero, star_zero, vecMulVec_zero, ptrace_zero, Complex.ofReal_zero,
        zero_smul]
    · rw [hξφ i h0, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, ptrace_smul, ← hφp i,
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring_nf
  -- D3.13.2: average over `i` with weights `p_i`
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hone i
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, hps, one_mul] at hsum
  have hSX : (OpenAI.pureState Ω hΩ).regionEntropy hXU = ∑ i, Real.negMulLog (p i) :=
    ρ.entropy_eq_H
  rw [← hSX] at hsum
  have hswap : ∑ i, p i * -(∑ j ∈ Finset.range m,
      a j / 2 * (OpenAI.pureState (ξ i) (hξ i)).regionEntropy (hTU j)) =
      -∑ j ∈ Finset.range m, a j / 2 *
        ∑ i, p i * (OpenAI.pureState (ξ i) (hξ i)).regionEntropy (hTU j) := by
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring)
  rw [hswap] at hsum
  have hconc' : ∑ j ∈ Finset.range m, a j / 2 *
      ∑ i, p i * (OpenAI.pureState (ξ i) (hξ i)).regionEntropy (hTU j) ≤
      ∑ j ∈ Finset.range m, a j / 2 * (OpenAI.pureState Ω hΩ).regionEntropy (hTU j) :=
    Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hconc j) (by linarith [ha j])
  have h2 : ∑ j ∈ Finset.range m, a j * (OpenAI.pureState Ω hΩ).regionEntropy (hTU j) =
      2 * ∑ j ∈ Finset.range m, a j / 2 * (OpenAI.pureState Ω hΩ).regionEntropy (hTU j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h2]
  linarith

end AreaLaw
