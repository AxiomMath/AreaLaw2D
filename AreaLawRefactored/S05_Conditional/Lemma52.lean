import AreaLawRefactored.S05_Conditional.Spectral
import AreaLawRefactored.S05_Conditional.Interfaces
import AreaLawRefactored.S05_Conditional.Faithful52

/-!
# §5 D5.12.11: Lemma 5.2 from its faithful case

`lemma_5_2_of_faithful` derives **Lemma 5.2** (`Lemma_5_2`, vector form on a purification `θ`)
from its faithful Hilbert–Schmidt form `Lemma_5_2_faithful`: (F1) moves the vector norm to the
Hilbert–Schmidt norm against `√ρ_f`, `ρ_f = ρ_{xUF}`, and D5.12.11 regularises a singular `ρ_f`
by `ρ_{f,ε} = (1-ε) ρ_f + ε I / dim(xUF)` and passes to the limit `ε → 0⁺`.
-/

namespace AreaLaw

open Arealaw Matrix Filter Topology
open OpenAI (pureState)
open scoped ComplexOrder MatrixOrder

namespace Conditional

/-! ## Affine images `aρ + b` in the eigenbasis of `ρ` -/

section Affine

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `aρ + b I` for real `a, b`. -/
noncomputable def aff (a b : ℝ) (ρ : Matrix n n ℂ) : Matrix n n ℂ := (a : ℂ) • ρ + (b : ℂ) • 1

omit [Fintype n] in
theorem isHermitian_aff {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) (a b : ℝ) :
    (aff a b ρ).IsHermitian := by
  simp [aff, IsHermitian, conjTranspose_add, conjTranspose_smul, h.eq]

variable {ρ : Matrix n n ℂ} (h : ρ.IsHermitian)

theorem specFun_smul (c : ℂ) (g : ℝ → ℂ) : specFun h (c • g) = c • specFun h g := by
  simp only [specFun, Pi.smul_apply]
  rw [show (diagonal fun i ↦ c • g (h.eigenvalues i)) = c • diagonal fun i ↦ g (h.eigenvalues i)
    by rw [← diagonal_smul]; rfl, Matrix.mul_smul, Matrix.smul_mul]

theorem trace_specFun_sum (g : ℝ → ℂ) : (specFun h g).trace = ∑ i, g (h.eigenvalues i) := by
  rw [specFun, trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul,
    trace_diagonal]

/-- `(aρ + b)` in the eigenbasis of `ρ`. -/
theorem specFun_affine (a b : ℝ) : specFun h (fun t ↦ ((a * t + b : ℝ) : ℂ)) = aff a b ρ := by
  rw [show (fun t : ℝ ↦ ((a * t + b : ℝ) : ℂ)) = (a : ℂ) • (fun t : ℝ ↦ (t : ℂ)) + (b : ℂ) • 1
    by funext t; simp, ← specFun_add, specFun_smul, specFun_smul, specFun_ofReal, specFun_one, aff]

/-- A spectral function of `aρ + b` is a spectral function of `ρ`. -/
theorem specFun_aff {a b : ℝ} (hB : (aff a b ρ).IsHermitian) (g : ℝ → ℂ) :
    specFun hB g = specFun h (fun t ↦ g (a * t + b)) := by
  have := diagonal_intertwine (Unitary.coe_star_mul_self hB.eigenvectorUnitary)
    (Unitary.coe_mul_star_self _) (Unitary.coe_star_mul_self h.eigenvectorUnitary)
    (Unitary.coe_mul_star_self _) (b := fun j ↦ a * h.eigenvalues j + b) 1
    (by
      change specFun hB (fun t ↦ (t : ℂ)) * 1 = 1 * specFun h (fun t ↦ ((a * t + b : ℝ) : ℂ))
      rw [specFun_ofReal, specFun_affine, Matrix.mul_one, Matrix.one_mul]) g
  simp only [Matrix.mul_one, Matrix.one_mul] at this
  exact this

/-- `√ρ` in the eigenbasis of `ρ ≥ 0`. -/
theorem sqrt_eq_specFun (hρ : ρ.PosSemidef) :
    CFC.sqrt ρ = specFun hρ.isHermitian (fun t ↦ ((√t : ℝ) : ℂ)) := by
  rw [CFC.sqrt_eq_real_sqrt _ hρ.nonneg, cfcₙ_eq_cfc (hf0 := Real.sqrt_zero),
    specFun_ofReal_comp]

/-- `S(aρ + b) = ∑ η(a λ_k + b)`. -/
theorem vonNeumann_aff {a b : ℝ} {B : Matrix n n ℂ} (hB : B.IsHermitian) (hBa : B = aff a b ρ) :
    vonNeumann hB = ∑ k, Real.negMulLog (a * h.eigenvalues k + b) := by
  subst hBa
  rw [vonNeumann, ← hB.cfc_eq, ← specFun_ofReal_comp hB, specFun_aff h hB, trace_specFun_sum]
  simp only [Real.negMulLog, ← Complex.ofReal_sum, ← Complex.ofReal_neg, RCLike.re_to_complex,
    Complex.ofReal_re, ← Finset.sum_neg_distrib, neg_mul]

end Affine

/-! ## Limits of spectral functions -/

section Limits

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) {l : Filter ℝ}

theorem tendsto_specFun {g : ℝ → ℝ → ℂ} {g₀ : ℝ → ℂ}
    (hg : ∀ k, Tendsto (fun ε ↦ g ε (h.eigenvalues k)) l (𝓝 (g₀ (h.eigenvalues k)))) :
    Tendsto (fun ε ↦ specFun h (g ε)) l (𝓝 (specFun h g₀)) :=
  (tendsto_const_nhds.mul ((continuous_id.matrix_diagonal.tendsto _).comp
    (tendsto_pi_nhds.2 hg))).mul tendsto_const_nhds

omit [DecidableEq m] in
/-- D5.12.11, one phase. A family of spectral functions of `ρ` converging on `supp ρ`, of norm
one on `ker ρ`, converges after any linear lift `L` once multiplied by a convergent family whose
limit `L(Π_{ker ρ})` kills. -/
theorem tendsto_specFun_mul (hnn : ∀ k, 0 ≤ h.eigenvalues k)
    (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {g : ℝ → ℝ → ℂ} {g₀ : ℝ → ℂ}
    {Y : ℝ → Matrix m m ℂ} {Y₀ : Matrix m m ℂ}
    (hg : ∀ t, 0 < t → Tendsto (fun ε ↦ g ε t) l (𝓝 (g₀ t))) (hg0 : ∀ᶠ ε in l, ‖g ε 0‖ = 1)
    (hg₀ : g₀ 0 = 1) (hY : Tendsto Y l (𝓝 Y₀)) (hK : L (1 - bracketPow ρ 0) * Y₀ = 0) :
    Tendsto (fun ε ↦ L (specFun h (g ε)) * Y ε) l (𝓝 (L (specFun h g₀) * Y₀)) := by
  set K := 1 - bracketPow ρ 0
  have hKs : K = specFun h (fun t ↦ if 0 < t then 0 else 1) := by
    rw [show K = 1 - bracketPow ρ 0 from rfl, bracketPow_eq h, ← specFun_one h, specFun_sub]
    exact specFun_congr _ fun i ↦ by by_cases hi : 0 < h.eigenvalues i <;> simp [bfun, hi]
  have hdec (f : ℝ → ℂ) : specFun h f =
      specFun h (fun t ↦ if 0 < t then f t else 0) + f 0 • K := by
    rw [hKs, ← specFun_smul, specFun_add]
    refine specFun_congr _ fun i ↦ ?_
    rcases (hnn i).lt_or_eq with hi | hi
    · simp [hi]
    · simp [← hi]
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h1 := ((hLc.tendsto _).comp (tendsto_specFun h (g := fun ε t ↦ if 0 < t then g ε t else 0)
    (g₀ := fun t ↦ if 0 < t then g₀ t else 0) fun k ↦ by
      by_cases hk : 0 < h.eigenvalues k
      · simpa [hk] using hg _ hk
      · simpa [hk] using tendsto_const_nhds)).mul hY
  have h2 : Tendsto (fun ε ↦ g ε 0 • (L K * Y ε)) l (𝓝 0) := by
    have h3 : Tendsto (fun ε ↦ L K * Y ε) l (𝓝 0) := by
      simpa [hK] using (tendsto_const_nhds (x := L K)).mul hY
    refine tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ ?_
    have h4 := ((continuous_apply j).tendsto _).comp (((continuous_apply i).tendsto _).comp h3)
    simp only [Matrix.zero_apply, Function.comp_def] at h4 ⊢
    rw [tendsto_zero_iff_norm_tendsto_zero] at h4 ⊢
    refine h4.congr' ?_
    filter_upwards [hg0] with ε hε
    simp [hε]
    rfl
  rw [hdec g₀, hg₀, one_smul, map_add, Matrix.add_mul, hK, add_zero]
  refine (by simpa using h1.add h2 : Tendsto _ l _).congr fun ε ↦ ?_
  simp only [hdec (g ε), map_add, map_smul, Matrix.add_mul, Matrix.smul_mul]

/-- `𝓡_η` is continuous in `η` (`𝓡 = 0` for `η ≤ 0`, `𝓡_η → 0` as `η → 0⁺`). -/
theorem continuous_𝓡 {d : ℕ} (hd : 1 ≤ d) : Continuous (𝓡 d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine continuous_iff_continuousAt.2 fun η₀ ↦ ?_
  rcases lt_trichotomy η₀ 0 with hneg | rfl | hpos
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [gt_mem_nhds hneg] with η hη
    simp [𝓡, not_lt.2 hη.le]
  · -- squeeze: `𝓡_η ≤ √η⁺ + √(η⁺(1 + log d) + η⁺ log(1/η⁺))` for `η < 1`
    set g : ℝ → ℝ := fun x ↦ √(max x 0) + √(max x 0 * (1 + Real.log d) +
      Real.negMulLog (max x 0))
    have hg : Continuous g := by have := Real.continuous_negMulLog; fun_prop
    have hlim : Tendsto (fun η ↦ g η) (𝓝 0) (𝓝 0) := by simpa [g] using hg.tendsto 0
    rw [ContinuousAt, show 𝓡 d 0 = 0 by simp [𝓡]]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun η ↦ by unfold 𝓡; split_ifs <;> positivity) ?_
    filter_upwards [gt_mem_nhds one_pos] with η hη
    unfold 𝓡
    split_ifs with h
    · simp only [g, max_eq_left h.le, min_eq_right hη.le]
      gcongr
      rw [Real.log_div (by positivity) h.ne', Real.log_mul (Real.exp_pos 1).ne' hd'.ne',
        Real.log_exp, Real.negMulLog]
      ring_nf; rfl
    · positivity
  · have hmin : 0 < min 1 η₀ := lt_min one_pos hpos
    have hc : ContinuousAt (fun x : ℝ ↦
        √(min 1 x) + √(x * Real.log (Real.exp 1 * d / min 1 x))) η₀ :=
      ((continuous_const.min continuous_id).sqrt.continuousAt).add
        (Real.continuous_sqrt.continuousAt.comp (continuousAt_id.mul
          ((continuousAt_const.div (continuous_const.min continuous_id).continuousAt
            hmin.ne').log (div_pos (by positivity) hmin).ne')))
    refine hc.congr ?_
    filter_upwards [lt_mem_nhds hpos] with η hη
    simp [𝓡, hη]

end Limits

/-! ## Regions: extension, partial trace of `aρ + b`, supports -/

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T V D E : Finset σ}

omit [∀ i, Fintype (loc i)] in
theorem extendId_sub (hD : D ⊆ T) (A B : Matrix (Reg loc D) (Reg loc D) ℂ) :
    extendId hD (A - B) = extendId hD A - extendId hD B := by
  rw [sub_eq_add_neg, extendId_add, ← neg_one_smul ℂ B, extendId_smul, neg_one_smul,
    ← sub_eq_add_neg]

omit [∀ i, Fintype (loc i)] in
/-- `A ↦ A ⊗ 1` as a linear map. -/
noncomputable def extendIdₗ (hD : D ⊆ T) :
    Matrix (Reg loc D) (Reg loc D) ℂ →ₗ[ℂ] Matrix (Reg loc T) (Reg loc T) ℂ where
  toFun := extendId hD
  map_add' := extendId_add hD
  map_smul' := extendId_smul hD

/-- `Tr_{T∖D}(aρ + b) = aρ_D + b dim(T∖D)`. -/
theorem ptrace_aff (hD : D ⊆ T) (a b : ℝ) (ρ : Matrix (Reg loc T) (Reg loc T) ℂ) :
    ptrace hD (aff a b ρ) = aff a (b * Fintype.card (Reg loc (T \ D))) (ptrace hD ρ) := by
  simp only [aff, ptrace_add, ptrace_smul, ptrace_one, smul_smul, Complex.ofReal_mul,
    Complex.ofReal_natCast]

/-- D5.12.11, support. `(Π_{ker ρ_D} ⊗ 1) √ρ = 0` for `ρ ≥ 0` on `T ⊇ D`. -/
theorem extendId_kerProj_mul_sqrt (hD : D ⊆ T) {ρ : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hρ : ρ.PosSemidef) : extendId hD (1 - bracketPow (ptrace hD ρ) 0) * CFC.sqrt ρ = 0 := by
  set Q := 1 - bracketPow (ptrace hD ρ) 0
  have hQ : Qᴴ = Q := by
    rw [conjTranspose_sub, conjTranspose_one, (isHermitian_bracketPow_zero _).eq]
  have hQQ : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      bracketPow_zero_mul_self, sub_self, sub_zero]
  have hs : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
  rw [← trace_mul_conjTranspose_self_eq_zero_iff, conjTranspose_mul, hs,
    ← extendId_conjTranspose, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt ρ),
    CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, trace_mul_comm, Matrix.mul_assoc, ← extendId_mul, hQQ,
    ← trace_ptrace_mul, trace_mul_comm,
    one_sub_bracketPow_zero_mul_self (posSemidef_ptrace hD hρ), trace_zero]

/-- D5.12.11, support. For `D ⊆ E ⊆ T`, `(Π_{ker ρ_D} ⊗ 1)(ρ̂_E^z ⊗ 1) √ρ = 0`: the output of
the inner phase lies in `supp ρ_D ⊗ (T ∖ D)`. -/
theorem extendId_kerProj_mul_hatPow_mul_sqrt (hDE : D ⊆ E) (hE : E ⊆ T)
    {ρ : Matrix (Reg loc T) (Reg loc T) ℂ} (hρ : ρ.PosSemidef) (z : ℂ) :
    extendId (hDE.trans hE) (1 - bracketPow (ptrace (hDE.trans hE) ρ) 0) *
      (extendId hE (hatPow (ptrace hE ρ) z) * CFC.sqrt ρ) = 0 := by
  have hρE := posSemidef_ptrace hE hρ
  rw [hatPow_eq_bracketPow_add, extendId_add, Matrix.add_mul, extendId_kerProj_mul_sqrt hE hρ,
    add_zero, ← add_sub_cancel (1 / 2 : ℂ) z, ← bracketPow_mul_bracketPow, bracketPow_half hρE,
    ← ptrace_ptrace hDE hE, ← extendId_extendId hDE hE, ← Matrix.mul_assoc, ← extendId_mul,
    ← Matrix.mul_assoc, extendId_kerProj_mul_sqrt hDE hρE, Matrix.zero_mul, extendId_zero,
    Matrix.zero_mul]

end Region

/-! ## D5.12.11 The regularised family -/

section Regularise

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {T X U F D : Finset σ}

/-- The phase difference `ρ̂_U^{-iu} ρ̂_{xU}^{iu} − ρ̂_{UF}^{-iu} ρ̂_{xUF}^{iu}` of a matrix `M` on
`T ⊇ x ∪ U ∪ F`, marginals `Tr_{T∖D} M`. -/
noncomputable def phaseOp (hX : X ⊆ T) (hU : U ⊆ T) (hF : F ⊆ T)
    (M : Matrix (Reg loc T) (Reg loc T) ℂ) (u : ℝ) : Matrix (Reg loc T) (Reg loc T) ℂ :=
  extendId hU (hatPow (ptrace hU M) (-(u * Complex.I))) *
      extendId (Finset.union_subset hX hU)
        (hatPow (ptrace (Finset.union_subset hX hU) M) (u * Complex.I)) -
    extendId (Finset.union_subset hU hF)
        (hatPow (ptrace (Finset.union_subset hU hF) M) (-(u * Complex.I))) *
      extendId (Finset.union_subset (Finset.union_subset hX hU) hF)
        (hatPow (ptrace (Finset.union_subset (Finset.union_subset hX hU) hF) M) (u * Complex.I))

/-- `∑_k η(a λ_k + b dim(T∖D))`, `λ` the spectrum of `Tr_{T∖D} M`: the entropy of the marginal
of `aM + b`. -/
noncomputable def regEnt (hD : D ⊆ T) {M : Matrix (Reg loc T) (Reg loc T) ℂ} (hM : M.IsHermitian)
    (a b : ℝ) : ℝ :=
  ∑ k, Real.negMulLog (a * (isHermitian_ptrace hD hM).eigenvalues k +
    b * Fintype.card (Reg loc (T \ D)))

theorem regionEntropy_eq_regEnt (ρ : SubState (Reg loc T) ℂ) (hD : D ⊆ T)
    {M : Matrix (Reg loc T) (Reg loc T) ℂ} (hM : M.IsHermitian) {a b : ℝ}
    (hρ : ρ.M = aff a b M) : ρ.regionEntropy hD = regEnt hD hM a b :=
  vonNeumann_aff (isHermitian_ptrace hD hM) _ (by
    change ptrace hD ρ.M = _
    rw [hρ, ptrace_aff])

theorem norm_hfun {z : ℂ} (hz : z.re = 0) (s : ℝ) : ‖hfun z s‖ = 1 := by
  unfold hfun
  split_ifs
  · rw [Complex.norm_exp]; simp [hz]
  · simp

/-- D5.12.11: `(ρ_{D,ε})^{z} → ρ̂_D^z` eigenvalue-wise on `supp ρ_D`, `ρ_{D,ε} = (1-ε)ρ_D + εc`. -/
theorem tendsto_hfun_aff (z : ℂ) {N c : ℝ} (hN : 0 < N) (hc : 0 ≤ c) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε ↦ hfun z ((1 - ε) * t + ε / N * c)) (𝓝[>] 0) (𝓝 (hfun z t)) := by
  have hc' : ContinuousAt (fun ε : ℝ ↦ Complex.exp (z * Real.log ((1 - ε) * t + ε / N * c))) 0 :=
    Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp
        ((show ContinuousAt (fun ε : ℝ ↦ (1 - ε) * t + ε / N * c) 0 by fun_prop).log
          (by simpa using ht.ne'))))
  have h0 := hc'.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [sub_zero, one_mul, zero_div, zero_mul, add_zero] at h0
  rw [show hfun z t = Complex.exp (z * Real.log t) from if_pos ht]
  refine h0.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have : 0 < (1 - ε) * t + ε / N * c :=
    add_pos_of_pos_of_nonneg (mul_pos (by linarith [hε.2]) ht) (by have := hε.1; positivity)
  simp only [hfun, if_pos this]

/-- D5.12.11 (the limit `ε → 0⁺`). If the faithful bound
`‖phaseOp(ρ) √ρ‖₂ ≤ c 𝓡_{I(x:F|U)_ρ}` holds for every positive definite state on `T`, it holds for
every state: apply it to `ρ_ε = (1-ε)ρ + ε I/dim T`; `η_ε → η` and `𝓡` is continuous; the phase
products on `√ρ_ε` converge in order of application, innermost first, each limit lying in the
support where the next phase converges, all phases of norm one. -/
theorem step_5_12_11 (hX : X ⊆ T) (hU : U ⊆ T) (hF : F ⊆ T) (c u : ℝ)
    (H : ∀ ρ : MState (Reg loc T) ℂ, ρ.M.PosDef →
      √((phaseOp hX hU hF ρ.M u * CFC.sqrt ρ.M)ᴴ * (phaseOp hX hU hF ρ.M u * CFC.sqrt ρ.M)).trace.re
        ≤ c * 𝓡 (Fintype.card (Reg loc X)) (condMutualInfo ρ.toSubState hX hU hF))
    (ρ : MState (Reg loc T) ℂ) :
    √((phaseOp hX hU hF ρ.M u * CFC.sqrt ρ.M)ᴴ * (phaseOp hX hU hF ρ.M u * CFC.sqrt ρ.M)).trace.re
      ≤ c * 𝓡 (Fintype.card (Reg loc X)) (condMutualInfo ρ.toSubState hX hU hF) := by
  have hne : Nonempty (Reg loc T) := by
    by_contra hne
    have := ρ.tr_eq_one
    simp [not_nonempty_iff.1 hne, Matrix.trace] at this
  have hd : 1 ≤ Fintype.card (Reg loc X) := Fintype.card_pos_iff.2 ⟨restr hX hne.some⟩
  set N : ℝ := (Fintype.card (Reg loc T) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  have hρh := ρ.psd.isHermitian
  set hXU := Finset.union_subset hX hU
  set hUF := Finset.union_subset hU hF
  set hXUF := Finset.union_subset hXU hF
  -- D5.12.11: `ρ_ε = (1-ε)ρ + ε I / N` is a faithful state
  have htr (ε : ℝ) : (aff (1 - ε) (ε / N) ρ.M).trace = 1 := by
    have hN' : (Fintype.card (Reg loc T) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [aff, trace_add, trace_smul, trace_smul, MState.trace_eq_one, trace_one]
    simp only [N, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_natCast]
    field_simp
    ring
  have hpd {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) : (aff (1 - ε) (ε / N) ρ.M).PosDef :=
    PosDef.posSemidef_add (ρ.psd.smul (Complex.zero_le_real.2 (by linarith [hε.2])))
      (PosDef.one.smul (Complex.zero_lt_real.2 (div_pos hε.1 hN)))
  let ρε {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) : MState (Reg loc T) ℂ :=
    MState.mk' (hpd hε).posSemidef (by rw [htr]; simp)
  -- D5.12.11: `η_ε → η`
  set E : ℝ → ℝ := fun ε ↦ regEnt hXU hρh (1 - ε) (ε / N) + regEnt hUF hρh (1 - ε) (ε / N) -
    regEnt hU hρh (1 - ε) (ε / N) - regEnt hXUF hρh (1 - ε) (ε / N)
  have hE {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) :
      condMutualInfo (ρε hε).toSubState hX hU hF = E ε := by
    have key {D : Finset σ} (hD : D ⊆ T) := regionEntropy_eq_regEnt (ρε hε).toSubState hD hρh
      (a := 1 - ε) (b := ε / N) rfl
    simp only [condMutualInfo, E, key]
  have hE0 : E 0 = condMutualInfo ρ.toSubState hX hU hF := by
    have h10 : ρ.M = aff (1 - 0) (0 / N) ρ.M := by simp [aff]
    have key {D : Finset σ} (hD : D ⊆ T) := regionEntropy_eq_regEnt ρ.toSubState hD hρh h10
    simp only [condMutualInfo, E, key]
  have hEc : Continuous E := by
    simp only [E, regEnt]
    have := Real.continuous_negMulLog
    fun_prop
  -- D5.12.11: the phase products on `√ρ_ε`, in the eigenbases of `ρ` and its marginals
  have hDh {D : Finset σ} (hD : D ⊆ T) := isHermitian_ptrace hD hρh
  have hnn {D : Finset σ} (hD : D ⊆ T) := (posSemidef_ptrace hD ρ.psd).eigenvalues_nonneg
  have hph {D : Finset σ} (hD : D ⊆ T) (z : ℂ) (ε : ℝ) :
      hatPow (ptrace hD (aff (1 - ε) (ε / N) ρ.M)) z =
        specFun (hDh hD)
          (fun t ↦ hfun z ((1 - ε) * t + ε / N * Fintype.card (Reg loc (T \ D)))) := by
    rw [ptrace_aff, hatPow_eq (isHermitian_aff (hDh hD) _ _), specFun_aff]
  set S : ℝ → Matrix (Reg loc T) (Reg loc T) ℂ :=
    fun ε ↦ specFun hρh (fun t ↦ ((√((1 - ε) * t + ε / N) : ℝ) : ℂ))
  have hS {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) : CFC.sqrt (aff (1 - ε) (ε / N) ρ.M) = S ε := by
    rw [sqrt_eq_specFun (hpd hε).posSemidef, specFun_aff hρh]
  have hS0 : Tendsto S (𝓝[>] 0) (𝓝 (CFC.sqrt ρ.M)) := by
    rw [sqrt_eq_specFun ρ.psd]
    refine tendsto_specFun hρh fun k ↦ ?_
    have : Continuous fun ε : ℝ ↦ ((√((1 - ε) * hρh.eigenvalues k + ε / N) : ℝ) : ℂ) := by
      fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hre (s : ℝ) : (s * Complex.I).re = 0 := by simp
  have hre' (s : ℝ) : (-(s * Complex.I)).re = 0 := by simp
  have hcard (D : Finset σ) : (0 : ℝ) ≤ Fintype.card (Reg loc (T \ D)) := Nat.cast_nonneg _
  have step {D : Finset σ} (hD : D ⊆ T) (z : ℂ) (hz : z.re = 0) {Y : ℝ → Matrix (Reg loc T)
      (Reg loc T) ℂ} {Y₀ : Matrix (Reg loc T) (Reg loc T) ℂ} (hY : Tendsto Y (𝓝[>] 0) (𝓝 Y₀))
      (hK : extendId hD (1 - bracketPow (ptrace hD ρ.M) 0) * Y₀ = 0) :
      Tendsto (fun ε ↦ extendId hD (hatPow (ptrace hD (aff (1 - ε) (ε / N) ρ.M)) z) * Y ε)
        (𝓝[>] 0) (𝓝 (extendId hD (hatPow (ptrace hD ρ.M) z) * Y₀)) := by
    simp only [hph, hatPow_eq (hDh hD)]
    exact tendsto_specFun_mul (hDh hD) (hnn hD) (extendIdₗ hD)
      (fun t ht ↦ tendsto_hfun_aff z hN (hcard D) ht)
      (Eventually.of_forall fun _ ↦ norm_hfun hz _) (by simp [hfun]) hY hK
  -- D5.12.11: innermost `ρ̂_{xU,ε}^{iu}`, then `ρ̂_{U,ε}^{-iu}`; same for `(xUF, UF)`
  have hXU' := step hXU _ (hre u) hS0 (extendId_kerProj_mul_sqrt hXU ρ.psd)
  have hK2 := extendId_kerProj_mul_hatPow_mul_sqrt (D := U) Finset.subset_union_right hXU ρ.psd
    (u * Complex.I)
  have hU' := step hU (-(u * Complex.I)) (hre' u) hXU' hK2
  have hXUF' := step hXUF _ (hre u) hS0 (extendId_kerProj_mul_sqrt hXUF ρ.psd)
  have hK3 := extendId_kerProj_mul_hatPow_mul_sqrt (D := U ∪ F)
    (Finset.union_subset_union Finset.subset_union_right subset_rfl) hXUF ρ.psd (u * Complex.I)
  have hUF' := step hUF (-(u * Complex.I)) (hre' u) hXUF' hK3
  have hΦ : Continuous fun M : Matrix (Reg loc T) (Reg loc T) ℂ ↦ √((Mᴴ * M).trace.re) :=
    Real.continuous_sqrt.comp (Complex.continuous_re.comp
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_trace))
  have hW := (hΦ.tendsto _).comp (hU'.sub hUF')
  have hR := (((continuous_𝓡 hd).tendsto _).comp
    ((hEc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))).const_mul c
  rw [← hE0, show phaseOp hX hU hF ρ.M u * CFC.sqrt ρ.M = _ by
    rw [phaseOp, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]]
  refine le_of_tendsto_of_tendsto hW hR ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have hb := H (ρε hε) (hpd hε)
  rw [hE hε, show phaseOp hX hU hF (ρε hε).M u * CFC.sqrt (ρε hε).M = _ by
    rw [show (ρε hε).M = aff (1 - ε) (ε / N) ρ.M from rfl, phaseOp, hS hε, Matrix.sub_mul,
      Matrix.mul_assoc, Matrix.mul_assoc]] at hb
  exact hb

end Regularise

end Conditional

/-! ## Lemma 5.2 -/

section Main

universe u v

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ T : Finset σ}

/-- D5.12.10, (F1): `‖(W ⊗ I) θ‖ = ‖W √ρ_T‖₂` for `W` on `T ⊆ Λ`. -/
theorem Conditional.norm_extendId_mulVec (θ : Reg loc Λ → ℂ) (hT : T ⊆ Λ)
    (W : Matrix (Reg loc T) (Reg loc T) ℂ) :
    ‖(WithLp.toLp 2 (extendId hT W *ᵥ θ) : EuclideanSpace ℂ (Reg loc Λ))‖ =
      √(((W * CFC.sqrt (marg θ hT))ᴴ * (W * CFC.sqrt (marg θ hT))).trace.re) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Conditional.norm_toLp_sq, step_5_1_F1_sqrt]

open Conditional in
/-- D5.12 **Lemma 5.2** from its faithful case (D5.12.10–11). With `ρ_f = ρ_{xUF}`: (F1) turns
`‖(ρ̂_U^{-iu} ρ̂_{xU}^{iu} − ρ̂_{UF}^{-iu} ρ̂_{xUF}^{iu}) θ‖` into the Hilbert–Schmidt norm of the
same operator times `√ρ_f`, the marginals of `θ` being those of `ρ_f`; D5.12.11 extends the
faithful bound to singular `ρ_f`; the constant `C` is unchanged. -/
theorem lemma_5_2_of_faithful (hf : Lemma_5_2_faithful.{u, v}) : Lemma_5_2.{u, v} := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, fun σ _ loc _ _ Λ P X U F hX hU hF _ _ _ _ hXU hXF hUF θ hθ u ↦ ?_⟩
  have hT : X ∪ U ∪ F ⊆ Λ := Finset.union_subset (Finset.union_subset hX hU) hF
  have hX' : X ⊆ X ∪ U ∪ F := Finset.subset_union_left.trans Finset.subset_union_left
  have hU' : U ⊆ X ∪ U ∪ F := Finset.subset_union_right.trans Finset.subset_union_left
  have hF' : F ⊆ X ∪ U ∪ F := Finset.subset_union_right
  set ρ := (pureState θ hθ).restrict hT
  -- D5.12.11: the faithful bound holds for every state `ρ_f` on `xUF`
  have hb := step_5_12_11 hX' hU' hF' (C * |Real.sinh (Real.pi * u)|) u
    (fun ρ' hρ' ↦ hf σ loc _ X U F hX' hU' hF' rfl hXU hXF hUF ρ' hρ' u) ρ
  convert hb using 1
  · -- D5.12.10: (F1), `θ` purifies `ρ_f`; marginals and extensions are transitive
    refine (congrArg (fun A ↦ ‖(WithLp.toLp 2 (A *ᵥ θ) : EuclideanSpace ℂ (Reg loc Λ))‖) ?_).trans
      (norm_extendId_mulVec θ hT (phaseOp hX' hU' hF' ρ.M u))
    simp only [phaseOp, extendId_sub, extendId_mul, extendId_extendId, ρ, MState.restrict_M,
      ptrace_ptrace]
    rfl
  · simp only [condMutualInfo, SubState.regionEntropy, ρ, MState.toSubState_restrict,
      SubState.restrict_restrict]

/-- D5.12 **Lemma 5.2** (marginal-phase comparison): the faithful case `lemma_5_2_faithful`
(D5.12.1–10) and the regularisation `lemma_5_2_of_faithful` (D5.12.11). -/
theorem lemma_5_2 : Lemma_5_2.{u, v} := lemma_5_2_of_faithful lemma_5_2_faithful

end Main

end AreaLaw
