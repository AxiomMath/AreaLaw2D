import AreaLawRefactored.S02_Preliminaries

/-!
# §4.3 Ground energy, gap and ground vector of the truncated Hamiltonian

Digest `digest/04-quasilocal.md` (D4.13), paper `paper/sections/03-quasilocal.tex`
lines 488–503. No geometry: an arbitrary finite index type `ι`.
-/

namespace AreaLaw

open Arealaw OpenAI Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- D4.13. Given `‖H̃ - H_F‖ ≤ ε := ε_n ≤ g/4`: `Ẽ₀ ∈ [0, ε]`; second eigenvalue of `H̃` `≥ g - ε`;
gap `≥ g - 2ε ≥ g/2`; ground vector unique; with phase fixed so `⟨Ω, Ω̃⟩ ≥ 0`:
`‖Ω̃ - Ω‖ ≤ 2√(ε/g)` and `½‖|Ω̃⟩⟨Ω̃| - P_Ω‖₁ ≤ √(2ε/g)`. -/
theorem step_4_13 {HF Ht : Matrix ι ι ℂ} {Ω : ι → ℂ} {g ε : ℝ} (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hHF : 0 ≤ HF) (hHFΩ : HF *ᵥ Ω = 0) (hgap : (g : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤ HF)
    (hHt : 0 ≤ Ht) (hdiff : ‖Ht - HF‖ ≤ ε) (hg : 0 < g) (hε : ε ≤ g / 4) :
    ∃ (E : ℝ) (Ωt : ι → ℂ) (hΩt : star Ωt ⬝ᵥ Ωt = 1),
      Ht *ᵥ Ωt = (E : ℂ) • Ωt ∧ 0 ≤ E ∧ E ≤ ε ∧ (E : ℂ) • 1 ≤ Ht ∧
      (E : ℂ) • vecMulVec Ωt (star Ωt) + ((g - ε : ℝ) : ℂ) • (1 - vecMulVec Ωt (star Ωt)) ≤ Ht ∧
      HasGlobalGap Ht Ωt E (g - 2 * ε) ∧ g / 2 ≤ g - 2 * ε ∧ HasGlobalGap Ht Ωt E (g / 2) ∧
      (∀ v, Ht *ᵥ v = (E : ℂ) • v → ∃ c : ℂ, v = c • Ωt) ∧
      (∃ s : ℝ, 0 ≤ s ∧ star Ω ⬝ᵥ Ωt = s) ∧
      √(star (Ωt - Ω) ⬝ᵥ (Ωt - Ω)).re ≤ 2 * √(ε / g) ∧
      traceDist (pureState Ωt hΩt) (pureState Ω hΩ) ≤ √(2 * ε / g) := by
  -- quadratic forms `q M x = Re ⟨x, M x⟩`; the Loewner order gives their order
  set q : Matrix ι ι ℂ → (ι → ℂ) → ℝ := fun M x => (star x ⬝ᵥ (M *ᵥ x)).re with hq
  have hmono {A B : Matrix ι ι ℂ} (h : A ≤ B) (x : ι → ℂ) : q A x ≤ q B x := by
    have := (le_iff.mp h).dotProduct_mulVec_nonneg x
    rw [sub_mulVec, dotProduct_sub] at this
    simpa [hq] using (Complex.le_def.mp this).1
  have hHtH : Ht.IsHermitian := by simpa using (le_iff.mp hHt).isHermitian
  have hHFH : HF.IsHermitian := by simpa using (le_iff.mp hHF).isHermitian
  have hnorm (x : ι → ℂ) : 0 ≤ (star x ⬝ᵥ x).re :=
    (Complex.le_def.mp (dotProduct_star_self_nonneg x)).1
  have hqsub (A B : Matrix ι ι ℂ) (x : ι → ℂ) : q (A - B) x = q A x - q B x := by
    simp [hq, sub_mulVec]
  have hqr (r : ℝ) (x : ι → ℂ) : q (algebraMap ℝ _ r) x = r * (star x ⬝ᵥ x).re := by
    simp only [hq, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, dotProduct_smul,
      Complex.smul_re, smul_eq_mul]
  have hqneg (A : Matrix ι ι ℂ) (x : ι → ℂ) : q (-A) x = - q A x := by simp [hq, neg_mulVec]
  have hconj (x y : ι → ℂ) : star x ⬝ᵥ y = star (star y ⬝ᵥ x) := by
    rw [← star_dotProduct_star, star_star, dotProduct_comm]
  have hqP (t : ℝ) (w x : ι → ℂ) : q ((t : ℂ) • (1 - vecMulVec w (star w))) x =
      t * ((star x ⬝ᵥ x).re - ‖star w ⬝ᵥ x‖ ^ 2) := by
    simp only [hq, smul_mulVec, sub_mulVec, one_mulVec, vecMulVec_mulVec, dotProduct_smul,
      dotProduct_sub, op_smul_eq_mul, hconj x w, Complex.star_def, Complex.conj_mul', smul_eq_mul]
    rw [Complex.re_ofReal_mul, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hsa : IsSelfAdjoint (Ht - HF) := (hHtH.sub hHFH).isSelfAdjoint
  have hQd (x : ι → ℂ) : |q Ht x - q HF x| ≤ ε * (star x ⬝ᵥ x).re := by
    have h1 := hmono hsa.le_algebraMap_norm_self x
    have h2 := hmono hsa.neg_algebraMap_norm_le_self x
    rw [hqsub, hqr] at h1
    rw [hqsub, hqneg, hqr] at h2
    rw [abs_le]
    constructor <;> nlinarith [hnorm x]
  have hQg (x : ι → ℂ) : g * ((star x ⬝ᵥ x).re - ‖star Ω ⬝ᵥ x‖ ^ 2) ≤ q HF x :=
    hqP g Ω x ▸ hmono hgap x
  have hQt (x : ι → ℂ) : 0 ≤ q Ht x := by simpa [hq] using hmono hHt x
  -- the spectral decomposition `H̃ = U diag(e) U*`
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [dotProduct] at hΩ
  set b := hHtH.eigenvectorBasis
  set e := hHtH.eigenvalues
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min e
  set E := e i₀ with hE
  set u : ι → ℂ := (b i₀).ofLp with hu_def
  have hb (i j : ι) : star (b i).ofLp ⬝ᵥ (b j).ofLp = if i = j then 1 else 0 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, b.inner_eq_ite]
  have heig (j : ι) : Ht *ᵥ (b j).ofLp = (e j : ℂ) • (b j).ofLp := by
    rw [hHtH.mulVec_eigenvectorBasis, Complex.coe_smul]
  have hu : star u ⬝ᵥ u = 1 := by simpa using hb i₀ i₀
  have hqeig (j : ι) : q Ht (b j).ofLp = e j := by simp [hq, heig, dotProduct_smul, hb]
  set U : Matrix ι ι ℂ := (hHtH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hspec : Ht = U * diagonal (fun j => (e j : ℂ)) * star U := by
    conv_lhs => rw [hHtH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem (SetLike.coe_mem _)
  set P := vecMulVec u (star u) with hP_def
  have hPU : U * diagonal (Pi.single i₀ 1) * star U = P := by
    ext i k
    simp [hU, P, u, mul_apply, diagonal_apply, Pi.single_apply, vecMulVec_apply,
      IsHermitian.eigenvectorUnitary_apply, star_apply]
    rfl
  have hLoew (a c : ℝ) (ha : a ≤ E) (hc : ∀ j ≠ i₀, c ≤ e j) :
      (a : ℂ) • P + (c : ℂ) • (1 - P) ≤ Ht := by
    have hd : diagonal (fun j => ((if j = i₀ then a else c : ℝ) : ℂ)) =
        ((a - c : ℝ) : ℂ) • diagonal (Pi.single i₀ 1) + (c : ℂ) • 1 := by
      ext i k
      simp only [diagonal_apply, Pi.single_apply, Matrix.add_apply, Matrix.smul_apply, one_apply]
      split_ifs <;> push_cast [smul_eq_mul] <;> ring
    have hM : U * diagonal (fun j => ((if j = i₀ then a else c : ℝ) : ℂ)) * star U =
        (a : ℂ) • P + (c : ℂ) • (1 - P) := by
      rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hPU,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
      push_cast
      module
    rw [← hM, le_iff]
    nth_rw 1 [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    refine (posSemidef_diagonal_iff.mpr fun j => ?_).mul_mul_conjTranspose_same U
    by_cases hj : j = i₀
    · simp [hj, ← hE, ha]
    · simpa [hj] using hc j hj
  -- D4.13.1
  have hground : algebraMap ℝ (Matrix ι ι ℂ) E ≤ Ht := by
    convert hLoew E E le_rfl (fun j _ => hi₀ j) using 1
    rw [← smul_add, add_sub_cancel, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  have hqu : q Ht u = E := hqeig i₀
  have hE0 : 0 ≤ E := hqu ▸ hQt u
  have hEε : E ≤ ε := by
    have h1 := hmono hground Ω
    have h2 := hQd Ω
    have h3 : q HF Ω = 0 := by simp [hq, hHFΩ]
    rw [hqr, hΩ, Complex.one_re, mul_one] at h1
    rw [hΩ, Complex.one_re, mul_one, h3, sub_zero] at h2
    linarith [le_abs_self (q Ht Ω)]
  -- D4.13.4 (used in D4.13.2: `|⟨Ω, Ω̃⟩|² ≥ 1/2`)
  set β := star Ω ⬝ᵥ u with hβ_def
  have hover : g * (1 - ‖β‖ ^ 2) ≤ 2 * ε := by
    have h1 := hQg u
    have h2 := hQd u
    rw [hu, Complex.one_re] at h1 h2
    rw [mul_one, hqu] at h2
    linarith [(abs_le.mp h2).1]
  have hβ : 1 / 2 ≤ ‖β‖ ^ 2 := by nlinarith
  have hn (z : ℂ) : z * star z = (‖z‖ : ℂ) ^ 2 := Complex.mul_conj' z
  -- D4.13.2
  have hsecond (j : ι) (hj : j ≠ i₀) : g - ε ≤ e j := by
    set v : ι → ℂ := (b j).ofLp with hv_def
    set α := star Ω ⬝ᵥ v with hα_def
    set φ := (-α) • u + β • v with hφ_def
    have huv : star u ⬝ᵥ v = 0 := by simpa [Ne.symm hj] using hb i₀ j
    have hvu : star v ⬝ᵥ u = 0 := by simpa [hj] using hb j i₀
    have hv : star v ⬝ᵥ v = 1 := by simpa using hb j j
    have hφΩ : star Ω ⬝ᵥ φ = 0 := by
      simp only [hφ_def, dotProduct_add, dotProduct_smul, smul_eq_mul, ← hα_def, ← hβ_def]
      ring
    have hφφ : star φ ⬝ᵥ φ = ((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hφ_def, star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, hu, hv, huv, hvu, smul_eq_mul, star_neg]
      push_cast
      linear_combination hn α + hn β
    have hφH : star φ ⬝ᵥ (Ht *ᵥ φ) = ((‖α‖ ^ 2 * E + ‖β‖ ^ 2 * e j : ℝ) : ℂ) := by
      have hHu : Ht *ᵥ u = (E : ℂ) • u := heig i₀
      have hHv : Ht *ᵥ v = (e j : ℂ) • v := heig j
      simp only [hφ_def, mulVec_add, mulVec_smul, hHu, hHv, star_add, star_smul, add_dotProduct,
        dotProduct_add, smul_dotProduct, dotProduct_smul, hu, hv, huv, hvu, smul_eq_mul, star_neg]
      push_cast
      linear_combination (E : ℂ) * hn α + (e j : ℂ) * hn β
    have h1 := hQg φ
    have h2 := hQd φ
    have hqφ : q Ht φ = ‖α‖ ^ 2 * E + ‖β‖ ^ 2 * e j := by simp only [hq, hφH, Complex.ofReal_re]
    rw [hφΩ, norm_zero, hφφ, Complex.ofReal_re] at h1
    rw [hφφ, Complex.ofReal_re, hqφ] at h2
    have hA : 0 ≤ ‖α‖ ^ 2 * (g - ε - E) := mul_nonneg (by positivity) (by linarith)
    have hkey : ‖β‖ ^ 2 * (g - ε) ≤ ‖β‖ ^ 2 * e j := by nlinarith [(abs_le.mp h2).1]
    exact le_of_mul_le_mul_left hkey (by linarith)
  have hε0 : 0 ≤ ε := hE0.trans hEε
  -- D4.13.6: the phase `Ω̃ = c u` with `c = β̄ / |β|`
  have hβn : (‖β‖ : ℂ) ≠ 0 := by
    have : β ≠ 0 := by
      rintro h
      rw [h, norm_zero] at hβ
      norm_num at hβ
    exact_mod_cast norm_ne_zero_iff.mpr this
  set c : ℂ := star β / ‖β‖ with hc_def
  have hcc : star c * c = 1 := by
    rw [hc_def, star_div₀, star_star, show star (‖β‖ : ℂ) = ‖β‖ from Complex.conj_ofReal _]
    field_simp
    linear_combination hn β
  set Ωt := c • u with hΩt_def
  have hΩt : star Ωt ⬝ᵥ Ωt = 1 := by
    simp only [hΩt_def, star_smul, smul_dotProduct, dotProduct_smul, hu, smul_eq_mul]
    linear_combination hcc
  have hPt : vecMulVec Ωt (star Ωt) = P := by
    ext i k
    simp only [hΩt_def, hP_def, vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
      star_mul']
    linear_combination (u i * star (u k)) * hcc
  have hstar : star Ω ⬝ᵥ Ωt = ‖β‖ := by
    rw [hΩt_def, dotProduct_smul, smul_eq_mul, ← hβ_def, hc_def]
    field_simp
    linear_combination hn β
  have hΩtE : Ht *ᵥ Ωt = (E : ℂ) • Ωt := by
    rw [hΩt_def, mulVec_smul, show Ht *ᵥ u = (E : ℂ) • u from heig i₀, smul_comm]
  -- D4.13.3
  have hgapΔ (Δ : ℝ) (hΔ : Δ ≤ g - 2 * ε) : HasGlobalGap Ht Ωt E Δ := by
    rw [HasGlobalGap, hPt, le_sub_iff_add_le]
    convert hLoew E (E + Δ) le_rfl (fun j hj => by linarith [hsecond j hj]) using 1
    push_cast
    module
  -- D4.13.5
  have hdist : traceDist (pureState Ωt hΩt) (pureState Ω hΩ) = √(1 - ‖β‖ ^ 2) := by
    have h := traceNorm_vecMulVec_sub_vecMulVec_div_two hΩt hΩ
    rw [hconj Ωt Ω, hstar, norm_star, Complex.norm_real, norm_norm] at h
    rw [traceDist, MState.D₁_eq_traceNorm_div_two]
    exact h
  have hd : star (Ωt - Ω) ⬝ᵥ (Ωt - Ω) = ((2 - 2 * ‖β‖ : ℝ) : ℂ) := by
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hΩt, hΩ, hstar, hconj Ωt Ω,
      hstar, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have hs1 : ‖β‖ ≤ 1 := by
    have := hnorm (Ωt - Ω)
    rw [hd, Complex.ofReal_re] at this
    linarith
  refine ⟨E, Ωt, hΩt, hΩtE, hE0, hEε, ?_, ?_, hgapΔ _ le_rfl, by linarith, hgapΔ _ (by linarith),
    ?_, ⟨‖β‖, norm_nonneg _, hstar⟩, ?_, ?_⟩
  · rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at hground
  · rw [hPt]
    exact hLoew E (g - ε) le_rfl hsecond
  · -- D4.13.3: uniqueness from the positive gap
    intro v hv
    set r := v - (star Ωt ⬝ᵥ v) • Ωt with hr_def
    have hr : (Ht - (E : ℂ) • 1) *ᵥ r = 0 := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, hr_def, mulVec_sub, mulVec_smul, hv, hΩtE,
        smul_comm, smul_sub, sub_self]
    have hΩr : star Ωt ⬝ᵥ r = 0 := by
      rw [hr_def, dotProduct_sub, dotProduct_smul, hΩt, smul_eq_mul, mul_one, sub_self]
    have h : q (((g / 2 : ℝ) : ℂ) • (1 - vecMulVec Ωt (star Ωt))) r ≤ q (Ht - (E : ℂ) • 1) r :=
      hmono (hgapΔ (g / 2) (by linarith)) r
    rw [hqP, hΩr, norm_zero] at h
    simp only [hq, hr, dotProduct_zero, Complex.zero_re] at h
    have hr0 : star r ⬝ᵥ r = 0 := by
      have h0 := Complex.le_def.mp (dotProduct_star_self_nonneg r)
      apply Complex.ext
      · simp only [Complex.zero_re]
        nlinarith [hnorm r]
      · simpa using h0.2.symm
    exact ⟨_, sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp hr0)⟩
  · -- D4.13.6
    rw [hd, Complex.ofReal_re, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (div_nonneg hε0 hg.le), mul_div_assoc', le_div_iff₀ hg]
    nlinarith [norm_nonneg β]
  · -- D4.13.5
    rw [hdist]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ hg]
    linarith

end AreaLaw
