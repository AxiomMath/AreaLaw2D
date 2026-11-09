import AreaLaw.S05_Conditional.Spectral
import AreaLaw.S05_Conditional.PhaseRate
import AreaLaw.S05_Conditional.Compression
import AreaLaw.S05_Conditional.HilbertSchmidt
import AreaLaw.S05_Conditional.Interfaces
import AreaLawForMathlib.Analysis.SpecialFunctions.ResolventMellin

/-!
# §5.2 Lemma 5.2, faithful case (D5.12.1–10)

Digest `digest/05-conditional.md` (D5.12, D5.13, D5.14), paper
`paper/sections/04-conditional.tex` lines 310–479. The resolvent compression of
`HilbertSchmidt.lean` turns the phase discrepancy into `A^{-iu} a₀ - V B^{-iu} b₀`; the resolvent
Mellin integral (D5.12.6), its boundary value at `Re z = 0` (D5.12.7) and the rate bound
`step_5_12_8` give `Lemma_5_2_faithful`.
-/

namespace AreaLaw

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace Real ComplexOrder MatrixOrder

namespace Conditional

namespace ResolventCompression

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] {ι κ : Type*} [Fintype ι] [Fintype κ]
  (R : ResolventCompression E F ι κ)

/-- `A^z = ∑ λᵢ^z Πᵢ`. -/
noncomputable def powA (z : ℂ) : E → E := spec R.eA fun i ↦ Complex.exp (z * Real.log (R.lam i))

/-- `B^z = ∑ μⱼ^z Πⱼ`. -/
noncomputable def powB (z : ℂ) : F → F := spec R.eB fun j ↦ Complex.exp (z * Real.log (R.mu j))

end ResolventCompression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- D5.12.6, vector form: for `xₖ > 0`, `wₖ ∈ E` and `-1 < Re z < 0`,
`∑ xₖ^z wₖ = -(sin πz / π) ∫₀^∞ v^z ∑ (xₖ + v)⁻¹ wₖ dv`, the integrand being integrable. -/
theorem sum_cpow_smul_eq_integral {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ k, 0 < x k)
    (w : ι → E) {z : ℂ} (h1 : -1 < z.re) (h0 : z.re < 0) :
    IntegrableOn (fun v : ℝ ↦ (v : ℂ) ^ z • ∑ k ∈ s, (((x k + v)⁻¹ : ℝ) : ℂ) • w k) (Ioi 0) ∧
      ∑ k ∈ s, Complex.exp (z * Real.log (x k)) • w k =
        -(Complex.sin (π * z) / π) •
          ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ z • ∑ k ∈ s, (((x k + v)⁻¹ : ℝ) : ℂ) • w k := by
  have hf : (fun v : ℝ ↦ (v : ℂ) ^ z • ∑ k ∈ s, (((x k + v)⁻¹ : ℝ) : ℂ) • w k) =
      fun v : ℝ ↦ ∑ k ∈ s, ((v : ℂ) ^ z / (x k + v)) • w k := by
    funext v
    simp only [Finset.smul_sum, smul_smul]
    push_cast
    simp only [div_eq_mul_inv]
  have hi : ∀ k ∈ s, IntegrableOn (fun v : ℝ ↦ ((v : ℂ) ^ z / (x k + v)) • w k) (Ioi 0) :=
    fun k _ ↦ (Complex.integrableOn_Ioi_cpow_div_add (hx k) h1 h0).smul_const (w k)
  have hsin := Complex.sin_pi_mul_ne_zero_of_re_mem h1 h0
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  refine ⟨hf ▸ integrable_finsetSum s hi, ?_⟩
  rw [hf, integral_finsetSum s hi, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_smul_const, Complex.integral_Ioi_cpow_div_add (hx k) h1 h0, smul_smul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (hx k).ne'),
    ← Complex.ofReal_log (hx k).le]
  congr 1
  field_simp
  ring_nf
  exact (mul_inv_cancel₀ (by rwa [mul_comm] at hsin)).symm

namespace ResolventCompression

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ι κ : Type*} [Fintype ι]
  [Fintype κ] (R : ResolventCompression E F ι κ)

omit [CompleteSpace E] in
/-- `φ(A) a₀ - V ψ(B) b₀` in the eigenbases, with `wᵢ = ⟪eᵢ, a₀⟫ eᵢ`, `w'ⱼ = ⟪fⱼ, b₀⟫ V fⱼ`. -/
theorem spec_a₀_sub (φ : ι → ℂ) (ψ : κ → ℂ) :
    spec R.eA φ R.a₀ - R.V (spec R.eB ψ R.b₀) =
      ∑ i, φ i • (⟪R.eA i, R.a₀⟫_ℂ • R.eA i) - ∑ j, ψ j • (⟪R.eB j, R.b₀⟫_ℂ • R.V (R.eB j)) := by
  simp only [spec, map_sum, map_smul, smul_smul]

/-- D5.12.6. For `-1 < Re z < 0`: `A^z a₀ - V B^z b₀ = -(sin πz / π) ∫₀^∞ v^z δ_v dv`, from
`∫₀^∞ v^z / (x + v) dv = -(π / sin πz) x^z` on each eigenvalue. -/
theorem step_5_12_6 {z : ℂ} (h1 : -1 < z.re) (h0 : z.re < 0) :
    IntegrableOn (fun v : ℝ ↦ (v : ℂ) ^ z • R.δ v) (Ioi 0) ∧
      R.powA z R.a₀ - R.V (R.powB z R.b₀) =
        -(Complex.sin (π * z) / π) • ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ z • R.δ v := by
  obtain ⟨hA, eA⟩ := sum_cpow_smul_eq_integral Finset.univ R.lam_pos
    (fun i ↦ ⟪R.eA i, R.a₀⟫_ℂ • R.eA i) h1 h0
  obtain ⟨hB, eB⟩ := sum_cpow_smul_eq_integral Finset.univ R.mu_pos
    (fun j ↦ ⟪R.eB j, R.b₀⟫_ℂ • R.V (R.eB j)) h1 h0
  have hδ : (fun v : ℝ ↦ (v : ℂ) ^ z • R.δ v) = fun v : ℝ ↦
      (v : ℂ) ^ z • ∑ i, (((R.lam i + v)⁻¹ : ℝ) : ℂ) • (⟪R.eA i, R.a₀⟫_ℂ • R.eA i) -
      (v : ℂ) ^ z • ∑ j, (((R.mu j + v)⁻¹ : ℝ) : ℂ) • (⟪R.eB j, R.b₀⟫_ℂ • R.V (R.eB j)) := by
    funext v
    rw [δ, resA, resB, spec_a₀_sub, smul_sub]
  refine ⟨hδ ▸ hA.sub hB, ?_⟩
  rw [powA, powB, spec_a₀_sub, eA, eB, hδ, integral_sub hA hB, smul_sub]

/-- `|sin(π(-iu))| = |sinh πu|`. -/
theorem norm_sin_pi_mul_neg_I (u : ℝ) :
    ‖Complex.sin (π * ((0 : ℝ) - u * Complex.I))‖ = |Real.sinh (π * u)| := by
  rw [show (π : ℂ) * ((0 : ℝ) - u * Complex.I) = ((-(π * u) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sin_mul_I, ← Complex.ofReal_sinh, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, Real.sinh_neg, abs_neg]

/-- D5.12.7. At `z = -iu`: `‖A^{-iu} a₀ - V B^{-iu} b₀‖ ≤ (|sinh πu| / π) ∫₀^∞ √(h(v)/v) dv`,
given the tails `h(v) ≤ min(d², v⁻²)` of D5.14. For `-1/4 ≤ Re z < 0`,
`‖v^z δ_v‖ ≤ v^{Re z} √(h/v)`; dominated convergence as `Re z ↑ 0`. -/
theorem step_5_12_7_vec {d : ℕ} (hh : ∀ v > 0, R.h v ≤ min ((d : ℝ) ^ 2) (v ^ 2)⁻¹) (u : ℝ) :
    ‖R.powA (-(u * Complex.I)) R.a₀ - R.V (R.powB (-(u * Complex.I)) R.b₀)‖ ≤
      |Real.sinh (π * u)| / π * ∫ v in Ioi 0, √(R.h v / v) := by
  set D : ℂ → E := fun z ↦ R.powA z R.a₀ - R.V (R.powB z R.b₀)
  obtain ⟨hI, hlim⟩ := step_5_12_7 (step_5_13 R).2.1 hh
  have hbound : ∀ s ∈ Ioo (-(1 / 4) : ℝ) 0, ‖D ((s : ℂ) - u * Complex.I)‖ ≤
      ‖Complex.sin (π * ((s : ℂ) - u * Complex.I))‖ / π *
        ∫ v in Ioi 0, v ^ s * √(R.h v / v) := by
    intro s hs
    have hre : ((s : ℂ) - u * Complex.I).re = s := by simp
    obtain ⟨-, he⟩ := step_5_12_6 R (z := (s : ℂ) - u * Complex.I) (by rw [hre]; linarith [hs.1])
      (by rw [hre]; exact hs.2)
    simp only [D]
    rw [he, norm_smul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, div_mul_eq_mul_div, mul_div_right_comm]
    gcongr
    refine norm_integral_le_of_norm_le (hI s ⟨hs.1.le, hs.2⟩) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v (hv : 0 < v)
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hv, hre]
    gcongr
    have h5 := (step_5_14 R hv).2.2.2
    rw [Real.le_sqrt (norm_nonneg _) (div_nonneg (step_5_14 R hv).1 hv.le), le_div_iff₀ hv]
    linarith
  have hD : Continuous D := by
    simp only [D, powA, powB, spec_a₀_sub]
    fun_prop
  have hz : Continuous fun s : ℝ ↦ (s : ℂ) - u * Complex.I := by fun_prop
  have hL : Tendsto (fun s : ℝ ↦ ‖D ((s : ℂ) - u * Complex.I)‖) (𝓝[<] 0)
      (𝓝 ‖D (-(u * Complex.I))‖) := by
    have := ((hD.comp hz).norm.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio 0))
    simpa using this
  have hR : Tendsto (fun s : ℝ ↦ ‖Complex.sin (π * ((s : ℂ) - u * Complex.I))‖ / π *
      ∫ v in Ioi 0, v ^ s * √(R.h v / v)) (𝓝[<] 0)
      (𝓝 (|Real.sinh (π * u)| / π * ∫ v in Ioi 0, √(R.h v / v))) := by
    refine Tendsto.mul ?_ hlim
    rw [← norm_sin_pi_mul_neg_I]
    exact (((Complex.continuous_sin.comp (continuous_const.mul hz)).norm.div_const _).tendsto
      0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hL hR
    (Filter.mem_of_superset (Ioo_mem_nhdsLT (by norm_num : -(1 / 4 : ℝ) < 0)) hbound)

/-- D5.12.5, D5.12.7–8. With `⟨a₀, A⁻¹ a₀⟩ ≤ d²` and `⟨b₀, B b₀⟩ ≤ 1` (D5.14.1–2):
`‖A^{-iu} a₀ - V B^{-iu} b₀‖ ≤ (4/π) |sinh πu| 𝓡_η`,
`η = -⟨a₀, log A a₀⟩ + ⟨b₀, log B b₀⟩ = ∫₀^∞ h` (D5.13). -/
theorem norm_powA_sub_le {d : ℕ} (hd : 1 ≤ d)
    (hA : (⟪R.a₀, R.invA R.a₀⟫_ℂ).re ≤ (d : ℝ) ^ 2) (hB : (⟪R.b₀, R.B R.b₀⟫_ℂ).re ≤ 1) (u : ℝ) :
    ‖R.powA (-(u * Complex.I)) R.a₀ - R.V (R.powB (-(u * Complex.I)) R.b₀)‖ ≤
      4 / π * |Real.sinh (π * u)| *
        𝓡 d (-(⟪R.a₀, R.logA R.a₀⟫_ℂ).re + (⟪R.b₀, R.logB R.b₀⟫_ℂ).re) := by
  obtain ⟨-, hint, hη⟩ := step_5_13 R
  -- D5.12.5 (D5.14)
  have hh : ∀ v > 0, R.h v ≤ min ((d : ℝ) ^ 2) (v ^ 2)⁻¹ := fun v hv ↦ by
    obtain ⟨-, h1, h2, -⟩ := step_5_14 R hv
    refine le_min (h1.trans hA) (h2.trans ?_)
    rw [inv_eq_one_div]
    gcongr
  -- D5.12.8
  have h8 := (step_5_12_8 hd hint (fun v hv ↦ (step_5_14 R hv).1) hh hη).2
  calc _ ≤ |Real.sinh (π * u)| / π * ∫ v in Ioi 0, √(R.h v / v) := step_5_12_7_vec R hh u
    _ ≤ |Real.sinh (π * u)| / π * (4 * 𝓡 d _) := by gcongr
    _ = _ := by ring

end ResolventCompression

/-! ## D5.12.10 Identifying the vectors -/

section HSPhase

open Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- D5.12.6–10. `A^z X = d^{-z} M^z X ρ^{-z}` for `A = L_σ R_{ρ⁻¹}`, `σ = M / d`. -/
theorem spec_hsLam_pow {M ρ : Matrix m m ℂ} {d : ℝ} (hM : M.PosDef) (hρ : ρ.PosDef) (hd : 0 < d)
    (z : ℂ) (X : Matrix m m ℂ) :
    spec (prodBasis hM.1 hρ.1) (fun p ↦ Complex.exp (z * Real.log (hsLam d hM.1 hρ.1 p))) (hs X) =
      hs (Complex.exp (-(z * Real.log d)) • hatPow M z * X * hatPow ρ (-z)) := by
  rw [spec_hsLam hM hρ (G := fun t ↦ Complex.exp (z * Real.log t))
      (f := fun a ↦ Complex.exp (-(z * Real.log d)) * Complex.exp (z * Real.log a))
      (g := fun b ↦ Complex.exp (-z * Real.log b)) fun a ha b hb ↦ by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_div ha.ne' hd.ne', Real.log_inv,
          ← Complex.exp_add, ← Complex.exp_add]
        push_cast; ring_nf,
    specFun_const_mul, specFun_eq_hatPow hM fun _ _ ↦ rfl, specFun_eq_hatPow hρ fun _ _ ↦ rfl]

variable {ρf Mf : Matrix m m ℂ} {ρs Ms : Matrix n n ℂ} {J : Matrix n n ℂ →ₐ[ℂ] Matrix m m ℂ}
  (hρf : ρf.PosDef) (hρs : ρs.PosDef) (hJ : ∀ Y, J Yᴴ = (J Y)ᴴ)
  (hJρ : ∀ Y, (ρf * J Y).trace = (ρs * Y).trace) (hMf : Mf.PosDef) (hMs : Ms.PosDef)
  (hJM : ∀ Y, (Mf * J Y).trace = (Ms * Y).trace)

include hρf hρs hJ hJρ hMf hMs hJM in
/-- D5.12.1–10, Hilbert–Schmidt form. With `d ≥ 1`, `ρ_f ≤ d M_f` (D5.2.1), `Tr ρ_f = 1`,
`Tr M_s = d`:
`‖(J(M_s^{-iu} ρ_s^{iu}) - M_f^{-iu} ρ_f^{iu}) √ρ_f‖₂ ≤ (4/π) |sinh πu| 𝓡_η`, where
`η = Tr ρ_f log ρ_f - Tr ρ_f log M_f - Tr ρ_s log ρ_s + Tr ρ_s log M_s`. -/
theorem step_5_12_10 {d : ℕ} (hd : 1 ≤ d) (hdom : ρf ≤ (d : ℂ) • Mf) (htr : ρf.trace.re = 1)
    (hMs1 : Ms.trace.re = d) (u : ℝ) :
    ‖hs ((J (hatPow Ms (-(u * Complex.I)) * hatPow ρs (u * Complex.I)) -
        hatPow Mf (-(u * Complex.I)) * hatPow ρf (u * Complex.I)) * hatPow ρf (1 / 2))‖ ≤
      4 / π * |Real.sinh (π * u)| * 𝓡 d
        ((ρf * specFun hρf.1 (fun t ↦ (Real.log t : ℂ))).trace -
          (ρf * specFun hMf.1 (fun t ↦ (Real.log t : ℂ))).trace -
          (ρs * specFun hρs.1 (fun t ↦ (Real.log t : ℂ))).trace +
          (ρs * specFun hMs.1 (fun t ↦ (Real.log t : ℂ))).trace).re := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set R := hsCompression hρf hρs hJ hJρ hMf hMs hJM hd0
  have hA : (⟪R.a₀, R.invA R.a₀⟫_ℂ).re ≤ (d : ℝ) ^ 2 := by
    have := hsCompression_invA_le hρf hρs hJ hJρ hMf hMs hJM hd0 (by exact_mod_cast hdom)
    rwa [htr, mul_one] at this
  have hB : (⟪R.b₀, R.B R.b₀⟫_ℂ).re ≤ 1 := by
    rw [hsCompression_quadB, ← Complex.ofReal_inv, Complex.re_ofReal_mul, hMs1,
      inv_mul_cancel₀ hd0.ne']
  have key := R.norm_powA_sub_le hd hA hB u
  rw [hsCompression_logGap] at key
  set z : ℂ := -(u * Complex.I)
  set c := Complex.exp (-(z * Real.log d))
  have hc : ‖c‖ = 1 := by
    rw [show c = Complex.exp (((u * Real.log d : ℝ) : ℂ) * Complex.I) by
      simp only [c, z]; congr 1; push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hD : R.powA z R.a₀ - R.V (R.powB z R.b₀) =
      c • -hs ((J (hatPow Ms z * hatPow ρs (u * Complex.I)) -
        hatPow Mf z * hatPow ρf (u * Complex.I)) * hatPow ρf (1 / 2)) := by
    rw [hsCompression_a₀]
    change spec (prodBasis hMf.1 hρf.1)
        (fun p ↦ Complex.exp (z * Real.log (hsLam (d : ℝ) hMf.1 hρf.1 p))) (hs _) -
      hsVLin J ρf ρs (spec (prodBasis hMs.1 hρs.1)
        (fun p ↦ Complex.exp (z * Real.log (hsLam (d : ℝ) hMs.1 hρs.1 p))) (hs _)) = _
    rw [spec_hsLam_pow hMf hρf hd0, spec_hsLam_pow hMs hρs hd0, hsVLin_hs, neg_neg]
    have e1 : hatPow Mf z * hatPow ρf (1 / 2) * hatPow ρf (u * Complex.I) =
        hatPow Mf z * hatPow ρf (u * Complex.I) * hatPow ρf (1 / 2) := by
      rw [Matrix.mul_assoc, (commute_hatPow_hatPow ρf _ _).eq, ← Matrix.mul_assoc]
    have e2 : hatPow Ms z * hatPow ρs (1 / 2) * hatPow ρs (u * Complex.I) * hatPow ρs (-(1 / 2)) =
        hatPow Ms z * hatPow ρs (u * Complex.I) := by
      rw [Matrix.mul_assoc (_ * _), Matrix.mul_assoc, hatPow_mul_hatPow, hatPow_mul_hatPow,
        show (1 / 2 + (u * Complex.I + -(1 / 2)) : ℂ) = u * Complex.I by ring]
    simp only [Matrix.smul_mul, map_smul, e1, e2]
    rw [hs_smul, hs_smul, ← smul_sub, Matrix.sub_mul, hs_sub, neg_sub]
  rw [hD, norm_smul, hc, one_mul, norm_neg] at key
  exact key

end HSPhase

/-! ## Region layer: extensions, partial traces, spectral functions -/

section Region

open Arealaw Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T : Finset σ}

omit [∀ i, Fintype (loc i)] in
/-- Extending to the same region does nothing. -/
theorem extendId_self (h : T ⊆ T) (A : Matrix (Reg loc T) (Reg loc T) ℂ) : extendId h A = A := by
  ext w w'
  simp only [extendId, of_apply]
  rw [if_pos (funext fun i ↦ absurd i.2 (by simp))]
  rfl

/-- `(N ⊗ 1) s_z = s_z N` for the slice isometries `s_z = |· ⊗ z⟩`. -/
theorem extendId_mul_sliceIsometry (h : S ⊆ T) (N : Matrix (Reg loc S) (Reg loc S) ℂ)
    (z : Reg loc (T \ S)) : extendId h N * sliceIsometry ℂ z = sliceIsometry ℂ z * N := by
  ext w x
  obtain ⟨u, z', rfl⟩ : ∃ u z', w = glue u z' := ⟨_, _, (glue_restr h w).symm⟩
  have hinj : ∀ y, (glue (T := T) u z' = glue y z) ↔ (u = y ∧ z' = z) := fun y ↦ by
    change glueEquiv h (u, z') = glueEquiv h (y, z) ↔ _
    rw [(glueEquiv h).injective.eq_iff, Prod.mk.injEq]
  simp only [mul_apply, sliceIsometry, of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, extendId_apply_glue, hinj]
  split_ifs with hz
  · subst hz
    simp
  · simp [hz]

/-- `g(N ⊗ 1) = g(N) ⊗ 1` for Hermitian `N`. -/
theorem specFun_extendId (h : S ⊆ T) {M : Matrix (Reg loc S) (Reg loc S) ℂ} (hM : M.IsHermitian)
    (g : ℝ → ℂ) : specFun (isHermitian_extendId h hM) g = extendId h (specFun hM g) := by
  have hX : ∀ z : Reg loc (T \ S), (specFun (isHermitian_extendId h hM) g -
      extendId h (specFun hM g)) * sliceIsometry (S := S) ℂ z = 0 := fun z ↦ by
    rw [Matrix.sub_mul, specFun_mul_intertwine _ hM _ (extendId_mul_sliceIsometry h M z),
      extendId_mul_sliceIsometry, sub_self]
  ext w' w
  have := congrFun (congrFun (hX (restr Finset.sdiff_subset w)) w') (restr h w)
  simp only [mul_apply, sliceIsometry, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, glue_restr, Matrix.zero_apply, Matrix.sub_apply] at this
  exact sub_eq_zero.1 this

/-- D5.12.3, `Tr_F σ_f = σ_s`: for `T = XUF` with `X ∩ F = ∅`,
`Tr_F (I_X ⊗ A_{UF}) = I_X ⊗ Tr_F A_{UF}`. -/
theorem ptrace_extendId_union {X U F : Finset σ} (hT : T = X ∪ U ∪ F) (hXF : Disjoint X F)
    (h₁ : X ∪ U ⊆ T) (h₂ : U ∪ F ⊆ T) (A : Matrix (Reg loc (U ∪ F)) (Reg loc (U ∪ F)) ℂ) :
    ptrace h₁ (extendId h₂ A) =
      extendId (Finset.subset_union_right : U ⊆ X ∪ U)
        (ptrace (Finset.subset_union_left : U ⊆ U ∪ F) A) := by
  subst hT
  have hXF' := Finset.disjoint_left.1 hXF
  have heq : (X ∪ U ∪ F) \ (X ∪ U) = (U ∪ F) \ U := by
    ext i; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
  ext a b
  simp only [ptrace, extendId, of_apply]
  have hcond : ∀ z : Reg loc ((X ∪ U ∪ F) \ (X ∪ U)),
      (restr (S := (X ∪ U ∪ F) \ (U ∪ F)) Finset.sdiff_subset (glue a z) =
        restr Finset.sdiff_subset (glue b z)) ↔
      restr (S := (X ∪ U) \ U) Finset.sdiff_subset a = restr Finset.sdiff_subset b := fun z ↦ by
    simp only [restr, Finset.restrict₂, funext_iff, Subtype.forall, Finset.mem_sdiff,
      Finset.mem_union, glue]
    constructor
    · rintro h i ⟨hi, hiU⟩
      have hiX : i ∈ X := by tauto
      have := h i ⟨Or.inl (Or.inl hiX), by tauto⟩
      simpa [hiX] using this
    · rintro h i ⟨hi, hiUF⟩
      have hiX : i ∈ X := by tauto
      simpa [hiX] using h i ⟨Or.inl hiX, by tauto⟩
  simp only [hcond]
  split_ifs with hc
  · refine Fintype.sum_equiv (regEquivOfEq heq) _ _ fun z ↦ ?_
    have hg : ∀ c : Reg loc (X ∪ U), restr h₂ (glue c z) =
        glue (restr Finset.subset_union_right c) (regEquivOfEq heq z) := fun c ↦ by
      funext i
      have hi := i.2
      simp only [Finset.mem_union] at hi
      by_cases hiU : (i : σ) ∈ U
      · simp [restr, glue, hiU, Finset.restrict₂]
      · have hiX : (i : σ) ∉ X := fun hX ↦ hXF' hX (by tauto)
        simp [restr, glue, hiU, hiX, Finset.restrict₂]
    rw [hg, hg]
  · simp

/-- `(N ⊗ 1)^̂z = N^̂z ⊗ 1` for Hermitian `N`. -/
theorem hatPow_extendId (h : S ⊆ T) {M : Matrix (Reg loc S) (Reg loc S) ℂ} (hM : M.IsHermitian)
    (z : ℂ) : hatPow (extendId h M) z = extendId h (hatPow M z) := by
  rw [hatPow_eq (isHermitian_extendId h hM), specFun_extendId, hatPow_eq hM]

omit [∀ i, DecidableEq (loc i)] in
/-- Marginals of a faithful state are faithful. -/
theorem posDef_ptrace (h : S ⊆ T) [Nonempty (Reg loc (T \ S))]
    {M : Matrix (Reg loc T) (Reg loc T) ℂ} (hM : M.PosDef) : (ptrace h M).PosDef := by
  classical
  obtain ⟨z₀⟩ := ‹Nonempty (Reg loc (T \ S))›
  rw [ptrace_eq_sum_conj, ← Finset.add_sum_erase _ _ (Finset.mem_univ z₀)]
  refine (hM.conjTranspose_mul_mul_same fun x y hxy ↦ ?_).add_posSemidef
    (posSemidef_sum _ fun z _ ↦ hM.posSemidef.conjTranspose_mul_mul_same _)
  simpa [mulVec_mulVec, sliceIsometry_conjTranspose_mul_self h] using
    congrArg ((sliceIsometry ℂ z₀)ᴴ *ᵥ ·) hxy

end Region

section Faithful

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- `ρ ≤ c M` with `ρ > 0`, `c > 0` forces `M > 0`. -/
theorem posDef_of_le_smul {ρ M : Matrix n n ℂ} (hρ : ρ.PosDef) {c : ℝ} (hc : 0 < c)
    (h : ρ ≤ (c : ℂ) • M) : M.PosDef := by
  have h1 : ((c : ℂ) • M).PosDef := by
    simpa using hρ.add_posSemidef (le_iff.1 h)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e : (c : ℂ)⁻¹ • ((c : ℂ) • M) = M := by rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
  exact e ▸ h1.smul (a := (c : ℂ)⁻¹) (by simpa using (Complex.zero_lt_real.2 (inv_pos.2 hc)))

/-- `Re Tr(N log N) = -S(N)`. -/
theorem re_trace_mul_log {N : Matrix n n ℂ} (hN : N.IsHermitian) :
    (N * specFun hN (fun t ↦ (Real.log t : ℂ))).trace.re = -Arealaw.vonNeumann hN := by
  rw [show N * specFun hN (fun t ↦ (Real.log t : ℂ)) =
      specFun hN (fun t ↦ (t : ℂ)) * specFun hN (fun t ↦ (Real.log t : ℂ)) by
    rw [specFun_ofReal], specFun_mul, trace_specFun, Arealaw.vonNeumann_eq_H, Arealaw.H,
    Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.mul_apply, Real.negMulLog, neg_mul, neg_neg]
  norm_cast

end Faithful

end Conditional

open Arealaw Matrix Conditional

/-- D5.12.1–10, the faithful case of **Lemma 5.2** in Hilbert–Schmidt form. Universal `C`
(`C = 4/π`) such that for every faithful density matrix `ρ_f` on `xUF` and real `u`,
`‖(ρ̂_U^{-iu} ρ̂_{xU}^{iu} − ρ̂_{UF}^{-iu} ρ̂_{xUF}^{iu}) √ρ_f‖₂ ≤ C |sinh πu| 𝓡_η`,
`η = I(x:F|U)_{ρ_f}`, `d = dim x`. -/
theorem lemma_5_2_faithful : Lemma_5_2_faithful := by
  refine ⟨4 / π, by positivity, ?_⟩
  intro σ _ loc _ _ T X U F hX hU hF hT hXU hXF hUF ρ hρ u
  subst hT
  have hXU' : X ∪ U ⊆ X ∪ U ∪ F := Finset.union_subset hX hU
  have hUF' : U ∪ F ⊆ X ∪ U ∪ F := Finset.union_subset hU hF
  have hU2 : U ⊆ X ∪ U := Finset.subset_union_right
  have hne : Nonempty (Reg loc (X ∪ U ∪ F)) := by
    by_contra hc
    have h1 := ρ.tr_eq_one
    rw [not_nonempty_iff] at hc
    simp [Matrix.trace] at h1
  obtain ⟨w₀⟩ := hne
  have : Nonempty (Reg loc ((X ∪ U ∪ F) \ (X ∪ U))) := ⟨restr Finset.sdiff_subset w₀⟩
  set d := Fintype.card (Reg loc X)
  have hd : 1 ≤ d := Fintype.card_pos_iff.2 ⟨restr hX w₀⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have card1 : Fintype.card (Reg loc ((X ∪ U ∪ F) \ (U ∪ F))) = d :=
    Fintype.card_congr (regEquivOfEq (by
      ext i; simp only [Finset.mem_sdiff, Finset.mem_union]
      have h1 : i ∈ X → i ∉ U := fun h ↦ Finset.disjoint_left.1 hXU h
      have h2 : i ∈ X → i ∉ F := fun h ↦ Finset.disjoint_left.1 hXF h
      tauto))
  have card2 : Fintype.card (Reg loc ((X ∪ U) \ U)) = d :=
    Fintype.card_congr (regEquivOfEq (by
      ext i; simp only [Finset.mem_sdiff, Finset.mem_union]
      have h1 : i ∈ X → i ∉ U := fun h ↦ Finset.disjoint_left.1 hXU h
      tauto))
  -- D5.12.1: `ρ_f`, `ρ_s = ρ_{xU}`, `M_f = I ⊗ ρ_{UF}` (`σ_f = M_f / d`), `M_s = I ⊗ ρ_U`.
  set ρs := ptrace hXU' ρ.M
  set Mf := extendId hUF' (ptrace hUF' ρ.M)
  set Ms := extendId hU2 (ptrace hU ρ.M)
  have hρs : ρs.PosDef := posDef_ptrace hXU' hρ
  -- D5.14.1: `ρ_f ≤ d (I_x ⊗ ρ_{UF})`, D5.2.1 with `UF` for `U`.
  have hdomf : ρ.M ≤ (d : ℂ) • Mf := card1 ▸ step_5_2_1 hUF' hρ.posSemidef
  have hdoms : ρs ≤ (d : ℂ) • Ms := by
    have h := step_5_2_1 hU2 hρs.posSemidef
    rwa [card2, ptrace_ptrace] at h
  have hMf := posDef_of_le_smul hρ hd0 hdomf
  have hMs := posDef_of_le_smul hρs hd0 hdoms
  let J : Matrix (Reg loc (X ∪ U)) (Reg loc (X ∪ U)) ℂ →ₐ[ℂ]
      Matrix (Reg loc (X ∪ U ∪ F)) (Reg loc (X ∪ U ∪ F)) ℂ :=
    AlgHom.ofLinearMap ⟨⟨extendId hXU', extendId_add hXU'⟩, extendId_smul hXU'⟩
      (extendId_one hXU') (extendId_mul hXU')
  have hJ : ∀ Y, J Yᴴ = (J Y)ᴴ := extendId_conjTranspose hXU'
  have hJρ : ∀ Y, (ρ.M * J Y).trace = (ρs * Y).trace := fun Y ↦ (trace_ptrace_mul hXU' _ _).symm
  -- D5.12.3: `Tr_F σ_f = σ_s`.
  have hJM : ∀ Y, (Mf * J Y).trace = (Ms * Y).trace := fun Y ↦ by
    change (Mf * extendId hXU' Y).trace = _
    rw [← trace_ptrace_mul, ptrace_extendId_union rfl hXF hXU' hUF', ptrace_ptrace]
  have htr : ρ.M.trace.re = 1 := ρ.tr_eq_one
  have hMs1 : Ms.trace.re = d := by
    rw [trace_extendId, card2, trace_ptrace, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, htr,
      mul_one]
  have key := step_5_12_10 hρ hρs hJ hJρ hMf hMs hJM hd hdomf htr hMs1 u
  -- D5.13.4: the four entropies give `I(x:F|U)`.
  have hη : ((ρ.M * specFun hρ.1 (fun t ↦ (Real.log t : ℂ))).trace -
      (ρ.M * specFun hMf.1 (fun t ↦ (Real.log t : ℂ))).trace -
      (ρs * specFun hρs.1 (fun t ↦ (Real.log t : ℂ))).trace +
      (ρs * specFun hMs.1 (fun t ↦ (Real.log t : ℂ))).trace).re =
      condMutualInfo ρ.toSubState hX hU hF := by
    have hUF'' := isHermitian_ptrace hUF' hρ.1
    have hU'' := isHermitian_ptrace hU hρ.1
    rw [show specFun hMf.1 (fun t ↦ (Real.log t : ℂ)) = _ from specFun_extendId hUF' hUF'' _,
      show specFun hMs.1 (fun t ↦ (Real.log t : ℂ)) = _ from specFun_extendId hU2 hU'' _,
      ← trace_ptrace_mul, ← trace_ptrace_mul, ptrace_ptrace]
    simp only [Complex.add_re, Complex.sub_re, re_trace_mul_log]
    change -ρ.toSubState.entropy - -ρ.toSubState.regionEntropy hUF' -
      -ρ.toSubState.regionEntropy hXU' + -ρ.toSubState.regionEntropy hU = _
    rw [condMutualInfo, SubState.regionEntropy_self]
    ring
  -- D5.12.10: `A^{-iu} a₀ = σ_f^{-iu} ρ_f^{iu} √ρ_f`,
  -- `V B^{-iu} b₀ = (σ_s^{-iu} ρ_s^{iu} ⊗ I) √ρ_f`; the Hilbert–Schmidt norm of the frozen `W`.
  have hW : (J (hatPow Ms (-(u * Complex.I)) * hatPow ρs (u * Complex.I)) -
      hatPow Mf (-(u * Complex.I)) * hatPow ρ.M (u * Complex.I)) * hatPow ρ.M (1 / 2) =
      (extendId hU (hatPow (ptrace hU ρ.M) (-(u * Complex.I))) *
          extendId hXU' (hatPow ρs (u * Complex.I)) -
        extendId hUF' (hatPow (ptrace hUF' ρ.M) (-(u * Complex.I))) *
          extendId (Finset.union_subset hXU' hF)
            (hatPow (ptrace (Finset.union_subset hXU' hF) ρ.M) (u * Complex.I))) *
        CFC.sqrt ρ.M := by
    rw [ptrace_self, extendId_self, hatPow_half_of_posDef hρ,
      hatPow_extendId hU2 (isHermitian_ptrace hU hρ.1),
      hatPow_extendId hUF' (isHermitian_ptrace hUF' hρ.1)]
    change (extendId hXU' (_ * _) - _) * _ = _
    rw [extendId_mul, Arealaw.extendId_extendId]
  rw [hη] at key
  refine le_of_eq_of_le ?_ key
  rw [norm_hs, hW]

end AreaLaw
