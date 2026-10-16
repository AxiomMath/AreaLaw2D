/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from QICLean, file `QICLean/Representation/ReplicaTransport/CoherentLog.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (coherent-average section).
-/
import OpenAI.ReplicaTransportSetup
import OpenAI.SymmetricProjection

/-!
# Coherent averages on the symmetric tensor sector

This is the coherent-average section of QICLean's logarithmic passage from a rank-one pin to
every symmetric state.  It constructs the coherent average, proves its resolution of the
symmetric projector, and relates its trace pairing to the real coherent integral.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The coherent-state vector `U e_a` is continuous in `U`. -/
theorem continuous_coherentVec (a : Ω) :
    Continuous fun U : unitaryGroup Ω ℂ => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1 := by
  refine continuous_pi fun x => ?_
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun y _ => (continuous_unitary_apply Ω _ _).mul continuous_const

omit [Fintype Ω] [DecidableEq Ω] in
/-- The coherent projector `P_{θ,k}` depends continuously on `θ`. -/
theorem continuous_coherentProj {X : Type*} [TopologicalSpace X] (k : ℕ) {θ : X → Ω → ℂ}
    (hθ : Continuous θ) : Continuous fun x => coherentProj k (θ x) := by
  refine continuous_pi fun y => continuous_pi fun z => ?_
  simp only [coherentProj, vecMulVec_apply, tensorVec, Pi.star_apply, star_prod]
  fun_prop

/-- The integrand of a coherent average is Haar integrable. -/
theorem integrable_smul_coherentProj (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    Integrable (fun U : unitaryGroup Ω ℂ => (f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) : ℂ) •
      coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) (unitaryHaar Ω) := by
  exact ((Complex.continuous_ofReal.comp (hf.comp (continuous_coherentVec a))).smul
    (continuous_coherentProj k (continuous_coherentVec a))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The letter counts of a word of length `k`. -/
def letterCount (k : ℕ) (x : Fin k → Ω) : Ω → Fin (k + 1) := fun c =>
  ⟨(Finset.univ.filter fun j => x j = c).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

omit [Fintype Ω] in
/-- Two words with the same letter counts differ by a permutation of the positions. -/
theorem exists_perm_of_letterCount_eq {k : ℕ} {x y : Fin k → Ω}
    (h : letterCount k x = letterCount k y) : ∃ σ : Equiv.Perm (Fin k), y ∘ σ = x := by
  have e : ∀ c, {j // x j = c} ≃ {j // y j = c} := fun c => Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact congrArg Fin.val (congrFun h c))
  exact ⟨Equiv.ofFiberEquiv e, funext fun j => Equiv.ofFiberEquiv_map e j⟩

/-- A symmetric vector is invariant under permuting the positions of its argument. -/
theorem apply_comp_of_mem_invariantSubspace {k : ℕ} {v : (Fin k → Ω) → ℂ}
    (hv : v ∈ invariantSubspace (copyPerm Ω k)) (x : Fin k → Ω) (σ : Equiv.Perm (Fin k)) :
    v (x ∘ σ) = v x := by
  have := congrFun (hv σ) x
  rw [permOp_mulVec, Function.comp_apply, ← map_inv] at this
  rw [show x ∘ σ = copyPerm Ω k σ⁻¹ x from funext fun j => by rw [copyPerm_apply, inv_inv]; rfl]
  exact this

/-- `D_k ≤ (k + 1)^{dim}`: a symmetric vector is determined by its values on one word of each
letter-count profile. -/
theorem symDim_le (k : ℕ) : symDim Ω k ≤ (k + 1) ^ Fintype.card Ω := by
  classical
  let R := Set.range (letterCount (Ω := Ω) k)
  let rep : R → (Fin k → Ω) := fun c => c.2.choose
  let L : invariantSubspace (copyPerm Ω k) →ₗ[ℂ] (R → ℂ) :=
    { toFun := fun v c => (v : (Fin k → Ω) → ℂ) (rep c)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    ext x
    let c : R := ⟨letterCount k x, x, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_perm_of_letterCount_eq (c.2.choose_spec)
    have h0 : (v : (Fin k → Ω) → ℂ) (rep c) = 0 := congrFun hv c
    rw [show rep c = x ∘ σ from hσ.symm, apply_comp_of_mem_invariantSubspace v.2] at h0
    simpa using h0
  calc symDim Ω k ≤ Module.finrank ℂ (R → ℂ) := LinearMap.finrank_le_finrank_of_injective hL
    _ = Fintype.card R := Module.finrank_fintype_fun_eq_card ℂ
    _ ≤ Fintype.card (Ω → Fin (k + 1)) := Fintype.card_subtype_le _
    _ = (k + 1) ^ Fintype.card Ω := by simp

/-- The symmetric projector is idempotent. -/
theorem symProj_mul_self (k : ℕ) :
    symProj (copyPerm Ω k) * symProj (copyPerm Ω k) = symProj (copyPerm Ω k) := by
  nth_rewrite 1 [symProj]
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [permOp_mul_symProj]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

/-- `Tr Π_k = D_k`. -/
theorem trace_symProj (k : ℕ) : (symProj (copyPerm Ω k)).trace = symDim Ω k := by
  have hR : LinearMap.range (Matrix.toLin' (symProj (copyPerm Ω k))) =
      invariantSubspace (copyPerm Ω k) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [Matrix.toLin'_apply]
      exact symProj_mulVec_mem _ v
    · intro v hv
      exact ⟨v, by rw [Matrix.toLin'_apply]; exact symProj_mulVec_of_mem _ hv⟩
  rw [trace_eq_finrank_range_of_mul_self (symProj_mul_self k), hR]

/-- `D_k ≥ 1`: the product vector `e_a^{⊗k}` is symmetric and nonzero. -/
theorem symDim_pos (k : ℕ) (a : Ω) : 0 < symDim Ω k := by
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨tensorVec k (Pi.single a 1), tensorVec_mem_symmetricSubspace _⟩, fun h => ?_⟩
  have := congrFun (congrArg Subtype.val h) (fun _ => a)
  simp [tensorVec] at this

/-- The coherent average `𝒬_k(f) = D_k ∫ f(θ) P_{θ,k} dθ` (`06-transport.tex` line 523). -/
def coherentAverage (k : ℕ) (a : Ω) (f : (Ω → ℂ) → ℝ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  (symDim Ω k : ℂ) • ∫ U, (f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) : ℂ) •
    coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ∂(unitaryHaar Ω)

/-- Tracing a coherent average against `ρ` gives the coherent integral. -/
theorem trace_mul_coherentAverage (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) :
    (ρ * coherentAverage k a f).trace.re = realCoherentIntegral k a ρ f := by
  have hF := integrable_smul_coherentProj k a hf
  let L : Matrix (Fin k → Ω) (Fin k → Ω) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap _ ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ ρ)
  have hL : ∀ M, L M = (ρ * M).trace := fun M => rfl
  have hint : Integrable (fun U : unitaryGroup Ω ℂ => L ((f ((U : Matrix Ω Ω ℂ) *ᵥ
      Pi.single a 1) : ℂ) • coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)))
      (unitaryHaar Ω) := L.integrable_comp hF
  rw [realCoherentIntegral, coherentAverage, mul_smul_comm, trace_smul, ← hL,
    ← L.integral_comp_comm hF, smul_eq_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  congr 1
  rw [← RCLike.re_to_complex, ← integral_re hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [hL, mul_smul_comm, trace_smul, smul_eq_mul, RCLike.re_to_complex,
    Complex.re_ofReal_mul]

/-- **Coherent-state resolution** in the form `𝒬_k(1) = Π_k`. -/
theorem coherentAverage_one (k : ℕ) (a : Ω) :
    coherentAverage k a (fun _ => 1) = symProj (copyPerm Ω k) := by
  have hD : (symDim Ω k : ℂ) ≠ 0 := by exact_mod_cast (symDim_pos k a).ne'
  have hF := integrable_smul_coherentProj k a (f := fun _ => 1) continuous_const
  ext x y
  let L : Matrix (Fin k → Ω) (Fin k → Ω) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ x y)
  have hL : ∀ M, L M = M x y := fun M => rfl
  have hres := congrFun (congrFun (unitaryTwirl_coherentProj (k := k) a) x) y
  rw [trace_symProj] at hres
  rw [coherentAverage, Matrix.smul_apply, ← hL (∫ U, _ ∂(unitaryHaar Ω)), ← L.integral_comp_comm hF]
  simp only [hL, Complex.ofReal_one, one_smul, coherentProj_mulVec]
  change _ * unitaryTwirl (coherentProj k (Pi.single a 1)) x y = _
  rw [hres, Matrix.smul_apply, smul_eq_mul]
  let z : ℂ := symProj (copyPerm Ω k) x y
  change (symDim Ω k : ℂ) * ((symDim Ω k : ℂ)⁻¹ * z) = z
  have hcancel : (symDim Ω k : ℂ) * (symDim Ω k : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hD
  calc
    _ = ((symDim Ω k : ℂ) * (symDim Ω k : ℂ)⁻¹) * z := by ring
    _ = z := by rw [hcancel]; ring

/-- The coherent measure of a state on `𝒮_k` has total mass one. -/
theorem realCoherentIntegral_one {k : ℕ} (a : Ω) {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (htr : ρ.trace = 1) (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    realCoherentIntegral k a ρ (fun _ => 1) = 1 := by
  rw [← trace_mul_coherentAverage k a continuous_const, coherentAverage_one, trace_mul_comm, hsym,
    htr, Complex.one_re]

/-- The coherent integrand of a continuous function is Haar integrable. -/
theorem integrable_realCoherentIntegral_integrand (k : ℕ) (a : Ω)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) {g : (Ω → ℂ) → ℝ} (hg : Continuous g) :
    Integrable (fun U : unitaryGroup Ω ℂ => g ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) *
      (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re) (unitaryHaar Ω) := by
  exact ((hg.comp (continuous_coherentVec a)).mul (Complex.continuous_re.comp
    ((continuous_const.mul (continuous_coherentProj k (continuous_coherentVec a))).matrix_trace))
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The coherent integral against a state on `𝒮_k` is affine in the integrand. -/
theorem realCoherentIntegral_affine {k : ℕ} (a : Ω) {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (htr : ρ.trace = 1) (hsym : symProj (copyPerm Ω k) * ρ = ρ) {F : (Ω → ℂ) → ℝ}
    (hF : Continuous F) (α β : ℝ) :
    realCoherentIntegral k a ρ (fun θ => α + β * F θ) = α + β * realCoherentIntegral k a ρ F := by
  have h1 := realCoherentIntegral_one a htr hsym
  unfold realCoherentIntegral at h1 ⊢
  beta_reduce at h1 ⊢
  set w : unitaryGroup Ω ℂ → ℝ := fun U =>
    (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re with hw
  have hI : ∫ U, (α + β * F ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) * w U ∂(unitaryHaar Ω) =
      α * ∫ U, 1 * w U ∂(unitaryHaar Ω) +
        β * ∫ U, F ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) * w U ∂(unitaryHaar Ω) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((integrable_realCoherentIntegral_integrand k a ρ continuous_const).const_mul α)
      ((integrable_realCoherentIntegral_integrand k a ρ hF).const_mul β)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U => by ring)
  rw [hI]
  linear_combination α * h1

end TensorPower
