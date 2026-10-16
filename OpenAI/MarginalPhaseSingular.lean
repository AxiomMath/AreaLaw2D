/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Entropy/MarginalPhaseSingular.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.MarginalPhaseLimit

/-! # The marginal-phase comparison for arbitrary states -/

open Filter Topology
open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.MarginalPhase

open _root_.Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U]
  [DecidableEq U] [Fintype F] [DecidableEq F]

/-- Tensoring with `I_X` on the left, as a linear map. -/
def oneKron : Matrix U U ℂ →ₗ[ℂ] Matrix (X × U) (X × U) ℂ where
  toFun M := (1 : Matrix X X ℂ) ⊗ₖ M
  map_add' A B := kronecker_add _ _ _
  map_smul' c A := by rw [kronecker_smul]; rfl

/-- The embedding `W ↦ W ⊗ I_F`, as a linear map. -/
def embedFLin : Matrix (X × U) (X × U) ℂ →ₗ[ℂ]
    Matrix (X × (U × F)) (X × (U × F)) ℂ where
  toFun := embedF
  map_add' := embedF_add
  map_smul' := embedF_smul

/-- The kernel-completed phase difference. -/
def phaseDifference
    {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
    (hρ : ρ.PosSemidef) (u : ℝ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  embedF (((1 : Matrix X X ℂ) ⊗ₖ
      hatPhase (posSemidef_marginalU hρ).1 (-u)) *
      hatPhase (posSemidef_marginalXU hρ).1 u) -
    ((1 : Matrix X X ℂ) ⊗ₖ
      hatPhase (posSemidef_marginalUF hρ).1 (-u)) *
      hatPhase hρ.1 u

/-- The affine functions of the approximation on the state and its marginals. -/
def affF (X U F : Type*) [Fintype X] [Fintype U] [Fintype F]
    (c : ℝ) (ε t : ℝ) : ℝ :=
  (1 - ε) * t + ε / Fintype.card (X × (U × F)) * c

/-- The phase family `t ↦ (affF c ε t)^z` in a fixed eigenbasis. -/
def phaseFam {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (g : ℝ → ℝ)
    (z : ℂ) : Matrix n n ℂ :=
  spectralFun hM.eigenvectorUnitary
    (fun k => ((g (hM.eigenvalues k) : ℝ) : ℂ) ^ z)

section Bound

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
  (hρ : ρ.PosSemidef)

/-- The faithful comparison at `ρ_ε`, written in the original eigenbases. -/
theorem norm_approx_le [Nonempty X] [Nonempty U] [Nonempty F]
    (htr : ρ.trace = 1) (u : ℝ) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ‖(WithLp.toLp 2 (vec
        ((embedF (((1 : Matrix X X ℂ) ⊗ₖ
            phaseFam (posSemidef_marginalU hρ).1
              (affF X U F (Fintype.card F * Fintype.card X) ε)
              (-(u * Complex.I))) *
            phaseFam (posSemidef_marginalXU hρ).1
              (affF X U F (Fintype.card F) ε)
              (u * Complex.I)) -
          ((1 : Matrix X X ℂ) ⊗ₖ
            phaseFam (posSemidef_marginalUF hρ).1
              (affF X U F (Fintype.card X) ε)
              (-(u * Complex.I))) *
            phaseFam hρ.1 (affF X U F 1 ε)
              (u * Complex.I)) *
          spectralFun hρ.1.eigenvectorUnitary
            (fun k => ((affF X U F 1 ε (hρ.1.eigenvalues k) ^
              (1 / 2 : ℝ) : ℝ) : ℂ)))) :
        EuclideanSpace ℂ ((X × (U × F)) × (X × (U × F))))‖ ≤
      2 * |Real.sinh (Real.pi * u)| * phaseRate (Fintype.card X)
        (condMutualInfo (approx ρ ε)
          (posDef_approx hρ h0 h1).posSemidef) := by
  have hpd := posDef_approx hρ h0 h1
  have h := norm_phaseDifference_le_of_posDef hpd
    (trace_approx htr ε) u
  rw [cpowSpec_of_eq_cfc (posDef_marginalU (F := F) hpd)
      (posSemidef_marginalU hρ).1 _ (marginalU_approx hρ ε),
    cpowSpec_of_eq_cfc (posDef_marginalXU (F := F) hpd)
      (posSemidef_marginalXU hρ).1 _ (marginalXU_approx hρ ε),
    cpowSpec_of_eq_cfc (posDef_marginalUF hpd)
      (posSemidef_marginalUF hρ).1 _ (marginalUF_approx hρ ε),
    cpowSpec_of_eq_cfc hpd hρ.1 _ (approx_eq_cfc hρ.1 ε),
    rpowSpec_of_eq_cfc hpd hρ.1 _ (approx_eq_cfc hρ.1 ε)] at h
  convert h using 8 <;> simp [phaseFam, affF, approxW, mul_assoc]

end Bound

section Limits

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem tendsto_affF (c t : ℝ) :
    Tendsto (fun ε => affF X U F c ε t) (𝓝[>] 0) (𝓝 t) := by
  have hc : ContinuousAt (fun ε => affF X U F c ε t) 0 := by
    unfold affF
    fun_prop
  have ht := hc.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [affF] using ht

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem affF_zero (c ε : ℝ) :
    affF X U F c ε 0 =
      ε / Fintype.card (X × (U × F)) * c := by
  simp [affF]

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem affF_pos [Nonempty X] [Nonempty U] [Nonempty F]
    {c ε t : ℝ} (hc : 0 < c) (h0 : 0 < ε) (h1 : ε ≤ 1)
    (ht : 0 ≤ t) : 0 < affF X U F c ε t := by
  unfold affF
  have : (0 : ℝ) < Fintype.card (X × (U × F)) :=
    Nat.cast_pos.2 Fintype.card_pos
  have : 0 ≤ (1 - ε) * t := mul_nonneg (by linarith) ht
  positivity

theorem tendsto_cpow_affF {c t : ℝ} (ht : 0 < t) (z : ℂ) :
    Tendsto (fun ε => ((affF X U F c ε t : ℝ) : ℂ) ^ z)
      (𝓝[>] 0) (𝓝 ((t : ℂ) ^ z)) :=
  ((Complex.continuousAt_ofReal_cpow_const t z
    (Or.inr ht.ne')).tendsto).comp (tendsto_affF c t)

theorem tendsto_rpow_affF (c t : ℝ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun ε =>
      ((affF X U F c ε t ^ s : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((t ^ s : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((Real.continuousAt_rpow_const t s
      (Or.inr hs.le)).tendsto.comp (tendsto_affF c t))

end Limits

section Main

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
  (hρ : ρ.PosSemidef)

theorem hatPhase_eq_spectralFun {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (v : ℝ) (z : ℂ) (hz : z = (v : ℂ) * Complex.I) :
    spectralFun hM.eigenvectorUnitary
        (fun k => if hM.eigenvalues k = 0 then 1 else
          ((hM.eigenvalues k : ℝ) : ℂ) ^ z) =
      hatPhase hM v := by
  rw [hatPhase, hz]

theorem sqrtSpec_eq_rpow {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    sqrtSpec hM = spectralFun hM.eigenvectorUnitary
      (fun k => ((hM.eigenvalues k ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
  rw [sqrtSpec]
  congr 1
  funext k
  rw [Real.sqrt_eq_rpow]

theorem norm_cpow_imag_eq_one {x : ℝ} (hx : 0 < x) (v : ℝ) :
    ‖(x : ℂ) ^ ((v : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- The phase family converges after multiplication by a family whose limit is
annihilated by the lifted kernel projection. -/
theorem tendsto_phaseFam_mul [Nonempty X] [Nonempty U] [Nonempty F]
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {M : Matrix n n ℂ} (hM : M.PosSemidef)
    {c : ℝ} (hc : 0 < c) (v : ℝ)
    (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {Y : ℝ → Matrix m m ℂ} {Y₀ : Matrix m m ℂ}
    (hY : Tendsto Y (𝓝[>] 0) (𝓝 Y₀))
    (hK : L (kerProj hM.1) * Y₀ = 0) :
    Tendsto (fun ε => L (phaseFam hM.1
      (affF X U F c ε) ((v : ℂ) * Complex.I)) * Y ε)
      (𝓝[>] 0) (𝓝 (L (hatPhase hM.1 v) * Y₀)) := by
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT
      (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact ⟨hε.1, hε.2.le⟩
  have h := tendsto_lift_spectralFun_mul
    hM.1.eigenvectorUnitary hM.1.eigenvalues
    (fun ε k => ((affF X U F c ε (hM.1.eigenvalues k) : ℝ) : ℂ) ^
      ((v : ℂ) * Complex.I))
    (fun k => ((hM.1.eigenvalues k : ℝ) : ℂ) ^
      ((v : ℂ) * Complex.I))
    (fun ε => ((affF X U F c ε 0 : ℝ) : ℂ) ^
      ((v : ℂ) * Complex.I)) L Y Y₀
    (fun k hk => tendsto_cpow_affF
      (lt_of_le_of_ne (hM.eigenvalues_nonneg k) (Ne.symm hk)) _)
    (Eventually.of_forall fun ε k hk => by simp only [hk])
    (by
      filter_upwards [hpos] with ε hε
      exact norm_cpow_imag_eq_one
        (affF_pos hc hε.1 hε.2 le_rfl) v) hY hK
  exact h

/-- Marginal-phase comparison for an arbitrary positive-semidefinite density matrix. -/
theorem norm_phaseDifference_le (htr : ρ.trace = 1) (u : ℝ) :
    ‖(WithLp.toLp 2 (vec (phaseDifference hρ u * sqrtSpec hρ.1)) :
        EuclideanSpace ℂ ((X × (U × F)) × (X × (U × F))))‖ ≤
      2 * |Real.sinh (Real.pi * u)| * phaseRate (Fintype.card X)
        (condMutualInfo ρ hρ) := by
  have hne : Nonempty (X × (U × F)) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Matrix.trace] at htr
  have : Nonempty X := ⟨hne.some.1⟩
  have : Nonempty U := ⟨hne.some.2.1⟩
  have : Nonempty F := ⟨hne.some.2.2⟩
  have hcX : (0 : ℝ) < Fintype.card X :=
    Nat.cast_pos.2 Fintype.card_pos
  have hcF : (0 : ℝ) < Fintype.card F :=
    Nat.cast_pos.2 Fintype.card_pos
  set hρH := hρ.1
  set hsP := posSemidef_marginalXU hρ
  set hUP := posSemidef_marginalU hρ
  set hUFP := posSemidef_marginalUF hρ
  have e : -((u : ℂ) * Complex.I) =
      ((-u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  set P : ℝ → Matrix (X × (U × F)) (X × (U × F)) ℂ :=
    fun ε => spectralFun hρH.eigenvectorUnitary
      (fun k => ((affF X U F 1 ε (hρH.eigenvalues k) ^
        (1 / 2 : ℝ) : ℝ) : ℂ))
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT
      (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact ⟨hε.1, hε.2.le⟩
  have hP : Tendsto P (𝓝[>] 0) (𝓝 (sqrtSpec hρH)) := by
    rw [sqrtSpec_eq_rpow]
    exact tendsto_spectralFun _ fun k =>
      tendsto_rpow_affF 1 _ _ (by norm_num)
  have hQP : Tendsto (fun ε =>
      phaseFam hρH (affF X U F 1 ε)
        ((u : ℂ) * Complex.I) * P ε)
      (𝓝[>] 0) (𝓝 (hatPhase hρH u * sqrtSpec hρH)) := by
    rw [hatPhase, sqrtSpec, spectralFun_mul]
    simp only [phaseFam, P, spectralFun_mul]
    refine tendsto_spectralFun _ fun k => ?_
    simp only [Pi.mul_apply]
    by_cases hk : hρH.eigenvalues k = 0
    · simp only [hk, ite_true, Real.sqrt_zero, Complex.ofReal_zero,
        mul_zero]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h0 := tendsto_rpow_affF
        (X := X) (U := U) (F := F) 1 0 (1 / 2) (by norm_num)
      rw [Real.zero_rpow (by norm_num), Complex.ofReal_zero] at h0
      have h0' := tendsto_zero_iff_norm_tendsto_zero.1 h0
      refine h0'.congr' ?_
      filter_upwards [hpos] with ε hε
      rw [norm_mul,
        norm_cpow_imag_eq_one
          (affF_pos one_pos hε.1 hε.2 le_rfl), one_mul]
    · have hk' : 0 < hρH.eigenvalues k :=
        lt_of_le_of_ne (hρ.eigenvalues_nonneg k) (Ne.symm hk)
      simp only [hk, ite_false]
      rw [Real.sqrt_eq_rpow]
      exact (tendsto_cpow_affF hk' _).mul
        (tendsto_rpow_affF 1 _ _ (by norm_num))
  have hUF := tendsto_phaseFam_mul
    (X := X) (U := U) (F := F) hUFP
    (c := Fintype.card X) hcX (-u) oneKron hQP (by
      change ((1 : Matrix X X ℂ) ⊗ₖ kerProj hUFP.1) *
        (hatPhase hρH u * sqrtSpec hρH) = 0
      have hcomm : hatPhase hρH u * sqrtSpec hρH =
          sqrtSpec hρH * hatPhase hρH u := by
        rw [hatPhase, sqrtSpec, spectralFun_mul,
          spectralFun_mul, mul_comm]
      have h0 := one_kronecker_kerProj_mul_sqrtSpec hρ hUFP.1
      rw [hcomm, ← Matrix.mul_assoc]
      erw [h0]
      rw [Matrix.zero_mul])
  have hXU := tendsto_phaseFam_mul
    (X := X) (U := U) (F := F) hsP
    (c := Fintype.card F) hcF u
    (embedFLin (X := X) (U := U) (F := F)) hP
    (embedF_kerProj_mul_sqrtSpec hρ)
  have hU := tendsto_phaseFam_mul
    (X := X) (U := U) (F := F) hUP
    (c := Fintype.card F * Fintype.card X) (mul_pos hcF hcX)
    (-u) ((embedFLin (X := X) (U := U) (F := F)).comp oneKron)
    hXU (by
      change embedF ((1 : Matrix X X ℂ) ⊗ₖ kerProj hUP.1) *
        (embedF (hatPhase hsP.1 u) * sqrtSpec hρH) = 0
      rw [← Matrix.mul_assoc, embedF_mul]
      exact embedF_kerProj_hatPhase_mul_sqrtSpec hρ u)
  have hLHSmat := hU.sub hUF
  have hlimG :
      (embedFLin.comp oneKron) (hatPhase hUP.1 (-u)) *
          (embedFLin (hatPhase hsP.1 u) * sqrtSpec hρH) -
        oneKron (hatPhase hUFP.1 (-u)) *
          (hatPhase hρH u * sqrtSpec hρH) =
      phaseDifference hρ u * sqrtSpec hρH := by
    change embedF ((1 : Matrix X X ℂ) ⊗ₖ _) * (embedF _ * _) -
      ((1 : Matrix X X ℂ) ⊗ₖ _) * (_ * _) = _
    rw [phaseDifference, Matrix.sub_mul, ← embedF_mul,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hlimG] at hLHSmat
  set Ef : ℝ → ℝ := fun ε =>
    ∑ k, Real.negMulLog
        (affF X U F (Fintype.card F) ε (hsP.1.eigenvalues k)) +
      ∑ k, Real.negMulLog
        (affF X U F (Fintype.card X) ε (hUFP.1.eigenvalues k)) -
      ∑ k, Real.negMulLog
        (affF X U F (Fintype.card F * Fintype.card X) ε
          (hUP.1.eigenvalues k)) -
      ∑ k, Real.negMulLog
        (affF X U F 1 ε (hρH.eigenvalues k))
  have hEf : ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1),
      condMutualInfo (approx ρ ε)
        (posDef_approx hρ h0 h1).posSemidef = Ef ε := by
    intro ε h0 h1
    have hpd := posDef_approx hρ h0 h1
    have e1 := vonNeumann_of_eq_cfc
      (posSemidef_marginalXU hpd.posSemidef).1 hsP.1 _
      (marginalXU_approx hρ ε)
    have e2 := vonNeumann_of_eq_cfc
      (posSemidef_marginalUF hpd.posSemidef).1 hUFP.1 _
      (marginalUF_approx hρ ε)
    have e3 := vonNeumann_of_eq_cfc
      (posSemidef_marginalU hpd.posSemidef).1 hUP.1 _
      (marginalU_approx hρ ε)
    have e4 := vonNeumann_of_eq_cfc hpd.1 hρH _
      (approx_eq_cfc hρH ε)
    unfold condMutualInfo
    erw [e1, e2, e3, e4]
    simp only [Ef, affF, approxW, mul_one, mul_assoc]
  have hEf0 : Ef 0 = condMutualInfo ρ hρ := by
    simp only [Ef, affF, sub_zero, one_mul, zero_div, zero_mul,
      add_zero]
    change Arealaw.H hsP.1.eigenvalues +
        Arealaw.H hUFP.1.eigenvalues -
        Arealaw.H hUP.1.eigenvalues -
        Arealaw.H hρH.eigenvalues = condMutualInfo ρ hρ
    rw [← Arealaw.vonNeumann_eq_H hsP.1,
      ← Arealaw.vonNeumann_eq_H hUFP.1,
      ← Arealaw.vonNeumann_eq_H hUP.1,
      ← Arealaw.vonNeumann_eq_H hρH]
    have hXU : Arealaw.vonNeumann hsP.1 =
        Arealaw.vonNeumann
          ((hρ.submatrix assocE).traceRight.isHermitian) := by
      rfl
    have hUF : Arealaw.vonNeumann hUFP.1 =
        Arealaw.vonNeumann hρ.traceLeft.isHermitian := by
      rfl
    have hU : Arealaw.vonNeumann hUP.1 =
        Arealaw.vonNeumann
          ((hρ.submatrix assocE).traceRight.traceLeft.isHermitian) := by
      rfl
    have hfull : Arealaw.vonNeumann hρH =
        Arealaw.vonNeumann hρ.isHermitian := by
      rfl
    unfold condMutualInfo
    rw [hXU, hUF, hU, hfull]
  have hEfc : Tendsto Ef (𝓝[>] 0) (𝓝 (Ef 0)) := by
    have hc : Continuous Ef := by
      simp only [Ef, affF]
      have := Real.continuous_negMulLog
      fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hEfnn : ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1),
      0 ≤ Ef ε := by
    intro ε h0 h1
    rw [← hEf ε h0 h1,
      ← compression_logGap (posDef_approx hρ h0 h1)]
    exact (compression (posDef_approx hρ h0 h1)).logGap_nonneg
  have hη0 : 0 ≤ Ef 0 := by
    refine ge_of_tendsto hEfc ?_
    filter_upwards [hpos] with ε hε
    exact hEfnn ε hε.1 hε.2
  have hD : (1 : ℝ) ≤ Fintype.card X :=
    Nat.one_le_cast.2 Fintype.card_pos
  have hRHS := (tendsto_phaseRate hD hEfc hη0).const_mul
    (2 * |Real.sinh (Real.pi * u)|)
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(WithLp.toLp 2 (vec
        ((embedFLin.comp oneKron) (phaseFam hUP.1
            (affF X U F (Fintype.card F * Fintype.card X) ε)
            (((-u : ℝ) : ℂ) * Complex.I)) *
          (embedFLin (phaseFam hsP.1
              (affF X U F (Fintype.card F) ε)
              ((u : ℂ) * Complex.I)) * P ε) -
          oneKron (phaseFam hUFP.1
              (affF X U F (Fintype.card X) ε)
              (((-u : ℝ) : ℂ) * Complex.I)) *
          (phaseFam hρH (affF X U F 1 ε)
              ((u : ℂ) * Complex.I) * P ε))) :
        EuclideanSpace ℂ ((X × (U × F)) × (X × (U × F))))‖ ≤
        2 * |Real.sinh (Real.pi * u)| *
          phaseRate (Fintype.card X) (Ef ε) := by
    filter_upwards [hpos] with ε hε
    have hb := norm_approx_le hρ htr u hε.1 hε.2
    rw [hEf ε hε.1 hε.2, e] at hb
    convert hb using 4
    change embedF ((1 : Matrix X X ℂ) ⊗ₖ _) * (embedF _ * _) -
      ((1 : Matrix X X ℂ) ⊗ₖ _) * (_ * _) = _
    rw [Matrix.sub_mul, ← embedF_mul,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have hcont : Continuous fun
      M : Matrix (X × (U × F)) (X × (U × F)) ℂ =>
      ‖(WithLp.toLp 2 (vec M) :
        EuclideanSpace ℂ ((X × (U × F)) × (X × (U × F))))‖ := by
    refine continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp ?_)
    exact continuous_pi fun p =>
      (continuous_apply p.1).comp (continuous_apply p.2)
  have hLHS := (hcont.tendsto _).comp hLHSmat
  have hfinal := le_of_tendsto_of_tendsto hLHS hRHS hbound
  rwa [hEf0] at hfinal

end Main

section Purification

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem dotProduct_mulVec_eq_trace {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (θ : n → ℂ) :
    star θ ⬝ᵥ (M *ᵥ θ) =
      (M * vecMulVec θ (star θ)).trace := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

theorem norm_toLp_sq_eq_re {n : Type*} [Fintype n] (v : n → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 =
      (star v ⬝ᵥ v).re := by
  rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp,
    dotProduct_comm]
  rfl

/-- A purification norm equals the Hilbert--Schmidt norm against the marginal square root. -/
theorem norm_kronecker_one_mulVec {S : Type*} [Fintype S]
    [DecidableEq S] (θ : S × P → ℂ) (T : Matrix S S ℂ) :
    ‖(WithLp.toLp 2
        ((T ⊗ₖ (1 : Matrix P P ℂ)) *ᵥ θ) :
      EuclideanSpace ℂ (S × P))‖ =
      ‖(WithLp.toLp 2
          (vec (T * sqrtSpec
            ((posSemidef_vecMulVec_self_star θ).traceRight).1)) :
        EuclideanSpace ℂ (S × S))‖ := by
  set hρ := (posSemidef_vecMulVec_self_star θ).traceRight
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toLp_sq_eq_re, norm_toLp_sq_eq_re,
    star_vec_dotProduct_vec, star_mulVec_dotProduct, mulVec_mulVec,
    dotProduct_mulVec_eq_trace, conjTranspose_kronecker,
    conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
    trace_mul_comm, trace_mul_kron_one_right, conjTranspose_mul,
    sqrtSpec_conjTranspose]
  conv_rhs => rw [Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]
  erw [sqrtSpec_mul_self hρ]
  rw [trace_mul_comm, Matrix.mul_assoc]

/-- Marginal-phase comparison acting on an arbitrary purification vector. -/
theorem norm_phaseDifference_mulVec_le
    (θ : EuclideanSpace ℂ ((X × (U × F)) × P))
    (hθ : ‖θ‖ = 1) (u : ℝ) :
    ‖(WithLp.toLp 2
      ((phaseDifference
          (posSemidef_vecMulVec_self_star θ.ofLp).traceRight u ⊗ₖ
          (1 : Matrix P P ℂ)) *ᵥ θ.ofLp) :
      EuclideanSpace ℂ ((X × (U × F)) × P))‖ ≤
      2 * |Real.sinh (Real.pi * u)| * phaseRate (Fintype.card X)
        (condMutualInfo
          (Matrix.traceRight (vecMulVec θ.ofLp (star θ.ofLp)))
          (posSemidef_vecMulVec_self_star θ.ofLp).traceRight) := by
  set hρ := (posSemidef_vecMulVec_self_star θ.ofLp).traceRight
  have htr : (Matrix.traceRight
      (vecMulVec θ.ofLp (star θ.ofLp))).trace = 1 := by
    rw [traceRight_trace, trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hθ]
    simp
  rw [norm_kronecker_one_mulVec]
  exact norm_phaseDifference_le hρ htr u

end Purification

end Entropy.MarginalPhase

end
