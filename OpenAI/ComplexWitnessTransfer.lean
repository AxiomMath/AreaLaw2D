import OpenAI.PositiveConstraints
import OpenAI.Embedding

/-!
# Transferring complex matrix witnesses to an `RCLike` field

The canonical map from an `RCLike` field to `ℂ` is either an equivalence or has the real
numbers as its image.  In the latter case, entrywise real part sends Hermitian positive
semidefinite complex matrices to positive semidefinite matrices over the source field and is
contractive for the `L²` operator norm.  These facts let us transfer the existential witnesses
of Proposition 4.3 without rebuilding the complex-time spectral filter over the source field.
-/

namespace OpenAI

open Arealaw
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

namespace Matrix

variable {m n : Type*}

/-- Entrywise real part of a complex matrix, cast into an `RCLike` field. -/
noncomputable def realProjection (A : Matrix m n ℂ) : Matrix m n 𝕜 :=
  fun i j => (A i j).re

/-- Pull a complex matrix back across the canonical equivalence in the complex-like case. -/
noncomputable def complexPullback (hI : RCLike.im (RCLike.I : 𝕜) = 1)
    (A : Matrix m n ℂ) : Matrix m n 𝕜 :=
  A.map (RCLike.complexRingEquiv hI).symm

theorem complexPullback_map_toComplex (hI : RCLike.im (RCLike.I : 𝕜) = 1)
    (A : Matrix m n ℂ) :
    (complexPullback hI A).map (toComplex 𝕜) = A := by
  ext i j
  change toComplex 𝕜 ((RCLike.complexRingEquiv hI).symm (A i j)) = A i j
  rw [toComplex_apply, ← RCLike.complexRingEquiv_apply hI]
  exact (RCLike.complexRingEquiv hI).apply_symm_apply (A i j)

@[simp] theorem realProjection_apply (A : Matrix m n ℂ) (i : m) (j : n) :
    realProjection (𝕜 := 𝕜) A i j = (A i j).re := rfl

@[simp] theorem realProjection_zero :
    realProjection (𝕜 := 𝕜) (0 : Matrix m n ℂ) = 0 := by
  ext i j
  simp

@[simp] theorem realProjection_add (A B : Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) (A + B) = realProjection A + realProjection B := by
  ext i j
  simp

@[simp] theorem realProjection_sub (A B : Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) (A - B) = realProjection A - realProjection B := by
  ext i j
  simp

@[simp] theorem realProjection_real_smul (r : ℝ) (A : Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) (r • A) = r • realProjection A := by
  ext i j
  simp

@[simp] theorem realProjection_complex_ofReal_smul (r : ℝ) (A : Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) ((r : ℂ) • A) = (r : 𝕜) • realProjection A := by
  ext i j
  simp [smul_eq_mul]

@[simp] theorem realProjection_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    realProjection (𝕜 := 𝕜) (∑ i ∈ s, A i) = ∑ i ∈ s, realProjection (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha => simp [ha, *]

theorem map_toComplex_realProjection (A : Matrix m n ℂ) :
    (realProjection (𝕜 := 𝕜) A).map (toComplex 𝕜) =
      fun i j => ((A i j).re : ℂ) := by
  ext i j
  simp

theorem realProjection_map_toComplex (hI : (RCLike.I : 𝕜) = 0) (A : Matrix m n 𝕜) :
    realProjection (A.map (toComplex 𝕜)) = A := by
  ext i j
  rw [realProjection_apply, Matrix.map_apply, re_toComplex]
  rw [← RCLike.re_add_im (A i j), RCLike.im_eq_zero hI]
  simp

variable [Fintype n] [DecidableEq n]

@[simp] theorem realProjection_one :
    realProjection (𝕜 := 𝕜) (1 : Matrix n n ℂ) = 1 := by
  ext i j
  rw [realProjection_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem map_toComplex_realProjection_eq_average {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (realProjection (𝕜 := 𝕜) A).map (toComplex 𝕜) =
      (2 : ℝ)⁻¹ • (A + Aᵀ) := by
  ext i j
  rw [map_toComplex_realProjection]
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Complex.real_smul]
  have hij : star (A i j) = A j i := by
    have := congrFun (congrFun hA.eq j) i
    simpa using this
  rw [← hij]
  apply Complex.ext <;> simp
  ring

theorem eigenvalues_multiset_transpose {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Finset.univ.val.map hA.transpose.eigenvalues = Finset.univ.val.map hA.eigenvalues := by
  apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
  rw [Multiset.map_map, Multiset.map_map]
  calc
    Finset.univ.val.map (RCLike.ofReal ∘ hA.transpose.eigenvalues) =
        Aᵀ.charpoly.roots := hA.transpose.roots_charpoly_eq_eigenvalues.symm
    _ = A.charpoly.roots := by rw [Matrix.charpoly_transpose]
    _ = Finset.univ.val.map (RCLike.ofReal ∘ hA.eigenvalues) :=
      hA.roots_charpoly_eq_eigenvalues

theorem range_eigenvalues_transpose {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Set.range hA.transpose.eigenvalues = Set.range hA.eigenvalues := by
  ext x
  simpa using congrArg (x ∈ ·) (eigenvalues_multiset_transpose hA)

theorem l2_opNorm_transpose_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖Aᵀ‖ = ‖A‖ := by
  have h := nnnorm_eq_iSup_eigenvalues hA.transpose
  rw [range_eigenvalues_transpose hA, ← nnnorm_eq_iSup_eigenvalues hA,
    ENNReal.coe_inj] at h
  exact congrArg NNReal.toReal h

theorem PosSemidef.realProjection {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (realProjection (𝕜 := 𝕜) A).PosSemidef := by
  rw [← posSemidef_map_toComplex_iff]
  rw [map_toComplex_realProjection_eq_average hA.isHermitian]
  exact (hA.add hA.transpose).smul (by positivity)

theorem realProjection_mono {A B : Matrix n n ℂ} (hAB : A ≤ B) :
    realProjection (𝕜 := 𝕜) A ≤ realProjection B := by
  rw [Matrix.le_iff] at hAB ⊢
  rw [← realProjection_sub]
  exact PosSemidef.realProjection hAB

theorem realProjection_mulVec_eq_zero (hI : (RCLike.I : 𝕜) = 0)
    {A : Matrix n n ℂ} {v : n → 𝕜}
    (h : A *ᵥ (fun i => toComplex 𝕜 (v i)) = 0) :
    realProjection A *ᵥ v = 0 := by
  funext i
  apply (RCLike.realRingEquiv hI).injective
  have hi := congrFun h i
  have hre := congrArg Complex.re hi
  simpa [Matrix.mulVec, dotProduct, realProjection, map_sum, Complex.mul_re,
    RCLike.mul_re, RCLike.im_eq_zero hI] using hre

theorem norm_realProjection_le {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖realProjection (𝕜 := 𝕜) A‖ ≤ ‖A‖ := by
  rw [← norm_map_toComplex]
  rw [map_toComplex_realProjection_eq_average hA]
  rw [smul_add]
  calc
    ‖(2 : ℝ)⁻¹ • A + (2 : ℝ)⁻¹ • Aᵀ‖ ≤
        ‖(2 : ℝ)⁻¹ • A‖ + ‖(2 : ℝ)⁻¹ • Aᵀ‖ := norm_add_le _ _
    _ = ‖A‖ := by
      rw [norm_smul, norm_smul, l2_opNorm_transpose_of_isHermitian hA]
      rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
      ring

section Region

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {S T : Finset σ}

theorem realProjection_ptrace (h : S ⊆ T)
    (A : Matrix (Reg loc T) (Reg loc T) ℂ) :
    realProjection (𝕜 := 𝕜) (ptrace h A) = ptrace h (realProjection A) := by
  ext i j
  simp [realProjection, ptrace]

theorem realProjection_extendId (h : S ⊆ T)
    (A : Matrix (Reg loc S) (Reg loc S) ℂ) :
    realProjection (𝕜 := 𝕜) (extendId h A) = extendId h (realProjection A) := by
  ext i j
  simp only [realProjection_apply, extendId, Matrix.of_apply]
  split_ifs <;> simp

theorem realProjection_condExpect (h : S ⊆ T)
    (A : Matrix (Reg loc T) (Reg loc T) ℂ) :
    realProjection (𝕜 := 𝕜) (condExpect h A) = condExpect h (realProjection A) := by
  unfold condExpect
  rw [show (Fintype.card (Reg loc (T \ S)) : ℂ)⁻¹ =
      (((Fintype.card (Reg loc (T \ S)) : ℝ)⁻¹ : ℝ) : ℂ) by
        rw [Complex.ofReal_inv, Complex.ofReal_natCast]]
  rw [realProjection_complex_ofReal_smul, realProjection_extendId, realProjection_ptrace]
  congr 1
  rw [RCLike.ofReal_inv, RCLike.ofReal_natCast]

theorem IsSupportedOn.realProjection (h : S ⊆ T)
    {A : Matrix (Reg loc T) (Reg loc T) ℂ} (hA : IsSupportedOn h A) :
    IsSupportedOn h (realProjection (𝕜 := 𝕜) A) := by
  obtain ⟨B, rfl⟩ := hA
  exact ⟨Matrix.realProjection B, realProjection_extendId h B⟩

end Region

end Matrix

/-- A complex proof of Proposition 4.3 supplies witnesses over every `RCLike` field.

In the complex-like case the canonical embedding is an equivalence.  In the real-like case
we take entrywise real parts of the complex witnesses; the preceding lemmas show that all
five clauses of `PositiveReplacement` survive this projection. -/
theorem positiveReplacement_of_complex (q R : ℕ) (J Δ : ℝ) (p : ℕ)
    (hcomplex : PositiveReplacement ℂ q R J Δ p) :
    PositiveReplacement 𝕜 q R J Δ p := by
  rcases hcomplex with ⟨cstar, hcstar, C, c, hc, hcomplex⟩
  refine ⟨cstar, hcstar, C, c, hc, ?_⟩
  intro Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor
  classical
  let ΦC : (X : Finset (ℤ × ℤ)) →
      Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ :=
    fun X => (Φ X).map (toComplex 𝕜)
  let ΩC : Reg (Qudits q) Λ → ℂ := fun i => toComplex 𝕜 (Ω i)
  have hΦC : IsAdmissible Λ R J ΦC := by
    exact (isAdmissible_map_toComplex_iff Λ R J Φ).2 hΦ
  have hΩC : star ΩC ⬝ᵥ ΩC = 1 := by
    exact star_dotProduct_comp_toComplex_eq_one hΩ
  have hHΩC : hamiltonian Λ ΦC *ᵥ ΩC = (E₀ : ℂ) • ΩC := by
    rw [show hamiltonian Λ ΦC = (hamiltonian Λ Φ).map (toComplex 𝕜) by
      exact hamiltonian_map_toComplex Λ Φ]
    simpa only [ΩC, toComplex_ofReal] using
      (mulVec_map_toComplex_eq_smul_iff (hamiltonian Λ Φ) Ω (E₀ : 𝕜)).2 hHΩ
  have hgapC : HasGlobalGap (hamiltonian Λ ΦC) ΩC E₀ Δ := by
    rw [show hamiltonian Λ ΦC = (hamiltonian Λ Φ).map (toComplex 𝕜) by
      exact hamiltonian_map_toComplex Λ Φ]
    exact (hasGlobalGap_map_toComplex_iff (hamiltonian Λ Φ) Ω E₀ Δ).2 hgap
  obtain ⟨kC, hkC, hsumC, hgapOrderC, htailC, hsuppC⟩ :=
    hcomplex Λ ΦC hΦC ΩC hΩC E₀ hHΩC hgapC anchor hanchor
  have hEnergyMap :
      ((cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1)).map (toComplex 𝕜) =
        (cstar : ℂ)⁻¹ • (hamiltonian Λ ΦC - (E₀ : ℂ) • 1) := by
    rw [map_toComplex_smul, map_inv₀, toComplex_ofReal, map_toComplex_sub,
      map_toComplex_smul, toComplex_ofReal, map_toComplex_one,
      ← hamiltonian_map_toComplex Λ Φ]
  have hGapMap :
      ((((Δ / cstar : ℝ) : 𝕜) • (1 - vecMulVec Ω (star Ω))).map (toComplex 𝕜)) =
        ((Δ / cstar : ℝ) : ℂ) • (1 - vecMulVec ΩC (star ΩC)) := by
    rw [map_toComplex_smul, toComplex_ofReal, map_toComplex_sub, map_toComplex_one,
      star_comp_toComplex, vecMulVec_comp_toComplex]
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · let k : Finset (ℤ × ℤ) → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜 :=
      fun X => Matrix.realProjection (kC X)
    have hEnergyProjection :
        Matrix.realProjection (𝕜 := 𝕜)
            ((cstar : ℂ)⁻¹ • (hamiltonian Λ ΦC - (E₀ : ℂ) • 1)) =
          (cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1) := by
      rw [← hEnergyMap, Matrix.realProjection_map_toComplex hI]
    have hGapProjection :
        Matrix.realProjection (𝕜 := 𝕜)
            (((Δ / cstar : ℝ) : ℂ) • (1 - vecMulVec ΩC (star ΩC))) =
          ((Δ / cstar : ℝ) : 𝕜) • (1 - vecMulVec Ω (star Ω)) := by
      rw [← hGapMap, Matrix.realProjection_map_toComplex hI]
    refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
    · intro X hX
      have hXc := hkC X hX
      refine ⟨?_, ?_, ?_⟩
      · simpa only [k, Matrix.realProjection_zero] using
          Matrix.realProjection_mono (𝕜 := 𝕜) hXc.1
      · simpa only [k, Matrix.realProjection_one] using
          Matrix.realProjection_mono (𝕜 := 𝕜) hXc.2.1
      · exact Matrix.realProjection_mulVec_eq_zero hI hXc.2.2
    · have h := Matrix.realProjection_mono (𝕜 := 𝕜) hsumC
      calc
        (cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1) =
            Matrix.realProjection (𝕜 := 𝕜)
              ((cstar : ℂ)⁻¹ • (hamiltonian Λ ΦC - (E₀ : ℂ) • 1)) :=
          hEnergyProjection.symm
        _ ≤ Matrix.realProjection (𝕜 := 𝕜) (∑ X ∈ supports Λ R, kC X) := h
        _ = ∑ X ∈ supports Λ R, k X := by
          rw [Matrix.realProjection_sum]
    · have h := Matrix.realProjection_mono (𝕜 := 𝕜) hgapOrderC
      calc
        ((Δ / cstar : ℝ) : 𝕜) • (1 - vecMulVec Ω (star Ω)) =
            Matrix.realProjection (𝕜 := 𝕜)
              (((Δ / cstar : ℝ) : ℂ) • (1 - vecMulVec ΩC (star ΩC))) :=
          hGapProjection.symm
        _ ≤ Matrix.realProjection (𝕜 := 𝕜)
            ((cstar : ℂ)⁻¹ • (hamiltonian Λ ΦC - (E₀ : ℂ) • 1)) := h
        _ = (cstar : 𝕜)⁻¹ • (hamiltonian Λ Φ - (E₀ : 𝕜) • 1) :=
          hEnergyProjection
    · intro X hX l
      let hN := graphNbhd_subset Λ {anchor X} l
      have ht := htailC X hX l
      refine ⟨?_, ?_, ?_⟩
      · have h := Matrix.realProjection_mono (𝕜 := 𝕜) ht.1
        simpa only [k, Matrix.realProjection_zero,
          Matrix.realProjection_condExpect hN] using h
      · have h := Matrix.realProjection_mono (𝕜 := 𝕜) ht.2.1
        simpa only [k, Matrix.realProjection_one,
          Matrix.realProjection_condExpect hN] using h
      · have hdiff :
            k X - condExpect hN (k X) =
              Matrix.realProjection (𝕜 := 𝕜) (kC X - condExpect hN (kC X)) := by
          simp only [k, Matrix.realProjection_sub, Matrix.realProjection_condExpect hN]
        have hherm : (kC X - condExpect hN (kC X)).IsHermitian :=
          (hkC X hX).1.posSemidef.isHermitian.sub ht.1.posSemidef.isHermitian
        calc
          ‖k X - condExpect hN (k X)‖ =
              ‖Matrix.realProjection (𝕜 := 𝕜) (kC X - condExpect hN (kC X))‖ :=
            congrArg norm hdiff
          _ ≤ ‖kC X - condExpect hN (kC X)‖ :=
            Matrix.norm_realProjection_le hherm
          _ ≤ C * Real.exp (-c * (l : ℝ) ^ ((p : ℝ) / (p + 1))) := ht.2.2
    · intro X hX
      exact Matrix.IsSupportedOn.realProjection
        (domainComponent_subset Λ (anchor X)) (hsuppC X hX)
  · let k : Finset (ℤ × ℤ) → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜 :=
      fun X => Matrix.complexPullback hI (kC X)
    have hkMap (X : Finset (ℤ × ℤ)) :
        (k X).map (toComplex 𝕜) = kC X := by
      exact Matrix.complexPullback_map_toComplex hI (kC X)
    refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
    · intro X hX
      have hXc := hkC X hX
      refine ⟨?_, ?_, ?_⟩
      · rw [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜)]
        simpa only [Matrix.map_zero, map_zero, hkMap] using hXc.1
      · rw [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜)]
        simpa only [map_toComplex_one, hkMap] using hXc.2.1
      · funext i
        apply toComplex_injective
        change toComplex 𝕜 ((k X *ᵥ Ω) i) = toComplex 𝕜 0
        rw [← congrFun (mulVec_map_toComplex (k X) Ω) i, hkMap]
        simpa only [ΩC, Pi.zero_apply, map_zero] using congrFun hXc.2.2 i
    · rw [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜), hEnergyMap,
        map_toComplex_sum]
      convert hsumC using 1
      · rfl
      · simp only [hkMap]
    · rw [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜), hGapMap, hEnergyMap]
      exact hgapOrderC
    · intro X hX l
      let hN := graphNbhd_subset Λ {anchor X} l
      have ht := htailC X hX l
      refine ⟨?_, ?_, ?_⟩
      · rw [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜)]
        simpa only [Matrix.map_zero, map_zero, condExpect_map_toComplex, hkMap] using ht.1
      · rw [← map_toComplex_le_map_toComplex_iff (𝕜 := 𝕜)]
        simpa only [condExpect_map_toComplex, map_toComplex_one, hkMap] using ht.2.1
      · rw [← norm_map_toComplex, map_toComplex_sub, hkMap,
          condExpect_map_toComplex, hkMap]
        exact ht.2.2
    · intro X hX
      obtain ⟨B, hB⟩ := hsuppC X hX
      refine ⟨Matrix.complexPullback hI B, ?_⟩
      apply map_toComplex_injective (𝕜 := 𝕜)
      change (k X).map (toComplex 𝕜) =
        (extendId (domainComponent_subset Λ (anchor X))
          (Matrix.complexPullback hI B)).map (toComplex 𝕜)
      rw [hkMap, hB, ← extendId_map_toComplex,
        Matrix.complexPullback_map_toComplex]

end OpenAI
