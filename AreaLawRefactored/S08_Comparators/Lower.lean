import AreaLawRefactored.S08_Comparators.Interfaces
import AreaLawRefactored.S08_Comparators.Entropy
import AreaLawForMathlib.Analysis.Matrix.ProjectionSectorMean

/-!
# §8.4–§8.5 The defect mass and the lower bounds (D8.23, D8.32–D8.35)

Digest `digest/08-comparators.md` D8.23, D8.32–D8.35, paper `paper/sections/07-comparators.tex`
422–439, 604–650. No geometry: the physical system is an arbitrary finite site type `σ` with
arbitrary local dimensions, the statuses and trees are arbitrary.

The lower pin D8.31 (`Step_8_31`), the prevector facts D8.13 (`Step_8_13`) and the band
commutation D8.1 (ii) (`Step_8_1`) enter as hypotheses.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

/-! ## One copy of `𝒱`: operators on the physical factor -/

section OneCopy

variable {σ : Type u} {n : σ → ℕ} (d : ℕ)

/-- `𝒱 = 𝓗_phys ⊗ (𝓗_C ⊗ 𝓗_R)` on basis configurations. -/
private def splitCR : SiteConfig (dims n d) ≃ SiteConfig n × (Fin d × Fin d) where
  toFun x := (physPart x, x .C, x .R)
  invFun w := fun s => match s with
    | .phys v => w.1 v
    | .C => w.2.1
    | .R => w.2.2
  left_inv x := by funext s; cases s <;> rfl
  right_inv w := rfl

@[simp] private theorem splitCR_apply (x : SiteConfig (dims n d)) :
    splitCR d x = (physPart x, x .C, x .R) := rfl

/-- A physical one-copy operator `m ⊗ 1_{CR}` on `𝒱`. -/
private noncomputable def liftCR (m : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Matrix (SiteConfig (dims n d)) (SiteConfig (dims n d)) ℂ :=
  reindex (splitCR d).symm (splitCR d).symm (m ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))

private theorem liftCR_apply (m : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (x y : SiteConfig (dims n d)) :
    liftCR d m x y = m (physPart x) (physPart y) * if x .C = y .C ∧ x .R = y .R then 1 else 0 := by
  change m (physPart x) (physPart y) * (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    ((x .C : Fin d), (x .R : Fin d)) ((y .C : Fin d), (y .R : Fin d)) = _
  rw [one_apply]
  exact congrArg _ (if_congr Prod.ext_iff rfl rfl)

private theorem liftCR_one [Fintype σ] :
    liftCR d (1 : Matrix (SiteConfig n) (SiteConfig n) ℂ) = 1 := by
  simp [liftCR]

private theorem liftCR_sub (A B : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    liftCR d (A - B) = liftCR d A - liftCR d B := by
  ext x y; simp only [Matrix.sub_apply, liftCR_apply]; ring

private theorem liftCR_smul (c : ℂ) (A : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    liftCR d (c • A) = c • liftCR d A := by
  ext x y; simp only [Matrix.smul_apply, liftCR_apply, smul_eq_mul]; ring

private theorem liftCR_mul [Fintype σ] [DecidableEq σ]
    (A B : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    liftCR d (A * B) = liftCR d A * liftCR d B := by
  simp only [liftCR, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one]

private theorem conjTranspose_liftCR (A : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    (liftCR d A)ᴴ = liftCR d Aᴴ := by
  simp [liftCR, conjTranspose_submatrix, conjTranspose_kronecker]

private theorem PosSemidef.liftCR [Finite σ] {A : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hA : A.PosSemidef) :
    (liftCR d A).PosSemidef :=
  (hA.kronecker PosSemidef.one).submatrix _

private theorem liftCR_le_liftCR [Finite σ] {A B : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (h : A ≤ B) :
    liftCR d A ≤ liftCR d B := by
  rw [Matrix.le_iff, ← liftCR_sub]; exact PosSemidef.liftCR d (Matrix.le_iff.mp h)

variable [Fintype σ] [DecidableEq σ] (D : PhysData n)

private theorem groundProj_eq : groundProj D d = liftCR d (vecMulVec D.Ω (star D.Ω)) := by
  ext x y; rw [liftCR_apply]; simp [groundProj, vecMulVec_apply]

private theorem excProj_eq : excProj D d = liftCR d (1 - vecMulVec D.Ω (star D.Ω)) := by
  rw [excProj, groundProj_eq, liftCR_sub, liftCR_one]

private theorem Hx_eq : Hx D d = liftCR d D.H := by
  ext x y; rw [liftCR_apply]; rfl

private theorem vecMulVec_Ω_mul_self :
    vecMulVec D.Ω (star D.Ω) * vecMulVec D.Ω (star D.Ω) = vecMulVec D.Ω (star D.Ω) := by
  rw [vecMulVec_mul_vecMulVec, D.norm_Ω, one_smul]

private theorem isStarProjection_groundProj : IsStarProjection (groundProj D d) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, groundProj_eq, ← liftCR_mul, vecMulVec_Ω_mul_self]
  · rw [IsSelfAdjoint, star_eq_conjTranspose, groundProj_eq, conjTranspose_liftCR,
      conjTranspose_vecMulVec, star_star]

private theorem isStarProjection_excProj : IsStarProjection (excProj D d) :=
  (isStarProjection_groundProj d D).one_sub

/-- D8.23.1 on one copy: `H̃ - Ẽ₀ ≥ g̃ Q` (tensored with `1_{CR}`). -/
private theorem gap_excProj : (D.g : ℂ) • excProj D d ≤ Hx D d - (D.E₀ : ℂ) • 1 := by
  rw [excProj_eq, Hx_eq, ← liftCR_smul, ← liftCR_one (n := n) d, ← liftCR_smul, ← liftCR_sub]
  exact liftCR_le_liftCR d D.gap

end OneCopy

/-! ## `k` copies: products over the copies -/

section Copies

variable {Ω : Type*} {k : ℕ}

/-- The product operator `⊗_j M_j` on `k` copies. -/
private def copyProd (M : Fin k → Matrix Ω Ω ℂ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  fun x y => ∏ j, M j (x j) (y j)

private theorem copyProd_mul [Fintype Ω] (M N : Fin k → Matrix Ω Ω ℂ) :
    copyProd M * copyProd N = copyProd fun j => M j * N j := by
  ext x y
  simp only [copyProd, mul_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private theorem conjTranspose_copyProd (M : Fin k → Matrix Ω Ω ℂ) :
    (copyProd M)ᴴ = copyProd fun j => (M j)ᴴ := by
  ext x y
  simp [copyProd, conjTranspose_apply]

private theorem copyProd_one [DecidableEq Ω] :
    copyProd (fun _ : Fin k => (1 : Matrix Ω Ω ℂ)) = 1 := by
  ext x y
  simp only [copyProd, one_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
  congr 1
  exact propext funext_iff.symm

private theorem siteOp_eq_copyProd [DecidableEq Ω] (i : Fin k) (A : Matrix Ω Ω ℂ) :
    TensorPower.siteOp i A = copyProd fun j => if j = i then A else 1 := by
  ext x y
  rw [TensorPower.siteOp_apply, copyProd, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    if_pos rfl, Finset.prod_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]]
  simp only [one_apply, Finset.prod_boole, Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
  by_cases h : ∀ j, j ≠ i → x j = y j
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

private theorem PosSemidef.siteOp [Finite Ω] [DecidableEq Ω] {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (i : Fin k) :
    (TensorPower.siteOp i A).PosSemidef := by
  rw [TensorPower.siteOp_eq_reindex]
  exact (hA.kronecker PosSemidef.one).submatrix _

end Copies

/-! ## D8.23 The excited-copy components and the defect mass -/

section Defect

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} (D : PhysData n) (d : ℕ)

/-- The factor of `Π_B` at copy `j`: `Q` on the copies in `B`, `1 - Q` on the others. -/
private noncomputable def compFac {k : ℕ} (B : Finset (Fin k)) (j : Fin k) :
    Matrix (SiteConfig (dims n d)) (SiteConfig (dims n d)) ℂ :=
  if j ∈ B then excProj D d else groundProj D d

private theorem compProj_eq_copyProd (k : ℕ) (B : Finset (Fin k)) :
    compProj D d k B = copyProd (compFac D d B) := rfl

private theorem compFac_mul {k : ℕ} (B B' : Finset (Fin k)) (j : Fin k) :
    compFac D d B j * compFac D d B' j = if (j ∈ B ↔ j ∈ B') then compFac D d B j else 0 := by
  have hG := isStarProjection_groundProj d D
  simp only [compFac, excProj]
  by_cases h : j ∈ B <;> by_cases h' : j ∈ B' <;>
    simp [h, h', hG.isIdempotentElem.eq, hG.one_sub.isIdempotentElem.eq, hG.mul_one_sub_self,
      hG.one_sub_mul_self]

private theorem isHermitian_compFac {k : ℕ} (B : Finset (Fin k)) (j : Fin k) :
    (compFac D d B j).IsHermitian := by
  unfold compFac
  split_ifs
  · exact (isStarProjection_excProj d D).isSelfAdjoint.isHermitian
  · exact (isStarProjection_groundProj d D).isSelfAdjoint.isHermitian

private theorem isHermitian_compProj (k : ℕ) (B : Finset (Fin k)) :
    (compProj D d k B).IsHermitian := by
  rw [IsHermitian, compProj_eq_copyProd, conjTranspose_copyProd]
  exact congrArg copyProd (funext fun j => (isHermitian_compFac D d B j).eq)

/-- D8.24. The `Π_B` resolve the identity into mutually orthogonal projections. -/
private theorem isOrthogonalResolution_compProj (k : ℕ) :
    IsOrthogonalResolution (compProj D d k) where
  mul_eq B B' := by
    rw [compProj_eq_copyProd, compProj_eq_copyProd, copyProd_mul]
    split_ifs with h
    · subst h
      exact congrArg copyProd (funext fun j => by rw [compFac_mul, if_pos Iff.rfl])
    · obtain ⟨j, hj⟩ : ∃ j, ¬(j ∈ B ↔ j ∈ B') := by
        by_contra hc
        push Not at hc
        exact h (Finset.ext hc)
      ext x y
      simp only [copyProd, Matrix.zero_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ j)
        (by rw [compFac_mul, if_neg hj, Matrix.zero_apply])
  sum_eq := by
    have h : ∑ B, compProj D d k B = copyProd fun _ => excProj D d + groundProj D d := by
      ext x y
      simp only [Matrix.sum_apply, compProj_eq_copyProd, copyProd, Matrix.add_apply]
      rw [Finset.prod_add, Finset.powerset_univ]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.prod_mul_prod_compl t, Finset.compl_eq_univ_sdiff]
      congr 1 <;> refine Finset.prod_congr rfl fun j hj => ?_
      · simp [compFac, hj]
      · simp [compFac, (Finset.mem_sdiff.mp hj).2]
    rw [h, excProj, sub_add_cancel, copyProd_one]

private theorem defectProj_eq (τ : ℝ) (k : ℕ) :
    defectProj D d τ k =
      ∑ B ∈ Finset.univ.filter fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k, compProj D d k B :=
  rfl

/-- D8.23. `Π` is an orthogonal projection. -/
private theorem isStarProjection_defectProj (τ : ℝ) (k : ℕ) :
    IsStarProjection (defectProj D d τ k) := by
  have hres := isOrthogonalResolution_compProj D d k
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, defectProj_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single B (fun B' _ hne => hres.mul_of_ne hne.symm)
      (fun h => absurd hB h)]
    exact hres.mul_self B
  · rw [IsSelfAdjoint, defectProj_eq, star_sum]
    exact Finset.sum_congr rfl fun B _ => (isHermitian_compProj D d k B).eq

/-- D8.23.2. `Q^{(i)} Π_B = Π_B` if `i ∈ B`, and `0` otherwise. -/
private theorem siteOp_excProj_mul_compProj {k : ℕ} (i : Fin k) (B : Finset (Fin k)) :
    TensorPower.siteOp i (excProj D d) * compProj D d k B =
      if i ∈ B then compProj D d k B else 0 := by
  have hE := isStarProjection_excProj d D
  have hG := isStarProjection_groundProj d D
  rw [siteOp_eq_copyProd, compProj_eq_copyProd, copyProd_mul]
  split_ifs with hi
  · refine congrArg copyProd (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj; simp [compFac, hi, hE.isIdempotentElem.eq]
    · simp [hj]
  · ext x y
    simp only [copyProd, Matrix.zero_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [compFac, hi, excProj, hG.one_sub_mul_self]

/-- D8.23.2. `∑_i Q_i = ∑_B |B| Π_B`: the count of excited copies. -/
private theorem sum_siteOp_excProj (k : ℕ) :
    ∑ i, TensorPower.siteOp i (excProj D d) =
      ∑ B : Finset (Fin k), ((B.card : ℝ) : ℂ) • compProj D d k B := by
  have hres := isOrthogonalResolution_compProj D d k
  calc ∑ i, TensorPower.siteOp i (excProj D d)
      = ∑ i, ∑ B, TensorPower.siteOp i (excProj D d) * compProj D d k B := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, hres.sum_eq, Matrix.mul_one]
    _ = ∑ B : Finset (Fin k), ((B.card : ℝ) : ℂ) • compProj D d k B := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun B _ => ?_
        simp_rw [siteOp_excProj_mul_compProj]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
        norm_cast

/-- D8.23.1. `\overline{H̃} - Ẽ₀ ≥ (g̃/k) ∑_i Q_i` for `k ≥ 1`: the one-copy gap averaged over
the copies. -/
private theorem gap_Hbar {k : ℕ} (hk : 0 < k) :
    ((D.g / k : ℝ) : ℂ) • ∑ i, TensorPower.siteOp i (excProj D d) ≤
      Hbar D d k - (D.E₀ : ℂ) • 1 := by
  set X := Hx D d - (D.E₀ : ℂ) • 1 - (D.g : ℂ) • excProj D d
  have hX : X.PosSemidef := Matrix.le_iff.mp (gap_excProj d D)
  have hsum : (∑ i : Fin k, TensorPower.siteOp i X).PosSemidef :=
    posSemidef_sum _ fun i _ => PosSemidef.siteOp hX i
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have heq : Hbar D d k - (D.E₀ : ℂ) • 1 -
      ((D.g / k : ℝ) : ℂ) • ∑ i, TensorPower.siteOp i (excProj D d) =
      ((k : ℂ))⁻¹ • ∑ i : Fin k, TensorPower.siteOp i X := by
    simp only [X, TensorPower.siteOp_sub, TensorPower.siteOp_smul, TensorPower.siteOp_one,
      Finset.sum_sub_distrib,
      ← Finset.smul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Hbar,
      TensorPower.copyMean]
    match_scalars <;> field_simp
  rw [Matrix.le_iff, heq]
  refine hsum.smul ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  exact Complex.zero_le_real.mpr (by positivity)

/-- D8.23.2. The Markov bound on the excited-copy count: for a unit vector `u` and `k ≥ 1`,
`⟨u, Π u⟩ ≥ 1 - ((⟨u, \overline{H̃} u⟩ - Ẽ₀)/g̃)/τ`. -/
private theorem defect_mass {τ : ℝ} (hτ : 0 < τ) {k : ℕ} (hk : 0 < k)
    {u : Transport.Config (dims n d) k → ℂ} (hu : star u ⬝ᵥ u = 1) :
    1 - ((star u ⬝ᵥ (Hbar D d k *ᵥ u)).re - D.E₀) / D.g / τ ≤
      (star u ⬝ᵥ (defectProj D d τ k *ᵥ u)).re := by
  have hres := isOrthogonalResolution_compProj D d k
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hg := D.gap_pos
  set w : Finset (Fin k) → ℝ := fun B => (star u ⬝ᵥ (compProj D d k B *ᵥ u)).re with hw
  have hw0 : ∀ B, 0 ≤ w B := fun B => by
    simpa [IsOrthogonalResolution.weight] using
      hres.weight_nonneg (isHermitian_compProj D d k) u B
  have hw1 : ∑ B, w B = 1 := by
    simpa [IsOrthogonalResolution.weight, hu] using hres.sum_weight u
  set Y := (star u ⬝ᵥ (Hbar D d k *ᵥ u)).re - D.E₀
  set X := ∑ B : Finset (Fin k), (B.card : ℝ) * w B
  have hcount : (star u ⬝ᵥ ((∑ i, TensorPower.siteOp i (excProj D d)) *ᵥ u)).re = X := by
    rw [sum_siteOp_excProj, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  -- D8.23.2: `⟨u, ∑ Q_i u⟩ ≤ k E_def`
  have hq := (Matrix.le_iff.mp (gap_Hbar D d hk)).re_dotProduct_nonneg u
  simp only [RCLike.re_to_complex, sub_mulVec, dotProduct_sub, Complex.sub_re,
    smul_mulVec, dotProduct_smul,
    smul_eq_mul, one_mulVec, hu, Complex.re_ofReal_mul, mul_one, Complex.ofReal_re, hcount] at hq
  have hgX : D.g * X ≤ Y * k := by
    have h1 : D.g / k * X ≤ Y := by simp only [Y]; linarith
    rwa [div_mul_eq_mul_div, div_le_iff₀ hkR] at h1
  -- D8.23.2: on `ran (1 - Π)` the count exceeds `τ k`
  set S := Finset.univ.filter fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k
  have hdef : (star u ⬝ᵥ (defectProj D d τ k *ᵥ u)).re = ∑ B ∈ S, w B := by
    rw [defectProj_eq, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  have hsplit : ∑ B ∈ S, w B + ∑ B ∈ Finset.univ.filter
      (fun B : Finset (Fin k) => ¬ (B.card : ℝ) ≤ τ * k), w B = 1 :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).trans hw1
  have hmarkov : ∑ B ∈ Finset.univ.filter
      (fun B : Finset (Fin k) => ¬ (B.card : ℝ) ≤ τ * k), w B ≤ X / (τ * k) := by
    rw [Finset.sum_div]
    calc ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) => ¬ (B.card : ℝ) ≤ τ * k), w B
        ≤ ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) => ¬ (B.card : ℝ) ≤ τ * k),
            (B.card : ℝ) * w B / (τ * k) := by
          refine Finset.sum_le_sum fun B hB => ?_
          have hB' : τ * k < B.card := lt_of_not_ge (Finset.mem_filter.mp hB).2
          rw [le_div_iff₀ (by positivity)]
          nlinarith [hw0 B]
      _ ≤ ∑ B, (B.card : ℝ) * w B / (τ * k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun B _ _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw0 B)) (by positivity)
  have hfin : X / (τ * k) ≤ Y / D.g / τ := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [hdef]
  linarith

omit [Fintype σ] in
/-- The physical part of a configuration is unchanged by a permutation of the copies of a
subsystem `Q` of the auxiliary factors. -/
private theorem physPart_subsystemPerm {k : ℕ} {Q : Finset (Site σ)}
    (hQ : ∀ v, Site.phys v ∉ Q) (g : Equiv.Perm (Fin k)) (x : Transport.Config (dims n d) k)
    (j : Fin k) :
    physPart (TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q g x j) =
      physPart (x j) := by
  funext v
  exact if_neg (hQ v)

private theorem compProj_apply (k : ℕ) (B : Finset (Fin k)) (x y : Transport.Config (dims n d) k) :
    compProj D d k B x y =
      (∏ j, (if j ∈ B then 1 - vecMulVec D.Ω (star D.Ω) else vecMulVec D.Ω (star D.Ω))
          (physPart (x j)) (physPart (y j))) *
        if ∀ j, x j .C = y j .C ∧ x j .R = y j .R then 1 else 0 := by
  have hf : ∀ j, compFac D d B j = liftCR d
      (if j ∈ B then 1 - vecMulVec D.Ω (star D.Ω) else vecMulVec D.Ω (star D.Ω)) := fun j => by
    unfold compFac; split_ifs
    · exact excProj_eq d D
    · exact groundProj_eq d D
  rw [compProj_eq_copyProd, copyProd]
  simp only [hf, liftCR_apply, Finset.prod_mul_distrib, Finset.prod_boole, Finset.mem_univ,
    true_implies]

/-- D8.23.3. `Π_B` acts on the physical copies only: it is invariant under the permutations of
the copies of the auxiliary factors. -/
private theorem compProj_subsystemPerm {k : ℕ} {Q : Finset (Site σ)} (hQ : ∀ v, Site.phys v ∉ Q)
    (g : Equiv.Perm (Fin k)) (B : Finset (Fin k)) (x y : Transport.Config (dims n d) k) :
    compProj D d k B (TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q g x)
        (TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q g y) =
      compProj D d k B x y := by
  have hiff : ∀ f : Site σ,
      (∀ j, TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q g x j f =
        TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q g y j f) ↔
      ∀ j, x j f = y j f := fun f => by
    by_cases hf : f ∈ Q
    · simp only [TensorPower.subsystemPerm_apply, hf, if_true]
      exact ⟨fun h j => by simpa using h (g j), fun h j => h _⟩
    · simp [hf]
  rw [compProj_apply, compProj_apply]
  simp only [physPart_subsystemPerm d hQ]
  congr 1
  refine if_congr ?_ rfl rfl
  rw [forall_and, forall_and, hiff, hiff]

/-- D8.23.3. `Π_B` under a permutation `s` of the whole copies is `Π_{s⁻¹ B}`. -/
private theorem compProj_copyPerm {k : ℕ} (s : Equiv.Perm (Fin k)) (B : Finset (Fin k))
    (x y : Transport.Config (dims n d) k) :
    compProj D d k B (TensorPower.copyPerm (SiteConfig (dims n d)) k s x)
        (TensorPower.copyPerm (SiteConfig (dims n d)) k s y) =
      compProj D d k (B.map s.symm.toEmbedding) x y := by
  simp only [compProj_eq_copyProd, copyProd, TensorPower.copyPerm_apply]
  rw [← Equiv.prod_comp s]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [compFac, Finset.mem_map_equiv]

/-- D8.23.3. `Π` commutes with the permutations of the whole copies. -/
private theorem commute_copyPerm_defectProj (τ : ℝ) {k : ℕ} (s : Equiv.Perm (Fin k)) :
    Commute (permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s)
      (defectProj D d τ k) := by
  refine commute_permOp_of_apply_eq _ s fun x y => ?_
  rw [defectProj_eq, Matrix.sum_apply, Matrix.sum_apply]
  simp only [compProj_copyPerm]
  exact Finset.sum_nbij' (fun B => B.map s.symm.toEmbedding) (fun B => B.map s.toEmbedding)
    (by simp) (by simp) (by simp [Finset.map_map]) (by simp [Finset.map_map]) fun _ _ => rfl

/-- D8.23.3. `Π` commutes with the permutations of the copies of an auxiliary subsystem. -/
private theorem commute_subsystemPerm_defectProj (τ : ℝ) {k : ℕ} {Q : Finset (Site σ)}
    (hQ : ∀ v, Site.phys v ∉ Q) (g : Equiv.Perm (Fin k)) :
    Commute (permOp (TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q) g)
      (defectProj D d τ k) := by
  refine commute_permOp_of_apply_eq _ g fun x y => ?_
  rw [defectProj_eq, Matrix.sum_apply, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun B _ => compProj_subsystemPerm D d hQ g B x y

private theorem commute_Pi_labelProj {k : ℕ} (Q : Finset (Site σ))
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Commute (Transport.Pi (dims n d) k)
      (labelProj (TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q) l) := by
  refine Transport.commute_Pi_of_forall fun s => ?_
  have h := TensorPower.commute_groupAlgebraRep_subsystemPerm_of_subset
    (fun f => Fin (dims n d f)) k (Finset.subset_univ Q) (IrrepLabel.centralIdem_mem_center l)
    (MonoidAlgebra.single s 1)
  rw [groupAlgebraRep_single, one_smul, TensorPower.subsystemPerm_univ] at h
  exact h.symm

/-- D8.13, D8.23. The auxiliary sector `π^λ_C π^λ_R Π_k` is an orthogonal projection. -/
private theorem isStarProjection_sector (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    IsStarProjection (sector (σ := σ) (n := n) d k l) := by
  have hC : IsStarProjection (piC (σ := σ) (n := n) d k l) :=
    ⟨labelProj_mul_self _ l, isHermitian_labelProj _ l⟩
  have hR : IsStarProjection (piR (σ := σ) (n := n) d k l) :=
    ⟨labelProj_mul_self _ l, isHermitian_labelProj _ l⟩
  have hP : IsStarProjection (Transport.Pi (dims n d) k) :=
    ⟨Transport.Pi_mul_Pi k, Transport.isHermitian_Pi k⟩
  have hCR : Commute (piC (σ := σ) (n := n) d k l) (piR d k l) :=
    TensorPower.commute_labelProj_subsystemPerm_of_disjoint _ k (by simp) l l
  exact (hC.mul hR hCR).mul hP ((commute_Pi_labelProj d {Site.C} l).symm.mul_left
    (commute_Pi_labelProj d {Site.R} l).symm)

/-- D8.23.3. `Π` commutes with the auxiliary sector. -/
private theorem commute_defectProj_sector (τ : ℝ) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Commute (defectProj D d τ k) (sector d k l) := by
  have hC : Commute (piC d k l) (defectProj D d τ k) :=
    commute_labelProj_of_forall_commute _
      (commute_subsystemPerm_defectProj D d τ (by simp)) l
  have hR : Commute (piR d k l) (defectProj D d τ k) :=
    commute_labelProj_of_forall_commute _
      (commute_subsystemPerm_defectProj D d τ (by simp)) l
  have hP : Commute (Transport.Pi (dims n d) k) (defectProj D d τ k) :=
    Transport.commute_Pi_of_forall (commute_copyPerm_defectProj D d τ)
  exact ((hC.mul_left hR).mul_left hP).symm

/-- D8.23. `Π` on the auxiliary sector is an orthogonal projection. -/
private theorem isStarProjection_lowProj (τ : ℝ) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    IsStarProjection (lowProj D d τ k l) :=
  (isStarProjection_defectProj D d τ k).mul (isStarProjection_sector d k l)
    (commute_defectProj_sector D d τ k l)


/-- D8.23 (`comparator:defect-mass`). `Q_i = 1 - |Ω̃⟩⟨Ω̃|` on physical copy `i`. On `𝒮_k` with
the two fixed auxiliary labels, `Π` = projection onto `∑_i Q_i ≤ τ k`.
$$\overline{\widetilde H}-\widetilde E_0\,1\ge\frac{\widetilde g}k\sum_iQ_i,\qquad
\langle v,\Pi v\rangle\ge1-E_{\rm def}/\tau.$$
`Π` commutes with symmetry and the auxiliary sectors. -/
theorem step_8_23 {τ : ℝ} (hτ : 0 < τ) {k : ℕ} (hk : 0 < k) :
    ((D.g / k : ℝ) : ℂ) • ∑ i, TensorPower.siteOp i (excProj D d) ≤
        Hbar D d k - (D.E₀ : ℂ) • 1 ∧
      (∀ u : Transport.Config (dims n d) k → ℂ, star u ⬝ᵥ u = 1 →
        1 - ((star u ⬝ᵥ (Hbar D d k *ᵥ u)).re - D.E₀) / D.g / τ ≤
          (star u ⬝ᵥ (defectProj D d τ k *ᵥ u)).re) ∧
      IsStarProjection (defectProj D d τ k) ∧
      (∀ s, Commute (permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s)
        (defectProj D d τ k)) ∧
      ∀ l, Commute (defectProj D d τ k) (sector d k l) := by
  -- D8.23.1: `H̃ - Ẽ₀ ≥ g̃ Q` per copy, averaged over the copies
  have h1 := gap_Hbar D d hk
  -- D8.23.2: `⟨u, ∑ Q_i u⟩ ≥ τ k ⟨u, (1 - Π) u⟩` and `⟨u, ∑ Q_i u⟩ ≤ k E_def`
  have h2 : ∀ u : Transport.Config (dims n d) k → ℂ, star u ⬝ᵥ u = 1 →
      1 - ((star u ⬝ᵥ (Hbar D d k *ᵥ u)).re - D.E₀) / D.g / τ ≤
        (star u ⬝ᵥ (defectProj D d τ k *ᵥ u)).re := fun u hu => defect_mass D d hτ hk hu
  -- D8.23.3: the count acts on the physical copies only
  have h3 := commute_copyPerm_defectProj D d τ (k := k)
  have h4 := commute_defectProj_sector D d τ k
  exact ⟨h1, h2, isStarProjection_defectProj D d τ k, h3, h4⟩

end Defect

/-! ## §8.5 Passing the lower pin through the tree -/

section Floor

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {K : ℕ} {St : Type v} {X : Finset σ}

omit [Fintype σ] [DecidableEq σ] in
private theorem phys_mem_physReg {Q : Finset σ} {v : σ} : Site.phys v ∈ physReg Q ↔ v ∈ Q :=
  Finset.mem_map' _

omit [Fintype σ] [DecidableEq σ] in
private theorem C_not_mem_physReg (Q : Finset σ) : (Site.C : Site σ) ∉ physReg Q := fun h => by
  obtain ⟨a, -, ha⟩ := Finset.mem_map.mp h
  cases ha

omit [Fintype σ] [DecidableEq σ] in
private theorem R_not_mem_physReg (Q : Finset σ) : (Site.R : Site σ) ∉ physReg Q := fun h => by
  obtain ⟨a, -, ha⟩ := Finset.mem_map.mp h
  cases ha

/-- D8.6. `P_{j,g}, Y_{j,g}, F_{j,g}` partition `𝒱`. -/
private theorem Statuses.isPartition_part (Γ : Statuses σ K St X) (s : St) (g : Fin K) :
    (Γ.part s g).IsPartition := by
  have hXY := Finset.disjoint_left.mp (Γ.disjoint_XY s g)
  have hUY := Finset.disjoint_left.mp (Γ.disjoint_UY s g)
  have hXV := Finset.disjoint_left.mp (Γ.disjoint_XV s g)
  have hUV := Finset.disjoint_left.mp (Γ.disjoint_UV s g)
  have hYV := Finset.disjoint_left.mp (Γ.disjoint_YV s g)
  have hcov : ∀ v, v ∈ X ∪ Γ.U s g ∪ Γ.Y s g ∪ Γ.V s g := fun v => Γ.cover s g ▸ Finset.mem_univ v
  simp only [Transport.PYF.IsPartition, Statuses.part, Statuses.P, Statuses.Yr, Statuses.F]
  refine ⟨Finset.disjoint_left.mpr fun a ha hb => ?_, Finset.disjoint_left.mpr fun a ha hb => ?_,
    Finset.disjoint_left.mpr fun a ha hb => ?_, Finset.eq_univ_of_forall fun a => ?_⟩
  · cases a with
    | phys v =>
      simp only [Finset.mem_insert, reduceCtorEq, false_or, phys_mem_physReg,
        Finset.mem_union] at ha hb
      exact ha.elim (hXY · hb) (hUY · hb)
    | C => exact C_not_mem_physReg _ hb
    | R => simp [R_not_mem_physReg] at ha
  · cases a with
    | phys v =>
      simp only [Finset.mem_insert, reduceCtorEq, false_or, phys_mem_physReg,
        Finset.mem_union] at ha hb
      exact ha.elim (hXV · hb) (hUV · hb)
    | C => simp [C_not_mem_physReg] at hb
    | R => simp [R_not_mem_physReg] at ha
  · cases a with
    | phys v =>
      simp only [Finset.mem_insert, reduceCtorEq, false_or, phys_mem_physReg] at ha hb
      exact hYV ha hb
    | C => exact C_not_mem_physReg _ ha
    | R => exact R_not_mem_physReg _ ha
  · cases a with
    | phys v =>
      have := hcov v
      simp only [Finset.mem_union] at this
      simp only [Finset.mem_union, Finset.mem_insert, reduceCtorEq, false_or, phys_mem_physReg]
      tauto
    | C => simp
    | R => simp

/-- A floor `c Π_k ≤ A` on `𝒮_k`, `c ≤ 1`, is a floor `c ≤ Π_k A + (1 - Π_k)` of the padded
operator. -/
private theorem smul_one_le_proj_mul_add_one_sub {m : Type*} [Fintype m] [DecidableEq m]
    {P A : Matrix m m ℂ} (hP : IsStarProjection P) (hPA : Commute P A) {c : ℝ} (hc : c ≤ 1)
    (hcA : c • P ≤ A) : c • (1 : Matrix m m ℂ) ≤ P * A + (1 - P) := by
  have hPh : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have h1 : (Pᴴ * (A - c • P) * P).PosSemidef :=
    (Matrix.le_iff.mp hcA).conjTranspose_mul_mul_same P
  have h2 : ((1 - c) • (1 - P)).PosSemidef :=
    (nonneg_iff_posSemidef.mp hP.one_sub.nonneg).smul (sub_nonneg.mpr hc)
  have heq : P * A + (1 - P) - c • (1 : Matrix m m ℂ) = Pᴴ * (A - c • P) * P +
      (1 - c) • (1 - P) := by
    rw [hPh, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hP.isIdempotentElem.eq, hP.isIdempotentElem.eq, Matrix.mul_assoc, ← hPA.eq,
      ← Matrix.mul_assoc, hP.isIdempotentElem.eq]
    module
  rw [Matrix.le_iff, heq]
  exact h1.add h2

variable {n : σ → ℕ} [∀ v, NeZero (n v)] (d : ℕ) [NeZero d]

/-- D8.32. There is a common polynomial `p(k)` with `A_{j,g} ≥ p(k)^{-1} 1` on `𝒮_k` for all
leaves. On the common auxiliary sector, with `b₀ = (2p(k))^{-1}`,
$$A_{j,g}\ge b_0(1-\Pi)+b_{j,g}\Pi,\qquad b_{j,g}=b_0+\tfrac12\exp\{kaL_{j,g}-o(k)\}.$$ -/
theorem step_8_32 (Γ : Statuses σ K St X) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (s : St) (g : Fin K),
      (((k : ℝ) + 2) ^ C)⁻¹ • (1 : Matrix (Transport.Config (dims n d) k)
          (Transport.Config (dims n d) k) ℂ) ≤ Γ.bandA n d t k s g ∧
      ∀ (P : Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ) (c : ℝ),
        IsStarProjection P → 0 < c → c • P ≤ Γ.bandA n d t k s g →
        (2 * ((k : ℝ) + 2) ^ C)⁻¹ • (1 - P) + ((2 * ((k : ℝ) + 2) ^ C)⁻¹ + c / 2) • P ≤
          Γ.bandA n d t k s g := by
  obtain ⟨C, hC, hfl⟩ := Replicas.eq_replicas_leaf_floor_2 (fun f => Fin (dims n d f)) ht
  refine ⟨C, hC, fun k s g => ?_⟩
  have hpart := Γ.isPartition_part s g
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [k.cast_nonneg (α := ℝ)]
  have hp1 : 1 ≤ ((k : ℝ) + 2) ^ C := Real.one_le_rpow hk1 hC
  have hp0 : 0 < ((k : ℝ) + 2) ^ C := by linarith
  -- D8.32: the floor `A_k ≥ poly(k)^{-1}` on `𝒮_k` of `replicas:leaf-floor`, padded by `1 - Π_k`
  have hfloor : (((k : ℝ) + 2) ^ C)⁻¹ • (1 : Matrix (Transport.Config (dims n d) k)
      (Transport.Config (dims n d) k) ℂ) ≤ Γ.bandA n d t k s g := by
    have h := (hfl k _ _ _ hpart.1 hpart.2.1 hpart.2.2.1 hpart.2.2.2).1
    rw [Real.rpow_neg (by linarith), ← Transport.Pi_eq_projS] at h
    exact smul_one_le_proj_mul_add_one_sub
      ⟨Transport.Pi_mul_Pi k, Transport.isHermitian_Pi k⟩
      (Transport.commute_Pi_A t k _ _ _) (inv_le_one_of_one_le₀ hp1) h
  refine ⟨hfloor, fun P c hP hc hcP => ?_⟩
  -- D8.32: `A = ½ A + ½ A ≥ ½ p⁻¹ 1 + ½ c Π`
  have h := add_le_add (smul_le_smul_of_nonneg_left hfloor (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (smul_le_smul_of_nonneg_left hcP (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hl : (1 / 2 : ℝ) • ((((k : ℝ) + 2) ^ C)⁻¹ • (1 : Matrix (Transport.Config (dims n d) k)
        (Transport.Config (dims n d) k) ℂ)) + (1 / 2 : ℝ) • (c • P) =
      (2 * ((k : ℝ) + 2) ^ C)⁻¹ • (1 - P) + ((2 * ((k : ℝ) + 2) ^ C)⁻¹ + c / 2) • P := by
    rw [mul_inv]
    module
  rw [hl, ← add_smul, add_halves, one_smul] at h
  exact h

end Floor

section Tree

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Type*} [Fintype m] [DecidableEq m]

/-- D8.33.1. A mean tree whose leaves are `b₀` on `ran (1 - Π)` and `e^{λ_j}` on `ran Π` has root
`b₀` on `ran (1 - Π)` and `e^{∑_j w_j λ_j}` on `ran Π` (homogeneity, `∑_j w_j = 1`). -/
private theorem eval_projSector {P : Matrix m m ℂ} (hP : IsStarProjection P) {b₀ : ℝ} (hb₀ : 0 < b₀)
    (μ : ι → ℝ) (T : Transport.MeanTree ι) :
    T.eval (fun j => b₀ • (1 - P) + Real.exp (μ j) • P) =
      b₀ • (1 - P) + Real.exp (∑ j, T.weight j * μ j) • P := by
  induction T with
  | leaf j => simp [Transport.MeanTree.weight, Pi.single_apply]
  | node p l r ihl ihr =>
    rw [Transport.MeanTree.eval_node, ihl, ihr,
      geomMean_projSector hP hb₀ (Real.exp_pos _) hb₀ (Real.exp_pos _),
      ← Real.rpow_add hb₀, sub_add_cancel, Real.rpow_one, ← Real.exp_mul, ← Real.exp_mul,
      ← Real.exp_add]
    congr 3
    simp only [Transport.MeanTree.weight_node, add_mul, Finset.sum_add_distrib, mul_assoc,
      ← Finset.mul_sum]
    ring

/-- D8.33.1 with monotonicity: lower bounds `b₀ (1 - Π) + e^{λ_j} Π ≤ A_j` pass to the root. -/
private theorem projSector_le_eval {P : Matrix m m ℂ} (hP : IsStarProjection P) {b₀ : ℝ}
    (hb₀ : 0 < b₀)
    {μ : ι → ℝ} {A : ι → Matrix m m ℂ}
    (hA : ∀ j, b₀ • (1 - P) + Real.exp (μ j) • P ≤ A j) (T : Transport.MeanTree ι) :
    b₀ • (1 - P) + Real.exp (∑ j, T.weight j * μ j) • P ≤ T.eval A := by
  rw [← eval_projSector hP hb₀ μ T]
  exact Transport.lemma_7_1_2 (fun j => posDef_projSector hP hb₀ (Real.exp_pos _)) hA T

/-- D8.34.1–2. If `M ≥ b₀ (1 - Π) + e^{ℓ} Π`, then
`⟨v, log M v⟩ ≥ log b₀ + (ℓ - log b₀) ⟨v, Π v⟩` for a unit vector `v`. -/
private theorem re_dotProduct_log_ge {P M : Matrix m m ℂ} (hP : IsStarProjection P) {b₀ ℓ : ℝ}
    (hb₀ : 0 < b₀) (hle : b₀ • (1 - P) + Real.exp ℓ • P ≤ M) {v : m → ℂ}
    (hv : star v ⬝ᵥ v = 1) :
    Real.log b₀ + (ℓ - Real.log b₀) * (star v ⬝ᵥ (P *ᵥ v)).re ≤
      (star v ⬝ᵥ (CFC.log M *ᵥ v)).re := by
  -- D8.34.1: `log` is operator monotone; the right side is a function of `Π`
  have hlog := CFC.log_le_log hle (posDef_projSector hP hb₀ (Real.exp_pos ℓ)).isStrictlyPositive
  rw [CFC.log, CFC.log, cfc_projSector hP, Real.log_exp] at hlog
  have h := (Matrix.le_iff.mp hlog).re_dotProduct_nonneg v
  -- D8.34.2
  simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, hv, RCLike.re_to_complex, Complex.sub_re, Complex.add_re,
    Complex.real_smul, Complex.re_ofReal_mul, Complex.one_re] at h
  rw [← CFC.log] at h
  linarith

end Tree

section Bands

/-- D8.32. `b_{j,g} = b₀ + ½ e^{k a L_{j,g} - k δ}`, `b₀ = (2p)⁻¹`. -/
noncomputable def bLeaf (p a δ : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  (2 * p)⁻¹ + Real.exp (k * a * L - k * δ) / 2

variable {p : ℝ} (hp : 1 ≤ p) (a δ : ℝ) (k : ℕ) (L : ℝ)
include hp

private theorem bLeaf_pos : 0 < bLeaf p a δ k L := by
  unfold bLeaf; have : 0 < p := by linarith
  positivity

/-- D8.33.2. `log b_{j,g} ≥ k a L_{j,g} - k δ - log 2`. -/
private theorem log_bLeaf_ge : k * a * L - k * δ - Real.log 2 ≤ Real.log (bLeaf p a δ k L) := by
  have h0 : 0 < p := by linarith
  have h : Real.exp (k * a * L - k * δ) / 2 ≤ bLeaf p a δ k L := by
    unfold bLeaf; have : 0 < (2 * p)⁻¹ := by positivity
    linarith
  have := Real.log_le_log (by positivity) h
  rwa [Real.log_div (Real.exp_pos _).ne' two_ne_zero, Real.log_exp] at this

/-- D8.33.3. `log b_{j,g} ≥ log b₀`. -/
private theorem log_bLeaf_ge_log : Real.log (2 * p)⁻¹ ≤ Real.log (bLeaf p a δ k L) := by
  have h0 : 0 < p := by linarith
  refine Real.log_le_log (by positivity) ?_
  unfold bLeaf; have := Real.exp_pos (k * a * L - k * δ)
  linarith

/-- D8.33.3. `log (b_{j,g}/b₀) ≤ max(k a L_{j,g} - k δ, 0) + log 2 + log p`. -/
private theorem log_bLeaf_sub_le : Real.log (bLeaf p a δ k L) - Real.log (2 * p)⁻¹ ≤
    max (k * a * L - k * δ) 0 + (Real.log 2 + Real.log p) := by
  have h0 : 0 < p := by linarith
  have hb : bLeaf p a δ k L ≤ Real.exp (max (k * a * L - k * δ) 0) := by
    unfold bLeaf
    have h1 : Real.exp (k * a * L - k * δ) ≤ Real.exp (max (k * a * L - k * δ) 0) :=
      Real.exp_le_exp.mpr (le_max_left _ _)
    have h2 : (1 : ℝ) ≤ Real.exp (max (k * a * L - k * δ) 0) :=
      Real.one_le_exp (le_max_right _ _)
    have h3 : (2 * p)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left zero_le_one two_pos (by linarith)
    linarith
  have := Real.log_le_log (bLeaf_pos hp a δ k L) hb
  rw [Real.log_exp] at this
  rw [Real.log_inv, Real.log_mul two_ne_zero h0.ne']
  linarith

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {d : ℕ}
  {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St] {X : Finset σ}

/-- D8.33.
$$\mathcal M_g\ge b_0(1-\Pi)+e^{\ell_g}\Pi,\quad\ell_g=\sum_jw_j\log b_{j,g},$$
$$\ell_g\ge ka\sum_jw_jL_{j,g}-o(k),\qquad0\le\ell_g-\log b_0\le ka\max_j(L_{j,g})_++o(k),$$
uniformly in the probabilities. -/
theorem step_8_33 (Γ : Statuses σ K St X) (T : Transport.MeanTree St) (t : ℝ) (g : Fin K)
    {P : Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ}
    (hP : IsStarProjection P) (L : St → ℝ)
    (hA : ∀ s, (2 * p)⁻¹ • (1 - P) + bLeaf p a δ k (L s) • P ≤ Γ.bandA n d t k s g) :
    (2 * p)⁻¹ • (1 - P) +
        Real.exp (∑ s, T.weight s * Real.log (bLeaf p a δ k (L s))) • P ≤
      Γ.bandRoot n d T t k g ∧
    k * a * ∑ s, T.weight s * L s - k * δ - Real.log 2 ≤
      ∑ s, T.weight s * Real.log (bLeaf p a δ k (L s)) ∧
    Real.log (2 * p)⁻¹ ≤ ∑ s, T.weight s * Real.log (bLeaf p a δ k (L s)) ∧
    ∀ Λ : ℝ, 0 ≤ Λ → 0 ≤ a → (∀ s, T.weight s ≠ 0 → L s ≤ Λ) →
      ∑ s, T.weight s * Real.log (bLeaf p a δ k (L s)) - Real.log (2 * p)⁻¹ ≤
        k * a * Λ + (Real.log 2 + Real.log p + k * |δ|) := by
  have h0 : 0 < p := by linarith
  have hw := T.weight_nonneg
  have hw1 := T.sum_weight
  -- D8.33.1: monotonicity and homogeneity of the tree
  have h1 := projSector_le_eval hP (by positivity : (0 : ℝ) < (2 * p)⁻¹)
    (μ := fun s => Real.log (bLeaf p a δ k (L s))) (A := fun s => Γ.bandA n d t k s g)
    (fun s => by rw [Real.exp_log (bLeaf_pos hp a δ k (L s))]; exact hA s) T
  -- D8.33.2: `b_{j,g} ≥ ½ e^{k a L_{j,g} - k δ}`
  have h2 : k * a * ∑ s, T.weight s * L s - k * δ - Real.log 2 ≤
      ∑ s, T.weight s * Real.log (bLeaf p a δ k (L s)) := by
    calc k * a * ∑ s, T.weight s * L s - k * δ - Real.log 2
        = ∑ s, T.weight s * (k * a * L s - k * δ - Real.log 2) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, Finset.mul_sum]
          ring_nf
      _ ≤ _ := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (log_bLeaf_ge hp a δ k (L s)) (hw s)
  -- D8.33.3: `b_{j,g} ≥ b₀`, and `log (b_{j,g}/b₀) ≤ log 2 + max(k a L_{j,g}, 0) + O(log k)`
  have hsub : ∑ s, T.weight s * Real.log (bLeaf p a δ k (L s)) - Real.log (2 * p)⁻¹ =
      ∑ s, T.weight s * (Real.log (bLeaf p a δ k (L s)) - Real.log (2 * p)⁻¹) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  have h3 : Real.log (2 * p)⁻¹ ≤ ∑ s, T.weight s * Real.log (bLeaf p a δ k (L s)) := by
    have : 0 ≤ ∑ s, T.weight s * (Real.log (bLeaf p a δ k (L s)) - Real.log (2 * p)⁻¹) :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (hw s) (sub_nonneg.mpr (log_bLeaf_ge_log hp a δ k (L s)))
    linarith
  refine ⟨h1, h2, h3, fun Λ hΛ ha hL => ?_⟩
  rw [hsub]
  calc ∑ s, T.weight s * (Real.log (bLeaf p a δ k (L s)) - Real.log (2 * p)⁻¹)
      ≤ ∑ s, T.weight s * (k * a * Λ + (Real.log 2 + Real.log p + k * |δ|)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rcases eq_or_ne (T.weight s) 0 with h | h
        · simp [h]
        refine mul_le_mul_of_nonneg_left ((log_bLeaf_sub_le hp a δ k (L s)).trans ?_) (hw s)
        have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
        have hz : k * a * L s - k * δ ≤ k * a * Λ + k * |δ| := by
          have := mul_le_mul_of_nonneg_left (hL s h) (mul_nonneg hk0 ha)
          have := mul_le_mul_of_nonneg_left (neg_le_abs δ) hk0
          nlinarith
        have : 0 ≤ k * a * Λ + k * |δ| := by positivity
        have := max_le hz this
        linarith
    _ = k * a * Λ + (Real.log 2 + Real.log p + k * |δ|) := by
        rw [← Finset.sum_mul, hw1, one_mul]

end Bands

section LogLower

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n} {X : Finset σ}
  {E : TypicalSet D X} {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]

/-- D8.34 (`comparator:tree-log-lower`).
$$\langle v,\log\mathcal M_gv\rangle\ge ka\Big[\sum_jw_jL_{j,g}-\frac{E_{\rm def}}\tau
\max_j(L_{j,g})_+\Big]-o(k).$$
Rough: `max_j (L_{j,g})_+ ≤ 2S'`. Sharp: `≤ 2S' + g_max`. -/
theorem step_8_34 (Γ : Statuses σ K St X) (T : Transport.MeanTree St) {a τ : ℝ} (ha : 0 < a)
    (hτ : 0 < τ) {k : ℕ} (hk : 0 < k) (l : IrrepLabel (Equiv.Perm (Fin k))) (g : Fin K)
    {p δ : ℝ} (hp : 1 ≤ p) (L : St → ℝ)
    (hA : ∀ s, (2 * p)⁻¹ • (1 - lowProj D E.d τ k l) + bLeaf p a δ k (L s) • lowProj D E.d τ k l ≤
      Γ.bandA n E.d (a / 2) k s g)
    (hv : star (vec D Γ E T a k l) ⬝ᵥ vec D Γ E T a k l = 1)
    (hsec : sector E.d k l *ᵥ vec D Γ E T a k l = vec D Γ E T a k l)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hL : ∀ s, T.weight s ≠ 0 → L s ≤ Λ) :
    k * a * (∑ s, T.weight s * L s - Edef D Γ E T a k l / τ * Λ) -
        (k * δ + k * |δ| + 2 * Real.log 2 + Real.log p) ≤
      (star (vec D Γ E T a k l) ⬝ᵥ
        (CFC.log (Γ.bandRoot n E.d T (a / 2) k g) *ᵥ vec D Γ E T a k l)).re := by
  set v := vec D Γ E T a k l
  set P := lowProj D E.d τ k l
  have hP := isStarProjection_lowProj D E.d τ k l
  have h0 : 0 < p := by linarith
  obtain ⟨h1, h2, -, h4⟩ := step_8_33 hp a δ k Γ T (a / 2) g hP L hA
  set ℓ := ∑ s, T.weight s * Real.log (bLeaf p a δ k (L s))
  have h4' := h4 Λ hΛ ha.le hL
  -- D8.34.1: `log 𝓜_g ≥ log b₀ (1 - Π) + ℓ_g Π`
  have hlog := re_dotProduct_log_ge hP (by positivity) h1 hv
  -- D8.23: `⟨v, Π v⟩ ≥ 1 - E_def/τ` (`v` lies in the sector)
  have hπ : 1 - Edef D Γ E T a k l / τ ≤ (star v ⬝ᵥ (P *ᵥ v)).re := by
    have h := (step_8_23 D E.d hτ hk).2.1 v hv
    have hPv : P *ᵥ v = defectProj D E.d τ k *ᵥ v := by
      simp only [P, lowProj, ← mulVec_mulVec, hsec]
    rw [hPv]
    exact h
  have hπ1 : (star v ⬝ᵥ (P *ᵥ v)).re ≤ 1 := by
    have h := (nonneg_iff_posSemidef.mp hP.one_sub.nonneg).re_dotProduct_nonneg v
    simp only [sub_mulVec, one_mulVec, dotProduct_sub, hv, RCLike.re_to_complex,
      Complex.sub_re, Complex.one_re] at h
    linarith
  -- D8.34.2: `⟨v, log 𝓜_g v⟩ ≥ ℓ_g - (ℓ_g - log b₀) min(1, E_def/τ)`
  set μ := 1 - (star v ⬝ᵥ (P *ᵥ v)).re
  have hμ0 : 0 ≤ μ := by simp only [μ]; linarith
  have hμε : μ ≤ Edef D Γ E T a k l / τ := by simp only [μ]; linarith
  have hμ1 : μ ≤ 1 := by
    have := (nonneg_iff_posSemidef.mp hP.nonneg).re_dotProduct_nonneg v
    simp only [μ, RCLike.re_to_complex] at this ⊢
    linarith
  -- D8.33: `ℓ_g ≥ k a ∑ w L - o(k)` and `ℓ_g - log b₀ ≤ k a Λ + o(k)`
  have hE' : 0 ≤ Real.log 2 + Real.log p + k * |δ| := by
    have := Real.log_nonneg hp
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hkaΛ : 0 ≤ k * a * Λ := by positivity
  -- D8.34.3: insert D8.33, weaken `min(1, E_def/τ)` to `E_def/τ`
  have e1 : (ℓ - Real.log (2 * p)⁻¹) * μ ≤
      (k * a * Λ + (Real.log 2 + Real.log p + k * |δ|)) * μ :=
    mul_le_mul_of_nonneg_right h4' hμ0
  have e2 : (k * a * Λ + (Real.log 2 + Real.log p + k * |δ|)) * μ ≤
      k * a * Λ * (Edef D Γ E T a k l / τ) + (Real.log 2 + Real.log p + k * |δ|) := by
    have := mul_le_mul_of_nonneg_left hμε hkaΛ
    have := mul_le_mul_of_nonneg_left hμ1 hE'
    nlinarith
  have e3 : Real.log (2 * p)⁻¹ + (ℓ - Real.log (2 * p)⁻¹) * (star v ⬝ᵥ (P *ᵥ v)).re =
      ℓ - (ℓ - Real.log (2 * p)⁻¹) * μ := by simp only [μ]; ring
  nlinarith

end LogLower

/-! ## The filtered vector -/

section Filtered

open Matrix.Transport

variable {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix m m ℂ} (hM : M.PosDef)
  {pre : m → ℂ}
include hM

/-- D8.35.1. `N² ⟨v, 𝓜^{2s} v⟩ = ‖𝓜^{s}(N v)‖² = ‖pre‖²`. -/
private theorem filteredNormSq_mul_re_rpow_half (hpre : pre ≠ 0) :
    filteredNormSq M pre *
        (star (filteredVector M pre) ⬝ᵥ (M ^ (1 / 2 : ℝ) *ᵥ filteredVector M pre)).re =
      (star pre ⬝ᵥ pre).re := by
  have hN := filteredNormSq_pos hM hpre
  have hraw : star (filteredRaw M pre) ⬝ᵥ (M ^ (1 / 2 : ℝ) *ᵥ filteredRaw M pre) =
      star pre ⬝ᵥ pre := by
    rw [filteredRaw, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
      ← star_eq_conjTranspose, hM.star_rpow, hM.rpow_mul_rpow, hM.rpow_mul_rpow]
    norm_num [hM.rpow_zero]
  have hs : ((Real.sqrt (filteredNormSq M pre) : ℂ))⁻¹ =
      (((Real.sqrt (filteredNormSq M pre))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [filteredVector, hs, mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, hraw,
    Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul, ← mul_inv, ← sq, Real.sq_sqrt hN.le,
    ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]

/-- D8.35.2. `-log N² ≥ log ⟨v, 𝓜^{2s} v⟩ ≥ 2s ⟨v, log 𝓜 v⟩` (convexity of `exp`), `s = 1/4`,
for `‖pre‖ ≤ 1`. -/
private theorem half_re_log_le_neg_log_filteredNormSq (hpre : pre ≠ 0)
    (hnorm : (star pre ⬝ᵥ pre).re ≤ 1) :
    2 * (1 / 4) * (star (filteredVector M pre) ⬝ᵥ (CFC.log M *ᵥ filteredVector M pre)).re ≤
      -Real.log (filteredNormSq M pre) := by
  have hN := filteredNormSq_pos hM hpre
  have hJ := hM.exp_mul_re_dotProduct_log_le (2 * (1 / 4))
    (star_dotProduct_filteredVector hM hpre)
  have h1 := filteredNormSq_mul_re_rpow_half hM hpre
  have h2 : (star (filteredVector M pre) ⬝ᵥ (M ^ (1 / 2 : ℝ) *ᵥ filteredVector M pre)).re ≤
      (filteredNormSq M pre)⁻¹ := by
    calc (star (filteredVector M pre) ⬝ᵥ (M ^ (1 / 2 : ℝ) *ᵥ filteredVector M pre)).re
        = (filteredNormSq M pre)⁻¹ * (filteredNormSq M pre *
            (star (filteredVector M pre) ⬝ᵥ (M ^ (1 / 2 : ℝ) *ᵥ filteredVector M pre)).re) := by
          rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
      _ ≤ (filteredNormSq M pre)⁻¹ * 1 := by
          rw [h1]; exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hN.le)
      _ = (filteredNormSq M pre)⁻¹ := mul_one _
  rw [show (2 * (1 / 4) : ℝ) = 1 / 2 by norm_num] at hJ
  have := Real.log_le_log (Real.exp_pos _) (hJ.trans h2)
  rw [Real.log_exp, Real.log_inv] at this
  linarith

end Filtered

/-! ## The root, the sector and `E_def` -/

section Root

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] {d : ℕ}
  [NeZero d] {K : ℕ} {St : Type v} {X : Finset σ}

private theorem Statuses.posDef_bandA (Γ : Statuses σ K St X) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (s : St)
    (g : Fin K) : (Γ.bandA n d t k s g).PosDef :=
  Transport.posDef_bandMetric (Γ.isPartition_part s g) ht k

variable (h1 : Step_8_1.{u, v})
include h1

private theorem Statuses.posDef_leafA (Γ : Statuses σ K St X) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (s : St) :
    (Γ.leafA n d t k s).PosDef :=
  PosDef.listProd_ofFn (fun g => Γ.posDef_bandA ht k s g)
    fun g g' hgg' => (h1 Γ).2 n d t ht k s s g g' hgg'

private theorem Statuses.posDef_root (Γ : Statuses σ K St X) (T : Transport.MeanTree St) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) : (Γ.root n d T t k).PosDef :=
  Transport.MeanTree.posDef_eval (fun s => Γ.posDef_leafA h1 ht k s) T

private theorem Statuses.commute_Pi_root (Γ : Statuses σ K St X) (T : Transport.MeanTree St) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) : Commute (Transport.Pi (dims n d) k) (Γ.root n d T t k) :=
  Transport.MeanTree.commute_eval_right (fun s => Γ.posDef_leafA h1 ht k s)
    (fun s => Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact Transport.commute_Pi_bandMetric t k _) T

/-- D8.7 (`Lemma 7.1 (6)`). `log 𝓜 = ∑_g log 𝓜_g`. -/
private theorem Statuses.log_root (Γ : Statuses σ K St X) (T : Transport.MeanTree St) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) :
    CFC.log (Γ.root n d T t k) = ∑ g, CFC.log (Γ.bandRoot n d T t k g) := by
  have h := Transport.lemma_7_1_6 (D := fun s g => Γ.bandA n d t k s g)
    (fun s g => Γ.posDef_bandA ht k s g)
    (fun s s' g g' hgg' => (h1 Γ).2 n d t ht k s s' g g' hgg') T
  rw [Statuses.root, show Γ.leafA n d t k = fun s => (List.ofFn fun g => Γ.bandA n d t k s g).prod
    from rfl, h.1]
  exact cfc_log_listProd_ofFn
    (fun g => Transport.MeanTree.posDef_eval (fun s => Γ.posDef_bandA ht k s g) T) h.2

end Root

section Sector

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  {D : PhysData n} {X : Finset σ} {E : TypicalSet D X} {K : ℕ} {St : Type v}
  (h1 : Step_8_1.{u, v}) (h13 : Step_8_13.{u, v})
  {l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))} (hl : HighLabel E l)
include h1 h13 hl

omit h1 in
/-- D8.13. `pre_k` lies in the auxiliary sector. -/
private theorem sector_mulVec_pre (k : ℕ) :
    sector E.d k (l k) *ᵥ pre D E.d k (l k) = pre D E.d k (l k) := by
  obtain ⟨hS, -, -, -, hC, hR, -⟩ := h13 D E l hl k
  have hP : Transport.Pi (dims n E.d) k *ᵥ pre D E.d k (l k) = pre D E.d k (l k) := by
    rw [Transport.Pi_eq_projS]
    exact symProj_mulVec_of_mem _ hS
  rw [sector, ← mulVec_mulVec, ← mulVec_mulVec, hP, hR, hC]

/-- D8.13, D8.34. `v = 𝓜^{-s} pre_k / N` is a unit vector in the auxiliary sector. -/
private theorem vec_props [Finite St] (Γ : Statuses σ K St X) (T : Transport.MeanTree St) {a : ℝ}
    (ha : 0 ≤ a) (k : ℕ) :
    0 < N2 D Γ E T a k (l k) ∧
    star (vec D Γ E T a k (l k)) ⬝ᵥ vec D Γ E T a k (l k) = 1 ∧
    sector E.d k (l k) *ᵥ vec D Γ E T a k (l k) = vec D Γ E T a k (l k) ∧
    2 * (1 / 4) * (star (vec D Γ E T a k (l k)) ⬝ᵥ
        (CFC.log (Γ.root n E.d T (a / 2) k) *ᵥ vec D Γ E T a k (l k))).re ≤
      -Real.log (N2 D Γ E T a k (l k)) := by
  obtain ⟨-, hpre, hnorm, -, -, -, hcomm⟩ := h13 D E l hl k
  have ht : 0 ≤ a / 2 := by positivity
  have hM := Γ.posDef_root (n := n) (d := E.d) h1 T ht k
  have := Fintype.ofFinite St
  classical
  obtain ⟨-, hroot⟩ := hcomm Γ (a / 2) ht
  obtain ⟨hMC, hMR⟩ := hroot T
  have hMS : Commute (Γ.root n E.d T (a / 2) k) (sector E.d k (l k)) :=
    (hMC.mul_right hMR).mul_right (Γ.commute_Pi_root (n := n) (d := E.d) h1 T ht k).symm
  refine ⟨Matrix.Transport.filteredNormSq_pos hM hpre,
    Matrix.Transport.star_dotProduct_filteredVector hM hpre, ?_,
    half_re_log_le_neg_log_filteredNormSq hM hpre hnorm⟩
  have hR : Commute (Γ.root n E.d T (a / 2) k ^ (-(1 / 4) : ℝ)) (sector E.d k (l k)) :=
    hM.commute_rpow_left hMS _
  rw [vec, Matrix.Transport.filteredVector, Matrix.Transport.filteredRaw, mulVec_smul,
    mulVec_mulVec, ← hR.eq, ← mulVec_mulVec, sector_mulVec_pre h13 hl]

end Sector

section Edef

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n} {X : Finset σ}
  {E : TypicalSet D X} {K : ℕ} {St : Type v}

private theorem Hbar_zero (d : ℕ) : Hbar D d 0 = 0 := by
  simp [Hbar, TensorPower.copyMean]

/-- At `k = 0` the mean energy is `0`: `E_def = -Ẽ₀/g̃` for every tree. -/
private theorem Edef_zero (Γ : Statuses σ K St X) (T : Transport.MeanTree St) (a : ℝ)
    (l : IrrepLabel (Equiv.Perm (Fin 0))) : Edef D Γ E T a 0 l = -D.E₀ / D.g := by
  simp [Edef, Hbar_zero]

/-- D8.23.1. `E_def ≥ 0` for a unit `v` and `k ≥ 1`. -/
private theorem Edef_nonneg (Γ : Statuses σ K St X) (T : Transport.MeanTree St) (a : ℝ) {k : ℕ}
    (hk : 0 < k) (l : IrrepLabel (Equiv.Perm (Fin k)))
    (hv : star (vec D Γ E T a k l) ⬝ᵥ vec D Γ E T a k l = 1) : 0 ≤ Edef D Γ E T a k l := by
  set v := vec D Γ E T a k l
  have hQ : (∑ i : Fin k, TensorPower.siteOp i (excProj D E.d)).PosSemidef :=
    posSemidef_sum _ fun i _ =>
      PosSemidef.siteOp (nonneg_iff_posSemidef.mp (isStarProjection_excProj E.d D).nonneg) i
  have hq := (Matrix.le_iff.mp (gap_Hbar D E.d hk)).re_dotProduct_nonneg v
  have hq' := hQ.re_dotProduct_nonneg v
  simp only [RCLike.re_to_complex, sub_mulVec, dotProduct_sub, Complex.sub_re,
    smul_mulVec, dotProduct_smul, smul_eq_mul, one_mulVec, hv, Complex.re_ofReal_mul, mul_one,
    Complex.ofReal_re] at hq hq'
  have hg := D.gap_pos
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have : 0 ≤ D.g / k * (star v ⬝ᵥ ((∑ i, TensorPower.siteOp i (excProj D E.d)) *ᵥ v)).re :=
    mul_nonneg (by positivity) hq'
  exact div_nonneg (by linarith) hg.le

end Edef

/-! ## D8.35 The two lower bounds -/

section Proof

/-- The remainder `(K/2) (δ_k + |δ_k| + (2 log 2 + C log (k + 2))/k) → 0`. -/
private theorem tendsto_lower_remainder {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (C K : ℝ) :
    Tendsto (fun k : ℕ => K / 2 * (δ k + |δ k| + (2 * Real.log 2 + C * Real.log ((k : ℝ) + 2)) /
      k)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2) / k) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    refine h.congr fun k => ?_
    simp only [Function.comp, pow_one, one_mul]
    ring_nf
  have hinv : Tendsto (fun k : ℕ => 1 / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h := (((hδ.add hδ.abs).add ((hinv.const_mul (2 * Real.log 2)).add
    (hlog.const_mul C))).const_mul (K / 2))
  simp only [abs_zero, add_zero, mul_zero] at h
  refine h.congr fun k => ?_
  rw [add_div]
  ring

private theorem S'_nonneg {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n}
    {X : Finset σ} (E : TypicalSet D X) : 0 ≤ E.S' := by
  have hp : ∀ i ∈ E.E, 0 < D.p X i := fun i hi => (Real.exp_pos _).trans_le (E.lower i hi)
  have hz : 0 < E.z := Finset.sum_pos hp E.nonempty
  refine Finset.sum_nonneg fun i hi => Real.negMulLog_nonneg (div_nonneg (hp i hi).le hz.le) ?_
  rw [TypicalSet.p', div_le_one hz]
  exact Finset.single_le_sum (fun j hj => (hp j hj).le) hi

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  {D : PhysData n} {X : Finset σ} {E : TypicalSet D X} {K : ℕ} {St : Type v} [Fintype St]
  [DecidableEq St]

/-- D8.35.1–3 for a lower pin `A_{j,g} ≥ e^{k a L_{j,g} - k δ_k} Π`: for `k ≥ 1` and
`Λ_g ≥ (L_{j,g})_+` on the leaves of positive weight,
`-log N²/k ≥ (a/2) ∑_g [∑_j w_j L_{j,g} - (E_def/τ) Λ_g] - (K/2) ρ_k`,
`ρ_k = δ_k + |δ_k| + (2 log 2 + C log (k + 2))/k`; and `E_def ≥ 0`. -/
private theorem lower_of_pin (h1 : Step_8_1.{u, v}) (h13 : Step_8_13.{u, v}) (Γ : Statuses σ K St X)
    {l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))} (hl : HighLabel E l) {a τ : ℝ} (ha : 0 < a)
    (hτ : 0 < τ) (L : St → Fin K → ℝ) (δ : ℕ → ℝ)
    (hpin : ∀ (k : ℕ) (s : St) (g : Fin K), Real.exp (k * a * L s g - k * δ k) •
      lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 0 < k → ∀ (T : Transport.MeanTree St) (Λ : Fin K → ℝ),
      (∀ g, 0 ≤ Λ g) → (∀ s g, T.weight s ≠ 0 → L s g ≤ Λ g) →
      0 ≤ Edef D Γ E T a k (l k) ∧
      a / 2 * ∑ g, (∑ s, T.weight s * L s g - Edef D Γ E T a k (l k) / τ * Λ g) -
          K / 2 * (δ k + |δ k| + (2 * Real.log 2 + C * Real.log ((k : ℝ) + 2)) / k) ≤
        -Real.log (N2 D Γ E T a k (l k)) / k := by
  obtain ⟨C, hC, hfl⟩ := step_8_32 (n := n) E.d Γ (t := a / 2) (by positivity)
  refine ⟨C, hC, fun k hk T Λ hΛ hL => ?_⟩
  set p : ℝ := ((k : ℝ) + 2) ^ C with hpdef
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [k.cast_nonneg (α := ℝ)]
  have hp : 1 ≤ p := Real.one_le_rpow hk1 hC
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  obtain ⟨-, hv, hsec, hJ⟩ := vec_props h1 h13 hl Γ T ha.le k
  have hE := Edef_nonneg Γ T a hk (l k) hv
  set v := vec D Γ E T a k (l k)
  -- D8.32: the block lower bound at every leaf
  have hA : ∀ g s, (2 * p)⁻¹ • (1 - lowProj D E.d τ k (l k)) +
      bLeaf p a (δ k) k (L s g) • lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g :=
    fun g s => (hfl k s g).2 _ _ (isStarProjection_lowProj D E.d τ k (l k)) (Real.exp_pos _)
      (hpin k s g)
  -- D8.34 for each band
  have hband : ∀ g, k * a * (∑ s, T.weight s * L s g - Edef D Γ E T a k (l k) / τ * Λ g) -
      (k * δ k + k * |δ k| + 2 * Real.log 2 + Real.log p) ≤
      (star v ⬝ᵥ (CFC.log (Γ.bandRoot n E.d T (a / 2) k g) *ᵥ v)).re := fun g =>
    step_8_34 Γ T ha hτ hk (l k) g hp (fun s => L s g) (hA g) hv hsec (hΛ g) fun s => hL s g
  -- D8.35.3: `log 𝓜 = ∑_g log 𝓜_g`
  have hsum : (star v ⬝ᵥ (CFC.log (Γ.root n E.d T (a / 2) k) *ᵥ v)).re =
      ∑ g, (star v ⬝ᵥ (CFC.log (Γ.bandRoot n E.d T (a / 2) k g) *ᵥ v)).re := by
    rw [Γ.log_root h1 T (by positivity) k, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  have hlogp : Real.log p = C * Real.log ((k : ℝ) + 2) := Real.log_rpow (by linarith) C
  have hsumb := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hband g
  rw [← hsum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hlogp] at hsumb
  refine ⟨hE, ?_⟩
  -- D8.35.4: divide by `k`
  have hrem : (δ k + |δ k| + (2 * Real.log 2 + C * Real.log ((k : ℝ) + 2)) / k) * k =
      k * δ k + k * |δ k| + 2 * Real.log 2 + C * Real.log ((k : ℝ) + 2) := by
    field_simp
    ring
  rw [le_div_iff₀ hkR]
  calc (a / 2 * ∑ g, (∑ s, T.weight s * L s g - Edef D Γ E T a k (l k) / τ * Λ g) -
        K / 2 * (δ k + |δ k| + (2 * Real.log 2 + C * Real.log ((k : ℝ) + 2)) / k)) * k
      = 1 / 2 * (k * a * ∑ g, (∑ s, T.weight s * L s g - Edef D Γ E T a k (l k) / τ * Λ g) -
          K * (k * δ k + k * |δ k| + 2 * Real.log 2 + C * Real.log ((k : ℝ) + 2))) := by
        rw [sub_mul, mul_assoc (K / 2 : ℝ), hrem]
        ring
    _ ≤ 1 / 2 * (star v ⬝ᵥ (CFC.log (Γ.root n E.d T (a / 2) k) *ᵥ v)).re := by linarith
    _ ≤ -Real.log (N2 D Γ E T a k (l k)) := by linarith

end Proof

section Assembly

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  {D : PhysData n} {X : Finset σ} {E : TypicalSet D X} {K : ℕ} {St : Type v} [Fintype St]
  [DecidableEq St]

omit [∀ v, NeZero (n v)] in
private theorem log_d_nonneg (E : TypicalSet D X) : 0 ≤ Real.log E.d :=
  Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne E.d))

/-- D8.35 (rough): from the rough lower pin of D8.31 with constant `C₃₁`, the rough lower bound
with constant `max C₃₁ 2`. -/
private theorem roughLower_of_pin (h1 : Step_8_1.{u, v}) (h13 : Step_8_13.{u, v})
    (Γ : Statuses σ K St X)
    {l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))} (hl : HighLabel E l) {a τ C₃₁ : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hτ' : τ < 1 / 2) (hC₃₁ : 0 < C₃₁) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    (hpin : ∀ (k : ℕ) (s : St) (g : Fin K),
      Real.exp (k * a * (2 * E.S' - C₃₁ * (τ * Real.log E.d + Real.binEntropy τ / a)) -
        k * δ k) • lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g) :
    RoughLower D Γ E (max C₃₁ 2) a τ l := by
  set C := max C₃₁ 2
  set B := τ * Real.log E.d + Real.binEntropy τ / a
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hτ.le (log_d_nonneg E))
    (div_nonneg (Real.binEntropy_nonneg hτ.le (by linarith)) ha.le)
  have hS := S'_nonneg E
  set L₀ := 2 * E.S' - C₃₁ * B
  obtain ⟨Cf, -, hcore⟩ := lower_of_pin h1 h13 Γ hl ha hτ (fun _ _ => L₀) δ hpin
  set c₀ := 2 * (1 / 4) * (a * K) * (2 * E.S' - C * B - C * (-D.E₀ / D.g / τ) * E.S')
  refine ⟨fun k => if k = 0 then c₀ else
    K / 2 * (δ k + |δ k| + (2 * Real.log 2 + Cf * Real.log ((k : ℝ) + 2)) / k), ?_, ?_⟩
  · refine (tendsto_lower_remainder hδ Cf K).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    rw [if_neg hk]
  intro k _ T
  dsimp only
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_pos rfl, Edef_zero, Nat.cast_zero, div_zero, sub_self]
  rw [if_neg hk.ne']
  -- D8.34.4 (rough): `L_{j,g} ≤ 2S'`
  obtain ⟨hE, hineq⟩ := hcore k hk T (fun _ => 2 * E.S') (fun _ => by positivity)
    (fun s g _ => by simp only [L₀]; nlinarith)
  -- D8.35.3: `∑_g ∑_j w_j L_{j,g} = K L`
  have hsig : ∑ g : Fin K, (∑ s, T.weight s * L₀ - Edef D Γ E T a k (l k) / τ * (2 * E.S')) =
      K * (L₀ - Edef D Γ E T a k (l k) / τ * (2 * E.S')) := by
    rw [← Finset.sum_mul, T.sum_weight, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsig] at hineq
  refine le_trans ?_ hineq
  -- D8.35.4: the constant of the `E_def` term is `2`
  have hε : 0 ≤ Edef D Γ E T a k (l k) / τ := div_nonneg hE hτ.le
  have key : C₃₁ * B + 2 * (Edef D Γ E T a k (l k) / τ * E.S') ≤
      C * B + C * (Edef D Γ E T a k (l k) / τ * E.S') :=
    add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hε hS))
  have hK : 0 ≤ a * K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hK]

/-- D8.35 (sharp, `k ≥ 1`): from the sharp lower pin of D8.31 with constant `C'`, the sharp lower
bound with constant `max C' 2`, for every `G ≥ g^pre` of the leaves of positive weight. -/
private theorem sharpLower_of_pin (h1 : Step_8_1.{u, v}) (h13 : Step_8_13.{u, v})
    (Γ : Statuses σ K St X)
    {l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))} (hl : HighLabel E l) {a τ C' 𝓑 : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hτ' : τ < 1 / 2) (hC' : 0 < C') (h𝓑 : 1 ≤ 𝓑) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    (hpin : ∀ (k : ℕ) (s : St) (g : Fin K),
      Real.exp (k * a * (2 * E.S' + (1 - τ) * gpre D Γ s g -
          C' * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑)) - k * δ k) •
        lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k → ∀ (T : Transport.MeanTree St) (G : ℝ),
      (∀ s g, T.weight s ≠ 0 → gpre D Γ s g ≤ G) →
      2 * (1 / 4) * (a * K) * (2 * E.S' + (1 - τ) * avg T (gpre D Γ) -
          max C' 2 * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑) -
          max C' 2 * (Edef D Γ E T a k (l k) / τ) * (E.S' + G)) - r k ≤
        -Real.log (N2 D Γ E T a k (l k)) / k := by
  set C := max C' 2
  set B := τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑
  have hB : 0 ≤ B := add_nonneg (add_nonneg (mul_nonneg hτ.le (log_d_nonneg E))
    (div_nonneg (Real.binEntropy_nonneg hτ.le (by linarith)) ha.le)) (by nlinarith)
  have hS := S'_nonneg E
  set L : St → Fin K → ℝ := fun s g => 2 * E.S' + (1 - τ) * gpre D Γ s g - C' * B
  obtain ⟨Cf, -, hcore⟩ := lower_of_pin h1 h13 Γ hl ha hτ L δ hpin
  refine ⟨fun k => K / 2 * (δ k + |δ k| + (2 * Real.log 2 + Cf * Real.log ((k : ℝ) + 2)) / k),
    tendsto_lower_remainder hδ Cf K, fun k hk T G hG => ?_⟩
  -- `G ≥ 0`: some leaf has positive weight
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := T.weight) (by rw [T.sum_weight]; exact one_ne_zero)
  have hG0 : ∀ g : Fin K, 0 ≤ G := fun g => (gpre_nonneg Γ s₀ g).trans (hG s₀ g hs₀)
  -- D8.34.4 (sharp): `L_{j,g} ≤ 2S' + (1 - τ) g^pre_{j,g} ≤ 2S' + g_max`
  obtain ⟨hE, hineq⟩ := hcore k hk T (fun _ => 2 * E.S' + G) (fun g => by linarith [hG0 g])
    (fun s g hs => by
      have h0 := gpre_nonneg (D := D) Γ s g
      have := hG s g hs
      change 2 * E.S' + (1 - τ) * gpre D Γ s g - C' * B ≤ 2 * E.S' + G
      nlinarith)
  -- D8.35.3: `∑_g ∑_j w_j L_{j,g} = K (2S' - C B) + (1 - τ) K ⟨g^pre⟩_av`
  have hinner : ∀ g, ∑ s, T.weight s * L s g =
      2 * E.S' - C' * B + (1 - τ) * ∑ s, T.weight s * gpre D Γ s g := fun g => by
    calc ∑ s, T.weight s * L s g
        = ∑ s, (T.weight s * (2 * E.S' - C' * B) + (1 - τ) * (T.weight s * gpre D Γ s g)) :=
          Finset.sum_congr rfl fun s _ => by
            change T.weight s * (2 * E.S' + (1 - τ) * gpre D Γ s g - C' * B) = _
            ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, T.sum_weight,
          one_mul]
  have hsig : ∑ g : Fin K, (∑ s, T.weight s * L s g -
        Edef D Γ E T a k (l k) / τ * (2 * E.S' + G)) =
      K * (2 * E.S' - C' * B - Edef D Γ E T a k (l k) / τ * (2 * E.S' + G)) +
        (1 - τ) * ∑ g : Fin K, ∑ s, T.weight s * gpre D Γ s g := by
    simp only [hinner, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have havg : (K : ℝ) * avg T (gpre D Γ) = ∑ g : Fin K, ∑ s, T.weight s * gpre D Γ s g := by
    rcases eq_or_ne K 0 with hK | hK
    · subst hK; simp
    · rw [avg, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hK), one_mul]
  rw [hsig] at hineq
  dsimp only
  refine le_trans ?_ hineq
  -- D8.35.4: the constant of the `E_def` term is `2`, as `2S' + G ≤ 2 (S' + G)`
  have hε : 0 ≤ Edef D Γ E T a k (l k) / τ := div_nonneg hE hτ.le
  have key : (K : ℝ) * (C' * B + Edef D Γ E T a k (l k) / τ * (2 * E.S' + G)) ≤
      K * (C * B + C * (Edef D Γ E T a k (l k) / τ) * (E.S' + G)) := by
    rcases eq_or_ne K 0 with hK | hK
    · subst hK; simp
    · have hG' := hG0 ⟨0, Nat.pos_of_ne_zero hK⟩
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have h2 : Edef D Γ E T a k (l k) / τ * (2 * E.S' + G) ≤
          C * (Edef D Γ E T a k (l k) / τ) * (E.S' + G) := by
        have : 2 * E.S' + G ≤ 2 * (E.S' + G) := by linarith
        have hC2 : (2 : ℝ) ≤ C := le_max_right _ _
        calc Edef D Γ E T a k (l k) / τ * (2 * E.S' + G)
            ≤ Edef D Γ E T a k (l k) / τ * (2 * (E.S' + G)) :=
              mul_le_mul_of_nonneg_left this hε
          _ ≤ Edef D Γ E T a k (l k) / τ * (C * (E.S' + G)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC2 (by linarith)) hε
          _ = _ := by ring
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hB) h2
  have ha2 : 0 ≤ a / 2 := by positivity
  have e : 2 * (1 / 4) * (a * K) * (2 * E.S' + (1 - τ) * avg T (gpre D Γ) - C * B -
      C * (Edef D Γ E T a k (l k) / τ) * (E.S' + G)) =
      a / 2 * (K * (2 * E.S') - K * (C * B + C * (Edef D Γ E T a k (l k) / τ) * (E.S' + G)) +
        (1 - τ) * (K * avg T (gpre D Γ))) := by ring
  have e' : (K : ℝ) * (2 * E.S' - C' * B - Edef D Γ E T a k (l k) / τ * (2 * E.S' + G)) =
      K * (2 * E.S') - K * (C' * B + Edef D Γ E T a k (l k) / τ * (2 * E.S' + G)) := by ring
  rw [e, e', havg]
  refine sub_le_sub_right (mul_le_mul_of_nonneg_left ?_ ha2) _
  linarith

end Assembly

/-- D8.35 (`comparator:rough-lower`, `comparator:sharp-lower`). (comparator:rough-lower) and
(comparator:sharp-lower) of D8.8. -/
theorem step_8_35 (h1 : Step_8_1.{u, v}) (h13 : Step_8_13.{u, v}) (h31 : Step_8_31.{u, v}) :
    Step_8_35.{u, v} := by
  unfold Step_8_35
  obtain ⟨a₀, C₃₁, ha₀, hC₃₁, hR, hS⟩ := h31
  refine ⟨a₀, max C₃₁ 2, ha₀, lt_max_of_lt_left hC₃₁, ?_, ?_⟩
  · intro σ _ _ n _ D X E K St _ _ Γ l hl a τ ha haa hτ hτ'
    -- D8.31 (rough lower pin)
    obtain ⟨δ, hδ, hpin⟩ := hR D E Γ l hl a τ ha haa hτ hτ'
    -- D8.35.1–4
    exact roughLower_of_pin h1 h13 Γ hl ha hτ hτ' hC₃₁ hδ hpin
  · intro C₀ c₀ hC₀ hc₀
    obtain ⟨c, C', hc, hC', hS'⟩ := hS C₀ c₀ hC₀ hc₀
    refine ⟨c, max C' 2, hc, lt_max_of_lt_left hC', ?_⟩
    intro σ _ _ n _ D X E K St _ _ Γ l hl 𝓑 h𝓑 a τ ha hac hτ hτ'
    -- D8.31 (sharp lower pin)
    obtain ⟨δ, hδ, hpin⟩ := hS' D E Γ l hl 𝓑 h𝓑 a τ ha hac hτ hτ'
    -- D8.35.1–4
    exact sharpLower_of_pin h1 h13 Γ hl ha hτ hτ' hC' h𝓑.one_le hδ hpin

end AreaLaw.Comparators
