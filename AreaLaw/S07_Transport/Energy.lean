import AreaLaw.S07_Transport.States
import AreaLawForMathlib.Analysis.Matrix.AdjointLogFunction
import AreaLawForMathlib.Analysis.Matrix.SkewAbsReduction
import AreaLawForMathlib.Analysis.Matrix.GeometricMeanCongruence
import AreaLawForMathlib.Analysis.SpecialFunctions.Pow.RpowNonneg
import AreaLawForMathlib.Topology.Instances.Real.UniformRemainder

/-!
# §7.4 Energy transport (Proposition 7.4 (c))

Digest `digest/07-transport.md` D7.21–D7.25, paper `paper/sections/06-transport.tex` 579–760.
Tensor factors are an arbitrary finite site type `V` with local dimensions `n : V → ℕ`; the
number `k` of copies is arbitrary. No geometry.

`T_i = h̄_i^{1/2}` acts on the whole tensor space, and `B_{i,j}` is a positive definite matrix
on the whole space (`Matrix.auxBlock`), instead of the paper's last-copy map
`T_i : 𝒮_k → 𝒟 = ran T_i` with `B_{i,j}` on `𝒟`; only `T_i^* T_i = h̄_i` is used.

Some declarations here come from the v1 files `OpenAI/BlockDiagonal.lean`,
`OpenAI/Transport/EnergyBlock.lean`, `OpenAI/Transport/ErrorFourier.lean`,
`OpenAI/TreeDerivative.lean`, whose header records them as ported or adapted from `LionSR/QICLean`
(see `NOTICE`).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix MeasureTheory Filter Topology Entropy Arealaw

universe u

namespace AreaLaw.Transport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

namespace EnergyTerms

variable {ι : Type*} (E : EnergyTerms V n ι)

theorem posSemidef_term (i : ι) : (E.term i).PosSemidef := by
  rw [term, Replicas.localLift_eq_extendId]
  exact (posSemidef_extendId _ (Matrix.nonneg_iff_posSemidef.mp (E.nonneg i))).submatrix _

/-- `h̄_i ≥ 0`. -/
theorem posSemidef_hbar (k : ℕ) (i : ι) : (E.hbar k i).PosSemidef := by
  have hh := E.posSemidef_term i
  unfold hbar TensorPower.copyMean
  have hs : ∀ j : Fin k, (TensorPower.siteOp j (E.term i)).PosSemidef := fun j => by
    rw [TensorPower.siteOp_eq_reindex]
    exact (hh.kronecker Matrix.PosSemidef.one).submatrix _
  have hsum := Matrix.posSemidef_sum Finset.univ fun j _ => hs j
  have hc : ((k : ℂ))⁻¹ = (((k : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc]
  exact hsum.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))

end EnergyTerms

/-! ## Mean-tree facts: transport of a commutator -/

namespace MeanTree

variable {J : Type*} [DecidableEq J] [Fintype J] {m : Type*} [Fintype m] [DecidableEq m]

/-- `∑_j ∂_{A_j} M[X^* A_j + A_j X] = X^* M + M X` (congruence covariance along the tree). -/
theorem sum_derivLabel_congr {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef) (T : MeanTree J)
    (X : Matrix m m ℂ) :
    ∑ j, T.derivLabel M j (Xᴴ * M j + M j * X) = Xᴴ * T.eval M + T.eval M * X := by
  induction T with
  | leaf i =>
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [derivLabel, Ne.symm hj]) (by simp)]
    simp [derivLabel]
  | node p l r ihl ihr =>
    simp only [derivLabel, _root_.add_apply, ContinuousLinearMap.comp_apply,
      Finset.sum_add_distrib, ← map_sum, ihl, ihr, eval_node]
    exact geomMeanDeriv_congr (posDef_eval hM l) (posDef_eval hM r) p.2 X

/-- `∑_j ∂_{A_j} M[A_j L - L A_j] = M L - L M` for Hermitian `L`. -/
theorem sum_derivLabel_commutator {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef)
    (T : MeanTree J) {L : Matrix m m ℂ} (hL : L.IsHermitian) :
    ∑ j, T.derivLabel M j (M j * L - L * M j) = T.eval M * L - L * T.eval M := by
  have h := sum_derivLabel_congr hM T (Complex.I • L)
  have hX : (Complex.I • L)ᴴ = -(Complex.I • L) := by
    rw [conjTranspose_smul, hL.eq, Complex.star_def, Complex.conj_I, neg_smul]
  have e : ∀ Y : Matrix m m ℂ, (Complex.I • L)ᴴ * Y + Y * (Complex.I • L) =
      Complex.I • (Y * L - L * Y) := by
    intro Y; rw [hX, smul_sub, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul]; abel
  simp only [e, map_smul, ← Finset.smul_sum] at h
  exact smul_right_injective _ Complex.I_ne_zero h

/-- D7.22.2–D7.22.3. Rotating every input by `e^{itL}` and differentiating at `t = 0`:
`∑_j w_j Φ_j(M_j^{1/2} L M_j^{-1/2} - M_j^{-1/2} L M_j^{1/2}) =
𝕄^{1/2} L 𝕄^{-1/2} - 𝕄^{-1/2} L 𝕄^{1/2}`. -/
theorem sum_weight_smul_leafMap_rotation {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef)
    (T : MeanTree J) (hw : ∀ j, T.weight j ≠ 0) {L : Matrix m m ℂ} (hL : L.IsHermitian) :
    ∑ j, ((T.weight j : ℝ) : ℂ) • T.leafMap M j (M j ^ (1 / 2 : ℝ) * L * M j ^ (-(1 / 2) : ℝ) -
        M j ^ (-(1 / 2) : ℝ) * L * M j ^ (1 / 2 : ℝ)) =
      T.eval M ^ (1 / 2 : ℝ) * L * T.eval M ^ (-(1 / 2) : ℝ) -
        T.eval M ^ (-(1 / 2) : ℝ) * L * T.eval M ^ (1 / 2 : ℝ) := by
  set R := T.eval M
  have hR : R.PosDef := posDef_eval hM T
  have hterm : ∀ j, ((T.weight j : ℝ) : ℂ) • T.leafMap M j (M j ^ (1 / 2 : ℝ) * L *
      M j ^ (-(1 / 2) : ℝ) - M j ^ (-(1 / 2) : ℝ) * L * M j ^ (1 / 2 : ℝ)) =
      R ^ (-(1 / 2) : ℝ) * T.derivLabel M j (M j * L - L * M j) * R ^ (-(1 / 2) : ℝ) := by
    intro j
    have hK : M j ^ (1 / 2 : ℝ) * (M j ^ (1 / 2 : ℝ) * L * M j ^ (-(1 / 2) : ℝ) -
        M j ^ (-(1 / 2) : ℝ) * L * M j ^ (1 / 2 : ℝ)) * M j ^ (1 / 2 : ℝ) = M j * L - L * M j := by
      have h1 := (hM j).rpow_half_mul_rpow_half
      have h2 := (hM j).rpow_mul_rpow_neg (1 / 2)
      have h3 := (hM j).rpow_neg_mul_rpow (1 / 2)
      calc _ = (M j ^ (1 / 2 : ℝ) * M j ^ (1 / 2 : ℝ)) * L *
            (M j ^ (-(1 / 2) : ℝ) * M j ^ (1 / 2 : ℝ)) -
          (M j ^ (1 / 2 : ℝ) * M j ^ (-(1 / 2) : ℝ)) * L *
            (M j ^ (1 / 2 : ℝ) * M j ^ (1 / 2 : ℝ)) := by noncomm_ring
        _ = _ := by rw [h1, h2, h3, Matrix.mul_one, Matrix.one_mul]
    rw [← hK, sandwich_derivLabel_eq_smul_leafMap T (hw j), Complex.coe_smul]
  simp only [hterm, ← Finset.sum_mul, ← Finset.mul_sum, sum_derivLabel_commutator hM T hL]
  have h1 := hR.rpow_half_mul_rpow_half
  have h2 := hR.rpow_mul_rpow_neg (1 / 2)
  have h3 := hR.rpow_neg_mul_rpow (1 / 2)
  calc R ^ (-(1 / 2) : ℝ) * (R * L - L * R) * R ^ (-(1 / 2) : ℝ)
      = R ^ (-(1 / 2) : ℝ) * (R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) * L * R ^ (-(1 / 2) : ℝ) -
        R ^ (-(1 / 2) : ℝ) * L * (R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) * R ^ (-(1 / 2) : ℝ) := by
        rw [h1]; noncomm_ring
    _ = (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) * R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) -
        R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ) * (R ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)) := by
        noncomm_ring
    _ = _ := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

omit [Fintype J] in
/-- D7.5: the normalized leaf map of a leaf of positive weight is unital. -/
theorem leafMap_one {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef) (T : MeanTree J) {j : J}
    (hw : 0 < T.weight j) : T.leafMap M j 1 = 1 :=
  normalizedDerivMap_one hw.ne' (posDef_eval hM T) (hM j) (derivLabel_self hM T j)

omit [Fintype J] in
/-- D7.5: the normalized leaf maps are completely positive. -/
theorem isNPositiveMap_leafMap {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef) (T : MeanTree J)
    (j : J) (k : ℕ) : IsNPositiveMap k (T.leafMap M j).toLinearMap :=
  isNPositiveMap_normalizedDerivMap (isNPositiveMap_derivLabel hM T j k) (T.weight_nonneg j)
    (posDef_eval hM T) (hM j)

omit [Fintype J] in
/-- D7.5.7 (block clause of Lemma 7.2): with block-diagonal inputs the normalized leaf maps
preserve the blocks, with first-block restriction the leaf map of the first blocks. -/
theorem isBlockDiagonalMap_leafMap {M : J → Matrix m m ℂ} {B : J → Matrix m m ℂ}
    (hM : ∀ j, (M j).PosDef) (hB : ∀ j, (B j).PosDef) (T : MeanTree J) (j : J) :
    IsBlockDiagonalMap (T.leafMap (fun i ↦ fromBlocks (M i) 0 0 (B i)) j)
      (T.leafMap M j) (T.leafMap B j) := by
  unfold MeanTree.leafMap
  rw [eval_fromBlocks_diag hM hB T]
  exact (isBlockDiagonalMap_derivLabel hM hB T j).normalizedDerivMap _ (posDef_eval hM T)
    (posDef_eval hB T) (hM j) (hB j)

end MeanTree

/-! ## D7.21 The auxiliary positive metric -/

namespace Round

variable {K : ℕ} {H : Type*} {C : H → Type*} (R : Round V K H C) {ι : Type*}

theorem root_eq_eval (t : ℝ) (k : ℕ) (p : I) :
    R.root n t k p = (R.tree p).eval (R.input n t k) := by
  simp only [root, Set.projIcc_val zero_le_one p]

/-- D7.21. `O_{i,j} = A_j^{-1/2} h̄_i A_j^{1/2}`. -/
noncomputable def simil (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    Matrix (Config n k) (Config n k) ℂ :=
  R.input n t k j ^ (-(1 / 2) : ℝ) * E.hbar k i * R.input n t k j ^ (1 / 2 : ℝ)

/-- D7.21. The auxiliary positive metric `B_{i,j}`. -/
noncomputable def auxMetric (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    Matrix (Config n k) (Config n k) ℂ :=
  Matrix.auxBlock (R.input n t k j) (E.hbar k i)

/-- D7.21. `Y_{i,j} = B_{i,j}^{1/2} T_i A_j^{-1/2}`, `T_i = h̄_i^{1/2}`. -/
noncomputable def mapY (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    Matrix (Config n k) (Config n k) ℂ :=
  Matrix.auxY (R.input n t k j) (R.auxMetric t k E i j) (E.hbar k i)

/-- D7.21. `Z_{i,j} = B_{i,j}^{-1/2} T_i A_j^{1/2}`, `T_i = h̄_i^{1/2}`. -/
noncomputable def mapZ (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    Matrix (Config n k) (Config n k) ℂ :=
  Matrix.auxZ (R.input n t k j) (R.auxMetric t k E i j) (E.hbar k i)

/-- D7.21. `𝖣_{i,j} = |O_{i,j}^*| + |O_{i,j}| - O_{i,j} - O_{i,j}^*`. -/
noncomputable def skew (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    Matrix (Config n k) (Config n k) ℂ :=
  skewAbs (R.simil t k E i j)

variable [∀ v, NeZero (n v)] [DecidableEq H] [∀ h, DecidableEq (C h)]

/-- D7.21 (auxiliary positive metric). For each `i` and each leaf `j` there are a positive
definite `B_{i,j}` and maps `Y_{i,j}, Z_{i,j}` (here on the whole tensor space, with
`T_i = h̄_i^{1/2}`, `T_i^* T_i = h̄_i`) with `Y_{i,j}^* Z_{i,j} = O_{i,j}` and
`𝖣_{i,j} := (Y_{i,j} - Z_{i,j})^*(Y_{i,j} - Z_{i,j}) = |O_{i,j}^*| + |O_{i,j}| - O_{i,j} -
O_{i,j}^* ≥ 0`, `O_{i,j} = A_j^{-1/2} h̄_i A_j^{1/2}`. `𝖣_{i,j} = 0` (`Y = Z`) when
`[A_j, h̄_i] = 0`, in particular at unsplit leaves. -/
theorem step_7_21 (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    (CFC.sqrt (E.hbar k i))ᴴ * CFC.sqrt (E.hbar k i) = E.hbar k i ∧
    (R.auxMetric t k E i j).PosDef ∧
    (R.mapY t k E i j)ᴴ * R.mapZ t k E i j = R.simil t k E i j ∧
    (R.mapY t k E i j - R.mapZ t k E i j)ᴴ * (R.mapY t k E i j - R.mapZ t k E i j) =
      R.skew t k E i j ∧
    (R.skew t k E i j).PosSemidef ∧
    (Commute (R.input n t k j) (E.hbar k i) → R.mapY t k E i j = R.mapZ t k E i j) ∧
    ((∀ g, (R.leafPart j g).Contains (E.support i)) → R.mapY t k E i j = R.mapZ t k E i j) := by
  have hA : (R.input n t k j).PosDef := R.posDef_input hR ht hcomm j
  have hh : (E.hbar k i).PosSemidef := E.posSemidef_hbar k i
  -- D7.21.1: `T = h̄_i^{1/2}`, `T^* T = h̄_i`
  have hT : (CFC.sqrt (E.hbar k i))ᴴ * CFC.sqrt (E.hbar k i) = E.hbar k i := by
    rw [conjTranspose_sqrt, CFC.sqrt_mul_sqrt_self _ hh.nonneg]
  -- D7.21.2: commuting leaf: `B = A_j`, `Y = Z = T`
  have hc : Commute (R.input n t k j) (E.hbar k i) → R.mapY t k E i j = R.mapZ t k E i j :=
    fun hc => by
      have h2 := auxY_self_of_commute hA hh hc
      simp only [mapY, mapZ, auxMetric, auxBlock_of_commute hc]
      rw [h2.1, h2.2]
  -- D7.21.3–D7.21.4: split leaf: `B_{i,j} > 0`
  have hB : (R.auxMetric t k E i j).PosDef := posDef_auxBlock hA hh
  -- D7.21.5: `Y^* Z = O`, `Y^* Y = |O^*|`; D7.21.6: `Z^* Z = |O|`
  have hYZ : (R.mapY t k E i j)ᴴ * R.mapZ t k E i j = R.simil t k E i j :=
    auxY_conjTranspose_mul_auxZ hA hB hh
  obtain ⟨hYY, hZZ⟩ := auxBlock_gram hA hh
  -- D7.21.7: `𝖣 = Y^*Y + Z^*Z - Y^*Z - Z^*Y = |O^*| + |O| - O - O^*`
  have hD := sub_conjTranspose_mul_sub_eq_skewAbs hYY hZZ hYZ
  exact ⟨hT, hB, hYZ, hD, posSemidef_skewAbs_of_eq hD, hc,
    fun hj => hc (R.step_7_12 hR ht k E i j hj)⟩

/-! ## D7.22 Transport of the commutator through the tree -/

/-- D7.22. `M_{i,j} = diag(A_j, B_{i,j})`. -/
noncomputable def blockInput (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    Matrix (Config n k ⊕ Config n k) (Config n k ⊕ Config n k) ℂ :=
  fromBlocks (R.input n t k j) 0 0 (R.auxMetric t k E i j)

/-- D7.22. `L_i = [[0, T_i^*], [T_i, 0]]`. -/
noncomputable def offDiag (k : ℕ) (E : EnergyTerms V n ι) (i : ι) :
    Matrix (Config n k ⊕ Config n k) (Config n k ⊕ Config n k) ℂ :=
  fromBlocks 0 (CFC.sqrt (E.hbar k i))ᴴ (CFC.sqrt (E.hbar k i)) 0

/-- D7.22. `K_{i,j} = M_{i,j}^{1/2} L_i M_{i,j}^{-1/2} - M_{i,j}^{-1/2} L_i M_{i,j}^{1/2}`. -/
noncomputable def rotK (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    Matrix (Config n k ⊕ Config n k) (Config n k ⊕ Config n k) ℂ :=
  R.blockInput t k E i j ^ (1 / 2 : ℝ) * offDiag k E i * R.blockInput t k E i j ^ (-(1 / 2) : ℝ) -
    R.blockInput t k E i j ^ (-(1 / 2) : ℝ) * offDiag k E i * R.blockInput t k E i j ^ (1 / 2 : ℝ)

/-- D7.22. The root `𝕄_i` of the terminal tree on the inputs `M_{i,j}`. -/
noncomputable def blockRoot (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (p : I) :
    Matrix (Config n k ⊕ Config n k) (Config n k ⊕ Config n k) ℂ :=
  (R.tree p).eval (R.blockInput t k E i)

/-- D7.22. The root `𝓑_i` of the terminal tree on the inputs `B_{i,j}`. -/
noncomputable def auxRoot (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (p : I) :
    Matrix (Config n k) (Config n k) ℂ :=
  (R.tree p).eval (R.auxMetric t k E i)

theorem posDef_blockInput (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    (R.blockInput t k E i j).PosDef :=
  (R.posDef_input hR ht hcomm j).fromBlocks_diag (R.step_7_21 hR ht hcomm E i j).2.1

omit [∀ v, NeZero (n v)] in
theorem isHermitian_offDiag (k : ℕ) (E : EnergyTerms V n ι) (i : ι) :
    (offDiag k E i).IsHermitian := by
  simp only [IsHermitian, offDiag, fromBlocks_conjTranspose, conjTranspose_zero,
    conjTranspose_conjTranspose]

/-- D7.22.1: `K_{i,j}` has lower-left block `Y_{i,j} - Z_{i,j}` and upper-right block
`-(Y_{i,j} - Z_{i,j})^*`. -/
theorem rotK_eq (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    R.rotK t k E i j = fromBlocks 0 (-(R.mapY t k E i j - R.mapZ t k E i j)ᴴ)
      (R.mapY t k E i j - R.mapZ t k E i j) 0 := by
  have hA := R.posDef_input hR ht hcomm j
  have hB := (R.step_7_21 hR ht hcomm E i j).2.1
  have hsub : ∀ A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Matrix (Config n k) (Config n k) ℂ,
      fromBlocks A₁ B₁ C₁ D₁ - fromBlocks A₂ B₂ C₂ D₂ =
        fromBlocks (A₁ - A₂) (B₁ - B₂) (C₁ - C₂) (D₁ - D₂) := by
    intros; simp only [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  rw [rotK, blockInput, offDiag, rpow_fromBlocks_diag hA hB, rpow_fromBlocks_diag hA hB]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hsub,
    sub_self]
  congr 1
  · simp only [mapY, mapZ, Matrix.auxY, Matrix.auxZ, conjTranspose_sub, conjTranspose_mul,
      (hA.rpow_isHermitian _).eq, (hB.rpow_isHermitian _).eq, neg_sub, Matrix.mul_assoc]

variable [Fintype H] [∀ h, Fintype (C h)]

/-- D7.22 (`transport:block-rotation`). Evaluate the full terminal tree on
`M_{i,j} = diag(A_j, B_{i,j})`: the root is `𝕄_i = diag(𝓜, 𝓑_i)`, the normalized leaf maps
`Φ̂_{i,j}` have first-block restrictions `Φ_j`, and with `L_i = [[0, T^*], [T, 0]]`,
`K_{i,j} = M_{i,j}^{1/2} L_i M_{i,j}^{-1/2} - M_{i,j}^{-1/2} L_i M_{i,j}^{1/2}`:
`2 sinh(ad_{log 𝕄_i}/2) L_i = ∑_j π_j Φ̂_{i,j}(K_{i,j})`. `K_{i,j}` has lower-left block
`Y_{i,j} - Z_{i,j}`, upper-right block `-(Y_{i,j} - Z_{i,j})^*`, upper-left block of
`K_{i,j}^* K_{i,j}` equal to `𝖣_{i,j}`, and `K_{i,j} = 0` for `j ∉ 𝒥_i`. -/
theorem step_7_22 (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (E : EnergyTerms V n ι) (i : ι) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    R.blockRoot t k E i p = fromBlocks (R.root n t k p) 0 0 (R.auxRoot t k E i p) ∧
    (∀ j, IsBlockDiagonalMap ((R.tree p).leafMap (R.blockInput t k E i) j)
      ((R.tree p).leafMap (R.input n t k) j) ((R.tree p).leafMap (R.auxMetric t k E i) j)) ∧
    (∀ h𝕄 : (R.blockRoot t k E i p).IsHermitian,
      Matrix.Transport.adLogFun h𝕄 (fun z => ((2 * Real.sinh (z / 2) : ℝ) : ℂ)) (offDiag k E i) =
        ∑ j, ((R.tree p).weight j : ℂ) • (R.tree p).leafMap (R.blockInput t k E i) j
          (R.rotK t k E i j)) ∧
    (∀ j, R.rotK t k E i j = fromBlocks 0 (-(R.mapY t k E i j - R.mapZ t k E i j)ᴴ)
      (R.mapY t k E i j - R.mapZ t k E i j) 0) ∧
    (∀ j, ((R.rotK t k E i j)ᴴ * R.rotK t k E i j).toBlocks₁₁ = R.skew t k E i j) ∧
    (∀ j ∉ R.splitLeaves E i, R.rotK t k E i j = 0) := by
  have hA : ∀ j, (R.input n t k j).PosDef := fun j => R.posDef_input hR ht hcomm j
  have hB : ∀ j, (R.auxMetric t k E i j).PosDef := fun j => (R.step_7_21 hR ht hcomm E i j).2.1
  have hM : ∀ j, (R.blockInput t k E i j).PosDef := R.posDef_blockInput hR ht hcomm E i
  -- D7.22.1: block entries of `K_{i,j}`; `K^* K = diag((Y - Z)^*(Y - Z), (Y - Z)(Y - Z)^*)`
  have hK := R.rotK_eq hR ht hcomm E i
  have hKK : ∀ j, ((R.rotK t k E i j)ᴴ * R.rotK t k E i j).toBlocks₁₁ = R.skew t k E i j := by
    intro j
    rw [hK, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [toBlocks_fromBlocks₁₁, conjTranspose_zero, Matrix.zero_mul, zero_add]
    exact (R.step_7_21 hR ht hcomm E i j).2.2.2.1
  -- D7.22.1: `Y = Z` at unsplit leaves, so `K = 0` there (D7.12, D7.21)
  have hK0 : ∀ j ∉ R.splitLeaves E i, R.rotK t k E i j = 0 := by
    classical
    intro j hj
    have hYZ : R.mapY t k E i j = R.mapZ t k E i j :=
      (R.step_7_21 hR ht hcomm E i j).2.2.2.2.2.2 fun g => by
        by_contra hg
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg⟩)
    rw [hK, hYZ, sub_self, conjTranspose_zero, neg_zero, fromBlocks_zero]
  -- D7.22.5: block-diagonal inputs, block-diagonal root and block-preserving leaf maps
  have hroot : R.blockRoot t k E i p = fromBlocks (R.root n t k p) 0 0 (R.auxRoot t k E i p) := by
    rw [blockRoot, root_eq_eval]
    exact MeanTree.eval_fromBlocks_diag hA hB _
  refine ⟨hroot, fun j => MeanTree.isBlockDiagonalMap_leafMap hA hB _ j, fun h𝕄 => ?_, hK,
    hKK, hK0⟩
  -- D7.22.2–D7.22.3: rotation covariance and Lemma 7.2 (leaf weights `π_j`)
  have hrot := MeanTree.sum_weight_smul_leafMap_rotation hM (R.tree p)
    (fun j => (R.weight_tree_pos hR hp0 hp1 j).ne') (isHermitian_offDiag k E i)
  -- D7.22.4: `2 sinh(ad_{log 𝕄}/2) L = 𝕄^{1/2} L 𝕄^{-1/2} - 𝕄^{-1/2} L 𝕄^{1/2}`
  have hsinh := Matrix.Transport.adLogFun_two_sinh (MeanTree.posDef_eval hM (R.tree p))
    (offDiag k E i)
  exact hsinh.trans hrot.symm

/-! ## D7.23 Bound on `E_{i,±}` -/

omit [Fintype H] [∀ h, Fintype (C h)] [∀ v, NeZero (n v)] [DecidableEq H]
  [∀ h, DecidableEq (C h)] in
theorem fromBlocks_sub' {m : Type*} (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Matrix m m ℂ) :
    fromBlocks A₁ B₁ C₁ D₁ - fromBlocks A₂ B₂ C₂ D₂ =
      fromBlocks (A₁ - A₂) (B₁ - B₂) (C₁ - C₂) (D₁ - D₂) := by
  simp only [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]

/-- D7.23 (`transport:E-def`). `E_{i,±} = 𝓑_i^{±s} T_i 𝓜^{∓s} - T_i`, `s = 1/4`, written with
the exponent `r = ±s`. -/
noncomputable def errOp (t : ℝ) (k : ℕ) (E : EnergyTerms V n ι) (i : ι) (p : I) (r : ℝ) :
    Matrix (Config n k) (Config n k) ℂ :=
  R.auxRoot t k E i p ^ r * CFC.sqrt (E.hbar k i) * R.root n t k p ^ (-r) - CFC.sqrt (E.hbar k i)

omit [Fintype H] [∀ h, Fintype (C h)] [∀ v, NeZero (n v)] in
/-- `Tr(σ_{j,u} X) = ⟨𝓜^{-iu} v, Φ_j(X) 𝓜^{-iu} v⟩`. -/
theorem trace_state_mul (t : ℝ) (k : ℕ) (pre : Config n k → ℂ) (p : I) (j : Leaf H C) (u : ℝ)
    (X : Matrix (Config n k) (Config n k) ℂ) :
    (R.state n t k pre p j u * X).trace =
      star (Matrix.Transport.imagPow (R.root n t k p) u *ᵥ R.v n t k pre p) ⬝ᵥ
        ((R.tree p).leafMap (R.input n t k) j X *ᵥ
          (Matrix.Transport.imagPow (R.root n t k p) u *ᵥ R.v n t k pre p)) := by
  simp only [state, MeanTree.leafDual]
  rw [trace_traceAdjointMap_mul, ContinuousLinearMap.coe_coe, trace_mul_comm, mul_vecMulVec,
    trace_vecMulVec, dotProduct_comm]

/-- D7.23.1–D7.23.6 for one sign: if `h(z) = ∫ e^{iuz} q(u) du` with `|q| ≤ m_s/√2`,
`∫ |q| ≤ 1/(2√2)` and `h(z) 2 sinh(z/2) = e^{rz} - 1`, then
`‖𝓑^r T 𝓜^{-r} v - T v‖² ≤ ¼ W_i ∑_{j ∈ 𝒥_i} π_j ∫ m_s(u) Tr(σ_{j,u} 𝖣_{i,j}) du`. -/
theorem normSq_errOp_le (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (E : EnergyTerms V n ι) (i : ι) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (pre : Config n k → ℂ) {r : ℝ} {f q : ℝ → ℂ}
    (hq : Integrable q) (hf : ∀ z : ℝ, ∫ u : ℝ, Complex.exp (Complex.I * u * z) * q u = f z)
    (hfs : ∀ z : ℝ, f z * ((2 * Real.sinh (z / 2) : ℝ) : ℂ) = ((Real.exp (r * z) - 1 : ℝ) : ℂ))
    (hqm : ∀ u, ‖q u‖ ≤ m (1 / 4) u / √2) (hqi : ∫ u, ‖q u‖ ≤ 1 / (2 * √2)) :
    (star (R.errOp t k E i p r *ᵥ R.v n t k pre p) ⬝ᵥ (R.errOp t k E i p r *ᵥ R.v n t k pre p)).re ≤
      1 / 4 * R.splitWeight E i p * ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j *
        ∫ u, m (1 / 4) u * (R.state n t k pre p j u * R.skew t k E i j).trace.re := by
  obtain ⟨hroot, hblk, hrot, -, hKK, hK0⟩ := R.step_7_22 hR ht hcomm E i hp0 hp1
  have hA : ∀ j, (R.input n t k j).PosDef := fun j => R.posDef_input hR ht hcomm j
  have hB : ∀ j, (R.auxMetric t k E i j).PosDef := fun j => (R.step_7_21 hR ht hcomm E i j).2.1
  have hM : ∀ j, (R.blockInput t k E i j).PosDef := R.posDef_blockInput hR ht hcomm E i
  have hw : ∀ j, 0 < (R.tree p).weight j := R.weight_tree_pos hR hp0 hp1
  set v := R.v n t k pre p
  set S := R.splitLeaves E i
  have h𝓜 : (R.root n t k p).PosDef := by rw [root_eq_eval]; exact MeanTree.posDef_eval hA _
  have h𝓑 : (R.auxRoot t k E i p).PosDef := MeanTree.posDef_eval hB _
  have h𝕄 : (R.blockRoot t k E i p).PosDef := MeanTree.posDef_eval hM _
  set x : Config n k ⊕ Config n k → ℂ := Sum.elim v 0
  set e := R.errOp t k E i p r *ᵥ v
  set G : Leaf H C → Matrix (Config n k ⊕ Config n k) (Config n k ⊕ Config n k) ℂ :=
    fun j => (R.tree p).leafMap (R.blockInput t k E i) j (R.rotK t k E i j)
  set W := fun u => Matrix.Transport.imagPow (R.root n t k p) u *ᵥ v
  set τ : Leaf H C → ℝ → ℝ := fun j u => (R.state n t k pre p j u * R.skew t k E i j).trace.re
  -- D7.23.1: `h_±(ad)(2 sinh(ad/2) L) = 𝕄^{±s} L 𝕄^{∓s} - L`, acting on `(v, 0)` as `(0, E_± v)`
  have hE : (R.blockRoot t k E i p ^ r * offDiag k E i * R.blockRoot t k E i p ^ (-r) -
      offDiag k E i) *ᵥ x = Sum.elim (0 : Config n k → ℂ) e := by
    rw [hroot, rpow_fromBlocks_diag h𝓜 h𝓑, rpow_fromBlocks_diag h𝓜 h𝓑]
    simp only [offDiag, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      fromBlocks_sub', sub_self, fromBlocks_mulVec, x, Sum.elim_comp_inl, Sum.elim_comp_inr,
      mulVec_zero, zero_mulVec, e, errOp, sub_mulVec]
  have hnorm : (star e ⬝ᵥ e).re = (star ((R.blockRoot t k E i p ^ r * offDiag k E i *
      R.blockRoot t k E i p ^ (-r) - offDiag k E i) *ᵥ x) ⬝ᵥ
        ((R.blockRoot t k E i p ^ r * offDiag k E i * R.blockRoot t k E i p ^ (-r) -
          offDiag k E i) *ᵥ x)).re := by
    rw [hE, Function.star_sumElim, sumElim_dotProduct_sumElim]
    simp
  -- D7.23.2: the rotation identity restricted to `𝒥_i` (`K_{i,j} = 0` off `𝒥_i`)
  have hG : Matrix.Transport.adLogFun h𝕄.isHermitian
      (fun z => ((2 * Real.sinh (z / 2) : ℝ) : ℂ)) (offDiag k E i) =
        ∑ j ∈ S, ((R.tree p).weight j : ℂ) • G j := by
    rw [hrot h𝕄.isHermitian]
    exact (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by
      simp only [hK0 j hj, map_zero, smul_zero]).symm
  -- D7.23.3: Cauchy–Schwarz for the measure `π_j |q_±(u)| du`
  have hCS := Matrix.Transport.normSq_conj_sub_le h𝕄 (offDiag k E i) hq hf hfs S
    (fun j _ => (hw j).le) G hG x
  -- D7.23.4–D7.23.5: Schwarz for the unital CP map `Φ̂_{i,j}`, first block `Φ_j`, `(K^*K)₁₁ = 𝖣`
  have hW : ∀ j u, τ j u = (star (W u) ⬝ᵥ ((R.tree p).leafMap (R.input n t k) j
      (R.skew t k E i j) *ᵥ W u)).re := fun j u => by
    simp only [τ, W, trace_state_mul]
    rfl
  have hτ : ∀ j u, (star (G j *ᵥ (Matrix.Transport.imagPow (R.blockRoot t k E i p) u *ᵥ x)) ⬝ᵥ
      (G j *ᵥ (Matrix.Transport.imagPow (R.blockRoot t k E i p) u *ᵥ x))).re ≤ τ j u := by
    intro j u
    have hy : Matrix.Transport.imagPow (R.blockRoot t k E i p) u *ᵥ x = Sum.elim (W u) 0 := by
      rw [hroot, Matrix.Transport.imagPow_fromBlocks_diag h𝓜.isHermitian h𝓑.isHermitian,
        fromBlocks_mulVec]
      simp [x, W]
    have h2 := Matrix.Transport.re_star_mulVec_dotProduct_le_of_twoPositive
      (MeanTree.isNPositiveMap_leafMap hM (R.tree p) j 2)
      (MeanTree.leafMap_one hM (R.tree p) (hw j)) (R.rotK t k E i j) (Sum.elim (W u) 0)
    simp only [ContinuousLinearMap.coe_coe] at h2
    rw [hy, hW]
    refine h2.trans (le_of_eq ?_)
    rw [Matrix.Transport.star_sumElim_zero_dotProduct, (hblk j).toBlocks₁₁, hKK]
  -- `τ ≥ 0`: `Φ_j(𝖣) ≥ 0`
  have hτ0 : ∀ j u, 0 ≤ τ j u := fun j u => by
    rw [hW]
    have hP := (isNPositiveMap_one_iff_isPositiveMap.mp
      (MeanTree.isNPositiveMap_leafMap hA (R.tree p) j 1)) _
      (R.step_7_21 hR ht hcomm E i j).2.2.2.2.1
    exact (Complex.nonneg_iff.mp (hP.dotProduct_mulVec_nonneg (W u))).1
  have hiq : ∀ j, Integrable fun u => ‖q u‖ * τ j u := fun j => by
    simp only [hW]
    exact Matrix.Transport.integrable_norm_mul_re_inner_imagPow h𝓜.isHermitian hq _ v
  have him : ∀ j, Integrable fun u => m (1 / 4) u * τ j u := fun j => by
    simp only [hW]
    exact Matrix.Transport.integrable_fourierWeight_mul_quadForm h𝓜.isHermitian _ v
  -- D7.23.6: `∫ |q_±| ≤ 1/(2√2)`, `|q_±| ≤ m_s/√2`, product of constants `1/4`
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hWi : 0 ≤ R.splitWeight E i p := Finset.sum_nonneg fun j _ => (hw j).le
  set sa := ∑ j ∈ S, (R.tree p).weight j * ∫ u, ‖q u‖ *
    (star (G j *ᵥ (Matrix.Transport.imagPow (R.blockRoot t k E i p) u *ᵥ x)) ⬝ᵥ
      (G j *ᵥ (Matrix.Transport.imagPow (R.blockRoot t k E i p) u *ᵥ x))).re
  set sm := ∑ j ∈ S, (R.tree p).weight j * ∫ u, m (1 / 4) u * τ j u
  have ha0 : 0 ≤ sa := Finset.sum_nonneg fun j _ => mul_nonneg (hw j).le
    (integral_nonneg fun u => mul_nonneg (norm_nonneg _)
      (Matrix.Transport.re_star_dotProduct_self_nonneg _))
  have hla : sa ≤ sm / √2 := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hw j).le
    calc ∫ u, ‖q u‖ * (star (G j *ᵥ (Matrix.Transport.imagPow (R.blockRoot t k E i p) u *ᵥ x)) ⬝ᵥ
          (G j *ᵥ (Matrix.Transport.imagPow (R.blockRoot t k E i p) u *ᵥ x))).re
        ≤ ∫ u, ‖q u‖ * τ j u := integral_mono
          (Matrix.Transport.integrable_norm_mul_normSq_imagPow h𝕄.isHermitian hq (G j) x) (hiq j)
          fun u => mul_le_mul_of_nonneg_left (hτ j u) (norm_nonneg _)
      _ ≤ ∫ u, m (1 / 4) u * τ j u / √2 := integral_mono (hiq j) ((him j).div_const _)
          fun u => by
            rw [mul_div_right_comm]
            exact mul_le_mul_of_nonneg_right (hqm u) (hτ0 j u)
      _ = (∫ u, m (1 / 4) u * τ j u) / √2 := integral_div _ _
  calc (star e ⬝ᵥ e).re = _ := hnorm
    _ ≤ R.splitWeight E i p * (∫ u, ‖q u‖) * sa := hCS
    _ ≤ R.splitWeight E i p * (1 / (2 * √2)) * (sm / √2) := by
        gcongr
    _ = 1 / 4 * R.splitWeight E i p * sm := by
        field_simp
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-- D7.23 (`transport:E-def`, `transport:cp-schwarz`, `transport:block-bound`). With
`𝕄_i = diag(𝓜, 𝓑_i)` (D7.22) and `E_{i,±} = 𝓑_i^{±s} T 𝓜^{∓s} - T`, `s = 1/4`:
`‖E_{i,±} v‖² ≤ ¼ W_i ∑_{j ∈ 𝒥_i} π_j ∫_ℝ m_s(u) Tr(σ_{j,u} 𝖣_{i,j}) du`.
For unital CP `Ψ`: `Ψ(K)^* Ψ(K) ≤ Ψ(K^* K)` (here for `Ψ = Φ̂_{i,j}`). -/
theorem step_7_23 (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (E : EnergyTerms V n ι) (i : ι) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (pre : Config n k → ℂ) :
    (∀ j (X : Matrix (Config n k ⊕ Config n k) (Config n k ⊕ Config n k) ℂ),
      ((R.tree p).leafMap (R.blockInput t k E i) j X)ᴴ *
          (R.tree p).leafMap (R.blockInput t k E i) j X ≤
        (R.tree p).leafMap (R.blockInput t k E i) j (Xᴴ * X)) ∧
    (star (R.errOp t k E i p (1 / 4) *ᵥ R.v n t k pre p) ⬝ᵥ
        (R.errOp t k E i p (1 / 4) *ᵥ R.v n t k pre p)).re ≤
      1 / 4 * R.splitWeight E i p * ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j *
        ∫ u, m (1 / 4) u * (R.state n t k pre p j u * R.skew t k E i j).trace.re ∧
    (star (R.errOp t k E i p (-(1 / 4)) *ᵥ R.v n t k pre p) ⬝ᵥ
        (R.errOp t k E i p (-(1 / 4)) *ᵥ R.v n t k pre p)).re ≤
      1 / 4 * R.splitWeight E i p * ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j *
        ∫ u, m (1 / 4) u * (R.state n t k pre p j u * R.skew t k E i j).trace.re := by
  have hM := R.posDef_blockInput hR ht hcomm E i
  have hw := R.weight_tree_pos hR hp0 hp1
  obtain ⟨hqP, hqM, hiP, hiM⟩ := integral_norm_q_le
  have hsh : ∀ z : ℝ, z ≠ 0 → 2 * Real.sinh (z / 2) ≠ 0 := fun z hz => by
    refine mul_ne_zero two_ne_zero ?_
    rw [Ne, Real.sinh_eq_zero]; intro h; exact hz (by linarith)
  refine ⟨fun j X => ?_, ?_, ?_⟩
  -- D7.23.4: Schwarz inequality for the unital CP map `Φ̂_{i,j}` (amplification, Schur
  -- complement)
  · have h := kadison_schwarz_twoPositive _ (MeanTree.isNPositiveMap_leafMap hM (R.tree p) j 2)
      (MeanTree.leafMap_one hM (R.tree p) (hw j)) X
    simp only [ContinuousLinearMap.coe_coe] at h
    exact Matrix.le_iff.mpr h
  -- D7.23.1: `h_+(z) 2 sinh(z/2) = e^{sz} - 1`; D7.23.2: Lemma 7.3(2), `h_+ = ∫ e^{iuz} q_+`;
  -- D7.23.6: `|q_+| ≤ m_s/√2`, `∫ |q_+| ≤ 1/(2√2)`
  · refine R.normSq_errOp_le hR ht hcomm E i hp0 hp1 pre hqP (f := fun z => (hPlus z : ℂ))
      (fun z => (lemma_7_3.2.2.1 z).1) (fun z => ?_) (fun u => (lemma_7_3.2.2.2 u).1) hiP
    rw [← Complex.ofReal_mul]
    congr 1
    unfold hPlus
    split_ifs with hz
    · simp [hz]
    · exact div_mul_cancel₀ _ (hsh z hz)
  -- D7.23.6: both signs identical
  · refine R.normSq_errOp_le hR ht hcomm E i hp0 hp1 pre hqM (f := fun z => (hMinus z : ℂ))
      (fun z => (lemma_7_3.2.2.1 z).2) (fun z => ?_) (fun u => (lemma_7_3.2.2.2 u).2) hiM
    rw [← Complex.ofReal_mul]
    congr 1
    unfold hMinus
    split_ifs with hz
    · simp [hz]
    · rw [div_mul_cancel₀ _ (hsh z hz), neg_mul]

/-! ## D7.24 Symbol cost of a split -/

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- D7.12 in one band: the band metric of a partition with `D_i` inside one part commutes with
`h̄_i`. -/
theorem commute_bandMetric_hbar (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) (g : Fin K)
    (hc : (R.leafPart j g).Contains (E.support i)) :
    Commute (bandMetric n t k (R.leafPart j g)) (E.hbar k i) := by
  obtain ⟨hPY, hPF, hYF, -⟩ := R.isPartition_leafPart hR j g
  exact commute_proj_mul_add_one_sub (commute_Pi_hbar E k i)
    (Replicas.eq_replicas_leaf_floor_3 ht k hPY hPF hYF (E.isSupportedOn_term i) hc)

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- D7.24.1. At a split leaf with exceptional band `g₀` the factors `A_{j,g}^{∓1/2}`, `g ≠ g₀`,
commute with `h̄_i` and with `A_{j,g₀}^{±1/2}` and cancel:
`O_{i,j} = A_{j,g₀}^{-1/2} h̄_i A_{j,g₀}^{1/2}`. -/
theorem simil_eq_band (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) {E : EnergyTerms V n ι} (hcompat : R.SupportCompatible E)
    {i : ι} {j : Leaf H C} {g : Fin K} (hg : ¬ (R.leafPart j g).Contains (E.support i)) :
    R.simil t k E i j = bandMetric n t k (R.leafPart j g) ^ (-(1 / 2) : ℝ) * E.hbar k i *
      bandMetric n t k (R.leafPart j g) ^ (1 / 2 : ℝ) := by
  rw [simil, input_eq_prod]
  exact list_ofFn_prod_rpow_conj _ (fun g => posDef_bandMetric (R.isPartition_leafPart hR j g) ht k)
    (fun g g' hgg => hcomm j j g g' hgg) g fun g' hg' =>
      R.commute_bandMetric_hbar hR ht k E i j g' (((hcompat j i g).resolve_left hg).2 g' hg')

omit [Fintype H] [∀ h, Fintype (C h)] [DecidableEq H] [∀ h, DecidableEq (C h)] in
/-- D7.24.3. Against a density on `𝒮_k`, the skew defect of the band-metric similarity transform
`(Π_k A + (1 - Π_k))^{-1/2} h̄ (Π_k A + (1 - Π_k))^{1/2}` is Lemma 6.4's
`𝒟_k = |O_k| + |O_k^†| - O_k - O_k^†` (absolute values on `𝒮_k`), `O_k = A^{-1/2} h̄ A^{1/2}`. -/
theorem trace_mul_skewAbs_bandMetric {π : PYF V} (hπ : π.IsPartition) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (E : EnergyTerms V n ι) (i : ι) {ρ : Matrix (Config n k) (Config n k) ℂ}
    (hρ : IsSymDensity n ρ) :
    (ρ * skewAbs (bandMetric n t k π ^ (-(1 / 2) : ℝ) * E.hbar k i *
        bandMetric n t k π ^ (1 / 2 : ℝ))).trace =
      (ρ * TensorPower.skewOperator k
        (TensorPower.markedSimilarity n t k π.P π.Y π.F (E.term i))).trace := by
  set A := Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F
  have hA : A.PosDef := posDef_A hπ ht k
  have hP := isHermitian_Pi (n := n) k
  have hPP := Pi_mul_Pi (n := n) k
  have hPA : Commute (Pi n k) A := commute_Pi_A t k π.P π.Y π.F
  have hPh : Commute (Pi n k) (E.hbar k i) := commute_Pi_hbar E k i
  -- `ρ = Π_k ρ = ρ Π_k`
  have hPρ : Pi n k * ρ = ρ := TensorPower.symProj_mul_of_permOp_mul fun s => by
    rw [← Replicas.U_univ_eq]; exact hρ.2.2 s
  have hρP : ρ * Pi n k = ρ := by
    have := congrArg conjTranspose hPρ
    rwa [conjTranspose_mul, hP.eq, hρ.1.isHermitian.eq] at this
  -- Lemma 6.4's `O_k = A_k^{-1/2} h̄ A_k^{1/2}`
  have hO : TensorPower.markedSimilarity n t k π.P π.Y π.F (E.term i) =
      A ^ (-(1 / 2) : ℝ) * E.hbar k i * A ^ (1 / 2 : ℝ) := by
    have hinv : (A ^ (1 / 2 : ℝ))⁻¹ = A ^ (-(1 / 2) : ℝ) :=
      Matrix.inv_eq_left_inv (hA.rpow_neg_mul_rpow _)
    rw [TensorPower.markedSimilarity, ← Replicas.A_eq_leafMetric, CFC.sqrt_eq_rpow, hinv]
    rfl
  set O := A ^ (-(1 / 2) : ℝ) * E.hbar k i * A ^ (1 / 2 : ℝ)
  have hPr : ∀ r : ℝ, Commute (Pi n k) (A ^ r) := fun r => (hA.commute_rpow_left hPA.symm r).symm
  have hPO : Commute (Pi n k) O := ((hPr _).mul_right hPh).mul_right (hPr _)
  have hPOs : Commute (Pi n k) Oᴴ := by
    have := hPO.star_star
    rwa [star_eq_conjTranspose, star_eq_conjTranspose, hP.eq] at this
  -- on `𝒮_k`, `|O_k Π| = |O_k|`
  have hskew : Pi n k * TensorPower.skewOperator k O = Pi n k * skewAbs O := by
    simp only [TensorPower.skewOperator, skewAbs, Matrix.mul_sub, Matrix.mul_add]
    rw [proj_mul_cfc_sqrt_proj_mul hP hPP (posSemidef_conjTranspose_mul_self O)
        (hPOs.mul_right hPO),
      proj_mul_cfc_sqrt_proj_mul hP hPP (posSemidef_self_mul_conjTranspose O)
        (hPO.mul_right hPOs), add_comm (Pi n k * CFC.sqrt (Oᴴ * O))]
  calc (ρ * skewAbs (bandMetric n t k π ^ (-(1 / 2) : ℝ) * E.hbar k i *
        bandMetric n t k π ^ (1 / 2 : ℝ))).trace
      = (ρ * (Pi n k * skewAbs (bandMetric n t k π ^ (-(1 / 2) : ℝ) * E.hbar k i *
          bandMetric n t k π ^ (1 / 2 : ℝ)))).trace := by rw [← Matrix.mul_assoc, hρP]
    _ = (ρ * (Pi n k * skewAbs O)).trace := by
        rw [bandMetric, proj_mul_skewAbs_conj_proj_mul_add_one_sub hA hP hPP hPA hPh]
    _ = (ρ * (Pi n k * TensorPower.skewOperator k O)).trace := by rw [hskew]
    _ = _ := by rw [← Matrix.mul_assoc, hρP, hO]

end Round

/-- D7.24 (`transport:symbol-cost`). For every split pair `(i, j)`, uniformly over density
matrices `σ` on `𝒮_k`:
`Tr(σ 𝖣_{i,j}) ≤ C a² ℓ^C ∫ η_{i,j}(θ)^{1/8} dμ_σ(θ) + r_k`, `r_k → 0`
(here `ℓ^C = ℓ⁴`, the exponent of Lemma 6.4). One common `r_k ≥ 0` serves all split pairs
(`r_k = 0` if none). Unsplit pairs: `𝖣_{i,j} = 0`, no remainder and no dimension factor. -/
theorem step_7_24 : ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)] {K : ℕ}
      {H : Type*} [Fintype H] [DecidableEq H] {Ch : H → Type*} [∀ h, Fintype (Ch h)]
      [∀ h, DecidableEq (Ch h)] (R : Round V K H Ch) {ι : Type*} [Fintype ι]
      (E : EnergyTerms V n ι), R.IsAdmissible → R.SupportCompatible E →
      ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, R.CrossBandCommute n (a / 2) k) →
      (∀ i, (R.splitLeaves E i).Nonempty → logDim (n := n) (E.support i) ≤ ℓ) →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ k, 0 ≤ r k) ∧
        (∀ k i, ∀ j ∈ R.splitLeaves E i, ∀ ρ : Matrix (Config n k) (Config n k) ℂ,
          IsSymDensity n ρ →
            (ρ * R.skew (a / 2) k E i j).trace.re ≤
              C * a ^ 2 * ℓ ^ 4 * ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ)
                ∂(Replicas.μ (fun v => Fin (n v)) k ρ) + r k) ∧
        (∀ k i, ∀ j ∉ R.splitLeaves E i, R.skew (a / 2) k E i j = 0) := by
  obtain ⟨c, C, hc, hC, h64⟩ := Replicas.lemma_6_4
  refine ⟨min c (1 / 2), C, lt_min hc (by norm_num), hC, ?_⟩
  intro V _ _ n _ K H _ _ Ch _ _ R ι _ E hR hcompat a ℓ ha hℓ haℓ hcomm hℓD
  have ht0 : 0 < a / 2 := by positivity
  have hat : a ≤ 1 / 2 :=
    (le_mul_of_one_le_right ha.le hℓ).trans (haℓ.trans (min_le_right _ _))
  have ht1 : a / 2 < 1 / 2 := by linarith
  have hac : a * ℓ ≤ c := haℓ.trans (min_le_left _ _)
  have hpair : ∀ x : ι × Round.Leaf H Ch, ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ k, 0 ≤ r k) ∧
      ∀ k, x.2 ∈ R.splitLeaves E x.1 → ∀ ρ : Matrix (Config n k) (Config n k) ℂ,
        IsSymDensity n ρ → (ρ * R.skew (a / 2) k E x.1 x.2).trace.re ≤
          C * a ^ 2 * ℓ ^ 4 * ∫ θ, R.splitEta E x.1 x.2 θ.1 ^ (1 / 8 : ℝ)
            ∂(Replicas.μ (fun v => Fin (n v)) k ρ) + r k := by
    rintro ⟨i, j⟩
    classical
    by_cases hj : j ∈ R.splitLeaves E i
    swap
    · exact ⟨0, tendsto_const_nhds, fun _ => le_rfl, fun k hk => absurd hk hj⟩
    obtain ⟨g, hg⟩ : ∃ g, ¬ (R.leafPart j g).Contains (E.support i) :=
      (Finset.mem_filter.mp hj).2
    obtain ⟨hsp, hoth⟩ := (hcompat j i g).resolve_left hg
    obtain ⟨hPY, hPF, hYF, hcov⟩ := R.isPartition_leafPart hR j g
    set π := R.leafPart j g
    set D := E.support i
    have hη0 : ∀ θ, R.splitEta E i j θ = Round.splitBandEta π D θ := fun θ => by
      unfold Round.splitEta
      exact Finset.sum_eq_single_of_mem g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
        fun g' hg' hne => absurd (hoth g' hne) (Finset.mem_filter.mp hg').2
    have hmem : ∀ v, v ∈ π.P ∨ v ∈ π.Y ∨ v ∈ π.F := fun v => by
      have hv : v ∈ π.P ∪ π.Y ∪ π.F := hcov ▸ Finset.mem_univ v
      simp only [Finset.mem_union] at hv; tauto
    -- D7.24.2: `h_i` is supported on `P Y` (or on `Y F`, exchanging the outer parts, D6.12.5)
    obtain ⟨P', F', hP'Y, hP'F', hYF', hcov', hDsub, hmarked, hη⟩ : ∃ P' F' : Finset V,
        Disjoint P' π.Y ∧ Disjoint P' F' ∧ Disjoint π.Y F' ∧ P' ∪ π.Y ∪ F' = Finset.univ ∧
        D ⊆ P' ∪ π.Y ∧
        (∀ k, TensorPower.markedSimilarity n (a / 2) k π.P π.Y π.F (E.term i) =
          TensorPower.markedSimilarity n (a / 2) k P' π.Y F' (E.term i)) ∧
        ∀ θ, R.splitEta E i j θ = Replicas.η (π.Y ∩ D) (π.Y \ D) F' θ := by
      rcases hsp with hP | hF
      · refine ⟨π.P, π.F, hPY, hPF, hYF, hcov, fun v hv => ?_, fun k => rfl, fun θ => ?_⟩
        · have hvF : v ∉ π.F := Finset.disjoint_left.mp hP.2.2 hv
          simp only [Finset.mem_union]; have := hmem v; tauto
        · rw [hη0, Round.splitBandEta, if_pos hP, Finset.inter_comm]
      · refine ⟨π.F, π.P, hYF.symm, hPF.symm, hPY.symm, ?_, fun v hv => ?_,
          fun k => Replicas.step_6_12_5 ht0.le k hPF _ _, fun θ => ?_⟩
        · ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; have := hmem v; tauto
        · have hvP : v ∉ π.P := Finset.disjoint_left.mp hF.2.2 hv
          simp only [Finset.mem_union]; have := hmem v; tauto
        · have hnP : ¬ π.SplitsToP D := fun h => by
            obtain ⟨w, hw⟩ := hF.2.1
            exact Finset.disjoint_left.mp h.2.2 (Finset.mem_inter.mp hw).1
              (Finset.mem_inter.mp hw).2
          rw [hη0, Round.splitBandEta, if_neg hnP, Finset.inter_comm]
    -- D7.24.2: `log(e dim D_i) ≤ ℓ`, `a ℓ` small: the hypotheses of Lemma 6.4, item 4
    have hlog : logDim (n := n) D ≤ ℓ := hℓD i ⟨j, hj⟩
    have hlog0 : 0 ≤ logDim (n := n) D := by
      have : (1 : ℝ) ≤ Fintype.card (Reg (fun v => Fin (n v)) D) := by
        exact_mod_cast Fintype.card_pos
      exact (Real.log_pos (by nlinarith [Real.add_one_le_exp (1 : ℝ)])).le
    have h4 := (h64 V n (a / 2) ht0 ht1 P' π.Y F' hP'Y hP'F' hYF' (E.term i)
      ((E.isSupportedOn_term i).mono hDsub)).2.2.2 hcov' D (E.op i) hDsub rfl (E.nonneg i)
      (E.le_one i) (by
        rw [show 2 * (a / 2) = a by ring]
        exact (mul_le_mul_of_nonneg_left hlog ha.le).trans hac)
    -- D7.24.3: one remainder, uniform in the densities `ρ` on `𝒮_k`
    have hint0 : ∀ k (ρ : Matrix (Config n k) (Config n k) ℂ),
        0 ≤ ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ) ∂(Replicas.μ (fun v => Fin (n v)) k ρ) :=
      fun k ρ => integral_nonneg fun θ => Real.rpow_nonneg_of_le_half _ (by norm_num) (by norm_num)
    set F : ∀ k, {ρ : Matrix (Config n k) (Config n k) ℂ // IsSymDensity n ρ} → ℝ :=
      fun k ρ => (ρ.1 * R.skew (a / 2) k E i j).trace.re - C * a ^ 2 * ℓ ^ 4 *
        ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ) ∂(Replicas.μ (fun v => Fin (n v)) k ρ.1)
    have hbdd : ∀ k, ∃ b, ∀ ρ, F k ρ ≤ b := fun k => ⟨‖R.skew (a / 2) k E i j‖, fun ρ => by
      have h1 := (Complex.re_le_norm _).trans (ρ.2.1.norm_trace_mul_le (R.skew (a / 2) k E i j))
      rw [ρ.2.2.1, Complex.one_re, one_mul] at h1
      have h2 := hint0 k ρ.1
      have h3 : 0 ≤ C * a ^ 2 * ℓ ^ 4 := by positivity
      simp only [F]; nlinarith⟩
    have hev : ∀ ε > 0, ∀ᶠ k in atTop, ∀ ρ, F k ρ ≤ ε := by
      intro ε hε
      filter_upwards [h4 ε hε] with k hk
      intro ρ
      obtain ⟨hρp, hρt, hρs⟩ := ρ.2
      have hb := hk (fun _ => 0) ρ.1 hρp hρt fun s => by rw [← Replicas.U_univ_eq]; exact hρs s
      -- D7.24.1, D7.24.3: `Tr(ρ 𝖣_{i,j}) = Tr(ρ 𝒟_k)`
      have htr : (ρ.1 * R.skew (a / 2) k E i j).trace = (ρ.1 * TensorPower.skewOperator k
          (TensorPower.markedSimilarity n (a / 2) k P' π.Y F' (E.term i))).trace := by
        rw [Round.skew, R.simil_eq_band hR ht0.le (hcomm k) hcompat hg,
          Round.trace_mul_skewAbs_bandMetric (R.isPartition_leafPart hR j g) ht0.le E i ρ.2,
          hmarked k]
      -- the coherent integral of Lemma 6.4 is the Husimi integral (D6.11)
      have hcoh : (TensorPower.coherentIntegral (fun _ => 0) ρ.1 fun θ =>
          ((Replicas.η (π.Y ∩ D) (π.Y \ D) F' θ ^ (1 / 8 : ℝ) : ℝ) : ℂ)).re =
            ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ) ∂(Replicas.μ (fun v => Fin (n v)) k ρ.1) := by
        have hφ : ContinuousOn (fun θ : SiteConfig n → ℂ =>
            ((Replicas.η (π.Y ∩ D) (π.Y \ D) F' θ ^ (1 / 8 : ℝ) : ℝ) : ℂ))
            TensorPower.unitSphere := Complex.continuous_ofReal.comp_continuousOn
          ((Replicas.continuousOn_η _ _ _).rpow_const fun _ _ => Or.inr (by norm_num))
        rw [Replicas.coherentIntegral_eq_integral_μ (fun v => Fin (n v)) k hρp _ hφ,
          integral_complex_ofReal, Complex.ofReal_re]
        simp only [hη]
      rw [← htr, hcoh] at hb
      have hpow : C * (2 * (a / 2)) ^ 2 * logDim (n := n) D ^ 4 *
          ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ) ∂(Replicas.μ (fun v => Fin (n v)) k ρ.1) ≤
          C * a ^ 2 * ℓ ^ 4 *
            ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ) ∂(Replicas.μ (fun v => Fin (n v)) k ρ.1) := by
        rw [show 2 * (a / 2) = a by ring]
        gcongr
        exact hint0 k ρ.1
      simp only [F]
      linarith
    obtain ⟨r, hr, hr0, hle⟩ := Real.exists_tendsto_zero_of_forall_eventually_le F hbdd hev
    exact ⟨r, hr, hr0, fun k _ ρ hρ => by
      have := hle k ⟨ρ, hρ⟩
      simp only [F] at this
      linarith⟩
  choose r hr hr0 hb using hpair
  refine ⟨fun k => ∑ x, r x k, by simpa using tendsto_finsetSum Finset.univ fun x _ => hr x,
    fun k => Finset.sum_nonneg fun x _ => hr0 x k, fun k i j hj ρ hρ => ?_, fun k i j hj => ?_⟩
  · exact (hb (i, j) k hj ρ hρ).trans (add_le_add le_rfl (Finset.single_le_sum
      (f := fun x => r x k) (fun x _ => hr0 x k) (Finset.mem_univ (i, j))))
  -- unsplit pairs: `Y = Z`, so `𝖣_{i,j} = 0`
  · classical
    have h21 := R.step_7_21 hR ht0.le (hcomm k) E i j
    have hYZ := h21.2.2.2.2.2.2 fun g => by
      by_contra hg
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg⟩)
    rw [← h21.2.2.2.1, hYZ, sub_self, conjTranspose_zero, Matrix.zero_mul]

/-! ## D7.25 Assembly of the energy bound -/

/-- D6.11: for a function `φ` continuous on unit vectors, the Husimi integral is a trace
pairing, `∫ φ dμ_ρ = Re Tr(ρ Q_φ)` for every `ρ ≥ 0`, with `Q_φ` independent of `ρ`. -/
theorem exists_integral_μ_eq_re_trace [∀ v, NeZero (n v)] (k : ℕ)
    {φ : (SiteConfig n → ℂ) → ℝ} (hφ : ContinuousOn φ TensorPower.unitSphere) :
    ∃ Q : Matrix (Config n k) (Config n k) ℂ, ∀ ρ : Matrix (Config n k) (Config n k) ℂ,
      ρ.PosSemidef →
        ∫ θ, φ θ.1 ∂(Replicas.μ (fun v => Fin (n v)) k ρ) = (ρ * Q).trace.re := by
  set a : SiteConfig n := fun _ => 0
  set θU : unitaryGroup (SiteConfig n) ℂ → SiteConfig n → ℂ :=
    fun U => (U : Matrix (SiteConfig n) (SiteConfig n) ℂ) *ᵥ Pi.single a 1
  have hθ : Continuous θU := continuous_subtype_val.matrix_mulVec continuous_const
  have hφc : ContinuousOn (fun θ => ((φ θ : ℝ) : ℂ)) TensorPower.unitSphere :=
    Complex.continuous_ofReal.comp_continuousOn hφ
  have hφU : Continuous fun U => ((φ (θU U) : ℝ) : ℂ) :=
    hφc.comp_continuous hθ fun U => TensorPower.unitary_mulVec_single_mem_unitSphere U a
  set F : unitaryGroup (SiteConfig n) ℂ → Matrix (Config n k) (Config n k) ℂ :=
    fun U => ((φ (θU U) : ℝ) : ℂ) • TensorPower.coherentProj k (θU U)
  have hF : ∀ x y, Integrable (fun U => F U x y) (unitaryHaar (SiteConfig n)) := fun x y => by
    have hc : Continuous fun U => F U x y := by
      simp only [F, Matrix.smul_apply, smul_eq_mul, θU, TensorPower.coherentProj_mulVec]
      exact hφU.mul (TensorPower.continuous_twirlIntegrand _ x y)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨(PermutationRepresentation.symProj (TensorPower.copyPerm (SiteConfig n) k)).trace •
    Matrix.of fun x y => ∫ U, F U x y ∂(unitaryHaar (SiteConfig n)), fun ρ hρ => ?_⟩
  have h := Replicas.coherentIntegral_eq_integral_μ (fun v => Fin (n v)) k hρ a hφc
  rw [integral_complex_ofReal] at h
  have hT := TensorPower.trace_mul_integral ρ F hF
    (T := Matrix.of fun x y => ∫ U, F U x y ∂(unitaryHaar (SiteConfig n))) (fun x y => rfl)
  rw [← Complex.ofReal_re (∫ θ, φ θ.1 ∂(Replicas.μ (fun v => Fin (n v)) k ρ)), ← h,
    TensorPower.coherentIntegral, Matrix.mul_smul, trace_smul, smul_eq_mul, hT]
  congr 3
  funext U
  simp only [F, Matrix.mul_smul, trace_smul, smul_eq_mul, mul_comm]
  rfl

namespace Round

variable {K : ℕ} {H : Type*} {C : H → Type*} (R : Round V K H C) {ι : Type*}
variable [∀ v, NeZero (n v)] [DecidableEq H] [∀ h, DecidableEq (C h)]

omit [∀ v, NeZero (n v)] [DecidableEq H] [∀ h, DecidableEq (C h)] in
/-- `η_{i,j}^{1/8}` is continuous on unit vectors. -/
theorem continuousOn_splitEta_rpow (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    ContinuousOn (fun θ => R.splitEta E i j θ ^ (1 / 8 : ℝ)) TensorPower.unitSphere := by
  refine ContinuousOn.rpow_const ?_ fun _ _ => Or.inr (by norm_num)
  refine continuousOn_finsetSum _ fun g _ => ?_
  unfold splitBandEta
  split_ifs
  · exact Replicas.continuousOn_η _ _ _
  · exact Replicas.continuousOn_η _ _ _

/-- D7.25.1. `T + E_± = 𝓑^{±s} T 𝓜^{∓s}`; the opposite powers of `𝓑_i` cancel:
`Re⟨(T + E_+) v, (T + E_-) v⟩ = Re⟨𝓜^{-s} v, h̄_i 𝓜^s v⟩`. -/
theorem re_inner_errOp_eq (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (E : EnergyTerms V n ι) (i : ι) (p : I)
    (x : Config n k → ℂ) :
    (star ((CFC.sqrt (E.hbar k i) + R.errOp t k E i p (1 / 4)) *ᵥ x) ⬝ᵥ
        ((CFC.sqrt (E.hbar k i) + R.errOp t k E i p (-(1 / 4))) *ᵥ x)).re =
      (star (R.root n t k p ^ (-(1 / 4) : ℝ) *ᵥ x) ⬝ᵥ
        (E.hbar k i *ᵥ (R.root n t k p ^ (1 / 4 : ℝ) *ᵥ x))).re := by
  have hA : ∀ j, (R.input n t k j).PosDef := fun j => R.posDef_input hR ht hcomm j
  have hB : ∀ j, (R.auxMetric t k E i j).PosDef := fun j => (R.step_7_21 hR ht hcomm E i j).2.1
  have hM : (R.root n t k p).PosDef := by rw [root_eq_eval]; exact MeanTree.posDef_eval hA _
  have hBr : (R.auxRoot t k E i p).PosDef := MeanTree.posDef_eval hB _
  have hTT : CFC.sqrt (E.hbar k i) * CFC.sqrt (E.hbar k i) = E.hbar k i :=
    CFC.sqrt_mul_sqrt_self _ (E.posSemidef_hbar k i).nonneg
  have h1 : CFC.sqrt (E.hbar k i) + R.errOp t k E i p (1 / 4) =
      R.auxRoot t k E i p ^ (1 / 4 : ℝ) * CFC.sqrt (E.hbar k i) *
        R.root n t k p ^ (-(1 / 4) : ℝ) := by
    simp [errOp]
  have h2 : CFC.sqrt (E.hbar k i) + R.errOp t k E i p (-(1 / 4)) =
      R.auxRoot t k E i p ^ (-(1 / 4) : ℝ) * CFC.sqrt (E.hbar k i) *
        R.root n t k p ^ (1 / 4 : ℝ) := by
    simp [errOp]
  rw [h1, h2, Matrix.Transport.star_mulVec_dotProduct_mulVec',
    Matrix.Transport.star_mulVec_dotProduct_mulVec', mulVec_mulVec]
  congr 3
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_sqrt, (hBr.rpow_isHermitian _).eq,
    (hM.rpow_isHermitian _).eq]
  calc _ = R.root n t k p ^ (-(1 / 4) : ℝ) * CFC.sqrt (E.hbar k i) *
        (R.auxRoot t k E i p ^ (1 / 4 : ℝ) * R.auxRoot t k E i p ^ (-(1 / 4) : ℝ)) *
          CFC.sqrt (E.hbar k i) * R.root n t k p ^ (1 / 4 : ℝ) := by noncomm_ring
    _ = R.root n t k p ^ (-(1 / 4) : ℝ) * E.hbar k i * R.root n t k p ^ (1 / 4 : ℝ) := by
      rw [hBr.rpow_mul_rpow_neg, Matrix.mul_one]; conv_rhs => rw [← hTT]
      noncomm_ring

omit [∀ v, NeZero (n v)] [DecidableEq H] [∀ h, DecidableEq (C h)] [DecidableEq V] [Fintype V] in
/-- D7.25.2. `Re⟨α + e₊, α + e₋⟩ ≥ ½‖α‖² - (3/2)(‖e₊‖² + ‖e₋‖²)`. -/
theorem re_star_add_dotProduct_add_ge {m : Type*} [Fintype m] (x e₁ e₂ : m → ℂ) :
    1 / 2 * (star x ⬝ᵥ x).re - 3 / 2 * ((star e₁ ⬝ᵥ e₁).re + (star e₂ ⬝ᵥ e₂).re) ≤
      (star (x + e₁) ⬝ᵥ (x + e₂)).re := by
  simp only [dotProduct, Pi.star_apply, Pi.add_apply, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im]
  nlinarith [sq_nonneg ((x i).re + (e₁ i).re + (e₂ i).re),
    sq_nonneg ((x i).im + (e₁ i).im + (e₂ i).im), sq_nonneg (e₁ i).re, sq_nonneg (e₁ i).im,
    sq_nonneg (e₂ i).re, sq_nonneg (e₂ i).im]

end Round

/-- D7.25 (part (c), `transport:energy-similarity`), Proposition 7.4 (c). With
`Re⟨(T_i + E_{i,+}) v, (T_i + E_{i,-}) v⟩ = Re⟨𝓜^{-s} v, h̄_i 𝓜^s v⟩ ≥ ½‖T_i v‖² -
(3/2)(‖E_{i,+} v‖² + ‖E_{i,-} v‖²)` (`re_inner_errOp_eq`, `re_star_add_dotProduct_add_ge`):
`⟨v, H̄ v⟩ ≤ 2 E₀ + 3 ∑_{i,±} ‖E_{i,±} v‖²`, and Proposition 7.4 (c) holds: if
`H̄ pre = E₀ pre`, then
`⟨v, H̄ v⟩ ≤ 2 E₀ + C a² ℓ^C ∑_i W_i(p) ∑_{j ∈ 𝒥_i} π_j ∫ m_s(u) ∫ η_{i,j}(θ)^{1/8}
dμ_{σ_{j,u}}(θ) du + o_k(1)`, `ℓ^C = ℓ⁴`, `C` universal, the `o_k(1)` uniform in `p ∈ (0, 1)`, in
`pre` and in the replica states (the states are assumed to be densities on `𝒮_k`). -/
theorem step_7_25 : ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)] {K : ℕ}
      {H : Type*} [Fintype H] [DecidableEq H] {Ch : H → Type*} [∀ h, Fintype (Ch h)]
      [∀ h, DecidableEq (Ch h)] (R : Round V K H Ch) {ι : Type*} [Fintype ι]
      (E : EnergyTerms V n ι), R.IsAdmissible → R.SupportCompatible E →
      ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, R.CrossBandCommute n (a / 2) k) →
      (∀ i, (R.splitLeaves E i).Nonempty → logDim (n := n) (E.support i) ≤ ℓ) →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
        ∀ (k : ℕ) (pre : Config n k → ℂ), pre ∈ Replicas.S (fun v => Fin (n v)) k → pre ≠ 0 →
        ∀ p : I, 0 < (p : ℝ) → (p : ℝ) < 1 →
        (∀ j u, IsSymDensity n (R.state n (a / 2) k pre p j u)) →
        ∀ E₀ : ℝ, E.Hbar k *ᵥ pre = (E₀ : ℂ) • pre →
          (star (R.v n (a / 2) k pre p) ⬝ᵥ (E.Hbar k *ᵥ R.v n (a / 2) k pre p)).re ≤
            2 * E₀ + C * a ^ 2 * ℓ ^ 4 * R.energyError n E (a / 2) k pre p + r k := by
  obtain ⟨c₀, C, hc₀, hC, h24⟩ := step_7_24
  refine ⟨c₀, 3 / 2 * C, hc₀, by positivity, ?_⟩
  intro V _ _ n _ K H _ _ Ch _ _ R ι _ E hR hcompat a ℓ ha hℓ haℓ hcomm hℓD
  obtain ⟨r, hr, hr0, hsplit, -⟩ := h24 V n R E hR hcompat ha hℓ haℓ hcomm hℓD
  refine ⟨fun k => 3 / 4 * (Fintype.card ι : ℝ) * r k, by
    simpa using hr.const_mul (3 / 4 * (Fintype.card ι : ℝ)), ?_⟩
  intro k pre _ hpre p hp0 hp1 hstate E₀ hE₀
  have ht : (0 : ℝ) ≤ a / 2 := by positivity
  have hA : ∀ j, (R.input n (a / 2) k j).PosDef := fun j => R.posDef_input hR ht (hcomm k) j
  have hM : (R.root n (a / 2) k p).PosDef := by
    rw [Round.root_eq_eval]; exact MeanTree.posDef_eval hA _
  have hw : ∀ j, 0 < (R.tree p).weight j := R.weight_tree_pos hR hp0 hp1
  set v := R.v n (a / 2) k pre p
  set M := R.root n (a / 2) k p
  set κ := C * a ^ 2 * ℓ ^ 4
  set W : ι → ℝ := fun i => R.splitWeight E i p
  set τ : ι → Round.Leaf H Ch → ℝ → ℝ :=
    fun i j u => (R.state n (a / 2) k pre p j u * R.skew (a / 2) k E i j).trace.re
  set Iη : ι → Round.Leaf H Ch → ℝ → ℝ := fun i j u =>
    ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ)
      ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n (a / 2) k pre p j u))
  set errSq : ι → ℝ := fun i =>
    (star (R.errOp (a / 2) k E i p (1 / 4) *ᵥ v) ⬝ᵥ (R.errOp (a / 2) k E i p (1 / 4) *ᵥ v)).re +
      (star (R.errOp (a / 2) k E i p (-(1 / 4)) *ᵥ v) ⬝ᵥ
        (R.errOp (a / 2) k E i p (-(1 / 4)) *ᵥ v)).re
  have hv1 : star v ⬝ᵥ v = 1 := Matrix.Transport.star_dotProduct_filteredVector hM hpre
  -- D7.25.1–D7.25.2: one term
  have hterm : ∀ i, (star (CFC.sqrt (E.hbar k i) *ᵥ v) ⬝ᵥ (CFC.sqrt (E.hbar k i) *ᵥ v)).re ≤
      2 * (star (M ^ (-(1 / 4) : ℝ) *ᵥ v) ⬝ᵥ (E.hbar k i *ᵥ (M ^ (1 / 4 : ℝ) *ᵥ v))).re +
        3 * errSq i := by
    intro i
    have h1 := R.re_inner_errOp_eq hR ht (hcomm k) E i p v
    have h2 := Round.re_star_add_dotProduct_add_ge (CFC.sqrt (E.hbar k i) *ᵥ v)
      (R.errOp (a / 2) k E i p (1 / 4) *ᵥ v) (R.errOp (a / 2) k E i p (-(1 / 4)) *ᵥ v)
    rw [← add_mulVec, ← add_mulVec, h1] at h2
    simp only [errSq]
    linarith
  -- D7.25.3: `𝓜^s v = pre / N`, `H̄ pre = E₀ pre`, `⟨𝓜^{-s} v, 𝓜^s v⟩ = ⟨v, v⟩ = 1`
  have hMv : M ^ (1 / 4 : ℝ) *ᵥ v =
      ((Real.sqrt (Matrix.Transport.filteredNormSq M pre) : ℂ)⁻¹) • pre := by
    change M ^ (1 / 4 : ℝ) *ᵥ (((Real.sqrt (Matrix.Transport.filteredNormSq M pre) : ℂ)⁻¹) •
      (M ^ (-(1 / 4) : ℝ) *ᵥ pre)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hM.rpow_mul_rpow_neg, Matrix.one_mulVec]
  have hsumO : ∑ i, (star (M ^ (-(1 / 4) : ℝ) *ᵥ v) ⬝ᵥ
      (E.hbar k i *ᵥ (M ^ (1 / 4 : ℝ) *ᵥ v))).re = E₀ := by
    rw [← Complex.re_sum, ← dotProduct_sum, ← Matrix.sum_mulVec]
    change (star (M ^ (-(1 / 4) : ℝ) *ᵥ v) ⬝ᵥ (E.Hbar k *ᵥ (M ^ (1 / 4 : ℝ) *ᵥ v))).re = E₀
    rw [hMv, Matrix.mulVec_smul, hE₀, smul_comm, ← hMv, dotProduct_smul,
      Matrix.Transport.star_mulVec_dotProduct_mulVec', (hM.rpow_isHermitian _).eq,
      hM.rpow_neg_mul_rpow, Matrix.one_mulVec, hv1, smul_eq_mul,
      mul_one, Complex.ofReal_re]
  have hsumT : (star v ⬝ᵥ (E.Hbar k *ᵥ v)).re =
      ∑ i, (star (CFC.sqrt (E.hbar k i) *ᵥ v) ⬝ᵥ (CFC.sqrt (E.hbar k i) *ᵥ v)).re := by
    rw [EnergyTerms.Hbar, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- D7.21.1: `T_i^* T_i = h̄_i`
    rw [Matrix.Transport.star_mulVec_dotProduct_mulVec', conjTranspose_sqrt,
      CFC.sqrt_mul_sqrt_self _ (E.posSemidef_hbar k i).nonneg]
  -- D7.25.4: insert D7.23 (both signs) and D7.24 (`∫ m_s = 1/2` for the remainder)
  have h23 : ∀ i, errSq i ≤ 1 / 2 * W i * ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j *
      ∫ u, m (1 / 4) u * τ i j u := by
    intro i
    obtain ⟨-, hP, hMi⟩ := R.step_7_23 hR ht (hcomm k) E i hp0 hp1 pre
    simp only [errSq, W, τ]
    linarith
  have hint_τ : ∀ i j, Integrable fun u => m (1 / 4) u * τ i j u := fun i j => by
    simp only [τ, Round.trace_state_mul]
    exact Matrix.Transport.integrable_fourierWeight_mul_quadForm hM.isHermitian _ v
  have hint_η : ∀ i j, Integrable fun u => m (1 / 4) u * Iη i j u := fun i j => by
    obtain ⟨Q, hQ⟩ := exists_integral_μ_eq_re_trace (n := n) k (R.continuousOn_splitEta_rpow E i j)
    have e : ∀ u, Iη i j u = (R.state n (a / 2) k pre p j u * Q).trace.re := fun u =>
      hQ _ (hstate j u).1
    simp only [e, Round.trace_state_mul]
    exact Matrix.Transport.integrable_fourierWeight_mul_quadForm hM.isHermitian _ v
  have hm0 : ∀ u, 0 ≤ m (1 / 4) u := fun u => (lemma_7_3.1 (1 / 4) (by norm_num)).2.1 u |>.le
  have h24' : ∀ i, ∀ j ∈ R.splitLeaves E i,
      ∫ u, m (1 / 4) u * τ i j u ≤ κ * (∫ u, m (1 / 4) u * Iη i j u) + r k / 2 := by
    intro i j hj
    calc ∫ u, m (1 / 4) u * τ i j u ≤ ∫ u, (κ * (m (1 / 4) u * Iη i j u) + r k * m (1 / 4) u) :=
          integral_mono (hint_τ i j) (((hint_η i j).const_mul κ).add
            ((integrable_m (by norm_num)).const_mul (r k))) fun u => by
            have hb := hsplit k i j hj _ (hstate j u)
            have := mul_le_mul_of_nonneg_left hb (hm0 u)
            simp only [τ, Iη, κ] at this ⊢
            linarith
      _ = κ * (∫ u, m (1 / 4) u * Iη i j u) + r k / 2 := by
          rw [integral_add ((hint_η i j).const_mul κ) ((integrable_m (by norm_num)).const_mul _),
            integral_const_mul, integral_const_mul, integral_m_quarter]
          ring
  have hW0 : ∀ i, 0 ≤ W i := fun i => Finset.sum_nonneg fun j _ => (hw j).le
  have hW1 : ∀ i, W i ≤ 1 := fun i => by
    rw [← R.sum_weight_tree p]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => (hw j).le
  have hstep : ∀ i, 3 * errSq i ≤ 3 / 2 * κ * (W i * ∑ j ∈ R.splitLeaves E i,
      (R.tree p).weight j * ∫ u, m (1 / 4) u * Iη i j u) + 3 / 4 * r k * (W i * W i) := by
    intro i
    have hle : ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j * ∫ u, m (1 / 4) u * τ i j u ≤
        ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j *
          (κ * (∫ u, m (1 / 4) u * Iη i j u) + r k / 2) :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (h24' i j hj) (hw j).le
    have e : ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j *
        (κ * (∫ u, m (1 / 4) u * Iη i j u) + r k / 2) =
        κ * (∑ j ∈ R.splitLeaves E i, (R.tree p).weight j * ∫ u, m (1 / 4) u * Iη i j u) +
          r k / 2 * W i := by
      simp only [W, Round.splitWeight, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at hle
    have h2 := mul_le_mul_of_nonneg_left hle (by linarith [hW0 i] : (0 : ℝ) ≤ 3 / 2 * W i)
    have h3 := h23 i
    nlinarith
  have hWW : ∑ i, W i * W i ≤ Fintype.card ι := by
    calc ∑ i, W i * W i ≤ ∑ _i : ι, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by nlinarith [hW0 i, hW1 i]
      _ = Fintype.card ι := by simp
  calc (star v ⬝ᵥ (E.Hbar k *ᵥ v)).re
      = ∑ i, (star (CFC.sqrt (E.hbar k i) *ᵥ v) ⬝ᵥ (CFC.sqrt (E.hbar k i) *ᵥ v)).re := hsumT
    _ ≤ ∑ i, (2 * (star (M ^ (-(1 / 4) : ℝ) *ᵥ v) ⬝ᵥ
          (E.hbar k i *ᵥ (M ^ (1 / 4 : ℝ) *ᵥ v))).re + 3 * errSq i) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * E₀ + ∑ i, 3 * errSq i := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumO]
    _ ≤ 2 * E₀ + ∑ i, (3 / 2 * κ * (W i * ∑ j ∈ R.splitLeaves E i,
          (R.tree p).weight j * ∫ u, m (1 / 4) u * Iη i j u) + 3 / 4 * r k * (W i * W i)) := by
        gcongr with i
        exact hstep i
    _ = 2 * E₀ + 3 / 2 * κ * R.energyError n E (a / 2) k pre p + 3 / 4 * r k * ∑ i, W i * W i := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [← add_assoc]; rfl
    _ ≤ 2 * E₀ + 3 / 2 * C * a ^ 2 * ℓ ^ 4 * R.energyError n E (a / 2) k pre p +
          3 / 4 * (Fintype.card ι : ℝ) * r k := by
        have := mul_le_mul_of_nonneg_left hWW (by linarith [hr0 k] : (0 : ℝ) ≤ 3 / 4 * r k)
        simp only [κ]
        linarith

end AreaLaw.Transport
