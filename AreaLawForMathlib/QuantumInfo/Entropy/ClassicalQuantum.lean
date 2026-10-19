import QuantumInfo.States.Entanglement
import QuantumInfo.Entropy.SSA
import QuantumInfo.States.Mixed.TraceDistance

/-!
# Classical–quantum states and the mixture bound for conditional entropy

Extends Physlib `QuantumInfo/Entropy/SSA.lean`: block-diagonal (classical–quantum) states,
their entropy, concavity of `Sᵥₙ`, the mixing bound, the two-sided mixture bound for
`qConditionalEnt` (Winter 2016, Lemma 2), `|S(D|E)| ≤ log d_D`, and the Jordan decomposition of
a difference of states.
-/

open Matrix Real
open scoped ComplexOrder MatrixOrder

/-! ## Library -/

section Library

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

theorem Matrix.charpoly_blockDiagonal {R : Type*} [CommRing R] (M : ι → Matrix d d R) :
    (blockDiagonal M).charpoly = ∏ k, (M k).charpoly := by
  have h : charmatrix (blockDiagonal M) = blockDiagonal fun k => charmatrix (M k) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l
    · subst hkl
      by_cases hij : i = j
      · subst hij; simp [blockDiagonal_apply]
      · simp [blockDiagonal_apply, hij]
    · simp [blockDiagonal_apply, hkl]
  rw [charpoly, h, det_blockDiagonal]
  rfl

theorem Matrix.IsHermitian.eigenvalues_blockDiagonal {M : ι → Matrix d d ℂ}
    (hM : ∀ k, (M k).IsHermitian) :
    Finset.univ.val.map (isHermitian_blockDiagonal_iff.2 hM).eigenvalues =
      Finset.univ.val.bind fun k => Finset.univ.val.map (hM k).eigenvalues := by
  refine Multiset.map_injective (RCLike.ofReal_injective (K := ℂ)) ?_
  rw [Multiset.map_map, Multiset.map_bind,
    ← (isHermitian_blockDiagonal_iff.2 hM).roots_charpoly_eq_eigenvalues,
    charpoly_blockDiagonal, Polynomial.roots_prod]
  · exact Multiset.bind_congr fun k _ => by
      rw [(hM k).roots_charpoly_eq_eigenvalues, Multiset.map_map]
  · exact Finset.prod_ne_zero_iff.2 fun k _ => (Matrix.charpoly_monic _).ne_zero

omit [Fintype d] [DecidableEq d] [Fintype ι] in
theorem Matrix.PosSemidef.blockDiagonal [Finite d] [Finite ι] {M : ι → Matrix d d ℂ}
    (hM : ∀ k, (M k).PosSemidef) : (blockDiagonal M).PosSemidef := by
  classical
  have := Fintype.ofFinite d
  have := Fintype.ofFinite ι
  have hH := isHermitian_blockDiagonal_iff.2 fun k => (hM k).isHermitian
  refine hH.posSemidef_iff_eigenvalues_nonneg.2 fun i => ?_
  have hi : hH.eigenvalues i ∈ Finset.univ.val.map hH.eigenvalues :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  rw [IsHermitian.eigenvalues_blockDiagonal fun k => (hM k).isHermitian] at hi
  obtain ⟨k, -, hk⟩ := Multiset.mem_bind.1 hi
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hk
  exact hj ▸ (hM k).eigenvalues_nonneg j

/-- `Tr η(t A) = t Tr η(A) + η(t) Tr A` for `η = negMulLog`. -/
theorem HermitianMat.trace_cfc_negMulLog_smul (A : HermitianMat d ℂ) (t : ℝ) :
    ((t • A).cfc negMulLog).trace = t * (A.cfc negMulLog).trace + negMulLog t * A.trace := by
  have h1 : t • A = A.cfc (fun x => t * x) := (A.cfc_const_mul_id t).symm
  rw [h1, ← HermitianMat.cfc_comp_apply]
  have h2 : (fun x => negMulLog (t * x)) = fun x => t * negMulLog x + negMulLog t * x := by
    funext x; rw [negMulLog_mul]; ring
  rw [h2, HermitianMat.cfc_add_apply, HermitianMat.cfc_const_mul, HermitianMat.cfc_const_mul_id]
  simp [HermitianMat.trace_add, HermitianMat.trace_smul]

/-- The classical–quantum state `∑ⱼ pⱼ τⱼ ⊗ |j⟩⟨j|` on `d × ι`. -/
noncomputable def MState.cq (p : ProbDistribution ι) (τ : ι → MState d) : MState (d × ι) where
  M := ⟨blockDiagonal fun j => ((p j : ℝ) • (τ j).M).mat,
    (isHermitian_blockDiagonal_iff.2 fun j => ((p j : ℝ) • (τ j).M).H :
      (blockDiagonal fun j => ((p j : ℝ) • (τ j).M).mat).IsHermitian)⟩
  nonneg := HermitianMat.zero_le_iff.2 <| PosSemidef.blockDiagonal fun j =>
    HermitianMat.zero_le_iff.1 (smul_nonneg (p j).2.1 (τ j).nonneg)
  tr := by
    have h : ∀ j, RCLike.re ((p j : ℝ) • (τ j).M).mat.trace = p j := fun j => by
      rw [← HermitianMat.trace_eq_re_trace]; simp [HermitianMat.trace_smul, (τ j).tr]
    refine (HermitianMat.trace_eq_re_trace _).trans ?_
    change RCLike.re (blockDiagonal fun j => ((p j : ℝ) • (τ j).M).mat).trace = 1
    simp only [trace_blockDiagonal, map_sum, h, ProbDistribution.normalized]

variable (p : ProbDistribution ι)

theorem MState.cq_m (τ : ι → MState d) :
    (MState.cq p τ).m = blockDiagonal fun j => (p j : ℝ) • (τ j).m := rfl

/-- `S(∑ⱼ pⱼ τⱼ ⊗ |j⟩⟨j|) = H(p) + ∑ⱼ pⱼ S(τⱼ)`. -/
theorem MState.Sᵥₙ_cq (τ : ι → MState d) :
    Sᵥₙ (MState.cq p τ) = Hₛ p + ∑ j, (p j : ℝ) * Sᵥₙ (τ j) := by
  have hB := fun j => ((p j : ℝ) • (τ j).M).H
  have h1 : Sᵥₙ (MState.cq p τ) =
      ((Finset.univ.val.map (isHermitian_blockDiagonal_iff.2 hB).eigenvalues).map
        negMulLog).sum := by
    rw [Sᵥₙ_eq_trace_cfc_negMulLog, HermitianMat.trace_cfc_eq, Finset.sum_eq_multiset_sum,
      Multiset.map_map]
    rfl
  rw [h1, IsHermitian.eigenvalues_blockDiagonal hB, Multiset.map_bind, Multiset.sum_bind]
  have h2 : ∀ j, ((Finset.univ.val.map (hB j).eigenvalues).map negMulLog).sum =
      (p j : ℝ) * Sᵥₙ (τ j) + negMulLog (p j) := fun j => by
    rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
    have := HermitianMat.trace_cfc_negMulLog_smul (τ j).M (p j)
    rw [HermitianMat.trace_cfc_eq, (τ j).tr, mul_one, ← Sᵥₙ_eq_trace_cfc_negMulLog] at this
    exact this
  simp only [h2, ← Finset.sum_eq_multiset_sum, Finset.sum_add_distrib, Hₛ, H₁]
  ring

/-- `tr_X (∑ⱼ pⱼ τⱼ ⊗ |j⟩⟨j|) = ∑ⱼ pⱼ τⱼ`. -/
theorem MState.cq_traceRight (τ : ι → MState d) :
    (MState.cq p τ).traceRight.m = ∑ j, (p j : ℝ) • (τ j).m := by
  change Matrix.traceRight (blockDiagonal _) = _
  ext a b
  simp [Matrix.traceRight, blockDiagonal_apply, Matrix.sum_apply]

/-- `tr_B (∑ⱼ pⱼ τⱼ ⊗ |j⟩⟨j|) = p` as a diagonal state. -/
theorem MState.cq_traceLeft (τ : ι → MState d) :
    (MState.cq p τ).traceLeft = MState.ofClassical p := by
  refine MState.ext_m ?_
  change Matrix.traceLeft (blockDiagonal _) = diagonal _
  ext k l
  by_cases hkl : k = l
  · subst hkl
    have : ∑ i, (τ k).m i i = 1 := (τ k).tr'
    simp [Matrix.traceLeft, blockDiagonal_apply, ← Finset.mul_sum, this]
  · simp [Matrix.traceLeft, blockDiagonal_apply, hkl]

/-- Tracing out `A` acts blockwise on a cq state over `A × B`. -/
theorem MState.cq_assoc_traceLeft {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (τ : ι → MState (A × B)) :
    (MState.cq p τ).assoc.traceLeft = MState.cq p fun j => (τ j).traceLeft := by
  refine MState.ext_m ?_
  change Matrix.traceLeft ((MState.cq p τ).m.submatrix (Equiv.prodAssoc A B ι).symm
    (Equiv.prodAssoc A B ι).symm) = (MState.cq p fun j => (τ j).traceLeft).m
  rw [MState.cq_m, MState.cq_m]
  ext ⟨b, k⟩ ⟨b', l⟩
  by_cases hkl : k = l
  · subst hkl
    simp only [Matrix.traceLeft, of_apply, submatrix_apply, Equiv.prodAssoc_symm_apply,
      blockDiagonal_apply_eq, Matrix.smul_apply, Complex.real_smul]
    rw [← Finset.mul_sum]; rfl
  · simp [Matrix.traceLeft, blockDiagonal_apply, hkl]

/-- `|j⟩⟨j| ⊗ τ_j ⊗ |j⟩⟨j|` summed against `p` and traced over the first register is the cq
state with the register on the left. -/
theorem MState.cq_cq_constant_traceRight (τ : ι → MState d) :
    (MState.cq p fun j => (MState.cq (ProbDistribution.constant j) fun _ => τ j).SWAP).traceRight =
      (MState.cq p τ).SWAP := by
  refine MState.ext_m ?_
  rw [MState.cq_traceRight]
  ext ⟨k, a⟩ ⟨l, b⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, MState.SWAP, MState.relabel_m, MState.cq_m,
    submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
    blockDiagonal_apply, ProbDistribution.constant_eq]
  by_cases hkl : k = l
  · subst hkl
    rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
    simp
  · simp [hkl]

/-- **Mixing bound**: `S(∑ⱼ pⱼ τⱼ) ≤ H(p) + ∑ⱼ pⱼ S(τⱼ)`, from strong subadditivity of
`∑ⱼ pⱼ |j⟩⟨j| ⊗ τⱼ ⊗ |j⟩⟨j|`. -/
theorem MState.Sᵥₙ_cq_traceRight_le (τ : ι → MState d) :
    Sᵥₙ (MState.cq p τ).traceRight ≤ Sᵥₙ (MState.cq p τ) := by
  let σ := fun j => (MState.cq (ProbDistribution.constant j) fun _ => τ j).SWAP
  have hσ : (fun j => (σ j).traceLeft) = τ := funext fun j => by
    refine MState.ext_m ?_
    change (MState.cq _ _).traceRight.m = _
    rw [MState.cq_traceRight, Finset.sum_eq_single j (fun x _ hx => by
      simp [ProbDistribution.constant_eq, Ne.symm hx]) (by simp)]
    simp [ProbDistribution.constant_eq]
  have hSσ : ∀ j, Sᵥₙ (σ j) = Sᵥₙ (τ j) := fun j => by
    simp only [σ, Sᵥₙ_of_SWAP_eq, MState.Sᵥₙ_cq, Hₛ_constant_eq_zero, zero_add]
    rw [Finset.sum_eq_single j (fun x _ hx => by
      simp [ProbDistribution.constant_eq, Ne.symm hx]) (by simp)]
    simp [ProbDistribution.constant_eq]
  have hT : (MState.cq p σ).traceRight = (MState.cq p τ).SWAP :=
    MState.cq_cq_constant_traceRight p τ
  have h := Sᵥₙ_strong_subadditivity (MState.cq p σ).assoc
  simp only [MState.assoc'_assoc, MState.cq_assoc_traceLeft, Sᵥₙ_of_assoc_eq] at h
  rw [hσ, hT, Sᵥₙ_of_SWAP_eq, MState.Sᵥₙ_cq p σ] at h
  simp only [hSσ] at h
  rw [← MState.Sᵥₙ_cq p τ] at h
  linarith

/-- **Concavity**: `∑ⱼ pⱼ S(τⱼ) ≤ S(∑ⱼ pⱼ τⱼ)`, from subadditivity of the cq state. -/
theorem MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight (τ : ι → MState d) :
    ∑ j, (p j : ℝ) * Sᵥₙ (τ j) ≤ Sᵥₙ (MState.cq p τ).traceRight := by
  have h := Sᵥₙ_subadditivity (MState.cq p τ)
  rw [MState.Sᵥₙ_cq, MState.cq_traceLeft, Sᵥₙ_ofClassical] at h
  linarith

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

/-- **Mixture bound, lower half** (Winter 2016, Lemma 2): `∑ⱼ pⱼ S(D|E)_{τⱼ} ≤ S(D|E)_τ` for
`τ = ∑ⱼ pⱼ τⱼ`, by strong subadditivity of the cq state with the register on `E`'s side. -/
theorem MState.sum_qConditionalEnt_le (τ : ι → MState (D × E)) :
    ∑ j, (p j : ℝ) * qConditionalEnt (τ j) ≤ qConditionalEnt (MState.cq p τ).traceRight := by
  have h := qConditionalEnt_strong_subadditivity (MState.cq p τ).assoc
  simp only [qConditionalEnt, MState.assoc'_assoc, MState.cq_assoc_traceLeft, Sᵥₙ_of_assoc_eq,
    MState.Sᵥₙ_cq] at h ⊢
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- **Mixture bound, upper half** (Winter 2016, Lemma 2): `S(D|E)_τ ≤ ∑ⱼ pⱼ S(D|E)_{τⱼ} + H(p)`
for `τ = ∑ⱼ pⱼ τⱼ`: the mixing bound on `DE` and concavity on `E`. -/
theorem MState.qConditionalEnt_le (τ : ι → MState (D × E)) :
    qConditionalEnt (MState.cq p τ).traceRight ≤ ∑ j, (p j : ℝ) * qConditionalEnt (τ j) + Hₛ p := by
  have h₁ := MState.Sᵥₙ_cq_traceRight_le p τ
  have h₂ := MState.sum_Sᵥₙ_le_Sᵥₙ_cq_traceRight p fun j => (τ j).traceLeft
  rw [← MState.cq_assoc_traceLeft, MState.traceLeft_right_assoc] at h₂
  rw [MState.Sᵥₙ_cq] at h₁
  simp only [qConditionalEnt, mul_sub, Finset.sum_sub_distrib]
  linarith

omit [Fintype E] [DecidableEq E] in
/-- **Dimension bound** (D2.2 item 4): `|S(D|E)_ρ| ≤ log d_D`. -/
theorem abs_qConditionalEnt_le_log_card [Fintype E] [DecidableEq E] (ρ : MState (D × E)) :
    |qConditionalEnt ρ| ≤ Real.log (Fintype.card D) := by
  have h1 := Sᵥₙ_subadditivity ρ
  have h2 := Sᵥₙ_triangle_subaddivity ρ
  have h3 := Sᵥₙ_le_log_d ρ.traceRight
  rw [Finset.card_univ] at h3
  rw [abs_le] at h2 ⊢
  unfold qConditionalEnt
  constructor <;> linarith [h2.1, h2.2]

/-- `Tr A⁺ = (‖A‖₁ + Tr A) / 2`. -/
theorem HermitianMat.trace_posPart (A : HermitianMat d ℂ) :
    (A⁺).trace = (A.mat.traceNorm + A.trace) / 2 := by
  obtain ⟨e, he⟩ := A.cfc_eigenvalues fun x => x ⊔ 0
  rw [HermitianMat.posPart_eq_cfc_max, ← HermitianMat.sum_eigenvalues_eq_trace, he,
    Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues A.H, ← A.sum_eigenvalues_eq_trace,
    ← Finset.sum_add_distrib, Finset.sum_div]
  rw [show ∑ i, ((fun x => x ⊔ 0) ∘ A.H.eigenvalues ∘ e) i = ∑ i, A.H.eigenvalues i ⊔ 0 from
    e.sum_comp fun i => A.H.eigenvalues i ⊔ 0]
  have key (x : ℝ) : x ⊔ 0 = (|x| + x) / 2 := by
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  exact Finset.sum_congr rfl fun i _ => key _

/-- **Jordan decomposition of `ρ - σ`**: `ρ - σ = P - N` with `P, N ≥ 0` and
`Tr P = Tr N = ½‖ρ - σ‖₁`. -/
theorem MState.exists_sub_eq_sub (ρ σ : MState d) :
    ∃ P N : HermitianMat d ℂ, 0 ≤ P ∧ 0 ≤ N ∧ ρ.M - σ.M = P - N ∧
      P.trace = TrDistance ρ σ ∧ N.trace = TrDistance ρ σ := by
  set A := ρ.M - σ.M
  have hA : A.trace = 0 := by simp [A, HermitianMat.trace_sub, ρ.tr, σ.tr]
  have hP : (A⁺).trace = TrDistance ρ σ := by
    rw [HermitianMat.trace_posPart, hA, TrDistance]; simp [A]; ring
  refine ⟨A⁺, A⁻, A.posPart_nonneg, A.negPart_nonneg, A.posPart_add_negPart.symm, hP, ?_⟩
  have h := congrArg HermitianMat.trace A.posPart_add_negPart
  rw [HermitianMat.trace_sub, hA, hP] at h
  linarith

end Library
