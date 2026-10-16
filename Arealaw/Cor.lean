import Arealaw.OpNorm
import Arealaw.TraceNorm

/-!
# The correlation measure `Cor`

Brandão–Horodecki's correlation function (BH12, Eq. (1)):

  `Cor(X : Y) = max_{‖M‖,‖N‖ ≤ 1} |tr((M ⊗ N)(ρ_XY − ρ_X ⊗ ρ_Y))|`,

where the maximum ranges over *general* operators, not observables.

`Cor` is total: a `Real.sSup`, which `corSet_nonempty` and `bddAbove_corSet` make the true
supremum.
-/

namespace Arealaw

open scoped Matrix.Norms.L2Operator Kronecker ComplexOrder
open Matrix

/-! ## The correlation functional on a product index -/

section Abstract

variable {𝕜 : Type*} [RCLike 𝕜] {α β α' β' : Type*}
  [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
  [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']

/-- The candidate set of the correlation functional: all values `|tr((M ⊗ N) A)|` over
product operators of operator norm at most one. -/
def corSet (A : Matrix (α × β) (α × β) 𝕜) : Set ℝ :=
  {r | ∃ M : Matrix α α 𝕜, ∃ N : Matrix β β 𝕜, ‖M‖ ≤ 1 ∧ ‖N‖ ≤ 1 ∧ r = ‖((M ⊗ₖ N) * A).trace‖}

/-- The correlation functional `A ↦ sup |tr((M ⊗ N) A)|` (BH12, Eq. (1)). -/
noncomputable def Cor (A : Matrix (α × β) (α × β) 𝕜) : ℝ := sSup (corSet A)

section Generic

variable (A : Matrix (α × β) (α × β) 𝕜)

theorem zero_mem_corSet : 0 ∈ corSet A :=
  ⟨0, 0, by simp, by simp, by simp⟩

theorem corSet_nonempty : (corSet A).Nonempty := ⟨0, zero_mem_corSet A⟩

/-- The candidate set is bounded, by the entrywise ℓ¹-mass of `A`. -/
theorem bddAbove_corSet : BddAbove (corSet A) := by
  refine ⟨∑ z, ∑ w, ‖A w z‖, ?_⟩
  rintro r ⟨M, N, hM, hN, rfl⟩
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine norm_sum_le_of_le _ fun z _ => norm_sum_le_of_le _ fun w _ => ?_
  grw [norm_mul, norm_entry_le_l2_opNorm _ z w, l2_opNorm_kronecker_le_one hM hN, one_mul]

/-- Every candidate bounds `Cor` from below. -/
theorem norm_trace_le_Cor {M : Matrix α α 𝕜} {N : Matrix β β 𝕜} (hM : ‖M‖ ≤ 1) (hN : ‖N‖ ≤ 1) :
    ‖((M ⊗ₖ N) * A).trace‖ ≤ Cor A :=
  le_csSup (bddAbove_corSet A) ⟨M, N, hM, hN, rfl⟩

/-- A uniform bound on the candidates bounds `Cor`. -/
theorem Cor_le {c : ℝ} (h : ∀ (M : Matrix α α 𝕜) (N : Matrix β β 𝕜), ‖M‖ ≤ 1 → ‖N‖ ≤ 1 →
    ‖((M ⊗ₖ N) * A).trace‖ ≤ c) : Cor A ≤ c :=
  csSup_le (corSet_nonempty A) fun _ ⟨M, N, hM, hN, hr⟩ => hr ▸ h M N hM hN

theorem Cor_nonneg : 0 ≤ Cor A := le_csSup (bddAbove_corSet A) (zero_mem_corSet A)

@[simp] theorem Cor_zero : Cor (0 : Matrix (α × β) (α × β) 𝕜) = 0 :=
  le_antisymm (Cor_le _ (by simp)) (Cor_nonneg 0)

/-! ### Invariance under reindexing -/

/-- Half of `corSet_submatrix`: a candidate for the reindexed operator transports back along
the inverse relabelling.  The reverse inclusion is this lemma at `e.symm` and `f.symm`. -/
theorem corSet_submatrix_subset (e : α' ≃ α) (f : β' ≃ β) :
    corSet (A.submatrix (e.prodCongr f) (e.prodCongr f)) ⊆ corSet A := by
  rintro r ⟨M, N, hM, hN, rfl⟩
  refine ⟨M.submatrix e.symm e.symm, N.submatrix f.symm f.symm,
    (l2_opNorm_submatrix M e.symm e.symm).le.trans hM,
    (l2_opNorm_submatrix N f.symm f.symm).le.trans hN, ?_⟩
  rw [show M ⊗ₖ N = (M.submatrix e.symm e.symm ⊗ₖ N.submatrix f.symm f.symm).submatrix
      (e.prodCongr f) (e.prodCongr f) by simp [← kroneckerMap_submatrix_submatrix],
    Matrix.submatrix_mul_equiv, Matrix.trace_submatrix]

theorem corSet_submatrix (e : α' ≃ α) (f : β' ≃ β) :
    corSet (A.submatrix (e.prodCongr f) (e.prodCongr f)) = corSet A := by
  refine (corSet_submatrix_subset A e f).antisymm ?_
  simpa [Prod.map_comp_map] using
    corSet_submatrix_subset (A.submatrix (e.prodCongr f) (e.prodCongr f)) e.symm f.symm

/-- **`Cor` is invariant under reindexing** of the two factors. -/
theorem Cor_submatrix (e : α' ≃ α) (f : β' ≃ β) :
    Cor (A.submatrix (e.prodCongr f) (e.prodCongr f)) = Cor A :=
  congrArg sSup (corSet_submatrix A e f)

/-- Half of `corSet_comm`: a candidate `(M, N)` for the swapped operator is the candidate
`(N, M)` for `A`.  The reverse inclusion is this lemma at the swapped operator. -/
theorem corSet_comm_subset :
    corSet (A.submatrix (Equiv.prodComm β α) (Equiv.prodComm β α)) ⊆ corSet A := by
  rintro r ⟨M, N, hM, hN, rfl⟩
  refine ⟨N, M, hN, hM, ?_⟩
  rw [kronecker_comm_submatrix, Matrix.submatrix_mul_equiv, Matrix.trace_submatrix]

theorem corSet_comm :
    corSet (A.submatrix (Equiv.prodComm β α) (Equiv.prodComm β α)) = corSet A := by
  refine (corSet_comm_subset A).antisymm ?_
  simpa using corSet_comm_subset (A.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _))

/-- **`Cor` is symmetric** in its two factors. -/
theorem Cor_comm : Cor (A.submatrix (Equiv.prodComm β α) (Equiv.prodComm β α)) = Cor A :=
  congrArg sSup (corSet_comm A)

end Generic

/-! ### Bound through the trace norm (`ℂ`-pinned) -/

variable (A : Matrix (α × β) (α × β) ℂ)

/-- `Cor A ≤ ‖A‖₁`: the trace-norm duality bound.  Pinned to `ℂ` by the two upstream facts
it composes, `Matrix.abs_trace_le_traceNorm` and `Matrix.traceNorm_mul_le_opNorm_traceNorm`,
both of which Physlib states for complex matrices only. -/
theorem Cor_le_traceNorm : Cor A ≤ A.traceNorm :=
  Cor_le A fun _ _ hM hN => (Matrix.abs_trace_le_traceNorm _).trans <|
    (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _).trans <|
      mul_le_of_le_one_left A.traceNorm_nonneg (l2_opNorm_kronecker_le_one hM hN)

end Abstract

/-! ## `Cor(X : Y)` of two regions of a chain state -/

section Regions

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  {𝕜 : Type*} [RCLike 𝕜] {U X Y : Finset σ}

/-- The correlation operator `ρ_{X∪Y} − ρ_X ⊗ ρ_Y` of two disjoint regions, on the product
index `Reg X × Reg Y`. -/
noncomputable def SubState.corMatrix (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : Matrix (Reg loc X × Reg loc Y) (Reg loc X × Reg loc Y) 𝕜 :=
  (ρ.restrict (Finset.union_subset hX hY)).M.submatrix (unionEquiv hd).symm (unionEquiv hd).symm
    - (ρ.restrict hX).M ⊗ₖ (ρ.restrict hY).M

/-- The trace of the correlation operator is `t(1 - t)` for the total weight `t`. -/
theorem SubState.trace_corMatrix (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : (ρ.corMatrix hd hX hY).trace = ρ.M.trace * (1 - ρ.M.trace) := by
  simp [corMatrix, Matrix.trace_kronecker, trace_ptrace, mul_one_sub]

/-- The correlation operator is Hermitian. -/
theorem SubState.isHermitian_corMatrix (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : (ρ.corMatrix hd hX hY).IsHermitian :=
  ((ρ.restrict _).psd.isHermitian.submatrix _).sub <|
    kroneckerMap_IsHermitian (ρ.restrict hX).psd.isHermitian (ρ.restrict hY).psd.isHermitian

/-- The correlation operator of `(Y, X)` is that of `(X, Y)` with the two factors swapped. -/
theorem SubState.corMatrix_comm (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : ρ.corMatrix hd.symm hY hX =
      (ρ.corMatrix hd hX hY).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
  rw [corMatrix, corMatrix, unionEquiv_comm hd, restrict_M, restrict_M,
    ptrace_congr (Finset.union_comm X Y) (Finset.union_subset hX hY) (Finset.union_subset hY hX),
    kronecker_comm_submatrix (ptrace hY ρ.M)]
  rfl

/-- The correlation operator of a normalized state is traceless. -/
@[simp] theorem MState.trace_corMatrix (ρ : MState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : (ρ.toSubState.corMatrix hd hX hY).trace = 0 := by
  simp [SubState.trace_corMatrix, ρ.trace_eq_one]

/-- If the `X ∪ Y` marginal of a normalized state is a product of two states, the
correlation operator vanishes. -/
theorem MState.corMatrix_eq_zero_of_product (ρ : MState (Reg loc U) 𝕜) (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) {ς : MState (Reg loc X) 𝕜} {τ : MState (Reg loc Y) 𝕜}
    (hprod : (ρ.restrict (Finset.union_subset hX hY)).M = kronUnion hd ς.M τ.M) :
    ρ.toSubState.corMatrix hd hX hY = 0 := by
  rw [restrict_M] at hprod
  have hXm : ptrace hX ρ.M = ς.M := by
    rw [← ptrace_ptrace Finset.subset_union_left (Finset.union_subset hX hY), hprod,
      ptrace_kronUnion_left_of_trace_one hd _ τ.trace_eq_one]
  have hYm : ptrace hY ρ.M = τ.M := by
    rw [← ptrace_ptrace Finset.subset_union_right (Finset.union_subset hX hY), hprod,
      ptrace_kronUnion_right_of_trace_one hd _ ς.trace_eq_one]
  simp_all [SubState.corMatrix, kronUnion_eq_submatrix]

section DecEqLoc

variable [∀ i, DecidableEq (loc i)]

/-- `Cor(X : Y)` of the paper (BH12, Eq. (1)). -/
noncomputable def SubState.Cor (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : ℝ :=
  Arealaw.Cor (ρ.corMatrix hd hX hY)

theorem SubState.Cor_def (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : ρ.Cor hd hX hY = Arealaw.Cor (ρ.corMatrix hd hX hY) := rfl

theorem SubState.Cor_nonneg (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : 0 ≤ ρ.Cor hd hX hY := Arealaw.Cor_nonneg _

/-- **`Cor(Y : X) = Cor(X : Y)`.**  BH12 writes `Cor(X : Y)` on ordered pairs without stating
the symmetry, then uses the two regions interchangeably. -/
theorem SubState.Cor_comm (ρ : SubState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) : ρ.Cor hd.symm hY hX = ρ.Cor hd hX hY := by
  rw [Cor_def, Cor_def, corMatrix_comm, Arealaw.Cor_comm]

/-- **`Cor` vanishes on product states.** -/
theorem MState.Cor_eq_zero_of_product (ρ : MState (Reg loc U) 𝕜) (hd : Disjoint X Y) (hX : X ⊆ U)
    (hY : Y ⊆ U) {ς : MState (Reg loc X) 𝕜} {τ : MState (Reg loc Y) 𝕜}
    (hprod : (ρ.restrict (Finset.union_subset hX hY)).M = kronUnion hd ς.M τ.M) :
    ρ.toSubState.Cor hd hX hY = 0 := by
  simp [SubState.Cor_def, corMatrix_eq_zero_of_product ρ hd hX hY hprod]

/-- **`Cor(X : Y) ≤ 2` on normalized states.**  Pinned to `ℂ` twice over, by
`Cor_le_traceNorm` and by `Matrix.traceNorm_add_le`. -/
theorem MState.Cor_le_two (ρ : MState (Reg loc U) ℂ) (hd : Disjoint X Y) (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.toSubState.Cor hd hX hY ≤ 2 := by
  have hB : ((ρ.toSubState.restrict hX).M ⊗ₖ (ρ.toSubState.restrict hY).M).traceNorm = 1 := by
    simpa [Matrix.trace_kronecker, trace_ptrace, ρ.trace_eq_one] using
      ((ρ.toSubState.restrict hX).psd.kronecker (ρ.toSubState.restrict hY).psd).traceNorm_eq_trace
  grw [SubState.Cor_def, Cor_le_traceNorm, SubState.corMatrix, sub_eq_add_neg,
    Matrix.traceNorm_add_le, Matrix.traceNorm_neg, hB, ← SubState.submatrix_M,
    SubState.traceNorm_submatrix, ← toSubState_restrict, MState.traceNorm_eq_one,
    one_add_one_eq_two]

end DecEqLoc

end Regions

end Arealaw
