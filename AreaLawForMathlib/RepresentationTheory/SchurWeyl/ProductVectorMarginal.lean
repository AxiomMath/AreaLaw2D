import AreaLawForMathlib.RepresentationTheory.SchurWeyl.SubsystemTransport
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.UnitaryCommutant
import AreaLawForMathlib.Analysis.Matrix.MatrixPowers

/-!
# Subsystem observables in a product vector

The expectation in `θ^{⊗k}` of an operator on `Q^{⊗k}` is its trace against the `k`-th power of the
one-copy marginal.
-/

open Matrix PermutationRepresentation
open scoped Kronecker ComplexOrder MatrixOrder

namespace TensorPower

section Marginal

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]

/-- The one-copy marginal `ρ_Q = Tr_{Qᶜ} |θ⟩⟨θ|` of a vector `θ` on `⨂_f ℂ^{ι f}`. -/
noncomputable def vecMarginal (θ : ((f : F) → ι f) → ℂ) (Q : Finset F) :
    Matrix (SubConfig ι Q) (SubConfig ι Q) ℂ :=
  Matrix.of fun a a' => ∑ b : ComplConfig ι Q,
    θ ((Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm (a, b)) *
      star (θ ((Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm (a', b)))

theorem vecMarginal_apply (θ : ((f : F) → ι f) → ℂ) (Q : Finset F) (a a' : SubConfig ι Q) :
    vecMarginal ι θ Q a a' = ∑ b : ComplConfig ι Q,
      θ ((Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm (a, b)) *
        star (θ ((Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm (a', b))) := rfl

theorem posSemidef_vecMarginal (θ : ((f : F) → ι f) → ℂ) (Q : Finset F) :
    (vecMarginal ι θ Q).PosSemidef := by
  have h : vecMarginal ι θ Q = ∑ b : ComplConfig ι Q,
      vecMulVec (fun a => θ ((Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm (a, b)))
        (star fun a => θ ((Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm (a, b))) := by
    ext a a'
    simp [vecMarginal, vecMulVec_apply, Matrix.sum_apply]
  exact h ▸ Finset.sum_induction _ PosSemidef (fun _ _ ha hb => ha.add hb) PosSemidef.zero
    fun b _ => posSemidef_vecMulVec_self_star _

/-- `Tr ρ_Q = ‖θ‖²`. -/
theorem trace_vecMarginal (θ : ((f : F) → ι f) → ℂ) (Q : Finset F) :
    (vecMarginal ι θ Q).trace = ∑ x, θ x * star (θ x) := by
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm, Fintype.sum_prod_type]
  rfl

variable [∀ f, DecidableEq (ι f)]

/-- `⟨θ^{⊗k}, (G ⊗ 1) θ^{⊗k}⟩ = Tr(ρ_Q^{⊗k} G)` for an operator `G` on `Q^{⊗k}`. -/
theorem dotProduct_kronecker_one_mulVec_prod (θ : ((f : F) → ι f) → ℂ) (Q : Finset F) (k : ℕ)
    (G : Matrix (Fin k → SubConfig ι Q) (Fin k → SubConfig ι Q) ℂ) :
    star (fun x : Config k ι => ∏ j, θ (x j)) ⬝ᵥ
        ((reindex (splitEquiv ι k Q) (splitEquiv ι k Q)).symm
            (G ⊗ₖ (1 : Matrix (Fin k → ComplConfig ι Q) (Fin k → ComplConfig ι Q) ℂ)) *ᵥ
          fun x : Config k ι => ∏ j, θ (x j)) =
      (tensorPow (vecMarginal ι θ Q) * G).trace := by
  set e := splitEquiv ι k Q
  have hv : ∀ p, (fun x : Config k ι => ∏ j, θ (x j)) (e.symm p) =
      ∏ j, θ ((Equiv.piEquivPiSubtypeProd (· ∈ Q) ι).symm (p.1 j, p.2 j)) := fun p => rfl
  simp only [dotProduct, mulVec, Pi.star_apply]
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp, reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply,
    Equiv.apply_symm_apply, hv, Fintype.sum_prod_type, kroneckerMap_apply, one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Finset.mul_sum]
  simp only [trace, diag, Matrix.mul_apply, tensorPow_apply, vecMarginal_apply, Fintype.prod_sum,
    Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ => by
      rw [star_prod, Finset.prod_mul_distrib]; ring

/-- `⟨θ^{⊗k}, h(F_Q) θ^{⊗k}⟩ = Tr(ρ_Q^{⊗k} h(F))` for every label observable of the copy
permutations of `Q`. -/
theorem dotProduct_labelObservable_mulVec_prod (θ : ((f : F) → ι f) → ℂ) (Q : Finset F)
    (k : ℕ) (h : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    star (fun x : Config k ι => ∏ j, θ (x j)) ⬝ᵥ
        (labelObservable (subsystemPerm k ι Q) h *ᵥ fun x : Config k ι => ∏ j, θ (x j)) =
      (tensorPow (vecMarginal ι θ Q) * labelObservable (copyPerm (SubConfig ι Q) k) h).trace := by
  have e : ∀ l, labelProj (subsystemPerm k ι Q) l =
      (reindex (splitEquiv ι k Q) (splitEquiv ι k Q)).symm
        (labelProj (copyPerm (SubConfig ι Q) k) l ⊗ₖ
          (1 : Matrix (Fin k → ComplConfig ι Q) (Fin k → ComplConfig ι Q) ℂ)) := fun l => by
    rw [Equiv.eq_symm_apply, labelProj_subsystemPerm_eq]
  simp only [labelObservable, sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, e,
    dotProduct_kronecker_one_mulVec_prod, Finset.mul_sum, mul_smul_comm, trace_sum, trace_smul]

end Marginal

section Factor

variable {F : Type*} [DecidableEq F] (ι : F → Type*) {X B : Finset F}

/-- The `X`-part of a configuration of `Bᶜ`, for `X` disjoint from `B`. -/
def complRestr (h : Disjoint X B) (b : ComplConfig ι B) : SubConfig ι X :=
  fun v => b ⟨v.1, Finset.disjoint_left.mp h v.2⟩

/-- A configuration of `Bᶜ` with its `X`-part replaced by `y`. -/
def complReplace (b : ComplConfig ι B) (y : SubConfig ι X) : ComplConfig ι B :=
  fun v => if hv : v.1 ∈ X then y ⟨v.1, hv⟩ else b v

theorem complRestr_complReplace (h : Disjoint X B) (b : ComplConfig ι B) (y : SubConfig ι X) :
    complRestr ι h (complReplace ι b y) = y := by
  funext v
  simp [complRestr, complReplace, v.2]

theorem complReplace_complReplace (b : ComplConfig ι B) (y y' : SubConfig ι X) :
    complReplace ι (complReplace ι b y) y' = complReplace ι b y' := by
  funext v
  by_cases hv : v.1 ∈ X <;> simp [complReplace, hv]

theorem complReplace_complRestr (h : Disjoint X B) (b : ComplConfig ι B) :
    complReplace ι b (complRestr ι h b) = b := by
  funext v
  by_cases hv : v.1 ∈ X <;> simp [complReplace, complRestr, hv]

variable [∀ f, Fintype (ι f)] [Fintype F]

/-- Summing over the configurations of `Bᶜ` a product of a function of the `X`-part
(`X ∩ B = ∅`) and a function insensitive to the `X`-part factorizes:
`dim 𝓗_X · ∑_b f(b_X) G(b) = (∑_y f(y)) (∑_b G(b))`. -/
theorem card_mul_sum_complRestr_mul (h : Disjoint X B) (f : SubConfig ι X → ℂ)
    (G : ComplConfig ι B → ℂ) (hG : ∀ b (y : SubConfig ι X), G (complReplace ι b y) = G b) :
    (Fintype.card (SubConfig ι X) : ℂ) * ∑ b, f (complRestr ι h b) * G b =
      (∑ y, f y) * ∑ b, G b := by
  let Ψ : SubConfig ι X × ComplConfig ι B ≃ ComplConfig ι B × SubConfig ι X :=
    { toFun := fun p => (complReplace ι p.2 p.1, complRestr ι h p.2)
      invFun := fun q => (complRestr ι h q.1, complReplace ι q.1 q.2)
      left_inv := fun p => by
        simp [complRestr_complReplace, complReplace_complReplace, complReplace_complRestr]
      right_inv := fun q => by
        simp [complRestr_complReplace, complReplace_complReplace, complReplace_complRestr] }
  have e : (∑ y, f y) * ∑ b, G b =
      ∑ p : SubConfig ι X × ComplConfig ι B,
        (fun q : ComplConfig ι B × SubConfig ι X => f (complRestr ι h q.1) * G q.1) (Ψ p) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by simp [Ψ, complRestr_complReplace, hG]
  rw [e, Equiv.sum_comp Ψ (fun q => f (complRestr ι h q.1) * G q.1), Fintype.sum_prod_type]
  simp [Finset.mul_sum]

end Factor

section Monotone

variable {Ω : Type*} {k : ℕ}

/-- The tensor product `⊗_j M_j` of matrices on `Ω`. -/
def tensorFamily (M : Fin k → Matrix Ω Ω ℂ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  Matrix.of fun x y => ∏ j, M j (x j) (y j)

theorem tensorFamily_mul [Fintype Ω] (M N : Fin k → Matrix Ω Ω ℂ) :
    tensorFamily M * tensorFamily N = tensorFamily fun j => M j * N j := by
  ext x y
  simp only [tensorFamily, Matrix.mul_apply, of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun z _ => (Finset.prod_mul_distrib).symm

theorem conjTranspose_tensorFamily (M : Fin k → Matrix Ω Ω ℂ) :
    (tensorFamily M)ᴴ = tensorFamily fun j => (M j)ᴴ := by
  ext x y
  simp [tensorFamily, conjTranspose_apply, star_prod]

theorem posSemidef_tensorFamily [Finite Ω] {M : Fin k → Matrix Ω Ω ℂ}
    (hM : ∀ j, (M j).PosSemidef) :
    (tensorFamily M).PosSemidef := by
  classical
  have := Fintype.ofFinite Ω
  have hs : ∀ j, (CFC.sqrt (M j))ᴴ * CFC.sqrt (M j) = M j := fun j => by
    rw [← star_eq_conjTranspose, (CFC.sqrt_nonneg (M j)).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self _ (hM j).nonneg]
  have h : tensorFamily M = (tensorFamily fun j => CFC.sqrt (M j))ᴴ *
      tensorFamily fun j => CFC.sqrt (M j) := by
    rw [conjTranspose_tensorFamily, tensorFamily_mul]; simp only [hs]
  exact h ▸ posSemidef_conjTranspose_mul_self _

theorem tensorPow_eq_tensorFamily [DecidableEq Ω] (A : Matrix Ω Ω ℂ) :
    tensorPow (k := k) A = tensorFamily fun _ => A := by
  ext x y; rw [tensorPow_apply]; rfl

/-- `(c A)^{⊗k} = c^k A^{⊗k}`. -/
theorem tensorPow_real_smul [DecidableEq Ω] (c : ℝ) (A : Matrix Ω Ω ℂ) :
    tensorPow (k := k) (c • A) = (c ^ k) • tensorPow (k := k) A := by
  ext x y
  simp only [tensorPow_apply, Matrix.smul_apply, Complex.real_smul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Complex.ofReal_pow]

/-- `A^{⊗k}` is positive semidefinite for `A ≥ 0`. -/
theorem posSemidef_tensorPow_of_posSemidef [Finite Ω] [DecidableEq Ω] {A : Matrix Ω Ω ℂ}
    (hA : A.PosSemidef) :
    (tensorPow (k := k) A).PosSemidef := by
  rw [tensorPow_eq_tensorFamily]
  exact posSemidef_tensorFamily fun _ => hA

/-- `0 ≤ A ≤ B ⇒ A^{⊗k} ≤ B^{⊗k}`. -/
theorem tensorPow_le_tensorPow [Finite Ω] [DecidableEq Ω] {A B : Matrix Ω Ω ℂ}
    (hA : A.PosSemidef) (hAB : A ≤ B) :
    tensorPow (k := k) A ≤ tensorPow (k := k) B := by
  have := Fintype.ofFinite Ω
  set D := B - A
  have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)
  have hexp : tensorPow (k := k) B = ∑ s : Finset (Fin k),
      tensorFamily fun j => if j ∈ s then D else A := by
    ext x y
    rw [tensorPow_apply, Matrix.sum_apply]
    rw [show B = D + A by simp [D]]
    simp only [Matrix.add_apply, tensorFamily, of_apply]
    rw [Fintype.prod_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.prod_mul_prod_compl s]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by rw [if_pos hj]
    · exact Finset.prod_congr rfl fun j hj => by rw [if_neg (Finset.mem_compl.mp hj)]
  have h0 : tensorFamily (k := k) (fun j => if j ∈ (∅ : Finset (Fin k)) then D else A) =
      tensorPow A := by
    simp [tensorPow_eq_tensorFamily]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅), h0, Matrix.le_iff, add_sub_cancel_left]
  refine Finset.sum_induction _ PosSemidef (fun _ _ ha hb => ha.add hb) PosSemidef.zero
    fun s _ => posSemidef_tensorFamily fun j => ?_
  split_ifs; exacts [hD, hA]

end Monotone

end TensorPower
