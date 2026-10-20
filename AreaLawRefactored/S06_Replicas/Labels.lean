import AreaLawRefactored.S06_Replicas.Setup

/-!
# §6 Lemma 6.1 (2): commutation and complement equality of Schur labels; D6.7 fixed-factor identity
-/

namespace AreaLaw.Replicas

open Matrix MonoidAlgebra PermutationRepresentation

variable {I : Type*} [DecidableEq I] (ι : I → Type*) (k : ℕ)

/-- `U_{Q'}(σ) U_Q(τ) = U_Q(σ τ σ⁻¹) U_{Q'}(σ)` for `Q ⊆ Q'`, on configurations. -/
private theorem copyPerm_conj {Q Q' : Finset I} (h : Q ⊆ Q') (σ τ : Equiv.Perm (Fin k)) :
    copyPerm ι k Q' σ * copyPerm ι k Q τ = copyPerm ι k Q (σ * τ * σ⁻¹) * copyPerm ι k Q' σ := by
  ext x j f
  simp only [Equiv.Perm.mul_apply, copyPerm_apply, _root_.mul_inv_rev]
  by_cases hf : f ∈ Q
  · simp [hf, h hf]
  · by_cases hf' : f ∈ Q' <;> simp [hf, hf']

variable [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

private theorem U_conj {Q Q' : Finset I} (h : Q ⊆ Q') (σ τ : Equiv.Perm (Fin k)) :
    U ι k Q' σ * U ι k Q τ = U ι k Q (σ * τ * σ⁻¹) * U ι k Q' σ := by
  simp only [U, permOp_apply]
  rw [← permMatrix_mul, ← permMatrix_mul, ← _root_.mul_inv_rev, ← _root_.mul_inv_rev,
    copyPerm_conj ι k h]

/-- A central element of `ℂ[S_k]` acting on `Q` commutes with `U_{Q'}(σ)` for `Q ⊆ Q'`. -/
private theorem commute_U_groupAlgebraRep {Q Q' : Finset I} (h : Q ⊆ Q')
    {a : MonoidAlgebra ℂ (Equiv.Perm (Fin k))}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin k))))
    (σ : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm ι k Q') σ) (groupAlgebraRep (copyPerm ι k Q) a) := by
  rw [Commute, SemiconjBy, groupAlgebraRep_eq_sum, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_smul_comm, smul_mul_assoc]
  have e := fun τ => U_conj ι k h σ τ
  simp only [U] at e
  simp only [e]
  exact Fintype.sum_equiv (MulAut.conj σ).toEquiv _ _ fun τ => by
    simp [IrrepLabel.coeff_conj_of_mem_center ha]

/-- D6.4.8. Label projectors of nested or disjoint subsystems commute. -/
theorem step_6_4_8 {Q Q' : Finset I} (h : Q ⊆ Q' ∨ Disjoint Q Q')
    (l l' : IrrepLabel (Equiv.Perm (Fin k))) : Commute (π ι k Q l) (π ι k Q' l') := by
  rcases h with h | h
  · -- D6.4.8, nested: `U_{Q'}(σ) U_Q(τ) U_{Q'}(σ)⁻¹ = U_Q(στσ⁻¹)`
    exact (commute_groupAlgebraRep_of_forall_commute _
      (fun σ => commute_U_groupAlgebraRep ι k h (IrrepLabel.centralIdem_mem_center l) σ) _).symm
  · -- D6.4.8, disjoint: operators on different tensor factors commute
    exact commute_groupAlgebraRep_of_commute _ _ (commute_copyPerm_of_disjoint ι k h) _ _

/-- D6.4.8. Central label functions of nested or disjoint subsystems commute. -/
theorem commute_labelObservable {Q Q' : Finset I} (h : Q ⊆ Q' ∨ Disjoint Q Q')
    (g g' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (copyPerm ι k Q) g) (labelObservable (copyPerm ι k Q') g') :=
  Commute.sum_left _ _ _ fun l _ => Commute.sum_right _ _ _ fun l' _ =>
    ((step_6_4_8 ι k h l l').smul_left _).smul_right _

/-- D6.4.9. On `𝒮_k`: `π^λ_{Q,k} = π^λ_{Q^c,k}`. -/
theorem step_6_4_9 (Q : Finset I) (l : IrrepLabel (Equiv.Perm (Fin k))) {z : Config ι k → ℂ}
    (hz : z ∈ S ι k) : π ι k Q l *ᵥ z = π ι k Qᶜ l *ᵥ z := by
  -- D6.4.9: `U(σ)z = z ⇒ U_Q(σ)z = U_{Q^c}(σ⁻¹)z`
  have hU : ∀ σ, U ι k Q σ *ᵥ z = U ι k Qᶜ σ⁻¹ *ᵥ z := fun σ => by
    conv_lhs => rw [← hz σ⁻¹]
    rw [show permOp (copyPerm ι k Finset.univ) σ⁻¹ = U ι k Finset.univ σ⁻¹ from rfl,
      U_univ_eq_mul ι k Q, mulVec_mulVec, ← mul_assoc, U, U, permOp_mul_inv_self, one_mul]
  -- D6.4.9: expand the central idempotent, reindex `σ ↦ σ⁻¹`, `coeff(σ⁻¹) = coeff(σ)`
  simp only [π, labelProj, groupAlgebraRep_eq_sum, sum_mulVec, smul_mulVec]
  simp only [show ∀ σ, permOp (copyPerm ι k Q) σ = U ι k Q σ from fun _ => rfl, hU]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => by
    simp [U, IrrepLabel.coeff_inv_of_mem_center (IrrepLabel.centralIdem_mem_center l)]

/-- D6.4 (2). Central label functions of `S_k` commute for nested or disjoint subsystems.
On `𝒮_k`: `π^λ_{Q,k} = π^λ_{Q^c,k}`. -/
theorem lemma_6_1_2 :
    (∀ Q Q' : Finset I, Q ⊆ Q' ∨ Disjoint Q Q' →
      ∀ l l' : IrrepLabel (Equiv.Perm (Fin k)), Commute (π ι k Q l) (π ι k Q' l')) ∧
    (∀ (Q : Finset I) (l : IrrepLabel (Equiv.Perm (Fin k))) (z : Config ι k → ℂ),
      z ∈ S ι k → π ι k Q l *ᵥ z = π ι k Qᶜ l *ᵥ z) :=
  ⟨fun _ _ h => step_6_4_8 ι k h, fun Q l _ hz => step_6_4_9 ι k Q l hz⟩

/-- The vector `φ^{⊗k} ⊗ z`: `φ` on each of the `k` copies of `B`, times `z`. -/
def fixFactor (B : Finset I) (φ : ((f : B) → ι f) → ℂ) (z : Config ι k → ℂ) :
    Config ι k → ℂ :=
  fun x => (∏ j, φ (fun f => x j f)) * z x

/-- D6.7.2. `U_{BQ}(σ)(φ^{⊗k} ⊗ z) = φ^{⊗k} ⊗ U_Q(σ)z`. -/
private theorem U_fixFactor {B Q : Finset I} (φ : ((f : B) → ι f) → ℂ) {z : Config ι k → ℂ}
    (hz : ∀ x y : Config ι k, (∀ j, ∀ f, f ∉ B → x j f = y j f) → z x = z y)
    (σ : Equiv.Perm (Fin k)) :
    permOp (copyPerm ι k (B ∪ Q)) σ *ᵥ fixFactor ι k B φ z =
      fixFactor ι k B φ (permOp (copyPerm ι k Q) σ *ᵥ z) := by
  rw [permOp_mulVec, permOp_mulVec, ← map_inv, ← map_inv]
  ext x
  simp only [fixFactor, Function.comp_apply]
  congr 1
  · simp only [copyPerm_apply, Finset.mem_union, Finset.coe_mem, true_or, if_true, inv_inv]
    exact Equiv.prod_comp σ (fun j => φ fun f => x j f)
  · refine hz _ _ fun j f hf => ?_
    simp only [copyPerm_apply, Finset.mem_union, hf, false_or]

/-- D6.7.1, D6.7.3. The identity extends linearly to the whole group algebra. -/
private theorem groupAlgebraRep_fixFactor {B Q : Finset I} (φ : ((f : B) → ι f) → ℂ)
    {z : Config ι k → ℂ}
    (hz : ∀ x y : Config ι k, (∀ j, ∀ f, f ∉ B → x j f = y j f) → z x = z y)
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin k))) :
    groupAlgebraRep (copyPerm ι k (B ∪ Q)) a *ᵥ fixFactor ι k B φ z =
      fixFactor ι k B φ (groupAlgebraRep (copyPerm ι k Q) a *ᵥ z) := by
  simp only [groupAlgebraRep_eq_sum, sum_mulVec, smul_mulVec, U_fixFactor ι k φ hz]
  ext x
  simp [fixFactor, Finset.sum_apply, Finset.mul_sum, mul_left_comm]

/-- D6.7. `B, Q` disjoint, `φ` fixed on `B`, `z` on the other factors:
`W_{BQ,k}(φ^{⊗k} ⊗ z) = φ^{⊗k} ⊗ W_{Q,k} z`; the same for `F` and every real power of `W`
(each is a central label function `∑ g(λ) π^λ`). -/
theorem eq_replicas_fixed_factor {B Q : Finset I} (_hBQ : Disjoint B Q)
    (φ : ((f : B) → ι f) → ℂ) {z : Config ι k → ℂ}
    (hz : ∀ x y : Config ι k, (∀ j, ∀ f, f ∉ B → x j f = y j f) → z x = z y)
    (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    labelObservable (copyPerm ι k (B ∪ Q)) g *ᵥ fixFactor ι k B φ z =
      fixFactor ι k B φ (labelObservable (copyPerm ι k Q) g *ᵥ z) := by
  have e : ∀ Q' : Finset I, labelObservable (copyPerm ι k Q') g =
      groupAlgebraRep (copyPerm ι k Q') (∑ l, (g l : ℂ) • IrrepLabel.centralIdem l) :=
    fun _ => by rw [labelObservable, map_sum]; simp_rw [map_smul]; rfl
  rw [e, e, groupAlgebraRep_fixFactor ι k φ hz]

/-- D6.7, single label: `π^λ_{BQ,k}(φ^{⊗k} ⊗ z) = φ^{⊗k} ⊗ π^λ_{Q,k} z`. -/
theorem π_fixFactor {B Q : Finset I} (φ : ((f : B) → ι f) → ℂ) {z : Config ι k → ℂ}
    (hz : ∀ x y : Config ι k, (∀ j, ∀ f, f ∉ B → x j f = y j f) → z x = z y)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    π ι k (B ∪ Q) l *ᵥ fixFactor ι k B φ z = fixFactor ι k B φ (π ι k Q l *ᵥ z) :=
  groupAlgebraRep_fixFactor ι k φ hz _

end AreaLaw.Replicas
