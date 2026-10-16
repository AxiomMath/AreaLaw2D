import OpenAI.Scan.SourceScan
import OpenAI.Scan.AugmentedReplicaPrevectorProperties

/-!
# The Schmidt–Bell prevector in augmented coordinates

A label sequence with the properties `OpenAI.Scan.IsSchmidtBellLabels` gives, at every positive
replica count `k`, a replica prevector which, read in the augmented site coordinates of the
scan (physical sites together with the two auxiliary systems `C` and `R`), is a nonzero
symmetric vector of norm at most one and an eigenvector of the copy mean of the physical
Hamiltonian extended by the identity on `C` and `R` [OAI265, Proposition 8.1, eq. (8.7)].
-/

namespace OpenAI.Scan

open Matrix TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- The Schmidt–Bell replica prevector in augmented coordinates is symmetric, nonzero, of norm
at most one, and an eigenvector of the augmented copy-mean Hamiltonian with the eigenvalue of
the supplied state. -/
theorem IsSchmidtBellLabels.augmentedPrevector {q : ℕ}
    {H : Matrix (V → Fin q) (V → Fin q) ℂ} {Ωt : EuclideanSpace ℂ (V → Fin q)} {E₀ : ℝ}
    {Xs : Finset V} {E : Finset (FiniteProduct.Configuration (fun _ : V => Fin q) Xs)}
    {ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))}
    (h : IsSchmidtBellLabels H Ωt E₀ Xs E ell) {k : ℕ} (hk : 0 < k) :
    let nA := augmentedDimensions (V := V) q (fun _ => E.card)
    let pre : Config k (fun v => Fin (nA v)) → ℂ :=
      replicaPrevector Ωt E.card k (ell k) ∘ augmentedSumReplicaCopiesEquiv q E.card k
    pre ∈ symmetricSubspace k (fun v => Fin (nA v)) ∧ pre ≠ 0 ∧
      ‖(EuclideanSpace.equiv (Config k fun v => Fin (nA v)) ℂ).symm pre‖ ≤ 1 ∧
      copyMean nA k (augmentOperator q (fun _ => E.card) H) *ᵥ pre = (E₀ : ℂ) • pre := by
  intro nA pre
  obtain ⟨hne, hnorm, heig, -, -, -⟩ := h.1 k hk
  let eO := augmentedReplicaConfigurationEquiv (V := V) q E.card k
  let eG := globalReplicaCopiesEquiv (fun _ : V => Fin q) (Fin E.card) (Fin E.card) k
  have hpre : pre ∘ eO = replicaPrevector Ωt E.card k (ell k) ∘ eG := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans, Function.comp_assoc, eO,
      Equiv.symm_comp_self, Function.comp_id, eG]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsym : symProj (copyPerm ((v : V ⊕ Bool) → Fin (nA v)) k) *ᵥ pre = pre :=
      symProj_mulVec_augmentedReplicaPrevector q E.card k Ωt (ell k)
    change pre ∈ invariantSubspace _
    rw [← hsym]
    exact symProj_mulVec_mem _ _
  · intro hz
    apply hne
    change WithLp.toLp 2 (replicaPrevector Ωt E.card k (ell k) ∘ eG) = 0
    rw [← hpre, hz]
    rfl
  · have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eO.symm).norm_map (WithLp.toLp 2 pre)
    have hno : ‖WithLp.toLp 2 (pre ∘ eO)‖ ≤ 1 := by
      rw [hpre]
      exact hnorm
    exact hn.symm.trans_le hno
  · have hM : ((k : ℝ)⁻¹ • Matrix.replicaHamiltonian H k) =
        ((k : ℂ)⁻¹ • Matrix.replicaHamiltonian H k) := by
      rw [← Complex.coe_smul]; push_cast; rfl
    rw [hM] at heig
    have key : ((((k : ℂ)⁻¹ • Matrix.replicaHamiltonian H k) ⊗ₖ
        (1 : Matrix ((Fin k → Fin E.card) × (Fin k → Fin E.card))
          ((Fin k → Fin E.card) × (Fin k → Fin E.card)) ℂ)) *ᵥ
          replicaPrevector Ωt E.card k (ell k)) =
        (E₀ : ℂ) • replicaPrevector Ωt E.card k (ell k) := by
      funext x
      have := congrFun heig (eG.symm x)
      simpa only [Matrix.submatrix_mulVec_equiv, WithLp.ofLp_toLp, Function.comp_apply,
        Pi.smul_apply, eG, Equiv.apply_symm_apply, Function.comp_assoc, Equiv.self_comp_symm,
        Function.comp_id] using this
    rw [copyMean_augmentOperator_eq_replicaHamiltonian_kronecker]
    simp only [pre, Matrix.submatrix_mulVec_equiv]
    funext y
    simp only [Function.comp_apply, Pi.smul_apply]
    exact congrFun key _

end OpenAI.Scan
