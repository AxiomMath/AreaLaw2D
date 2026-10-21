import AreaLawRefactored.S08_Comparators.Interfaces
import AreaLawRefactored.S06_Replicas.Ported.ReplicaGroupedInverse
import AreaLawRefactored.S06_Replicas.Ported.GroupedLabelSymmetricSupport
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.CopySplit
import AreaLawForMathlib.Analysis.Matrix.ReducedVectorState
import AreaLawForMathlib.LinearAlgebra.Matrix.PiTensorOp

/-!
# §8.4 The inverse metric on copies near the ground state: components (D8.24–D8.27)

Digest `digest/08-comparators.md` D8.24–D8.27, paper `paper/sections/07-comparators.tex`
441–493. No geometry: an arbitrary finite physical site type. For `B ⊆ {1..k}` the copies split
by `split B : Fin (k - r) ⊕ Fin r ≃ Fin k` into the good copies `Bᶜ` and the bad copies `B`;
the good- and bad-copy permutations are `TensorPower.groupHom₁/₂ (split B)` and their labels
are the subgroup labels of Lemma 6.1 (4).
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

/-! ## One copy of `𝒱`: physical operators -/

section OneCopy

variable {σ : Type u} {n : σ → ℕ} (d : ℕ)

/-- One copy of `𝒱` as the physical configuration and the auxiliary pair. -/
def siteSplit : SiteConfig (dims n d) ≃ SiteConfig n × (Fin d × Fin d) where
  toFun x := (physPart x, (x .C, x .R))
  invFun p s := match s with
    | .phys v => p.1 v
    | .C => p.2.1
    | .R => p.2.2
  left_inv x := by funext s; cases s <;> rfl
  right_inv p := rfl

@[simp]
theorem physPart_siteSplit_symm (p : SiteConfig n × (Fin d × Fin d)) :
    physPart ((siteSplit d).symm p) = p.1 := rfl

@[simp]
theorem siteSplit_symm_C (p : SiteConfig n × (Fin d × Fin d)) :
    (siteSplit d).symm p .C = p.2.1 := rfl

@[simp]
theorem siteSplit_symm_R (p : SiteConfig n × (Fin d × Fin d)) :
    (siteSplit d).symm p .R = p.2.2 := rfl

@[simp]
theorem siteSplit_apply (x : SiteConfig (dims n d)) :
    siteSplit d x = (physPart x, (x .C, x .R)) := rfl

/-- `M ⊗ 1_{CR}`: a physical one-copy operator on `𝒱`. -/
def physOp (M : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Matrix (SiteConfig (dims n d)) (SiteConfig (dims n d)) ℂ :=
  reindex (siteSplit d).symm (siteSplit d).symm
    (M ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))

theorem physOp_apply (M : Matrix (SiteConfig n) (SiteConfig n) ℂ) (x y : SiteConfig (dims n d)) :
    physOp d M x y = M (physPart x) (physPart y) *
      if x .C = y .C ∧ x .R = y .R then 1 else 0 := by
  have h : physOp d M x y = M (physPart x) (physPart y) *
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (x .C, x .R) (y .C, y .R) := rfl
  rw [h, one_apply]
  congr 1
  exact if_congr Prod.ext_iff rfl rfl

theorem physOp_mul [Fintype σ] [DecidableEq σ] (M N : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    physOp d M * physOp d N = physOp d (M * N) := by
  rw [physOp, physOp, physOp, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv,
    ← mul_kronecker_mul, one_mul]

theorem physOp_one [Fintype σ] : physOp d (1 : Matrix (SiteConfig n) (SiteConfig n) ℂ) = 1 := by
  rw [physOp, one_kronecker_one, reindex_apply, submatrix_one_equiv]

theorem physOp_add (M N : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    physOp d (M + N) = physOp d M + physOp d N := by
  ext x y
  simp only [physOp_apply, Matrix.add_apply, add_mul]

theorem physOp_sub (M N : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    physOp d (M - N) = physOp d M - physOp d N := by
  rw [eq_sub_iff_add_eq, ← physOp_add, sub_add_cancel]

theorem conjTranspose_physOp (M : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    (physOp d M)ᴴ = physOp d Mᴴ := by
  rw [physOp, physOp, conjTranspose_reindex, conjTranspose_kronecker, conjTranspose_one]

end OneCopy

/-! ## D8.23, D8.24 The excited-copy components `Π_B` -/

section Components

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} (D : PhysData n) (d : ℕ)

/-- `|Ω̃⟩⟨Ω̃|` on the physical system. -/
noncomputable def physGround : Matrix (SiteConfig n) (SiteConfig n) ℂ :=
  vecMulVec D.Ω (star D.Ω)

theorem physGround_mul_self : physGround D * physGround D = physGround D := by
  ext x y
  simp only [physGround, mul_apply, vecMulVec_apply, Pi.star_apply]
  have h : ∑ w, star (D.Ω w) * D.Ω w = 1 := D.norm_Ω
  calc ∑ w, D.Ω x * star (D.Ω w) * (D.Ω w * star (D.Ω y)) =
      D.Ω x * (∑ w, star (D.Ω w) * D.Ω w) * star (D.Ω y) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun w _ => by ring
    _ = D.Ω x * star (D.Ω y) := by rw [h, mul_one]

theorem isHermitian_physGround : (physGround D).IsHermitian := by
  ext x y
  simp [physGround, vecMulVec_apply, mul_comm]

theorem groundProj_eq : groundProj D d = physOp d (physGround D) := by
  ext x y
  simp [groundProj, physOp_apply, physGround, vecMulVec_apply]

theorem excProj_eq : excProj D d = physOp d (1 - physGround D) := by
  rw [excProj, physOp_sub, physOp_one, groundProj_eq]

/-- The one-copy physical factor of `Π_B` at copy `j`. -/
noncomputable def compFactor {k : ℕ} (B : Finset (Fin k)) (j : Fin k) :
    Matrix (SiteConfig n) (SiteConfig n) ℂ :=
  if j ∈ B then 1 - physGround D else physGround D

theorem compProj_eq (k : ℕ) (B : Finset (Fin k)) :
    compProj D d k B = piTensorOp fun j => physOp d (compFactor D B j) := by
  ext x y
  simp only [compProj, piTensorOp_apply, compFactor]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [excProj_eq, groundProj_eq]

/-- `Π_B(x, y) = ∏_j c_j(x_j, y_j) · [x, y agree on every auxiliary factor]`. -/
theorem compProj_apply (k : ℕ) (B : Finset (Fin k)) (x y : Transport.Config (dims n d) k) :
    compProj D d k B x y = (∏ j, compFactor D B j (physPart (x j)) (physPart (y j))) *
      if ∀ j, x j .C = y j .C ∧ x j .R = y j .R then 1 else 0 := by
  rw [compProj_eq, piTensorOp_apply]
  simp only [physOp_apply]
  rw [Finset.prod_mul_distrib, Fintype.prod_boole]
  by_cases h : ∀ j, x j .C = y j .C ∧ x j .R = y j .R <;> simp [h]

theorem compFactor_mul (k : ℕ) (B B' : Finset (Fin k)) (j : Fin k) :
    compFactor D B j * compFactor D B' j =
      if (j ∈ B ↔ j ∈ B') then compFactor D B j else 0 := by
  have hG := physGround_mul_self D
  have h1 : (1 - physGround D) * physGround D = 0 := by rw [sub_mul, one_mul, hG, sub_self]
  have h2 : physGround D * (1 - physGround D) = 0 := by rw [mul_sub, mul_one, hG, sub_self]
  have h3 : (1 - physGround D) * (1 - physGround D) = 1 - physGround D := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hG, sub_self, sub_zero]
  unfold compFactor
  by_cases hB : j ∈ B <;> by_cases hB' : j ∈ B' <;> simp [hB, hB', h1, h2, h3, hG]

/-- D8.24.1. `Π_B Π_{B'} = δ_{BB'} Π_B`. -/
theorem compProj_mul (k : ℕ) (B B' : Finset (Fin k)) :
    compProj D d k B * compProj D d k B' = if B = B' then compProj D d k B else 0 := by
  rw [compProj_eq, compProj_eq, piTensorOp_mul]
  simp only [physOp_mul, compFactor_mul]
  split_ifs with h
  · subst h
    congr 1
    funext j
    rw [if_pos Iff.rfl]
  · obtain ⟨j, hj⟩ : ∃ j, ¬(j ∈ B ↔ j ∈ B') := by
      by_contra! hc
      exact h (Finset.ext hc)
    ext x y
    rw [piTensorOp_apply, Matrix.zero_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [if_neg hj]
    simp [physOp_apply]

/-- D8.24.1. `∑_B Π_B = 1`. -/
theorem sum_compProj (k : ℕ) : ∑ B : Finset (Fin k), compProj D d k B = 1 := by
  simp only [compProj_eq, compFactor]
  have h : ∀ B : Finset (Fin k), (fun j => physOp d (if j ∈ B then 1 - physGround D
      else physGround D)) = fun j => if j ∈ B then physOp d (1 - physGround D)
      else physOp d (physGround D) := fun B => by
    funext j; split_ifs <;> rfl
  simp only [h]
  rw [sum_piTensorOp_ite, ← physOp_add, sub_add_cancel, physOp_one, piTensorOp_one]

theorem isHermitian_compProj (k : ℕ) (B : Finset (Fin k)) :
    (compProj D d k B).IsHermitian := by
  rw [IsHermitian, compProj_eq, conjTranspose_piTensorOp]
  congr 1
  funext j
  rw [conjTranspose_physOp]
  unfold compFactor
  have hG := isHermitian_physGround D
  split_ifs
  · rw [conjTranspose_sub, conjTranspose_one, hG.eq]
  · rw [hG.eq]

/-- `Π_B(x, y) = ∏_{j ∈ B} (1 - |Ω̃⟩⟨Ω̃|)(x_j, y_j) ∏_{j ∉ B} Ω̃(x_j) Ω̃(y_j)^* · [aux agree]`. -/
theorem compProj_apply' (k : ℕ) (B : Finset (Fin k)) (x y : Transport.Config (dims n d) k) :
    compProj D d k B x y = (∏ j ∈ Bᶜ, D.Ω (physPart (x j))) *
      ((∏ j ∈ Bᶜ, star (D.Ω (physPart (y j)))) *
        (∏ j ∈ B, (1 - physGround D) (physPart (x j)) (physPart (y j))) *
        if ∀ j, x j .C = y j .C ∧ x j .R = y j .R then 1 else 0) := by
  rw [compProj_apply, ← Finset.prod_mul_prod_compl B]
  have h1 : ∏ j ∈ B, compFactor D B j (physPart (x j)) (physPart (y j)) =
      ∏ j ∈ B, (1 - physGround D) (physPart (x j)) (physPart (y j)) :=
    Finset.prod_congr rfl fun j hj => by simp [compFactor, hj]
  have h2 : ∏ j ∈ Bᶜ, compFactor D B j (physPart (x j)) (physPart (y j)) =
      (∏ j ∈ Bᶜ, D.Ω (physPart (x j))) * ∏ j ∈ Bᶜ, star (D.Ω (physPart (y j))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j hj => by
      simp [compFactor, Finset.mem_compl.mp hj, physGround, vecMulVec_apply]
  rw [h1, h2]
  ring

/-- D8.24.2. The vector on the factors other than the good physical ones: `u_B = Ω̃^{⊗Bᶜ} ⊗ φ`. -/
noncomputable def goodRest (k : ℕ) (B : Finset (Fin k)) (u : Transport.Config (dims n d) k → ℂ) :
    Transport.Config (dims n d) k → ℂ :=
  fun x => ∑ y, (∏ j ∈ Bᶜ, star (D.Ω (physPart (y j)))) *
    (∏ j ∈ B, (1 - physGround D) (physPart (x j)) (physPart (y j))) *
    (if ∀ j, x j .C = y j .C ∧ x j .R = y j .R then 1 else 0) * u y

/-- D8.24.2. `u_B(x) = ∏_{j ∉ B} Ω̃(x_j) · φ(x)`. -/
theorem compProj_mulVec_apply (k : ℕ) (B : Finset (Fin k))
    (u : Transport.Config (dims n d) k → ℂ) (x : Transport.Config (dims n d) k) :
    (compProj D d k B *ᵥ u) x = (∏ j ∈ Bᶜ, D.Ω (physPart (x j))) * goodRest D d k B u x := by
  simp only [mulVec, dotProduct, compProj_apply', goodRest, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- D8.24.2. `φ` does not depend on the good physical factors. -/
theorem goodRest_congr (k : ℕ) (B : Finset (Fin k)) (u : Transport.Config (dims n d) k → ℂ)
    {x x' : Transport.Config (dims n d) k} (hB : ∀ j ∈ B, x j = x' j)
    (haux : ∀ j, x j .C = x' j .C ∧ x j .R = x' j .R) :
    goodRest D d k B u x = goodRest D d k B u x' := by
  unfold goodRest
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : ∏ j ∈ B, (1 - physGround D) (physPart (x j)) (physPart (y j)) =
      ∏ j ∈ B, (1 - physGround D) (physPart (x' j)) (physPart (y j)) :=
    Finset.prod_congr rfl fun j hj => by rw [hB j hj]
  have h2 : (∀ j, x j .C = y j .C ∧ x j .R = y j .R) ↔
      ∀ j, x' j .C = y j .C ∧ x' j .R = y j .R := by
    simp only [(haux _).1, (haux _).2]
  rw [h1, if_congr h2 rfl rfl]

/-- An auxiliary-factor permutation leaves `Π_B` invariant. -/
theorem compProj_apply_copyPerm_aux (k : ℕ) (B : Finset (Fin k)) {Q : Finset (Site σ)}
    (hQ : ∀ v, Site.phys v ∉ Q) (s : Equiv.Perm (Fin k)) (x y : Transport.Config (dims n d) k) :
    compProj D d k B (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q s x)
        (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q s y) = compProj D d k B x y := by
  have hp : ∀ z : Transport.Config (dims n d) k, ∀ j,
      physPart (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q s z j) = physPart (z j) :=
    fun z j => funext fun v => by
      simp only [physPart]
      rw [Replicas.copyPerm_apply, if_neg (hQ v)]
  rw [compProj_apply, compProj_apply]
  simp only [hp]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [Replicas.copyPerm_apply]
  constructor
  · intro h j
    have hC := (h (s j)).1
    have hR := (h (s j)).2
    have hC' := (h j).1
    have hR' := (h j).2
    have hs : s⁻¹ (s j) = j := s.symm_apply_apply j
    rw [hs] at hC hR
    by_cases hc : Site.C ∈ Q <;> by_cases hr : Site.R ∈ Q <;> simp_all
  · intro h j
    by_cases hc : Site.C ∈ Q <;> by_cases hr : Site.R ∈ Q <;> simp_all

/-- A whole-copy permutation moves `Π_B` to `Π_{σ⁻¹ B}`. -/
theorem compProj_apply_copyPerm (k : ℕ) (B : Finset (Fin k)) (s : Equiv.Perm (Fin k))
    (x y : Transport.Config (dims n d) k) :
    compProj D d k B (TensorPower.copyPerm (SiteConfig (dims n d)) k s x)
        (TensorPower.copyPerm (SiteConfig (dims n d)) k s y) =
      compProj D d k (B.map s.symm.toEmbedding) x y := by
  rw [compProj_apply, compProj_apply]
  simp only [TensorPower.copyPerm_apply]
  congr 1
  · rw [← Equiv.prod_comp s]
    refine Finset.prod_congr rfl fun j _ => ?_
    have : (s j ∈ B ↔ j ∈ B.map s.symm.toEmbedding) := by
      simp
    have hs : s⁻¹ (s j) = j := s.symm_apply_apply j
    simp only [hs, compFactor, this]
  · refine if_congr ⟨fun h j => by simpa using h (s j), fun h j => h _⟩ rfl rfl

/-! ### `Π` and the auxiliary sector -/

variable (τ : ℝ) (k : ℕ)

theorem isHermitian_defectProj : (defectProj D d τ k).IsHermitian := by
  rw [IsHermitian, defectProj, conjTranspose_sum]
  exact Finset.sum_congr rfl fun B _ => isHermitian_compProj D d k B

theorem defectProj_mul_self : defectProj D d τ k * defectProj D d τ k = defectProj D d τ k := by
  simp only [defectProj, Finset.sum_mul, Finset.mul_sum, compProj_mul]
  refine Finset.sum_congr rfl fun B hB => ?_
  rw [Finset.sum_ite_eq' _ B, if_pos hB]

variable {k}

theorem commute_permOp_aux_compProj (B : Finset (Fin k)) {Q : Finset (Site σ)}
    (hQ : ∀ v, Site.phys v ∉ Q) (s : Equiv.Perm (Fin k)) :
    Commute (permOp (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q) s) (compProj D d k B) :=
  commute_permOp_of_apply_eq _ s fun x y => compProj_apply_copyPerm_aux D d k B hQ s x y

/-- D8.24.2. The physical `Π_B` commutes with the auxiliary label projectors. -/
theorem commute_labelProj_aux_compProj (B : Finset (Fin k)) {Q : Finset (Site σ)}
    (hQ : ∀ v, Site.phys v ∉ Q) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Commute (labelProj (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q) l)
      (compProj D d k B) :=
  commute_groupAlgebraRep_of_forall_commute _
    (fun s => commute_permOp_aux_compProj D d B hQ s) _

theorem commute_permOp_compProj (B : Finset (Fin k)) {s : Equiv.Perm (Fin k)}
    (hs : ∀ j, s j ∈ B ↔ j ∈ B) :
    Commute (permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s) (compProj D d k B) := by
  refine commute_permOp_of_apply_eq _ s fun x y => ?_
  rw [compProj_apply_copyPerm]
  congr 1
  ext j
  simp [hs]

theorem commute_permOp_defectProj (s : Equiv.Perm (Fin k)) :
    Commute (permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s) (defectProj D d τ k) := by
  refine commute_permOp_of_apply_eq _ s fun x y => ?_
  simp only [defectProj, Matrix.sum_apply, compProj_apply_copyPerm]
  refine Finset.sum_nbij' (fun B => B.map s.symm.toEmbedding) (fun B => B.map s.toEmbedding)
    ?_ ?_ ?_ ?_ fun _ _ => rfl
  · intro B hB
    simpa using hB
  · intro B hB
    simpa using hB
  · intro B _
    ext j
    simp
  · intro B _
    ext j
    simp

/-- `π^λ_Q` commutes with the permutations of whole copies. -/
theorem commute_labelProj_permOp_copyPerm (Q : Finset (Site σ))
    (l : IrrepLabel (Equiv.Perm (Fin k))) (s : Equiv.Perm (Fin k)) :
    Commute (labelProj (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q) l)
      (permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s) := by
  have h := commute_groupAlgebraRep_of_eq_mul
    (TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Q)
    (TensorPower.subsystemPerm k (fun f => Fin (dims n d f)) Qᶜ)
    (TensorPower.copyPerm (SiteConfig (dims n d)) k)
    (fun g => TensorPower.copyPerm_eq_mul_compl (ι := fun f => Fin (dims n d f)) Q g)
    (fun g h => TensorPower.commute_subsystemPerm_of_disjoint k _ disjoint_compl_right g h)
    (IrrepLabel.centralIdem_mem_center l) (MonoidAlgebra.single s 1)
  simpa [labelProj, groupAlgebraRep_single] using h

variable (k)

/-- D8.23. The factors `Π`, `π^λ_C`, `π^λ_R`, `Π_k` of the sector projection pairwise commute. -/
theorem commute_sector_factors (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Commute (defectProj D d τ k) (piC (n := n) d k l) ∧
      Commute (defectProj D d τ k) (piR (n := n) d k l) ∧
      Commute (defectProj D d τ k) (Transport.Pi (dims n d) k) ∧
      Commute (piC (n := n) d k l) (piR (n := n) d k l) ∧
      Commute (piC (n := n) d k l) (Transport.Pi (dims n d) k) ∧
      Commute (piR (n := n) d k l) (Transport.Pi (dims n d) k) := by
  have hC : ∀ v, Site.phys v ∉ ({Site.C} : Finset (Site σ)) := fun v => by simp
  have hR : ∀ v, Site.phys v ∉ ({Site.R} : Finset (Site σ)) := fun v => by simp
  refine ⟨(Commute.sum_left _ _ _ fun B _ => (commute_labelProj_aux_compProj D d B hC l).symm),
    (Commute.sum_left _ _ _ fun B _ => (commute_labelProj_aux_compProj D d B hR l).symm),
    (Transport.commute_Pi_of_forall fun s => commute_permOp_defectProj D d τ s).symm,
    Replicas.step_6_4_8 (fun f => Fin (dims n d f)) k (Or.inr (by simp)) l l,
    (Transport.commute_Pi_of_forall fun s =>
      (commute_labelProj_permOp_copyPerm d {Site.C} l s).symm).symm,
    (Transport.commute_Pi_of_forall fun s =>
      (commute_labelProj_permOp_copyPerm d {Site.R} l s).symm).symm⟩

/-- D8.23. `Π` on the sector is an orthogonal projection, below each of its factors. -/
theorem lowProj_spec (l : IrrepLabel (Equiv.Perm (Fin k))) :
    IsStarProjection (lowProj D d τ k l) ∧
      defectProj D d τ k * lowProj D d τ k l = lowProj D d τ k l ∧
      piC (n := n) d k l * lowProj D d τ k l = lowProj D d τ k l ∧
      piR (n := n) d k l * lowProj D d τ k l = lowProj D d τ k l ∧
      Transport.Pi (dims n d) k * lowProj D d τ k l = lowProj D d τ k l := by
  obtain ⟨h1C, h1R, h1P, hCR, hCP, hRP⟩ := commute_sector_factors D d τ k l
  set P1 := defectProj D d τ k
  set P2 := piC (n := n) d k l
  set P3 := piR (n := n) d k l
  set P4 := Transport.Pi (dims n d) k
  have e1 : P1 * P1 = P1 := defectProj_mul_self D d τ k
  have e2 : P2 * P2 = P2 := labelProj_mul_self _ _
  have e3 : P3 * P3 = P3 := labelProj_mul_self _ _
  have e4 : P4 * P4 = P4 := Transport.Pi_mul_Pi k
  have H1 : P1ᴴ = P1 := isHermitian_defectProj D d τ k
  have H2 : P2ᴴ = P2 := isHermitian_labelProj _ _
  have H3 : P3ᴴ = P3 := isHermitian_labelProj _ _
  have H4 : P4ᴴ = P4 := Transport.isHermitian_Pi k
  have hL : lowProj D d τ k l = P1 * (P2 * P3 * P4) := rfl
  have sp : ∀ {p q : Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ},
      IsStarProjection p → IsStarProjection q → Commute p q → IsStarProjection (p * q) :=
    fun {p q} hp hq h => ⟨by
      rw [IsIdempotentElem, mul_assoc, ← mul_assoc q, ← h.eq, mul_assoc, hq.isIdempotentElem.eq,
        ← mul_assoc, hp.isIdempotentElem.eq], by
      rw [IsSelfAdjoint, star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, h.eq]⟩
  have s1 : IsStarProjection P1 := ⟨e1, H1⟩
  have s2 : IsStarProjection P2 := ⟨e2, H2⟩
  have s3 : IsStarProjection P3 := ⟨e3, H3⟩
  have s4 : IsStarProjection P4 := ⟨e4, H4⟩
  rw [hL]
  refine ⟨sp s1 (sp (sp s2 s3 hCR) s4 (hCP.mul_left hRP)) ((h1C.mul_right h1R).mul_right h1P),
    by rw [← mul_assoc, e1], ?_, ?_, ?_⟩
  · rw [← mul_assoc, ← h1C.eq, mul_assoc, ← mul_assoc P2, ← mul_assoc P2, e2]
  · rw [← mul_assoc, ← h1R.eq, mul_assoc, ← mul_assoc P3, ← mul_assoc P3, ← hCR.eq,
      mul_assoc P2, e3]
  · rw [← mul_assoc, ← h1P.eq, mul_assoc, ← mul_assoc P4, ← (hCP.mul_left hRP).eq, mul_assoc, e4]

/-! ### D8.24 The split into good and bad copies -/

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem phys_mem_physReg (Q : Finset σ) (v : σ) : Site.phys v ∈ physReg Q ↔ v ∈ Q := by
  simp only [physReg, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    have h' : Site.phys a = Site.phys v := h
    cases h'
    exact ha
  · exact fun h => ⟨v, h, rfl⟩

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem C_not_mem_physReg (Q : Finset σ) : Site.C ∉ physReg Q := by
  simp [physReg]

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem R_not_mem_physReg (Q : Finset σ) : Site.R ∉ physReg Q := by
  simp [physReg]

omit [Fintype σ] [DecidableEq σ] in
/-- D8.24. The split of the copies into the good copies `Bᶜ` (first group) and the bad copies
`B` (second group). -/
noncomputable def split {k : ℕ} (B : Finset (Fin k)) : Fin Bᶜ.card ⊕ Fin B.card ≃ Fin k :=
  (Equiv.sumCongr (Bᶜ.equivFin.symm.trans (Equiv.subtypeEquivRight fun _ => Finset.mem_compl))
    B.equivFin.symm).trans ((Equiv.sumComm _ _).trans (Equiv.sumCompl (· ∈ B)))

omit [Fintype σ] [DecidableEq σ] in
theorem split_inl {k : ℕ} (B : Finset (Fin k)) (i : Fin Bᶜ.card) : split B (.inl i) ∉ B := by
  have := ((Bᶜ.equivFin.symm.trans (Equiv.subtypeEquivRight fun _ => Finset.mem_compl)) i).2
  simpa [split] using this

omit [Fintype σ] [DecidableEq σ] in
theorem split_inr {k : ℕ} (B : Finset (Fin k)) (j : Fin B.card) : split B (.inr j) ∈ B := by
  have := (B.equivFin.symm j).2
  simp [split]

omit [Fintype σ] [DecidableEq σ] in
theorem groupHom₁_split_of_mem {k : ℕ} {B : Finset (Fin k)} (a : Equiv.Perm (Fin Bᶜ.card))
    {j : Fin k} (hj : j ∈ B) : TensorPower.groupHom₁ (split B) a j = j := by
  obtain ⟨y, rfl⟩ := (split B).surjective j
  rcases y with i | i
  · exact absurd hj (split_inl B i)
  · exact TensorPower.groupHom₁_apply_inr _ a i

omit [Fintype σ] [DecidableEq σ] in
theorem groupHom₁_split_mem_iff {k : ℕ} (B : Finset (Fin k)) (a : Equiv.Perm (Fin Bᶜ.card))
    (j : Fin k) : TensorPower.groupHom₁ (split B) a j ∈ B ↔ j ∈ B := by
  obtain ⟨y, rfl⟩ := (split B).surjective j
  rcases y with i | i
  · rw [TensorPower.groupHom₁_apply_inl]
    exact iff_of_false (split_inl B _) (split_inl B i)
  · rw [TensorPower.groupHom₁_apply_inr]

omit [Fintype σ] [DecidableEq σ] in
theorem groupHom₂_split_mem_iff {k : ℕ} (B : Finset (Fin k)) (b : Equiv.Perm (Fin B.card))
    (j : Fin k) : TensorPower.groupHom₂ (split B) b j ∈ B ↔ j ∈ B := by
  obtain ⟨y, rfl⟩ := (split B).surjective j
  rcases y with i | i
  · rw [TensorPower.groupHom₂_apply_inl]
  · rw [TensorPower.groupHom₂_apply_inr]
    exact iff_of_true (split_inr B _) (split_inr B i)

/-- D8.24.2. A copy permutation preserving `B` fixes `u_B` when it fixes `u`. -/
theorem permOp_mulVec_compProj (B : Finset (Fin k)) {s : Equiv.Perm (Fin k)}
    (hs : ∀ j, s j ∈ B ↔ j ∈ B) {u : Transport.Config (dims n d) k → ℂ}
    (hu : permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s *ᵥ u = u) :
    permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s *ᵥ (compProj D d k B *ᵥ u) =
      compProj D d k B *ᵥ u := by
  rw [mulVec_mulVec, (commute_permOp_compProj D d B hs).eq, ← mulVec_mulVec, hu]

/-- D8.24.2. The good copies of `u_B` are in `Ω̃^{⊗k'}`: `u_B` is invariant under every
permutation of the physical factors of the good copies. -/
theorem physPerm_mulVec_compProj (B : Finset (Fin k)) {s : Equiv.Perm (Fin k)}
    (hs : ∀ j ∈ B, s j = j) (u : Transport.Config (dims n d) k → ℂ) :
    permOp (Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg Finset.univ)) s *ᵥ
        (compProj D d k B *ᵥ u) = compProj D d k B *ᵥ u := by
  rw [permOp_mulVec, ← map_inv]
  funext x
  simp only [Function.comp_apply]
  set y := Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg Finset.univ) s⁻¹ x
  have hy : ∀ j f, y j f = if f ∈ physReg Finset.univ then x (s j) f else x j f := fun j f => by
    change Replicas.copyPerm _ k _ s⁻¹ x j f = _
    rw [Replicas.copyPerm_apply, inv_inv]
  rw [compProj_mulVec_apply, compProj_mulVec_apply]
  congr 1
  · have hp : ∀ j, physPart (y j) = physPart (x (s j)) := fun j => funext fun v => by
      change y j (Site.phys v) = x (s j) (Site.phys v)
      rw [hy, if_pos (by simp)]
    simp only [hp]
    exact Equiv.Perm.prod_comp s Bᶜ (fun j => D.Ω (physPart (x j))) fun j hj => by
      simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
      exact fun hB => hj (hs j hB)
  · refine goodRest_congr D d k B u (fun j hj => funext fun f => ?_) fun j => ?_
    · rw [hy, hs j hj]
      split_ifs <;> rfl
    · simp [hy]

/-- D8.24. For `u ∈ ran Π` and `B ⊆ {1..k}`, `u_B` = component with exactly the copies in `B`
excited. `u = ∑_{|B| ≤ τk} u_B`, `∑_B ‖u_B‖² = 1`. For `r = |B|`, `k' = k - r`: `u_B` is
invariant under simultaneous permutations separately on the `k'` good and `r` bad copies;
factors as `Ω̃^{⊗k'}` on the good physical factors tensored with a vector on the rest; has the
two whole-copy auxiliary labels `λ_k`. Terms with `u_B = 0` omitted in normalized estimates. -/
theorem step_8_24 (l : IrrepLabel (Equiv.Perm (Fin k))) {u : Transport.Config (dims n d) k → ℂ}
    (hu : lowProj D d τ k l *ᵥ u = u) :
    ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k),
        compProj D d k B *ᵥ u = u ∧
    ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k),
        (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re = (star u ⬝ᵥ u).re ∧
    ∀ B : Finset (Fin k),
      (∀ a, permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k)
          (TensorPower.groupHom₁ (split B) a) *ᵥ (compProj D d k B *ᵥ u) =
            compProj D d k B *ᵥ u) ∧
      (∀ b, permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k)
          (TensorPower.groupHom₂ (split B) b) *ᵥ (compProj D d k B *ᵥ u) =
            compProj D d k B *ᵥ u) ∧
      (∀ x, (compProj D d k B *ᵥ u) x =
        (∏ j ∈ Bᶜ, D.Ω (physPart (x j))) * goodRest D d k B u x) ∧
      (∀ x x' : Transport.Config (dims n d) k, (∀ j ∈ B, x j = x' j) →
        (∀ j, x j .C = x' j .C ∧ x j .R = x' j .R) →
          goodRest D d k B u x = goodRest D d k B u x') ∧
      piC d k l *ᵥ (compProj D d k B *ᵥ u) = compProj D d k B *ᵥ u ∧
      piR d k l *ᵥ (compProj D d k B *ᵥ u) = compProj D d k B *ᵥ u := by
  obtain ⟨-, hDef, hC, hR, hS⟩ := lowProj_spec D d τ k l
  have hfix : ∀ M : Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ,
      M * lowProj D d τ k l = lowProj D d τ k l → M *ᵥ u = u := fun M hM => by
    rw [← hu, mulVec_mulVec, hM]
  have hsym : ∀ s, permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) s *ᵥ u = u := fun s => by
    rw [← hfix _ hS, mulVec_mulVec, permOp_mul_symProj]
  -- D8.24.1
  have h1 : ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k),
      compProj D d k B *ᵥ u = u := by
    rw [← sum_mulVec]
    exact hfix _ hDef
  refine ⟨h1, ?_, fun B => ⟨fun a => permOp_mulVec_compProj D d k B
    (groupHom₁_split_mem_iff B a) (hsym _), fun b => permOp_mulVec_compProj D d k B
    (groupHom₂_split_mem_iff B b) (hsym _), compProj_mulVec_apply D d k B u,
    fun x x' hB haux => goodRest_congr D d k B u hB haux, ?_, ?_⟩⟩
  · -- D8.24.1: `∑_B ‖u_B‖² = ‖u‖²`
    have hB : ∀ B, star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u) =
        star u ⬝ᵥ (compProj D d k B *ᵥ u) := fun B => by
      rw [star_mulVec, ← dotProduct_mulVec, (isHermitian_compProj D d k B).eq, mulVec_mulVec,
        compProj_mul, if_pos rfl]
    simp only [hB, ← Complex.re_sum, ← dotProduct_sum, h1]
  · -- D8.24.2: the auxiliary labels
    have hCB : ∀ v, Site.phys v ∉ ({Site.C} : Finset (Site σ)) := fun v => by simp
    have hc : Commute (piC (n := n) d k l) (compProj D d k B) :=
      commute_labelProj_aux_compProj D d B hCB l
    rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, hfix _ hC]
  · have hRB : ∀ v, Site.phys v ∉ ({Site.R} : Finset (Site σ)) := fun v => by simp
    have hc : Commute (piR (n := n) d k l) (compProj D d k B) :=
      commute_labelProj_aux_compProj D d B hRB l
    rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, hfix _ hR]

end Components

/-! ## D8.25–D8.27 Labels of the two groups of copies -/

section GroupLabels

variable {I : Type*} [DecidableEq I] [Fintype I] (ι : I → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {k : ℕ}

/-- D8.25 (`comparator:restriction-dimensions`). For any region `Q`, whole label and two
subgroup labels commute. On a compatible triple,
`F_Q^good + F_Q^bad ≤ F_Q^whole ≤ F_Q^good + F_Q^bad + log binom(k, r)`. -/
theorem step_8_25 {m r : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (Q : Finset I) :
    (∀ (α : IrrepLabel (Equiv.Perm (Fin m))) (β : IrrepLabel (Equiv.Perm (Fin r)))
      (l : IrrepLabel (Equiv.Perm (Fin k))),
      Commute (labelProj ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₁ e)) α)
          (Replicas.π ι k Q l) ∧
        Commute (labelProj ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₂ e)) β)
          (Replicas.π ι k Q l) ∧
        (labelProj ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₁ e)) α *
          labelProj ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₂ e)) β *
            Replicas.π ι k Q l ≠ 0 →
          Real.log α.dim + Real.log β.dim ≤ Real.log l.dim ∧
            Real.log l.dim ≤ Real.log α.dim + Real.log β.dim + Real.log (k.choose r))) ∧
    labelEntropy ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₁ e)) +
        labelEntropy ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₂ e)) ≤
      Replicas.F ι k Q ∧
    Replicas.F ι k Q ≤ labelEntropy ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₁ e)) +
        labelEntropy ((Replicas.copyPerm ι k Q).comp (TensorPower.groupHom₂ e)) +
      (Real.log (k.choose r) : ℂ) • 1 := by
  obtain ⟨hlo, hup⟩ := TensorPower.groupedCopies_labelEntropy_bounds e (Replicas.copyPerm ι k Q)
  refine ⟨fun α β l => ?_, hlo, hup⟩
  obtain ⟨hd, hc₁, hc₂⟩ := Replicas.lemma_6_1_4 ι k e Q α β l
  refine ⟨hc₁, hc₂, fun h => ?_⟩
  -- D8.25.1, D8.25.2
  obtain ⟨hd₁, hd₂⟩ := hd h
  have hk : r ≤ k := by have := Fintype.card_congr e; simp at this; omega
  have ha : (0 : ℝ) < α.dim := by exact_mod_cast α.dim_pos
  have hb : (0 : ℝ) < β.dim := by exact_mod_cast β.dim_pos
  have hl : (0 : ℝ) < l.dim := by exact_mod_cast l.dim_pos
  have hch : (0 : ℝ) < k.choose r := by exact_mod_cast Nat.choose_pos hk
  rw [← Real.log_mul ha.ne' hb.ne', ← Real.log_mul (mul_pos ha hb).ne' hch.ne']
  exact ⟨Real.log_le_log (mul_pos ha hb) (by exact_mod_cast hd₁),
    Real.log_le_log hl (by rw [mul_comm]; exact_mod_cast hd₂)⟩

omit [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
private theorem ne_zero_of_reindex_eq_kronecker {X Y Z : Type*} [DecidableEq Z] (e : X ≃ Y × Z)
    {A : Matrix X X ℂ} {B : Matrix Y Y ℂ} (h : reindex e e A = B ⊗ₖ (1 : Matrix Z Z ℂ))
    (hA : A ≠ 0) : B ≠ 0 := by
  rintro rfl
  rw [zero_kronecker] at h
  apply hA
  simpa using congrArg (reindex e e).symm h

/-- D8.27.2. A label of the second group of copies of a region `T` occurring at all has
`d_β ≤ (dim 𝓗_T)^r`. -/
theorem dim_le_pow_of_labelProj_groupHom₂ {m r : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (T : Finset I) {β : IrrepLabel (Equiv.Perm (Fin r))}
    (h : labelProj ((Replicas.copyPerm ι k T).comp (TensorPower.groupHom₂ e)) β ≠ 0) :
    β.dim ≤ Fintype.card (TensorPower.SubConfig ι T) ^ r := by
  rw [TensorPower.groupHom₂_eq] at h
  have h1 := ne_zero_of_reindex_eq_kronecker _
    (TensorPower.labelProj_groupHom₁_eq ι (TensorPower.swapSplit e) T β) h
  have h2 := ne_zero_of_reindex_eq_kronecker _ (TensorPower.labelProj_subsystemPerm_eq ι r T β) h1
  simpa using dim_le_card_of_labelProj_ne_zero _ h2

/-- D8.27.2. If `u` has the whole label `λ` on `T` and `π^α_{T,good} u ≠ 0`, then
`log d_λ ≤ log d_α + r log dim 𝓗_T + log binom(k, r)`. -/
theorem log_dim_le_of_good {m r : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (T : Finset I)
    {l : IrrepLabel (Equiv.Perm (Fin k))} {v : Replicas.Config ι k → ℂ}
    (hv : Replicas.π ι k T l *ᵥ v = v) {α : IrrepLabel (Equiv.Perm (Fin m))}
    (hα : labelProj ((Replicas.copyPerm ι k T).comp (TensorPower.groupHom₁ e)) α *ᵥ v ≠ 0) :
    Real.log l.dim ≤ Real.log α.dim + r * Real.log (Fintype.card (TensorPower.SubConfig ι T)) +
      Real.log (k.choose r) := by
  set Pα := labelProj ((Replicas.copyPerm ι k T).comp (TensorPower.groupHom₁ e)) α
  set Pβ := fun β => labelProj ((Replicas.copyPerm ι k T).comp (TensorPower.groupHom₂ e)) β
  obtain ⟨β, hβ⟩ : ∃ β, Pα * Pβ β * Replicas.π ι k T l ≠ 0 := by
    by_contra! h0
    apply hα
    have hsum : Pα * Replicas.π ι k T l = ∑ β, Pα * Pβ β * Replicas.π ι k T l := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_labelProj, mul_one]
    rw [← hv, mulVec_mulVec, hsum, Finset.sum_eq_zero fun β _ => h0 β, zero_mulVec]
  have hd := (Replicas.lemma_6_1_4 ι k e T α β l).1 hβ
  have hβd := dim_le_pow_of_labelProj_groupHom₂ ι e T (β := β) fun h => hβ (by
    simp only [Pβ, h, mul_zero, zero_mul])
  have hk : r ≤ k := by have := Fintype.card_congr e; simp at this; omega
  have ha : (0 : ℝ) < α.dim := by exact_mod_cast α.dim_pos
  have hb : (0 : ℝ) < β.dim := by exact_mod_cast β.dim_pos
  have hch : (0 : ℝ) < k.choose r := by exact_mod_cast Nat.choose_pos hk
  calc Real.log l.dim ≤ Real.log (k.choose r * (α.dim * β.dim) : ℕ) :=
        Real.log_le_log (by exact_mod_cast l.dim_pos) (by exact_mod_cast hd.2)
    _ = Real.log (k.choose r) + Real.log α.dim + Real.log β.dim := by
        push_cast
        rw [Real.log_mul hch.ne' (mul_pos ha hb).ne', Real.log_mul ha.ne' hb.ne', add_assoc]
    _ ≤ Real.log (k.choose r) + Real.log α.dim +
          Real.log ((Fintype.card (TensorPower.SubConfig ι T) : ℝ) ^ r) := by
        gcongr
        exact_mod_cast hβd
    _ = _ := by rw [Real.log_pow]; ring

/-- D8.27.3, D8.28.3. On a vector invariant under the simultaneous permutations of a group of
copies of `T₁ T₂ T₃` (pairwise disjoint), compatible labels have `d_{λ₃} ≤ d_{λ₁} d_{λ₂}`:
`F_{T₃} = F_{T₁T₂} ≤ F_{T₁} + F_{T₂}` on its support. -/
theorem dim_le_mul_of_mulVec_ne_zero {m : ℕ} (θ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin k))
    {T₁ T₂ T₃ : Finset I} (h12 : Disjoint T₁ T₂) (h3 : Disjoint T₃ (T₁ ∪ T₂))
    {v : Replicas.Config ι k → ℂ}
    (hv : v ∈ invariantSubspace ((Replicas.copyPerm ι k (T₃ ∪ (T₁ ∪ T₂))).comp θ))
    {a b c : IrrepLabel (Equiv.Perm (Fin m))}
    (h : (labelProj ((Replicas.copyPerm ι k T₁).comp θ) a *
      labelProj ((Replicas.copyPerm ι k T₂).comp θ) b *
        labelProj ((Replicas.copyPerm ι k T₃).comp θ) c) *ᵥ v ≠ 0) :
    c.dim ≤ a.dim * b.dim := by
  have hc : labelProj ((Replicas.copyPerm ι k T₃).comp θ) c *ᵥ v =
      labelProj ((Replicas.copyPerm ι k (T₁ ∪ T₂)).comp θ) c *ᵥ v :=
    groupAlgebraRep_mulVec_eq_of_eq_mul _ _ _
      (fun g => TensorPower.subsystemPerm_union k ι h3 (θ g))
      (IrrepLabel.coeff_inv_of_mem_center (IrrepLabel.centralIdem_mem_center c)) hv
  rw [← mulVec_mulVec, hc, mulVec_mulVec] at h
  refine dim_le_mul_dim_of_compatible (φQ := (Replicas.copyPerm ι k T₁).comp θ)
    (φE := (Replicas.copyPerm ι k T₂).comp θ) (φQE := (Replicas.copyPerm ι k (T₁ ∪ T₂)).comp θ)
    (fun g h => TensorPower.commute_subsystemPerm_of_disjoint k ι h12 (θ g) (θ h))
    (fun g => TensorPower.subsystemPerm_union k ι h12 (θ g)) fun h0 => h ?_
  rw [h0, zero_mulVec]

end GroupLabels

/-! ## The regions of a band -/

section Regions

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {K : ℕ} {St : Type v} {X : Finset σ}
  (Γ : Statuses σ K St X) (s : St) (g : Fin K)

omit [Fintype σ] [DecidableEq σ] in
theorem physReg_disjoint {A A' : Finset σ} : Disjoint (physReg A) (physReg A') ↔ Disjoint A A' :=
  Finset.disjoint_map _

omit [Fintype σ] in
theorem physReg_union (A A' : Finset σ) : physReg (A ∪ A') = physReg A ∪ physReg A' :=
  Finset.map_union _ _

theorem disjoint_XU_Y : Disjoint (X ∪ Γ.U s g) (Γ.Y s g) :=
  Finset.disjoint_union_left.mpr ⟨Γ.disjoint_XY s g, Γ.disjoint_UY s g⟩

theorem disjoint_XU_V : Disjoint (X ∪ Γ.U s g) (Γ.V s g) :=
  Finset.disjoint_union_left.mpr ⟨Γ.disjoint_XV s g, Γ.disjoint_UV s g⟩

/-- `P_{j,g} = XU_{j,g} ∪ C`. -/
theorem P_eq : Γ.P s g = physReg (X ∪ Γ.U s g) ∪ {Site.C} := by
  rw [Statuses.P, Finset.insert_eq, Finset.union_comm]

/-- `F_{j,g} = V_{j,g} ∪ R`. -/
theorem F_eq : Γ.F s g = physReg (Γ.V s g) ∪ {Site.R} := by
  rw [Statuses.F, Finset.insert_eq, Finset.union_comm]

theorem disjoint_P_Yr : Disjoint (Γ.P s g) (Γ.Yr s g) := by
  rw [P_eq, Statuses.Yr, Finset.disjoint_union_left, physReg_disjoint]
  exact ⟨disjoint_XU_Y Γ s g, by simp⟩

theorem disjoint_P_F : Disjoint (Γ.P s g) (Γ.F s g) := by
  rw [P_eq, F_eq, Finset.disjoint_union_left, Finset.disjoint_union_right,
    Finset.disjoint_union_right, physReg_disjoint]
  exact ⟨⟨disjoint_XU_V Γ s g, by simp⟩, by simp, by simp⟩

theorem disjoint_Yr_F : Disjoint (Γ.Yr s g) (Γ.F s g) := by
  rw [F_eq, Statuses.Yr, Finset.disjoint_union_right, physReg_disjoint]
  exact ⟨(Γ.disjoint_YV s g), by simp⟩

/-- `P_{j,g}, Y_{j,g}, F_{j,g}` partition `𝒱`. -/
theorem Yr_union_P_union_F : Γ.Yr s g ∪ (Γ.P s g ∪ Γ.F s g) = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  rintro (v | _ | _)
  · have hv := Γ.cover s g ▸ Finset.mem_univ v
    simp only [Finset.mem_union] at hv
    simp only [P_eq, F_eq, Statuses.Yr, Finset.mem_union, phys_mem_physReg,
      Finset.mem_singleton, reduceCtorEq, or_false]
    tauto
  · simp [P_eq]
  · simp [F_eq]

/-- The physical regions `XU, V, Y` cover the physical factors. -/
theorem Yr_union_XU_union_V :
    Γ.Yr s g ∪ (physReg (X ∪ Γ.U s g) ∪ physReg (Γ.V s g)) = physReg Finset.univ := by
  rw [Statuses.Yr, ← physReg_union, ← physReg_union, ← Γ.cover s g]
  congr 1
  ext v
  simp only [Finset.mem_union]
  tauto

end Regions

/-! ## D8.26, D8.27 on the system of §8 -/

section Site

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (d : ℕ)
  [NeZero d] {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)

/-- D8.26 (`comparator:whole-inverse`). With `G = F_P + F_F - F_Y` for the partition `P, Y, F`
(all its labels commute): `A_{j,g}^{-1} ≤ poly(k) binom(k, r)^{Ca} exp{-aG^good - aG^bad}`
(with `C = 1`; `a = 2t`). -/
theorem step_8_26 {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (B : Finset (Fin k)) (s : St) (g : Fin K),
      (Replicas.A (fun f => Fin (dims n d f)) (a / 2) k (Γ.P s g) (Γ.Yr s g) (Γ.F s g))⁻¹ ≤
        (((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ a) •
          NormedSpace.exp ((-a) •
            ((labelEntropy ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.P s g)).comp
                (TensorPower.groupHom₁ (split B))) +
              labelEntropy ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.F s g)).comp
                (TensorPower.groupHom₁ (split B))) -
              labelEntropy ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.Yr s g)).comp
                (TensorPower.groupHom₁ (split B)))) +
            (labelEntropy ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.P s g)).comp
                (TensorPower.groupHom₂ (split B))) +
              labelEntropy ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.F s g)).comp
                (TensorPower.groupHom₂ (split B))) -
              labelEntropy ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.Yr s g)).comp
                (TensorPower.groupHom₂ (split B)))))) := by
  obtain ⟨C, hC, h⟩ := TensorPower.exists_replicaMetric_inv_square_le_grouped_exp
    (fun f => Fin (dims n d f)) (half_pos ha)
  refine ⟨C, hC, fun k B s g => ?_⟩
  -- D8.26.1, D8.26.2
  have h' := h _ _ k (split B) (Γ.P s g) (Γ.Yr s g) (Γ.F s g) (disjoint_P_Yr Γ s g)
    (disjoint_P_F Γ s g) (disjoint_Yr_F Γ s g)
  rw [show 2 * (a / 2) = a by ring] at h'
  exact h'

omit [Fintype σ] [∀ v, NeZero (n v)] [NeZero d] in
theorem card_subConfig_C : Fintype.card (TensorPower.SubConfig (fun f => Fin (dims n d f))
    ({Site.C} : Finset (Site σ))) = d := by
  rw [Fintype.card_pi]
  have : (Finset.univ : Finset {f // f ∈ ({Site.C} : Finset (Site σ))}) = {⟨Site.C, by simp⟩} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun ⟨f, hf⟩ _ => by
      simp only [Finset.mem_singleton] at hf; subst hf; rfl⟩
  rw [this, Finset.prod_singleton, Fintype.card_fin]
  rfl

omit [Fintype σ] [∀ v, NeZero (n v)] [NeZero d] in
theorem card_subConfig_R : Fintype.card (TensorPower.SubConfig (fun f => Fin (dims n d f))
    ({Site.R} : Finset (Site σ))) = d := by
  rw [Fintype.card_pi]
  have : (Finset.univ : Finset {f // f ∈ ({Site.R} : Finset (Site σ))}) = {⟨Site.R, by simp⟩} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun ⟨f, hf⟩ _ => by
      simp only [Finset.mem_singleton] at hf; subst hf; rfl⟩
  rw [this, Finset.prod_singleton, Fintype.card_fin]
  rfl

omit [∀ v, NeZero (n v)] [NeZero d] in
/-- D8.27 (`comparator:good-auxiliary`). On `u_B`:
`F_C^good, F_R^good ≥ k S' - r log d_* - log binom(k, r) - o(k)`. Also `G^bad ≥ 0` on the measured
support.

Here with `log d_{λ_k}` for `k S' + o(k)`: every good label `α` of `C` (or `R`) occurring in
`u_B` has `log d_α ≥ log d_{λ_k} - r log d_* - log binom(k, r)`, and every bad triple of labels
`(p, f, y)` of `(P, F, Y)` occurring in `u_B` has `d_y ≤ d_p d_f`. -/
theorem step_8_27 (D : PhysData n) (τ : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k)))
    {u : Transport.Config (dims n d) k → ℂ} (hu : lowProj D d τ k l *ᵥ u = u)
    (B : Finset (Fin k)) :
    (∀ α, labelProj ((Replicas.copyPerm (fun f => Fin (dims n d f)) k {Site.C}).comp
        (TensorPower.groupHom₁ (split B))) α *ᵥ (compProj D d k B *ᵥ u) ≠ 0 →
      Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card) ≤ Real.log α.dim) ∧
    (∀ α, labelProj ((Replicas.copyPerm (fun f => Fin (dims n d f)) k {Site.R}).comp
        (TensorPower.groupHom₁ (split B))) α *ᵥ (compProj D d k B *ᵥ u) ≠ 0 →
      Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card) ≤ Real.log α.dim) ∧
    ∀ (s : St) (g : Fin K) (p f y : IrrepLabel (Equiv.Perm (Fin B.card))),
      (labelProj ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.P s g)).comp
          (TensorPower.groupHom₂ (split B))) p *
        labelProj ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.F s g)).comp
          (TensorPower.groupHom₂ (split B))) f *
        labelProj ((Replicas.copyPerm (fun f => Fin (dims n d f)) k (Γ.Yr s g)).comp
          (TensorPower.groupHom₂ (split B))) y) *ᵥ (compProj D d k B *ᵥ u) ≠ 0 →
      y.dim ≤ p.dim * f.dim := by
  obtain ⟨-, -, hB⟩ := step_8_24 D d τ k l hu
  obtain ⟨-, hbad, -, -, hC, hR⟩ := hB B
  refine ⟨fun α hα => ?_, fun α hα => ?_, fun s g p f y h => ?_⟩
  -- D8.27.1, D8.27.2
  · have := log_dim_le_of_good _ (split B) {Site.C} hC hα
    rw [card_subConfig_C] at this
    linarith
  · have := log_dim_le_of_good _ (split B) {Site.R} hR hα
    rw [card_subConfig_R] at this
    linarith
  -- D8.27.3
  · refine dim_le_mul_of_mulVec_ne_zero _ (TensorPower.groupHom₂ (split B)) (disjoint_P_F Γ s g)
      (Finset.disjoint_union_right.mpr ⟨(disjoint_P_Yr Γ s g).symm, disjoint_Yr_F Γ s g⟩)
      ?_ h
    rw [Yr_union_P_union_F]
    refine fun b => ?_
    have h1 : permOp ((Replicas.copyPerm (fun f => Fin (dims n d f)) k Finset.univ).comp
        (TensorPower.groupHom₂ (split B))) b =
          permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k)
            (TensorPower.groupHom₂ (split B) b) := by
      rw [Replicas.copyPerm, TensorPower.subsystemPerm_univ]
      rfl
    rw [h1]
    exact hbad b

end Site

end AreaLaw.Comparators
