/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/Circuit/SiteExpectation.lean` (Apache 2.0), the product Weyl average behind
`siteExpectation_eq_average`, `partialWeyl` and `norm_commutator_partialWeyl_le`.  Adaptations:
the sites are a region `T : Finset σ` with local family `loc` instead of `ι → Fin q`; TNLean's
product Weyl operators `partialWeyl S p` are Physlib's `Matrix.piProd` of single-site operators,
and the averaging identity is proved for any family of single-site unitary one-designs
(`Matrix.sum_piProd_conj`), the Weyl operators `Matrix.reindexedWeyl` being one
(`Matrix.sum_reindexedWeyl_conj_eq`).
-/
import OpenAI.ConditionalExpectation

/-!
# Product averages of single-site unitaries

A family `W g` of matrices on `C` is a one-design with constant `κ` when
`∑_g W_g M W_gᴴ = κ tr(M) 1` for every `M`.  A product `⊗_i W_i` of one-designs on the factors
of `∀ i, d i` is a one-design with constant `∏_i κ_i` (`Matrix.sum_piProd_conj`), and on a
bipartite space `X × C` the average of the conjugations by `1 ⊗ W_g` is `κ` times the partial
trace over `C`, tensored with the identity (`Matrix.sum_one_kronecker_conj`).  The Weyl operators
`W_{a,b}` on a space of dimension `d` form a one-design with constant `d`.

On the regional side, a product operator on `T` that is a unitary at each site of a finite set
`F` and the identity elsewhere almost commutes with `B ⊗ 1`, up to the sum over `F` of the
on-site commutator bounds of `B` (`OpenAI.norm_commutator_piProd_kronecker_one_le`), the
telescoping estimate of [OAI265, §10.1, before eq. (10.8)].

## Main statements

* `Matrix.sum_piProd_conj`, `Matrix.sum_one_kronecker_conj`, `Matrix.sum_reindexedWeyl_conj_eq`.
* `OpenAI.norm_sub_le_of_card_smul_eq_sum_conj`: an average of unitary conjugations moves `B`
  by at most a uniform commutator bound.
* `OpenAI.norm_commutator_piProd_kronecker_one_le`.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

section PiProd

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → Type*} [∀ i, Fintype (d i)]
  {R : Type*} [CommRing R]

theorem piProd_mul (A B : ∀ i, Matrix (d i) (d i) R) :
    piProd A * piProd B = piProd fun i => A i * B i := by
  ext x y
  simp only [mul_apply, piProd, of_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ i, Fintype (d i)] in
theorem conjTranspose_piProd [StarRing R] (A : ∀ i, Matrix (d i) (d i) R) :
    (piProd A)ᴴ = piProd fun i => (A i)ᴴ := by
  ext x y
  simp only [conjTranspose_apply, piProd, of_apply, star_prod]

theorem piProd_mem_unitary [StarRing R] [∀ i, DecidableEq (d i)] {A : ∀ i, Matrix (d i) (d i) R}
    (hA : ∀ i, A i ∈ unitary (Matrix (d i) (d i) R)) :
    piProd A ∈ unitary (Matrix (∀ i, d i) (∀ i, d i) R) := by
  have h1 := OpenAI.piProd_one (d := d) (R := R)
  rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_piProd, piProd_mul, piProd_mul]
  refine ⟨?_, ?_⟩
  · rw [← h1]
    congr 1
    funext i
    exact (Unitary.mem_iff.1 (hA i)).1
  · rw [← h1]
    congr 1
    funext i
    exact (Unitary.mem_iff.1 (hA i)).2

omit [∀ i, Fintype (d i)] in
private theorem sum_conj_apply_eq_of_design {C G : Type*} [Fintype C] [DecidableEq C] [Fintype G]
    [StarRing R] (W : G → Matrix C C R) (κ : R)
    (hW : ∀ M : Matrix C C R, ∑ g, W g * M * (W g)ᴴ = (κ * M.trace) • 1) (a a' b b' : C) :
    ∑ g, W g a a' * star (W g b b') = if a = b ∧ a' = b' then κ else 0 := by
  have h := congrArg (fun N : Matrix C C R => N a b) (hW (single a' b' 1))
  simp only [sum_apply, mul_apply, single_apply, conjTranspose_apply, smul_apply, one_apply,
    mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ite_mul, zero_mul] at h
  rw [h]
  by_cases h' : a' = b'
  · subst h'
    by_cases hab : a = b <;> simp [hab]
  · rw [trace_single_eq_of_ne _ _ _ h']
    simp [h']

/-- **Product of one-designs.**  If each family `W i` is a one-design with constant `κ i`, the
product operators `⊗_i W_i(p_i)` form a one-design with constant `∏_i κ_i`. -/
theorem sum_piProd_conj [StarRing R] [∀ i, DecidableEq (d i)] {G : ι → Type*}
    [∀ i, Fintype (G i)] (W : ∀ i, G i → Matrix (d i) (d i) R) (κ : ι → R)
    (hW : ∀ i (M : Matrix (d i) (d i) R), ∑ g, W i g * M * (W i g)ᴴ = (κ i * M.trace) • 1)
    (M : Matrix (∀ i, d i) (∀ i, d i) R) :
    ∑ p : ∀ i, G i, piProd (fun i => W i (p i)) * M * (piProd fun i => W i (p i))ᴴ =
      ((∏ i, κ i) * M.trace) • 1 := by
  have hterm : ∀ (p : ∀ i, G i) (u v : ∀ i, d i),
      (piProd (fun i => W i (p i)) * M * (piProd fun i => W i (p i))ᴴ) u v =
        ∑ u', ∑ v', M u' v' * ∏ i, (W i (p i) (u i) (u' i) * star (W i (p i) (v i) (v' i))) := by
    intro p u v
    simp only [mul_apply, piProd, of_apply, conjTranspose_apply, star_prod, Finset.sum_mul,
      Finset.prod_mul_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun v' _ => by ring
  ext u v
  rw [sum_apply, Finset.sum_congr rfl fun p _ => hterm p u v, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (∀ i, G i))), ← Finset.mul_sum]
  have hprod : ∀ u' v' : ∀ i, d i,
      ∑ p : ∀ i, G i, ∏ i, (W i (p i) (u i) (u' i) * star (W i (p i) (v i) (v' i))) =
        if u = v ∧ u' = v' then ∏ i, κ i else 0 := by
    intro u' v'
    rw [← Fintype.prod_sum (fun i g => W i g (u i) (u' i) * star (W i g (v i) (v' i)))]
    simp_rw [sum_conj_apply_eq_of_design (W _) (κ _) (hW _)]
    rw [Finset.prod_ite_zero]
    congr 1
    simp [funext_iff, forall_and]
  rw [Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun v' _ => by rw [hprod u' v']]
  by_cases huv : u = v
  · subst huv
    simp [trace, Finset.mul_sum, mul_comm]
  · simp [huv]

end PiProd

section Kronecker

variable {R : Type*} [CommRing R] [StarRing R] {X C : Type*} [Fintype X] [DecidableEq X]
  [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
private theorem kronecker_one_conj_apply (W : Matrix C C R) (M : Matrix (X × C) (X × C) R)
    (s₁ s₂ : X) (c₁ c₂ : C) :
    ((1 : Matrix X X R) ⊗ₖ W * M * ((1 : Matrix X X R) ⊗ₖ W)ᴴ) (s₁, c₁) (s₂, c₂) =
      (W * M.submatrix (fun c => (s₁, c)) (fun c => (s₂, c)) * Wᴴ) c₁ c₂ := by
  rw [conjTranspose_kronecker, conjTranspose_one]
  simp only [mul_apply, submatrix_apply, Fintype.sum_prod_type, kronecker_apply, one_apply]
  rw [Finset.sum_eq_single s₂]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [if_pos rfl, one_mul]
    congr 1
    rw [Finset.sum_eq_single s₁]
    · exact Finset.sum_congr rfl fun c' _ => by rw [if_pos rfl, one_mul]
    · intro s' _ hs'
      simp [Ne.symm hs']
    · intro h
      exact absurd (Finset.mem_univ s₁) h
  · intro s' _ hs'
    simp [hs']
  · intro h
    exact absurd (Finset.mem_univ s₂) h

/-- Conjugation by `1 ⊗ W_g`, averaged over a one-design with constant `κ`, is `κ` times the
partial trace over the second factor, tensored with the identity. -/
theorem sum_one_kronecker_conj {G : Type*} [Fintype G] (W : G → Matrix C C R) (κ : R)
    (hW : ∀ M : Matrix C C R, ∑ g, W g * M * (W g)ᴴ = (κ * M.trace) • 1)
    (M : Matrix (X × C) (X × C) R) :
    ∑ g, (1 : Matrix X X R) ⊗ₖ W g * M * ((1 : Matrix X X R) ⊗ₖ W g)ᴴ =
      κ • (M.traceRight ⊗ₖ (1 : Matrix C C R)) := by
  ext ⟨s₁, c₁⟩ ⟨s₂, c₂⟩
  have h := congrArg (fun N : Matrix C C R => N c₁ c₂)
    (hW (M.submatrix (fun c => (s₁, c)) (fun c => (s₂, c))))
  simp only [sum_apply] at h
  simp only [sum_apply, kronecker_one_conj_apply, h, smul_apply, kronecker_apply, smul_eq_mul]
  rw [mul_assoc]
  rfl

end Kronecker

section Weyl

variable {C : Type*} [Fintype C] [DecidableEq C] {dC : ℕ} [NeZero dC]

/-- The Weyl operators on a space of dimension `d` form a one-design with constant `d`. -/
theorem sum_reindexedWeyl_conj_eq (e : C ≃ ZMod dC) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    (M : Matrix C C ℂ) :
    ∑ g : ZMod dC × ZMod dC, reindexedWeyl e ζ g.1 g.2 * M * (reindexedWeyl e ζ g.1 g.2)ᴴ =
      ((dC : ℂ) * M.trace) • 1 := by
  have h : ((dC : ℂ) ^ 2)⁻¹ • ∑ a : ZMod dC, ∑ b : ZMod dC,
      reindexedWeyl e ζ a b * M * (reindexedWeyl e ζ a b)ᴴ =
        (M.trace / dC) • (1 : Matrix C C ℂ) := by
    ext i j
    have hentry := congrArg (fun N : Matrix (ZMod dC) (ZMod dC) ℂ => N (e i) (e j))
      (sum_weyl_conj hζ (M.submatrix e.symm e.symm))
    simp only [smul_apply, sum_apply] at hentry ⊢
    have hconj : ∀ a b : ZMod dC,
        (reindexedWeyl e ζ a b * M * (reindexedWeyl e ζ a b)ᴴ) i j =
          (weyl ζ a b * M.submatrix e.symm e.symm * (weyl ζ a b)ᴴ) (e i) (e j) := by
      intro a b
      calc
        _ = ((weyl ζ a b).submatrix e e * (M.submatrix e.symm e.symm).submatrix e e *
            (weyl ζ a b)ᴴ.submatrix e e) i j := by
          simp only [reindexedWeyl, reindex_apply, Equiv.symm_symm, conjTranspose_submatrix]
          rw [submatrix_submatrix, e.symm_comp_self, submatrix_id_id]
        _ = ((weyl ζ a b * M.submatrix e.symm e.symm * (weyl ζ a b)ᴴ).submatrix e e) i j := by
          rw [submatrix_mul_equiv, submatrix_mul_equiv]
        _ = _ := rfl
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hconj a b, hentry,
      trace_submatrix _ e.symm]
    simp only [one_apply, e.injective.eq_iff]
  have hd : (dC : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne dC
  rw [Fintype.sum_prod_type]
  calc
    _ = ((dC : ℂ) ^ 2) • (((dC : ℂ) ^ 2)⁻¹ • ∑ a : ZMod dC, ∑ b : ZMod dC,
        reindexedWeyl e ζ a b * M * (reindexedWeyl e ζ a b)ᴴ) := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hd), one_smul]
    _ = _ := by
      rw [h, smul_smul]
      congr 1
      field_simp

end Weyl

end Matrix

namespace OpenAI

open Arealaw Matrix

/-- An average of unitary conjugations moves `B` by at most a uniform bound on the commutators of
`B` with the averaging unitaries. -/
theorem norm_sub_le_of_card_smul_eq_sum_conj {A : Type*} [NormedRing A] [StarRing A]
    [CStarRing A] [NormedAlgebra ℂ A] {P : Type*} [Fintype P] [Nonempty P] {B E : A}
    {U : P → A} (hU : ∀ p, U p ∈ unitary A)
    (hE : (Fintype.card P : ℂ) • E = ∑ p, U p * B * star (U p)) {r : ℝ}
    (hr : ∀ p, ‖B * U p - U p * B‖ ≤ r) : ‖B - E‖ ≤ r := by
  have hN : (0 : ℝ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ p, (B * U p - U p * B) * star (U p) = B - U p * B * star (U p) := fun p => by
    rw [sub_mul, mul_assoc B, Unitary.mul_star_self_of_mem (hU p), mul_one]
  have key : (Fintype.card P : ℂ) • (B - E) = ∑ p, (B * U p - U p * B) * star (U p) := by
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← hE, Finset.sum_const, Finset.card_univ, smul_sub,
      Nat.cast_smul_eq_nsmul]
  have hle : ‖∑ p, (B * U p - U p * B) * star (U p)‖ ≤ Fintype.card P * r := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _p : P, r := Finset.sum_le_sum fun p _ => by
        rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (hU p))]
        exact hr p
      _ = _ := by simp
  rw [← key, norm_smul, Complex.norm_natCast] at hle
  exact le_of_mul_le_mul_left hle hN

section Sites

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {T : Finset σ}

omit [∀ i, Fintype (loc i)] in
/-- A product operator that is the identity off the site `y` is supported on `{y} ∩ T`. -/
theorem isSupportedOn_piProd_ite_eq {𝕜 : Type*} [RCLike 𝕜] (y : σ)
    (m : ∀ i : T, Matrix (loc i) (loc i) 𝕜) :
    IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T)
      (piProd fun i : T => if (i : σ) = y then m i else 1) := by
  refine ⟨piProd fun j : ↥({y} ∩ T) => m ⟨j.1, (Finset.mem_inter.1 j.2).2⟩, ?_⟩
  rw [extendId_piProd]
  congr 1
  funext i
  by_cases hi : (i : σ) = y
  · rw [if_pos hi, dif_pos (Finset.mem_inter.2 ⟨by simp [hi], i.2⟩)]
  · rw [if_neg hi, dif_neg (by simp [hi])]

variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- **Telescoping over sites.**  A product operator on `T` that is a unitary at each site of `F`
and the identity elsewhere, tensored with the spectator identity, has commutator with `B` at most
the sum over `F` of the on-site commutator bounds of `B` [OAI265, §10.1, before eq. (10.8)]. -/
theorem norm_commutator_piProd_kronecker_one_le
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) (ε : σ → ℝ) (F : Finset σ)
    (hε : ∀ y ∈ F, ∀ U : Matrix (Reg loc T) (Reg loc T) ℂ,
      IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U →
      U ∈ unitary (Matrix (Reg loc T) (Reg loc T) ℂ) →
        ‖B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ ≤ ε y)
    (m : ∀ i : T, Matrix (loc i) (loc i) ℂ)
    (hm : ∀ i : T, (i : σ) ∈ F → m i ∈ unitary (Matrix (loc i) (loc i) ℂ))
    (h1 : ∀ i : T, (i : σ) ∉ F → m i = 1) :
    ‖B * (piProd m ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (piProd m ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ ≤
      ∑ y ∈ F, ε y := by
  induction F using Finset.induction_on generalizing m with
  | empty =>
    have hm1 : m = fun i => 1 := funext fun i => h1 i (Finset.notMem_empty _)
    subst hm1
    simp
  | insert y F hy ih =>
    let m₁ : ∀ i : T, Matrix (loc i) (loc i) ℂ := fun i => if (i : σ) = y then m i else 1
    let m₂ : ∀ i : T, Matrix (loc i) (loc i) ℂ := fun i => if (i : σ) = y then 1 else m i
    have hsplit : piProd m ⊗ₖ (1 : Matrix Aux Aux ℂ) =
        (piProd m₁ ⊗ₖ (1 : Matrix Aux Aux ℂ)) * (piProd m₂ ⊗ₖ (1 : Matrix Aux Aux ℂ)) := by
      rw [← mul_kronecker_mul, one_mul, piProd_mul]
      congr 2
      funext i
      by_cases hi : (i : σ) = y
      · simp [m₁, m₂, hi]
      · simp [m₁, m₂, hi]
    have hu₁ : piProd m₁ ∈ unitary (Matrix (Reg loc T) (Reg loc T) ℂ) :=
      piProd_mem_unitary fun i => by
        by_cases hi : (i : σ) = y
        · simpa [m₁, hi] using hm i (by simp [hi])
        · simp [m₁, hi]
    have hu₂ : piProd m₂ ∈ unitary (Matrix (Reg loc T) (Reg loc T) ℂ) :=
      piProd_mem_unitary fun i => by
        by_cases hi : (i : σ) = y
        · simp [m₂, hi]
        · by_cases hiF : (i : σ) ∈ F
          · simpa [m₂, hi] using hm i (by simp [hiF])
          · simp [m₂, hi, h1 i (by simp [hi, hiF])]
    have hk₁ := kronecker_mem_unitary hu₁ (one_mem (unitary (Matrix Aux Aux ℂ)))
    have hk₂ := kronecker_mem_unitary hu₂ (one_mem (unitary (Matrix Aux Aux ℂ)))
    set U := piProd m₁ ⊗ₖ (1 : Matrix Aux Aux ℂ)
    set V := piProd m₂ ⊗ₖ (1 : Matrix Aux Aux ℂ)
    have hcomm : B * (U * V) - U * V * B = (B * U - U * B) * V + U * (B * V - V * B) := by
      noncomm_ring
    rw [hsplit, hcomm, Finset.sum_insert hy]
    refine (norm_add_le _ _).trans ?_
    rw [CStarRing.norm_mul_mem_unitary _ hk₂, CStarRing.norm_mem_unitary_mul _ hk₁]
    refine add_le_add (hε y (Finset.mem_insert_self y F) _ (isSupportedOn_piProd_ite_eq y m) hu₁)
      (ih (fun z hz => hε z (Finset.mem_insert_of_mem hz)) m₂ (fun i hi => ?_) fun i hi => ?_)
    · by_cases hiy : (i : σ) = y
      · simp [m₂, hiy]
      · simpa [m₂, hiy] using hm i (Finset.mem_insert_of_mem hi)
    · by_cases hiy : (i : σ) = y
      · simp [m₂, hiy]
      · simpa [m₂, hiy] using h1 i (by simp [hiy, hi])

end Sites

end OpenAI
