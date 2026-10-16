/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/Circuit/SpectatorSiteExpectation.lean` (Apache 2.0).  Adaptations: the sites are a
region `T : Finset σ` with local family `loc`; TNLean `spectatorSiteExpectation q K` is
`OpenAI.spectatorCondExpect (h : K ⊆ T)`, defined blockwise from `OpenAI.condExpect`;
`supportedOperators q (Kᶜ)` is `IsSupportedOn (Finset.sdiff_subset : T \ K ⊆ T)` and the
on-site test unitaries at `y` are those with `IsSupportedOn (Finset.inter_subset_right :
{y} ∩ T ⊆ T)`, as in `OpenAI.siteOscillation`; sums over `Kᶜ` are sums over `T \ K`.  The
algebraic statements are over `RCLike 𝕜`; the two norm estimates are over `ℂ`, because the
contractivity of `OpenAI.condExpect` (`OpenAI.norm_condExpect_le`) is.  The contraction
`norm_spectatorCondExpect_le` uses the complementary Weyl twirl behind
`OpenAI.norm_condExpect_le`.  The Weyl-average formula `spectatorSiteExpectation_eq_average`
becomes `OpenAI.smul_spectatorCondExpect_eq_sum_conj`, stated for any family of single-site
one-designs, with TNLean's `outsideWeyl q K p` as `extendId` of the product operator
`Matrix.piProd` over `T \ S` and the normalization multiplied out; the private
`norm_weyl_average_le` and `norm_commutator_partialWeyl_kronecker_one_le` are
`OpenAI.norm_sub_le_of_card_smul_eq_sum_conj` and
`OpenAI.norm_commutator_piProd_kronecker_one_le` (OpenAI/SiteWeylAverage.lean).
`spectatorSiteExpectation_univ` is not used along the cone and is omitted.
-/
import OpenAI.SiteWeylAverage

/-!
# Conditional expectations with an untouched spectator

For an operator `B` on the sites `T` and a finite spectator `Aux`, the conditional expectation
`E_S ⊗ id` onto `S ⊆ T` acts on the physical indices of each spectator block of `B`
[OAI265, §10.1, the averaging argument before eq. (10.8)].  On simple tensors it averages the
physical factor only; its values commute with every physical operator supported on `T \ S`.
It is a contraction in operator norm, and its distance to `B` is bounded by the sum of the
on-site commutator bounds of `B` over `T \ S`, with no spectator dimension factor and no
Hermiticity assumption.

## Main definitions

* `OpenAI.spectatorCondExpect`: the blockwise conditional expectation.

## Main statements

* `OpenAI.spectatorCondExpect_kronecker`: `(E_S ⊗ id)(A ⊗ C) = E_S(A) ⊗ C`.
* `OpenAI.spectatorCondExpect_commute`: the values commute with the physical operators
  supported on `T \ S`.
* `OpenAI.smul_spectatorCondExpect_eq_sum_conj`: `E_S ⊗ id` is the average of the conjugations
  by products of single-site unitaries on `T \ S`, tensored with the spectator identity.
* `OpenAI.norm_spectatorCondExpect_le`, `OpenAI.norm_sub_spectatorCondExpect_le`.
-/

namespace OpenAI

open Arealaw Matrix
open scoped Kronecker Matrix.Norms.L2Operator

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {S T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux] {𝕜 : Type*} [RCLike 𝕜]

/-- The conditional expectation `E_S ⊗ id` onto `S ⊆ T` with an untouched finite spectator: the
normalized partial trace `E_S` applied to every spectator block
[OAI265, §10.1, before eq. (10.8)]. -/
noncomputable def spectatorCondExpect (h : S ⊆ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜 :=
  Matrix.of fun x y => condExpect h (Matrix.of fun u v => B (u, x.2) (v, y.2)) x.1 y.1

omit [Fintype Aux] [DecidableEq Aux] in
theorem spectatorCondExpect_apply (h : S ⊆ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) (x y : Reg loc T × Aux) :
    spectatorCondExpect h B x y =
      condExpect h (Matrix.of fun u v => B (u, x.2) (v, y.2)) x.1 y.1 :=
  rfl

omit [Fintype Aux] [DecidableEq Aux] in
/-- On a simple tensor only the physical factor is averaged
[OAI265, §10.1, before eq. (10.8)]. -/
theorem spectatorCondExpect_kronecker (h : S ⊆ T) (A : Matrix (Reg loc T) (Reg loc T) 𝕜)
    (C : Matrix Aux Aux 𝕜) :
    spectatorCondExpect h (A ⊗ₖ C) = condExpect h A ⊗ₖ C := by
  ext ⟨u, a⟩ ⟨v, b⟩
  have hblock : (Matrix.of fun u' v' => (A ⊗ₖ C) (u', a) (v', b)) = C a b • A := by
    ext u' v'
    simp [Matrix.kroneckerMap_apply, mul_comm]
  rw [spectatorCondExpect_apply, hblock, condExpect_smul]
  simp [Matrix.kroneckerMap_apply, mul_comm]

omit [Fintype Aux] [DecidableEq Aux] in
/-- An operator acting only on the spectator is fixed [OAI265, §10.1, before eq. (10.8)]. -/
@[simp] theorem spectatorCondExpect_one_kronecker (h : S ⊆ T) [Nonempty (Reg loc (T \ S))]
    (C : Matrix Aux Aux 𝕜) :
    spectatorCondExpect h ((1 : Matrix (Reg loc T) (Reg loc T) 𝕜) ⊗ₖ C) =
      (1 : Matrix (Reg loc T) (Reg loc T) 𝕜) ⊗ₖ C := by
  rw [spectatorCondExpect_kronecker, condExpect_one]

omit [∀ i, DecidableEq (loc i)] in
private theorem mul_kronecker_one_apply (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    (U : Matrix (Reg loc T) (Reg loc T) 𝕜) (u v : Reg loc T) (a b : Aux) :
    (B * (U ⊗ₖ (1 : Matrix Aux Aux 𝕜))) (u, a) (v, b) =
      ((Matrix.of fun u' v' => B (u', a) (v', b)) * U) u v := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

omit [∀ i, DecidableEq (loc i)] in
private theorem kronecker_one_mul_apply (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜)
    (U : Matrix (Reg loc T) (Reg loc T) 𝕜) (u v : Reg loc T) (a b : Aux) :
    ((U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * B) (u, a) (v, b) =
      (U * (Matrix.of fun u' v' => B (u', a) (v', b))) u v := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The values commute with every physical operator supported on `T \ S`, tensored with the
spectator identity [OAI265, §10.1, before eq. (10.8)]. -/
theorem spectatorCondExpect_commute (h : S ⊆ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) {U : Matrix (Reg loc T) (Reg loc T) 𝕜}
    (hU : IsSupportedOn (Finset.sdiff_subset : T \ S ⊆ T) U) :
    Commute (spectatorCondExpect h B) (U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) := by
  change spectatorCondExpect h B * (U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) =
    (U ⊗ₖ (1 : Matrix Aux Aux 𝕜)) * spectatorCondExpect h B
  ext ⟨u, a⟩ ⟨v, b⟩
  rw [mul_kronecker_one_apply, kronecker_one_mul_apply]
  have hc := ((isSupportedOn_condExpect h
    (Matrix.of fun u' v' => B (u', a) (v', b))).commute hU Finset.disjoint_sdiff).eq
  have hblock : (Matrix.of fun u' v' => spectatorCondExpect h B (u', a) (v', b)) =
      condExpect h (Matrix.of fun u' v' => B (u', a) (v', b)) := by
    ext u' v'
    rfl
  rw [hblock, hc]

/-- The product coordinates `(S × Aux) × (T \ S)` of `T × Aux`. -/
private def spectatorGlueEquiv (h : S ⊆ T) :
    (Reg loc S × Aux) × Reg loc (T \ S) ≃ Reg loc T × Aux :=
  ((Equiv.prodAssoc _ _ _).trans ((Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodComm _ _)).trans (Equiv.prodAssoc _ _ _).symm)).trans
    (Equiv.prodCongr (glueEquiv h) (Equiv.refl Aux))

/-- `E_S ⊗ id` is a contraction in operator norm for every finite spectator
[OAI265, §10.1, before eq. (10.8)]. -/
theorem norm_spectatorCondExpect_le (h : S ⊆ T) [Nonempty (Reg loc S)]
    [Nonempty (Reg loc (T \ S))] (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖spectatorCondExpect h B‖ ≤ ‖B‖ := by
  rcases isEmpty_or_nonempty Aux with hAux | hAux
  · rw [Subsingleton.elim B 0, Subsingleton.elim (spectatorCondExpect h 0) 0]
  let C := Reg loc (T \ S)
  have : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  have hroot := isPrimitiveRoot_regWeylRoot C
  let e : (Reg loc S × Aux) × C ≃ Reg loc T × Aux :=
    ((Equiv.prodAssoc _ _ _).trans ((Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodComm _ _)).trans (Equiv.prodAssoc _ _ _).symm)).trans
      (Equiv.prodCongr (glueEquiv h) (Equiv.refl Aux))
  have key : (spectatorCondExpect h B).submatrix e e =
      Matrix.complementaryWeylTwirl (regZModEquiv C) (regWeylRoot C) (B.submatrix e e) := by
    rw [Matrix.complementaryWeylTwirl_eq_smul_traceRight_kronecker_one _ hroot]
    ext ⟨⟨u, a⟩, z⟩ ⟨⟨v, b⟩, w⟩
    by_cases hzw : z = w
    · subst hzw
      simp [e, C, spectatorCondExpect_apply, condExpect, Matrix.kroneckerMap_apply,
        ptrace_eq_traceRight_submatrix_glueEquiv, Matrix.traceRight]
    · simp [e, C, spectatorCondExpect_apply, condExpect, Matrix.kroneckerMap_apply, hzw]
  rw [← l2_opNorm_submatrix (spectatorCondExpect h B) e e, key,
    ← l2_opNorm_submatrix B e e]
  exact Matrix.norm_complementaryWeylTwirl_le (regZModEquiv C) hroot _

omit [Fintype Aux] [DecidableEq Aux] in
/-- In product coordinates `((S × Aux) × (T \ S))`, `E_S ⊗ id` is the normalized partial trace over
`T \ S`, tensored with the identity. -/
private theorem spectatorCondExpect_submatrix_eq (h : S ⊆ T)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    (spectatorCondExpect h B).submatrix (spectatorGlueEquiv h) (spectatorGlueEquiv h) =
      ((Fintype.card (Reg loc (T \ S)) : 𝕜)⁻¹ •
        (B.submatrix (spectatorGlueEquiv h) (spectatorGlueEquiv h)).traceRight) ⊗ₖ
        (1 : Matrix (Reg loc (T \ S)) (Reg loc (T \ S)) 𝕜) := by
  ext ⟨⟨u, a⟩, z⟩ ⟨⟨v, b⟩, w⟩
  by_cases hzw : z = w
  · subst hzw
    simp [spectatorGlueEquiv, spectatorCondExpect_apply, condExpect, Matrix.kroneckerMap_apply,
      ptrace_eq_traceRight_submatrix_glueEquiv, Matrix.traceRight]
  · simp [spectatorGlueEquiv, spectatorCondExpect_apply, condExpect, Matrix.kroneckerMap_apply,
      hzw]

omit [∀ i, Fintype (loc i)] [Fintype Aux] in
private theorem extendId_sdiff_kronecker_one_submatrix (h : S ⊆ T)
    (Q : Matrix (Reg loc (T \ S)) (Reg loc (T \ S)) 𝕜) :
    (extendId (Finset.sdiff_subset : T \ S ⊆ T) Q ⊗ₖ (1 : Matrix Aux Aux 𝕜)).submatrix
        (spectatorGlueEquiv h) (spectatorGlueEquiv h) =
      (1 : Matrix (Reg loc S × Aux) (Reg loc S × Aux) 𝕜) ⊗ₖ Q := by
  ext ⟨⟨u, a⟩, z⟩ ⟨⟨v, b⟩, w⟩
  have hQ := congrArg (fun X => X (u, z) (v, w)) (extendId_sdiff_submatrix_glueEquiv h Q)
  simp only [submatrix_apply, glueEquiv_apply, kroneckerMap_apply] at hQ
  simp only [spectatorGlueEquiv, submatrix_apply, Equiv.trans_apply, Equiv.prodAssoc_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Equiv.prodAssoc_symm_apply, glueEquiv_apply, kroneckerMap_apply, hQ,
    one_apply, Prod.mk.injEq]
  by_cases hu : u = v <;> by_cases ha : a = b <;> simp [hu, ha]

/-- **Product Weyl average.**  If each family `W i` of operators on the site `i ∈ T \ S` is a
one-design with constant `κ i`, then `E_S ⊗ id` is, up to the factor `(∏ κ i) |T \ S|`, the sum of
the conjugations by the product operators `⊗_{i ∈ T \ S} W_i(p_i) ⊗ 1`
[OAI265, §10.1, before eq. (10.8)]. -/
theorem smul_spectatorCondExpect_eq_sum_conj (h : S ⊆ T) {G : ↥(T \ S) → Type*}
    [∀ i, Fintype (G i)] (W : ∀ i : ↥(T \ S), G i → Matrix (loc i) (loc i) 𝕜)
    (κ : ↥(T \ S) → 𝕜)
    (hW : ∀ (i : ↥(T \ S)) (M : Matrix (loc i) (loc i) 𝕜),
      ∑ g, W i g * M * (W i g)ᴴ = (κ i * M.trace) • 1)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜) :
    ((∏ i, κ i) * Fintype.card (Reg loc (T \ S))) • spectatorCondExpect h B =
      ∑ p : ∀ i, G i,
        (extendId (Finset.sdiff_subset : T \ S ⊆ T) (piProd fun i => W i (p i)) ⊗ₖ
            (1 : Matrix Aux Aux 𝕜)) * B *
          (extendId (Finset.sdiff_subset : T \ S ⊆ T) (piProd fun i => W i (p i)) ⊗ₖ
            (1 : Matrix Aux Aux 𝕜))ᴴ := by
  rcases isEmpty_or_nonempty (Reg loc (T \ S)) with hC | hC
  · have : IsEmpty (Reg loc T) := (glueEquiv h).symm.isEmpty
    ext ⟨w, _⟩
    exact isEmptyElim w
  set e := spectatorGlueEquiv (Aux := Aux) h
  suffices hs : (((∏ i, κ i) * Fintype.card (Reg loc (T \ S))) • spectatorCondExpect h B).submatrix
      e e = (∑ p : ∀ i, G i,
        (extendId (Finset.sdiff_subset : T \ S ⊆ T) (piProd fun i => W i (p i)) ⊗ₖ
            (1 : Matrix Aux Aux 𝕜)) * B *
          (extendId (Finset.sdiff_subset : T \ S ⊆ T) (piProd fun i => W i (p i)) ⊗ₖ
            (1 : Matrix Aux Aux 𝕜))ᴴ).submatrix e e by
    simpa [submatrix_submatrix] using congrArg (fun X => X.submatrix e.symm e.symm) hs
  have hsum : ∀ X : (∀ i, G i) → Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜,
      (∑ p, X p).submatrix e e = ∑ p, (X p).submatrix e e := fun X => by
    ext
    simp [Matrix.sum_apply]
  have hsmul : ∀ (c : 𝕜) (X : Matrix (Reg loc T × Aux) (Reg loc T × Aux) 𝕜),
      (c • X).submatrix e e = c • X.submatrix e e := fun _ _ => rfl
  rw [hsmul, spectatorCondExpect_submatrix_eq, hsum]
  rw [Finset.sum_congr rfl fun p _ => by
    rw [← submatrix_mul_equiv _ _ e e e, ← submatrix_mul_equiv _ _ e e e,
      ← conjTranspose_submatrix, extendId_sdiff_kronecker_one_submatrix]]
  rw [sum_one_kronecker_conj _ (∏ i, κ i) (sum_piProd_conj W κ hW), smul_kronecker, smul_smul,
    mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), mul_one]

/-- **Averaging one site at a time.**  If the commutator of `B` with every on-site unitary at
`y ∈ T \ S`, tensored with the spectator identity, has norm at most `ε y`, then
`‖B - (E_S ⊗ id)(B)‖ ≤ ∑_{y ∈ T \ S} ε y`, with no spectator dimension factor
[OAI265, §10.1, the averaging argument before eq. (10.8)]. -/
theorem norm_sub_spectatorCondExpect_le (h : S ⊆ T) [Nonempty (Reg loc S)]
    [Nonempty (Reg loc (T \ S))] (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ)
    (ε : σ → ℝ)
    (hε : ∀ y ∈ T \ S, ∀ U : Matrix (Reg loc T) (Reg loc T) ℂ,
      IsSupportedOn (Finset.inter_subset_right : {y} ∩ T ⊆ T) U →
      U ∈ unitary (Matrix (Reg loc T) (Reg loc T) ℂ) →
        ‖B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ ≤ ε y) :
    ‖B - spectatorCondExpect h B‖ ≤ ∑ y ∈ T \ S, ε y := by
  have hloc : ∀ i : ↥(T \ S), Nonempty (loc i) :=
    fun i => ⟨Classical.arbitrary (Reg loc (T \ S)) i⟩
  have hd : ∀ i : ↥(T \ S), NeZero (Fintype.card (loc i)) :=
    fun i => ⟨Fintype.card_ne_zero⟩
  let G : ↥(T \ S) → Type _ := fun i => ZMod (Fintype.card (loc i)) × ZMod (Fintype.card (loc i))
  let W : ∀ i : ↥(T \ S), G i → Matrix (loc i) (loc i) ℂ :=
    fun i g => reindexedWeyl (regZModEquiv (loc i)) (regWeylRoot (loc i)) g.1 g.2
  have hW : ∀ (i : ↥(T \ S)) (M : Matrix (loc i) (loc i) ℂ),
      ∑ g, W i g * M * (W i g)ᴴ = ((Fintype.card (loc i) : ℂ) * M.trace) • 1 :=
    fun i M => sum_reindexedWeyl_conj_eq _ (isPrimitiveRoot_regWeylRoot (loc i)) M
  have hWu : ∀ (i : ↥(T \ S)) (g : G i), W i g ∈ unitary (Matrix (loc i) (loc i) ℂ) :=
    fun i g => reindexedWeyl_mem_unitary _ (isPrimitiveRoot_regWeylRoot (loc i)) _ _
  have hform := smul_spectatorCondExpect_eq_sum_conj (Aux := Aux) h W _ hW B
  have hcard : (∏ i : ↥(T \ S), (Fintype.card (loc i) : ℂ)) * Fintype.card (Reg loc (T \ S)) =
      Fintype.card (∀ i, G i) := by
    rw [Fintype.card_pi, Fintype.card_pi]
    simp only [G, Fintype.card_prod, ZMod.card]
    push_cast
    rw [Finset.prod_mul_distrib]
  rw [hcard] at hform
  simp only [extendId_piProd] at hform
  let m : (∀ i, G i) → ∀ i : T, Matrix (loc i) (loc i) ℂ := fun p i =>
    if hi : (i : σ) ∈ T \ S then W ⟨i, hi⟩ (p ⟨i, hi⟩) else 1
  have hm : ∀ p (i : T), (i : σ) ∈ T \ S → m p i ∈ unitary (Matrix (loc i) (loc i) ℂ) :=
    fun p i hi => by
      simp only [m, dif_pos hi]
      exact hWu _ _
  have h1 : ∀ p (i : T), (i : σ) ∉ T \ S → m p i = 1 := fun p i hi => by
    simp only [m, dif_neg hi]
  have hU : ∀ p, piProd (m p) ⊗ₖ (1 : Matrix Aux Aux ℂ) ∈
      unitary (Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) := fun p =>
    kronecker_mem_unitary (piProd_mem_unitary fun i => by
      by_cases hi : (i : σ) ∈ T \ S
      · exact hm p i hi
      · rw [h1 p i hi]
        exact one_mem _) (one_mem _)
  refine norm_sub_le_of_card_smul_eq_sum_conj (U := fun p => piProd (m p) ⊗ₖ 1) hU
    (by simp only [star_eq_conjTranspose]; exact hform) fun p =>
      norm_commutator_piProd_kronecker_one_le B ε (T \ S) hε (m p) (hm p) (h1 p)

end OpenAI
