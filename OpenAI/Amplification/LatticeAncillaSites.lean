/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/LatticeAncillaSites.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw` renamed to `OpenAI`.  Adaptations:
* Encodings as in `OpenAI.Amplification.LatticeAncillaTransport`: TNLean's `Site Λ` is
  `↥(Λ : Set (ℤ × ℤ))`, `Configuration Λ q` is `Reg (Qudits q) Λ`, `StateSpace Λ q` is
  `EuclideanSpace ℂ (Reg (Qudits q) Λ)`.
* Support, following `OpenAI.Amplification.SupportedPolarCorrection`.  For a physical operator
  `P` and a cut `S : Finset (Site Λ)`, TNLean's `P ∈ supportedOperators q (S : Set (Site Λ))` is
  `OpenAI.IsSupportedOn (map_embeddingSubtype_subset S) P`; for an operator `U` on the enlarged
  sites and `S : Finset (AncillaSites Λ X)`, it is
  `OpenAI.IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv)`.
  TNLean's `kronecker_one_submatrix_ancillaSplit` and `one_kronecker_submatrix_ancillaSplit`,
  which identify the two factors with `embedOp` along `Sum.inl` and `Sum.inr ∘ Sum.inl`, are
  not ported: the support of `P ⊗ (b ⊗ 1)` is read off its matrix entries through the added
  `OpenAI.isSupportedOn_submatrix_univEquiv_of_eq_ite`.  Renamed:
  `kronecker_submatrix_ancillaSplit_mem_supportedOperators` and
  `kronecker_one_submatrix_ancillaSplit_mem_supportedOperators` are
  `OpenAI.isSupportedOn_kronecker_submatrix_ancillaSplit` and
  `OpenAI.isSupportedOn_kronecker_one_submatrix_ancillaSplit`, stated over `RCLike 𝕜`.
  Added: `OpenAI.IsSupportedOn.subtype_map`, from support on a region of `ℤ × ℤ` inside `Λ` to
  support on the corresponding cut of the sites.
-/
import OpenAI.Amplification.LatticeAncillaTransport
import OpenAI.Amplification.AncillaSiteEntropy
import OpenAI.Amplification.SupportedPolarCorrection

/-!
# The physical sites enlarged by two copies of the target

The final entropy comparison of the amplification proof treats the two ancillary copies
`s', e'` of the target `X` as additional sites, each copy carrying the local dimension `q`.
This module sets up the enlarged site set `Λ ⊔ (X ⊔ X)`, whose configurations are pairs of a
physical configuration and two configurations of `X`, and identifies there:

* physical operators, operators on `s'`, and the supports of the transported restoring
  operator `R₀`;
* the restored vector `η = Ω ⊗ χ`, in which the copy `e'` has no mutual information with
  any physical region;
* the copied vector `φ`, which is `Ω` with the target relabelled as `e'`, tensored with
  blank vectors on `X` and `s'`; its mutual information between a part of `e'` and a
  physical region disjoint from `X` equals that of `Ω` between the corresponding part of
  `X` and the same region.

## Main definitions

* `OpenAI.AncillaSites`, `OpenAI.ancillaSplit`, `OpenAI.ancillaCopyRegion`.

## Main statements

* `OpenAI.isSupportedOn_kronecker_submatrix_ancillaSplit`.
* `OpenAI.mutualInformation_ancillaProduct_copy_eq_zero`.
* `OpenAI.mutualInformation_ancillaCopy_eq`.

## Implementation notes

Operators on the enlarged sites act on the finite-product space of `AncillaSites Λ X`, and
their support is that of `OpenAI.Amplification.SupportedPolarCorrection`: the support predicate
of regions, read on the whole site set through `Arealaw.univEquiv`.  Physical supports are
stated on the region of `ℤ × ℤ` of a cut, as the local-products lemma states them;
`OpenAI.IsSupportedOn.subtype_map` passes from a region `S ⊆ Λ` to the cut it defines.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 330–347
  and 547–556: the copies `s', e'` of the Hilbert space on `X`, the swapped and restored
  vectors, and the comparison of `I(e' : J)` with `I_Ω(X : J)`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix Arealaw
open scoped Kronecker

namespace OpenAI

section Support

variable {V : Type*} [Fintype V] [DecidableEq V] {β : V → Type*} [∀ v, DecidableEq (β v)]
  {𝕜 : Type*} [RCLike 𝕜]

/-- **Support from the matrix entries.** An operator on the finite-product space whose entry
between `x` and `y` vanishes unless `x, y` agree off `S`, and is otherwise given by a matrix on
the configurations of `S`, acts on `S`. -/
theorem isSupportedOn_submatrix_univEquiv_of_eq_ite (S : Finset V)
    (U : Matrix ((v : V) → β v) ((v : V) → β v) 𝕜)
    (K : Matrix (FiniteProduct.Configuration β S) (FiniteProduct.Configuration β S) 𝕜)
    (hU : ∀ x y, U x y = if ∀ v ∉ S, x v = y v then K (fun v => x v) (fun v => y v) else 0) :
    IsSupportedOn (Finset.subset_univ S) (U.submatrix univEquiv univEquiv) := by
  refine (isSupportedOn_submatrix_univEquiv_iff S U).2 ⟨K, ?_⟩
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [submatrix_apply, hU, kroneckerMap_apply, one_apply]
  have hfst (a : FiniteProduct.Configuration β S) (b : FiniteProduct.Configuration β Sᶜ) :
      (fun v : S => (FiniteProduct.splitEquiv β S).symm (a, b) v) = a :=
    funext fun v => FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ v.2
  have hiff : (∀ v ∉ S, (FiniteProduct.splitEquiv β S).symm (a, b) v =
      (FiniteProduct.splitEquiv β S).symm (a', b') v) ↔ b = b' := by
    constructor
    · intro h
      funext v
      have hv : (v : V) ∉ S := Finset.mem_compl.1 v.2
      have := h v hv
      rwa [FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv,
        FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv] at this
    · rintro rfl v hv
      rw [FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv,
        FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv]
  rw [hfst, hfst]
  by_cases hb : b = b'
  · rw [if_pos (hiff.2 hb), if_pos hb, mul_one]
  · rw [if_neg (hiff.not.2 hb), if_neg hb, mul_zero]

end Support

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- **From a region inside `Λ` to a cut of the sites.** An operator acting on a region
`S ⊆ Λ` acts on the image in `ℤ × ℤ` of the cut of the sites of `Λ` lying in `S`. -/
theorem IsSupportedOn.subtype_map {𝕜 : Type*} [RCLike 𝕜] {S : Finset (ℤ × ℤ)} {hS : S ⊆ Λ}
    {L : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜} (hL : IsSupportedOn hS L) :
    IsSupportedOn (map_embeddingSubtype_subset (T := Λ)
      (S.subtype (· ∈ (Λ : Set (ℤ × ℤ))))) L :=
  hL.mono (fun x hx => Finset.mem_map.2 ⟨⟨x, hS hx⟩, Finset.mem_subtype.2 hx, rfl⟩) _

/-- The physical sites of `Λ` together with two copies `s'` and `e'` of the target `X`.
Source: `09-amplification.tex`, lines 330–331. -/
abbrev AncillaSites (Λ : Finset (ℤ × ℤ)) (X : Finset ↥(Λ : Set (ℤ × ℤ))) :=
  ↥(Λ : Set (ℤ × ℤ)) ⊕ (↥X ⊕ ↥X)

/-- Shortcut instance, which keeps instance search on regions of the enlarged sites short. -/
instance (X : Finset ↥(Λ : Set (ℤ × ℤ))) : DecidableEq (AncillaSites Λ X) := inferInstance

/-- Shortcut instance, which keeps instance search on regions of the enlarged sites short. -/
instance (X : Finset ↥(Λ : Set (ℤ × ℤ))) : Fintype (AncillaSites Λ X) := inferInstance

/-- The configurations of the enlarged sites as a physical configuration together with the
configurations of `s'` and of `e'`. -/
def ancillaSplit (q : ℕ) (X : Finset ↥(Λ : Set (ℤ × ℤ))) :
    (AncillaSites Λ X → Fin q) ≃
      Reg (Qudits q) Λ × (RegionalConfiguration q X × RegionalConfiguration q X) :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))

theorem ancillaSplit_apply (X : Finset ↥(Λ : Set (ℤ × ℤ))) (c : AncillaSites Λ X → Fin q) :
    ancillaSplit q X c = (c ∘ Sum.inl, (c ∘ Sum.inr ∘ Sum.inl, c ∘ Sum.inr ∘ Sum.inr)) :=
  rfl

/-- The copy `e'` of a part `X'` of the target, as a region of the enlarged sites. -/
def ancillaCopyRegion {X : Finset ↥(Λ : Set (ℤ × ℤ))} (X' : Finset ↥X) :
    Finset (AncillaSites Λ X) :=
  (∅ : Finset ↥(Λ : Set (ℤ × ℤ))).disjSum ((∅ : Finset ↥X).disjSum X')

/-- A physical region, as a region of the enlarged sites. -/
def ancillaPhysicalRegion (X J : Finset ↥(Λ : Set (ℤ × ℤ))) : Finset (AncillaSites Λ X) :=
  J.disjSum ∅

/-! ### Operators -/

/-- **Supports on the enlarged sites.** An operator `P ⊗ (b ⊗ 1_{e'})`, with `P` acting on a
physical region `S` and `b` acting on `s'`, acts on `S ⊔ s'`.
Source: `09-amplification.tex`, lines 345–346 and 524–525. -/
theorem isSupportedOn_kronecker_submatrix_ancillaSplit {𝕜 : Type*} [RCLike 𝕜]
    {X S : Finset ↥(Λ : Set (ℤ × ℤ))} {P : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜}
    (hP : IsSupportedOn (map_embeddingSubtype_subset (T := Λ) S) P)
    (b : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) 𝕜) :
    IsSupportedOn (Finset.subset_univ (S.disjSum (Finset.univ.disjSum ∅) :
        Finset (AncillaSites Λ X)))
      (((P ⊗ₖ (b ⊗ₖ (1 : Matrix (RegionalConfiguration q X)
        (RegionalConfiguration q X) 𝕜))).submatrix (ancillaSplit q X)
          (ancillaSplit q X)).submatrix univEquiv univEquiv) := by
  obtain ⟨K, rfl⟩ := hP
  set S' : Finset (AncillaSites Λ X) := S.disjSum (Finset.univ.disjSum ∅) with hS'
  have hmem : ∀ i : ↥(S.map (Function.Embedding.subtype _)),
      (Sum.inl ⟨i.1, map_embeddingSubtype_subset (T := Λ) S i.2⟩ : AncillaSites Λ X) ∈ S' := by
    rintro ⟨i, hi⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hi
    exact Finset.inl_mem_disjSum.2 ha
  have hmem' : ∀ x : ↥X, (Sum.inr (Sum.inl x) : AncillaSites Λ X) ∈ S' := fun x => by
    simp [hS']
  refine isSupportedOn_submatrix_univEquiv_of_eq_ite S' _
    (fun w w' => K (fun i => w ⟨_, hmem i⟩) (fun i => w' ⟨_, hmem i⟩) *
      b (fun x => w ⟨_, hmem' x⟩) (fun x => w' ⟨_, hmem' x⟩)) fun c c' => ?_
  have hiff : (∀ v ∉ S', c v = c' v) ↔
      (∀ i : ↥(Λ : Set (ℤ × ℤ)), i ∉ S → c (Sum.inl i) = c' (Sum.inl i)) ∧
        c ∘ Sum.inr ∘ Sum.inr = c' ∘ Sum.inr ∘ Sum.inr := by
    constructor
    · intro h
      exact ⟨fun i hi => h _ (by simpa [hS'] using hi),
        funext fun x => h _ (by simp [hS'])⟩
    · rintro ⟨h1, h2⟩ v hv
      rcases v with v | x | x
      · exact h1 v (by simpa [hS'] using hv)
      · exact absurd (hmem' x) hv
      · exact congrFun h2 x
  have hrestr (w w' : Reg (Qudits q) Λ) :
      restr (S := Λ \ S.map (Function.Embedding.subtype _)) Finset.sdiff_subset w =
          restr Finset.sdiff_subset w' ↔
        ∀ i : ↥(Λ : Set (ℤ × ℤ)), i ∉ S → w i = w' i := by
    constructor
    · intro h i hi
      refine congrFun h ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, fun hm => hi ?_⟩⟩
      obtain ⟨a, ha, hai⟩ := Finset.mem_map.1 hm
      exact (Subtype.ext hai : a = i) ▸ ha
    · intro h
      funext i
      have hi := Finset.mem_sdiff.1 i.2
      exact h ⟨i.1, hi.1⟩ fun hS => hi.2 (Finset.mem_map_of_mem _ hS)
  simp only [submatrix_apply, kroneckerMap_apply, ancillaSplit_apply, extendId_apply, one_apply]
  by_cases h1 : ∀ i : ↥(Λ : Set (ℤ × ℤ)), i ∉ S → c (Sum.inl i) = c' (Sum.inl i)
  · by_cases h2 : c ∘ Sum.inr ∘ Sum.inr = c' ∘ Sum.inr ∘ Sum.inr
    · rw [if_pos ((hrestr (c ∘ Sum.inl) (c' ∘ Sum.inl)).2 h1), if_pos h2,
        if_pos (hiff.2 ⟨h1, h2⟩), mul_one]
      rfl
    · rw [if_neg h2, if_neg fun h => h2 (hiff.1 h).2, mul_zero, mul_zero]
  · rw [if_neg ((hrestr (c ∘ Sum.inl) (c' ∘ Sum.inl)).not.2 h1),
      if_neg fun h => h1 (hiff.1 h).1, zero_mul]

/-- **Physical operators on the enlarged sites.** A physical operator acting on a region `S`,
tensored with the identity on both copies, acts on `S ⊔ s'`. -/
theorem isSupportedOn_kronecker_one_submatrix_ancillaSplit {𝕜 : Type*} [RCLike 𝕜]
    {X S : Finset ↥(Λ : Set (ℤ × ℤ))} {L : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) 𝕜}
    (hL : IsSupportedOn (map_embeddingSubtype_subset (T := Λ) S) L) :
    IsSupportedOn (Finset.subset_univ (S.disjSum (Finset.univ.disjSum ∅) :
        Finset (AncillaSites Λ X)))
      (((L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
        (RegionalConfiguration q X × RegionalConfiguration q X) 𝕜)).submatrix
          (ancillaSplit q X) (ancillaSplit q X)).submatrix univEquiv univEquiv) := by
  have h := isSupportedOn_kronecker_submatrix_ancillaSplit (X := X) hL 1
  rwa [one_kronecker_one] at h

/-! ### Vectors and mutual information -/

/-- The value of `restoringSplit` inverted at a configuration whose `X` part is replaced. -/
theorem restoringSplit_symm_replace (X Y : Finset ↥(Λ : Set (ℤ × ℤ))) (hXY : Disjoint X Y)
    (c : Reg (Qudits q) Λ) (e : RegionalConfiguration q X) :
    (restoringSplit q X Y hXY).symm ((e, (restoringSplit q X Y hXY c).1.2),
        (restoringSplit q X Y hXY c).2) =
      fun v : ↥(Λ : Set (ℤ × ℤ)) => if hv : v ∈ X then e ⟨v, hv⟩ else c v := by
  funext v
  change (FiniteProduct.splitEquiv (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) (X ∪ Y)).symm
    ((FiniteProduct.unionEquiv (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) X Y hXY).symm
      (e, fun w : ↥Y => c w), fun w => c w) v = _
  by_cases hv : v ∈ X ∪ Y
  · rw [FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ hv]
    by_cases hvX : v ∈ X
    · simp [FiniteProduct.unionEquiv, hvX]
    · simp [FiniteProduct.unionEquiv, hvX]
  · have hvX : v ∉ X := fun h => hv (Finset.mem_union_left Y h)
    rw [FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv]
    simp [hvX]

/-- The swap of each site of the target `X` with its copy in `e'`. -/
def ancillaSwapFun (X : Finset ↥(Λ : Set (ℤ × ℤ))) : AncillaSites Λ X → AncillaSites Λ X
  | .inl v => if hv : v ∈ X then .inr (.inr ⟨v, hv⟩) else .inl v
  | .inr (.inl x) => .inr (.inl x)
  | .inr (.inr x) => .inl x.val

theorem ancillaSwapFun_involutive (X : Finset ↥(Λ : Set (ℤ × ℤ))) :
    Function.Involutive (ancillaSwapFun X) := by
  rintro (v | x | x)
  · by_cases hv : v ∈ X <;> simp [ancillaSwapFun, hv]
  · rfl
  · simp [ancillaSwapFun, x.2]

/-- The swap of the target with its copy `e'`, as a permutation of the enlarged sites. -/
def ancillaSwap (X : Finset ↥(Λ : Set (ℤ × ℤ))) : Equiv.Perm (AncillaSites Λ X) :=
  (ancillaSwapFun_involutive X).toPerm _

/-- **The restored vector has a product reduction on `e'` and a physical region.** For a
unit physical vector `Ω` and a unit ancillary vector `χ`, the vector `Ω ⊗ χ` on the enlarged
sites has no mutual information between `e'` and any physical region.
Source: `09-amplification.tex`, lines 342–347 and 550–551. -/
theorem mutualInformation_ancillaProduct_copy_eq_zero {X : Finset ↥(Λ : Set (ℤ × ℤ))}
    {Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)} (hΩ : ‖Ω‖ = 1)
    {χ : RegionalConfiguration q X × RegionalConfiguration q X → ℂ}
    (hχ : ‖WithLp.toLp 2 χ‖ = 1) (X' : Finset ↥X) (J : Finset ↥(Λ : Set (ℤ × ℤ))) :
    FiniteProduct.mutualInformation (fun _ : AncillaSites Λ X => Fin q)
        (WithLp.toLp 2 ((fun c => Ω c.1 * χ c.2) ∘ ancillaSplit q X))
        (ancillaCopyRegion X') (ancillaPhysicalRegion X J) = 0 := by
  set g : EuclideanSpace ℂ (↥X ⊕ ↥X → Fin q) :=
    WithLp.toLp 2 fun d => χ (d ∘ Sum.inl, d ∘ Sum.inr)
  have hg : ‖g‖ = 1 := by
    rw [← hχ]
    exact EuclideanSpace.norm_toLp_comp_equiv (Equiv.sumArrowEquivProdArrow _ _ _) χ
  have hvec : WithLp.toLp 2 ((fun c => Ω c.1 * χ c.2) ∘ ancillaSplit q X) =
      FiniteProduct.sumSitesProduct (A := ↥(Λ : Set (ℤ × ℤ))) (F := Fin q) Ω g := rfl
  rw [hvec, ancillaCopyRegion, ancillaPhysicalRegion]
  exact FiniteProduct.mutualInformation_sumSitesProduct_inr_inl hΩ hg _ J

/-- **The copied vector carries the original reduction of the target, on `e'`.** Let `φ` be
the vector whose value at a physical configuration `c` and an ancillary pair `(s, e)` is
`a(s) b(c_X) Ω(c')`, where `c'` agrees with `c` off `X` and reads `e` on `X`, for unit
vectors `a, b`. For a part `X'` of `X` and a physical region `J` disjoint from `X`, the
mutual information of `φ` between the copy of `X'` in `e'` and `J` equals `I_Ω(X' : J)`.
Source: `09-amplification.tex`, lines 342–344 and 547–550. -/
theorem mutualInformation_ancillaCopy_eq {X Y : Finset ↥(Λ : Set (ℤ × ℤ))}
    (hXY : Disjoint X Y) {Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)} (hΩ : ‖Ω‖ = 1)
    {a b : RegionalConfiguration q X → ℂ}
    (ha : ‖WithLp.toLp 2 a‖ = 1) (hb : ‖WithLp.toLp 2 b‖ = 1) (X' : Finset ↥X)
    {J : Finset ↥(Λ : Set (ℤ × ℤ))} (hJ : Disjoint J X) :
    FiniteProduct.mutualInformation (fun _ : AncillaSites Λ X => Fin q)
        (WithLp.toLp 2 ((fun c : Reg (Qudits q) Λ × (RegionalConfiguration q X ×
          RegionalConfiguration q X) => a c.2.1 * b (restoringSplit q X Y hXY c.1).1.1 *
            Ω ((restoringSplit q X Y hXY).symm ((c.2.2, (restoringSplit q X Y hXY c.1).1.2),
              (restoringSplit q X Y hXY c.1).2))) ∘ ancillaSplit q X))
        (ancillaCopyRegion X') (ancillaPhysicalRegion X J) =
      FiniteProduct.mutualInformation (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ω (X'.map
        (Function.Embedding.subtype _)) J := by
  set g : EuclideanSpace ℂ (↥X ⊕ ↥X → Fin q) :=
    WithLp.toLp 2 fun d => a (d ∘ Sum.inl) * b (d ∘ Sum.inr)
  have hab : ‖WithLp.toLp 2 (fun p : RegionalConfiguration q X × RegionalConfiguration q X =>
      a p.1 * b p.2)‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron (WithLp.toLp 2 a) (WithLp.toLp 2 b)
    rw [ha, hb, mul_one] at h
    exact h
  have hg : ‖g‖ = 1 := by
    rw [← hab]
    exact EuclideanSpace.norm_toLp_comp_equiv (Equiv.sumArrowEquivProdArrow ↥X ↥X (Fin q))
      (fun p : RegionalConfiguration q X × RegionalConfiguration q X => a p.1 * b p.2)
  have hσ : ∀ x, (ancillaSwap X).symm x = ancillaSwapFun X x := fun x => rfl
  have hvec : WithLp.toLp 2 ((fun c : Reg (Qudits q) Λ × (RegionalConfiguration q X ×
      RegionalConfiguration q X) => a c.2.1 * b (restoringSplit q X Y hXY c.1).1.1 *
        Ω ((restoringSplit q X Y hXY).symm ((c.2.2, (restoringSplit q X Y hXY c.1).1.2),
          (restoringSplit q X Y hXY c.1).2))) ∘ ancillaSplit q X) =
      FiniteProduct.relabelSites (ancillaSwap X)
        (FiniteProduct.sumSitesProduct (A := ↥(Λ : Set (ℤ × ℤ))) Ω g) := by
    congr 1
    funext c
    simp only [Function.comp_apply, ancillaSplit_apply, restoringSplit_symm_replace,
      FiniteProduct.sumSitesProduct, g, PiLp.toLp_apply]
    have h1 : (c ∘ (ancillaSwap X).symm) ∘ Sum.inl =
        fun v => if hv : v ∈ X then c (Sum.inr (Sum.inr ⟨v, hv⟩)) else c (Sum.inl v) := by
      funext v
      simp only [Function.comp_apply, hσ, ancillaSwapFun]
      split_ifs <;> rfl
    have h2 : ((c ∘ (ancillaSwap X).symm) ∘ Sum.inr) ∘ Sum.inl = c ∘ Sum.inr ∘ Sum.inl := rfl
    have h3 : ((c ∘ (ancillaSwap X).symm) ∘ Sum.inr) ∘ Sum.inr =
        fun x : ↥X => c (Sum.inl x.val) := rfl
    rw [h1, h2, h3]
    have h4 : (restoringSplit q X Y hXY (c ∘ Sum.inl)).1.1 =
        fun x : ↥X => c (Sum.inl x.val) := rfl
    rw [h4]
    ring
  have hcopy : (ancillaCopyRegion X').map (ancillaSwap X).toEmbedding =
      (X'.map (Function.Embedding.subtype _)).disjSum ∅ := by
    ext x
    rw [Finset.mem_map_equiv, hσ]
    rcases x with v | y | y
    · by_cases hv : v ∈ X
      · simp only [ancillaSwapFun, hv, dite_true, ancillaCopyRegion, Finset.inr_mem_disjSum,
          Finset.inl_mem_disjSum, Finset.mem_map, Function.Embedding.coe_subtype]
        constructor
        · intro h
          exact ⟨_, h, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact hx
      · simp only [ancillaSwapFun, hv, dite_false, ancillaCopyRegion, Finset.inl_mem_disjSum,
          Finset.notMem_empty, false_iff, Finset.mem_map, Function.Embedding.coe_subtype,
          not_exists, not_and]
        exact fun x _ hx => hv (hx ▸ x.2)
    · simp [ancillaSwapFun, ancillaCopyRegion]
    · simp [ancillaSwapFun, ancillaCopyRegion]
  have hphys : (ancillaPhysicalRegion X J).map (ancillaSwap X).toEmbedding = J.disjSum ∅ := by
    ext x
    rw [Finset.mem_map_equiv, hσ]
    rcases x with v | y | y
    · by_cases hv : v ∈ X
      · have hvJ : v ∉ J := fun h => Finset.disjoint_left.mp hJ h hv
        simp [ancillaSwapFun, ancillaPhysicalRegion, hv, hvJ]
      · simp [ancillaSwapFun, ancillaPhysicalRegion, hv]
    · simp [ancillaSwapFun, ancillaPhysicalRegion]
    · have hyJ : (y : ↥(Λ : Set (ℤ × ℤ))) ∉ J := fun h => Finset.disjoint_left.mp hJ h y.2
      simp [ancillaSwapFun, ancillaPhysicalRegion, hyJ]
  rw [hvec, FiniteProduct.mutualInformation_relabelSites, hcopy, hphys]
  exact FiniteProduct.mutualInformation_sumSitesProduct_inl hΩ hg _ _

end OpenAI
