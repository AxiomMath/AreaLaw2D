import OpenAI.RegionEntropy

/-!
# Two-family entropy cancellation

Lemma 11.1 of [OAI265, §11.1].  Let `ψ` be a pure state on `Λ` and
`A = D ∪ ⋃ᵢ Xᵢ ⊆ Λ` a disjoint decomposition whose pieces carry labels `f i ∈ {0, 1}`, each
family ordered as in `Fin m`.  If every piece is nearly uncorrelated with `B = Λ \ A` together
with the earlier pieces of its own family, `I(Xᵢ : B ∪ ⋃_{j < i, f j = f i} X_j) ≤ εᵢ`, then
`S(A) ≤ S(D) + ½ ∑ εᵢ`.

For one family `F`, with `A_F = ⋃_{i ∈ F} Xᵢ`, the chain rule and purity give
`S(B ∪ A_F) ≥ S(A) + ∑_{i ∈ F} S(Xᵢ) - ∑_{i ∈ F} εᵢ`, while purity and subadditivity give
`S(B ∪ A_F) = S(D ∪ A_{F'}) ≤ S(D) + ∑_{i ∈ F'} S(Xᵢ)` for the other family `F'`
(`regionEntropy_add_sum_le_of_mutualInfo_le`).  Adding the two instances cancels the
single-piece entropies.

## Main statements

* `OpenAI.regionEntropy_add_sum_le_of_mutualInfo_le`: the one-family bound.
* `OpenAI.two_family_cancellation`: Lemma 11.1.

## Implementation notes

Deviation (CLAUDE.md criterion 3, decision 4.3 in docs/oai265/Memory.md): subadditivity enters through
`Arealaw.MState.regionEntropy_union_biUnion_le`, which is proved over `ℂ`, where Physlib's
`Sᵥₙ_subadditivity` lives, and transferred to `𝕜` by `OpenAI.Embedding`.  Purity and the
chain rule are native over `𝕜`.
-/

namespace OpenAI

open Arealaw

variable {σ : Type*} [DecidableEq σ]

/-- Removing from `Λ` the complement of `A = D ∪ ⋃ᵢ Xᵢ` and the pieces `Xᵢ` with `p i` leaves
`D` and the pieces with `¬p i`, when the decomposition is disjoint. -/
theorem sdiff_sdiff_union_biUnion_filter {ι : Type*} [Fintype ι] {Λ A D : Finset σ}
    (hA : A ⊆ Λ) {X : ι → Finset σ} (p : ι → Prop) [DecidablePred p]
    (hAD : A = D ∪ Finset.univ.biUnion X) (hDX : ∀ i, Disjoint D (X i))
    (hXX : Pairwise (Function.onFun Disjoint X)) :
    Λ \ (Λ \ A ∪ (Finset.univ.filter p).biUnion X) =
      D ∪ (Finset.univ.filter fun i => ¬p i).biUnion X := by
  have hmem : ∀ x, x ∈ A ↔ x ∈ D ∨ ∃ i, x ∈ X i := fun x => by simp [hAD]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxΛ, hx⟩
    have hxA : x ∈ A := by_contra fun h => hx (Or.inl ⟨hxΛ, h⟩)
    rcases (hmem x).1 hxA with h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, fun hp => hx (Or.inr ⟨i, hp, hi⟩), hi⟩
  · rintro (h | ⟨i, hpi, hi⟩)
    · have hxA : x ∈ A := (hmem x).2 (Or.inl h)
      refine ⟨hA hxA, ?_⟩
      rintro (⟨_, h'⟩ | ⟨j, _, hj⟩)
      · exact h' hxA
      · exact Finset.disjoint_left.1 (hDX j) h hj
    · have hxA : x ∈ A := (hmem x).2 (Or.inr ⟨i, hi⟩)
      refine ⟨hA hxA, ?_⟩
      rintro (⟨_, h'⟩ | ⟨j, hpj, hj⟩)
      · exact h' hxA
      · exact Finset.disjoint_left.1 (hXX fun h : i = j => hpi (h ▸ hpj)) hi hj

variable {loc : σ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
  {𝕜 : Type*} [RCLike 𝕜]

/-- **The one-family bound** behind Lemma 11.1 [OAI265, §11.1]: for a pure state `ψ` on `Λ`,
a disjoint decomposition `A = D ∪ ⋃ᵢ Xᵢ ⊆ Λ` over an ordered index, and a family `p` with
`I(Xᵢ : (Λ \ A) ∪ ⋃_{j < i, p j} X_j) ≤ εᵢ` for `p i`,
`S(A) + ∑_{p i} S(Xᵢ) ≤ S(D) + ∑_{¬p i} S(Xᵢ) + ∑_{p i} εᵢ`. -/
theorem regionEntropy_add_sum_le_of_mutualInfo_le {ι : Type*} [Fintype ι] [LinearOrder ι]
    {Λ : Finset σ} (ψ : Reg loc Λ → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1) {A D : Finset σ} (hA : A ⊆ Λ)
    (hD : D ⊆ Λ) {X : ι → Finset σ} (hX : ∀ i, X i ⊆ Λ) (p : ι → Prop) [DecidablePred p]
    (ε : ι → ℝ) (hAD : A = D ∪ Finset.univ.biUnion X) (hDX : ∀ i, Disjoint D (X i))
    (hXX : Pairwise (Function.onFun Disjoint X))
    (hε : ∀ i, p i → (pureState ψ hψ).mutualInfo (hX i)
        (Finset.union_subset Finset.sdiff_subset (Finset.biUnion_subset.2 fun j _ => hX j) :
          Λ \ A ∪ (Finset.univ.filter fun j => p j ∧ j < i).biUnion X ⊆ Λ) ≤ ε i) :
    (pureState ψ hψ).regionEntropy hA +
        ∑ i ∈ Finset.univ.filter p, (pureState ψ hψ).regionEntropy (hX i) ≤
      (pureState ψ hψ).regionEntropy hD +
        ∑ i ∈ Finset.univ.filter (fun i => ¬p i), (pureState ψ hψ).regionEntropy (hX i) +
        ∑ i ∈ Finset.univ.filter p, ε i := by
  have hB : Λ \ A ⊆ Λ := Finset.sdiff_subset
  have hchain := (pureState ψ hψ).regionEntropy_union_biUnion hB (Finset.univ.filter p) hX
  have hI : ∑ i ∈ Finset.univ.filter p, (pureState ψ hψ).mutualInfo (hX i)
      (Finset.union_subset hB (Finset.biUnion_subset.2 fun j _ => hX j) :
        Λ \ A ∪ ((Finset.univ.filter p).filter (· < i)).biUnion X ⊆ Λ) ≤
      ∑ i ∈ Finset.univ.filter p, ε i :=
    Finset.sum_le_sum fun i hi => ((pureState ψ hψ).mutualInfo_congr rfl
      (by rw [Finset.filter_filter]) _ _ _ _).trans_le (hε i (Finset.mem_filter.1 hi).2)
  have hpureA := regionEntropy_pureState_sdiff hA ψ hψ
  have hpureB := regionEntropy_pureState_sdiff
    (Finset.union_subset hB (Finset.biUnion_subset.2 fun j _ => hX j) :
      Λ \ A ∪ (Finset.univ.filter p).biUnion X ⊆ Λ) ψ hψ
  rw [(pureState ψ hψ).regionEntropy_congr (sdiff_sdiff_union_biUnion_filter hA p hAD hDX hXX) _
    (Finset.union_subset hD (Finset.biUnion_subset.2 fun i _ => hX i))] at hpureB
  have hsub := (pureState ψ hψ).regionEntropy_union_biUnion_le hD
    (Finset.univ.filter fun i => ¬p i) hX (fun i _ => hDX i) (hXX.set_pairwise _)
  linarith

/-- **Lemma 11.1** [OAI265, §11.1]. -/
theorem two_family_cancellation {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ]
    {loc : σ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] :
    TwoFamilyCancellation σ loc 𝕜 := by
  intro Λ ψ hψ A D hA hD m X hX f ε hAD hDX hXX hε
  have key (c : Fin 2) := regionEntropy_add_sum_le_of_mutualInfo_le ψ hψ hA hD hX (f · = c) ε
    hAD hDX hXX fun i hi => ((pureState ψ hψ).mutualInfo_congr rfl (by rw [hi]) _ _ _ _).trans_le
      (hε i)
  have h0 := key 0
  have h1 := key 1
  have hc : ∀ i, ¬f i = 0 ↔ f i = 1 := fun i => by
    generalize f i = c; fin_cases c <;> decide
  have hc' : ∀ i, ¬f i = 1 ↔ f i = 0 := fun i => by
    generalize f i = c; fin_cases c <;> decide
  have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ (f · = 0) ε
  rw [Finset.filter_congr fun i _ => hc i] at h0 hsum
  rw [Finset.filter_congr fun i _ => hc' i] at h1
  linarith

end OpenAI

