import OpenAI.Statements

/-!
# Basic facts about the statement layer

Sanity lemmas for the definitions of `OpenAI.Statements` [OAI265, §1.1]: the domain distance
`domainEDist` agrees with `SimpleGraph.edist` of the induced graph, the square lattice has its
nearest-neighbour adjacency and degree four, the edge boundary counts each crossing edge once,
admissible Hamiltonians are Hermitian, range-zero supports are single sites, and a global gap
`H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)` with `Δ > 0` makes `E₀` the ground energy and `Ω` its unique ground
vector up to scalars.
-/

namespace OpenAI

open Arealaw
open scoped ComplexOrder MatrixOrder
open Matrix SimpleGraph

/-! ## The domain distance -/

section Distance

variable {Λ X : Finset (ℤ × ℤ)} {x y : ℤ × ℤ} {r : ℕ∞}

theorem domainEDist_of_mem (hx : x ∈ Λ) (hy : y ∈ Λ) :
    domainEDist Λ x y =
      ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist ⟨x, hx⟩ ⟨y, hy⟩ :=
  dif_pos ⟨hx, hy⟩

theorem domainEDist_of_not_mem_left (hx : x ∉ Λ) : domainEDist Λ x y = ⊤ :=
  dif_neg fun h => hx h.1

theorem domainEDist_of_not_mem_right (hy : y ∉ Λ) : domainEDist Λ x y = ⊤ :=
  dif_neg fun h => hy h.2

theorem domainEDist_comm : domainEDist Λ x y = domainEDist Λ y x := by
  by_cases hx : x ∈ Λ
  · by_cases hy : y ∈ Λ
    · rw [domainEDist_of_mem hx hy, domainEDist_of_mem hy hx, SimpleGraph.edist_comm]
    · rw [domainEDist_of_not_mem_right hy, domainEDist_of_not_mem_left hy]
  · rw [domainEDist_of_not_mem_left hx, domainEDist_of_not_mem_right hx]

/-- The domain distance vanishes exactly on the diagonal of `Λ`; off `Λ` it is `⊤`. -/
theorem domainEDist_eq_zero_iff : domainEDist Λ x y = 0 ↔ x ∈ Λ ∧ x = y := by
  by_cases hx : x ∈ Λ
  · by_cases hy : y ∈ Λ
    · rw [domainEDist_of_mem hx hy, SimpleGraph.edist_eq_zero_iff, Subtype.mk.injEq]
      exact ⟨fun h => ⟨hx, h⟩, And.right⟩
    · rw [domainEDist_of_not_mem_right hy]
      exact ⟨fun h => absurd h ENat.top_ne_zero, fun h => absurd (h.2 ▸ hx) hy⟩
  · rw [domainEDist_of_not_mem_left hx]
    exact ⟨fun h => absurd h ENat.top_ne_zero, fun h => absurd h.1 hx⟩

@[simp] theorem domainEDist_self (hx : x ∈ Λ) : domainEDist Λ x x = 0 :=
  domainEDist_eq_zero_iff.2 ⟨hx, rfl⟩

theorem domainEDiam_le_iff :
    domainEDiam Λ X ≤ r ↔ ∀ x ∈ X, ∀ y ∈ X, domainEDist Λ x y ≤ r := by
  simp only [domainEDiam, iSup₂_le_iff]

end Distance

/-! ## The square lattice -/

/-- Two sites of `ℤ²` are adjacent when one coordinate agrees and the other differs by one. -/
theorem squareLattice_adj_iff (x y : ℤ × ℤ) :
    (hasse ℤ □ hasse ℤ).Adj x y ↔
      (x.2 = y.2 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1)) ∨
        (x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) := by
  simp only [boxProd_adj, hasse_adj, Order.covBy_iff_add_one_eq]
  tauto

/-- The four lattice neighbours of a site. -/
theorem squareLattice_adj_mem (x y : ℤ × ℤ) (h : (hasse ℤ □ hasse ℤ).Adj x y) :
    y ∈ ({(x.1 + 1, x.2), (x.1 - 1, x.2), (x.1, x.2 + 1), (x.1, x.2 - 1)} :
      Finset (ℤ × ℤ)) := by
  obtain ⟨y1, y2⟩ := y
  rw [squareLattice_adj_iff] at h
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- Every site of the square lattice has at most four neighbours in any finite set. -/
theorem card_neighbors_le_four (x : ℤ × ℤ) (s : Finset (ℤ × ℤ)) :
    (s.filter ((hasse ℤ □ hasse ℤ).Adj x)).card ≤ 4 :=
  (Finset.card_le_card fun y hy => squareLattice_adj_mem x y (Finset.mem_filter.1 hy).2).trans
    Finset.card_le_four

/-! ## The edge boundary -/

section EdgeBoundary

variable {Λ A : Finset (ℤ × ℤ)}

theorem mem_edgeBoundary {p : (ℤ × ℤ) × (ℤ × ℤ)} :
    p ∈ edgeBoundary Λ A ↔ p.1 ∈ A ∧ p.2 ∈ Λ \ A ∧ (hasse ℤ □ hasse ℤ).Adj p.1 p.2 :=
  mem_interedges_iff _

theorem edgeBoundary_subset : edgeBoundary Λ A ⊆ A ×ˢ (Λ \ A) := fun p hp => by
  rw [mem_edgeBoundary] at hp
  exact Finset.mem_product.2 ⟨hp.1, hp.2.1⟩

/-- Unordering is injective on the edge boundary: the endpoint in `A` fixes the orientation. -/
theorem injOn_mk_edgeBoundary :
    Set.InjOn (fun p : (ℤ × ℤ) × (ℤ × ℤ) => s(p.1, p.2)) (edgeBoundary Λ A) := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
  rw [Finset.mem_coe, mem_edgeBoundary, Finset.mem_sdiff] at hp hp'
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hp.1 hp'.2.1.2

/-- The edge boundary counts each unordered crossing edge `{x, y}` once, so its cardinality
is the paper's `|∂_Λ A|`. -/
theorem card_image_mk_edgeBoundary :
    ((edgeBoundary Λ A).image fun p => s(p.1, p.2)).card = (edgeBoundary Λ A).card :=
  Finset.card_image_of_injOn injOn_mk_edgeBoundary

theorem mem_image_mk_edgeBoundary {e : Sym2 (ℤ × ℤ)} :
    e ∈ (edgeBoundary Λ A).image (fun p => s(p.1, p.2)) ↔
      ∃ x ∈ A, ∃ y ∈ Λ \ A, (hasse ℤ □ hasse ℤ).Adj x y ∧ e = s(x, y) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_edgeBoundary] at hp
    exact ⟨p.1, hp.1, p.2, hp.2.1, hp.2.2, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨(x, y), mem_edgeBoundary.2 ⟨hx, hy, hxy⟩, rfl⟩

end EdgeBoundary

/-! ## Admissible supports and Hamiltonians -/

section Hamiltonian

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J : ℝ} {Λ X : Finset (ℤ × ℤ)}
  {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}

theorem mem_supports_iff : X ∈ supports Λ R ↔ X ⊆ Λ ∧ X.Nonempty ∧ domainEDiam Λ X ≤ R := by
  rw [supports, Finset.mem_filter, Finset.mem_powerset]

/-- The supports of range zero are the single sites of `Λ`. -/
theorem mem_supports_zero_iff : X ∈ supports Λ 0 ↔ ∃ x ∈ Λ, X = {x} := by
  rw [mem_supports_iff, Nat.cast_zero, domainEDiam_le_iff]
  simp only [nonpos_iff_eq_zero, domainEDist_eq_zero_iff]
  constructor
  · rintro ⟨hΛ, ⟨x, hx⟩, h⟩
    exact ⟨x, hΛ hx, Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => (h x hx y hy).2.symm⟩⟩
  · rintro ⟨x, hx, rfl⟩
    simp [hx]

/-- A sum of Hermitian terms extended by the identity is Hermitian. -/
theorem isHermitian_hamiltonian (h : ∀ X ⊆ Λ, (Φ X).IsHermitian) :
    (hamiltonian Λ Φ).IsHermitian :=
  (isSelfAdjoint_sum _ fun X _ =>
    (isHermitian_extendId _ (h X.1 (Finset.mem_powerset.1 X.2))).isSelfAdjoint).isHermitian

namespace IsAdmissible

theorem isHermitian_hamiltonian (hΦ : IsAdmissible Λ R J Φ) : (hamiltonian Λ Φ).IsHermitian :=
  OpenAI.isHermitian_hamiltonian fun X hX => (hΦ X hX).1

/-- A nonzero term of a range-zero interaction acts on a single site. -/
theorem exists_eq_singleton (hΦ : IsAdmissible Λ 0 J Φ) (hX : X ⊆ Λ) (h0 : Φ X ≠ 0) :
    ∃ x ∈ Λ, X = {x} :=
  mem_supports_zero_iff.1 (by_contra fun h => h0 ((hΦ X hX).2.2 h))

end IsAdmissible

end Hamiltonian

/-! ## Ground states and the global gap -/

section Gap

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι 𝕜}
  {Ω v : ι → 𝕜} {E₀ Δ : ℝ}

omit [DecidableEq ι] in
@[simp] theorem pureState_M (hΩ : star Ω ⬝ᵥ Ω = 1) :
    (pureState Ω hΩ).M = vecMulVec Ω (star Ω) := rfl

/-- The complement `1 - |Ω⟩⟨Ω|` of a unit vector is an orthogonal projection, hence positive
semidefinite. -/
theorem posSemidef_one_sub_vecMulVec_self_star (hΩ : star Ω ⬝ᵥ Ω = 1) :
    (1 - vecMulVec Ω (star Ω)).PosSemidef := by
  have hP : (1 - vecMulVec Ω (star Ω))ᴴ * (1 - vecMulVec Ω (star Ω)) =
      1 - vecMulVec Ω (star Ω) := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_vecMulVec, star_star, sub_mul,
      mul_sub, mul_sub, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, hΩ, one_smul]
    abel
  exact hP ▸ posSemidef_conjTranspose_mul_self _

/-- A nonnegative gap makes `H - E₀` positive semidefinite. -/
theorem HasGlobalGap.posSemidef_sub_smul_one (hgap : HasGlobalGap H Ω E₀ Δ) (hΔ : 0 ≤ Δ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) : (H - (E₀ : 𝕜) • 1).PosSemidef := by
  have h0 : (0 : Matrix ι ι 𝕜) ≤ (Δ : 𝕜) • (1 - vecMulVec Ω (star Ω)) := by
    rw [Matrix.le_iff, sub_zero]
    exact (posSemidef_one_sub_vecMulVec_self_star hΩ).smul (RCLike.ofReal_nonneg.2 hΔ)
  simpa [Matrix.le_iff] using h0.trans hgap

/-- **`E₀` is the ground energy**: under a nonnegative gap every vector has energy at least
`E₀`. -/
theorem HasGlobalGap.le_re_dotProduct_mulVec (hgap : HasGlobalGap H Ω E₀ Δ) (hΔ : 0 ≤ Δ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (v : ι → 𝕜) :
    E₀ * RCLike.re (star v ⬝ᵥ v) ≤ RCLike.re (star v ⬝ᵥ (H *ᵥ v)) := by
  have h := RCLike.nonneg_iff.1 ((hgap.posSemidef_sub_smul_one hΔ hΩ).dotProduct_mulVec_nonneg v)
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    map_sub, RCLike.re_ofReal_mul] at h
  linarith [h.1]

/-- **Uniqueness of the ground state**: under a positive gap every eigenvector of `H` with
eigenvalue `E₀` is a multiple of `Ω`. -/
theorem HasGlobalGap.eq_smul_of_mulVec_eq (hgap : HasGlobalGap H Ω E₀ Δ) (hΔ : 0 < Δ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) (hΩE : H *ᵥ Ω = (E₀ : 𝕜) • Ω) (hv : H *ᵥ v = (E₀ : 𝕜) • v) :
    v = (star Ω ⬝ᵥ v) • Ω := by
  set w := v - (star Ω ⬝ᵥ v) • Ω with hw
  have hHw : (H - (E₀ : 𝕜) • 1) *ᵥ w = 0 := by
    rw [hw, sub_mulVec, smul_mulVec, one_mulVec, mulVec_sub, mulVec_smul, hv, hΩE]
    module
  have hΩw : star Ω ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, hΩ, smul_eq_mul, mul_one, sub_self]
  have hPw : (1 - vecMulVec Ω (star Ω)) *ᵥ w = w := by
    rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, hΩw, MulOpposite.op_zero, zero_smul, sub_zero]
  have h := (Matrix.le_iff.1 hgap).dotProduct_mulVec_nonneg w
  rw [sub_mulVec, hHw, smul_mulVec, hPw, zero_sub, dotProduct_neg, dotProduct_smul,
    smul_eq_mul, neg_nonneg] at h
  have hww : star w ⬝ᵥ w = 0 := by
    refine le_antisymm ?_ (dotProduct_star_self_nonneg w)
    have h' := mul_nonpos_of_nonneg_of_nonpos (RCLike.ofReal_nonneg.2 (inv_nonneg.2 hΔ.le)) h
    rwa [← mul_assoc, ← RCLike.ofReal_mul, inv_mul_cancel₀ hΔ.ne', RCLike.ofReal_one,
      one_mul] at h'
  exact sub_eq_zero.1 (dotProduct_star_self_eq_zero.1 hww)

end Gap

end OpenAI
