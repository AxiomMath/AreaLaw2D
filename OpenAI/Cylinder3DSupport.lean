import AreaLaw.Transfer
import AreaLawForMathlib.QuantumInfo.Entropy.Subadditivity
import AreaLawForMathlib.QuantumInfo.StateToComplex
import AreaLawForMathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Lemmas of v1 used by the cylinder area law

`OpenAI/Cylinder3D.lean` was written against the v1 tree (tag `v1.0`). The restructuring into
`AreaLaw/` and `AreaLawForMathlib/` removed or renamed the lemmas below, so they are restored
here under their v1 names and namespaces, with their v1 proofs, from `OpenAI/Basic.lean`,
`OpenAI/Rectangles.lean`, `OpenAI/SupportCounting.lean`, `OpenAI/ZeroBoundary.lean`,
`OpenAI/CutTransport.lean`, `OpenAI/RegionEntropy.lean`, `OpenAI/BoxEntropy.lean`,
`OpenAI/AreaLaw.lean` and `Arealaw/State.lean` of v1. The only proofs that differ from v1 are
those of `OpenAI.area_law`, which applies `AreaLaw.areaLaw`, and of
`Arealaw.MState.regionEntropy_union_le`, which goes through the embedding into `ℂ` of
`AreaLawForMathlib/QuantumInfo/StateToComplex.lean` in place of v1's `OpenAI/Embedding.lean`.
-/

open Matrix SimpleGraph

/-! ## Spectra that agree away from zero -/

namespace Arealaw

section Spectrum

variable {𝕜 : Type*} [RCLike 𝕜] {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

/-- Reduced density operator on the `A` side, `ρ_A = M Mᴴ`. -/
def rhoA (M : Matrix A B 𝕜) : Matrix A A 𝕜 := M * Mᴴ

omit [Fintype A] [DecidableEq A] in
/-- `ρ_A = M Mᴴ` is Hermitian. -/
theorem isHermitian_rhoA (M : Matrix A B 𝕜) : (rhoA M).IsHermitian :=
  isHermitian_mul_conjTranspose_self M

/-- Entanglement entropy across the `A | B` cut: the Shannon entropy of the eigenvalues of
the reduced density operator `ρ_A`. -/
noncomputable def EE (M : Matrix A B 𝕜) : ℝ := H (isHermitian_rhoA M).eigenvalues

end Spectrum

section Spectrum

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Shannon entropy of a family is the sum of `negMulLog` over its nonzero values. -/
theorem H_eq_sum_filter_ne_zero (p : ι → ℝ) :
    H p = (((Finset.univ.val.map p).filter (· ≠ 0)).map Real.negMulLog).sum := by
  rw [H_eq_multiset_sum]
  conv_lhs => rw [← Multiset.filter_add_not (· ≠ 0) (Finset.univ.val.map p)]
  rw [Multiset.map_add, Multiset.sum_add, add_eq_left]
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
  rw [not_not.1 (Multiset.mem_filter.1 hy).2, Real.negMulLog_zero]

/-- **The Shannon entropy ignores zeros**: two families with the same nonzero values, counted
with multiplicity, have the same entropy. -/
theorem H_eq_of_filter_ne_zero_eq {p : ι → ℝ} {q : κ → ℝ}
    (h : (Finset.univ.val.map p).filter (· ≠ 0) = (Finset.univ.val.map q).filter (· ≠ 0)) :
    H p = H q := by
  rw [H_eq_sum_filter_ne_zero, H_eq_sum_filter_ne_zero, h]

/-- `AB` and `BA` have the same nonzero characteristic roots, with multiplicity, for
rectangular `A` and `B`. -/
theorem roots_charpoly_mul_comm_filter_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).charpoly.roots.filter (· ≠ 0) = (B * A).charpoly.roots.filter (· ≠ 0) := by
  have h := congrArg (fun p : Polynomial R => p.roots.filter (· ≠ 0)) (charpoly_mul_comm' A B)
  have hz (n : ℕ) : (Multiset.replicate n (0 : R)).filter (· ≠ 0) = 0 :=
    Multiset.filter_eq_nil.2 fun a ha => by simp [Multiset.eq_of_mem_replicate ha]
  simpa [Polynomial.roots_mul, Polynomial.Monic.ne_zero, Matrix.charpoly_monic,
    Polynomial.X_ne_zero, pow_ne_zero, Multiset.nsmul_singleton, hz] using h

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι] [DecidableEq κ]

/-- Two Hermitian matrices whose characteristic polynomials have the same nonzero roots have
the same spectral entropy, whatever their sizes. -/
theorem H_eigenvalues_eq_of_roots_charpoly_filter_eq {A : Matrix ι ι 𝕜} {B : Matrix κ κ 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly.roots.filter (· ≠ 0) = B.charpoly.roots.filter (· ≠ 0)) :
    H hA.eigenvalues = H hB.eigenvalues := by
  refine H_eq_of_filter_ne_zero_eq (Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) ?_)
  rw [hA.roots_charpoly_eq_eigenvalues, hB.roots_charpoly_eq_eigenvalues] at h
  simpa [Multiset.filter_map, Multiset.map_map, Function.comp_def] using h

/-- Equal Hermitian matrices have equal spectral entropies; the Hermiticity proofs are
irrelevant. -/
theorem H_eigenvalues_congr {A B : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : H hA.eigenvalues = H hB.eigenvalues := by
  subst h; rfl

/-- **Purity across a cut**: the entanglement entropy of a bipartite pure state is the same
from either side, `S(ρ_A) = S(ρ_B)`, where `ρ_B = Mᵀ (Mᵀ)ᴴ`. -/
theorem EE_transpose (M : Matrix ι κ 𝕜) : EE Mᵀ = EE M := by
  refine H_eigenvalues_eq_of_roots_charpoly_filter_eq _ _ ?_
  rw [rhoA, rhoA, conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul,
    charpoly_transpose]
  exact roots_charpoly_mul_comm_filter_ne_zero _ _

omit [DecidableEq κ] in
/-- Relabelling the traced-out side of a bipartite pure state leaves its entanglement entropy
unchanged. -/
theorem EE_submatrix_id_equiv {μ : Type*} [Fintype μ] (M : Matrix ι κ 𝕜) (e : μ ≃ κ) :
    EE (M.submatrix id e) = EE M :=
  H_eigenvalues_congr _ _ (by
    rw [rhoA, rhoA, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id])

end Spectrum

/-! ## Region entropies over any `RCLike` field -/

namespace MState

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U X : Finset σ}

/-- **Subadditivity on regions** over any `RCLike` field: `S(X ∪ Y) ≤ S(X) + S(Y)` for
disjoint `X`, `Y`. -/
theorem regionEntropy_union_le (ρ : MState (Reg loc U) 𝕜) {X Y : Finset σ} (hd : Disjoint X Y)
    (hX : X ⊆ U) (hY : Y ⊆ U) :
    ρ.regionEntropy (Finset.union_subset hX hY) ≤ ρ.regionEntropy hX + ρ.regionEntropy hY := by
  simpa using Arealaw.regionEntropy_union_le ρ.toComplex hd hX hY

/-- A region of `|X|` sites, each of dimension `d`, has entropy at most `|X| log d`. -/
theorem regionEntropy_le_card_mul_log (ρ : MState (Reg loc U) 𝕜) (h : X ⊆ U) {d : ℕ}
    (hd : ∀ i, Fintype.card (loc i) = d) : ρ.regionEntropy h ≤ X.card * Real.log d := by
  have := (ρ.restrict h).entropy_le_log_card
  rw [card_reg_const hd, Nat.cast_pow, Real.log_pow] at this
  exact this

end MState

end Arealaw

namespace OpenAI

open Arealaw

/-! ## Distances, supports and the edge boundary on `ℤ²` -/

section Lattice

variable {Λ A X : Finset (ℤ × ℤ)} {R : ℕ} {x y : ℤ × ℤ} {r : ℕ∞}

theorem domainEDist_of_mem (hx : x ∈ Λ) (hy : y ∈ Λ) :
    domainEDist Λ x y =
      ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))).edist ⟨x, hx⟩ ⟨y, hy⟩ :=
  dif_pos ⟨hx, hy⟩

theorem domainEDiam_le_iff :
    domainEDiam Λ X ≤ r ↔ ∀ x ∈ X, ∀ y ∈ X, domainEDist Λ x y ≤ r := by
  simp only [domainEDiam, iSup₂_le_iff]

/-- Two sites of `ℤ²` are adjacent when one coordinate agrees and the other differs by one. -/
theorem squareLattice_adj_iff (x y : ℤ × ℤ) :
    (hasse ℤ □ hasse ℤ).Adj x y ↔
      (x.2 = y.2 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1)) ∨
        (x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) := by
  simp only [boxProd_adj, hasse_adj, Order.covBy_iff_add_one_eq]
  tauto

theorem mem_edgeBoundary {p : (ℤ × ℤ) × (ℤ × ℤ)} :
    p ∈ edgeBoundary Λ A ↔ p.1 ∈ A ∧ p.2 ∈ Λ \ A ∧ (hasse ℤ □ hasse ℤ).Adj p.1 p.2 :=
  mem_interedges_iff _

theorem mem_supports_iff : X ∈ supports Λ R ↔ X ⊆ Λ ∧ X.Nonempty ∧ domainEDiam Λ X ≤ R := by
  rw [supports, Finset.mem_filter, Finset.mem_powerset]

/-- The ambient distance on `ℤ × ℤ` is the sup-distance of the coordinates. -/
theorem dist_eq_max_abs (x y : ℤ × ℤ) :
    dist x y = ((max |x.1 - y.1| |x.2 - y.2| : ℤ) : ℝ) := by
  rw [Prod.dist_eq, Int.dist_eq, Int.dist_eq]
  push_cast
  rfl

theorem dist_le_natCast_iff {k : ℕ} :
    dist x y ≤ k ↔ |x.1 - y.1| ≤ k ∧ |x.2 - y.2| ≤ k := by
  rw [dist_eq_max_abs, ← Int.cast_natCast (R := ℝ), Int.cast_le, max_le_iff]

/-- Adjacent sites of the square lattice are at sup-distance one. -/
theorem dist_eq_one_of_adj (h : (hasse ℤ □ hasse ℤ).Adj x y) : dist x y = 1 := by
  rw [squareLattice_adj_iff] at h
  rw [dist_eq_max_abs, Int.cast_eq_one]
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> simp [h1, ← h2]

/-- A walk of length `k` in an induced subgraph of the square lattice moves the sup-distance by
at most `k`. -/
theorem dist_le_length_of_walk {s : Set (ℤ × ℤ)} {u v : s}
    (p : ((hasse ℤ □ hasse ℤ).induce s).Walk u v) : dist (u : ℤ × ℤ) v ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Nat.cast_add_one, add_comm]
    exact (dist_triangle _ _ _).trans
      (add_le_add (dist_eq_one_of_adj (induce_adj.1 h)).le ih)

/-- A walk of length at most `n` from `u` to `v` exists iff the extended graph distance from
`u` to `v` is at most `n`; between components both sides fail.  TNLean
`exists_walk_length_le_iff_edist_le` (`TNLean/PEPS/AreaLaw/FiniteDomain.lean:131`, commit
`f4c2d204`) for an arbitrary graph. -/
theorem exists_walk_length_le_iff_edist_le {V : Type*} (G : SimpleGraph V) {u v : V} {n : ℕ} :
    (∃ p : G.Walk u v, p.length ≤ n) ↔ G.edist u v ≤ n := by
  constructor
  · rintro ⟨p, hp⟩
    exact p.edist_le.trans (by exact_mod_cast hp)
  · intro h
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) h)
    exact ⟨p, by exact_mod_cast hp ▸ h⟩

theorem dist_le_of_domainEDist_le {k : ℕ} (h : domainEDist Λ x y ≤ k) : dist x y ≤ k := by
  by_cases hxy : x ∈ Λ ∧ y ∈ Λ
  · rw [domainEDist, dif_pos hxy] at h
    obtain ⟨p, hp⟩ := (exists_walk_length_le_iff_edist_le _).2 h
    exact (dist_le_length_of_walk p).trans (by exact_mod_cast hp)
  · rw [domainEDist, dif_neg hxy] at h
    exact absurd h (by simp)

/-- Two sites of an admissible support of range `R` are at sup-distance at most `R`. -/
theorem dist_le_of_mem_supports (hX : X ∈ supports Λ R) (hx : x ∈ X) (hy : y ∈ X) :
    dist x y ≤ R :=
  dist_le_of_domainEDist_le (domainEDiam_le_iff.1 (mem_supports_iff.1 hX).2.2 x hx y hy)

/-- A support of range `R` containing `a` lies in the box `[a - (R, R), a + (R, R)]`. -/
theorem subset_Icc_of_mem_supports (hX : X ∈ supports Λ R) {a : ℤ × ℤ} (ha : a ∈ X) :
    X ⊆ Finset.Icc (a - ((R : ℤ), (R : ℤ))) (a + ((R : ℤ), (R : ℤ))) := by
  intro x hx
  obtain ⟨h1, h2⟩ := dist_le_natCast_iff.1 (dist_le_of_mem_supports hX hx ha)
  rw [abs_le] at h1 h2
  rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  omega

theorem card_Icc_eq_mul (a b : ℤ × ℤ) :
    (Finset.Icc a b).card = (b.1 + 1 - a.1).toNat * (b.2 + 1 - a.2).toNat := by
  rw [Finset.card_Icc_prod, Int.card_Icc, Int.card_Icc]

theorem card_Icc_sub_add (a : ℤ × ℤ) (R : ℕ) :
    (Finset.Icc (a - ((R : ℤ), (R : ℤ))) (a + ((R : ℤ), (R : ℤ)))).card = (2 * R + 1) ^ 2 := by
  rw [card_Icc_eq_mul, sq]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  congr 1 <;> omega

/-- A support of range `R` has at most `(2R + 1)²` sites. -/
theorem card_le_of_mem_supports (hX : X ∈ supports Λ R) : X.card ≤ (2 * R + 1) ^ 2 := by
  obtain ⟨a, ha⟩ := (mem_supports_iff.1 hX).2.1
  exact (Finset.card_le_card (subset_Icc_of_mem_supports hX ha)).trans
    (card_Icc_sub_add a R).le

end Lattice

/-! ## Extension by the identity and pure states on regions -/

section Regions

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  {𝕜 : Type*} [RCLike 𝕜] {S T : Finset σ}

section Extend

variable [∀ i, DecidableEq (loc i)]

omit [∀ i, Fintype (loc i)] in
/-- Extension by the identity commutes with finite sums. -/
theorem extendId_sum {κ : Type*} (h : S ⊆ T) (s : Finset κ)
    (f : κ → Matrix (Reg loc S) (Reg loc S) 𝕜) :
    extendId h (∑ k ∈ s, f k) = ∑ k ∈ s, extendId h (f k) :=
  map_sum (AddMonoidHom.mk' (extendId h) (extendId_add h)) f s

open scoped Matrix.Norms.L2Operator in
/-- Extension by the identity does not increase the L2 operator norm. -/
theorem l2_opNorm_extendId_le (h : S ⊆ T) (A : Matrix (Reg loc S) (Reg loc S) 𝕜) :
    ‖extendId h A‖ ≤ ‖A‖ := by
  rw [extendId_eq_kronecker, l2_opNorm_submatrix]
  exact l2_opNorm_kronecker_one_le A

end Extend

section CoeffMatrix

omit [∀ i, Fintype (loc i)]

variable {α : Type*}

/-- The coefficient matrix of a vector `v` on `T` across the cut `S | T \ S`: the entry at
`(x, z)` is the amplitude of `v` on the glued configuration `x ∪ z`. -/
def coeffMatrix (S : Finset σ) (v : Reg loc T → α) : Matrix (Reg loc S) (Reg loc (T \ S)) α :=
  of fun x z => v (glue x z)

@[simp] theorem coeffMatrix_apply (v : Reg loc T → α) (x : Reg loc S) (z : Reg loc (T \ S)) :
    coeffMatrix S v x z = v (glue x z) := rfl

end CoeffMatrix

/-- The reduced matrix of `|ψ⟩⟨ψ|` on `S ⊆ T` is `M Mᴴ` for the coefficient matrix `M` of `ψ`
across the cut `S | T \ S`. -/
theorem ptrace_vecMulVec_star (h : S ⊆ T) (ψ : Reg loc T → 𝕜) :
    ptrace h (vecMulVec ψ (star ψ)) = rhoA (coeffMatrix S ψ) := by
  ext x y
  simp [ptrace, rhoA, mul_apply, vecMulVec_apply]

variable [∀ i, DecidableEq (loc i)]

/-- The entropy of a region `S ⊆ T` of a pure state on `T` is the entanglement entropy of its
coefficient matrix across the cut `S | T \ S`. -/
theorem regionEntropy_pureState (h : S ⊆ T) (ψ : Reg loc T → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (pureState ψ hψ).regionEntropy h =
      EE (coeffMatrix S ψ) := by
  rw [SubState.regionEntropy_def, SubState.entropy, vonNeumann_eq_H, EE]
  exact H_eigenvalues_congr _ _ (ptrace_vecMulVec_star h ψ)

end Regions

/-! ## Theorem 1.1 under its v1 name -/

/-- **Theorem 1.1** under its v1 name; the proof is `AreaLaw.areaLaw`. -/
theorem area_law {𝕜 : Type*} [RCLike 𝕜] (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) : AreaLaw 𝕜 q R J Δ :=
  AreaLaw.areaLaw 𝕜 q R J Δ hq hJ hΔ

end OpenAI
