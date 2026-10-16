import Arealaw.TraceNorm
import OpenAI.Bridges
import OpenAI.CutTransport
import OpenAI.EigenbasisTails
import OpenAI.Embedding

/-!
# Marginal moment and tail bounds on a region

Lemma 3.1 of [OAI265] on a finite tensor product `⊗_{j ∈ U} 𝕜^{loc j}`: for a gapped
Hamiltonian `H = ∑ᵢ hᵢ` with terms supported on regions `Dᵢ ⊆ U` and a cut `B ⊆ U`, the
surprisal `K = -log pⱼ` of the marginal `ρ` of the ground vector on `B` has a moment
generating function controlled by `S(ρ)` and `𝓑 = 1 + ∑_{i crossing} log² (e dᵢ)`, and
exponential tails around `S(ρ)`.

The statement `OpenAI.MarginalTails` follows from the bipartite bounds
`OpenAI.log_surprisalMoment_eigenvalues_le` and `OpenAI.surprisalTail_eigenvalues_le`.  The
operators and the ground vector are embedded into `ℂ` and reindexed along the cut
`Arealaw.glueEquiv : Reg loc B × Reg loc (U \ B) ≃ Reg loc U`; there a term not meeting both
sides of the cut is one-sided and a crossing term supported on `Dᵢ` is a sum of at most `dᵢ²`
products.

## Main statements

* `OpenAI.marginal_tails`: **Lemma 3.1** of [OAI265], eqs. (3.1) and (3.2).

## Implementation notes

The bipartite bounds are proved over `ℂ`, since they rest on complex interpolation; the
statement over a general `RCLike 𝕜` is transferred along `OpenAI.toComplex`, which preserves
operator norms, the gap inequality and the spectrum of the marginal.

The sums of the statement run over the positive eigenvalues `pⱼ > 0`, those of
`OpenAI.surprisalMoment` and `OpenAI.surprisalTail` over all eigenvalues; a zero eigenvalue
contributes `0` to both.

The reindexing along the cut follows the cut transport of QICLean,
`QICLean/Entropy/SupportedMarginalTails.lean` at commit `32a5a1a8` (Apache 2.0).

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.1, Lemma 3.1.
-/

namespace OpenAI

open Arealaw Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Product decompositions -/

section ProductDecomposition

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A product decomposition with factor bound `c` is one with any larger bound. -/
theorem HasProductDecomposition.mono {X : Matrix (α × β) (α × β) 𝕜} {c c' : ℝ} {N : ℕ}
    (hX : HasProductDecomposition X c N) (hc : c ≤ c') : HasProductDecomposition X c' N := by
  obtain ⟨M, a, b, hM, hab, hbd⟩ := hX
  exact ⟨M, a, b, hM, hab, fun k => (hbd k).trans hc⟩

end ProductDecomposition

/-! ## Surprisal sums over the positive weights -/

section Surprisal

variable {ι : Type*} [Fintype ι] {p : ι → ℝ}

/-- For nonnegative weights, the moment generating function of the surprisal may be summed over
the positive weights only. -/
theorem sum_filter_pos_mul_exp_eq_surprisalMoment (hp : ∀ j, 0 ≤ p j) (u : ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), p j * Real.exp (-u * Real.log (p j)) =
      surprisalMoment p u := by
  rw [Finset.sum_filter, surprisalMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases (hp j).lt_or_eq with hj | hj
  · rw [if_pos hj, neg_mul, mul_neg]
  · simp [← hj]

/-- For nonnegative weights, the tail probability of the surprisal may be summed over the
positive weights only. -/
theorem sum_filter_pos_eq_surprisalTail (hp : ∀ j, 0 ≤ p j) (S w : ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j => 0 < p j ∧ w < |-Real.log (p j) - S|), p j =
      surprisalTail p S w := by
  rw [Finset.sum_filter, surprisalTail]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases (hp j).lt_or_eq with hj | hj
  · simp [hj]
  · simp [← hj]

variable [DecidableEq ι] {A : Matrix ι ι 𝕜}

/-- The moment generating function of the surprisal of the spectrum is unchanged by the
embedding into `ℂ`. -/
theorem surprisalMoment_eigenvalues_map_toComplex (hA : A.IsHermitian) (u : ℝ) :
    surprisalMoment (isHermitian_map_toComplex hA).eigenvalues u =
      surprisalMoment hA.eigenvalues u :=
  sum_eq_of_multiset_map_eq (fun x => x * Real.exp (u * -Real.log x))
    (eigenvalues_multiset_map_toComplex hA)

/-- The tail probability of the surprisal of the spectrum is unchanged by the embedding into
`ℂ`. -/
theorem surprisalTail_eigenvalues_map_toComplex (hA : A.IsHermitian) (S w : ℝ) :
    surprisalTail (isHermitian_map_toComplex hA).eigenvalues S w =
      surprisalTail hA.eigenvalues S w :=
  sum_eq_of_multiset_map_eq (fun x => if w < |-Real.log x - S| then x else 0)
    (eigenvalues_multiset_map_toComplex hA)

end Surprisal

/-! ## Reindexing a gapped ground state -/

section Reindex

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The global gap is invariant under a relabelling of the basis. -/
theorem hasGlobalGap_submatrix_equiv (e : m ≃ n) (H : Matrix n n 𝕜) (Ω : n → 𝕜) (E₀ Δ : ℝ) :
    HasGlobalGap (H.submatrix e e) (Ω ∘ e) E₀ Δ ↔ HasGlobalGap H Ω E₀ Δ := by
  rw [HasGlobalGap, HasGlobalGap, Matrix.le_iff, Matrix.le_iff,
    ← posSemidef_submatrix_equiv e]
  refine Eq.to_iff (congrArg _ ?_)
  ext a b
  simp [Matrix.sub_apply, Matrix.smul_apply, one_apply, vecMulVec_apply, e.injective.eq_iff]

end Reindex

/-! ## Lemma 3.1 -/

/-- **Lemma 3.1** [OAI265, §3.1, eqs. (3.1) and (3.2)]. -/
theorem marginal_tails {𝕜 : Type*} [RCLike 𝕜] {σ : Type*} [DecidableEq σ]
    {loc : σ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] :
    MarginalTails σ loc 𝕜 := by
  intro U ι _ D hD h c₀ g₀ E₀ Ψ hΨ hsupp hherm hc₀ hnorm hg₀ heig hgap B hB ρ p 𝓑
  set e := glueEquiv (loc := loc) hB
  let ΨC : Reg loc U → ℂ := fun x => toComplex 𝕜 (Ψ x)
  let Ψ' : Reg loc B × Reg loc (U \ B) → ℂ := ΨC ∘ e
  let h' : ι → Matrix (Reg loc B × Reg loc (U \ B)) (Reg loc B × Reg loc (U \ B)) ℂ :=
    fun i => ((h i).map (toComplex 𝕜)).submatrix e e
  let Cr := Finset.univ.filter fun i => (D i ∩ B).Nonempty ∧ (D i \ B).Nonempty
  let dim : ι → ℕ := fun i => Fintype.card (Reg loc (D i))
  have hρ : ρ.M.IsHermitian := ρ.psd.isHermitian
  have hsum : ∑ i, h' i = ((∑ i, h i).map (toComplex 𝕜)).submatrix e e := by
    rw [map_toComplex_sum, submatrix_sum]
  have hΨ' : star Ψ' ⬝ᵥ Ψ' = 1 := by
    rw [← star_dotProduct_comp_toComplex_eq_one hΨ]
    exact Equiv.sum_comp e (fun x => star (ΨC x) * ΨC x)
  have heig' : (∑ i, h' i) *ᵥ Ψ' = (E₀ : ℂ) • Ψ' := by
    have h1 := (mulVec_map_toComplex_eq_smul_iff (∑ i, h i) Ψ (E₀ : 𝕜)).2 heig
    rw [toComplex_ofReal] at h1
    rw [hsum, submatrix_mulVec_equiv]
    simp only [Ψ', Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
    rw [h1]
    rfl
  have hgap' : HasGlobalGap (∑ i, h' i) Ψ' E₀ g₀ := by
    rw [hsum, hasGlobalGap_submatrix_equiv, hasGlobalGap_map_toComplex_iff]
    exact hgap
  obtain ⟨hn, heu, hpsd⟩ :=
    (normalized_eigen_hasGlobalGap_iff_euclidean _ _ _ _).1 ⟨hΨ', heig', hgap'⟩
  have hρdef : traceRight (vecMulVec Ψ' (star Ψ')) = ρ.M.map (toComplex 𝕜) := by
    change _ = (ptrace hB (vecMulVec Ψ (star Ψ))).map (toComplex 𝕜)
    rw [← ptrace_map_toComplex, ← vecMulVec_comp_toComplex, ← star_comp_toComplex,
      ptrace_eq_traceRight_submatrix_glueEquiv]
    rfl
  obtain ⟨x₀⟩ : Nonempty (Reg loc U) := by
    by_contra hU
    rw [not_nonempty_iff] at hU
    simp [dotProduct, Finset.univ_eq_empty] at hΨ
  have hherm' : ∀ i, (h' i).IsHermitian := fun i =>
    (isHermitian_map_toComplex (hherm i)).submatrix e
  have hnorm' : ∀ i, ‖h' i‖ ≤ c₀ := fun i => by
    simp only [h', l2_opNorm_submatrix, norm_map_toComplex]
    exact hnorm i
  have hsupp' : ∀ i, IsSupportedOn (hD i) ((h i).map (toComplex 𝕜)) := fun i => by
    obtain ⟨Y, hY⟩ := hsupp i
    exact ⟨Y.map (toComplex 𝕜), by rw [extendId_map_toComplex, hY]⟩
  have hone : ∀ i ∉ Cr, IsOneSided (h' i) := fun i hi => by
    refine (hsupp' i).isOneSided_submatrix_glueEquiv hB (hD i) ?_
    simp only [Cr, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
    by_cases hDB : (D i ∩ B).Nonempty
    · left
      have := hi hDB
      rwa [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at this
    · right
      rwa [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hDB
  have hdim : ∀ i ∈ Cr, 1 ≤ dim i := fun i _ =>
    Fintype.card_pos_iff.2 ⟨restr (hD i) x₀⟩
  have hcross : ∀ i ∈ Cr, HasProductDecomposition (h' i) c₀ (dim i ^ 2) := fun i _ =>
    ((hsupp' i).hasProductDecomposition_submatrix_glueEquiv hB (hD i)).mono
      ((norm_map_toComplex _).trans_le (hnorm i))
  have hp : ∀ j, 0 ≤ p j := ρ.psd.eigenvalues_nonneg
  have hS : ρ.entropy = vonNeumann (isHermitian_map_toComplex hρ) :=
    (vonNeumann_map_toComplex hρ).symm
  have hr : (32 * Real.sqrt ((1 + c₀ / g₀) * 𝓑))⁻¹ = tailRadius (c₀ / g₀) (cutLogBudget Cr dim) :=
    (one_div _).symm
  refine ⟨fun u hu => ?_, fun w _ => ?_⟩
  · rw [sum_filter_pos_mul_exp_eq_surprisalMoment hp,
      ← surprisalMoment_eigenvalues_map_toComplex hρ, hS]
    exact log_surprisalMoment_eigenvalues_le hherm' hc₀ hnorm' hone hdim hcross hn hg₀ heu hpsd
      hρdef (isHermitian_map_toComplex hρ) (hr ▸ hu)
  · rw [sum_filter_pos_eq_surprisalTail hp, ← surprisalTail_eigenvalues_map_toComplex hρ, hS]
    exact surprisalTail_eigenvalues_le hherm' hc₀ hnorm' hone hdim hcross hn hg₀ heu hpsd
      hρdef (isHermitian_map_toComplex hρ) w

end OpenAI
