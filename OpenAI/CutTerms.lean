import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Terms across a cut

The two shapes a term of a Hamiltonian on a bipartite space `𝕜^α ⊗ 𝕜^β` can take in Lemma 3.1
of [OAI265]: a term acting on one tensor factor only, and a crossing term, a sum of at most `N`
products `c_a ⊗ d_a` with `‖c_a‖ ‖d_a‖ ≤ c₀`.  A term supported on sites of total dimension
`d` admits such a decomposition with `N = d²`, through matrix units on the part of its support
on the first side.  Also the surprisal parameter `𝓑 = 1 + ∑_{i crossing} log² (e dᵢ)` and the
bound `log (2N) ≤ 2 log (e d)` that turns `N ≤ d²` into a factor of `𝓑`.

## Main definitions

* `OpenAI.IsOneSided`: `X = A ⊗ 1` or `X = 1 ⊗ A`.
* `OpenAI.HasProductDecomposition`: `X = ∑_{a < M} c_a ⊗ d_a`, `M ≤ N`, `‖c_a‖ ‖d_a‖ ≤ c₀`.
* `OpenAI.cutLogBudget`: `𝓑 = 1 + ∑_{i ∈ Cr} log² (e dᵢ)`.

## Implementation notes

Ported from QICLean, `QICLean/Entropy/GapSurprisal.lean` at commit `32a5a1a8` (Apache 2.0):
`IsOneSided`, `HasProductDecomposition`, `log_two_mul_le_two_mul_log`, `cutLogBudget`,
`one_le_cutLogBudget`, `log_sq_le_cutLogBudget`.  The definitions are stated here over any
`RCLike` field instead of `ℂ`; the norm is Mathlib's L2 operator norm.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.1, Lemma 3.1.
-/

namespace OpenAI

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

/-- An operator on `𝕜^α ⊗ 𝕜^β` acts on a single tensor factor: it is `A ⊗ 1` or `1 ⊗ A`. -/
def IsOneSided (X : Matrix (α × β) (α × β) 𝕜) : Prop :=
  (∃ A : Matrix α α 𝕜, X = A ⊗ₖ (1 : Matrix β β 𝕜)) ∨
    ∃ A : Matrix β β 𝕜, X = (1 : Matrix α α 𝕜) ⊗ₖ A

/-- An operator on `𝕜^α ⊗ 𝕜^β` is a sum of at most `N` products `c_a ⊗ d_a` with
`‖c_a‖ ‖d_a‖ ≤ c₀`. -/
def HasProductDecomposition (X : Matrix (α × β) (α × β) 𝕜) (c₀ : ℝ) (N : ℕ) : Prop :=
  ∃ (M : ℕ) (c : Fin M → Matrix α α 𝕜) (d : Fin M → Matrix β β 𝕜),
    M ≤ N ∧ X = ∑ a, c a ⊗ₖ d a ∧ ∀ a, ‖c a‖ * ‖d a‖ ≤ c₀

/-- `log (2N) ≤ 2 log (e d)` when `N ≤ d²` and `d ≥ 1`. -/
theorem log_two_mul_le_two_mul_log {N d : ℕ} (hN : N ≤ d ^ 2) (hd : 1 ≤ d) :
    Real.log (2 * N) ≤ 2 * Real.log (Real.exp 1 * d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.log_mul (Real.exp_pos 1).ne' hd0.ne', Real.log_exp]
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp only [Nat.cast_zero, mul_zero, Real.log_zero]
    have := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
    linarith
  have h1 : Real.log (2 * N) ≤ Real.log (2 * d ^ 2) :=
    Real.log_le_log (by positivity) (by gcongr; exact_mod_cast hN)
  have h3 : Real.log (2 * (d : ℝ) ^ 2) = Real.log 2 + 2 * Real.log d := by
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow]; push_cast; ring
  have h2 : Real.log 2 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  linarith

section Budget

variable {ι : Type*}

/-- The surprisal parameter `𝓑 = 1 + ∑_{i ∈ Cr} log² (e dᵢ)` of Lemma 3.1, for the crossing
terms `Cr` of dimensions `dᵢ`. -/
noncomputable def cutLogBudget (Cr : Finset ι) (dim : ι → ℕ) : ℝ :=
  1 + ∑ i ∈ Cr, Real.log (Real.exp 1 * dim i) ^ 2

theorem one_le_cutLogBudget (Cr : Finset ι) (dim : ι → ℕ) : 1 ≤ cutLogBudget Cr dim := by
  unfold cutLogBudget
  linarith [Finset.sum_nonneg fun i (_ : i ∈ Cr) ↦ sq_nonneg (Real.log (Real.exp 1 * dim i))]

theorem log_sq_le_cutLogBudget {Cr : Finset ι} {dim : ι → ℕ} {i : ι} (hi : i ∈ Cr) :
    Real.log (Real.exp 1 * dim i) ^ 2 ≤ cutLogBudget Cr dim := by
  unfold cutLogBudget
  have := Finset.single_le_sum (f := fun i ↦ Real.log (Real.exp 1 * dim i) ^ 2)
    (fun i _ ↦ sq_nonneg _) hi
  linarith

end Budget

end OpenAI
