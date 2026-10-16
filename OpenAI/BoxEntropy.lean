import OpenAI.Rectangles

/-!
# The safe-box entropy

`F_box(r)` is the supremum of `S_Ω(A ∩ Q)` over every safety parameter `D₀ > 2R + 10`, every
admissible Hamiltonian of range `R` and term norm `J` on a finite domain `Λ ⊂ ℤ²` with a
normalized ground vector `Ω` and global gap `Δ`, every cut `A ⊆ Λ`, and every rectangle `Q` of
size at most `r` that is safe for `A` at `D₀`.  A region of `k` sites of local dimension `q` has
entropy at most `k log q`, and `A ∩ Q` has at most `size(Q)²` sites, so `F_box(r) ≤ r² log q`:
the supremum is finite.  It is nonnegative and nondecreasing in `r`, and every safe-box entropy
is at most it.

## Main definitions

* `OpenAI.boxEntropyValues`: the set of safe-box entropies at size at most `r`.
* `OpenAI.boxEntropy`: its supremum, the function `F_box` of Proposition 3.3.

## Main statements

* `Arealaw.MState.regionEntropy_le_card_mul_log`: a region of `k` sites of local dimension `d`
  has entropy at most `k log d`.
* `OpenAI.boxEntropy_le_sq_mul_log`: `F_box(r) ≤ r² log q`.
* `OpenAI.regionEntropy_le_boxEntropy`: every safe-box entropy is at most `F_box(r)`.
* `OpenAI.boxEntropy_mono`: `F_box` is nondecreasing.

## Implementation notes

The paper fixes `D₀ > 2R + 10` once and defines `F_box` at that `D₀`.  Here the supremum runs
over every such `D₀` as well.  Proposition 3.3 asserts constants uniform in `D₀`, and the
supremum over `D₀` turns that uniformity into a bound on one function.  With `D₀` real there is
no least admissible safety parameter, so the estimate at one `D₀` does not bound the others
through monotonicity in `D₀`, which is how TNLean, with `D₀ : ℕ`, reaches every `D₀` from
`D₀ = 2R + 11`.

Adapted from TNLean (`LionSR/TNLean`, commit `f4c2d204`, Apache 2.0),
`TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean` (`boxEntropyValues`, `boxEntropy` and their
first lemmas).  TNLean's `LocalHamiltonian` structure, `IsGappedGroundState`, region type and
`regionalEntropy` become `IsAdmissible`, the eigenvector equation with `HasGlobalGap`, cuts
`A ⊆ Λ`, and `Arealaw.SubState.regionEntropy` of `pureState`, over any `RCLike` field.
TNLean's `boxEntropy_antitone` is not ported.

## References

* [OAI265] OpenAI, *A two-dimensional area law from a global spectral gap*, 24 September 2026,
  §3.3, the definition of `F_box` before Proposition 3.3.
-/

namespace Arealaw.MState

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {𝕜 : Type*} [RCLike 𝕜] {U X : Finset σ}

/-- A region of `|X|` sites, each of dimension `d`, has entropy at most `|X| log d`. -/
theorem regionEntropy_le_card_mul_log (ρ : MState (Reg loc U) 𝕜) (h : X ⊆ U) {d : ℕ}
    (hd : ∀ i, Fintype.card (loc i) = d) : ρ.regionEntropy h ≤ X.card * Real.log d := by
  have := (ρ.restrict h).entropy_le_log_card
  rw [card_reg_const hd, Nat.cast_pow, Real.log_pow] at this
  exact this

end Arealaw.MState

namespace OpenAI

open Arealaw Matrix
open scoped MatrixOrder

variable {𝕜 : Type*} [RCLike 𝕜] {q R : ℕ} {J Δ : ℝ}

variable (𝕜 q R J Δ) in
/-- The safe-box entropies at size at most `r`: the values `S_Ω(A ∩ Q)` for every
`D₀ > 2R + 10`, admissible Hamiltonian with gapped ground vector `Ω`, cut `A ⊆ Λ` and
rectangle `Q` of size at most `r` safe for `A` at `D₀`. -/
def boxEntropyValues (r : ℕ) : Set ℝ :=
  {s | ∃ D₀ : ℝ, 2 * R + 10 < D₀ ∧ ∃ (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜),
    IsAdmissible Λ R J Φ ∧ ∃ (Ω : Reg (Qudits q) Λ → 𝕜) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
    hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω ∧ HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ ∧
    ∃ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (Q : Finset (ℤ × ℤ)), IsIntRect Q ∧ IsSafe D₀ Λ A Q ∧
      boxSize Q ≤ r ∧
        s = (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ)}

variable (𝕜 q R J Δ) in
/-- **The safe-box entropy** `F_box(r)` [OAI265, §3.3]: the supremum of `S_Ω(A ∩ Q)` over
every `D₀ > 2R + 10`, admissible Hamiltonian with gapped ground vector `Ω`, cut `A` and
rectangle `Q` of size at most `r` safe for `A` at `D₀`. -/
noncomputable def boxEntropy (r : ℕ) : ℝ :=
  sSup (boxEntropyValues 𝕜 q R J Δ r)

/-- The safe-box entropies at size at most `r` are at most `r² log q`. -/
theorem le_of_mem_boxEntropyValues {r : ℕ} {s : ℝ} (hs : s ∈ boxEntropyValues 𝕜 q R J Δ r) :
    s ≤ (r : ℝ) ^ 2 * Real.log q := by
  obtain ⟨-, -, Λ, Φ, -, Ω, hΩ, -, -, -, A, hA, Q, -, -, hQ, rfl⟩ := hs
  refine ((pureState Ω hΩ).regionEntropy_le_card_mul_log _ fun _ => Fintype.card_fin q).trans ?_
  have hcard : ((A ∩ Q).card : ℝ) ≤ (r : ℝ) ^ 2 := by
    exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans
      ((card_le_boxSize_sq Q).trans (Nat.pow_le_pow_left hQ 2))
  exact mul_le_mul_of_nonneg_right hcard (Real.log_natCast_nonneg q)

theorem bddAbove_boxEntropyValues (r : ℕ) : BddAbove (boxEntropyValues 𝕜 q R J Δ r) :=
  ⟨_, fun _ hs => le_of_mem_boxEntropyValues hs⟩

theorem nonneg_of_mem_boxEntropyValues {r : ℕ} {s : ℝ}
    (hs : s ∈ boxEntropyValues 𝕜 q R J Δ r) : 0 ≤ s := by
  obtain ⟨-, -, Λ, Φ, -, Ω, hΩ, -, -, -, A, hA, Q, -, -, -, rfl⟩ := hs
  exact SubState.regionEntropy_nonneg _ _

theorem boxEntropy_nonneg (r : ℕ) : 0 ≤ boxEntropy 𝕜 q R J Δ r :=
  Real.sSup_nonneg fun _ hs => nonneg_of_mem_boxEntropyValues hs

/-- `F_box(r) ≤ r² log q`. -/
theorem boxEntropy_le_sq_mul_log (r : ℕ) : boxEntropy 𝕜 q R J Δ r ≤ (r : ℝ) ^ 2 * Real.log q :=
  Real.sSup_le (fun _ hs => le_of_mem_boxEntropyValues hs)
    (mul_nonneg (sq_nonneg _) (Real.log_natCast_nonneg q))

/-- Every safe-box entropy of size at most `r` is at most `F_box(r)`. -/
theorem regionEntropy_le_boxEntropy {D₀ : ℝ} (hD₀ : 2 * R + 10 < D₀) {Λ : Finset (ℤ × ℤ)}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) 𝕜}
    (hΦ : IsAdmissible Λ R J Φ) {Ω : Reg (Qudits q) Λ → 𝕜} (hΩ : star Ω ⬝ᵥ Ω = 1) {E₀ : ℝ}
    (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : 𝕜) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) {Q : Finset (ℤ × ℤ)} (hQ : IsIntRect Q)
    (hs : IsSafe D₀ Λ A Q) {r : ℕ} (hr : boxSize Q ≤ r) :
    (pureState Ω hΩ).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ Q ⊆ Λ) ≤
      boxEntropy 𝕜 q R J Δ r :=
  le_csSup (bddAbove_boxEntropyValues r)
    ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hr, rfl⟩

/-- `F_box` is nondecreasing. -/
theorem boxEntropy_mono : Monotone (boxEntropy 𝕜 q R J Δ) := by
  intro r r' hrr
  refine Real.sSup_le (fun s hs => ?_) (boxEntropy_nonneg r')
  obtain ⟨D₀, hD₀, Λ, Φ, hΦ, Ω, hΩ, E₀, hE, hgap, A, hA, Q, hQ, hs, hQr, rfl⟩ := hs
  exact regionEntropy_le_boxEntropy hD₀ hΦ hΩ hE hgap hA hQ hs (hQr.trans hrr)

end OpenAI
