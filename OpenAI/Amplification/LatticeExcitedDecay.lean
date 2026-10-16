/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/LatticeExcitedDecay.lean` (Apache 2.0). Namespace
`TNLean.PEPS.AreaLaw` renamed to `OpenAI`. Adapted to the encodings of
`OpenAI.LatticeConstraints`: TNLean's bundled `LocalHamiltonian Λ q R J` is an interaction `Φ`
with `OpenAI.IsAdmissible Λ R J Φ`, its operator `hamiltonian Λ Φ` and its term `h.term X`
being `extendId _ (Φ X)`; `AdmissibleSupport Λ R` is `supports Λ R`; `Configuration Λ q` is
`Reg (Qudits q) Λ` and `StateSpace Λ q` is `EuclideanSpace ℂ (Reg (Qudits q) Λ)`;
`IsGappedGroundState Λ q H E₀ Ω Δ` is `‖Ω‖ = 1`, `H *ᵥ ofLp Ω = E₀ • ofLp Ω` and
`OpenAI.HasGlobalGap H (ofLp Ω) E₀ Δ`, taken as three hypotheses. The source's unused
instance argument `[NeZero q]` is dropped.
-/
import OpenAI.LatticeConstraints
import OpenAI.PoissonContractionDecay

/-!
# Excited-state decay for the exact lattice constraints

The fresh exact positive constraints of a finite induced-domain Hamiltonian
annihilate its original ground vector. Their sum has gap `Δ / c_*`, with
`c_*` the normalization of the positive replacement. Chronological products of their
complementary square roots therefore suppress the component orthogonal to
that ground vector in squared-norm expectation, with any finite spectator.
The expectation uses the concrete fixed-time Poisson-word probability law.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `09-amplification.tex`, lines 237–253,
  `eq:amplification-excited-decay`, at revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  The exact positive replacement is `03-quasilocal.tex`, lines 220–246,
  Proposition 4.3. Independently formalized from the manuscript;
  no upstream Lean text is reused.
-/

noncomputable section

open Matrix MeasureTheory SpectralFilter Arealaw
open scoped Kronecker NNReal MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace OpenAI

/-- The literal exact lattice constraint product has an integrable squared
excited-component norm and the original full-gap exponential decay rate,
including arbitrary entangled finite spectators.
Source: area law, `09-amplification.tex`, lines 237–253,
`eq:amplification-excited-decay`. -/
theorem latticeConstraintWord_excitedProjection_decay
    {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ} (_hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {q : ℕ} (Λ : Finset (ℤ × ℤ))
    (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ)
    (hΦ : IsAdmissible Λ R J Φ)
    (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩ : ‖Ω‖ = 1)
    (heig : hamiltonian Λ Φ *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    (hgap : HasGlobalGap (hamiltonian Λ Φ) (WithLp.ofLp Ω) E₀ Δ)
    {Aux : Type*} [Fintype Aux] [DecidableEq Aux]
    (ζ : EuclideanSpace ℂ (Reg (Qudits q) Λ × Aux)) (t : ℝ≥0) :
    let cs := positiveNormalization p (Δ / 2) J
    let k := fun i : supports Λ R =>
      positiveConstraint cs (centeredFilter p (Δ / 2) (hamiltonian Λ Φ) Ω
        (extendId (subset_of_mem_supports i.2) (Φ i)))
    let ξ := toEuclideanLin
      ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
        (1 : Matrix Aux Aux ℂ)) ζ
    Integrable (poissonContractionWordEnergy k ξ)
        (PoissonWord.measure (supports Λ R) t) ∧
      (∫ w, poissonContractionWordEnergy k ξ w
        ∂PoissonWord.measure (supports Λ R) t) ≤
        Real.exp (-(Δ / cs) * (t : ℝ)) * ‖ξ‖ ^ 2 := by
  classical
  obtain ⟨hk, hsum, hgapk⟩ := SpectralFilter.positive_replacement (E₀ := E₀) (J := J) hp hΔ
    hΩ heig (Matrix.le_iff.mp hgap)
    (fun X : supports Λ R => extendId (subset_of_mem_supports X.2) (Φ X))
    (fun X => hΦ.isHermitian_extendId X) (fun X => hΦ.norm_extendId_le X)
    hΦ.hamiltonian_eq_sum_supports.symm
  exact Matrix.poissonContractionWord_excitedProjection_decay _
    (fun i => (hk i).2.1) hΩ
    (fun i => WithLp.ofLp_injective 2 (hk i).2.2)
    (hgapk.trans hsum) ζ t

end OpenAI
