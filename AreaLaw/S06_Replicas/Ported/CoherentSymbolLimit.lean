/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLaw.S06_Replicas.Ported.CoherentSymbol
import AreaLawForMathlib.Analysis.Matrix.MatrixIntertwine

/-!
# Limits of coherent symbols

Coherent symbols are closed under limits, and `‖Π M Π‖` is bounded by the bilinear form of `M` on
symmetric vectors.

Reference: OpenAI, *A two-dimensional area law from a global spectral gap*, Lemma 6.4,
`05-replicas.tex`, lines 693–708 and 813–836.

Ported from `LionSR/QICLean`,
`QICLean/Representation/CoherentSymbolLimit.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/

open Matrix PermutationRepresentation Filter
open scoped Matrix.Norms.L2Operator

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

/-- `‖Π M Π‖ ≤ c` if `|⟨u, M z⟩| ≤ c ‖u‖ ‖z‖` for symmetric `u, z`. -/
theorem l2_opNorm_symProj_mul_mul_symProj_le {M : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ u z, u ∈ invariantSubspace (copyPerm Ω k) → z ∈ invariantSubspace (copyPerm Ω k) →
      ‖star u ⬝ᵥ (M *ᵥ z)‖ ≤
        c * ‖(EuclideanSpace.equiv _ ℂ).symm u‖ * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) :
    ‖symProj (copyPerm Ω k) * M * symProj (copyPerm Ω k)‖ ≤ c := by
  set P := symProj (copyPerm Ω k)
  have hPv : ∀ v, ‖(EuclideanSpace.equiv _ ℂ).symm (P *ᵥ v)‖ ≤
      ‖(EuclideanSpace.equiv _ ℂ).symm v‖ := fun v => by
    refine le_trans (by simpa using P.l2_opNorm_mulVec ((EuclideanSpace.equiv _ ℂ).symm v)) ?_
    exact mul_le_of_le_one_left (norm_nonneg _) l2_opNorm_symProj_le
  refine l2_opNorm_le_of_forall hc fun v => ?_
  have hPP : P * P = P := symProj_mul_symProj
  have hwdef : (P * M * P) *ᵥ v = P *ᵥ (M *ᵥ (P *ᵥ v)) := by
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  set w := (P * M * P) *ᵥ v
  have hw : P *ᵥ w = w := by rw [hwdef, mulVec_mulVec, hPP]
  have key : ∀ y, star w ⬝ᵥ (P *ᵥ y) = star w ⬝ᵥ y := fun y => by
    have h1 : star (P *ᵥ w) = star w ᵥ* Pᴴ := star_mulVec P w
    rw [(isHermitian_symProj (Ω := Ω) (k := k)).eq, hw] at h1
    rw [dotProduct_mulVec, ← h1]
  have hww : star w ⬝ᵥ w = star w ⬝ᵥ (M *ᵥ (P *ᵥ v)) := (congrArg _ hwdef).trans (key _)
  have hbd : ‖star w ⬝ᵥ w‖ ≤ c * ‖(EuclideanSpace.equiv _ ℂ).symm w‖ *
      ‖(EuclideanSpace.equiv _ ℂ).symm v‖ := by
    rw [hww]
    refine (h w (P *ᵥ v) (hw ▸ symProj_mulVec_mem _ w) (symProj_mulVec_mem _ v)).trans ?_
    gcongr
    exact hPv v
  have hsq : ‖(EuclideanSpace.equiv _ ℂ).symm w‖ ^ 2 ≤
      c * ‖(EuclideanSpace.equiv _ ℂ).symm w‖ * ‖(EuclideanSpace.equiv _ ℂ).symm v‖ := by
    rw [← re_star_dotProduct_self_eq_norm_sq]
    exact (RCLike.re_le_norm _).trans hbd
  rcases (norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm w)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith [norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm v)]

variable {X : ∀ k, Matrix (Fin k → Ω) (Fin k → Ω) ℂ} {f : (Ω → ℂ) → ℂ}

/-- Coherent symbols are closed under limits. -/
theorem HasCoherentSymbol.of_approx (hc : ∀ k, Commute (symProj (copyPerm Ω k)) (X k))
    (hb : ∃ M, ∀ k, ‖X k * symProj (copyPerm Ω k)‖ ≤ M)
    (ha : ∀ ε > 0, ∃ (X' : ∀ k, Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (f' : (Ω → ℂ) → ℂ),
      HasCoherentSymbol X' f' ∧ (∀ θ ∈ unitSphere, ‖f θ - f' θ‖ ≤ ε) ∧
        ∀ᶠ k in atTop, ‖(X k - X' k) * symProj (copyPerm Ω k)‖ ≤ ε) :
    HasCoherentSymbol X f where
  commute := hc
  bounded := hb
  continuousOn := by
    have hch : ∀ n : ℕ, ∃ g : (Ω → ℂ) → ℂ, ContinuousOn g unitSphere ∧
        ∀ θ ∈ unitSphere, ‖f θ - g θ‖ ≤ 1 / (n + 1) := fun n => by
      obtain ⟨X', f', hX', hf', -⟩ := ha (1 / (n + 1)) (by positivity)
      exact ⟨f', hX'.continuousOn, hf'⟩
    choose g hg hfg using hch
    refine TendstoUniformlyOn.continuousOn (F := g) (p := atTop) ?_
      (Eventually.of_forall hg).frequently
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn θ hθ
    rw [dist_eq_norm]
    exact (hfg n θ hθ).trans_lt (lt_of_le_of_lt (by gcongr) hN)
  approx ε hε := by
    obtain ⟨X', f', hX', hf', hev⟩ := ha (ε / 2) (by positivity)
    obtain ⟨Y, ψ, hY, hψ, hev'⟩ := hX'.approx (ε / 2) (by positivity)
    refine ⟨Y, ψ, hY, fun θ hθ => ?_, ?_⟩
    · exact (norm_sub_le_norm_sub_add_norm_sub _ (f' θ) _).trans
        ((add_le_add (hf' θ hθ) (hψ θ hθ)).trans_eq (add_halves ε))
    · filter_upwards [hev, hev'] with k h1 h2
      rw [← sub_add_sub_cancel (X k) (X' k) (Y k), Matrix.add_mul]
      exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (add_halves ε))

end TensorPower
