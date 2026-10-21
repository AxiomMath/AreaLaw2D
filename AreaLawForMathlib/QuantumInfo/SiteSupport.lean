/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.Analysis.Matrix.L2OpNormReindex

/-!
# Concrete support for finite tensor-product matrices

Extends `Mathlib/LinearAlgebra/Matrix/Kronecker.lean`.

Operators on `⊗_v ℂ^{n_v}` acting as the identity outside a set of sites.
-/

open Matrix

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Configurations of a finite tensor product `⊗_v ℂ^{n_v}`. -/
abbrev SiteConfig (n : V → ℕ) := (v : V) → Fin (n v)

/-- An operator is supported on `D` when it acts as the identity outside `D`. -/
def IsSupportedOn (X : Matrix (SiteConfig n) (SiteConfig n) ℂ) (D : Finset V) : Prop :=
  (∀ σ τ : SiteConfig n, (∃ v ∉ D, σ v ≠ τ v) → X σ τ = 0) ∧
    ∀ σ τ σ' τ' : SiteConfig n, (∀ v ∈ D, σ v = σ' v) → (∀ v ∈ D, τ v = τ' v) →
      (∀ v ∉ D, σ v = τ v) → (∀ v ∉ D, σ' v = τ' v) → X σ τ = X σ' τ'

omit [Fintype V] [DecidableEq V] in
/-- Matrix elements of a supported operator depend only on the support and the coincidence
pattern outside it. -/
theorem IsSupportedOn.apply_eq {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} {D : Finset V}
    (hX : IsSupportedOn X D) {σ τ σ' τ' : SiteConfig n} (h1 : ∀ v ∈ D, σ v = σ' v)
    (h2 : ∀ v ∈ D, τ v = τ' v) (h3 : ∀ v ∉ D, (σ v = τ v ↔ σ' v = τ' v)) :
    X σ τ = X σ' τ' := by
  by_cases h : ∃ v ∉ D, σ v ≠ τ v
  · obtain ⟨v, hv, hne⟩ := h
    rw [hX.1 σ τ ⟨v, hv, hne⟩, hX.1 σ' τ' ⟨v, hv, fun h' ↦ hne ((h3 v hv).mpr h')⟩]
  · push Not at h
    exact hX.2 σ τ σ' τ' h1 h2 h fun v hv ↦ (h3 v hv).mp (h v hv)

end Entropy
