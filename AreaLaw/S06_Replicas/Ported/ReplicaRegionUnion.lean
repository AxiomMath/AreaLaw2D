/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import AreaLawForMathlib.QuantumInfo.SiteSupport
/-!
# Regional lifts for the concrete replica-site model

The regional lift `K ↦ K ⊗ 1` on `Entropy.SiteConfig` and the product decomposition of an
operator supported on a disjoint union.

Ported and specialized from LionSR/QICLean commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`,
`QICLean/Entropy/LocalLift.lean` and
`QICLean/Entropy/RegionUnion.lean`.
-/

open Matrix
open scoped Kronecker

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Configurations restricted to a finite region. -/
abbrev RegionConfig (n : V → ℕ) (D : Finset V) := (v : {v // v ∈ D}) → Fin (n v)

/-- Restriction of a full configuration to a region. -/
def restrictConfig (D : Finset V) (σ : SiteConfig n) : RegionConfig n D :=
  fun v => σ v.1

/-- Extension of a regional configuration using a fixed reference configuration off the region. -/
noncomputable def extendConfig (D : Finset V) (σ₀ : SiteConfig n) (x : RegionConfig n D) :
    SiteConfig n :=
  fun v => if h : v ∈ D then x ⟨v, h⟩ else σ₀ v

/-- The regional lift `K ↦ K ⊗ 1` in concrete configuration coordinates. -/
noncomputable def localLift (D : Finset V)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    Matrix (SiteConfig n) (SiteConfig n) ℂ :=
  fun σ τ => if ∀ v ∉ D, σ v = τ v then K (restrictConfig D σ) (restrictConfig D τ) else 0

/-- Matrix elements of a regional lift. -/
theorem localLift_apply (D : Finset V) (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ)
    (σ τ : SiteConfig n) :
    localLift D K σ τ =
      if ∀ v ∉ D, σ v = τ v then K (fun v ↦ σ v) (fun v ↦ τ v) else 0 := by
  rfl

theorem localLift_add (D : Finset V)
    (K K' : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D (K + K') = localLift D K + localLift D K' := by
  ext σ τ
  simp only [localLift_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem localLift_smul (D : Finset V) (c : ℂ)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D (c • K) = c • localLift D K := by
  ext σ τ
  simp only [localLift_apply, Matrix.smul_apply]
  split_ifs <;> simp

/-- In coordinates splitting a region from its complement, `localLift` is `K ⊗ 1`. -/
theorem localLift_eq_reindex_kronecker (D : Finset V)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D K =
      reindex (Equiv.piEquivPiSubtypeProd (· ∈ D) fun v => Fin (n v)).symm
        (Equiv.piEquivPiSubtypeProd (· ∈ D) fun v => Fin (n v)).symm
        (K ⊗ₖ (1 : Matrix ((v : {v // v ∉ D}) → Fin (n v))
          ((v : {v // v ∉ D}) → Fin (n v)) ℂ)) := by
  ext σ τ
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    Equiv.piEquivPiSubtypeProd_apply, localLift_apply, Matrix.one_apply]
  have : (∀ v ∉ D, σ v = τ v) ↔
      (fun x : {x // x ∉ D} => σ x) = fun x : {x // x ∉ D} => τ x :=
    ⟨fun h => funext fun v => h v.1 v.2, fun he v hv => congrFun he ⟨v, hv⟩⟩
  simp only [this]
  split_ifs <;> simp

/-- The concrete regional lift preserves multiplication. -/
theorem localLift_mul (D : Finset V)
    (K K' : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D (K * K') = localLift D K * localLift D K' := by
  rw [localLift_eq_reindex_kronecker, localLift_eq_reindex_kronecker,
    localLift_eq_reindex_kronecker, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

/-- The concrete regional lift preserves the identity. -/
theorem localLift_one (D : Finset V) :
    localLift D (1 : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) = 1 := by
  rw [localLift_eq_reindex_kronecker, one_kronecker_one]
  simp

/-- The concrete regional lift commutes with conjugate transpose. -/
theorem localLift_conjTranspose (D : Finset V)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D Kᴴ = (localLift D K)ᴴ := by
  rw [localLift_eq_reindex_kronecker, localLift_eq_reindex_kronecker]
  simp [conjTranspose_kronecker, conjTranspose_submatrix]

/-- A regional lift is supported on its region. -/
theorem isSupportedOn_localLift (D : Finset V)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    IsSupportedOn (localLift D K) D := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ => if_neg fun h => hne (h v hv), fun σ τ σ' τ' h1 h2 h3 h4 => ?_⟩
  rw [localLift_apply, localLift_apply, if_pos h3, if_pos h4]
  congr 1 <;> funext v
  exacts [h1 v.1 v.2, h2 v.1 v.2]

/-- Every concretely supported operator is a regional lift. -/
theorem IsSupportedOn.exists_localLift {D : Finset V}
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hX : IsSupportedOn X D)
    (σ₀ : SiteConfig n) :
    ∃ K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ, X = localLift D K := by
  classical
  refine ⟨fun x y => X (extendConfig D σ₀ x) (extendConfig D σ₀ y), ?_⟩
  ext σ τ
  change X σ τ = if ∀ v ∉ D, σ v = τ v then
    X (extendConfig D σ₀ (restrictConfig D σ))
      (extendConfig D σ₀ (restrictConfig D τ)) else 0
  split_ifs with h
  · exact hX.2 _ _ _ _ (fun v hv => by simp [extendConfig, restrictConfig, hv])
      (fun v hv => by simp [extendConfig, restrictConfig, hv]) h
      (fun v hv => by simp [extendConfig, hv])
  · push Not at h
    exact hX.1 σ τ h

omit [Fintype V] [DecidableEq V] in
/-- Support is monotone in the region. -/
theorem IsSupportedOn.mono {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} {D D' : Finset V}
    (hX : IsSupportedOn X D) (hDD : D ⊆ D') : IsSupportedOn X D' := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ => hX.1 σ τ ⟨v, fun h => hv (hDD h), hne⟩,
    fun σ τ σ' τ' h1 h2 h3 h4 => hX.apply_eq (fun v hv => h1 v (hDD hv))
      (fun v hv => h2 v (hDD hv)) fun v hv => ?_⟩
  by_cases hv' : v ∈ D'
  · rw [h1 v hv', h2 v hv']
  · exact ⟨fun _ => h4 v hv', fun _ => h3 v hv'⟩

/-- Configurations of a disjoint union are pairs of regional configurations. -/
def regionUnionEquiv {X T : Finset V} (hXT : Disjoint X T) :
    RegionConfig n (X ∪ T) ≃ RegionConfig n X × RegionConfig n T where
  toFun σ := (fun v ↦ σ ⟨v.1, Finset.mem_union_left T v.2⟩,
    fun v ↦ σ ⟨v.1, Finset.mem_union_right X v.2⟩)
  invFun p v := if h : v.1 ∈ X then p.1 ⟨v.1, h⟩ else
    p.2 ⟨v.1, (Finset.mem_union.mp v.2).resolve_left h⟩
  left_inv σ := by
    funext v
    by_cases h : v.1 ∈ X <;> simp [h]
  right_inv p := by
    ext v
    · simp [v.2]
    · simp [Finset.disjoint_right.mp hXT v.2]

omit [Fintype V] in
@[simp] theorem regionUnionEquiv_apply_fst {X T : Finset V} (hXT : Disjoint X T)
    (σ : RegionConfig n (X ∪ T)) (v : {v // v ∈ X}) :
    (regionUnionEquiv hXT σ).1 v = σ ⟨v.1, Finset.mem_union_left T v.2⟩ := by
  rfl

omit [Fintype V] in
@[simp] theorem regionUnionEquiv_apply_snd {X T : Finset V} (hXT : Disjoint X T)
    (σ : RegionConfig n (X ∪ T)) (v : {v // v ∈ T}) :
    (regionUnionEquiv hXT σ).2 v = σ ⟨v.1, Finset.mem_union_right X v.2⟩ := by
  rfl

/-- Regional lifts multiply across a disjoint union. -/
theorem localLift_union_kronecker {X T : Finset V} (hXT : Disjoint X T)
    (A : Matrix (RegionConfig n X) (RegionConfig n X) ℂ)
    (B : Matrix (RegionConfig n T) (RegionConfig n T) ℂ) :
    localLift (X ∪ T) (reindex (regionUnionEquiv hXT).symm (regionUnionEquiv hXT).symm
      (A ⊗ₖ B)) = localLift X A * localLift T B := by
  have hTX : ∀ v ∈ T, v ∉ X := fun v hv hvX ↦ Finset.disjoint_left.mp hXT hvX hv
  have hXT' : ∀ v ∈ X, v ∉ T := fun v hv hvT ↦ Finset.disjoint_left.mp hXT hv hvT
  ext σ τ
  rw [mul_apply, localLift_apply]
  by_cases h : ∀ v ∉ X ∪ T, σ v = τ v
  · rw [if_pos h]
    set ρ : SiteConfig n := fun v ↦ if v ∈ X then τ v else σ v
    rw [Finset.sum_eq_single ρ]
    · rw [localLift_apply, localLift_apply, if_pos, if_pos]
      · simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply]
        congr 1 <;> congr 1 <;> funext v <;> simp [ρ, v.2, hTX]
      · intro v hv
        by_cases hvX : v ∈ X
        · simp [ρ, hvX]
        · simpa [ρ, hvX] using h v (by simp [hv, hvX])
      · exact fun v hv => by simp [ρ, hv]
    · intro ρ' _ hne
      obtain ⟨v, hv⟩ := Function.ne_iff.mp hne
      by_cases hvX : v ∈ X
      · have : ρ' v ≠ τ v := by simpa [ρ, hvX] using hv
        rw [localLift_apply T, if_neg (fun hc ↦ this (hc v (hXT' v hvX))), mul_zero]
      · have : σ v ≠ ρ' v := fun he ↦ hv (by simp [ρ, hvX, he])
        rw [localLift_apply X, if_neg (fun hc ↦ this (hc v hvX)), zero_mul]
    · exact fun hρ => absurd (Finset.mem_univ ρ) hρ
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun ρ _ ↦ ?_).symm
    rw [localLift_apply, localLift_apply]
    split_ifs with h1 h2
    · exact absurd (fun v hv ↦ by
        simp only [Finset.mem_union, not_or] at hv
        exact (h1 v hv.1).trans (h2 v hv.2)) h
    all_goals simp

/-- Concrete regional lifts on disjoint regions commute. -/
theorem localLift_commute_of_disjoint {X T : Finset V}
    (A : Matrix (RegionConfig n X) (RegionConfig n X) ℂ)
    (B : Matrix (RegionConfig n T) (RegionConfig n T) ℂ) (hTX : Disjoint T X) :
    localLift X A * localLift T B = localLift T B * localLift X A := by
  rw [← localLift_union_kronecker hTX.symm, ← localLift_union_kronecker hTX]
  ext σ τ
  rw [localLift_apply, localLift_apply]
  simp only [Finset.union_comm T X]
  split_ifs
  · exact mul_comm _ _
  · rfl

/-- An operator supported on a disjoint union is a finite sum of products of operators
supported on the two regions. -/
theorem IsSupportedOn.exists_sum_mul {M : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    {X T : Finset V} (hXT : Disjoint X T) (hM : IsSupportedOn M (X ∪ T))
    (σ₀ : SiteConfig n) :
    ∃ (N : ℕ) (a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ),
      (∀ i, IsSupportedOn (a i) X) ∧ (∀ i, IsSupportedOn (b i) T) ∧
        M = ∑ i, a i * b i := by
  classical
  obtain ⟨K, rfl⟩ := hM.exists_localLift σ₀
  set e := regionUnionEquiv (n := n) hXT
  set K' := reindex e e K
  set I := (RegionConfig n X × RegionConfig n T) × (RegionConfig n X × RegionConfig n T)
  set g := Fintype.equivFin I
  set A : I → Matrix (SiteConfig n) (SiteConfig n) ℂ := fun p =>
    K' p.1 p.2 • localLift X (single p.1.1 p.2.1 1)
  set B : I → Matrix (SiteConfig n) (SiteConfig n) ℂ := fun p =>
    localLift T (single p.1.2 p.2.2 1)
  refine ⟨Fintype.card I, fun i => A (g.symm i), fun i => B (g.symm i), fun i => ?_,
    fun i => isSupportedOn_localLift _ _, ?_⟩
  · simp only [A, ← localLift_smul]
    exact isSupportedOn_localLift _ _
  · have hK : K = reindex e.symm e.symm K' := by simp [K']
    let Ψ : Matrix (RegionConfig n X × RegionConfig n T)
        (RegionConfig n X × RegionConfig n T) ℂ
        →ₗ[ℂ] Matrix (SiteConfig n) (SiteConfig n) ℂ :=
      { toFun := fun L => localLift (X ∪ T) (reindex e.symm e.symm L)
        map_add' := fun L L' => by
          rw [← localLift_add]
          congr 1
        map_smul' := fun c L => by
          rw [RingHom.id_apply, ← localLift_smul]
          congr 1 }
    have hΨ : ∀ L, Ψ L = localLift (X ∪ T) (reindex e.symm e.symm L) := fun _ => rfl
    rw [Equiv.sum_comp g.symm (fun p => A p * B p), hK, ← hΨ, matrix_eq_sum_single K',
      map_sum]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : single i j (K' i j) =
        K' i j • (single i.1 j.1 (1 : ℂ) ⊗ₖ single i.2 j.2 1) := by
      rw [single_kronecker_single, one_mul, smul_single, smul_eq_mul, mul_one]
    rw [h1, map_smul, hΨ, localLift_union_kronecker hXT]
    simp only [A, B, smul_mul_assoc]

end Entropy
