/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors

Ported from `LionSR/QICLean`,
`QICLean/Representation/ReplicaEtaForms.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (Apache 2.0).
-/
import OpenAI.MovementEtaRegional
import OpenAI.RelativePin
import OpenAI.SkewSymbolBound

/-!
# Relative-pin and skew bounds in regional entropy form

Lemma 6.3 is first proved with the coordinate exponent `Entropy.movementEta`.  This file
restates it with
`Entropy.regionalMovementEta P x Y θ = Sθ(x|P) + Sθ(x|Y)` and records the symmetry of the
replica partition metric under exchange of the two outer regions.

It also restates the skew-symbol bound (Lemma 6.4) with the same regional entropy exponent,
using the separate `SkewSymbolBound` development.
-/

open Matrix Entropy Entropy.ConditionalSkew Entropy.MarginalPhase PermutationRepresentation
open scoped Kronecker ComplexOrder MatrixOrder

namespace TensorPower

universe u

section Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

/-- The square-root partition metric is symmetric in its two outer regions. -/
theorem leafRoot_comm {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V}
    (hPF : Disjoint P F) :
    leafRoot n t k F Y P = leafRoot n t k P Y F := by
  have hPF' : Commute (replicaMetric (fun v => Fin (n v)) t k P)⁻¹
      (replicaMetric (fun v => Fin (n v)) t k F)⁻¹ := by
    rw [replicaMetric_inv_eq ht, replicaMetric_inv_eq ht]
    exact commute_replicaMetric_of_disjoint' k hPF _ _
  rw [leafRoot, leafRoot, hPF'.eq]

/-- The partition metric is symmetric in its two outer regions. -/
theorem leafMetric_comm {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V}
    (hPF : Disjoint P F) :
    leafMetric n t k F Y P = leafMetric n t k P Y F := by
  rw [leafMetric, leafMetric, leafRoot_comm ht k hPF]

theorem markedSimilarity_comm {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V}
    (hPF : Disjoint P F) (A : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    markedSimilarity n t k F Y P A = markedSimilarity n t k P Y F A := by
  rw [markedSimilarity, markedSimilarity, leafMetric_comm ht k hPF]

end Symmetry

/-- **Lemma 6.3 with its exponent in regional form**:
`ηθ = Sθ(x|P) + Sθ(x|Y)`. -/
theorem relativePin_regionalMovementEta :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {P x Y F : Finset V} (_ : FourPartition P x Y F) {t : ℝ}, 0 < t → t ≤ 1 →
        2 * t * Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ≤ c →
        ∃ K N : ℝ, 0 < K ∧ ∀ (k : ℕ) (θ : EuclideanSpace ℂ (SiteConfig n)), ‖θ‖ = 1 →
          ∀ w : Config k (fun v => Fin (n v)) → ℂ,
            ‖star (tensorVec k θ.ofLp) ⬝ᵥ w‖ ^ 2 *
              Real.exp (k * (2 * t) * (regionalMovementEta P x Y θ -
                C * (2 * t) ^ (1 / 4 : ℝ) *
                  Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ^ 2)) ≤
            K * ((k : ℝ) + 2) ^ N *
              (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re := by
  obtain ⟨C, c, hC, hc, H⟩ := relativePin.{u}
  refine ⟨C, c, hC, hc, fun h t ht0 ht1 hsmall => ?_⟩
  obtain ⟨K, N, hK, H'⟩ := H h ht0 ht1 hsmall
  refine ⟨K, N, hK, fun k θ hθ w => ?_⟩
  rw [← h.movementEta_frameVector θ]
  exact H' k θ hθ w

/-- **Lemma 6.3 for a move to the other outer region**. -/
theorem relativePin_toF :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {P x Y F : Finset V} (_ : FourPartition P x Y F) {t : ℝ}, 0 < t → t ≤ 1 →
        2 * t * Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ≤ c →
        ∃ K N : ℝ, 0 < K ∧ ∀ (k : ℕ) (θ : EuclideanSpace ℂ (SiteConfig n)), ‖θ‖ = 1 →
          ∀ w : Config k (fun v => Fin (n v)) → ℂ,
            ‖star (tensorVec k θ.ofLp) ⬝ᵥ w‖ ^ 2 *
              Real.exp (k * (2 * t) * (regionalMovementEta F x Y θ -
                C * (2 * t) ^ (1 / 4 : ℝ) *
                  Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ^ 2)) ≤
            K * ((k : ℝ) + 2) ^ N * (star w ⬝ᵥ
              (((CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹ *
                leafMetric n t k P Y (F ∪ x) *
                (CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹) *ᵥ w)).re := by
  obtain ⟨C, c, hC, hc, H⟩ := relativePin_regionalMovementEta.{u}
  refine ⟨C, c, hC, hc, ?_⟩
  intro V _ _ n _ P x Y F h t ht0 ht1 hsmall
  obtain ⟨K, N, hK, H'⟩ := H h.swap ht0 ht1 hsmall
  refine ⟨K, N, hK, fun k θ hθ w => ?_⟩
  have e : relativeMetric n t k F x Y P =
      (CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹ *
        leafMetric n t k P Y (F ∪ x) *
        (CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹ := by
    rw [relativeMetric, leafMetric_comm ht0.le k h.PF,
      leafMetric_comm ht0.le k (Finset.disjoint_union_right.mpr ⟨h.PF, h.Px⟩)]
  rw [← e]
  exact H' k θ hθ w

namespace SkewPartition

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
variable {P₀ P₁ x U F : Finset V} (hp : SkewPartition P₀ P₁ x U F)
include hp

omit [Fintype V] in
theorem Px : Disjoint (P₀ ∪ P₁) x :=
  Finset.disjoint_of_subset_right Finset.subset_union_left hp.PY

omit [Fintype V] [DecidableEq V] hp in
/-- `((P₀ P₁) x)(U F) ≃ (P₀ P₁)((x U) F)`. -/
def regroupUF {A₀ A₁ X' U' F' : Type*} :
    ((A₀ × A₁) × X') × (U' × F') ≃ (A₀ × A₁) × ((X' × U') × F') where
  toFun r := (r.1.1, ((r.1.2, r.2.1), r.2.2))
  invFun q := ((q.1, q.2.1.1), (q.2.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem isRegionSplit_Px : IsRegionSplit ((P₀ ∪ P₁) ∪ x)
    ((regionUnionEquiv hp.Px).trans (Equiv.prodCongr (regionUnionEquiv hp.P₀P₁) (Equiv.refl _)))
    ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm) where
  fst _ := rfl
  snd σ τ := by
    change ((fun v : {v // v ∈ U} => σ v), (fun v : {v // v ∈ F} => σ v)) =
      ((fun v : {v // v ∈ U} => τ v), (fun v : {v // v ∈ F} => τ v)) ↔ _
    simp only [Prod.mk.injEq, restrict_eq_iff]
    constructor
    · rintro ⟨hU, hF⟩ v hv
      simp only [Finset.mem_union, not_or] at hv
      rcases hp.mem_cases v with h | h | h | h | h
      · exact absurd h hv.1.1
      · exact absurd h hv.1.2
      · exact absurd h hv.2
      · exact hU v h
      · exact hF v h
    · intro h
      have nm := fun v => hp.not_mem_of_mem (v := v)
      refine ⟨fun v hv => h v ?_, fun v hv => h v ?_⟩ <;>
        simp only [Finset.mem_union, not_or] <;> have := nm v <;> tauto

omit [Fintype V] in
theorem marginalUF_rhoW_transport (θ : SiteConfig n → ℂ) :
    marginalUF (rhoW (hp.transport n θ)) =
      Matrix.traceLeft
        (vecMulVec (θ ∘ ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm).symm)
          (star (θ ∘ ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm).symm))) := by
  ext ⟨u, f⟩ ⟨u', f'⟩
  simp only [marginalUF, rhoW, margW, Matrix.traceLeft, submatrix_apply, vecMulVec_apply,
    Pi.star_apply, Function.comp_apply, Fintype.sum_prod_type, transport, Equiv.symm_trans_apply,
    Equiv.symm_symm, assocE, Equiv.prodAssoc_symm_apply, regroupUF, Equiv.coe_fn_mk]
  simp only [Matrix.of_apply]
  change (∑ x₀ : RegionConfig n x, ∑ p₀ : RegionConfig n P₀, ∑ p₁ : RegionConfig n P₁,
      θ (hp.equiv.symm ((p₀, p₁), ((x₀, u), f))) *
        star (θ (hp.equiv.symm ((p₀, p₁), ((x₀, u'), f'))))) =
    ∑ p₀ : RegionConfig n P₀, ∑ p₁ : RegionConfig n P₁, ∑ x₀ : RegionConfig n x,
      θ (hp.equiv.symm ((p₀, p₁), ((x₀, u), f))) *
        star (θ (hp.equiv.symm ((p₀, p₁), ((x₀, u'), f'))))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

/-- **`η_θ` of the skew bound in region form**: `I(x:F|U)` of the transported vector is
`S_θ(x|P) + S_θ(x|U)` with `P = P₀ ∪ P₁` (`05-replicas.tex`, lines 645–647; the two forms
agree by purity, `04-conditional.tex`, lines 122–124 and 138–139). -/
theorem skewEta_transport (θ : SiteConfig n → ℂ) :
    skewEta (hp.transport n θ) = regionalMovementEta (P₀ ∪ P₁) x U (WithLp.toLp 2 θ) := by
  set θt := hp.transport n θ
  set w := θ ∘ ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm).symm
  have eXU : ∀ hh, Arealaw.vonNeumann (hh : (marginalXU (rhoW θt)).IsHermitian) =
      FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) (x ∪ U) := by
    intro hh
    unfold FiniteProduct.entropy
    calc
      Arealaw.vonNeumann hh = Arealaw.vonNeumann
          (((FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
            (WithLp.toLp 2 θ) (x ∪ U)).submatrix (regionUnionEquiv hp.xU).symm).isHermitian) :=
        Arealaw.vonNeumann_congr hh _ (by
          rw [marginalXU_rhoW]
          change margY (hp.transport n θ) = _
          rw [hp.margY_transport, Entropy.margMatrix_eq_reducedPure])
      _ = Arealaw.vonNeumann
          (FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
            (WithLp.toLp 2 θ) (x ∪ U)).isHermitian :=
        Arealaw.vonNeumann_submatrix_equiv _ (regionUnionEquiv hp.xU).symm
  have eU : ∀ hh, Arealaw.vonNeumann (hh : (marginalU (rhoW θt)).IsHermitian) =
      FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) U := by
    intro hh
    unfold FiniteProduct.entropy
    apply Arealaw.vonNeumann_congr hh _
    rw [marginalU, marginalXU_rhoW]
    change Matrix.traceLeft (margY (hp.transport n θ)) = _
    rw [hp.margY_transport, Entropy.margMatrix_eq_reducedPure]
    have he : regionUnionEquiv (n := n) hp.xU =
        FiniteProduct.unionEquiv (fun v => Fin (n v)) x U hp.xU := rfl
    rw [he]
    simpa [FiniteProduct.reducedPure] using
      FiniteProduct.traceLeft_reducedMatrix_union (fun v => Fin (n v))
        (Matrix.vecMulVec θ (star θ)) x U hp.xU
  have eW : ∀ hh, Arealaw.vonNeumann (hh : (rhoW θt).IsHermitian) =
      FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) (P₀ ∪ P₁) := by
    intro hh
    have hpsd := posSemidef_vecMulVec_self_star θt
    have h1 : Arealaw.vonNeumann hh = Arealaw.vonNeumann hpsd.traceLeft.isHermitian := by
      calc
        Arealaw.vonNeumann hh = Arealaw.vonNeumann
            ((hpsd.traceLeft).submatrix assocE.symm).isHermitian :=
          Arealaw.vonNeumann_congr hh _ (by rfl)
        _ = Arealaw.vonNeumann hpsd.traceLeft.isHermitian :=
          Arealaw.vonNeumann_submatrix_equiv _ assocE.symm
    rw [h1, Arealaw.vonNeumann_traceLeft_vecMulVec_eq_traceRight]
    unfold FiniteProduct.entropy
    calc
      Arealaw.vonNeumann hpsd.traceRight.isHermitian = Arealaw.vonNeumann
          (((FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
            (WithLp.toLp 2 θ) (P₀ ∪ P₁)).submatrix
              (regionUnionEquiv hp.P₀P₁).symm).isHermitian) :=
        Arealaw.vonNeumann_congr _ _ (by
          change margP θt = _
          change margP (hp.transport n θ) = _
          rw [hp.margP_transport, Entropy.margMatrix_eq_reducedPure])
      _ = Arealaw.vonNeumann
          (FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
            (WithLp.toLp 2 θ) (P₀ ∪ P₁)).isHermitian :=
        Arealaw.vonNeumann_submatrix_equiv _ (regionUnionEquiv hp.P₀P₁).symm
  have eUF : ∀ hh, Arealaw.vonNeumann (hh : (marginalUF (rhoW θt)).IsHermitian) =
      FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) ((P₀ ∪ P₁) ∪ x) := by
    intro hh
    have hpsd := posSemidef_vecMulVec_self_star w
    unfold FiniteProduct.entropy
    calc
      Arealaw.vonNeumann hh = Arealaw.vonNeumann hpsd.traceLeft.isHermitian :=
        Arealaw.vonNeumann_congr hh _ (by
          change marginalUF (rhoW (hp.transport n θ)) = _
          simpa only [w] using hp.marginalUF_rhoW_transport θ)
      _ = Arealaw.vonNeumann hpsd.traceRight.isHermitian :=
        Arealaw.vonNeumann_traceLeft_vecMulVec_eq_traceRight w
      _ = Arealaw.vonNeumann
          (((FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
            (WithLp.toLp 2 θ) ((P₀ ∪ P₁) ∪ x)).submatrix
              ((regionUnionEquiv hp.Px).trans
                (Equiv.prodCongr (regionUnionEquiv hp.P₀P₁) (Equiv.refl _))).symm).isHermitian) :=
        Arealaw.vonNeumann_congr _ _ (by
          simpa only [w] using hp.isRegionSplit_Px.traceRight_vecMulVec θ)
      _ = Arealaw.vonNeumann
          (FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
            (WithLp.toLp 2 θ) ((P₀ ∪ P₁) ∪ x)).isHermitian :=
        Arealaw.vonNeumann_submatrix_equiv _ _
  rw [skewEta, condMutualInfo, regionalMovementEta]
  have hρ := posSemidef_rhoW θt
  have a1 := eXU (hρ.submatrix assocE).traceRight.isHermitian
  have a2 := eUF hρ.traceLeft.isHermitian
  have a3 := eU (hρ.submatrix assocE).traceRight.traceLeft.isHermitian
  have a4 := eW hρ.isHermitian
  calc
    _ = FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) (x ∪ U) +
        FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) ((P₀ ∪ P₁) ∪ x) -
        FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) U -
        FiniteProduct.entropy (fun v => Fin (n v)) (WithLp.toLp 2 θ) (P₀ ∪ P₁) := by
      have h12 := congrArg₂ (fun a b : ℝ => a + b) a1 a2
      have h123 := congrArg₂ (fun a b : ℝ => a - b) h12 a3
      have h1234 := congrArg₂ (fun a b : ℝ => a - b) h123 a4
      exact h1234
    _ = _ := by ring

/-- **Lemma 6.4, equation `replicas:skew-bound`, with `η_θ` in region form**
(`05-replicas.tex`, lines 640–660): for `h = lift_{P₀ x} K` with `0 ≤ K ≤ 1`,
`d_h = (dim P₀)(dim x)`, `0 < a` with `a log (e d_h) ≤ 1/8` and `t = a/2`, uniformly over
symmetric density matrices `σ`,
`Tr σ 𝒟_k ≤ 2 C a² log⁴(e d_h) ∫ η_θ^{1/8} dμ_σ(θ) + o_k(1)` with
`η_θ = S_θ(x|P) + S_θ(x|U)`, `P = P₀ ∪ P₁` and `C = skewConst`. -/
theorem eventually_re_trace_skewOperator_le_regionalMovementEta [∀ v, NeZero (n v)]
    {K : Matrix (RegionConfig n (P₀ ∪ x)) (RegionConfig n (P₀ ∪ x)) ℂ} (hK0 : 0 ≤ K)
    (hK1 : K ≤ 1) {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
      Fintype.card (RegionConfig n x))) ≤ 1 / 8) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ (b : SiteConfig n)
      (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
      σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
        ((σ * skewOperator k (markedSimilarity n (a / 2) k (P₀ ∪ P₁) (x ∪ U) F
            (localLift (P₀ ∪ x) K))).trace).re ≤
          2 * skewConst * a ^ 2 * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
            Fintype.card (RegionConfig n x))) ^ 4 *
            (coherentIntegral b σ fun θ =>
              ((regionalMovementEta (P₀ ∪ P₁) x U (WithLp.toLp 2 θ) ^ (1 / 8 : ℝ) : ℝ) :
                ℂ)).re + ε := by
  simpa only [hp.skewEta_transport] using
    hp.eventually_re_trace_skewOperator_le hK0 hK1 ha hac hε

/-- **Lemma 6.4, the skew bound with the outer parts exchanged** (`05-replicas.tex`, line 657,
and lines 842–843). For the partition metric `A_k(F, x ∪ U, P₀ ∪ P₁)`, whose second outer part
`P₀ ∪ P₁` contains the support `P₀` of `h` outside the middle part, the bound holds with
`η_θ = S_θ(x|P₀ ∪ P₁) + S_θ(x|U)`. -/
theorem eventually_re_trace_skewOperator_le_swap [∀ v, NeZero (n v)]
    {K : Matrix (RegionConfig n (P₀ ∪ x)) (RegionConfig n (P₀ ∪ x)) ℂ} (hK0 : 0 ≤ K)
    (hK1 : K ≤ 1) {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
      Fintype.card (RegionConfig n x))) ≤ 1 / 8) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ (b : SiteConfig n)
      (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
      σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
        ((σ * skewOperator k (markedSimilarity n (a / 2) k F (x ∪ U) (P₀ ∪ P₁)
            (localLift (P₀ ∪ x) K))).trace).re ≤
          2 * skewConst * a ^ 2 * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
            Fintype.card (RegionConfig n x))) ^ 4 *
            (coherentIntegral b σ fun θ =>
              ((regionalMovementEta (P₀ ∪ P₁) x U (WithLp.toLp 2 θ) ^ (1 / 8 : ℝ) : ℝ) :
                ℂ)).re + ε := by
  have hc : ∀ (k : ℕ) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ),
      markedSimilarity n (a / 2) k F (x ∪ U) (P₀ ∪ P₁) h =
        markedSimilarity n (a / 2) k (P₀ ∪ P₁) (x ∪ U) F h := fun k h =>
    markedSimilarity_comm (by positivity) k hp.PF h
  simp only [hc]
  exact hp.eventually_re_trace_skewOperator_le_regionalMovementEta hK0 hK1 ha hac hε

end SkewPartition

end TensorPower
