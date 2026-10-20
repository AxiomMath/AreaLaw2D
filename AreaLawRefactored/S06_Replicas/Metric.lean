import AreaLawRefactored.S06_Replicas.SchurLemma
import AreaLawRefactored.S06_Replicas.Ported.ReplicaMetric
import AreaLawRefactored.S06_Replicas.Ported.ReplicaIntegral
import AreaLawRefactored.S06_Replicas.Ported.ReplicaMarkedRatio
import AreaLawRefactored.S06_Replicas.Ported.ReplicaMarkedRatioInverse
import AreaLawRefactored.S06_Replicas.Ported.ReplicaSimilarity
import AreaLawRefactored.S06_Replicas.Ported.ReplicaSymmetricMetricFloor

/-!
# §6.1 A common metric on every subsystem (D6.5, D6.6) and the leaf metric (D6.8, D6.9)

Digest `digest/06-replicas.md` D6.5, D6.6, D6.8, D6.9; paper `paper/sections/05-replicas.tex`
lines 279–468.

`w ι t l` is the label function `w_k(λ)` with `λ` padded to `d = dim 𝒱` for every subsystem,
`W ι t k Q = ∑_λ w_k(λ) π^λ_{Q,k}`, `R ι t m Q = W_{Q,k} W_{Q,k-1}^{-1}` (`k = m + 1`) and
`A ι t k P Y F = (W_P^{-1} W_F^{-1} W_Y)^2`. They are definitionally the library declarations
`TensorPower.replicaLabelWeight`, `TensorPower.replicaMetric`, `TensorPower.markedRatio`, and
(for `ι = fun v => Fin (n v)`) `TensorPower.leafMetric`. Operator norms are `L²` operator
norms; `a = 2t`.
-/

namespace AreaLaw.Replicas

open Matrix PermutationRepresentation Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

variable {I : Type*} [DecidableEq I] [Fintype I] (ι : I → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-! ## D6.5 The label function `w_k` and `W_{Q,k}` -/

/-- D6.5 (`replicas:w-definition`). The label function `w_k(λ)`, the label padded to length
`d = dim 𝒱` for every subsystem; see `w_eq`. -/
noncomputable abbrev w (t : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) : ℝ :=
  TensorPower.replicaLabelWeight ι t l

/-- D6.5 (`replicas:w-definition`). `W_{Q,k} = ∑_λ w_k(λ) π^λ_{Q,k}`. -/
noncomputable abbrev W (t : ℝ) (k : ℕ) (Q : Finset I) :
    Matrix (Config ι k) (Config ι k) ℂ :=
  TensorPower.replicaMetric ι t k Q

omit [∀ f, DecidableEq (ι f)] in
/-- D6.5. With `d = dim 𝒱`, `c = d + (1 + t) binom(d, 2)` and `l_i = λ_i + d - i` (rows from
`0`: `λ_i + d - 1 - i`), for a label with `ℓ(λ) ≤ d` (all others have `π^λ_{Q,k} = 0`):
`w_k(λ) = Γ(c)/Γ(c + t k) ∏_i Γ(1 + t l_i)/Γ(1 + t (d - i))`. -/
theorem w_eq (t : ℝ) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k)))
    (hl : ∀ a, Fintype.card ((f : I) → ι f) ≤ a → TensorPower.labelPart l a = 0) :
    w ι t l =
      Real.Gamma (Fintype.card ((f : I) → ι f) +
          (1 + t) * ((Fintype.card ((f : I) → ι f)).choose 2 : ℕ)) /
        Real.Gamma (Fintype.card ((f : I) → ι f) +
          (1 + t) * ((Fintype.card ((f : I) → ι f)).choose 2 : ℕ) + t * k) *
      ∏ i : Fin (Fintype.card ((f : I) → ι f)),
        Real.Gamma (1 + t * (TensorPower.labelPart l i + (Fintype.card ((f : I) → ι f) - 1 - i)
            : ℕ)) /
          Real.Gamma (1 + t * (Fintype.card ((f : I) → ι f) - 1 - i : ℕ)) := by
  rw [w, TensorPower.replicaLabelWeight, Partition.replicaWeight,
    TensorPower.sum_labelPart_of_rows l hl]
  rfl

/-- D6.5. `W_{Q,k} = ∑_λ w_k(λ) π^λ_{Q,k}`. -/
theorem W_eq (t : ℝ) (k : ℕ) (Q : Finset I) : W ι t k Q = ∑ l, (w ι t l : ℂ) • π ι k Q l :=
  rfl

/-- D6.5. `W_{Q,0} = I`. -/
theorem W_zero [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (Q : Finset I) : W ι t 0 Q = 1 :=
  TensorPower.replicaMetric_zero ι ht Q

/-! ## D6.6 Lemma 6.2 -/

/-- D6.6. The marked ratio `R_{Q,k} = W_{Q,k} W_{Q,k-1}^{-1}`, `k = m + 1`, with `W_{Q,k-1}`
extended by `I` on the last copy (`eq_R`). -/
noncomputable abbrev R (t : ℝ) (m : ℕ) (Q : Finset I) :
    Matrix (Config ι (m + 1)) (Config ι (m + 1)) ℂ :=
  TensorPower.markedRatio ι t m Q

/-- D6.6. `R_{Q,k} = W_{Q,k} W'^{-1}` where `W'` is `W_{Q,k-1} ⊗ I` after splitting off the
last copy. -/
theorem eq_R (t : ℝ) (m : ℕ) (Q : Finset I) :
    R ι t m Q = W ι t (m + 1) Q * (TensorPower.replicaMetricFirst ι t m Q)⁻¹ ∧
      reindex (TensorPower.snocEquiv ι m) (TensorPower.snocEquiv ι m)
          (TensorPower.replicaMetricFirst ι t m Q) =
        W ι t m Q ⊗ₖ (1 : Matrix ((f : I) → ι f) ((f : I) → ι f) ℂ) :=
  ⟨rfl, TensorPower.replicaMetricFirst_eq ι t m Q⟩

/-- `𝒮_k` is the library's symmetric subspace. -/
theorem S_eq_symmetricSubspace (k : ℕ) : S ι k = TensorPower.symmetricSubspace k ι := by
  rw [S, TensorPower.symmetricSubspace, copyPerm, TensorPower.subsystemPerm_univ]

/-- D6.6, Lemma 6.2 (positivity, centrality). `W_{Q,k}` is positive definite and central: it
commutes with every `U_Q(π)`, and the metrics of nested or disjoint subsystems commute. -/
theorem lemma_6_2_1 [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (Q : Finset I) :
    (W ι t k Q).PosDef ∧ (∀ σ, Commute (W ι t k Q) (U ι k Q σ)) ∧
      ∀ Q' : Finset I, Q ⊆ Q' ∨ Disjoint Q Q' → Commute (W ι t k Q) (W ι t k Q') :=
  -- D6.6.1
  ⟨TensorPower.posDef_replicaMetric ι ht k Q,
    TensorPower.commute_replicaMetric_permOp ι t k Q,
    fun _ h => commute_labelObservable ι k h _ _⟩

/-- D6.6, Lemma 6.2 (`replicas:W-comparison`). Uniformly in `k`, `Q` and the labels,
`(k + 2)^{-C} e^{-t F_{Q,k}} ≤ W_{Q,k} ≤ (k + 2)^C e^{-t F_{Q,k}}`. -/
theorem lemma_6_2_2 [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, ∀ (k : ℕ) (Q : Finset I),
      (((k : ℝ) + 2) ^ (-C) : ℝ) • cfc (fun x => Real.exp (-t * x)) (F ι k Q) ≤ W ι t k Q ∧
        W ι t k Q ≤ (((k : ℝ) + 2) ^ C : ℝ) • cfc (fun x => Real.exp (-t * x)) (F ι k Q) := by
  -- D6.6.10
  obtain ⟨C, hC⟩ := TensorPower.exists_replicaMetric_comparison ι ht
  refine ⟨C, fun k Q => ?_⟩
  have h := hC k Q
  simp only [Complex.coe_smul] at h
  exact h

/-- D6.6, Lemma 6.2 (complement). On `𝒮_k`: `W_{Q,k} = W_{Q^c,k}`. -/
theorem lemma_6_2_3 (t : ℝ) (k : ℕ) (Q : Finset I) {z : Config ι k → ℂ} (hz : z ∈ S ι k) :
    W ι t k Q *ᵥ z = W ι t k Qᶜ *ᵥ z := by
  -- D6.6.9
  simp only [W_eq, sum_mulVec, smul_mulVec, step_6_4_9 ι k Q _ hz]

/-- D6.6, Lemma 6.2 (`replicas:W-integral`). For `0 < t ≤ 1` and each `Q` there is a
probability law (a random variable `τ` on a probability space `(Ω, P)`, its law being `ζ_Q`) of
positive definite subdensities `τ` on `Q` (`Tr τ ≤ 1`), independent of `k`, with
`W_{Q,k} = ∫ (τ^t)^{⊗k} dζ_Q(τ)` (tensored with `I` on `Q^c`) for every `k ≥ 0`. -/
theorem lemma_6_2_4 [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (Q : Finset I) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω),
      MeasureTheory.IsProbabilityMeasure P ∧
      ∃ τ : Ω → Matrix (TensorPower.SubConfig ι Q) (TensorPower.SubConfig ι Q) ℂ,
        (∀ᵐ ω ∂P, (τ ω).PosDef ∧ (τ ω).trace.re ≤ 1) ∧
        (∀ (k : ℕ) (a b : Fin k → TensorPower.SubConfig ι Q),
          MeasureTheory.Integrable (fun ω => TensorPower.tensorPow (k := k) (τ ω ^ t) a b) P) ∧
        ∀ k : ℕ, reindex (TensorPower.splitEquiv ι k Q) (TensorPower.splitEquiv ι k Q)
            (W ι t k Q) =
          (Matrix.of fun a b => ∫ ω, TensorPower.tensorPow (k := k) (τ ω ^ t) a b ∂P) ⊗ₖ
            (1 : Matrix (Fin k → TensorPower.ComplConfig ι Q)
              (Fin k → TensorPower.ComplConfig ι Q) ℂ) :=
  -- D6.6.2–D6.6.8
  TensorPower.exists_replicaMetric_integral ι ht0 ht1 Q

/-- D6.6, Lemma 6.2 (`replicas:R-forward`). On the whole tensor space,
`‖R_{Q,k} - (J_{Q,k})_+^t‖ ≤ C k^{-t} → 0`, and `‖R_{Q,k}‖ ≤ C`, uniformly in `Q`. -/
theorem lemma_6_2_5 [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C, ∀ (m : ℕ) (Q : Finset I),
      ‖R ι t m Q - cfc (fun x : ℝ => (max x 0) ^ t) (J ι m Q)‖ ≤ C * ((m + 1 : ℕ) : ℝ) ^ (-t) ∧
        ‖R ι t m Q‖ ≤ C ∧
        Tendsto (fun m => ‖R ι t m Q - cfc (fun x : ℝ => (max x 0) ^ t) (J ι m Q)‖) atTop
          (𝓝 0) := by
  -- D6.6.11–D6.6.13
  obtain ⟨C₁, hC₁⟩ := TensorPower.exists_l2_opNorm_markedRatio_sub_le ι ht0 ht1
  obtain ⟨C₂, hC₂⟩ := TensorPower.exists_l2_opNorm_markedRatio_le ι ht0 ht1
  refine ⟨max C₁ C₂, fun m Q => ⟨(hC₁ m Q).trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (by positivity)), (hC₂ m Q).trans (le_max_right _ _), ?_⟩⟩
  have hk : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun m : ℕ => C₁ * ((m + 1 : ℕ) : ℝ) ^ (-t)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop ht0).comp hk).const_mul C₁
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => hC₁ m Q) h0

/-- D6.6, Lemma 6.2 (inverse vector bound). There is `C_{𝒱,t}` with
`‖R_{Q,k}^{-1} z‖ ≤ C_{𝒱,t} ‖z‖` for every `z ∈ 𝒮_k`, uniformly in `k` and `Q`. -/
theorem lemma_6_2_6 [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    ∃ C, ∀ (m : ℕ) (Q : Finset I) (z : Config ι (m + 1) → ℂ), z ∈ S ι (m + 1) →
      ‖(EuclideanSpace.equiv _ ℂ).symm ((R ι t m Q)⁻¹ *ᵥ z)‖ ≤
        C * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ := by
  -- D6.6.14
  obtain ⟨C, hC⟩ := TensorPower.exists_norm_markedRatio_inv_mulVec_le ι ht0 ht1
  exact ⟨C, fun m Q z hz => hC m Q z (S_eq_symmetricSubspace ι _ ▸ hz)⟩

/-- D6.6, Lemma 6.2 (`replicas:R-inverse`). There is `C_{𝒱,t}` such that for `0 < δ < 1`
`limsup_k sup_{z ∈ 𝒮_k, ‖z‖ = 1} ‖(R_{Q,k}^{-1} - max(J_{Q,k}, δ)^{-t}) z‖ ≤ C_{𝒱,t} δ^{(1-2t)/2}`,
in the form: for every `ε > 0` the bound `C δ^{(1-2t)/2} + ε` holds for all large `k`, uniformly
in `Q` and the unit `z ∈ 𝒮_k`. -/
theorem lemma_6_2_7 [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    ∃ C, ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m ≥ K, ∀ (Q : Finset I)
      (z : Config ι (m + 1) → ℂ), z ∈ S ι (m + 1) →
        ‖(EuclideanSpace.equiv _ ℂ).symm (((R ι t m Q)⁻¹ -
            cfc (fun x : ℝ => (max x δ) ^ (-t)) (J ι m Q)) *ᵥ z)‖ ≤
          (C * δ ^ ((1 - 2 * t) / 2) + ε) * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ := by
  -- D6.6.15, D6.6.16
  obtain ⟨C, hC⟩ := TensorPower.exists_norm_markedRatio_inv_sub_clipped_le ι ht0 ht1
  refine ⟨C, fun δ hδ hδ1 ε hε => ?_⟩
  obtain ⟨K, hK⟩ := hC δ hδ hδ1 ε hε
  exact ⟨K, fun m hm Q z hz => hK m hm Q z (S_eq_symmetricSubspace ι _ ▸ hz)⟩

/-- D6.6, Lemma 6.2. For `0 < t < 1/2` (the paper's `t < 1/4`; only `1 - 2t > 0` is used):
items (1)–(7) above. -/
theorem lemma_6_2 [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (∀ k Q, (W ι t k Q).PosDef ∧ (∀ σ, Commute (W ι t k Q) (U ι k Q σ)) ∧
      ∀ Q' : Finset I, Q ⊆ Q' ∨ Disjoint Q Q' → Commute (W ι t k Q) (W ι t k Q')) ∧
    (∃ C : ℝ, ∀ (k : ℕ) (Q : Finset I),
      (((k : ℝ) + 2) ^ (-C) : ℝ) • cfc (fun x => Real.exp (-t * x)) (F ι k Q) ≤ W ι t k Q ∧
        W ι t k Q ≤ (((k : ℝ) + 2) ^ C : ℝ) • cfc (fun x => Real.exp (-t * x)) (F ι k Q)) ∧
    (∀ k (Q : Finset I) (z : Config ι k → ℂ), z ∈ S ι k →
      W ι t k Q *ᵥ z = W ι t k Qᶜ *ᵥ z) ∧
    (∀ Q : Finset I, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω),
      MeasureTheory.IsProbabilityMeasure P ∧
      ∃ τ : Ω → Matrix (TensorPower.SubConfig ι Q) (TensorPower.SubConfig ι Q) ℂ,
        (∀ᵐ ω ∂P, (τ ω).PosDef ∧ (τ ω).trace.re ≤ 1) ∧
        (∀ (k : ℕ) (a b : Fin k → TensorPower.SubConfig ι Q),
          MeasureTheory.Integrable (fun ω => TensorPower.tensorPow (k := k) (τ ω ^ t) a b) P) ∧
        ∀ k : ℕ, reindex (TensorPower.splitEquiv ι k Q) (TensorPower.splitEquiv ι k Q)
            (W ι t k Q) =
          (Matrix.of fun a b => ∫ ω, TensorPower.tensorPow (k := k) (τ ω ^ t) a b ∂P) ⊗ₖ
            (1 : Matrix (Fin k → TensorPower.ComplConfig ι Q)
              (Fin k → TensorPower.ComplConfig ι Q) ℂ)) ∧
    (∃ C, ∀ (m : ℕ) (Q : Finset I),
      ‖R ι t m Q - cfc (fun x : ℝ => (max x 0) ^ t) (J ι m Q)‖ ≤ C * ((m + 1 : ℕ) : ℝ) ^ (-t) ∧
        ‖R ι t m Q‖ ≤ C ∧
        Tendsto (fun m => ‖R ι t m Q - cfc (fun x : ℝ => (max x 0) ^ t) (J ι m Q)‖) atTop
          (𝓝 0)) ∧
    (∃ C, ∀ (m : ℕ) (Q : Finset I) (z : Config ι (m + 1) → ℂ), z ∈ S ι (m + 1) →
      ‖(EuclideanSpace.equiv _ ℂ).symm ((R ι t m Q)⁻¹ *ᵥ z)‖ ≤
        C * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) ∧
    (∃ C, ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m ≥ K, ∀ (Q : Finset I)
      (z : Config ι (m + 1) → ℂ), z ∈ S ι (m + 1) →
        ‖(EuclideanSpace.equiv _ ℂ).symm (((R ι t m Q)⁻¹ -
            cfc (fun x : ℝ => (max x δ) ^ (-t)) (J ι m Q)) *ᵥ z)‖ ≤
          (C * δ ^ ((1 - 2 * t) / 2) + ε) * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) :=
  ⟨lemma_6_2_1 ι ht0.le, lemma_6_2_2 ι ht0, lemma_6_2_3 ι t, lemma_6_2_4 ι ht0 (by linarith),
    lemma_6_2_5 ι ht0 (by linarith), lemma_6_2_6 ι ht0 ht1, lemma_6_2_7 ι ht0 ht1⟩

/-! ## D6.8 The partition metric `A_k(P, Y, F)` -/

/-- D6.8 (`replicas:leaf-metric`). `A_k(P, Y, F) = (W_{P,k}^{-1} W_{F,k}^{-1} W_{Y,k})^2`. -/
noncomputable def A (t : ℝ) (k : ℕ) (P Y F : Finset I) : Matrix (Config ι k) (Config ι k) ℂ :=
  ((W ι t k P)⁻¹ * (W ι t k F)⁻¹ * W ι t k Y) ^ 2

/-- D6.8. `A` is the library's `TensorPower.leafMetric` for local dimensions `n`. -/
theorem A_eq_leafMetric {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) (t : ℝ) (k : ℕ)
    (P Y F : Finset V) : A (fun v => Fin (n v)) t k P Y F = TensorPower.leafMetric n t k P Y F :=
  rfl

/-- `W_{Q,k}^{-1} = ∑_λ w_k(λ)^{-1} π^λ_{Q,k}`. -/
theorem W_inv [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (Q : Finset I) :
    (W ι t k Q)⁻¹ = labelObservable (copyPerm ι k Q) fun l => (w ι t l)⁻¹ :=
  labelObservable_inv _ fun l => (TensorPower.replicaLabelWeight_pos ι ht l).ne'

/-- D6.8 (`replicas:leaf-metric`). For pairwise disjoint `P, Y, F` the factors
`W_P^{±1}, W_F^{±1}, W_Y^{±1}` pairwise commute (Lemma 6.1 (2)); `A_k(P, Y, F)` is positive
definite and `A_k(P, Y, F) = A_k(F, Y, P)`. -/
theorem eq_replicas_leaf_metric [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {P Y F : Finset I} (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F) :
    (∀ g g' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ,
      Commute (labelObservable (copyPerm ι k P) g) (labelObservable (copyPerm ι k F) g') ∧
      Commute (labelObservable (copyPerm ι k P) g) (labelObservable (copyPerm ι k Y) g') ∧
      Commute (labelObservable (copyPerm ι k F) g) (labelObservable (copyPerm ι k Y) g')) ∧
    Commute (W ι t k P)⁻¹ (W ι t k F)⁻¹ ∧ Commute (W ι t k P)⁻¹ (W ι t k Y) ∧
    Commute (W ι t k F)⁻¹ (W ι t k Y) ∧
    (A ι t k P Y F).PosDef ∧ A ι t k P Y F = A ι t k F Y P := by
  have hc := fun (g g' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) =>
    (⟨commute_labelObservable ι k (Or.inr hPF) g g', commute_labelObservable ι k (Or.inr hPY) g g',
      commute_labelObservable ι k (Or.inr hYF.symm) g g'⟩ :
      Commute (labelObservable (copyPerm ι k P) g) (labelObservable (copyPerm ι k F) g') ∧
      Commute (labelObservable (copyPerm ι k P) g) (labelObservable (copyPerm ι k Y) g') ∧
      Commute (labelObservable (copyPerm ι k F) g) (labelObservable (copyPerm ι k Y) g'))
  have hPF' : Commute (W ι t k P)⁻¹ (W ι t k F)⁻¹ := by
    rw [W_inv ι ht, W_inv ι ht]; exact (hc _ _).1
  refine ⟨hc, hPF', by rw [W_inv ι ht]; exact (hc _ _).2.1, by rw [W_inv ι ht]; exact (hc _ _).2.2,
    TensorPower.posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht k hPF hPY hYF.symm, ?_⟩
  rw [A, A, hPF'.eq]

/-! ## D6.9 Floor of the leaf metric and commutation with copy averages -/

/-- D6.9 (`replicas:leaf-floor`), log formula. For pairwise disjoint `P, Y, F`, in operator
norm on the whole tensor space (in particular on `𝒮_k`), with `a = 2t`:
`‖log A_k - a (F_P + F_F - F_Y)‖ ≤ C log(k + 2)`, `C = C_{𝒱,t}` uniform in `k, P, Y, F`. -/
theorem eq_replicas_leaf_floor_1 [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset I), Disjoint P Y → Disjoint P F →
      Disjoint Y F →
      ‖cfc Real.log (A ι t k P Y F) -
          ((2 * t : ℝ) : ℂ) • (Replicas.F ι k P + Replicas.F ι k F - Replicas.F ι k Y)‖ ≤
        C * Real.log ((k : ℝ) + 2) := by
  obtain ⟨C₀, hC₀, hweight⟩ := TensorPower.exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨6 * C₀, by positivity, fun k P Y F hPY hdisPF hYF => ?_⟩
  -- D6.9.1: the joint resolution of the three commuting label decompositions
  let hP := isOrthogonalResolution_labelProj (TensorPower.subsystemPerm k ι P)
  let hF := isOrthogonalResolution_labelProj (TensorPower.subsystemPerm k ι F)
  let hY := isOrthogonalResolution_labelProj (TensorPower.subsystemPerm k ι Y)
  let hPF := hP.prod hF (fun α β =>
    TensorPower.commute_labelProj_subsystemPerm_of_disjoint ι k hdisPF α β)
  let R := hPF.prod hY (fun ab γ =>
    (TensorPower.commute_labelProj_subsystemPerm_of_disjoint ι k hPY ab.1 γ).mul_left
      (TensorPower.commute_labelProj_subsystemPerm_of_disjoint ι k hYF.symm ab.2 γ))
  have hRP (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.1) = hP.hom f :=
    (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_fst hF hPF f)
  have hRF (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.2) = hF.hom f :=
    (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_snd hF hPF f)
  have hRY (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.2) = hY.hom f :=
    hPF.prod_hom_snd hY R f
  have hw (l : IrrepLabel (Equiv.Perm (Fin k))) : 0 < w ι t l :=
    TensorPower.replicaLabelWeight_pos ι ht.le l
  have hWP : (W ι t k P)⁻¹ = R.hom (fun p => (((w ι t p.1.1)⁻¹ : ℝ) : ℂ)) := by
    rw [W_inv ι ht.le]
    simpa only [labelObservable_eq_hom] using (hRP (fun l => (((w ι t l)⁻¹ : ℝ) : ℂ))).symm
  have hWF : (W ι t k F)⁻¹ = R.hom (fun p => (((w ι t p.1.2)⁻¹ : ℝ) : ℂ)) := by
    rw [W_inv ι ht.le]
    simpa only [labelObservable_eq_hom] using (hRF (fun l => (((w ι t l)⁻¹ : ℝ) : ℂ))).symm
  have hWY : W ι t k Y = R.hom (fun p => (w ι t p.2 : ℂ)) := by
    simpa only [W, TensorPower.replicaMetric, labelObservable_eq_hom] using
      (hRY (fun l => (w ι t l : ℂ))).symm
  let q : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => ((w ι t p.1.1)⁻¹ * (w ι t p.1.2)⁻¹ * w ι t p.2) ^ 2
  have hA : A ι t k P Y F = R.hom (fun p => (q p : ℂ)) := by
    rw [A, hWP, hWF, hWY, ← map_mul, ← map_mul, ← map_pow]
    congr 1
    ext p
    simp only [q, Pi.mul_apply, Pi.pow_apply]
    push_cast
    rfl
  let g : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => Real.log p.1.1.dim + Real.log p.1.2.dim - Real.log p.2.dim
  have hG : Replicas.F ι k P + Replicas.F ι k F - Replicas.F ι k Y =
      R.hom (fun p => (g p : ℂ)) := by
    change labelEntropy (TensorPower.subsystemPerm k ι P) +
      labelEntropy (TensorPower.subsystemPerm k ι F) -
        labelEntropy (TensorPower.subsystemPerm k ι Y) = _
    simp only [labelEntropy, labelObservable_eq_hom]
    rw [← hRP, ← hRF, ← hRY, ← map_add, ← map_sub]
    congr 1
    ext p
    simp only [g, Pi.add_apply, Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_add]
  have hHerm (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k))) :
      (labelProj (TensorPower.subsystemPerm k ι P) p.1.1 *
        labelProj (TensorPower.subsystemPerm k ι F) p.1.2 *
          labelProj (TensorPower.subsystemPerm k ι Y) p.2).IsHermitian :=
    ((((isHermitian_labelProj _ p.1.1).commute_iff (isHermitian_labelProj _ p.1.2)).mp
      (TensorPower.commute_labelProj_subsystemPerm_of_disjoint ι k hdisPF p.1.1 p.1.2)).commute_iff
        (isHermitian_labelProj _ p.2)).mp
          ((TensorPower.commute_labelProj_subsystemPerm_of_disjoint ι k hPY p.1.1 p.2).mul_left
            (TensorPower.commute_labelProj_subsystemPerm_of_disjoint ι k hYF.symm p.1.2 p.2))
  rw [hA, R.cfc_hom hHerm, hG, ← map_smul, ← map_sub]
  have hL : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
  refine R.l2_opNorm_hom_le hHerm (by positivity) fun p hp => ?_
  have hPn : labelProj (TensorPower.subsystemPerm k ι P) p.1.1 ≠ 0 := fun hz =>
    hp (by simp only [hz, zero_mul])
  have hFn : labelProj (TensorPower.subsystemPerm k ι F) p.1.2 ≠ 0 := fun hz =>
    hp (by simp only [hz, mul_zero, zero_mul])
  have hYn : labelProj (TensorPower.subsystemPerm k ι Y) p.2 ≠ 0 := fun hz =>
    hp (by simp only [hz, mul_zero])
  have heP := abs_le.mp (hweight k P p.1.1 hPn)
  have heF := abs_le.mp (hweight k F p.1.2 hFn)
  have heY := abs_le.mp (hweight k Y p.2 hYn)
  -- D6.9.1: `log w_k(λ) = -t log d_λ + O(log(k + 2))` on each of the three labels
  have hlog : Real.log (q p) = 2 * (Real.log (w ι t p.2) - Real.log (w ι t p.1.1) -
      Real.log (w ι t p.1.2)) := by
    simp only [q, Real.log_pow, Real.log_mul (mul_pos (inv_pos.mpr (hw _))
      (inv_pos.mpr (hw _))).ne' (hw _).ne', Real.log_mul (inv_pos.mpr (hw _)).ne'
      (inv_pos.mpr (hw _)).ne', Real.log_inv]
    push_cast
    ring
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hlog,
    abs_le]
  simp only [g, w] at heP heF heY ⊢
  constructor <;> nlinarith

/-- D6.9 (`replicas:leaf-floor`), floor. For a partition `P, Y, F` of `𝒱`, on `𝒮_k`:
`A_k ≥ (k + 2)^{-C} I` (`Π_k`-form `(k + 2)^{-C} Π_k ≤ A_k`), and
`Π_k A_k^{-1} Π_k ≤ (k + 2)^C Π_k`, `C` uniform in `k, P, Y, F`. -/
theorem eq_replicas_leaf_floor_2 [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset I), Disjoint P Y → Disjoint P F →
      Disjoint Y F → P ∪ Y ∪ F = Finset.univ →
      (((k : ℝ) + 2) ^ (-C)) • projS ι k ≤ A ι t k P Y F ∧
        projS ι k * (A ι t k P Y F)⁻¹ * projS ι k ≤ (((k : ℝ) + 2) ^ C) • projS ι k := by
  -- D6.9.1, D6.9.2
  obtain ⟨C, hC, h⟩ := TensorPower.exists_replicaMetric_symProj_inverse_bound_and_floor ι ht
  refine ⟨C, hC, fun k P Y F hPY hPF hYF hcov => ?_⟩
  have hS : projS ι k = symProj (TensorPower.copyPerm ((f : I) → ι f) k) := by
    rw [projS, copyPerm, TensorPower.subsystemPerm_univ]
  rw [hS]
  exact ⟨(h k P Y F hPY hPF hYF hcov).2, (h k P Y F hPY hPF hYF hcov).1⟩

section CopyMean

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

omit [DecidableEq I] [Fintype I] in
/-- D6.9.3. For `h` inside `D` and `Q ⊇ D` or `Q` disjoint from `D`, `h̄ = k⁻¹ ∑_j h^{(j)}`
commutes with every `U_Q(π)`. -/
theorem commute_permOp_copyMean {h : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ}
    {D Q : Finset V} (hh : Entropy.IsSupportedOn h D) (hQ : D ⊆ Q ∨ Disjoint Q D) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) :
    Commute (permOp (TensorPower.subsystemPerm k (fun v => Fin (n v)) Q) σ)
      (TensorPower.copyMean n k h) := by
  have hdis : ∀ Q' : Finset V, Disjoint Q' D → ∀ σ : Equiv.Perm (Fin k),
      Commute (permOp (TensorPower.subsystemPerm k (fun v => Fin (n v)) Q') σ)
        (TensorPower.copyMean n k h) := fun Q' hQ' σ =>
    (Commute.sum_right _ _ _ fun j _ =>
      TensorPower.commute_permOp_subsystemPerm_siteOp_of_disjoint hh hQ' j σ).smul_right _
  rcases hQ with hDQ | hQD
  · -- `U_Q(π) = U(π) U_{Q^c}(π⁻¹)`, `h̄` symmetric and `Q^c` disjoint from `D`
    have e : permOp (TensorPower.subsystemPerm k (fun v => Fin (n v)) Q) σ =
        permOp (TensorPower.copyPerm (Entropy.SiteConfig n) k) σ *
          permOp (TensorPower.subsystemPerm k (fun v => Fin (n v)) Qᶜ) σ⁻¹ := by
      rw [permOp_of_eq_mul _ _ _ (fun g => TensorPower.copyPerm_eq_mul_compl Q g) σ, mul_assoc,
        permOp_mul_inv_self, mul_one]
    rw [e]
    exact (TensorPower.commute_copyPerm_copyMean k h σ).mul_left
      (hdis Qᶜ (disjoint_compl_left.mono_right hDQ) σ⁻¹)
  · exact hdis Q hQD σ

omit [DecidableEq I] [Fintype I] in
/-- D6.9.3. A one-copy `h` inside one part `R ∈ {P, Y, F}` of pairwise disjoint `P, Y, F`
(`h` supported on `D ⊆ R`): `h̄ = k⁻¹ ∑_j h^{(j)}` commutes with `A_k(P, Y, F)`. -/
theorem eq_replicas_leaf_floor_3 [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {P Y F D : Finset V} (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F)
    {h : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ} (hh : Entropy.IsSupportedOn h D)
    (hD : D ⊆ P ∨ D ⊆ Y ∨ D ⊆ F) :
    Commute (A (fun v => Fin (n v)) t k P Y F) (TensorPower.copyMean n k h) := by
  have hc : ∀ Q : Finset V, D ⊆ Q ∨ Disjoint Q D →
      ∀ g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ,
        Commute (labelObservable (copyPerm (fun v => Fin (n v)) k Q) g)
          (TensorPower.copyMean n k h) := fun Q hQ g =>
    commute_labelObservable_of_forall_commute _ (commute_permOp_copyMean hh hQ) g
  -- D6.9.3: each part contains `D` or is disjoint from it
  have hP : D ⊆ P ∨ Disjoint P D := by
    rcases hD with hD | hD | hD
    · exact .inl hD
    · exact .inr (hPY.mono_right hD)
    · exact .inr (hPF.mono_right hD)
  have hY : D ⊆ Y ∨ Disjoint Y D := by
    rcases hD with hD | hD | hD
    · exact .inr (hPY.symm.mono_right hD)
    · exact .inl hD
    · exact .inr (hYF.mono_right hD)
  have hF : D ⊆ F ∨ Disjoint F D := by
    rcases hD with hD | hD | hD
    · exact .inr (hPF.symm.mono_right hD)
    · exact .inr (hYF.symm.mono_right hD)
    · exact .inl hD
  rw [A, W_inv _ ht, W_inv _ ht]
  exact (((hc P hP _).mul_left (hc F hF _)).mul_left (hc Y hY _)).pow_left 2

/-- D6.9 (`replicas:leaf-floor`). For a partition `P, Y, F` of `𝒱 = ⨂_v ℂ^{n_v}` and
`a = 2t`: `log A_k = a (F_P + F_F - F_Y) + O_{𝒱,t}(log(k + 2))` in operator norm,
`A_k ≥ poly(k)^{-1} I` on `𝒮_k`, and `h̄ = k⁻¹ ∑_j h^{(j)}` commutes with `A_k` for a one-copy
`h` inside one part. (Parts (1), (2) for arbitrary local dimensions: `eq_replicas_leaf_floor_1`,
`eq_replicas_leaf_floor_2`.) -/
theorem eq_replicas_leaf_floor [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V), Disjoint P Y → Disjoint P F →
      Disjoint Y F → P ∪ Y ∪ F = Finset.univ →
      ‖cfc Real.log (A (fun v => Fin (n v)) t k P Y F) - ((2 * t : ℝ) : ℂ) •
          (Replicas.F (fun v => Fin (n v)) k P + Replicas.F (fun v => Fin (n v)) k F -
            Replicas.F (fun v => Fin (n v)) k Y)‖ ≤ C * Real.log ((k : ℝ) + 2) ∧
      (((k : ℝ) + 2) ^ (-C)) • projS (fun v => Fin (n v)) k ≤ A (fun v => Fin (n v)) t k P Y F ∧
      ∀ (D : Finset V) (h : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ),
        Entropy.IsSupportedOn h D → (D ⊆ P ∨ D ⊆ Y ∨ D ⊆ F) →
          Commute (A (fun v => Fin (n v)) t k P Y F) (TensorPower.copyMean n k h) := by
  obtain ⟨C₁, hC₁, h₁⟩ := eq_replicas_leaf_floor_1 (fun v => Fin (n v)) ht
  obtain ⟨C₂, hC₂, h₂⟩ := eq_replicas_leaf_floor_2 (fun v => Fin (n v)) ht
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun k P Y F hPY hPF hYF hcov => ⟨?_, ?_,
    fun D h hh hD => eq_replicas_leaf_floor_3 ht.le k hPY hPF hYF hh hD⟩⟩
  · have hL : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
    exact (h₁ k P Y F hPY hPF hYF).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hL)
  · have hk : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [k.cast_nonneg (α := ℝ)]
    refine le_trans ?_ (h₂ k P Y F hPY hPF hYF hcov).1
    have hS : (0 : Matrix _ _ ℂ) ≤ projS (fun v => Fin (n v)) k :=
      (isStarProjection_symProj _).nonneg
    exact smul_le_smul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hk (neg_le_neg (le_max_right _ _))) hS

end CopyMean

end AreaLaw.Replicas
