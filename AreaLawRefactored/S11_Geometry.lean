import AreaLawRefactored.S02_Preliminaries
import AreaLawForMathlib.QuantumInfo.Entropy.Subadditivity
import AreaLawRefactored.S11_Geometry.Exponents
import AreaLawRefactored.S11_Geometry.Layers
import AreaLawRefactored.S11_Geometry.Scales
import AreaLawRefactored.S11_Geometry.RepairScales
import AreaLawRefactored.S11_Geometry.Primaries
import AreaLawRefactored.S11_Geometry.RepairRegions

/-!
# §11 Two families of regions and the area bound

Digest `digest/11-geometry.md`, paper `paper/sections/10-geometry.tex`.

Propositions 9.6 and 10.2 and Proposition 11.2 enter through their frozen statements
`OpenAI.CollarBound`, `OpenAI.Amplification` and `OpenAI.TwoFamilyDecomposition`, taken as
hypotheses.
-/

namespace AreaLaw

open Arealaw OpenAI Finset
open scoped ENNReal Matrix

/-! ## 11.1 The entropy cancellation -/

section D111

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U : Finset σ}

/-- D11.1.1. Chain rule adding the `X_i`, `i ∈ s`, in increasing order to `B`:
`S(B ∪ ⋃_{i∈s} X_i) = S(B) + ∑_{i∈s} S(X_i | B ∪ X_{<i})`, `X_{<i} = ⋃_{j∈s, j<i} X_j`. -/
theorem step_11_1_1 {ι : Type*} [LinearOrder ι] (ρ : SubState (Reg loc U) ℂ) {B : Finset σ}
    (hB : B ⊆ U) (s : Finset ι) {X : ι → Finset σ} (hX : ∀ i, X i ⊆ U) :
    ρ.regionEntropy (union_subset hB (biUnion_subset.2 fun i _ => hX i) : B ∪ s.biUnion X ⊆ U) =
      ρ.regionEntropy hB + ∑ i ∈ s, condEntropy ρ (hX i)
        (union_subset hB (biUnion_subset.2 fun j _ => hX j) :
          B ∪ (s.filter (· < i)).biUnion X ⊆ U) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hlt : (insert a s).filter (· < a) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      exact ⟨fun h => h.1.resolve_left (ne_of_lt h.2), fun hx => ⟨Or.inr hx, ha x hx⟩⟩
    have hs : ∀ i ∈ s, (insert a s).filter (· < i) = s.filter (· < i) := fun i hi => by
      rw [filter_insert, if_neg (not_lt.2 (ha i hi).le)]
    have hc : ∀ {D E E' : Finset σ} (hD : D ⊆ U) (hE : E ⊆ U) (hE' : E' ⊆ U), E = E' →
        condEntropy ρ hD hE = condEntropy ρ hD hE' := by rintro _ _ _ _ _ _ rfl; rfl
    have hBs : B ∪ s.biUnion X ⊆ U := union_subset hB (biUnion_subset.2 fun j _ => hX j)
    rw [sum_insert has, sum_congr rfl fun i hi => hc (hX i) _
        (union_subset hB (biUnion_subset.2 fun j _ => hX j)) (congrArg (B ∪ ·.biUnion X) (hs i hi)),
      hc (hX a) _ hBs (congrArg (B ∪ ·.biUnion X) hlt),
      condEntropy, ρ.regionEntropy_congr (show B ∪ (insert a s).biUnion X = X a ∪ (B ∪ s.biUnion X)
        by rw [biUnion_insert]; ac_rfl) _ (union_subset (hX a) hBs)]
    linarith [ih]

/-- D11.1.4. For `ψ` pure on `Λ`, `A = D ∪ ⋃ᵢ Xᵢ` disjoint, `B = Λ \ A` and `A_f = ⋃_{p i} Xᵢ`:
`Λ \ (B ∪ A_f) = D ∪ A_{1-f}`, so `S(B A_f) = S(D A_{1-f}) ≤ S(D) + ∑_{¬p i} S(Xᵢ)`. -/
theorem step_11_1_4 {ι : Type*} [Fintype ι] {Λ : Finset σ} (ψ : Reg loc Λ → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) {A D : Finset σ} (hA : A ⊆ Λ) (hD : D ⊆ Λ) {X : ι → Finset σ}
    (hX : ∀ i, X i ⊆ Λ) (p : ι → Prop) [DecidablePred p] (hAD : A = D ∪ univ.biUnion X)
    (hDX : ∀ i, Disjoint D (X i)) (hXX : Pairwise (Function.onFun Disjoint X)) :
    (pureState ψ hψ).regionEntropy (union_subset sdiff_subset
        (biUnion_subset.2 fun j _ => hX j) : Λ \ A ∪ (univ.filter p).biUnion X ⊆ Λ) ≤
      (pureState ψ hψ).regionEntropy hD +
        ∑ i ∈ univ.filter fun i => ¬p i, (pureState ψ hψ).regionEntropy (hX i) := by
  have hset : Λ \ (Λ \ A ∪ (univ.filter p).biUnion X) =
      D ∪ (univ.filter fun i => ¬p i).biUnion X := by
    have hmem : ∀ x, x ∈ A ↔ x ∈ D ∨ ∃ i, x ∈ X i := fun x => by simp [hAD]
    ext x
    simp only [mem_sdiff, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
    refine ⟨fun ⟨hxΛ, hx⟩ => ?_, fun h => ?_⟩
    · rcases (hmem x).1 (by_contra fun h => hx (Or.inl ⟨hxΛ, h⟩)) with h | ⟨i, hi⟩
      exacts [Or.inl h, Or.inr ⟨i, fun hp => hx (Or.inr ⟨i, hp, hi⟩), hi⟩]
    · have hxA : x ∈ A := (hmem x).2 (h.imp_right fun ⟨i, _, hi⟩ => ⟨i, hi⟩)
      refine ⟨hA hxA, ?_⟩
      rintro (⟨_, h'⟩ | ⟨j, hpj, hj⟩)
      · exact h' hxA
      rcases h with h | ⟨i, hpi, hi⟩
      · exact disjoint_left.1 (hDX j) h hj
      · exact disjoint_left.1 (hXX fun h : i = j => hpi (h ▸ hpj)) hi hj
  rw [MState.regionEntropy_pureState_sdiff ψ hψ, (pureState ψ hψ).regionEntropy_congr hset _
    (union_subset hD (biUnion_subset.2 fun i _ => hX i))]
  exact regionEntropy_union_biUnion_le _ hD _ hX (fun i _ => hDX i)
    fun i _ j _ hij => hXX hij

/-- D11.1 **Lemma 11.1** (two-family entropy cancellation). Let `ψ` be pure on a finite tensor
product with site set `Λ`, `A = D ⊔ ⋃_{i∈𝓘₀} Xᵢ ⊔ ⋃_{i∈𝓘₁} Xᵢ ⊆ Λ` a partition into disjoint
sets, each `𝓘_f` finite and ordered, `B = Λ \ A`. If
`I_ψ(Xᵢ : B ∪ ⋃_{j∈𝓘_f, j<i} X_j) ≤ εᵢ` (`f ∈ {0,1}`, `i ∈ 𝓘_f`), then
`S_ψ(A) ≤ S_ψ(D) + ½ ∑ᵢ εᵢ`. -/
theorem lemma_11_1 : TwoFamilyCancellation σ loc ℂ := by
  intro Λ ψ hψ A D hA hD m X hX f ε hAD hDX hXX hε
  have hB : Λ \ A ⊆ Λ := sdiff_subset
  have key (c : Fin 2) : (pureState ψ hψ).regionEntropy hA +
      ∑ i ∈ univ.filter (f · = c), (pureState ψ hψ).regionEntropy (hX i) -
        ∑ i ∈ univ.filter (f · = c), ε i ≤ (pureState ψ hψ).regionEntropy hD +
      ∑ i ∈ univ.filter fun i => ¬f i = c, (pureState ψ hψ).regionEntropy (hX i) := by
    -- D11.1.1
    have h1 := step_11_1_1 (pureState ψ hψ).toSubState hB (univ.filter (f · = c)) hX
    -- D11.1.2: `S(Xᵢ | Jᵢ) = S(Xᵢ) - I(Xᵢ : Jᵢ) ≥ S(Xᵢ) - εᵢ`
    have h2 : ∑ i ∈ univ.filter (f · = c), ((pureState ψ hψ).regionEntropy (hX i) - ε i) ≤
        ∑ i ∈ univ.filter (f · = c), condEntropy (pureState ψ hψ).toSubState (hX i)
          (union_subset hB (biUnion_subset.2 fun j _ => hX j) :
            Λ \ A ∪ ((univ.filter (f · = c)).filter (· < i)).biUnion X ⊆ Λ) := by
      refine sum_le_sum fun i hi => ?_
      have hJ : (univ.filter (f · = c)).filter (· < i) =
          univ.filter fun j => f j = f i ∧ j < i := by
        rw [filter_filter, (mem_filter.1 hi).2]
      have h := hε i
      have hm : ∀ {Y Y' : Finset σ} (hY : Y ⊆ Λ) (hY' : Y' ⊆ Λ), Y = Y' →
          (pureState ψ hψ).mutualInfo (hX i) hY = (pureState ψ hψ).mutualInfo (hX i) hY' := by
        rintro _ _ _ _ rfl; rfl
      rw [hm _ (union_subset hB (biUnion_subset.2 fun j _ => hX j))
        (congrArg (Λ \ A ∪ ·.biUnion X) hJ.symm), SubState.mutualInfo_def] at h
      simp only [condEntropy]
      linarith
    -- D11.1.3: purity, `S(B) = S(A)`
    have h3 := MState.regionEntropy_pureState_sdiff ψ hψ hA
    -- D11.1.4
    have h4 := step_11_1_4 ψ hψ hA hD hX (f · = c) hAD hDX hXX
    -- D11.1.5
    rw [sum_sub_distrib] at h2
    linarith
  -- D11.1.6: add `f = 0` and `f = 1`; every `S(Xᵢ)` cancels
  have h0 := key 0
  have h1 := key 1
  have hc : ∀ i, ¬f i = 0 ↔ f i = 1 := fun i => by generalize f i = c; fin_cases c <;> decide
  have hc' : ∀ i, ¬f i = 1 ↔ f i = 0 := fun i => by generalize f i = c; fin_cases c <;> decide
  have hsum := sum_filter_add_sum_filter_not univ (f · = 0) ε
  rw [filter_congr fun i _ => hc i] at h0 hsum
  rw [filter_congr fun i _ => hc' i] at h1
  linarith

end D111

/-! ## 11.8 Proof of the area law -/

section D1126

open AreaLaw.Geometry

/-- D11.26.2, the scale threshold. With `α = p/(p+1)` and `ε = ℓ = 10⁻⁵`, every radius
`r ≤ C_M n^{(1-ε)/α}` has `L + 2r < n^β`, `L = ⌊n^{1-ℓ}⌋`, for all `n` beyond a threshold. -/
theorem step_11_26_2_threshold (CM : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ r : ℕ,
      (r : ℝ) ≤ CM * (n : ℝ) ^ ((1 - (1 / 100000 : ℝ)) / ((p : ℝ) / (p + 1))) →
      (collarWidth n + 2 * r : ℝ) < (n : ℝ) ^ β := by
  set γ : ℝ := (1 - (1 / 100000 : ℝ)) / ((p : ℝ) / (p + 1))
  have ha : 0 < β - (1 - 1 / 100000) := by simp only [β]; norm_num
  have hb : 0 < β - γ := by simp only [β, γ, p]; norm_num
  have hlim : Filter.Tendsto (fun x : ℝ => x ^ (-(β - (1 - 1 / 100000))) +
      2 * CM * x ^ (-(β - γ))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop ha).add ((tendsto_rpow_neg_atTop hb).const_mul (2 * CM))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (hlim.eventually (gt_mem_nhds one_pos)))
  refine ⟨max N 2, le_max_right _ _, fun n hn r hr => ?_⟩
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le two_pos (le_max_right N 2)).trans_le hn
  have h1 := hN n ((le_max_left _ _).trans hn)
  have hβ : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn0 _
  have e1 : (n : ℝ) ^ (1 - 1 / 100000 : ℝ) = (n : ℝ) ^ β * (n : ℝ) ^ (-(β - (1 - 1 / 100000))) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have e2 : (n : ℝ) ^ γ = (n : ℝ) ^ β * (n : ℝ) ^ (-(β - γ)) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hL : (collarWidth n : ℝ) ≤ (n : ℝ) ^ (1 - 1 / 100000 : ℝ) := Nat.floor_le (by positivity)
  calc (collarWidth n + 2 * r : ℝ) ≤ (n : ℝ) ^ (1 - 1 / 100000 : ℝ) + 2 * (CM * (n : ℝ) ^ γ) := by
        linarith
    _ = (n : ℝ) ^ β * ((n : ℝ) ^ (-(β - (1 - 1 / 100000))) + 2 * CM * (n : ℝ) ^ (-(β - γ))) := by
        rw [e1, e2]; ring
    _ < (n : ℝ) ^ β * 1 := mul_lt_mul_of_pos_left h1 hβ
    _ = (n : ℝ) ^ β := mul_one _

/-- D11.26.2. Propositions 9.6 and 10.2 with `M = 100` apply to every template beyond one
threshold `n_*`: for a template `T` of scale `n ≥ n_*` separated from the cut, with
`L = ⌊n^{1-ℓ}⌋ ≤ s₀`, `X = A ∩ T` and `S = A ∩ T_L`, there is a radius `r` with `L + 2r < n^β`
and `I_Ω(X' : J) ≤ C n^{-100}` for every `X' ⊆ X` and every `J ⊆ Λ \ N^Λ_{2r}(S)`. -/
theorem step_11_26_2 {q R : ℕ} {J Δ : ℝ} (prop_9_6 : CollarBound ℂ q R J Δ)
    (prop_10_2 : Amplification ℂ q R J Δ p) (D₀ : ℝ) (hD₀ : 2 * R + 10 < D₀) :
    ∃ Ctpl C : ℝ, 0 ≤ C ∧ ∃ nStar : ℕ, 1 ≤ nStar ∧
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n s : ℕ),
      IsTemplate Ctpl n s T → IsSeparatedFromCut D₀ s Λ A T → collarWidth n ≤ s → nStar ≤ n →
      ∃ r : ℕ, (collarWidth n + 2 * r : ℝ) < (n : ℝ) ^ β ∧
        ∀ (X' : Finset (ℤ × ℤ)) (hX' : X' ⊆ A ∩ T) (Y : Finset (ℤ × ℤ))
          (hY : Y ⊆ Λ \ graphNbhd Λ (A ∩ ambientDilation T (collarWidth n)) (2 * r)),
          (pureState Ω hΩ).mutualInfo (hX'.trans (inter_subset_left.trans hA))
            (hY.trans sdiff_subset) ≤ C * ((n : ℝ) ^ 100)⁻¹ := by
  obtain ⟨Ctpl, hcol⟩ := prop_9_6 D₀ hD₀
  obtain ⟨C₁, n₁, hcol⟩ := hcol Ctpl le_rfl
  obtain ⟨CM, n₂, hamp⟩ := prop_10_2 (max C₁ 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
    100 (by norm_num)
  obtain ⟨N, hN2, hN⟩ := step_11_26_2_threshold CM
  refine ⟨Ctpl, max CM 0, le_max_right _ _, max (max n₁ n₂) N, le_max_of_le_right (by omega),
    fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s htpl hsep hL hn => ?_⟩
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  -- Proposition 9.6
  obtain ⟨hI, hbX, hbS, hbSX, hcard⟩ := hcol Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s htpl hsep hL hn₁
  have hC : C₁ ≤ max C₁ 1 := le_max_left _ _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Proposition 10.2, `M = 100`
  obtain ⟨r, hr, hout, -⟩ := hamp Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n (hN2.trans hnN) hn₂
    (hcard.trans (mul_le_mul_of_nonneg_right hC (by positivity)))
    (hbX.trans (mul_le_mul_of_nonneg_right hC hn0))
    (hbSX.trans (mul_le_mul_of_nonneg_right hC hn0))
    (hbS.trans (mul_le_mul_of_nonneg_right hC hn0))
    (hI.trans (mul_le_mul_of_nonneg_right hC (by positivity)))
  exact ⟨r, hN n hnN r hr, fun X' hX' Y hY => (hout X' hX' Y hY).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩

/-- D11.26.3, for a graph `G` on a pseudo-emetric space whose edges have length at most `1`
(the square lattice in the sup-norm). A graph path of length `≤ r` from `S₀` stays within
ambient distance `L + r` of `T` when every point of `S₀` is within `L` of `T`; so if the cut
endpoints and every point of `Y ⊆ Λ` are farther than `L + r` from `T`, then
`(Λ \ A) ∪ Y ⊆ Λ \ N^Λ_r(S₀)` for `S₀ ⊆ A`, the whole union at once. -/
theorem step_11_26_3 {σ : Type*} [DecidableEq σ] [PseudoEMetricSpace σ] (G : SimpleGraph σ)
    [DecidableRel G.Adj] (hG : ∀ x y, G.Adj x y → edist x y ≤ 1) {Λ A S₀ T Y : Finset σ}
    {L r : ℕ} (hS₀A : S₀ ⊆ A) (hS₀ : ∀ x ∈ S₀, Metric.infEDist x (T : Set σ) ≤ L)
    (hY : Y ⊆ Λ)
    (hcut : ∀ z ∈ GraphDomain.cutEndpoints G Λ A, ((L + r : ℕ) : ℝ≥0∞) < Metric.infEDist z T)
    (hrem : ∀ y ∈ Y, ((L + r : ℕ) : ℝ≥0∞) < Metric.infEDist y T) :
    (Λ \ A) ∪ Y ⊆ Λ \ GraphDomain.graphNbhd G Λ S₀ r := by
  -- a graph step moves at most `1` in the ambient metric
  have hlen : ∀ {u w : Λ} (p : (G.induce (Λ : Set σ)).Walk u w),
      edist (u : σ) (w : σ) ≤ p.length := by
    intro u w p
    induction p with
    | nil => simp
    | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
      exact (edist_triangle _ _ _).trans (add_le_add (hG _ _ h) ih)
  -- the ambient distance to `T` grows by at most the path length
  have hgrow : ∀ (x : σ) (y : Λ) (z : Λ) (p : (G.induce (Λ : Set σ)).Walk y z), x = y →
      x ∈ S₀ → p.length ≤ r → Metric.infEDist (z : σ) T ≤ ((L + r : ℕ) : ℝ≥0∞) := by
    rintro x y z p rfl hx hp
    calc Metric.infEDist (z : σ) T ≤ Metric.infEDist (y : σ) T + edist (z : σ) (y : σ) :=
          Metric.infEDist_le_infEDist_add_edist
      _ ≤ L + r := by
          rw [edist_comm]
          exact add_le_add (hS₀ _ hx) ((hlen p).trans (by exact_mod_cast hp))
      _ = ((L + r : ℕ) : ℝ≥0∞) := by push_cast; rfl
  intro x hx
  have hxΛ : x ∈ Λ := (mem_union.1 hx).elim (fun h => (mem_sdiff.1 h).1) (fun h => hY h)
  refine mem_sdiff.2 ⟨hxΛ, fun hxN => ?_⟩
  have hinf := (mem_filter.1 hxN).2
  -- a nearest point `y ∈ S₀`
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ S₀, GraphDomain.domainEDist G Λ x y ≤ r := by
    by_contra! h
    refine absurd hinf (not_le.2 ?_)
    rcases S₀.eq_empty_or_nonempty with hS | hS
    · simp [hS]
    · obtain ⟨y, hy, hmin⟩ := S₀.exists_min_image (GraphDomain.domainEDist G Λ x) hS
      exact lt_of_lt_of_le (h y hy) (le_iInf₂ fun z hz => hmin z hz)
  have hyΛ : y ∈ Λ := by
    by_contra hyΛ
    simp [GraphDomain.domainEDist, hyΛ] at hxy
  rw [GraphDomain.domainEDist_eq G ⟨x, hxΛ⟩ ⟨y, hyΛ⟩] at hxy
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (hxy.trans_lt (ENat.natCast_lt_top r)).ne
  have hpr : p.reverse.length ≤ r := by
    rw [SimpleGraph.Walk.length_reverse]; exact_mod_cast hp ▸ hxy
  rcases mem_union.1 hx with hxB | hxY
  · -- the path from `y ∈ A` to `x ∉ A` meets a cut endpoint `z`
    obtain ⟨z, hz, p', hp'⟩ := GraphDomain.exists_cutEndpoints_of_walk G p.reverse
      (D := A) (by simp [hS₀A hy, (mem_sdiff.1 hxB).2])
    exact absurd (hgrow y ⟨y, hyΛ⟩ z p' rfl hy (hp'.trans hpr)) (not_le.2 (hcut _ hz))
  · exact absurd (hgrow y ⟨y, hyΛ⟩ ⟨x, hxΛ⟩ p.reverse rfl hy hpr) (not_le.2 (hrem x hxY))

/-- The square-lattice edges of the frozen statements have sup-norm length `1`. -/
theorem edist_le_one_of_adj {x y : ℤ × ℤ} (h : squareLattice.Adj x y) : edist x y ≤ 1 := by
  simp only [squareLattice, SimpleGraph.boxProd_adj, SimpleGraph.hasse_adj,
    Order.covBy_iff_add_one_eq] at h
  have h1 : |x.1 - y.1| ≤ (1 : ℤ) := by rw [abs_le]; omega
  have h2 : |x.2 - y.2| ≤ (1 : ℤ) := by rw [abs_le]; omega
  rw [edist_dist, Prod.dist_eq, Int.dist_eq, Int.dist_eq, ENNReal.ofReal_le_one]
  exact max_le (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- Points of the dilation `T_L` are within sup-norm distance `L` of `T`. -/
theorem infEDist_le_of_mem_ambientDilation {T : Finset (ℤ × ℤ)} {L : ℕ} {x : ℤ × ℤ}
    (hx : x ∈ ambientDilation T L) : Metric.infEDist x (T : Set (ℤ × ℤ)) ≤ L := by
  obtain ⟨t, ht, v, hv, rfl⟩ := mem_add.1 hx
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_Icc.1 hv)
  refine (Metric.infEDist_le_edist_of_mem (mem_coe.2 ht)).trans ?_
  rw [edist_dist, Prod.dist_eq, Int.dist_eq, Int.dist_eq, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal (max_le ?_ ?_)
  · have : |t.1 + v.1 - t.1| ≤ (L : ℤ) := by rw [abs_le]; simp at h1 h3; omega
    exact_mod_cast this
  · have : |t.2 + v.2 - t.2| ≤ (L : ℤ) := by rw [abs_le]; simp at h2 h4; omega
    exact_mod_cast this

/-- The set clearance `dist_∞(T, Y)` bounds the distance from each point of `Y` to `T`. -/
theorem ambientEDist_le_infEDist {T Y : Finset (ℤ × ℤ)} {y : ℤ × ℤ} (hy : y ∈ Y) :
    ambientEDist T Y ≤ Metric.infEDist y (T : Set (ℤ × ℤ)) :=
  Metric.le_infEDist.2 fun t ht => (iInf₂_le t ht).trans
    ((Metric.infEDist_le_edist_of_mem (mem_coe.2 hy)).trans (edist_comm _ _).le)

/-- D11.26.3 on the square lattice: if `L + 2r < n^β`, `dist_∞(T, Z_A) > 2n^β` and
`dist_∞(T, Y) > 2n^β` for `Y ⊆ Λ`, then `(Λ \ A) ∪ Y ⊆ Λ \ N^Λ_{2r}(A ∩ T_L)`. -/
theorem step_11_26_3_two {Λ A T Y : Finset (ℤ × ℤ)} {n L r : ℕ} (hY : Y ⊆ Λ)
    (hLr : (L + 2 * r : ℝ) < (n : ℝ) ^ β)
    (hcut : ENNReal.ofReal (2 * (n : ℝ) ^ β) < ambientEDist T (cutEndpoints Λ A))
    (hrem : ENNReal.ofReal (2 * (n : ℝ) ^ β) < ambientEDist T Y) :
    (Λ \ A) ∪ Y ⊆ Λ \ graphNbhd Λ (A ∩ ambientDilation T L) (2 * r) := by
  have hsmall : ((L + 2 * r : ℕ) : ℝ≥0∞) < ENNReal.ofReal (2 * (n : ℝ) ^ β) := by
    have hpos : 0 < (n : ℝ) ^ β := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso; simp only [Nat.cast_zero] at hLr
        rw [Real.zero_rpow (by simp only [β]; norm_num)] at hLr
        linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) L]
      · exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    push_cast; linarith
  exact step_11_26_3 squareLattice (fun _ _ => edist_le_one_of_adj) inter_subset_left
    (fun x hx => infEDist_le_of_mem_ambientDilation (mem_inter.1 hx).2) hY
    (fun z hz => hsmall.trans (hcut.trans_le (ambientEDist_le_infEDist hz)))
    (fun y hy => hsmall.trans (hrem.trans_le (ambientEDist_le_infEDist hy)))

end D1126

end AreaLaw
