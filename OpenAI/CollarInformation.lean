import OpenAI.Scan.CollarComparison
import OpenAI.Scan.Budgets
import OpenAI.ImprovedBoxEstimate
import OpenAI.TemplateEntropy
import OpenAI.CollarEntropyIdentity
import OpenAI.CollarReduction
import OpenAI.Embedding
import OpenAI.Scan.TemplateTestGeometry
import OpenAI.Scan.SourceScanTerminalRegions
import OpenAI.Scan.SourceScanTruncation

/-!
# The collar mutual-information bound

The mutual-information inequality (9.16) of Proposition 9.6 [OAI265, §9.5]: for a template `T`
separated from the cut, `X = A ∩ T` and `S₀ = A ∩ T_L`, `I_Ω(X : Λ \ S₀) ≤ C n^{1-ε}`.

A truncated ground state `Ωt` at trace distance `O(n^{-500})` from `Ω` carries a probability
family of leaf partitions `X, U, Y, V` of `Λ`, with `X ∪ U ∪ Y ⊆ S₀`, whose average of
`2 S(X) + g_pre - g_post` is at most `C n^{1-ε}`
(`OpenAI.exists_truncated_collar_leaf_family`).  At every leaf this quantity is
`I(X : V) + I(X : YV) ≥ 2 I(X : Λ \ S₀)` (eq. (9.20)), and Lemma 2.1 moves the mutual
information from `Ωt` back to `Ω` at the cost of `O(n^{-248})`, since only `log dim X = O(n²)`
enters.

## Main statements

* `OpenAI.exists_truncated_collar_leaf_family`: the leaf-averaged bound for a truncated state.
* `OpenAI.collarInformationBound_complex`: `CollarInformationBound` over `ℂ`.
* `OpenAI.collarInformationBound`: `CollarInformationBound` over every `RCLike` field.

## Implementation notes

The leaf bound is stated over `ℂ`, where the scanner layer lives; `collarInformationBound`
transfers the conclusion to `𝕜` through `OpenAI.toComplex`, which preserves admissibility, the
eigenvector equation, the gap and every mutual information.
-/

namespace OpenAI

open Arealaw Matrix

/-- A cut of the sites of `Λ` and its image region carry the same entropy, for any proof that
the image lies in `Λ`. -/
theorem regionEntropy_eq_finiteProduct_of_map_eq {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (hΩ : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1)
    {Y : Finset ↥(Λ : Set (ℤ × ℤ))} {Z : Finset (ℤ × ℤ)}
    (hYZ : Y.map (Function.Embedding.subtype _) = Z) (hZ : Z ⊆ Λ) :
    (pureState (WithLp.ofLp Ω) hΩ).regionEntropy hZ =
      FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ω Y := by
  rw [← regionalEntropy_eq_finiteProduct Λ q Ω hΩ Y]
  exact (pureState (WithLp.ofLp Ω) hΩ).toSubState.regionEntropy_congr hYZ.symm _ _

/-- The image of the complement of a cut of the sites of `Λ` is the complement in `Λ` of its
image. -/
theorem map_embeddingSubtype_compl {Λ : Finset (ℤ × ℤ)} (Y : Finset ↥(Λ : Set (ℤ × ℤ))) :
    Yᶜ.map (Function.Embedding.subtype _) = Λ \ Y.map (Function.Embedding.subtype _) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_compl, Function.Embedding.coe_subtype, Finset.mem_sdiff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun ⟨y', hy', h⟩ => hy (Subtype.ext h ▸ hy')⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨⟨x, hx⟩, fun h => hx' ⟨_, h, rfl⟩, rfl⟩

/-- **The truncated collar leaf bound** [OAI265, §9.5, proof of Proposition 9.6,
eqs. (9.17)–(9.20)].  With the quantifiers of `CollarBound`, at every large `n` there is a unit
vector `Ωt` (the truncated ground state of Proposition 4.5) at trace distance at most
`C n^{-500}` from `Ω`, and a probability family of leaf partitions of `Λ` into
`X = A ∩ T`, `U`, `Y` and `V = Λ \ (X ∪ U ∪ Y)` with `X ∪ U ∪ Y ⊆ S₀ = A ∩ T_L`, such that
`2 S(X) + ⟨(S(XU) + S(V) - S(Y)) - (S(U) + S(UY) - S(Y))⟩ ≤ C n^{1-ε}`, `ε = 10⁻⁵`, all
entropies of `Ωt`. -/
theorem exists_truncated_collar_leaf_family (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) :
    ∀ D₀ : ℝ, 2 * R + 10 < D₀ → ∃ Ctpl₀ : ℝ, ∀ Ctpl : ℝ, Ctpl₀ ≤ Ctpl → ∃ C : ℝ, ∃ n₀ : ℕ,
    ∀ Λ : Finset (ℤ × ℤ),
    ∀ Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ,
      IsAdmissible Λ R J Φ →
    ∀ (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n s₀ : ℕ),
      IsTemplate Ctpl n s₀ T → IsSeparatedFromCut D₀ s₀ Λ A T →
      collarWidth n ≤ s₀ → n₀ ≤ n →
    ∃ (Ωt : Reg (Qudits q) Λ → ℂ) (hΩt : star Ωt ⬝ᵥ Ωt = 1),
      (pureState Ωt hΩt).toSubState.D₁ (pureState Ω hΩ).toSubState ≤
        C * (n : ℝ) ^ (-500 : ℝ) ∧
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (U Y : ι → Finset (ℤ × ℤ))
        (hU : ∀ j, U j ⊆ Λ) (hY : ∀ j, Y j ⊆ Λ),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
        (∀ j, Disjoint (A ∩ T) (U j) ∧ Disjoint (A ∩ T) (Y j) ∧ Disjoint (U j) (Y j) ∧
          A ∩ T ∪ U j ∪ Y j ⊆ A ∩ ambientDilation T (collarWidth n)) ∧
        2 * (pureState Ωt hΩt).regionEntropy (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ) +
            ∑ j, w j *
              (((pureState Ωt hΩt).regionEntropy
                    (Finset.union_subset (Finset.inter_subset_left.trans hA : A ∩ T ⊆ Λ)
                      (hU j)) +
                  (pureState Ωt hΩt).regionEntropy
                    (Finset.sdiff_subset : Λ \ (A ∩ T ∪ U j ∪ Y j) ⊆ Λ) -
                  (pureState Ωt hΩt).regionEntropy (hY j)) -
                ((pureState Ωt hΩt).regionEntropy (hU j) +
                  (pureState Ωt hΩt).regionEntropy (Finset.union_subset (hU j) (hY j)) -
                  (pureState Ωt hΩt).regionEntropy (hY j))) ≤
          C * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by
  have : NeZero q := ⟨by omega⟩
  intro D₀ hD₀
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  -- The constants are fixed in the order the paper fixes them: the truncation radius, the
  -- template constant, the entropy input, then the sharp comparison at those values.
  obtain ⟨Ctr, hCtr, Cb, hCb1, hev1⟩ :=
    Scan.exists_sourceScan_truncation Scan.finalExponents q R hJ hΔ (CT := 4) (by norm_num)
  obtain ⟨Ctpl₁, hCtpl₁, hgeom⟩ := Scan.isTemplate_test_geometry hCtr.le
  obtain ⟨Ctpl₂, hent⟩ := templateEntropy_le_of_boxEntropy_le (𝕜 := ℂ) (q := q) (R := R)
    (J := J) (Δ := Δ)
  -- Proposition 9.5 with Lemma 9.4 gives the entropy input (9.4) at `e = e_*`.
  obtain ⟨Cbox, -, hbox⟩ := improved_box_estimate q R J Δ hq hJ hΔ
  obtain ⟨C', hC'⟩ := hent Cbox _ (by norm_num [Exponents.boxError])
    (by norm_num [Exponents.boxError]) hbox
  have hg : 0 < Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (SpectralFilter.positiveNormalization_pos 1 (Δ / 2) J)
  set g := Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J with hg_def
  set Ce : ℝ := max C' 0 + 1 with hCe
  obtain ⟨C₁₂, N₁₂, h12⟩ := Scan.sourceScan_collar_leaf_bound q R (Ctr := Ctr) (CT := 4)
    (Ce := Ce) (g₀ := g / 2) (ϑ := 2 / g) (Cb := Cb) hJ hΔ hCtr (by norm_num) (by positivity)
    (by positivity) (by linarith)
  refine ⟨max Ctpl₁ Ctpl₂, fun Ctpl hCtpl => ?_⟩
  obtain ⟨N₁₀, hN₁₀⟩ := hgeom Ctpl (le_of_max_le_left hCtpl)
  obtain ⟨Csf, hsf⟩ := Scan.eventually_scaleFacts Scan.finalExponents
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    (hev1.and (hsf.and (Scan.eventually_sourceScan_scales Scan.finalExponents hCtr.le)))
  refine ⟨max C₁₂ Cb, max (max N₁₂ N₁₀) N₁,
    fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hTt hsep hL hn => ?_⟩
  have hn12 : N₁₂ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn10 : N₁₀ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : N₁ ≤ n := (le_max_right _ _).trans hn
  obtain ⟨htrunc, hsfn, hscn⟩ := hN₁ n hn1
  have hT : T.Nonempty := hTt.2.2.1
  obtain ⟨hcard, hrows, hclear⟩ := hN₁₀ D₀ (by linarith) n s₀ Λ A T hTt hsep hL hn10
  rw [← Scan.finalExponents_L] at hrows hclear hL
  -- Any order on the supports serves: the scan lemmas hold for every one.
  let : LinearOrder (supports Λ R) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  set S := Scan.sourceScan Scan.finalExponents Ctr R Λ A T hT n with hSdef
  have hΩe : ‖WithLp.toLp 2 Ω‖ = 1 := (norm_toLp_eq_one_iff Ω).2 hΩ
  obtain ⟨e, Ωt, hΩt, heig, he0, he1, hpsd, hD, htransfer, hmom, E, hmass, hwin⟩ :=
    htrunc Λ A T hA hT Φ hΦ (WithLp.toLp 2 Ω) hΩe E₀ hE hgap hcard hrows hclear
  have hn1' : 1 ≤ n := hTt.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
  have hn0 : (0 : ℝ) < n := by linarith
  have hΩt' := star_dotProduct_self_eq_one_of_norm_eq_one hΩt
  have hCe1 : 1 ≤ Ce := by have := le_max_right C' 0; linarith
  have hC'Ce : max C' 0 ≤ Ce := by linarith
  have hs₀n : s₀ ≤ n := by
    have := hTt.twentyFour_mul_add_one_le (hCtpl₁.trans (le_of_max_le_left hCtpl)); omega
  have h200 : (n : ℝ) ^ (-200 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnR (by norm_num)
  have hC'n := hC' Ctpl (le_of_max_le_right hCtpl) D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀
    hTt hsep
  have hXsmap : (S.A.filter fun x => x.val ∈ T).map (Function.Embedding.subtype _) = A ∩ T := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Function.Embedding.coe_subtype,
      Finset.mem_inter]
    constructor
    · rintro ⟨y, ⟨hyA, hyT⟩, rfl⟩
      exact ⟨Finset.mem_subtype.mp hyA, hyT⟩
    · rintro ⟨hxA, hxT⟩
      exact ⟨⟨x, hA hxA⟩, ⟨Finset.mem_subtype.mpr hxA, hxT⟩, rfl⟩
  have hprefix : ∀ j : ℕ, (Scan.positiveDepthPrefix S.A S.depth (j : ℤ)).map
      (Function.Embedding.subtype _) = A ∩ (ambientDilation T j \ T) := by
    intro j
    ext x
    simp only [Finset.mem_map, Scan.positiveDepthPrefix, Finset.mem_filter,
      Function.Embedding.coe_subtype, Finset.mem_inter, Finset.mem_sdiff]
    have h0 : ∀ y : ℤ × ℤ, 0 < Scan.ambientDepth T hT y ↔ y ∉ T := fun y => by
      have h := Scan.ambientDepth_le_iff_mem_dilation T hT y 0
      rw [ambientDilation_zero, Nat.cast_zero] at h
      rw [← not_le, h]
    constructor
    · rintro ⟨y, ⟨hyA, hy0, hyj⟩, rfl⟩
      exact ⟨Finset.mem_subtype.mp hyA,
        (Scan.ambientDepth_le_iff_mem_dilation T hT y.val j).mp hyj, (h0 y.val).mp hy0⟩
    · rintro ⟨hxA, hxj, hxT⟩
      exact ⟨⟨x, hA hxA⟩, ⟨Finset.mem_subtype.mpr hxA, (h0 x).mpr hxT,
        (Scan.ambientDepth_le_iff_mem_dilation T hT x j).mpr hxj⟩, rfl⟩
  -- The entropy inputs of the comparison, moved from `Ω` to `Ωt` at cost `n^{-200}`.
  have hSx : FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt
      (S.A.filter fun x => x.val ∈ T) ≤ Ce * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
    rw [← regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' hXsmap
      (Finset.inter_subset_left.trans hA)]
    have h1 := htransfer (A ∩ T) (Finset.inter_subset_inter_left (subset_ambientDilation T _))
    have h2 := hC'n.1
    have h3 : C' * n * (s₀ : ℝ) ^ (Exponents.boxError : ℝ) ≤
        max C' 0 * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
      rw [Real.rpow_add hn0, Real.rpow_one]
      have : (s₀ : ℝ) ^ (Exponents.boxError : ℝ) ≤ (n : ℝ) ^ (Exponents.boxError : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hs₀n)
          (by norm_num [Exponents.boxError])
      have h0 : 0 ≤ (s₀ : ℝ) ^ (Exponents.boxError : ℝ) := by positivity
      calc C' * n * (s₀ : ℝ) ^ (Exponents.boxError : ℝ)
          ≤ max C' 0 * n * (s₀ : ℝ) ^ (Exponents.boxError : ℝ) := by gcongr; exact le_max_left _ _
        _ ≤ max C' 0 * n * (n : ℝ) ^ (Exponents.boxError : ℝ) := by gcongr
        _ = _ := by ring
    have h4 : (1 : ℝ) ≤ (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) :=
      Real.one_le_rpow hnR (by norm_num [Exponents.boxError])
    have h5 : max C' 0 * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) + 1 ≤
        Ce * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by rw [hCe]; nlinarith
    linarith [(abs_le.mp h1).2]
  have hK1 : 1 ≤ Scan.finalExponents.K n := hsfn.one_le_K
  have hm1 : 1 ≤ Scan.finalExponents.m n := hsfn.one_le_m
  have hKL : 8 * Scan.finalExponents.K n * Scan.finalExponents.m n ≤ Scan.finalExponents.L n :=
    hscn.2.2.2.2.2
  have hL1 : 1 ≤ Scan.finalExponents.L n := by nlinarith
  have hsh : ∀ j : Fin (Scan.finalExponents.L n + 1),
      FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q) Ωt
        (Scan.positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤
        Ce * ((n : ℝ) * (Scan.finalExponents.L n : ℝ) ^ (Exponents.boxError : ℝ) + n) := by
    intro j
    have hjL : j.val ≤ Scan.finalExponents.L n := Nat.lt_succ_iff.mp j.isLt
    have hsub : A ∩ (ambientDilation T j.val \ T) ⊆
        A ∩ ambientDilation T (Scan.finalExponents.L n) :=
      Finset.inter_subset_inter_left (Finset.sdiff_subset.trans (ambientDilation_mono T hjL))
    rw [← regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' (hprefix j.val)
      (Finset.inter_subset_left.trans hA)]
    have h1 := htransfer _ hsub
    have h2 := hC'n.2 (Scan.finalExponents.L n) j.val hL1 hL hjL
    have hP : 0 ≤ (n : ℝ) * (Scan.finalExponents.L n : ℝ) ^ (Exponents.boxError : ℝ) := by
      positivity
    have h3 : C' * n * (Scan.finalExponents.L n : ℝ) ^ (Exponents.boxError : ℝ) ≤
        max C' 0 * ((n : ℝ) * (Scan.finalExponents.L n : ℝ) ^ (Exponents.boxError : ℝ)) := by
      rw [← mul_assoc]; gcongr; exact le_max_left _ _
    have h4 : max C' 0 * ((n : ℝ) * (Scan.finalExponents.L n : ℝ) ^ (Exponents.boxError : ℝ)) +
        1 ≤ Ce * ((n : ℝ) * (Scan.finalExponents.L n : ℝ) ^ (Exponents.boxError : ℝ) + n) := by
      rw [hCe]; nlinarith [le_max_right C' 0]
    linarith [(abs_le.mp h1).2]
  have hz := (show (0 : ℝ) < 1 - (n : ℝ) ^ (-100 : ℝ) by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hsfn.two_le_n
    have : (n : ℝ) ^ (-100 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
      (by norm_num)
    linarith).trans_le hmass
  have hEne : E.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hE'
    rw [hE'] at hz
    simp only [Matrix.IsHermitian.spectralRestrictionMass, Finset.sum_empty,
      lt_self_iff_false] at hz
  have : NeZero E.card := ⟨(Finset.card_pos.mpr hEne).ne'⟩
  obtain ⟨ell, hSB⟩ := Scan.exists_isSchmidtBellLabels _ Ωt e hΩt heig _ E hz
  -- The comparison needs no hypothesis on `X = A ∩ T`; an empty `X` is covered.
  obtain ⟨Tr, hTr⟩ := h12 n hn12 Λ A T hA hT hcard hrows hclear Φ hΦ (WithLp.toLp 2 Ω) hΩe Ωt e
    (g / 2) hΩt heig hpsd he0 he1 le_rfl hmom E hmass hwin hSx hsh ell hSB
  have hreg := Scan.sourceScan_terminal_regions Scan.finalExponents Ctr R Λ A T hT n hKL
  dsimp only at hTr hreg
  refine ⟨Ωt.ofLp, hΩt',
    hD.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)), ?_⟩
  let σ := Scan.CollarScan.ActualTerminals.terminalPartition S (S.n * S.m)
  have hK0 : (0 : ℝ) < S.K := by
    exact_mod_cast (show 0 < S.K by change 0 < Scan.finalExponents.K n; omega)
  have hmemS : ∀ y, y ∈ S.truncationSet (Scan.finalExponents.L n) →
      y.val ∈ A ∩ ambientDilation T (Scan.finalExponents.L n) := by
    intro y hy
    obtain ⟨hyA, hyd⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_inter.mpr ⟨Finset.mem_subtype.mp hyA,
      (Scan.ambientDepth_le_iff_mem_dilation T hT y.val _).mp hyd⟩
  classical
  -- The leaves are the pairs (terminal history, band), weighted by `K⁻¹ w_j`.
  refine ⟨Scan.CollarScan.ActualTerminals.terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K,
    inferInstance, fun p => (S.K : ℝ)⁻¹ * Tr.weight p.1,
    fun p => (Scan.positiveNear S.depth (σ p.1 p.2)).map (Function.Embedding.subtype _),
    fun p => (Scan.middle (σ p.1 p.2)).map (Function.Embedding.subtype _),
    fun p => map_embeddingSubtype_subset _, fun p => map_embeddingSubtype_subset _,
    fun p => mul_nonneg (inv_nonneg.mpr hK0.le) (Tr.weight_nonneg _), ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul]
    exact Tr.sum_weight
  · rintro ⟨j, g'⟩
    obtain ⟨-, -, hdX, hdUY, -, hsubT⟩ := hreg j g'
    refine ⟨?_, ?_, (Finset.disjoint_map _).mpr hdUY, ?_⟩
    · rw [← hXsmap]
      exact (Finset.disjoint_map _).mpr
        (Finset.disjoint_of_subset_right Finset.subset_union_left hdX)
    · rw [← hXsmap]
      exact (Finset.disjoint_map _).mpr
        (Finset.disjoint_of_subset_right Finset.subset_union_right hdX)
    · rw [← Scan.finalExponents_L]
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.inter_subset_inter_left (subset_ambientDilation T _) hx
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
          exact hmemS y (hsubT (Finset.mem_union_left _ hy))
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact hmemS y (hsubT (Finset.mem_union_right _ hy))
  · have hXent := regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' hXsmap
      (Finset.inter_subset_left.trans hA)
    refine le_trans (le_of_eq ?_)
      (hTr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    rw [hXent, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    obtain ⟨hrecv, hpnm, -, -, -, -⟩ := hreg j g'
    have e1 : (Scan.receiving (σ j g') false).map (Function.Embedding.subtype _) =
        A ∩ T ∪ (Scan.positiveNear S.depth (σ j g')).map (Function.Embedding.subtype _) := by
      rw [hrecv, Finset.map_union, hXsmap]
    have e2 : ((Scan.receiving (σ j g') false ∪ Scan.middle (σ j g'))ᶜ).map
        (Function.Embedding.subtype _) =
        Λ \ (A ∩ T ∪ (Scan.positiveNear S.depth (σ j g')).map (Function.Embedding.subtype _) ∪
          (Scan.middle (σ j g')).map (Function.Embedding.subtype _)) := by
      rw [map_embeddingSubtype_compl, Finset.map_union, e1]
    have e5 : (Scan.positiveNearMiddle S.depth (σ j g')).map (Function.Embedding.subtype _) =
        (Scan.positiveNear S.depth (σ j g')).map (Function.Embedding.subtype _) ∪
          (Scan.middle (σ j g')).map (Function.Embedding.subtype _) := by
      rw [hpnm, Finset.map_union]
    rw [regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' e1,
      regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' e2,
      regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' e5,
      regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' (Y := Scan.middle (σ j g')) rfl,
      regionEntropy_eq_finiteProduct_of_map_eq Ωt hΩt' (Y := Scan.positiveNear S.depth (σ j g'))
        rfl]
    ring

/-- **The collar mutual-information bound over `ℂ`** [OAI265, Proposition 9.6, eq. (9.16)]. -/
theorem collarInformationBound_complex (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J)
    (hΔ : 0 < Δ) : CollarInformationBound ℂ q R J Δ := by
  intro D₀ hD₀
  obtain ⟨Ctpl₀, hT⟩ := exists_truncated_collar_leaf_family q R J Δ hq hJ hΔ D₀ hD₀
  refine ⟨max Ctpl₀ 24, fun Ctpl hCtpl => ?_⟩
  obtain ⟨C, n₀, hC⟩ := hT Ctpl (le_of_max_le_left hCtpl)
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    (Scan.eventually_continuityCost_le_of_fixed_coefficient (max C 0) 10 (Real.log q)
      (le_max_right _ _) (by norm_num) hlogq)
  refine ⟨max C 0 + 1, max (max n₀ n₁) 1,
    fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hTt hsep hL hn => ?_⟩
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn₁' : n₁ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  obtain ⟨Ωt, hΩt, hD, ι, _, w, U, Y, hU, hY, hw, hsum, hpart, hineq⟩ :=
    hC Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hTt hsep hL hn₀
  have hX : A ∩ T ⊆ Λ := Finset.inter_subset_left.trans hA
  have hW : Λ \ (A ∩ ambientDilation T (collarWidth n)) ⊆ Λ := Finset.sdiff_subset
  have hXS : A ∩ T ⊆ A ∩ ambientDilation T (collarWidth n) :=
    Finset.inter_subset_inter_left (subset_ambientDilation T (collarWidth n))
  have hXW : Disjoint (A ∩ T) (Λ \ (A ∩ ambientDilation T (collarWidth n))) :=
    Finset.disjoint_of_subset_left hXS Finset.disjoint_sdiff
  -- Each leaf bounds twice the mutual information of the truncated state.
  have hleaf : ∀ j, 2 * (pureState Ωt hΩt).mutualInfo hX hW ≤
      2 * (pureState Ωt hΩt).regionEntropy hX +
        (((pureState Ωt hΩt).regionEntropy (Finset.union_subset hX (hU j)) +
            (pureState Ωt hΩt).regionEntropy
              (Finset.sdiff_subset : Λ \ (A ∩ T ∪ U j ∪ Y j) ⊆ Λ) -
            (pureState Ωt hΩt).regionEntropy (hY j)) -
          ((pureState Ωt hΩt).regionEntropy (hU j) +
            (pureState Ωt hΩt).regionEntropy (Finset.union_subset (hU j) (hY j)) -
            (pureState Ωt hΩt).regionEntropy (hY j))) := by
    intro j
    obtain ⟨hXU, hXY, hUY, hsub⟩ := hpart j
    have hcov : A ∩ T ∪ U j ∪ Y j ⊆ Λ :=
      Finset.union_subset (Finset.union_subset hX (hU j)) (hY j)
    have hV : Disjoint (A ∩ T ∪ U j ∪ Y j) (Λ \ (A ∩ T ∪ U j ∪ Y j)) := Finset.disjoint_sdiff
    have h := two_mutualInfo_le_collarLeaf Ωt hΩt hX (hU j) (hY j) Finset.sdiff_subset hXU hXY
      (Finset.disjoint_of_subset_left (by intro x hx; simp [hx]) hV) hUY
      (Finset.disjoint_of_subset_left (by intro x hx; simp [hx]) hV)
      (Finset.disjoint_of_subset_left (by intro x hx; simp [hx]) hV)
      (Finset.union_sdiff_of_subset hcov)
      (Finset.sdiff_subset_sdiff le_rfl hsub)
    linarith
  -- Averaging over the leaves.
  have havg : 2 * (pureState Ωt hΩt).mutualInfo hX hW ≤
      C * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by
    refine le_trans ?_ hineq
    calc 2 * (pureState Ωt hΩt).mutualInfo hX hW
        = ∑ j, w j * (2 * (pureState Ωt hΩt).mutualInfo hX hW) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ j, w j * (2 * (pureState Ωt hΩt).regionEntropy hX +
          (((pureState Ωt hΩt).regionEntropy (Finset.union_subset hX (hU j)) +
              (pureState Ωt hΩt).regionEntropy
                (Finset.sdiff_subset : Λ \ (A ∩ T ∪ U j ∪ Y j) ⊆ Λ) -
              (pureState Ωt hΩt).regionEntropy (hY j)) -
            ((pureState Ωt hΩt).regionEntropy (hU j) +
              (pureState Ωt hΩt).regionEntropy (Finset.union_subset (hU j) (hY j)) -
              (pureState Ωt hΩt).regionEntropy (hY j)))) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hleaf j) (hw j)
      _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  -- The transfer from `Ωt` back to `Ω`.
  have hcard : ((A ∩ T).card : ℝ) ≤ 10 * (n : ℝ) ^ 2 := by
    have h₄ := (hTt.collar_cut_card_le (le_of_max_le_right hCtpl) hsep
      (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]) hL).2.2.2
    exact_mod_cast (Finset.card_le_card hXS).trans h₄
  have hlogcard : Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) (A ∩ T))) ≤
      1 + 10 * (n : ℝ) ^ 2 * Real.log q := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    rw [card_reg_const (fun _ => Fintype.card_fin q), Nat.cast_pow,
      Real.log_mul (Real.exp_pos 1).ne' (pow_pos hq0 _).ne', Real.log_exp, Real.log_pow]
    linarith [mul_le_mul_of_nonneg_right hcard hlogq]
  have hD' : (pureState Ωt hΩt).toSubState.D₁ (pureState Ω hΩ).toSubState ≤
      max C 0 * (n : ℝ) ^ (-500 : ℝ) :=
    hD.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hcost := hn₁ n hn₁' _ hD'
  have htr := abs_mutualInfo_sub_le hX hW hXW (pureState Ωt hΩt) (pureState Ω hΩ)
  have hsqrt : 0 ≤ Real.sqrt ((pureState Ωt hΩt).toSubState.D₁ (pureState Ω hΩ).toSubState) :=
    Real.sqrt_nonneg _
  have hsmall : 8 * Real.sqrt ((pureState Ωt hΩt).toSubState.D₁ (pureState Ω hΩ).toSubState) *
      Real.log (Real.exp 1 * Fintype.card (Reg (Qudits q) (A ∩ T))) ≤ 1 := by
    have hn247 : (n : ℝ) ^ (-247 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    have hlog0 : 0 ≤ 1 + 10 * (n : ℝ) ^ 2 * Real.log q := by positivity
    calc _ ≤ 8 * Real.sqrt ((pureState Ωt hΩt).toSubState.D₁ (pureState Ω hΩ).toSubState) *
          (1 + 10 * (n : ℝ) ^ 2 * Real.log q) :=
          mul_le_mul_of_nonneg_left hlogcard (by positivity)
      _ ≤ 10 * Real.sqrt ((pureState Ωt hΩt).toSubState.D₁ (pureState Ω hΩ).toSubState) *
          (1 + 10 * (n : ℝ) ^ 2 * Real.log q) :=
          mul_le_mul_of_nonneg_right (by linarith) hlog0
      _ ≤ 1 := hcost.trans hn247
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) :=
    Real.one_le_rpow hn1 (by norm_num)
  have hI : (pureState Ω hΩ).mutualInfo hX hW ≤
      (pureState Ωt hΩt).mutualInfo hX hW + 1 := by
    have := (abs_le.1 htr).1
    linarith
  calc (pureState Ω hΩ).mutualInfo hX hW
      ≤ (pureState Ωt hΩt).mutualInfo hX hW + 1 := hI
    _ ≤ max C 0 * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) + (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by
        have hpos : 0 ≤ (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by positivity
        have : C * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) ≤
            max C 0 * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
        have hmax : 0 ≤ max C 0 * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) :=
          mul_nonneg (le_max_right _ _) hpos
        nlinarith
    _ = (max C 0 + 1) * (n : ℝ) ^ (1 - (1 / 100000 : ℝ)) := by ring

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The collar mutual-information bound** [OAI265, Proposition 9.6, eq. (9.16)], over every
`RCLike` field: the statement over `ℂ` applied to the embedded Hamiltonian and vector. -/
theorem collarInformationBound (q R : ℕ) (J Δ : ℝ) (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    CollarInformationBound 𝕜 q R J Δ := by
  intro D₀ hD₀
  obtain ⟨Ctpl₀, h⟩ := collarInformationBound_complex q R J Δ hq hJ hΔ D₀ hD₀
  refine ⟨Ctpl₀, fun Ctpl hCtpl => ?_⟩
  obtain ⟨C, n₀, h⟩ := h Ctpl hCtpl
  refine ⟨C, n₀, fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T n s₀ hT hsep hL hn => ?_⟩
  have hE' : hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)) *ᵥ
      (fun i => toComplex 𝕜 (Ω i)) = (E₀ : ℂ) • (fun i => toComplex 𝕜 (Ω i)) := by
    rw [hamiltonian_map_toComplex, ← toComplex_ofReal (𝕜 := 𝕜)]
    exact (mulVec_map_toComplex_eq_smul_iff _ _ _).2 hE
  have hgap' : HasGlobalGap (hamiltonian Λ (fun X => (Φ X).map (toComplex 𝕜)))
      (fun i => toComplex 𝕜 (Ω i)) E₀ Δ := by
    rw [hamiltonian_map_toComplex]
    exact (hasGlobalGap_map_toComplex_iff _ _ _ _).2 hgap
  have key := h Λ (fun X => (Φ X).map (toComplex 𝕜))
    ((isAdmissible_map_toComplex_iff Λ R J Φ).2 hΦ) (fun i => toComplex 𝕜 (Ω i))
    (star_dotProduct_comp_toComplex_eq_one hΩ) E₀ hE' hgap' A hA T n s₀ hT hsep hL hn
  rw [← pureState_toComplex Ω hΩ] at key
  simpa only [MState.toSubState_toComplex, SubState.mutualInfo_toComplex] using key

end OpenAI
