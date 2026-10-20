import AreaLawRefactored.S10_Amplification.Setup
import AreaLawRefactored.S10_Amplification.Channels
import AreaLawRefactored.S10_Amplification.Lemma101
import AreaLawRefactored.S10_Amplification.ExcitedDecay
import AreaLawRefactored.S10_Amplification.Polar
import AreaLawRefactored.S10_Amplification.Typical
import AreaLawRefactored.S10_Amplification.Restoring
import AreaLawRefactored.S10_Amplification.Information
import AreaLawRefactored.S10_Amplification.Scales

/-!
# §10 Amplifying the collar estimate

Digest `digest/10-amplification.md`, paper `paper/sections/09-amplification.tex`. Graph-level
(`Map.md`, Dimension): a simple graph `G` on a site type `σ` with ball growth `V`; the frozen
`OpenAI.Amplification ℂ` is the `G = squareLattice`, `d = 2` instance.

* `S10_Amplification/Setup.lean`: D10.1 (standing exponents), the clock law, vector norms and
  the shared objects (`blank`, `marg`, `copyVec`, `restoredVec`, `splitN`, `ActsOn`).
* `S10_Amplification/Channels.lean`: §10.1, Lemma 10.1, deterministic channel facts
  (D10.2.1–D10.2.7, D10.2.10).
* `S10_Amplification/Lemma101.lean`: §10.1, Lemma 10.1 (D10.2), kernel, propagation, coupling,
  (A) and (B).
* `S10_Amplification/ExcitedDecay.lean`: D10.3 and D10.13.
* `S10_Amplification/Typical.lean`: D10.5.
* `S10_Amplification/Restoring.lean`: D10.6–D10.10.
* `S10_Amplification/Polar.lean`: D10.14.
* `S10_Amplification/Information.lean`: D10.6.1–2, D10.15.
* `S10_Amplification/Scales.lean`: D10.11, D10.12.4, D10.13.6, D10.15.5–6, D10.16.
* This file: §10.2, Proposition 10.2 (D10.4), and `OpenAI.Amplification ℂ`.
-/

namespace AreaLaw

open Arealaw Matrix GraphDomain Finset
open OpenAI (pureState HasGlobalGap IsSupportedOn)
open scoped Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator Pointwise

section Helpers

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

-- helper
/-- D10.4.1. `I_ρ(∅ : J) = 0`. -/
theorem mutualInfo_empty_left {Λ J : Finset σ} (ρ : Arealaw.MState (Reg loc Λ) ℂ)
    (h : (∅ : Finset σ) ⊆ Λ) (hJ : J ⊆ Λ) : ρ.toSubState.mutualInfo h hJ = 0 := by
  rw [SubState.mutualInfo_def, ρ.regionEntropy_empty,
    SubState.regionEntropy_congr _ (empty_union J) _ hJ]
  ring

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
-- helper
theorem subset_graphNbhd_self (G : SimpleGraph σ) {Λ S : Finset σ} (hS : S ⊆ Λ) (r : ℕ) :
    S ⊆ graphNbhd G Λ S r := fun x hx =>
  (mem_graphNbhd_iff G).2 ⟨hS hx, (Finset.inf_le (f := fun y => domainEDist G Λ x y) hx).trans
    (by unfold domainEDist; rw [dif_pos ⟨hS hx, hS hx⟩, SimpleGraph.edist_self]; exact zero_le)⟩

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
-- helper
/-- Labels `Fin |s|` of the supports `s`: at most `#{Z ∈ s | a Z = y}` anchored at `y`. -/
theorem card_anchor_le (s : Finset (Finset σ)) (a : Finset σ → σ) (y : σ) :
    #{i : Fin #s | a (s.equivFin.symm i).1 = y} ≤ #{Z ∈ s | a Z = y} :=
  card_le_card_of_injOn (fun i => (s.equivFin.symm i).1)
    (fun i hi => mem_filter.2 ⟨(s.equivFin.symm i).2, (mem_filter.1 hi).2⟩)
    (fun _ _ _ _ h => s.equivFin.symm.injective (Subtype.ext h))

omit [∀ i, DecidableEq (loc i)] in
-- helper
/-- D10.15.5. `log dim ℋ_X ≤ |X| log q` when every site has dimension `≤ q`. -/
theorem log_card_reg_le {q : ℕ} (hq : ∀ i, Fintype.card (loc i) ≤ q) (X : Finset σ) :
    Real.log (Fintype.card (Reg loc X)) ≤ #X * Real.log q := by
  rcases (Nat.zero_le (Fintype.card (Reg loc X))).eq_or_lt with h0 | h0
  · rw [← h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q)
  · rw [← Real.log_pow]
    refine Real.log_le_log (by exact_mod_cast h0) ?_
    rw [card_reg]
    exact_mod_cast Finset.prod_le_pow_card _ _ _ fun i _ => hq i

end Helpers

-- helper
theorem vnorm_le_of_sq_le {n : Type*} [Fintype n] {v : n → ℂ} {x : ℝ} (hx : 0 ≤ x)
    (h : vnorm v ^ 2 ≤ x ^ 2) : vnorm v ≤ x :=
  (pow_le_pow_iff_left₀ (vnorm_nonneg v) hx two_ne_zero).1 h


section Reindex

variable {n κ κ' : Type*} [Fintype n] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

omit [Fintype n] [Fintype κ] [Fintype κ'] in
-- helper
/-- Lemma 10.1 (B) takes spectators `κ : Type`: a spectator is moved there by an equivalence
`f : κ' ≃ κ`, through `e = id × f`. -/
theorem kronecker_one_reindex (A : Matrix n n ℂ) (f : κ' ≃ κ) :
    A ⊗ₖ (1 : Matrix κ' κ' ℂ) = (A ⊗ₖ (1 : Matrix κ κ ℂ)).submatrix
      ((Equiv.refl n).prodCongr f) ((Equiv.refl n).prodCongr f) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [kroneckerMap_apply, one_apply, f.injective.eq_iff]

omit [DecidableEq κ] [DecidableEq κ'] in
-- helper
theorem vnorm_comp_equiv (v : n × κ → ℂ) (f : κ' ≃ κ) :
    vnorm (v ∘ (Equiv.refl n).prodCongr f) = vnorm v := by
  rw [vnorm_eq_sqrt, vnorm_eq_sqrt]
  congr 2
  simp only [dotProduct, Pi.star_apply, Function.comp_apply]
  exact ((Equiv.refl n).prodCongr f).sum_comp fun x => star (v x) * v x

-- helper
theorem vnorm_reindex (A : Matrix n n ℂ) (B : Matrix (n × κ) (n × κ) ℂ) (Ω : n → ℂ)
    (ξ : κ → ℂ) (f : κ' ≃ κ) :
    vnorm ((A ⊗ₖ (1 : Matrix κ' κ' ℂ)) *ᵥ (B.submatrix ((Equiv.refl n).prodCongr f)
      ((Equiv.refl n).prodCongr f) *ᵥ tensVec Ω (ξ ∘ f))) =
      vnorm ((A ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ (B *ᵥ tensVec Ω ξ)) := by
  classical
  have h2 : tensVec Ω (ξ ∘ f) = tensVec Ω ξ ∘ (Equiv.refl n).prodCongr f := by
    ext ⟨a, i⟩; rfl
  have h3 : ∀ (M : Matrix (n × κ) (n × κ) ℂ) (u : n × κ → ℂ),
      M.submatrix ((Equiv.refl n).prodCongr f) ((Equiv.refl n).prodCongr f) *ᵥ
        (u ∘ (Equiv.refl n).prodCongr f) = (M *ᵥ u) ∘ (Equiv.refl n).prodCongr f := by
    intro M u
    rw [submatrix_mulVec_equiv]
    congr 2
    ext ⟨a, b⟩
    simp
  rw [kronecker_one_reindex A f, h2, h3, h3, vnorm_comp_equiv]

end Reindex
/-! ## D10.4 Proposition 10.2 -/

/-- D10.4 (Proposition 10.2), graph form. Fix `C₀ > 0`; `ε, β, α` as in D10.1. Let `n ≥ 2`,
`X ⊆ S₀ ⊆ Λ`, `Y = S₀ \ X`, `Z' = Λ \ S₀`. Assume `|S₀| ≤ C₀ n^d`; the cuts of `X`, `Y`, `S₀`
each have `≤ C₀ n` crossing edges; and `𝓘 := I_Ω(X : Z') ≤ C₀ n^{1-ε}`. For every integer
`M ≥ 1` and all sufficiently large `n` there is an integer `r` with `r ≤ C_M n^{(1-ε)/α}` and,
simultaneously for every physical `J ⊆ Λ \ N_{2r}(S₀)`, `I_Ω(X : J) ≤ C_M n^{-M}`; the same for
any subset of `X` in place of `X`. Constants and threshold depend on `C₀, M` (and the standing
data, `p`), not on `Λ, X, S₀`. (`K = 4(M + d + 1)`, the paper's `4(M + 3)` at `d = 2`.) -/
theorem prop_10_2 {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj]
    (V : ℕ → ℕ) (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {K₀ : ℝ}
    {m₀ : ℕ} (hVK : ∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀)
    {loc : σ → Type} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)]
    {q : ℕ} (hq : ∀ i, Fintype.card (loc i) ≤ q) (R : ℕ) {J Δ : ℝ} (hJ0 : 0 ≤ J) (hΔ : 0 < Δ)
    {p : ℕ} (hp : 10 ^ 6 ≤ p) (d : ℕ) (C₀ : ℝ) (hC₀ : 0 < C₀) (M : ℕ) (hM : 1 ≤ M) :
    ∃ C_M : ℝ, ∃ n₀ : ℕ,
    ∀ (Λ : Finset σ) (Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ),
      IsAdmissible G Λ R J Φ →
    ∀ (Ω : Reg loc Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ (X S₀ : Finset σ) (hXS : X ⊆ S₀) (hS₀ : S₀ ⊆ Λ) (n : ℕ), 2 ≤ n → n₀ ≤ n →
      (#S₀ : ℝ) ≤ C₀ * (n : ℝ) ^ d →
      (#(edgeBoundary G Λ X) : ℝ) ≤ C₀ * n → (#(edgeBoundary G Λ (S₀ \ X)) : ℝ) ≤ C₀ * n →
      (#(edgeBoundary G Λ S₀) : ℝ) ≤ C₀ * n →
      (pureState Ω hΩ).toSubState.mutualInfo (hXS.trans hS₀)
          (Finset.sdiff_subset : Λ \ S₀ ⊆ Λ) ≤ C₀ * (n : ℝ) ^ (1 - ε) →
      ∃ r : ℕ, (r : ℝ) ≤ C_M * (n : ℝ) ^ ((1 - ε) / α p) ∧
        ∀ (X' : Finset σ) (hX' : X' ⊆ X) (J : Finset σ)
          (hJ : J ⊆ Λ \ graphNbhd G Λ S₀ (2 * r)),
          (pureState Ω hΩ).toSubState.mutualInfo (hX'.trans (hXS.trans hS₀))
              (hJ.trans Finset.sdiff_subset) ≤ C_M * ((n : ℝ) ^ M)⁻¹ := by
  -- constants, in the order of the D10.4 Pitfall: `p → α`; `M → K → n₀`; `C → C'`
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hα := α_pos hp1
  have hα1 := α_le_one p
  obtain ⟨cstar, hcs, Cp, cp, hcp, hP⟩ := prop_4_3 G V hV (loc := loc) hp1 R J Δ hΔ
  have hg : 0 < Δ / cstar := div_pos hΔ hcs
  obtain ⟨CL, cL, v, hCL, hcL, hv, hL⟩ :=
    lemma_10_1 (loc := loc) (C := Cp) G V hV hVK (μ V R) hα hα1 hcp
  have hK : 1 ≤ 4 * (M + d + 1) := by omega
  obtain ⟨Ct, Ct', Cr, -, -, n₁, hsc⟩ :=
    step_10_11 hg hv hcL hα hα1 hCL hCL hC₀ d m₀ (4 * (M + d + 1)) hK
  obtain ⟨n₂, hty⟩ := step_10_5 G V hV hq R hJ0 hΔ C₀ (4 * (M + d + 1))
  have hlq := Real.log_natCast_nonneg q
  have hCM : 0 ≤ max Cr (24 * (1 + C₀ * Real.log q)) :=
    le_max_of_le_right (by nlinarith [mul_nonneg hC₀.le hlq])
  refine ⟨max Cr (24 * (1 + C₀ * Real.log q)), max 2 (max n₁ n₂), ?_⟩
  intro Λ Φ hΦ Ω hΩ E₀ heig hgap X S₀ hXS hS₀ n hn2 hn hcard hbX hbY hbS h𝓘
  have hn₁ : n₁ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hn₂ : n₂ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- D10.4.1: `X = ∅`
  rcases X.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine ⟨0, by rw [Nat.cast_zero]; exact mul_nonneg hCM (Real.rpow_nonneg hnpos.le _), ?_⟩
    intro X' hX' J hJ
    obtain rfl := subset_empty.1 hX'
    rw [mutualInfo_empty_left]
    exact mul_nonneg hCM (by positivity)
  have : Nonempty σ := ⟨x₀⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fintype.card_pos (α := loc x₀)).trans_le (hq x₀)
  -- `S₀ = X ∪ Y`, `Y = S₀ \ X`
  obtain ⟨Y, hXY, rfl⟩ : ∃ Y, Disjoint X Y ∧ S₀ = X ∪ Y :=
    ⟨S₀ \ X, disjoint_sdiff, (union_sdiff_of_subset hXS).symm⟩
  rw [union_sdiff_cancel_left hXY] at hbY
  have hX : X ⊆ Λ := hXS.trans hS₀
  have hY : Y ⊆ Λ := subset_union_right.trans hS₀
  set 𝓘 := (pureState Ω hΩ).toSubState.mutualInfo hX (sdiff_subset : Λ \ (X ∪ Y) ⊆ Λ)
    with h𝓘def
  have h𝓘' : 𝓘 ≤ C₀ * (n : ℝ) ^ (1 - ε) := h𝓘
  have h𝓘0 : 0 ≤ 𝓘 := mutualInfo_nonneg (pureState Ω hΩ)
    ((disjoint_sdiff : Disjoint (X ∪ Y) (Λ \ (X ∪ Y))).mono_left subset_union_left) hX
    sdiff_subset
  -- D10.11: time `t`, radius `r`
  obtain ⟨ht0, hr1, hM₀1, hdec, hBsc, hAsc, hrad⟩ := hsc n hn₁ 𝓘 h𝓘0 h𝓘'
  set K := 4 * (M + d + 1) with hKdef
  set w : ℝ := (n : ℝ) ^ (3 / 5 : ℝ) with hwdef
  set M₀ := Real.exp ((𝓘 + 3 * w) / 2) with hM₀def
  set t := tStar Ct 𝓘 K n with htdef
  set r := AreaLaw.radius Ct Ct' 𝓘 (α p) K n with hrdef
  have hM₀pos : 0 < M₀ := Real.exp_pos _
  -- labels: the supports, anchored at a chosen site (D10.1, D4.6)
  set anchor : Finset σ → σ := fun Z => if h : Z.Nonempty then h.choose else x₀ with hanchor_def
  have hanchor : ∀ Z ∈ supports G Λ R, anchor Z ∈ Z := fun Z hZ => by
    have hne := ((GraphDomain.mem_supports G).1 hZ).2.1
    simp only [hanchor_def, dif_pos hne]
    exact hne.choose_spec
  obtain ⟨kF, hk₁, hk₂, hk₃, hk₄, -⟩ := hP Λ Φ hΦ Ω hΩ E₀ heig hgap anchor hanchor
  let e := (supports G Λ R).equivFin
  let anc : Fin #(supports G Λ R) → σ := fun i => anchor (e.symm i).1
  let k : Fin #(supports G Λ R) → Matrix (Reg loc Λ) (Reg loc Λ) ℂ := fun i => kF (e.symm i).1
  have hZ : ∀ i, (e.symm i).1 ∈ supports G Λ R := fun i => (e.symm i).2
  have hanc : ∀ i, anc i ∈ Λ := fun i =>
    ((GraphDomain.mem_supports G).1 (hZ i)).1 (hanchor _ (hZ i))
  have hμ : ∀ y, #{i | anc i = y} ≤ μ V R := fun y =>
    (card_anchor_le _ anchor y).trans ((step_2_8 G V hV Λ R y).2.1 anchor hanchor)
  have hk : ∀ i, 0 ≤ k i ∧ k i ≤ 1 := fun i => ⟨(hk₁ _ (hZ i)).1, (hk₁ _ (hZ i)).2.1⟩
  have hkΩ : ∀ i, k i *ᵥ Ω = 0 := fun i => (hk₁ _ (hZ i)).2.2
  have htail : ∀ i (l : ℕ), 0 ≤ E G Λ (anc i) l (k i) ∧ E G Λ (anc i) l (k i) ≤ 1 ∧
      ‖k i - E G Λ (anc i) l (k i)‖ ≤ Cp * Real.exp (-cp * (l : ℝ) ^ α p) :=
    fun i l => hk₄ _ (hZ i) l
  have hgap' : ((Δ / cstar : ℝ) : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤ ∑ i, k i := by
    have hsum : ∑ i, k i = ∑ Z ∈ supports G Λ R, kF Z :=
      (e.symm.sum_comp fun Z : supports G Λ R => kF Z.1).trans (sum_coe_sort _ kF)
    rw [hsum]
    exact hk₃.trans hk₂
  -- D10.4.2 (D10.5): typical projections, failure `δ = n^{-2K}`, norm `x = n^{-K}`
  set sel := typicalSet Ω hΩ hX w
  set T₀ := typicalProj Ω hΩ hY w
  set Q := typicalProj Ω hΩ (union_subset hX hY) w
  set x : ℝ := ((n : ℝ) ^ K)⁻¹ with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hn1))
  have hsq : ((n : ℝ) ^ (2 * K))⁻¹ = x ^ 2 := by rw [hxdef, inv_pow, ← pow_mul, mul_comm]
  have eX : vnorm ((1 - extendId hX (specProj (marg Ω hΩ hX).psd.isHermitian sel)) *ᵥ Ω) ≤ x :=
    vnorm_le_of_sq_le hx0.le ((hty n hn₂ Λ Φ hΦ Ω hΩ E₀ heig hgap X hX hbX).trans_eq hsq)
  have eY : vnorm ((1 - extendId hY T₀) *ᵥ Ω) ≤ x :=
    vnorm_le_of_sq_le hx0.le ((hty n hn₂ Λ Φ hΦ Ω hΩ E₀ heig hgap Y hY hbY).trans_eq hsq)
  have eS : vnorm ((1 - extendId (union_subset hX hY) Q) *ᵥ Ω) ≤ x :=
    vnorm_le_of_sq_le hx0.le
      ((hty n hn₂ Λ Φ hΦ Ω hΩ E₀ heig hgap (X ∪ Y) (union_subset hX hY) hbS).trans_eq hsq)
  obtain ⟨hX1, -, -, -, -, -⟩ := step_10_5_4 Ω hΩ hX w
  obtain ⟨-, hQle, -, hQρ, hQh, hQQ⟩ := step_10_5_4 Ω hΩ (union_subset hX hY) w
  obtain ⟨-, -, hTle, -, hTh, hTT⟩ := step_10_5_4 Ω hΩ hY w
  have hsel : ∀ y ∈ sel, 0 < (marg Ω hΩ hX).psd.isHermitian.eigenvalues y :=
    fun y hy => (hX1 y hy).1
  have hsel' : ∀ y ∈ sel, 0 < (marg Ω hΩ hX).psd.isHermitian.eigenvalues y ∧
      ((marg Ω hΩ hX).psd.isHermitian.eigenvalues y)⁻¹ ≤
        Real.exp ((marg Ω hΩ hX).entropy + w) := fun y hy => ⟨(hX1 y hy).1, by
    have := inv_anti₀ (Real.exp_pos _) (hX1 y hy).2.1
    rwa [← Real.exp_neg, neg_neg] at this⟩
  -- D10.4.3–5 (D10.6–D10.10)
  set R₀ := restoringOp hX hY hXY Ω hΩ sel T₀ Q
  set B₀ := columnOp hX hY hXY Ω hΩ sel T₀ Q
  set φ := copyVec hX Ω
  set η := restoredVec hX Ω hΩ
  set ξ := blankVec (loc := loc) X
  set ζ := R₀ *ᵥ φ
  have h𝓘eq : (marg Ω hΩ hX).entropy + (marg Ω hΩ (union_subset hX hY)).entropy -
      (marg Ω hΩ hY).entropy = 𝓘 := step_10_8_4 hX hY hXY Ω hΩ
  obtain ⟨hR₀, hB₀⟩ := step_10_8 hX hY hXY Ω hΩ sel T₀ Q _ _ _ hsel' hQh hQQ hQle hTh hTT hTle
  have hexp : Real.exp (((marg Ω hΩ hX).entropy + w + ((marg Ω hΩ (union_subset hX hY)).entropy
      + w) + (-(marg Ω hΩ hY).entropy + w)) / 2) = M₀ := by
    rw [hM₀def]; congr 1; linarith
  have hR₀' : ‖R₀‖ ≤ M₀ := hR₀.trans_eq hexp
  have hB₀' : ‖B₀‖ ≤ M₀ := hB₀.trans_eq hexp
  have hζB : ζ = B₀ *ᵥ tensVec Ω ξ := step_10_7 hX hY hXY Ω hΩ sel T₀ Q
  have hφ : vnorm φ = 1 := vnorm_copyVec hX Ω hΩ
  have hη : vnorm η = 1 := vnorm_restoredVec hX Ω hΩ
  have hζ : vnorm ζ ≤ M₀ := (vnorm_mulVec_le _ _).trans (by rw [hφ, mul_one]; exact hR₀')
  have hPζ := step_10_10 hX hY hXY Ω hΩ sel T₀ Q hsel hQh hQQ hQρ hTh hTT
  have hξ : star ξ ⬝ᵥ ξ = 1 := by simp [ξ, dotProduct, blankVec, apply_ite star]
  -- D10.4.6 (D10.12): the clocks of Lemma 10.1 with `S = S₀`, `B = B₀`, `ξ = |00⟩`
  obtain ⟨⟨sA, hA⟩, hLs, hB⟩ :=
    hL Λ (Fin #(supports G Λ R)) anc hanc hμ k hk htail t ht0 r hr1 (X ∪ Y) hS₀
  -- Lemma 10.1 (B) takes spectators in `Type`: carry `s'e'` to `Fin |s'e'|`
  obtain ⟨sB, hB⟩ := hB Ω hkΩ (Fin (Fintype.card (Reg loc X × Reg loc X)))
    (B₀.submatrix ((Equiv.refl (Reg loc Λ)).prodCongr
        (Fintype.equivFin (Reg loc X × Reg loc X)).symm)
      ((Equiv.refl (Reg loc Λ)).prodCongr (Fintype.equivFin (Reg loc X × Reg loc X)).symm))
    (fun A => by
      have hc := columnOp_support hX hY hXY Ω hΩ sel T₀ Q A
      change _ * _ = _ * _
      rw [kronecker_one_reindex _ (Fintype.equivFin (Reg loc X × Reg loc X)).symm,
        submatrix_mul_equiv, submatrix_mul_equiv, hc.eq])
    (ξ ∘ (Fintype.equivFin (Reg loc X × Reg loc X)).symm) hΩ (by
      simp only [dotProduct, Pi.star_apply, Function.comp_apply]
      rw [(Fintype.equivFin (Reg loc X × Reg loc X)).symm.sum_comp
        (fun j => star (ξ j) * ξ j)]
      exact hξ)
  rw [l2_opNorm_submatrix] at hB
  simp only [vnorm_reindex] at sB hB
  obtain ⟨s₁, h₁⟩ := step_10_3 (κ := Reg loc X × Reg loc X) k hk hΩ hkΩ hgap' ht0 ζ
  set P := vecMulVec Ω (star Ω) ⊗ₖ
    (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ) with hPdef
  have hPh : Pᴴ = P := by
    rw [hPdef, conjTranspose_kronecker, conjTranspose_vecMulVec, star_star, conjTranspose_one]
  have hPP : P * P = P := by
    rw [hPdef, ← mul_kronecker_one, vecMulVec_mul_vecMulVec, hΩ, one_smul]
  have hperp : vnorm ((1 - P) *ᵥ ζ) ≤ vnorm ζ := vnorm_proj_mulVec_le
    ⟨by rw [conjTranspose_sub, conjTranspose_one, hPh],
      by simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP,
        sub_self, sub_zero]⟩ ζ
  have he₁ : clockExp (Fin #(supports G Λ R)) t (fun m u =>
      vnorm ((wordProd (fun i => CFC.sqrt (1 - k i)) m u ⊗ₖ
        (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ ((1 - P) *ᵥ ζ)) ^ 2) ≤
      ((n : ℝ) ^ (6 * K))⁻¹ := by
    refine h₁.trans ?_
    have h2 : vnorm ((1 - P) *ᵥ ζ) ^ 2 ≤ M₀ ^ 2 :=
      pow_le_pow_left₀ (vnorm_nonneg _) (hperp.trans hζ) 2
    have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(Δ / cstar) * t)).le
    linarith
  have he₂ : clockExp (Fin #(supports G Λ R)) t (fun m u =>
      vnorm (((wordProd (fun i => CFC.sqrt (1 - k i)) m u -
        wordProd (fun i => if anc i ∈ graphNbhd G Λ (X ∪ Y) r then CFC.sqrt (1 - k i) else 1) m u)
          ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ
            (B₀ *ᵥ tensVec Ω ξ))) ≤ ((n : ℝ) ^ (3 * K))⁻¹ := by
    refine hB.trans (le_trans ?_ hBsc)
    have h2 := mul_le_mul_of_nonneg_left hcard (mul_nonneg hCL ht0)
    have h3 := mul_le_mul h2 hB₀' (norm_nonneg _)
      (mul_nonneg (mul_nonneg hCL ht0) (mul_nonneg hC₀.le (by positivity)))
    exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have he₃ : clockExp (Fin #(supports G Λ R)) t (fun m u =>
      ‖wordProd (fun i => if anc i ∈ graphNbhd G Λ (X ∪ Y) r then CFC.sqrt (1 - k i) else 1) m u -
        wordProd (fun i => if anc i ∈ graphNbhd G Λ (X ∪ Y) r then
          CFC.sqrt (1 - E G Λ (anc i) r (k i)) else 1) m u‖) ≤
      ((n : ℝ) ^ (3 * K))⁻¹ / M₀ := by
    refine hA.trans ?_
    rw [le_div_iff₀' hM₀pos]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hM₀pos.le) hAsc
    have h2 := mul_le_mul_of_nonneg_left hcard (mul_nonneg hCL ht0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity))
      (Real.exp_pos _).le
  have he : ((n : ℝ) ^ (6 * K))⁻¹ / x ^ 2 + ((n : ℝ) ^ (3 * K))⁻¹ / x +
      ((n : ℝ) ^ (3 * K))⁻¹ / M₀ / (x / M₀) < 1 := by
    have h1 := step_10_12_4 hK hn2
    have h2 : ((n : ℝ) ^ (3 * K))⁻¹ / M₀ / (x / M₀) = ((n : ℝ) ^ (3 * K))⁻¹ / x := by
      field_simp
    rw [h2]
    linarith
  -- one realization with all three bounds `≤ n^{-K}`
  obtain ⟨m, u, hu₁, hu₂, hu₃⟩ := exists_word_le ht0 (fun _ _ => sq_nonneg _)
    (fun _ _ => vnorm_nonneg _) (fun _ _ => norm_nonneg _) s₁ sB sA (pow_pos hx0 2) hx0
    (div_pos hx0 hM₀pos) he₁ he₂ he₃ he
  -- D10.4.7 (D10.13): `‖L'R₀φ‖ ≤ 1 + 3n^{-K}`, `‖R'^†η - φ‖ ≤ 4n^{-K}`, `R' = L'R₀`
  set Df := wordProd (fun i => CFC.sqrt (1 - k i)) m u with hDfdef
  set Dr := wordProd (fun i => if anc i ∈ graphNbhd G Λ (X ∪ Y) r then CFC.sqrt (1 - k i)
    else 1) m u with hDrdef
  set L' := wordProd (fun i => if anc i ∈ graphNbhd G Λ (X ∪ Y) r then
    CFC.sqrt (1 - E G Λ (anc i) r (k i)) else 1) m u with hL'def
  have hGf := fun i => sqrt_one_sub (hk i) (hkΩ i)
  have hDf := step_10_13_1 (κ := Reg loc X × Reg loc X) (fun i => CFC.sqrt (1 - k i))
    (fun i => (hGf i).1) (fun i => (hGf i).2.2) m u
  have hDr := step_10_13_1 (κ := Reg loc X × Reg loc X)
    (fun i => if anc i ∈ graphNbhd G Λ (X ∪ Y) r then CFC.sqrt (1 - k i) else 1)
    (fun i => by split_ifs; exacts [(hGf i).1, isHermitian_one])
    (fun i => by split_ifs; exacts [(hGf i).2.2, one_mulVec Ω]) m u
  have b₁ : vnorm ((Df ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ
      ((1 - P) *ᵥ ζ)) ≤ x := vnorm_le_of_sq_le hx0.le hu₁
  have b₂ : vnorm ((Df ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ) -
      Dr ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ ζ) ≤ x := by
    rw [sub_kronecker_one, hζB]; exact hu₂
  have b₃' : M₀ * ‖Dr - L'‖ ≤ x := (le_div_iff₀' hM₀pos).1 hu₃
  have b₃ : M₀ * ‖Dr ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ) -
      L' ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)‖ ≤ x := by
    rw [sub_kronecker_one]
    exact (mul_le_mul_of_nonneg_left (l2_opNorm_kronecker_one_le _) hM₀pos.le).trans b₃'
  have b₄ : vnorm ((Df ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ
      (P *ᵥ ζ)) ≤ 1 := by
    rw [mulVec_mulVec, hDf.2.2.2.1]; exact hPζ
  have hL'ζ : vnorm ((L' ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ
      ζ) ≤ 1 + 3 * x := step_10_13_2 hζ b₁ b₂ b₃ b₄
  have hLΩ : vnorm (L'ᴴ *ᵥ Ω - Ω) ≤ x := step_10_13_3 hDr.2.1 (vnorm_eq_one hΩ) hM₀1 b₃'
  have hadj := step_10_9 hX hY hXY Ω hΩ sel T₀ Q hsel hTh hTT hQh hQQ L'
  set R' := (L' ⊗ₖ (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) * R₀
    with hR'def
  have hR'φ : vnorm (R' *ᵥ φ) ≤ 1 + 3 * x := by rw [hR'def, ← mulVec_mulVec]; exact hL'ζ
  have hR'η : vnorm (R'ᴴ *ᵥ η - φ) ≤ 4 * x := by
    rw [hR'def, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, ← mulVec_mulVec]
    refine hadj.trans ?_
    linarith [eX, eY, eS, hLΩ]
  have hdir : vnorm (R' *ᵥ φ - η) ≤ √(23 * x) := by
    have h := step_10_13_6 hφ hη hR'φ hR'η (by positivity : (0 : ℝ) ≤ 3 * x)
    have h' := step_10_13_6'.1 x hx0.le hx1
    refine (le_abs_self _).trans (Real.abs_le_sqrt (h.trans ?_))
    exact (by ring : 2 * (3 * x) + (3 * x) ^ 2 + 2 * (4 * x) = 14 * x + 9 * x ^ 2).trans_le h'
  -- D10.4.8 (D10.14): `R'` acts on `s' ∪ N_{2r}(S₀)`; the local unitary `U'`
  have hN : graphNbhd G Λ (X ∪ Y) (2 * r) ⊆ Λ := graphNbhd_subset G Λ _ _
  have hXYN : X ∪ Y ⊆ graphNbhd G Λ (X ∪ Y) (2 * r) := subset_graphNbhd_self G hS₀ _
  have hact : ActsOn hN X R' := ActsOn.mul (actsOn_kronecker_one X (hLs m u).2)
    (ActsOn.mono hXYN hN (restoringOp_actsOn hX hY hXY Ω hΩ sel T₀ Q))
  obtain ⟨Vu, hVu, hU⟩ := step_10_14_supported hact hdir hR'η
  have hU' := hU.trans (step_10_13_6'.2 n K hn1)
  -- D10.4.10 (D10.11): the radius bound
  refine ⟨r, hrad.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg hnpos.le _)), ?_⟩
  -- D10.4.9 (D10.15): continuity on `e'`, `log dim e' ≤ C₀ n^d log q`
  intro X' hX' J hJ
  have hI := step_10_15 hX hN (subset_union_left.trans hXYN) hJ Ω hΩ Vu hVu hU' X' hX'
  have hD : (1 : ℝ) ≤ Fintype.card (Reg loc X) := by exact_mod_cast Fintype.card_pos
  have hDq : Real.log (Fintype.card (Reg loc X)) ≤ C₀ * (n : ℝ) ^ d * Real.log q :=
    (log_card_reg_le hq X).trans (mul_le_mul_of_nonneg_right
      ((by exact_mod_cast card_le_card subset_union_left : (#X : ℝ) ≤ #(X ∪ Y)).trans hcard) hlq)
  have h6 := step_10_15_6 (M := M) hn1 le_rfl hC₀.le hq1 hD hDq
  exact hI.trans (h6.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

/-! ## The frozen statement -/

/-- **Proposition 10.2** over `ℂ` [OAI265, §10.2], the frozen `OpenAI.Amplification ℂ`: the
`G = ℤ²`, `V = v 2`, `d = 2` instance of `prop_10_2`, with `X = A ∩ T`, `S₀ = A ∩ T_L`,
`L = ⌊n^{1-ε}⌋`, and the containment `N_{2r}(S₀) ⊆ A` under the clearance
`dist_∞(T, Z_A) > L + n^β` (D10.16). -/
theorem amplification_complex (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q) (hΔ : 0 < Δ)
    (hp : 10 ^ 6 ≤ p) : OpenAI.Amplification ℂ q R J Δ p := by
  intro C₀ hC₀ M hM
  -- `J ≥ 0`: otherwise no interaction is admissible (`‖Φ ∅‖ ≤ J`)
  rcases lt_or_ge J 0 with hJ | hJ
  · exact ⟨0, 0, fun Λ Φ hΦ => absurd (hΦ ∅ (empty_subset Λ)).2.1
      (not_le.2 (hJ.trans_le (norm_nonneg _)))⟩
  have : ∀ i, Nonempty (OpenAI.Qudits q i) := fun _ => ⟨⟨0, hq⟩⟩
  have hVK : ∀ r : ℕ, (v 2 r : ℝ) ≤ 2 * (r + 1) ^ 2 := fun r => by
    rw [v_two]; push_cast; nlinarith
  obtain ⟨C_M, n₀, H⟩ := prop_10_2 squareLattice (v 2) eq_ball_count_two hVK
    (loc := OpenAI.Qudits q) (q := q) (fun _ => by simp) R hJ hΔ hp 2 C₀ hC₀ M hM
  -- D10.16.2: `2 C_M n^{(1-ε)/α} < n^β` eventually
  obtain ⟨n₃, hn₃⟩ := step_10_16_2 hp C_M
  refine ⟨C_M, max n₀ n₃, ?_⟩
  intro Λ Φ hΦ Ω hΩ E₀ heig hgap A hA T n hn2 hn hcard hbX hbY hbS h𝓘
  have hTL : T ⊆ OpenAI.ambientDilation T (OpenAI.collarWidth n) := fun t ht =>
    mem_add.2 ⟨t, ht, 0, by simp [Prod.le_def], add_zero t⟩
  obtain ⟨r, hr, hMI⟩ := H Λ Φ hΦ Ω hΩ E₀ heig hgap (A ∩ T)
    (A ∩ OpenAI.ambientDilation T (OpenAI.collarWidth n)) (inter_subset_inter subset_rfl hTL)
    (inter_subset_left.trans hA) n hn2 (le_of_max_le_left hn) hcard hbX hbY hbS h𝓘
  refine ⟨r, hr, hMI, fun hclear => step_10_16_3_sq hA (lt_of_le_of_lt ?_ hclear)⟩
  -- D10.16.3: `L + 2r < L + n^β`
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 2 * C_M * (n : ℝ) ^ ((1 - ε) / α p) < (n : ℝ) ^ (1 - (2 / 1000000 : ℝ)) :=
    hn₃ n (le_of_max_le_right hn)
  have h2 : (r : ℝ) ≤ C_M * (n : ℝ) ^ ((1 - ε) / α p) := hr
  linarith

end AreaLaw
