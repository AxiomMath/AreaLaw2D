import AreaLaw.S09_Scanner.Truncation

/-!
# §9.2 The comparator data of Proposition 9.2 (D9.9.2)

Digest `digest/09-scanner.md` (D9.9.2), paper `paper/sections/08-scanner.tex` lines 410–430.
Graph-level (Map.md, Dimension: `any d`). The three inputs of Proposition 8.1 for the truncated
system `Ω̃` of D9.3, stated for an arbitrary status collection and prefix family satisfying
explicit hypotheses (the scan supplies them through Lemma 9.1):

* the typical set at the target `X = A ∩ T` with `w = n^{3/5}`, `z ≥ 1 - n^{-100}`;
* marginal moment data `comparator:mgf-data` with `𝓑 ≤ C n D (log n)^{6 m₀}`;
* prefix data `comparator:prefix-data` with `B_sh = C_e (n L^e + n) + n log q + 1`,
  `B_exc = 1 + M log q`.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Arealaw Finset Entropy
open OpenAI (pureState HasGlobalGap)

namespace AreaLaw.Scanner

open Comparators Transport GraphDomain

universe u

theorem eventually_log_pow_mul_le (K c : ℝ) (m : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      K * Real.log n ^ m * (c + 100 * Real.log n) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
  set K' := |K| * (|c| + 100) + 1
  have hK' : 0 < K' := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop ((m + 1 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 10)).def (inv_pos.2 hK')
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨n₀, hn₀⟩ :=
    Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually (h1.and h2))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h1n, h2n⟩ := hn₀ n hn
  have hl : 0 ≤ Real.log n := by linarith
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at h1n
  have h0 : 0 ≤ Real.log n ^ m := by positivity
  have hx : |c + 100 * Real.log n| ≤ (|c| + 100) * Real.log n := by
    rw [abs_le]; constructor <;> nlinarith [le_abs_self c, neg_abs_le c]
  calc K * Real.log n ^ m * (c + 100 * Real.log n)
      ≤ |K * Real.log n ^ m * (c + 100 * Real.log n)| := le_abs_self _
    _ = |K| * Real.log n ^ m * |c + 100 * Real.log n| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h0]
    _ ≤ |K| * Real.log n ^ m * ((|c| + 100) * Real.log n) := by gcongr
    _ = |K| * (|c| + 100) * Real.log n ^ (m + 1) := by ring
    _ ≤ K' * Real.log n ^ (m + 1) := by
        have : 0 ≤ Real.log n ^ (m + 1) := by positivity
        nlinarith
    _ ≤ K' * (K'⁻¹ * (n : ℝ) ^ (1 / 10 : ℝ)) := by gcongr
    _ = _ := by field_simp

theorem one_le_budget {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {ι : Type}
    [Fintype ι] (Et : EnergyTerms V n ι) (Q : Finset V) : 1 ≤ budget Et Q :=
  le_add_of_nonneg_right (sum_nonneg fun _ _ => sq_nonneg _)

variable {σ : Type u} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem up_target {Λ A : Finset σ} (hA : A ⊆ Λ) (dep : σ → ℕ) :
    up ((A.filter fun x => dep x = 0).subtype (· ∈ Λ)) = A.filter fun x => dep x = 0 := by
  rw [up, subtype_map, filter_true_of_mem fun x hx => hA (mem_filter.1 hx).1]

/-- D9.3. The target cut `∂_Λ X`, `X = A ∩ T`, has at most `V(1) n` edges: an edge leaving `X`
ends in the first positive depth row (at most `n` sites), and clearance excludes edges from `X`
to `Λ \ A`. -/
theorem card_edgeBoundary_target {V : ℕ → ℕ}
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {Λ A : Finset σ}
    (hA : A ⊆ Λ) {dep : σ → ℕ} {CT : ℝ} {n L r : ℕ} (hT : TestGeometry G Λ A dep CT n L r)
    (hL : 1 ≤ L) :
    (#(edgeBoundary G Λ (A.filter fun x => dep x = 0)) : ℝ) ≤ V 1 * n := by
  set X := A.filter fun x => dep x = 0
  set row := Λ.filter fun x => dep x = 1
  have hsub : edgeBoundary G Λ X ⊆ row.biUnion fun y => ball G Λ y 1 ×ˢ {y} := by
    rintro ⟨x, y⟩ he
    rw [edgeBoundary, SimpleGraph.mem_interedges_iff] at he
    obtain ⟨hx, hy, hxy⟩ := he
    rw [mem_filter] at hx
    rw [mem_sdiff] at hy
    have hx0 : dep x = 0 := hx.2
    have hyA : y ∈ A := by
      by_contra hyA
      have hz : x ∈ cutEndpoints G Λ A := mem_union_left _ (mem_image.2 ⟨(x, y),
        (SimpleGraph.mem_interedges_iff G).2 ⟨hx.1, mem_sdiff.2 ⟨hy.1, hyA⟩, hxy⟩, rfl⟩)
      have := hT.clearance x hz
      omega
    have hdy : dep y = 1 := by
      have h1 := hT.lipschitz y x hxy.symm
      have h2 : dep y ≠ 0 := fun h => hy.2 (mem_filter.2 ⟨hyA, h⟩)
      omega
    have hxΛ : x ∈ Λ := hA hx.1
    refine mem_biUnion.2 ⟨y, mem_filter.2 ⟨hy.1, hdy⟩, mem_product.2 ⟨?_, mem_singleton_self y⟩⟩
    rw [mem_ball]
    refine ⟨hxΛ, ?_⟩
    rw [domainEDist, dif_pos ⟨hxΛ, hy.1⟩]
    exact (SimpleGraph.edist_eq_one_iff_adj.2 (by simpa using hxy)).le
  have hcard : #(edgeBoundary G Λ X) ≤ #row * V 1 := by
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun y _ => by rw [card_product, card_singleton, mul_one]; exact hV _ _ _
  have hrow : #row ≤ n := hT.card_row 1 le_rfl hL
  have : #(edgeBoundary G Λ X) ≤ V 1 * n := by nlinarith
  exact_mod_cast this

/-! ## D9.9.2 (i) The typical set at the target -/

/-- D9.9.2 (typical set). For `n ≥ n₀` (depending only on `g`, the growth data and the
constants of Proposition 4.5), the truncated system has a typical Schmidt set
`E = {i : |-log p_i - S(X)| ≤ w}` at the target `X = A ∩ T` with `w = n^{3/5}` and
`z = ∑_{i ∈ E} p_i ≥ 1 - n^{-100}`: `|∂_Λ X| ≤ V(1) n` (D9.3), so `𝓑_X ≤ C n (log n)^{6 m₀}`
(D4.14), and Lemma 3.1 (`ϑ ≤ 2/g`) gives `P{|K - S_X| > w} ≤ C exp(-c w/√𝓑_X) ≤ n^{-100}`. -/
theorem step_9_9_2_typical {V : ℕ → ℕ}
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) (q : ℕ) [NeZero q]
    (R : ℕ) {g C₁ Cb : ℝ} {m₀ : ℕ} (hg : 0 < g) (hcut : CutBudgetBound G q R C₁ m₀) :
    ∃ n₀ : ℕ, ∀ n L : ℕ, n₀ ≤ n → 1 ≤ L →
    ∀ (Λ : Finset σ) (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
      (A : Finset σ), A ⊆ Λ → ∀ (dep : σ → ℕ) (CT : ℝ) (r : ℕ),
      TestGeometry G Λ A dep CT n L r →
    ∀ T : TruncatedSystem G q R g C₁ Cb m₀ n L Λ Ω hΩ A dep,
      ∃ E : TypicalSet T.Dt ((A.filter fun x => dep x = 0).subtype (· ∈ Λ)),
        E.w = (n : ℝ) ^ (3 / 5 : ℝ) ∧ 1 - (n : ℝ) ^ (-100 : ℝ) ≤ E.z := by
  obtain ⟨CD, hCD⟩ := hcut (V 1) (Nat.cast_nonneg _)
  set c₁ := Real.log (2 * Real.exp (Real.exp 1 / 2))
  set K := 32 * √((1 + 2 / g) * max CD 1)
  obtain ⟨n₁, hn₁⟩ := eventually_log_pow_mul_le K c₁ (3 * m₀)
  refine ⟨max n₁ 3, fun n L hn hL Λ Ω hΩ A hA dep CT r hT Tr => ?_⟩
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans hn3
  -- D9.3, D4.14: `𝓑_X ≤ C n (log n)^{6 m₀}`
  have hb1 := one_le_budget Tr.Et ((A.filter fun x => dep x = 0).subtype (· ∈ Λ))
  have hb : budget Tr.Et ((A.filter fun x => dep x = 0).subtype (· ∈ Λ)) ≤
      max CD 1 * n * Real.log n ^ (6 * m₀) := by
    have h := hCD Λ (A.filter fun x => dep x ≤ L) (A.filter fun x => dep x = 0) Tr.a n 1
      Tr.anchor (fun x hx => mem_filter.2 ⟨(mem_filter.1 hx).1, by
        rw [(mem_filter.1 hx).2]; exact Nat.zero_le _⟩) (by linarith) le_rfl
      (by rw [mul_one]; exact card_edgeBoundary_target G hV hA hT hL)
    have he := Tr.budget_eq ((A.filter fun x => dep x = 0).subtype (· ∈ Λ))
    rw [up_target hA] at he
    have hpos : 0 ≤ (n : ℝ) * Real.log n ^ (6 * m₀) := by positivity
    refine (he.trans_le h).trans ?_
    rw [mul_one, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  set X' := (A.filter fun x => dep x = 0).subtype (· ∈ Λ)
  set D := Tr.Dt
  set w := (n : ℝ) ^ (3 / 5 : ℝ)
  set b := budget Tr.Et X'
  -- D9.9.2: `w / √𝓑 ≥ n^{1/10} / (log n)^C`, hence the tail is `≤ n^{-100}`
  have hgD : 1 / D.g = 2 / g := by rw [Tr.g_eq]; field_simp
  set s := 32 * √((1 + 2 / g) * b)
  have hs : 0 < s := by positivity
  have hsK : s ≤ K * √n * Real.log n ^ (3 * m₀) := by
    have hsq : √(Real.log n ^ (6 * m₀)) = Real.log n ^ (3 * m₀) := by
      rw [show 6 * m₀ = 2 * (3 * m₀) by ring, pow_mul', Real.sqrt_sq (by positivity)]
    calc s = 32 * √((1 + 2 / g) * b) := rfl
      _ ≤ 32 * √((1 + 2 / g) * (max CD 1 * n * Real.log n ^ (6 * m₀))) := by gcongr
      _ = K * √n * Real.log n ^ (3 * m₀) := by
          rw [show (1 + 2 / g) * (max CD 1 * n * Real.log n ^ (6 * m₀)) =
              (1 + 2 / g) * max CD 1 * n * Real.log n ^ (6 * m₀) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), hsq]
          ring
  have hc₁ : 0 < c₁ := Real.log_pos (by
    have := Real.add_one_le_exp (Real.exp 1 / 2)
    nlinarith [Real.exp_pos 1])
  have hsw : s * (c₁ + 100 * Real.log n) ≤ w := by
    have hw : w = √n * (n : ℝ) ^ (1 / 10 : ℝ) := by
      change (n : ℝ) ^ (3 / 5 : ℝ) = _
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]; norm_num
    rw [hw]
    calc s * (c₁ + 100 * Real.log n)
        ≤ K * √n * Real.log n ^ (3 * m₀) * (c₁ + 100 * Real.log n) := by
          gcongr
      _ = √n * (K * Real.log n ^ (3 * m₀) * (c₁ + 100 * Real.log n)) := by ring
      _ ≤ √n * (n : ℝ) ^ (1 / 10 : ℝ) := by
          gcongr; exact hn₁ n (le_of_max_le_left hn)
  have htail := (lemma_3_1_physData D Tr.Et Tr.H_eq X').2 w (by positivity)
  rw [hgD] at htail
  have htail' : ∑ j ∈ univ.filter (fun j => 0 < D.p X' j ∧ w < |-Real.log (D.p X' j) - D.S X'|),
      D.p X' j ≤ (n : ℝ) ^ (-100 : ℝ) := by
    refine htail.trans ((min_le_right _ _).trans ?_)
    have h1 : w / s ≥ c₁ + 100 * Real.log n := by rw [ge_iff_le, le_div_iff₀ hs]; linarith
    have h2 : (n : ℝ) ^ (-100 : ℝ) = Real.exp (-(100 * Real.log n)) := by
      rw [Real.rpow_def_of_pos hn0]; ring_nf
    rw [h2, show 2 * Real.exp (Real.exp 1 / 2) = Real.exp c₁ from
      (Real.exp_log (by positivity)).symm, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  -- D9.9.2: `E = {i : |-log p_i - S_X| ≤ w}`, `z = 1 - P{|K - S_X| > w}`
  have hp0 (j) : 0 ≤ D.p X' j := (D.state.restrict (subset_univ X')).psd.eigenvalues_nonneg j
  have hsum1 : ∑ j, D.p X' j = 1 := (D.state.restrict (subset_univ X')).sum_eigenvalues_eq_one
  have hsplit := sum_filter_add_sum_filter_not (univ.filter fun j => 0 < D.p X' j)
    (fun j => |-Real.log (D.p X' j) - D.S X'| ≤ w) (D.p X')
  rw [filter_filter, filter_filter, sum_filter_of_ne fun j _ hj => lt_of_le_of_ne (hp0 j)
    (Ne.symm hj), hsum1] at hsplit
  simp only [not_le] at hsplit
  set E := univ.filter fun j => 0 < D.p X' j ∧ |-Real.log (D.p X' j) - D.S X'| ≤ w
  have hz : 1 - (n : ℝ) ^ (-100 : ℝ) ≤ ∑ j ∈ E, D.p X' j := by linarith
  have hlt : (n : ℝ) ^ (-100 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have hne : E.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hz
    linarith
  refine ⟨{
    E := E
    w := w
    nonempty := hne
    w_nonneg := by positivity
    lower := fun j hj => ?_
    upper := fun j hj => ?_ }, rfl, hz⟩
  · obtain ⟨hj0, hjw⟩ := (mem_filter.1 hj).2
    exact (Real.exp_le_exp.2 (by linarith [(abs_le.1 hjw).2])).trans_eq (Real.exp_log hj0)
  · obtain ⟨hj0, hjw⟩ := (mem_filter.1 hj).2
    exact (Real.exp_log hj0).symm.trans_le (Real.exp_le_exp.2 (by linarith [(abs_le.1 hjw).1]))

/-! ## D9.9.2 (ii) Marginal moment data -/

/-- D9.9.2 (marginal moments). For every status collection whose regions
`Q ∈ {XU_g, Y_g, U_g, U_gY_g, XU_gY_g}` lie in `S₀` with `|∂_Λ Q| ≤ C₂ n D` (`D ≥ 1`), the
truncated system has `comparator:mgf-data` with `C₀ = 512 e ϑ`, `ϑ = 2/g`,
`c₀ = [32 √(1 + ϑ)]⁻¹` and `𝓑 = C n D (log n)^{6 m₀}`: Lemma 3.1 with the cut budget of D4.14
(for `V_g` that of `XU_gY_g`, its complement). -/
theorem step_9_9_2_mgf (q : ℕ) [NeZero q] (R : ℕ) {g C₁ Cb : ℝ} {m₀ : ℕ} (hg : 0 < g)
    (hcut : CutBudgetBound G q R C₁ m₀) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, ∀ n L : ℕ, 3 ≤ n →
    ∀ (Λ : Finset σ) (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
      (A : Finset σ) (dep : σ → ℕ) (T : TruncatedSystem G q R g C₁ Cb m₀ n L Λ Ω hΩ A dep)
      {K : ℕ} {St : Type*}
      (Γ : Statuses Λ K St ((A.filter fun x => dep x = 0).subtype (· ∈ Λ))) (D : ℝ), 1 ≤ D →
      (∀ s j, ∀ Q ∈ ({(A.filter fun x => dep x = 0).subtype (· ∈ Λ) ∪ Γ.U s j, Γ.Y s j,
          Γ.U s j, Γ.U s j ∪ Γ.Y s j,
          (A.filter fun x => dep x = 0).subtype (· ∈ Λ) ∪ Γ.U s j ∪ Γ.Y s j} :
          Finset (Finset Λ)),
        up Q ⊆ A.filter (fun x => dep x ≤ L) ∧ (#(edgeBoundary G Λ (up Q)) : ℝ) ≤ C₂ * n * D) →
      MgfData T.Dt Γ (1024 * Real.exp 1 / g) (32 * √(1 + 2 / g))⁻¹
        (max C 1 * n * D * Real.log n ^ (6 * m₀)) := by
  obtain ⟨CD, hCD⟩ := hcut C₂ hC₂
  refine ⟨CD, fun n L hn Λ Ω hΩ A dep T K St Γ D hD hΓ => ?_⟩
  set 𝓑 := max CD 1 * n * D * Real.log n ^ (6 * m₀)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans hn3
  have h𝓑 : 1 ≤ 𝓑 := by
    have h1 : 1 ≤ max CD 1 * n := one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 hD)
      (one_le_pow₀ hlog)
  -- D4.14: the cut budget of every status region in `S₀`
  have hgen : ∀ Q : Finset Λ, up Q ⊆ A.filter (fun x => dep x ≤ L) →
      (#(edgeBoundary G Λ (up Q)) : ℝ) ≤ C₂ * n * D → budget T.Et Q ≤ 𝓑 := fun Q hQ hQb => by
    rw [T.budget_eq]
    refine (hCD Λ _ (up Q) T.a n D T.anchor hQ (by linarith) hD hQb).trans ?_
    have hpos : 0 ≤ (n : ℝ) * (D * Real.log n ^ (6 * m₀)) := by positivity
    simp only [𝓑, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  have hV (s j) : univ \ Γ.V s j =
      (A.filter fun x => dep x = 0).subtype (· ∈ Λ) ∪ Γ.U s j ∪ Γ.Y s j := by
    rw [← Γ.cover s j, union_sdiff_right, sdiff_eq_self_of_disjoint
      (disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨Γ.disjoint_XV s j, Γ.disjoint_UV s j⟩,
        Γ.disjoint_YV s j⟩)]
  have hgD : 1 / T.Dt.g = 2 / g := by rw [T.g_eq]; field_simp
  refine ⟨h𝓑, fun s j Q hQ u hu => ?_⟩
  -- D9.9.2: `𝓑_Q ≤ 𝓑`, using `XU_gY_g` for `V_g`
  have hb : budget T.Et Q ≤ 𝓑 := by
    simp only [mem_insert, mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl | rfl | rfl
    · exact hgen _ (hΓ s j _ (by simp)).1 (hΓ s j _ (by simp)).2
    · rw [← budget_compl, hV]
      exact hgen _ (hΓ s j _ (by simp)).1 (hΓ s j _ (by simp)).2
    · exact hgen _ (hΓ s j _ (by simp)).1 (hΓ s j _ (by simp)).2
    · exact hgen _ (hΓ s j _ (by simp)).1 (hΓ s j _ (by simp)).2
    · exact hgen _ (hΓ s j _ (by simp)).1 (hΓ s j _ (by simp)).2
  have hb1 := one_le_budget T.Et Q
  have hmgf := (lemma_3_1_physData T.Dt T.Et T.H_eq Q).1 u (by
    rw [hgD]
    refine hu.trans ?_
    rw [div_eq_mul_inv, ← mul_inv, mul_assoc, ← Real.sqrt_mul (by positivity)]
    gcongr)
  rw [hgD] at hmgf
  refine hmgf.trans ?_
  have : 512 * Real.exp 1 * (2 / g) * budget T.Et Q * u ^ 2 ≤
      1024 * Real.exp 1 / g * 𝓑 * u ^ 2 := by
    rw [show 512 * Real.exp 1 * (2 / g) = 1024 * Real.exp 1 / g by ring]
    gcongr
  linarith

/-! ## D9.9.2 (iii) Prefix data -/

theorem eventually_rpow_neg_mul_le {CT : ℝ} (hCT : 0 ≤ CT) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ (-200 : ℝ) * (1 + (CT + 1) * (n : ℝ) ^ 2) ≤ 1 := by
  obtain ⟨n₀, hn₀⟩ := eventually_rpow_neg_le (a := 198) (by norm_num)
    (by positivity : 0 < 1 / (CT + 2))
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 := hn₀ n (le_of_max_le_left hn)
  rw [le_div_iff₀ (by positivity)] at h1
  have h2 : (n : ℝ) ^ (-200 : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ (-198 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have h3 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have h4 : 0 ≤ (n : ℝ) ^ (-200 : ℝ) := Real.rpow_nonneg hn0.le _
  nlinarith

/-- D9.9.2 (prefix data). For `n ≥ n₀`, every nested family `𝓡` disjoint from `X` of depth
prefixes `A ∩ T_{j-1} \ T ⊆ B ⊆ A ∩ T_j \ T` (`j ≤ L`, a partial row) and every status
collection whose `U_g`, `U_gY_g` are each matched with some `B ∈ 𝓡` within `M` sites give
`comparator:prefix-data` with `B_sh = C_e (n L^e + n) + n log q + 1` and `B_exc = 1 + M log q`:
subadditivity for the partial row (`≤ n` sites), the hypothesis `S_Ω(Q_j) ≤ C_e (n L^e + n)` and
the transfer D9.9.1. -/
theorem step_9_9_2_prefix (q : ℕ) [NeZero q] (R : ℕ) {g C₁ Cb : ℝ} {m₀ : ℕ} (hg : 0 < g)
    {CT : ℝ} (hCT : 0 ≤ CT) :
    ∃ n₀ : ℕ, ∀ n L : ℕ, n₀ ≤ n → L ≤ n →
    ∀ (Λ : Finset σ) (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
      (A : Finset σ) (hA : A ⊆ Λ) (dep : σ → ℕ) (r : ℕ), TestGeometry G Λ A dep CT n L r →
    ∀ Ce e : ℝ, (∀ j ≤ L, (pureState Ω hΩ).regionEntropy
        ((filter_subset _ A).trans hA : A.filter (fun x => 0 < dep x ∧ dep x ≤ j) ⊆ Λ) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n)) →
    ∀ (T : TruncatedSystem G q R g C₁ Cb m₀ n L Λ Ω hΩ A dep) (𝓡 : Finset (Finset Λ)),
      (∀ B ∈ 𝓡, ∀ B' ∈ 𝓡, B ⊆ B' ∨ B' ⊆ B) →
      (∀ B ∈ 𝓡, Disjoint B ((A.filter fun x => dep x = 0).subtype (· ∈ Λ))) →
      (∀ B ∈ 𝓡, ∃ j ≤ L, A.filter (fun x => 0 < dep x ∧ dep x < j) ⊆ up B ∧
        up B ⊆ A.filter (fun x => 0 < dep x ∧ dep x ≤ j)) →
    ∀ {K : ℕ} {St : Type*} (Γ : Statuses Λ K St ((A.filter fun x => dep x = 0).subtype (· ∈ Λ)))
      (M : ℕ), (∀ s j, ∀ Q ∈ ({Γ.U s j, Γ.U s j ∪ Γ.Y s j} : Finset (Finset Λ)), ∃ B ∈ 𝓡,
        (Q ⊆ B ∧ #(B \ Q) ≤ M) ∨ (B ⊆ Q ∧ #(Q \ B) ≤ M)) →
      PrefixData T.Dt Γ 𝓡 (Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + n * Real.log q + 1)
        (1 + M * Real.log q) := by
  obtain ⟨n₁, hn₁⟩ := step_9_9_1 (σ := σ) q hg
  obtain ⟨n₂, hn₂⟩ := eventually_rpow_neg_mul_le hCT
  refine ⟨max n₁ n₂, fun n L hn hLn Λ Ω hΩ A hA dep r hT Ce e hshell T 𝓡 hnest hdisj hpre
    K St Γ M hmatch => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have htr := (hn₁ n (le_of_max_le_left hn) Λ Ω hΩ T.Dt T.traceDist_le).1
  have hdim (Z : Finset Λ) : Real.log (dimReg (fun _ : Λ => q) Z) = #Z * Real.log q := by
    rw [dimReg, prod_const, Nat.cast_pow, Real.log_pow]
  refine ⟨hnest, hdisj, fun s j Q hQ => ?_, fun B hB => ?_⟩
  · -- D8.4: `B_exc ≥ 1 + log dim 𝓗_{B △ Q}`, `|B △ Q| ≤ M`
    obtain ⟨B, hB, h⟩ := hmatch s j Q hQ
    refine ⟨B, hB, h.imp (fun h => ⟨h.1, ?_⟩) (fun h => ⟨h.1, ?_⟩)⟩
    · have : (#(B \ Q) : ℝ) ≤ M := by exact_mod_cast h.2
      rw [hdim]; gcongr
    · have : (#(Q \ B) : ℝ) ≤ M := by exact_mod_cast h.2
      rw [hdim]; gcongr
  · -- the shell bound for a prefix with a partial last row, then D9.9.1
    obtain ⟨j, hj, hlo, hhi⟩ := hpre B hB
    set P := A.filter fun x => 0 < dep x ∧ dep x ≤ j - 1
    set Z := up B \ P
    have hPΛ : P ⊆ Λ := (filter_subset _ A).trans hA
    have hPB : P ⊆ up B := fun x hx => by
      rw [mem_filter] at hx
      exact hlo (mem_filter.2 ⟨hx.1, hx.2.1, by omega⟩)
    have hZΛ : Z ⊆ Λ := sdiff_subset.trans (up_subset B)
    have hZ : #Z ≤ n := by
      have hZr : Z ⊆ Λ.filter fun x => dep x = j := fun x hx => by
        rw [mem_sdiff] at hx
        have h1 := mem_filter.1 (hhi hx.1)
        have h2 : ¬ (0 < dep x ∧ dep x ≤ j - 1) := fun h => hx.2 (mem_filter.2 ⟨h1.1, h⟩)
        exact mem_filter.2 ⟨hA h1.1, by omega⟩
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · have : Z = ∅ := eq_empty_of_forall_notMem fun x hx => by
          have h1 := mem_filter.1 (hhi (mem_sdiff.1 hx).1)
          omega
        rw [this, card_empty]; exact Nat.zero_le _
      · exact (card_le_card hZr).trans (hT.card_row j h0 hj)
    have hS : (pureState Ω hΩ).regionEntropy (up_subset B) ≤
        Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + n * Real.log q := by
      have h1 := regionEntropy_union_le (pureState Ω hΩ) disjoint_sdiff hPΛ hZΛ
      have h2 := hshell (j - 1) (by omega)
      have h3 : (pureState Ω hΩ).regionEntropy hZΛ ≤ n * Real.log q := by
        have := ((pureState Ω hΩ).restrict hZΛ).entropy_le_log_card
        rw [card_reg_fin, Real.log_pow] at this
        refine this.trans ?_
        gcongr
      rw [(pureState Ω hΩ).toSubState.regionEntropy_congr (union_sdiff_of_subset hPB).symm
        (up_subset B) (union_subset hPΛ hZΛ)]
      linarith
    have hcard : (#B : ℝ) ≤ (CT + 1) * (n : ℝ) ^ 2 := by
      have : up B ⊆ A.filter fun x => dep x ≤ L := fun x hx => by
        have h1 := mem_filter.1 (hhi hx)
        exact mem_filter.2 ⟨h1.1, by omega⟩
      have h := (Nat.cast_le (α := ℝ)).2 (card_le_card this)
      rw [up, card_map] at h
      exact h.trans (card_S₀_le G hA hT hLn)
    have herr : (n : ℝ) ^ (-200 : ℝ) * (1 + #B) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
        (hn₂ n (le_of_max_le_right hn))
    have := (abs_le.1 (htr B)).2
    linarith

end AreaLaw.Scanner
