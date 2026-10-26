import AreaLaw.S04_Quasilocal.Setup

/-!
# §4.3 Crossing supports and the cut budget

Digest `digest/04-quasilocal.md` (D4.11 definitions `𝓒_X`, `𝓑_X`; D4.14), paper
`paper/sections/03-quasilocal.tex` lines 436–454, 505–521. Graph-level (`Map.md`, Dimension):
a simple graph `G` on a site type `σ` with ball growth `#B_Λ(x, r) ≤ V r`.
-/

namespace AreaLaw

open Finset

namespace GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ)

/-- D4.11. The crossing labels `𝓒_X`: the labels `i` (supports `X_i ∈ supports G Λ R`, anchors
`a_i = a X_i`) whose truncated support `X̃_i` meets both `X` and `Λ \ X`. -/
noncomputable def crossingLabels (Λ S₀ : Finset σ) (R r₀ : ℕ) (a : Finset σ → σ)
    (X : Finset σ) : Finset (Finset σ) :=
  {Y ∈ supports G Λ R | (truncatedSupport G Λ S₀ r₀ (a Y) ∩ X).Nonempty ∧
    (truncatedSupport G Λ S₀ r₀ (a Y) ∩ (Λ \ X)).Nonempty}

/-- D4.11. The cut budget `𝓑_X = 1 + ∑_{i ∈ 𝓒_X} log²(e d_i)`, `d_i = q^{|X̃_i|}`. -/
noncomputable def cutBudget (q : ℕ) (Λ S₀ : Finset σ) (R r₀ : ℕ) (a : Finset σ → σ)
    (X : Finset σ) : ℝ :=
  1 + ∑ Y ∈ crossingLabels G Λ S₀ R r₀ a X,
    Real.log (Real.exp 1 * (q : ℝ) ^ #(truncatedSupport G Λ S₀ r₀ (a Y))) ^ 2

end GraphDomain

open GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ)

/-- D4.14.1–D4.14.2. For `X ⊆ S₀`, a crossing label has `d_i^0 < ∞`, `r_i = r₀` and
`X̃_i = N_{r₀}(a_i)`. -/
theorem step_4_14_2 {Λ S₀ X : Finset σ} {R r₀ : ℕ} {a : Finset σ → σ} (hX : X ⊆ S₀)
    {Y : Finset σ} (hY : Y ∈ crossingLabels G Λ S₀ R r₀ a X) :
    setDist G Λ S₀ (a Y) ≠ ⊤ ∧ radius r₀ (setDist G Λ S₀ (a Y)).toNat = r₀ ∧
      truncatedSupport G Λ S₀ r₀ (a Y) = ball G Λ (a Y) r₀ := by
  obtain ⟨x, hx⟩ := (mem_filter.1 hY).2.1
  rw [mem_inter] at hx
  have hle : setDist G Λ S₀ (a Y) ≤ domainEDist G Λ (a Y) x := inf_le (hX hx.2)
  -- D4.14.1
  have hfin : setDist G Λ S₀ (a Y) ≠ ⊤ := by
    intro htop
    have h1 := hx.1
    simp only [truncatedSupport, htop, if_true, component, mem_filter] at h1
    exact h1.2 (top_le_iff.1 (htop ▸ hle))
  -- D4.14.2
  have hd : ((setDist G Λ S₀ (a Y)).toNat : ℕ∞) = setDist G Λ S₀ (a Y) := ENat.natCast_toNat hfin
  have hx1 := hx.1
  simp only [truncatedSupport, hfin, if_false] at hx1
  have hcomm : ∀ u w, domainEDist G Λ u w = domainEDist G Λ w u := by
    intro u w
    unfold domainEDist
    by_cases h : u ∈ Λ ∧ w ∈ Λ
    · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, SimpleGraph.edist_comm]
    · rw [dif_neg h, dif_neg fun h' => h ⟨h'.2, h'.1⟩]
  have hxr : domainEDist G Λ (a Y) x ≤ (radius r₀ (setDist G Λ S₀ (a Y)).toNat : ℕ) :=
    hcomm x (a Y) ▸ ((GraphDomain.mem_ball G).1 hx1).2
  have hr : radius r₀ (setDist G Λ S₀ (a Y)).toNat = r₀ := by
    refine max_eq_left (not_lt.1 fun hlt => ?_)
    rw [radius, max_eq_right hlt.le] at hxr
    have := Nat.cast_le.1 ((hd.trans_le hle).trans hxr)
    omega
  exact ⟨hfin, hr, by simp only [truncatedSupport, hfin, if_false, hr]⟩

/-- D4.14.3–D4.14.4. For `X ⊆ S₀`, `|𝓒_X| ≤ 2 μ_R b_X V(r₀)`. -/
theorem step_4_14_4 [DecidableRel G.Adj] (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {Λ S₀ X : Finset σ} {R r₀ : ℕ} {a : Finset σ → σ} (ha : ∀ Y ∈ supports G Λ R, a Y ∈ Y)
    (hX : X ⊆ S₀) :
    #(crossingLabels G Λ S₀ R r₀ a X) ≤ 2 * μ V R * #(edgeBoundary G Λ X) * V r₀ := by
  let Z := cutEndpoints G Λ X
  -- D4.14.3
  have h3 : ∀ Y ∈ crossingLabels G Λ S₀ R r₀ a X, a Y ∈ Z.biUnion (ball G Λ · r₀) := by
    intro Y hY
    obtain ⟨hYs, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := mem_filter.1 hY
    rw [(step_4_14_2 G hX hY).2.2, mem_inter] at hx₁ hx₂
    obtain ⟨y, hyB, hy⟩ : ∃ y ∈ ball G Λ (a Y) r₀, ¬(a Y ∈ X ↔ y ∈ X) := by
      by_cases haX : a Y ∈ X
      · exact ⟨x₂, hx₂.1, fun h => (mem_sdiff.1 hx₂.2).2 (h.1 haX)⟩
      · exact ⟨x₁, hx₁.1, fun h => haX (h.2 hx₁.2)⟩
    obtain ⟨hyΛ, hya⟩ := (GraphDomain.mem_ball G).1 hyB
    have haΛ : a Y ∈ Λ := ((GraphDomain.mem_supports G).1 hYs).1 (ha Y hYs)
    rw [GraphDomain.domainEDist_eq G ⟨y, hyΛ⟩ ⟨a Y, haΛ⟩] at hya
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (hya.trans_lt (ENat.natCast_lt_top r₀)).ne
    obtain ⟨z, hz, p', hp'⟩ := GraphDomain.exists_cutEndpoints_of_walk G p.reverse hy
    refine mem_biUnion.2 ⟨z, hz, (GraphDomain.mem_ball G).2 ⟨haΛ, ?_⟩⟩
    rw [GraphDomain.domainEDist_eq G ⟨a Y, haΛ⟩ z]
    exact p'.edist_le.trans
      ((Nat.cast_le.2 (hp'.trans_eq p.length_reverse)).trans (hp ▸ hya))
  -- D4.14.4
  calc #(crossingLabels G Λ S₀ R r₀ a X)
      ≤ #((Z.biUnion (ball G Λ · r₀)).biUnion fun x => {Y ∈ supports G Λ R | a Y = x}) :=
        card_le_card fun Y hY =>
          mem_biUnion.2 ⟨a Y, h3 Y hY, mem_filter.2 ⟨(mem_filter.1 hY).1, rfl⟩⟩
    _ ≤ #(Z.biUnion (ball G Λ · r₀)) * μ V R :=
        card_biUnion_le_card_mul _ _ _ fun x _ => (step_2_8 G V hV Λ R x).2.1 a ha
    _ ≤ #Z * V r₀ * μ V R := by
        gcongr
        exact card_biUnion_le_card_mul _ _ _ fun z _ => hV Λ z r₀
    _ ≤ 2 * #(edgeBoundary G Λ X) * V r₀ * μ V R := by
        gcongr
        exact (card_union_le _ _).trans (by
          have := card_image_le (s := edgeBoundary G Λ X) (f := Prod.fst)
          have := card_image_le (s := edgeBoundary G Λ X) (f := Prod.snd)
          omega)
    _ = 2 * μ V R * #(edgeBoundary G Λ X) * V r₀ := by ring

/-- D4.14. The crossing/cut clause of D4.11: for `X ⊆ S₀`, `r₀ ≥ 1`, every crossing label has
`d_i^0 < ∞` and radius exactly `r₀`, and
`|𝓒_X| ≤ 2 μ_R b_X V(r₀)`, `log d_i = |X̃_i| log q ≤ V(r₀) log q`,
`𝓑_X ≤ 1 + |𝓒_X| (1 + V(r₀) log q)²`; under `V(r) ≤ K (r+1)^m`, with `C` depending only on
`q, R, K, m`: `|𝓒_X| ≤ C b_X (r₀+1)^m`, `log d_i ≤ C (r₀+1)^m`,
`𝓑_X = 1 + ∑_{i ∈ 𝓒_X} log²(e d_i) ≤ C (1 + b_X) (r₀+1)^{3m}`. -/
theorem step_4_14 [DecidableRel G.Adj] (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {q : ℕ} (hq : 1 ≤ q)
    (R : ℕ) :
    (∀ (Λ S₀ X : Finset σ) (r₀ : ℕ) (a : Finset σ → σ), (∀ Y ∈ supports G Λ R, a Y ∈ Y) →
      X ⊆ S₀ → 1 ≤ r₀ →
      (∀ Y ∈ crossingLabels G Λ S₀ R r₀ a X, setDist G Λ S₀ (a Y) ≠ ⊤ ∧
        radius r₀ (setDist G Λ S₀ (a Y)).toNat = r₀ ∧
        truncatedSupport G Λ S₀ r₀ (a Y) = ball G Λ (a Y) r₀) ∧
      #(crossingLabels G Λ S₀ R r₀ a X) ≤ 2 * μ V R * #(edgeBoundary G Λ X) * V r₀ ∧
      (∀ Y ∈ crossingLabels G Λ S₀ R r₀ a X,
        Real.log ((q : ℝ) ^ #(truncatedSupport G Λ S₀ r₀ (a Y))) =
          #(truncatedSupport G Λ S₀ r₀ (a Y)) * Real.log q ∧
        (#(truncatedSupport G Λ S₀ r₀ (a Y)) : ℝ) * Real.log q ≤ V r₀ * Real.log q) ∧
      cutBudget G q Λ S₀ R r₀ a X ≤
        1 + #(crossingLabels G Λ S₀ R r₀ a X) * (1 + V r₀ * Real.log q) ^ 2) ∧
    ∀ (K : ℝ) (m : ℕ), (∀ r : ℕ, (V r : ℝ) ≤ K * (r + 1) ^ m) → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Λ S₀ X : Finset σ) (r₀ : ℕ) (a : Finset σ → σ), (∀ Y ∈ supports G Λ R, a Y ∈ Y) →
      X ⊆ S₀ → 1 ≤ r₀ →
      (#(crossingLabels G Λ S₀ R r₀ a X) : ℝ) ≤ C * #(edgeBoundary G Λ X) * (r₀ + 1) ^ m ∧
      (∀ Y ∈ crossingLabels G Λ S₀ R r₀ a X,
        Real.log ((q : ℝ) ^ #(truncatedSupport G Λ S₀ r₀ (a Y))) ≤ C * (r₀ + 1) ^ m) ∧
      cutBudget G q Λ S₀ R r₀ a X ≤ C * (1 + #(edgeBoundary G Λ X)) * (r₀ + 1) ^ (3 * m) := by
  have hL : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : ∀ (Λ S₀ X : Finset σ) (r₀ : ℕ) (a : Finset σ → σ), (∀ Y ∈ supports G Λ R, a Y ∈ Y) →
      X ⊆ S₀ → 1 ≤ r₀ →
      (∀ Y ∈ crossingLabels G Λ S₀ R r₀ a X, setDist G Λ S₀ (a Y) ≠ ⊤ ∧
        radius r₀ (setDist G Λ S₀ (a Y)).toNat = r₀ ∧
        truncatedSupport G Λ S₀ r₀ (a Y) = ball G Λ (a Y) r₀) ∧
      #(crossingLabels G Λ S₀ R r₀ a X) ≤ 2 * μ V R * #(edgeBoundary G Λ X) * V r₀ ∧
      (∀ Y ∈ crossingLabels G Λ S₀ R r₀ a X,
        Real.log ((q : ℝ) ^ #(truncatedSupport G Λ S₀ r₀ (a Y))) =
          #(truncatedSupport G Λ S₀ r₀ (a Y)) * Real.log q ∧
        (#(truncatedSupport G Λ S₀ r₀ (a Y)) : ℝ) * Real.log q ≤ V r₀ * Real.log q) ∧
      cutBudget G q Λ S₀ R r₀ a X ≤
        1 + #(crossingLabels G Λ S₀ R r₀ a X) * (1 + V r₀ * Real.log q) ^ 2 := by
    intro Λ S₀ X r₀ a ha hX _
    -- D4.14.5
    have hdim : ∀ Y ∈ crossingLabels G Λ S₀ R r₀ a X,
        Real.log ((q : ℝ) ^ #(truncatedSupport G Λ S₀ r₀ (a Y))) =
          #(truncatedSupport G Λ S₀ r₀ (a Y)) * Real.log q ∧
        (#(truncatedSupport G Λ S₀ r₀ (a Y)) : ℝ) * Real.log q ≤ V r₀ * Real.log q := by
      intro Y hY
      refine ⟨Real.log_pow _ _, ?_⟩
      rw [(step_4_14_2 G hX hY).2.2]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hV Λ (a Y) r₀) hL
    refine ⟨fun Y hY => step_4_14_2 G hX hY, step_4_14_4 G V hV ha hX, hdim, ?_⟩
    -- D4.14.6
    rw [cutBudget, ← nsmul_eq_mul, ← sum_const]
    gcongr with Y hY
    all_goals
      rw [Real.log_mul (Real.exp_pos 1).ne' (pow_pos hq0 _).ne', Real.log_exp, (hdim Y hY).1]
    · positivity
    · linarith [(hdim Y hY).2]
  refine ⟨h1, fun K m hK => ?_⟩
  have hK0 : 0 ≤ K := by simpa using (Nat.cast_nonneg (V 0)).trans (hK 0)
  have hμ : (0 : ℝ) ≤ μ V R := Nat.cast_nonneg _
  set A : ℝ := 2 * (μ V R : ℝ) * K * (1 + K * Real.log q) ^ 2
  have hA : 0 ≤ A := by positivity
  refine ⟨A + 2 * (μ V R : ℝ) * K + K * Real.log q + 1, by positivity, ?_⟩
  intro Λ S₀ X r₀ a ha hX hr₀
  obtain ⟨-, hc, hd, hb⟩ := h1 Λ S₀ X r₀ a ha hX hr₀
  set ρ : ℝ := ((r₀ : ℝ) + 1) ^ m
  have hρ : 1 ≤ ρ := one_le_pow₀ (by linarith [(Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)])
  have hVr : (V r₀ : ℝ) ≤ K * ρ := hK r₀
  set b : ℝ := (#(edgeBoundary G Λ X) : ℝ)
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have hc' : (#(crossingLabels G Λ S₀ R r₀ a X) : ℝ) ≤ 2 * (μ V R : ℝ) * K * b * ρ := by
    calc (#(crossingLabels G Λ S₀ R r₀ a X) : ℝ) ≤ 2 * (μ V R : ℝ) * b * V r₀ := by
          have := (Nat.cast_le (α := ℝ)).2 hc
          push_cast at this
          exact this
      _ ≤ 2 * (μ V R : ℝ) * b * (K * ρ) := by gcongr
      _ = 2 * (μ V R : ℝ) * K * b * ρ := by ring
  refine ⟨?_, fun Y hY => ?_, ?_⟩
  · refine hc'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hb0) (by linarith))
    nlinarith [mul_nonneg hK0 hL]
  · rw [(hd Y hY).1]
    nlinarith [(hd Y hY).2, mul_nonneg hK0 hL, mul_le_mul_of_nonneg_right hVr hL]
  · have h3 : ((r₀ : ℝ) + 1) ^ (3 * m) = ρ ^ 3 := by rw [mul_comm, pow_mul]
    have hρ3 : 1 ≤ ρ ^ 3 := one_le_pow₀ hρ
    have hlin : 1 + V r₀ * Real.log q ≤ (1 + K * Real.log q) * ρ := by
      nlinarith [mul_le_mul_of_nonneg_right hVr hL]
    have hsq : (1 + V r₀ * Real.log q) ^ 2 ≤ (1 + K * Real.log q) ^ 2 * ρ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlin 2
    have hprod : (#(crossingLabels G Λ S₀ R r₀ a X) : ℝ) * (1 + V r₀ * Real.log q) ^ 2 ≤
        A * b * ρ ^ 3 := by
      calc _ ≤ (2 * (μ V R : ℝ) * K * b * ρ) * ((1 + K * Real.log q) ^ 2 * ρ ^ 2) :=
            mul_le_mul hc' hsq (by positivity) (by positivity)
        _ = A * b * ρ ^ 3 := by ring
    rw [h3]
    refine hb.trans ?_
    have : 0 ≤ (2 * (μ V R : ℝ) * K + K * Real.log q) * (1 + b) * ρ ^ 3 := by positivity
    nlinarith [mul_nonneg hA hb0, mul_nonneg (mul_nonneg hA hb0) (by linarith : (0:ℝ) ≤ ρ ^ 3 - 1)]

/-- D4.14.7. Under `V(r) ≤ K (r+1)^m`, with `C` depending only on `q, R, K, m, C₁, C₂`:
if `b_X ≤ C₂ n D`, `D ≥ 1`, `n ≥ 2` and `r₀ = ⌈C₁ (log n)²⌉`, then
`𝓑_X ≤ C n D (log n)^{6m}`. -/
theorem step_4_14_7 [DecidableRel G.Adj] (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {q : ℕ} (hq : 1 ≤ q)
    (R : ℕ) (K : ℝ) (m : ℕ) (hVpoly : ∀ r : ℕ, (V r : ℝ) ≤ K * (r + 1) ^ m) {C₁ C₂ : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, ∀ (Λ S₀ X : Finset σ) (a : Finset σ → σ) (n D : ℝ),
      (∀ Y ∈ supports G Λ R, a Y ∈ Y) → X ⊆ S₀ → 2 ≤ n → 1 ≤ D →
      (#(edgeBoundary G Λ X) : ℝ) ≤ C₂ * n * D →
      cutBudget G q Λ S₀ R ⌈C₁ * Real.log n ^ 2⌉₊ a X ≤ C * n * D * Real.log n ^ (6 * m) := by
  obtain ⟨C, hC0, hC⟩ := (step_4_14 G V hV hq R).2 K m hVpoly
  refine ⟨C * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ (3 * m), ?_⟩
  intro Λ S₀ X a n D ha hX hn hD hb
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL2 : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos hn
  have hL : 0 < Real.log n := hl2.trans_le hL2
  have hr₀ : 1 ≤ ⌈C₁ * Real.log n ^ 2⌉₊ := Nat.one_le_iff_ne_zero.2
    (Nat.ceil_pos.2 (by positivity)).ne'
  have hr : ((⌈C₁ * Real.log n ^ 2⌉₊ : ℕ) : ℝ) + 1 ≤
      (C₁ + 2 / Real.log 2 ^ 2) * Real.log n ^ 2 := by
    have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ C₁ * Real.log n ^ 2)
    have h2 : 2 ≤ 2 / Real.log 2 ^ 2 * Real.log n ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ hl2.le hL2 2]
    nlinarith
  have hb' : 1 + (#(edgeBoundary G Λ X) : ℝ) ≤ (1 + C₂) * (n * D) := by nlinarith
  refine (hC Λ S₀ X _ a ha hX hr₀).2.2.trans ?_
  -- D4.14.7
  calc C * (1 + (#(edgeBoundary G Λ X) : ℝ)) * (((⌈C₁ * Real.log n ^ 2⌉₊ : ℕ) : ℝ) + 1) ^ (3 * m)
      ≤ C * ((1 + C₂) * (n * D)) * ((C₁ + 2 / Real.log 2 ^ 2) * Real.log n ^ 2) ^ (3 * m) := by
        gcongr
    _ = C * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ (3 * m) * n * D *
        Real.log n ^ (6 * m) := by
        rw [mul_pow, ← pow_mul]
        ring

end AreaLaw
