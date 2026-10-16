/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit
fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/CrossingBudget.lean`. Apache 2.0; adapted to the frozen
`OpenAI.edgeBoundary`, `domainComponent`, `graphNbhd`, and `IsSupportedOn` interfaces.
-/
import OpenAI.Corollary
import OpenAI.FiniteSetTruncationGap
import OpenAI.Rectangles

/-!
# Crossing supports after finite-set truncation

The geometric half of Proposition 4.5 of OAI265, using the repository's square-lattice
boundary and induced-domain neighbourhoods.
-/

namespace OpenAI

open Arealaw

/-- The support designated to a constraint after variable-radius truncation. -/
noncomputable def designatedSupport (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ)
    (a : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  if setDist Λ S₀ a = ⊤ then domainComponent Λ a
  else graphNbhd Λ {a} (truncationRadius r₀ (setDist Λ S₀ a).toNat)

/-- Every designated support lies in the finite domain. -/
theorem designatedSupport_subset (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : ℤ × ℤ) :
    designatedSupport Λ S₀ r₀ a ⊆ Λ := by
  unfold designatedSupport
  split_ifs
  · exact domainComponent_subset Λ a
  · exact graphNbhd_subset Λ {a} _

/-- Labels whose designated support meets both sides of a cut. -/
noncomputable def crossingLabels {κ : Type*} [Fintype κ]
    (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : κ → ℤ × ℤ)
    (X : Finset (ℤ × ℤ)) : Finset κ := by
  classical
  exact Finset.univ.filter fun i =>
    (∃ x ∈ designatedSupport Λ S₀ r₀ (a i), x ∈ X) ∧
      ∃ x ∈ designatedSupport Λ S₀ r₀ (a i), x ∉ X

/-- A crossing designated support has exactly the base radius `r₀`. -/
theorem truncationRadius_eq_of_mem_crossingLabels {κ : Type*} [Fintype κ]
    {Λ S₀ : Finset (ℤ × ℤ)} {r₀ : ℕ} {a : κ → ℤ × ℤ}
    {X : Finset (ℤ × ℤ)} (hX : X ⊆ S₀) {i : κ}
    (hi : i ∈ crossingLabels Λ S₀ r₀ a X) :
    setDist Λ S₀ (a i) ≠ ⊤ ∧
      truncationRadius r₀ (setDist Λ S₀ (a i)).toNat = r₀ ∧
      designatedSupport Λ S₀ r₀ (a i) = graphNbhd Λ {a i} r₀ := by
  classical
  simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨⟨x, hxD, hxX⟩, -⟩ := hi
  have hfin : setDist Λ S₀ (a i) ≠ ⊤ := by
    intro htop
    simp only [designatedSupport, htop, ite_true, domainComponent,
      Finset.mem_filter] at hxD
    have hle : setDist Λ S₀ (a i) ≤ domainEDist Λ (a i) x :=
      Finset.inf_le (hX hxX)
    rw [htop, top_le_iff] at hle
    exact hxD.2 hle
  set d := (setDist Λ S₀ (a i)).toNat with hd
  have hdcoe : (d : ℕ∞) = setDist Λ S₀ (a i) := ENat.natCast_toNat hfin
  simp only [designatedSupport, hfin, ite_false] at hxD
  have hxdr : domainEDist Λ (a i) x ≤
      (truncationRadius r₀ d : ℕ) := by
    rw [domainEDist_comm]
    simpa only [hd] using (mem_graphNbhd_singleton_iff.1 hxD).2
  have hdle : (d : ℕ∞) ≤ domainEDist Λ (a i) x := by
    rw [hdcoe]
    exact Finset.inf_le (hX hxX)
  have hr : truncationRadius r₀ d = r₀ := by
    refine max_eq_left (not_lt.mp fun hlt => ?_)
    have h' : domainEDist Λ (a i) x ≤ ((max r₀ (d / 2) : ℕ) : ℕ∞) := hxdr
    rw [max_eq_right hlt.le] at h'
    have hdd : d ≤ d / 2 := by exact_mod_cast hdle.trans h'
    omega
  refine ⟨hfin, hr, ?_⟩
  simp only [designatedSupport, hfin, ite_false, ← hd, hr]

/-- At most `2 μ K_b (r₀+1)² |∂_Λ X|` designated supports cross `X ⊆ S₀`. -/
theorem card_crossingLabels_le {κ : Type*} [Fintype κ]
    (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : κ → ℤ × ℤ)
    {X : Finset (ℤ × ℤ)} (hX : X ⊆ S₀) {Kb μ : ℝ} (hμ : 0 ≤ μ)
    (hBall : ∀ x (d : ℕ), ((graphNbhd Λ {x} d).card : ℝ) ≤
      Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) :
    ((crossingLabels Λ S₀ r₀ a X).card : ℝ) ≤
      2 * μ * Kb * ((r₀ : ℝ) + 1) ^ 2 * (edgeBoundary Λ X).card := by
  classical
  set P := cutEndpoints Λ X
  set T : Finset (ℤ × ℤ) := P.biUnion fun u => graphNbhd Λ {u} r₀
  have hsub : crossingLabels Λ S₀ r₀ a X ⊆
      T.biUnion fun x => Finset.univ.filter fun i => a i = x := by
    intro i hi
    obtain ⟨-, -, hsupp⟩ := truncationRadius_eq_of_mem_crossingLabels hX hi
    have hi' := hi
    simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and,
      hsupp] at hi'
    obtain ⟨⟨x₁, hx₁, hx₁X⟩, ⟨x₂, hx₂, hx₂X⟩⟩ := hi'
    refine Finset.mem_biUnion.mpr ⟨a i, ?_, by simp⟩
    refine Finset.mem_biUnion.mpr ?_
    by_cases hai : a i ∈ X
    · obtain ⟨hx₂Λ, y, hy, hyΛ, p, hp⟩ := mem_graphNbhd_iff_walk.mp hx₂
      simp only [Finset.mem_singleton] at hy
      subst y
      obtain ⟨u, v, he, p', hp'⟩ := exists_edgeBoundary_of_walk p hai hx₂X
      refine ⟨(u : ℤ × ℤ), ?_, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst he)
      · refine mem_graphNbhd_iff_walk.mpr ⟨hyΛ, (u : ℤ × ℤ), by simp,
          u.2, p'.reverse, ?_⟩
        simpa using hp'.trans hp
    · obtain ⟨hx₁Λ, y, hy, hyΛ, p, hp⟩ := mem_graphNbhd_iff_walk.mp hx₁
      simp only [Finset.mem_singleton] at hy
      subst y
      obtain ⟨d, hd, hd1, hd2⟩ :=
        p.exists_boundary_dart {z | (z : ℤ × ℤ) ∉ X} hai (by simpa using hx₁X)
      have hs := p.dart_fst_mem_support_of_mem_darts hd
      have he : (((d.snd : (Λ : Set (ℤ × ℤ))) : ℤ × ℤ),
          ((d.fst : (Λ : Set (ℤ × ℤ))) : ℤ × ℤ)) ∈ edgeBoundary Λ X := by
        refine mem_edgeBoundary.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨d.fst.2, hd1⟩, ?_⟩
        · simpa using hd2
        · exact (SimpleGraph.induce_adj.mp d.adj).symm
      refine ⟨(d.fst : ℤ × ℤ), ?_, ?_⟩
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd he)
      · refine mem_graphNbhd_iff_walk.mpr ⟨hyΛ, (d.fst : ℤ × ℤ), by simp,
          d.fst.2, (p.takeUntil _ hs).reverse, ?_⟩
        simpa using (p.length_takeUntil_le_length hs).trans hp
  have hKb : 0 ≤ Kb := by
    have h := hBall (0, 0) 0
    have hcard : (0 : ℝ) ≤ (graphNbhd Λ {(0, 0)} 0).card := Nat.cast_nonneg _
    norm_num at h
    linarith
  have hPcard : (P.card : ℝ) ≤ 2 * (edgeBoundary Λ X).card := by
    exact_mod_cast card_cutEndpoints_le
  calc
    ((crossingLabels Λ S₀ r₀ a X).card : ℝ) ≤
        ((T.biUnion fun x => Finset.univ.filter fun i => a i = x).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ T, ((Finset.univ.filter fun i => a i = x).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ T, μ := Finset.sum_le_sum fun x _ => hMult x
    _ = T.card * μ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ u ∈ P, ((graphNbhd Λ {u} r₀).card : ℝ)) * μ := by
      gcongr
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ (∑ _u ∈ P, Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by
      gcongr with u hu
      exact hBall u r₀
    _ = P.card * (Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (edgeBoundary Λ X).card) *
        (Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by
      gcongr
    _ = 2 * μ * Kb * ((r₀ : ℝ) + 1) ^ 2 * (edgeBoundary Λ X).card := by
      ring

/-- The logarithmic cut budget of the designated supports. -/
noncomputable def cutBudget {κ : Type*} [Fintype κ] (q : ℕ)
    (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : κ → ℤ × ℤ)
    (X : Finset (ℤ × ℤ)) : ℝ :=
  1 + ∑ i ∈ crossingLabels Λ S₀ r₀ a X,
    Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport Λ S₀ r₀ (a i)).card) ^ 2

/-- The cut budget always retains its constant term. -/
theorem one_le_cutBudget {κ : Type*} [Fintype κ] (q : ℕ)
    (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : κ → ℤ × ℤ)
    (X : Finset (ℤ × ℤ)) : 1 ≤ cutBudget q Λ S₀ r₀ a X := by
  unfold cutBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- A crossing support has logarithmic dimension at most
`K_b log(q) (r₀+1)²`. -/
theorem log_dim_le_of_mem_crossingLabels {κ : Type*} [Fintype κ]
    {q : ℕ} (hq : 1 ≤ q) {Λ S₀ : Finset (ℤ × ℤ)} {r₀ : ℕ}
    {a : κ → ℤ × ℤ} {X : Finset (ℤ × ℤ)} (hX : X ⊆ S₀)
    {Kb : ℝ} (hBall : ∀ x (d : ℕ), ((graphNbhd Λ {x} d).card : ℝ) ≤
      Kb * ((d : ℝ) + 1) ^ 2) {i : κ}
    (hi : i ∈ crossingLabels Λ S₀ r₀ a X) :
    Real.log ((q : ℝ) ^ (designatedSupport Λ S₀ r₀ (a i)).card) ≤
      Kb * Real.log q * ((r₀ : ℝ) + 1) ^ 2 := by
  obtain ⟨-, -, hsupp⟩ := truncationRadius_eq_of_mem_crossingLabels hX hi
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  rw [Real.log_pow, hsupp]
  calc
    ((graphNbhd Λ {a i} r₀).card : ℝ) * Real.log q ≤
        Kb * ((r₀ : ℝ) + 1) ^ 2 * Real.log q :=
      mul_le_mul_of_nonneg_right (hBall _ _) hlq
    _ = Kb * Real.log q * ((r₀ : ℝ) + 1) ^ 2 := by ring

/-- The cut budget is bounded by a sixth-degree radius factor times the edge boundary. -/
theorem cutBudget_le {κ : Type*} [Fintype κ] {q : ℕ} (hq : 1 ≤ q)
    (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : κ → ℤ × ℤ)
    {X : Finset (ℤ × ℤ)} (hX : X ⊆ S₀) {Kb μ : ℝ}
    (hKb : 0 ≤ Kb) (hμ : 0 ≤ μ)
    (hBall : ∀ x (d : ℕ), ((graphNbhd Λ {x} d).card : ℝ) ≤
      Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) :
    cutBudget q Λ S₀ r₀ a X ≤
      max 1 (2 * μ * Kb * (1 + Kb * Real.log q) ^ 2) *
        (1 + (edgeBoundary Λ X).card) * ((r₀ : ℝ) + 1) ^ 6 := by
  set L := Real.log q
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hq)
  set R := (r₀ : ℝ) + 1
  have hR : 1 ≤ R := by
    simp only [R]
    linarith [(Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)]
  set b : ℝ := ((edgeBoundary Λ X).card : ℝ)
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hterm : ∀ i ∈ crossingLabels Λ S₀ r₀ a X,
      Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport Λ S₀ r₀ (a i)).card) ^ 2 ≤
        (1 + Kb * L) ^ 2 * R ^ 4 := by
    intro i hi
    have hlog := log_dim_le_of_mem_crossingLabels hq hX hBall hi
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have h0 : 0 ≤ Real.log ((q : ℝ) ^
        (designatedSupport Λ S₀ r₀ (a i)).card) := by
      rw [Real.log_pow]
      positivity
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
    have h1 : 1 + Real.log ((q : ℝ) ^
        (designatedSupport Λ S₀ r₀ (a i)).card) ≤ (1 + Kb * L) * R ^ 2 := by
      have heq : Kb * L * R ^ 2 = Kb * L * ((r₀ : ℝ) + 1) ^ 2 := rfl
      nlinarith [mul_nonneg hKb hL]
    calc
      (1 + Real.log ((q : ℝ) ^
          (designatedSupport Λ S₀ r₀ (a i)).card)) ^ 2 ≤
          ((1 + Kb * L) * R ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      _ = (1 + Kb * L) ^ 2 * R ^ 4 := by ring
  have hcard := card_crossingLabels_le Λ S₀ r₀ a hX hμ hBall hMult
  set K := 2 * μ * Kb * (1 + Kb * L) ^ 2
  have hsum : ∑ i ∈ crossingLabels Λ S₀ r₀ a X,
      Real.log (Real.exp 1 * (q : ℝ) ^
        (designatedSupport Λ S₀ r₀ (a i)).card) ^ 2 ≤ K * b * R ^ 6 := by
    calc
      _ ≤ ∑ _i ∈ crossingLabels Λ S₀ r₀ a X,
          (1 + Kb * L) ^ 2 * R ^ 4 := Finset.sum_le_sum hterm
      _ = (crossingLabels Λ S₀ r₀ a X).card *
          ((1 + Kb * L) ^ 2 * R ^ 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * μ * Kb * R ^ 2 * b) * ((1 + Kb * L) ^ 2 * R ^ 4) := by
        gcongr
      _ = K * b * R ^ 6 := by
        simp only [K]
        ring
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hM1 : 1 ≤ max 1 K := le_max_left _ _
  have hMK : K ≤ max 1 K := le_max_right _ _
  unfold cutBudget
  calc
    1 + ∑ i ∈ crossingLabels Λ S₀ r₀ a X,
        Real.log (Real.exp 1 * (q : ℝ) ^
          (designatedSupport Λ S₀ r₀ (a i)).card) ^ 2 ≤
        1 + K * b * R ^ 6 := by linarith
    _ ≤ max 1 K * R ^ 6 + max 1 K * b * R ^ 6 := by
      have hfirst : (1 : ℝ) ≤ max 1 K * R ^ 6 := by nlinarith
      have hsecond : K * b * R ^ 6 ≤ max 1 K * b * R ^ 6 := by gcongr
      linarith
    _ = max 1 K * (1 + b) * R ^ 6 := by ring

/-- Substituting `r₀ = ⌈C₁(log n)²⌉` turns the cut budget into the paper's
`n D (log n)¹²` bound. -/
theorem le_of_cutBudget_le {C C₁ C₂ B n D b : ℝ}
    (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hn : 2 ≤ n) (hD : 1 ≤ D) (hbX : b ≤ C₂ * n * D)
    (hB : B ≤ C * (1 + b) *
      (((⌈C₁ * Real.log n ^ 2⌉₊ : ℕ) : ℝ) + 1) ^ 6) :
    B ≤ C * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ 6 *
      (n * D * Real.log n ^ 12) := by
  set L := Real.log n
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos hn
  have hL : 0 < L := hl2.trans_le hL2
  have hr : ((⌈C₁ * L ^ 2⌉₊ : ℕ) : ℝ) + 1 ≤
      (C₁ + 2 / Real.log 2 ^ 2) * L ^ 2 := by
    have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ C₁ * L ^ 2)
    have h2 : 2 ≤ 2 / Real.log 2 ^ 2 * L ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ hl2.le hL2 2]
    nlinarith
  have hnD : 1 ≤ n * D := by nlinarith
  have hb' : 1 + b ≤ (1 + C₂) * (n * D) := by nlinarith
  refine hB.trans ?_
  calc
    C * (1 + b) * (((⌈C₁ * L ^ 2⌉₊ : ℕ) : ℝ) + 1) ^ 6 ≤
        C * ((1 + C₂) * (n * D)) *
          ((C₁ + 2 / Real.log 2 ^ 2) * L ^ 2) ^ 6 := by
      gcongr
    _ = C * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ 6 *
        (n * D * L ^ 12) := by ring

/-- A truncated constraint acts on its designated support. -/
theorem truncatedConstraint_isSupportedOn {q : ℕ} [NeZero q]
    (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ) (a : ℤ × ℤ)
    {k : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ}
    (hk : IsSupportedOn (domainComponent_subset Λ a) k) :
    IsSupportedOn (designatedSupport_subset Λ S₀ r₀ a)
      (truncatedConstraint q Λ S₀ r₀ a k) := by
  unfold truncatedConstraint designatedSupport
  split_ifs with h
  · exact hk
  · exact isSupportedOn_condExpect _ k

end OpenAI
