import AreaLawRefactored.S10_Amplification.Channels

/-!
# §10.2 Lemma 10.1: kernel, propagation, coupling, (A)

Digest `digest/10-amplification.md` (D10.2.8–D10.2.13), paper
`paper/sections/09-amplification.tex` lines 139–234. Graph-level: ball growth `V` with
`V r ≤ K₀ (r+1)^{m₀}`, at most `μ` labels per anchor.

D10.2.8–D10.2.11 are stated for abstract channel data: maps `𝓔 i` on a normed group, additive
and contractive, and a site functional `d` (the oscillation `d_y`) with `0 ≤ d_y(B) ≤ 2‖B‖`,
the oscillation increment D10.2.7 and the shell bound of D10.2.10 as hypotheses; `C₂` is the
shell constant and `c₁` its rate. The clocks enter through the word law of `Setup.lean`.
-/

universe u v

namespace AreaLaw

open GraphDomain Finset

section Geometry

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ)

-- helper
/-- The triangle inequality for `d_Λ`. -/
theorem domainEDist_triangle (Λ : Finset σ) (x y z : σ) :
    domainEDist G Λ x z ≤ domainEDist G Λ x y + domainEDist G Λ y z := by
  by_cases hx : x ∈ Λ
  · by_cases hy : y ∈ Λ
    · by_cases hz : z ∈ Λ
      · unfold domainEDist
        rw [dif_pos ⟨hx, hz⟩, dif_pos ⟨hx, hy⟩, dif_pos ⟨hy, hz⟩]
        exact SimpleGraph.edist_triangle
      · rw [show domainEDist G Λ y z = ⊤ from dif_neg fun h => hz h.2]; simp
    · rw [show domainEDist G Λ x y = ⊤ from dif_neg fun h => hy h.2]; simp
  · rw [show domainEDist G Λ x y = ⊤ from dif_neg fun h => hx h.1]; simp

-- helper
/-- `d_Λ(x, S) ≤ d_Λ(x, y) + d_Λ(y, S)`. -/
theorem setDist_le_add (Λ S : Finset σ) (x y : σ) :
    setDist G Λ S x ≤ domainEDist G Λ x y + setDist G Λ S y := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [setDist]
  obtain ⟨s, hs, hs'⟩ := Finset.exists_mem_eq_inf S hS (fun s => domainEDist G Λ y s)
  unfold setDist
  rw [hs']
  exact (Finset.inf_le (f := fun s => domainEDist G Λ x s) hs).trans
    (domainEDist_triangle G Λ x y s)

-- helper
theorem exists_setDist_eq {Λ S : Finset σ} {x : σ} (h : setDist G Λ S x ≠ ⊤) :
    ∃ s ∈ S, setDist G Λ S x = domainEDist G Λ x s := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [setDist] at h
  exact Finset.exists_mem_eq_inf S hS _

-- helper
theorem mem_graphNbhd_iff {Λ S : Finset σ} {r : ℕ} {x : σ} :
    x ∈ graphNbhd G Λ S r ↔ x ∈ Λ ∧ setDist G Λ S x ≤ r := by
  simp [graphNbhd, setDist, Finset.inf_eq_iInf]

-- helper
theorem domainEDist_le_of_mem_ball {Λ : Finset σ} {a y z : σ} {l : ℕ}
    (hy : y ∈ graphNbhd G Λ {a} l) (hz : z ∈ graphNbhd G Λ {a} l) :
    domainEDist G Λ y z ≤ (2 * l : ℕ) := by
  have h1 := ((mem_ball G).1 hy).2
  have h2 := ((mem_ball G).1 hz).2
  rw [domainEDist_comm] at h2
  calc domainEDist G Λ y z ≤ domainEDist G Λ y a + domainEDist G Λ a z :=
        domainEDist_triangle G Λ y a z
    _ ≤ l + l := add_le_add h1 h2
    _ = (2 * l : ℕ) := by push_cast; ring

/-- The weight `e^{-a d_Λ(y, S)^α}`, `0` when `d_Λ(y, S) = ∞`. -/
noncomputable def decay (Λ S : Finset σ) (a α : ℝ) (y : σ) : ℝ :=
  if setDist G Λ S y = ⊤ then 0 else Real.exp (-a * ((setDist G Λ S y).toNat : ℝ) ^ α)

variable {G}

theorem decay_nonneg (Λ S : Finset σ) (a α : ℝ) (y : σ) : 0 ≤ decay G Λ S a α y := by
  unfold decay; split_ifs <;> positivity

theorem decay_eq_one {Λ S : Finset σ} (hS : S ⊆ Λ) (a : ℝ) {α : ℝ} (hα : 0 < α) {y : σ}
    (hy : y ∈ S) : decay G Λ S a α y = 1 := by
  have h0 : setDist G Λ S y = 0 := by
    refine le_antisymm ((Finset.inf_le (f := fun s => domainEDist G Λ y s) hy).trans ?_)
      (zero_le)
    unfold domainEDist
    rw [dif_pos ⟨hS hy, hS hy⟩, SimpleGraph.edist_self]
  rw [decay, h0, if_neg ENat.zero_ne_top, ENat.toNat_zero, Nat.cast_zero,
    Real.zero_rpow hα.ne', mul_zero, Real.exp_zero]

/-- D10.2.9 (route). `d_Λ(y,S)^α ≤ d_Λ(z,S)^α + d_Λ(y,z)^α`, i.e.
`e^{-a d(z,S)^α} ≤ e^{-a d(y,S)^α} e^{a e^α}` when `d_Λ(y, z) ≤ e`. -/
theorem decay_le_mul {Λ S : Finset σ} {a α : ℝ} (ha : 0 ≤ a) (hα : 0 < α) (hα1 : α ≤ 1)
    {y z : σ} {e : ℕ} (he : domainEDist G Λ y z ≤ e) :
    decay G Λ S a α z ≤ decay G Λ S a α y * Real.exp (a * (e : ℝ) ^ α) := by
  by_cases hz : setDist G Λ S z = ⊤
  · rw [decay, if_pos hz]; exact mul_nonneg (decay_nonneg _ _ _ _ _) (Real.exp_pos _).le
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.1 hz
  have hy : setDist G Λ S y ≤ (e + p : ℕ) := (setDist_le_add G Λ S y z).trans (by
    rw [← hp]; push_cast; gcongr)
  obtain ⟨q, hq⟩ : ∃ q : ℕ, setDist G Λ S y = q :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hy)).symm⟩
  rw [hq, Nat.cast_le] at hy
  unfold decay
  rw [if_neg hz, ← hp, hq, if_neg (ENat.natCast_ne_top q), ENat.toNat_natCast, ENat.toNat_natCast,
    ← Real.exp_add, Real.exp_le_exp]
  have h1 : (q : ℝ) ^ α ≤ ((e : ℝ) + p) ^ α :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hy) hα.le
  have h2 := Real.rpow_add_le_add_rpow (Nat.cast_nonneg e) (Nat.cast_nonneg p) hα.le hα1
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) ha
  rw [mul_add] at h3
  linarith

end Geometry

/-! ## Counting -/

section Counting

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ)

-- helper
/-- At most `μ |T|` labels have their anchor in `T`. -/
theorem card_label_le {ι : Type*} [Fintype ι] (anc : ι → σ) {μ : ℕ}
    (hμ : ∀ y, #{i | anc i = y} ≤ μ) (T : Finset σ) : #{i | anc i ∈ T} ≤ μ * #T := by
  classical
  calc #{i | anc i ∈ T} ≤ #(T.biUnion fun y => ({i | anc i = y} : Finset ι)) :=
        card_le_card fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi
          simp only [mem_biUnion, mem_filter, mem_univ, true_and]
          exact ⟨_, hi, rfl⟩
    _ ≤ ∑ y ∈ T, #{i | anc i = y} := card_biUnion_le
    _ ≤ ∑ _y ∈ T, μ := sum_le_sum fun y _ => hμ y
    _ = μ * #T := by rw [sum_const, smul_eq_mul, mul_comm]

-- helper
/-- At most `μ V l` labels have `y ∈ N_l(a_i)`. -/
theorem card_label_ball_le (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {Λ : Finset σ}
    {ι : Type*} [Fintype ι] (anc : ι → σ) (hanc : ∀ i, anc i ∈ Λ) {μ : ℕ}
    (hμ : ∀ y, #{i | anc i = y} ≤ μ) (y : σ) (l : ℕ) :
    #{i | y ∈ graphNbhd G Λ {anc i} l} ≤ μ * V l :=
  calc #{i | y ∈ graphNbhd G Λ {anc i} l} ≤ #{i | anc i ∈ ball G Λ y l} :=
        card_le_card fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi ⊢
          exact (mem_ball G).2 ⟨hanc i, (domainEDist_comm G Λ _ _).trans_le
            ((mem_ball G).1 hi).2⟩
    _ ≤ μ * #(ball G Λ y l) := card_label_le anc hμ _
    _ ≤ μ * V l := Nat.mul_le_mul_left _ (hV Λ y l)

/-- D10.2.13. The retained labels (anchors in `N_r(S)`) number at most `μ |S| V r`. -/
theorem card_retained_le (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) (Λ S : Finset σ)
    {ι : Type*} [Fintype ι] (anc : ι → σ) {μ : ℕ} (hμ : ∀ y, #{i | anc i = y} ≤ μ) (r : ℕ) :
    #{i | anc i ∈ graphNbhd G Λ S r} ≤ μ * #S * V r := by
  have hsub : graphNbhd G Λ S r ⊆ S.biUnion fun s => ball G Λ s r := fun x hx => by
    obtain ⟨hxΛ, hxr⟩ := (mem_graphNbhd_iff G).1 hx
    obtain ⟨s, hs, hs'⟩ := exists_setDist_eq G (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hxr)
    exact mem_biUnion.2 ⟨s, hs, (mem_ball G).2 ⟨hxΛ, hs' ▸ hxr⟩⟩
  calc #{i | anc i ∈ graphNbhd G Λ S r} ≤ μ * #(graphNbhd G Λ S r) := card_label_le anc hμ _
    _ ≤ μ * ∑ s ∈ S, #(ball G Λ s r) := Nat.mul_le_mul_left _ ((card_le_card hsub).trans
        card_biUnion_le)
    _ ≤ μ * ∑ _s ∈ S, V r := Nat.mul_le_mul_left _ (sum_le_sum fun s _ => hV Λ s r)
    _ = μ * #S * V r := by rw [sum_const, smul_eq_mul, mul_assoc]

end Counting

/-! ## Constants -/

section Constants

/-- `∑_{l ≥ 0} (l+1)^k e^{-b l^α}`. -/
noncomputable def polyExpSum (k : ℕ) (b α : ℝ) : ℝ :=
  ∑' l : ℕ, ((l : ℝ) + 1) ^ k * Real.exp (-b * (l : ℝ) ^ α)

theorem summable_polyExp {b α : ℝ} (hb : 0 < b) (hα : 0 < α) (k : ℕ) :
    Summable fun l : ℕ => ((l : ℝ) + 1) ^ k * Real.exp (-b * (l : ℝ) ^ α) := by
  obtain ⟨M, hM, hMb⟩ := step_4_12_6 hb hα (k + 2)
  have h2 : Summable fun l : ℕ => 1 / ((l : ℝ) + 1) ^ 2 := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) (h2.mul_left M)
  have h := hMb l (Nat.cast_nonneg l)
  have hpos : (0 : ℝ) < ((l : ℝ) + 1) ^ 2 := by positivity
  rw [mul_one_div, le_div_iff₀ hpos]
  have he : ((l : ℝ) + 1) ^ k * Real.exp (-b * (l : ℝ) ^ α) * ((l : ℝ) + 1) ^ 2 =
      ((l : ℝ) + 1) ^ (k + 2) * Real.exp (-(b * (l : ℝ) ^ α)) := by
    rw [neg_mul, pow_add]; ring
  rw [he]; exact h

theorem polyExpSum_nonneg (k : ℕ) (b α : ℝ) : 0 ≤ polyExpSum k b α :=
  tsum_nonneg fun l => by positivity

theorem sum_le_polyExpSum {b α : ℝ} (hb : 0 < b) (hα : 0 < α) (k N : ℕ) :
    ∑ l ∈ range N, ((l : ℝ) + 1) ^ k * Real.exp (-b * (l : ℝ) ^ α) ≤ polyExpSum k b α :=
  (summable_polyExp hb hα k).sum_le_tsum _ fun l _ => by positivity

/-- D10.2.8. The weight exponent `a = c₁/4` (so `a 2^α ≤ c₁/2`). -/
noncomputable def kernelExp (c₁ : ℝ) : ℝ := c₁ / 4

/-- D10.2.8. The light-cone rate
`v = 2 C₂ μ K₀² ∑_l (l+1)^{2m₀} e^{-(c₁/2) l^α}`. -/
noncomputable def lightCone (C₂ c₁ α : ℝ) (μ : ℕ) (K₀ : ℝ) (m₀ : ℕ) : ℝ :=
  2 * C₂ * μ * K₀ ^ 2 * polyExpSum (2 * m₀) (c₁ / 2) α

theorem lightCone_nonneg {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (c₁ α : ℝ) (μ : ℕ) (K₀ : ℝ) (m₀ : ℕ) :
    0 ≤ lightCone C₂ c₁ α μ K₀ m₀ := by
  unfold lightCone; have := polyExpSum_nonneg (2 * m₀) (c₁ / 2) α; positivity

theorem kernelExp_pos {c₁ : ℝ} (hc₁ : 0 < c₁) : 0 < kernelExp c₁ := by
  unfold kernelExp; positivity

-- helper
/-- `g (m+1) ≤ N g m + X a^m`, `g 0 = 0`, `0 ≤ N ≤ a` give `g m ≤ X m a^{m-1}`. -/
theorem le_mul_pow_of_succ_le {g : ℕ → ℝ} {N a X : ℝ} (hN : 0 ≤ N) (hNa : N ≤ a)
    (hX : 0 ≤ X) (h0 : g 0 = 0) (hs : ∀ m, g (m + 1) ≤ N * g m + X * a ^ m) :
    ∀ m, g m ≤ X * (m * a ^ (m - 1)) := by
  intro m
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    refine (hs m).trans ?_
    have ha : 0 ≤ a := hN.trans hNa
    have hm : N * (m * a ^ (m - 1)) ≤ m * a ^ m := by
      rcases m with _ | m
      · simp
      · rw [Nat.add_sub_cancel, pow_succ]
        have := mul_le_mul_of_nonneg_left hNa
          (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * a ^ m)
        linarith
    calc N * g m + X * a ^ m ≤ N * (X * (m * a ^ (m - 1))) + X * a ^ m := by gcongr
      _ = X * (N * (m * a ^ (m - 1))) + X * a ^ m := by ring
      _ ≤ X * (m * a ^ m) + X * a ^ m := by gcongr
      _ = X * (((m + 1 : ℕ) : ℝ) * a ^ (m + 1 - 1)) := by
          rw [Nat.add_sub_cancel]; push_cast; ring

end Constants

/-! ## D10.2.8 The kernel -/

section Kernel

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ)

/-- D10.2.8. `A_{yz} = 2 C₂ ∑_i ∑_{l ≥ 0} e^{-c₁ l^α} 1{y, z ∈ N_l(a_i)}` (`l ≤ |Λ|` suffices:
`N_l(a_i)` is the component of `a_i` for `l ≥ |Λ|`). -/
noncomputable def kernel (Λ : Finset σ) {ι : Type*} [Fintype ι] (anc : ι → σ) (C₂ c₁ α : ℝ)
    (y z : σ) : ℝ :=
  2 * C₂ * ∑ i, ∑ l ∈ range (#Λ + 1),
    if y ∈ graphNbhd G Λ {anc i} l ∧ z ∈ graphNbhd G Λ {anc i} l then
      Real.exp (-c₁ * (l : ℝ) ^ α) else 0

variable {G}

theorem kernel_nonneg {Λ : Finset σ} {ι : Type*} [Fintype ι] (anc : ι → σ) {C₂ : ℝ}
    (hC₂ : 0 ≤ C₂) (c₁ α : ℝ) (y z : σ) : 0 ≤ kernel G Λ anc C₂ c₁ α y z := by
  unfold kernel
  refine mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun l _ => ?_)
  split_ifs <;> positivity

/-- D10.2.8. No kernel entries between components. -/
theorem kernel_eq_zero {Λ : Finset σ} {ι : Type*} [Fintype ι] (anc : ι → σ) (C₂ c₁ α : ℝ)
    {y z : σ} (h : domainEDist G Λ y z = ⊤) : kernel G Λ anc C₂ c₁ α y z = 0 := by
  unfold kernel
  rw [sum_eq_zero fun i _ => sum_eq_zero fun l _ => if_neg fun hyz => ?_, mul_zero]
  have := domainEDist_le_of_mem_ball G hyz.1 hyz.2
  rw [h] at this
  exact ENat.natCast_ne_top _ (top_le_iff.1 this)

/-- D10.2.8. D10.2.7 summed over the labels is `∑_z A_{yz} d_z(B)`. -/
theorem sum_increment_eq (Λ : Finset σ) {ι : Type*} [Fintype ι] (anc : ι → σ) (C₂ c₁ α : ℝ)
    (y : σ) (f : σ → ℝ) :
    ∑ i, 2 * C₂ * ∑ l ∈ range (#Λ + 1), (if y ∈ graphNbhd G Λ {anc i} l then
      Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, f z else 0) =
      ∑ z ∈ Λ, kernel G Λ anc C₂ c₁ α y z * f z := by
  have key : ∀ i l, (if y ∈ graphNbhd G Λ {anc i} l then
      Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, f z else 0) =
      ∑ z ∈ Λ, (if y ∈ graphNbhd G Λ {anc i} l ∧ z ∈ graphNbhd G Λ {anc i} l then
        Real.exp (-c₁ * (l : ℝ) ^ α) else 0) * f z := by
    intro i l
    split_ifs with hy
    · simp only [hy, true_and, ite_mul, zero_mul]
      rw [sum_ite_mem, inter_eq_right.2 (graphNbhd_subset G Λ {anc i} l), mul_sum]
    · simp [hy]
  calc _ = ∑ i, ∑ l ∈ range (#Λ + 1), ∑ z ∈ Λ, 2 * C₂ *
        ((if y ∈ graphNbhd G Λ {anc i} l ∧ z ∈ graphNbhd G Λ {anc i} l then
          Real.exp (-c₁ * (l : ℝ) ^ α) else 0) * f z) := by
          simp only [key]; simp only [mul_sum]
    _ = ∑ i, ∑ z ∈ Λ, ∑ l ∈ range (#Λ + 1), 2 * C₂ *
        ((if y ∈ graphNbhd G Λ {anc i} l ∧ z ∈ graphNbhd G Λ {anc i} l then
          Real.exp (-c₁ * (l : ℝ) ^ α) else 0) * f z) := sum_congr rfl fun i _ => sum_comm
    _ = ∑ z ∈ Λ, ∑ i, ∑ l ∈ range (#Λ + 1), 2 * C₂ *
        ((if y ∈ graphNbhd G Λ {anc i} l ∧ z ∈ graphNbhd G Λ {anc i} l then
          Real.exp (-c₁ * (l : ℝ) ^ α) else 0) * f z) := sum_comm
    _ = _ := by simp only [kernel, mul_sum, sum_mul, mul_assoc]

/-- D10.2.8 (eq:amplification-weighted-kernel). With `a = c₁/4`:
`sup_y ∑_{z : d_Λ(y,z) < ∞} A_{yz} e^{a d_Λ(y,z)^α} ≤ v`, `v` depending only on
`C₂, c₁, α, μ, K₀, m₀`. -/
theorem step_10_2_8 (V : ℕ → ℕ) (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {K₀ : ℝ} {m₀ : ℕ} (hVK : ∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) (μ : ℕ) {α C₂ c₁ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC₂ : 0 ≤ C₂) (hc₁ : 0 < c₁) (Λ : Finset σ) {ι : Type*}
    [Fintype ι] (anc : ι → σ) (hanc : ∀ i, anc i ∈ Λ) (hμ : ∀ y, #{i | anc i = y} ≤ μ)
    (y : σ) :
    ∑ z ∈ Λ, kernel G Λ anc C₂ c₁ α y z *
        Real.exp (kernelExp c₁ * ((domainEDist G Λ y z).toNat : ℝ) ^ α) ≤
      lightCone C₂ c₁ α μ K₀ m₀ := by
  set N := fun i l => graphNbhd G Λ {anc i} l
  set e := fun l : ℕ => Real.exp (-(c₁ / 2) * (l : ℝ) ^ α)
  -- radius `l`: `d_Λ(y,z) ≤ 2l` and `a (2l)^α ≤ (c₁/2) l^α`
  have hterm : ∀ z ∈ Λ, kernel G Λ anc C₂ c₁ α y z *
      Real.exp (kernelExp c₁ * ((domainEDist G Λ y z).toNat : ℝ) ^ α) ≤
      2 * C₂ * ∑ i, ∑ l ∈ range (#Λ + 1), if y ∈ N i l ∧ z ∈ N i l then e l else 0 := by
    intro z _
    unfold kernel
    rw [mul_assoc, sum_mul]
    gcongr with i _
    rw [sum_mul]
    gcongr with l _
    split_ifs with h
    · have hd := ENat.toNat_le_of_le_natCast (domainEDist_le_of_mem_ball G h.1 h.2)
      have h2 : (2 : ℝ) ^ α ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
      have h3 : ((domainEDist G Λ y z).toNat : ℝ) ^ α ≤ 2 * (l : ℝ) ^ α :=
        calc _ ≤ ((2 * l : ℕ) : ℝ) ^ α :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast hd) hα.le
          _ = 2 ^ α * (l : ℝ) ^ α := by push_cast; exact Real.mul_rpow (by norm_num) (by positivity)
          _ ≤ 2 * (l : ℝ) ^ α := by gcongr
      rw [← Real.exp_add, Real.exp_le_exp]
      unfold kernelExp
      nlinarith
    · simp
  -- `≤ μ V l` labels with `y ∈ N_l(a_i)`, `≤ V l` sites in `N_l(a_i)`
  have hcount : ∀ l, ∑ i, ∑ z ∈ Λ, (if y ∈ N i l ∧ z ∈ N i l then e l else 0) ≤
      μ * (V l : ℝ) ^ 2 * e l := by
    intro l
    calc ∑ i, ∑ z ∈ Λ, (if y ∈ N i l ∧ z ∈ N i l then e l else 0) ≤
          ∑ i, if y ∈ N i l then (V l : ℝ) * e l else 0 := by
          gcongr with i
          split_ifs with hy
          · simp only [hy, true_and]
            rw [sum_ite_mem, sum_const, nsmul_eq_mul]
            gcongr
            exact_mod_cast (card_le_card inter_subset_right).trans (hV Λ (anc i) l)
          · simp [hy]
      _ = #{i | y ∈ N i l} * ((V l : ℝ) * e l) := by rw [← sum_filter, sum_const, nsmul_eq_mul]
      _ ≤ (μ * V l : ℕ) * ((V l : ℝ) * e l) := by
          gcongr; exact_mod_cast card_label_ball_le G V hV anc hanc hμ y l
      _ = μ * (V l : ℝ) ^ 2 * e l := by push_cast; ring
  have hK₀ : 0 ≤ K₀ := by have := hVK 0; simp at this; linarith [(V 0).cast_nonneg (α := ℝ)]
  calc _ ≤ ∑ z ∈ Λ, 2 * C₂ * ∑ i, ∑ l ∈ range (#Λ + 1),
          (if y ∈ N i l ∧ z ∈ N i l then e l else 0) := sum_le_sum hterm
    _ = 2 * C₂ * ∑ z ∈ Λ, ∑ i, ∑ l ∈ range (#Λ + 1),
          (if y ∈ N i l ∧ z ∈ N i l then e l else 0) := by rw [← mul_sum]
    _ = 2 * C₂ * ∑ i, ∑ z ∈ Λ, ∑ l ∈ range (#Λ + 1),
          (if y ∈ N i l ∧ z ∈ N i l then e l else 0) := by rw [sum_comm]
    _ = 2 * C₂ * ∑ i, ∑ l ∈ range (#Λ + 1), ∑ z ∈ Λ,
          (if y ∈ N i l ∧ z ∈ N i l then e l else 0) := by
        congr 1; exact sum_congr rfl fun i _ => sum_comm
    _ = 2 * C₂ * ∑ l ∈ range (#Λ + 1), ∑ i, ∑ z ∈ Λ,
          (if y ∈ N i l ∧ z ∈ N i l then e l else 0) := by rw [sum_comm]
    _ ≤ 2 * C₂ * ∑ l ∈ range (#Λ + 1), μ * (V l : ℝ) ^ 2 * e l :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun l _ => hcount l) (by positivity)
    _ ≤ 2 * C₂ * ∑ l ∈ range (#Λ + 1), μ * K₀ ^ 2 * (((l : ℝ) + 1) ^ (2 * m₀) * e l) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun l _ => ?_) (by positivity)
        have h0 : (0 : ℝ) ≤ V l := Nat.cast_nonneg _
        have he : 0 ≤ e l := (Real.exp_pos _).le
        calc (μ : ℝ) * (V l : ℝ) ^ 2 * e l ≤ μ * (K₀ * ((l : ℝ) + 1) ^ m₀) ^ 2 * e l := by
              gcongr; exact hVK l
          _ = _ := by ring
    _ ≤ lightCone C₂ c₁ α μ K₀ m₀ := by
        have h := sum_le_polyExpSum (half_pos hc₁) hα (2 * m₀) (#Λ + 1)
        have h0 : 0 ≤ 2 * C₂ * μ * K₀ ^ 2 := by positivity
        rw [← mul_sum, lightCone]
        calc 2 * C₂ * (μ * K₀ ^ 2 * ∑ l ∈ range (#Λ + 1), ((l : ℝ) + 1) ^ (2 * m₀) * e l) =
              2 * C₂ * μ * K₀ ^ 2 * ∑ l ∈ range (#Λ + 1), ((l : ℝ) + 1) ^ (2 * m₀) * e l := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h h0

end Kernel

/-! ## D10.2.9 Propagation, D10.2.10 omitted events, D10.2.11 coupling -/

section Propagation

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ)

/-- D10.2.9 (eq:amplification-propagation), word form. For `B` with `d_y(B) = 0` off `S`,
maps `R_i ∈ {𝓔_i, id}` (`id` for omitted labels) and `B_w` the operator after the events of
the word `w`: `∑_{|w| = m} d_y(B_w) ≤ 2‖B‖ (N + v)^m e^{-a d_Λ(y,S)^α}`, and `= 0` when
`d_Λ(y,S) = ∞` (`decay` is `0` there); `N = |ι|`, `a = c₁/4`, `v` from D10.2.8. -/
theorem step_10_2_9 (V : ℕ → ℕ) (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {K₀ : ℝ} {m₀ : ℕ} (hVK : ∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) (μ : ℕ) {α C₂ c₁ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC₂ : 0 ≤ C₂) (hc₁ : 0 < c₁) {Λ S : Finset σ} (hS : S ⊆ Λ)
    {ι : Type*} [Fintype ι] (anc : ι → σ) (hanc : ∀ i, anc i ∈ Λ)
    (hμ : ∀ y, #{i | anc i = y} ≤ μ) {Xt : Type*} [NormedAddCommGroup Xt] (𝓔 : ι → Xt → Xt)
    (d : σ → Xt → ℝ) (hd0 : ∀ y B, 0 ≤ d y B) (hd2 : ∀ y B, d y B ≤ 2 * ‖B‖)
    (hd7 : ∀ i y B, d y (𝓔 i B) ≤ d y B + 2 * C₂ * ∑ l ∈ range (#Λ + 1),
      (if y ∈ graphNbhd G Λ {anc i} l then
        Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, d z B else 0))
    (R : ι → Xt → Xt) (hR : ∀ i, R i = 𝓔 i ∨ R i = id) (B : Xt) (hB : ∀ y ∉ S, d y B = 0)
    (m : ℕ) (y : σ) :
    ∑ w : Fin m → ι, d y (wordMap R m w B) ≤
      2 * ‖B‖ * (Fintype.card ι + lightCone C₂ c₁ α μ K₀ m₀) ^ m *
        decay G Λ S (kernelExp c₁) α y := by
  set N : ℝ := (Fintype.card ι : ℝ)
  set v := lightCone C₂ c₁ α μ K₀ m₀
  set a := kernelExp c₁
  have ha : 0 ≤ a := (kernelExp_pos hc₁).le
  have hv : 0 ≤ v := lightCone_nonneg hC₂ c₁ α μ K₀ m₀
  induction m generalizing y with
  | zero =>
    -- initial data: `d_y(B) ≤ 2‖B‖ 1_S(y)`
    simp only [Finset.univ_unique, sum_singleton, wordMap_zero, pow_zero, mul_one]
    by_cases hy : y ∈ S
    · rw [decay_eq_one hS a hα hy, mul_one]; exact hd2 y B
    · rw [hB y hy]; exact mul_nonneg (by positivity) (decay_nonneg _ _ _ _ _)
  | succ m ih =>
    set P := 2 * ‖B‖ * (N + v) ^ m
    have hP : 0 ≤ P := by positivity
    -- one step of the word adds one event: jump formula with D10.2.7–D10.2.8
    have hstep : ∀ i (B' : Xt), d y (R i B') ≤ d y B' + 2 * C₂ * ∑ l ∈ range (#Λ + 1),
        (if y ∈ graphNbhd G Λ {anc i} l then
          Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, d z B' else 0) := by
      intro i B'
      rcases hR i with h | h
      · rw [h]; exact hd7 i y B'
      · rw [h, id]
        refine le_add_of_nonneg_right (mul_nonneg (by positivity) (sum_nonneg fun l _ => ?_))
        split_ifs
        · exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun z _ => hd0 z B')
        · exact le_rfl
    -- `e^{a d(y,S)^α} A_{yz} f(z) ≤ A_{yz} e^{a d(y,z)^α} sup f`
    have hz : ∀ z ∈ Λ, kernel G Λ anc C₂ c₁ α y z *
        ∑ w : Fin m → ι, d z (wordMap R m w B) ≤ kernel G Λ anc C₂ c₁ α y z *
          (P * (decay G Λ S a α y *
            Real.exp (a * ((domainEDist G Λ y z).toNat : ℝ) ^ α))) := by
      intro z _
      by_cases hyz : domainEDist G Λ y z = ⊤
      · simp [kernel_eq_zero anc C₂ c₁ α hyz]
      refine mul_le_mul_of_nonneg_left ((ih z).trans (mul_le_mul_of_nonneg_left ?_ hP))
        (kernel_nonneg anc hC₂ c₁ α y z)
      exact decay_le_mul ha hα hα1 (ENat.natCast_toNat hyz).symm.le
    rw [sum_word_succ]
    simp only [wordMap_succ, Fin.cons_zero, Fin.tail_cons]
    calc ∑ i, ∑ w : Fin m → ι, d y (R i (wordMap R m w B)) ≤
          ∑ i, ∑ w : Fin m → ι, (d y (wordMap R m w B) + 2 * C₂ * ∑ l ∈ range (#Λ + 1),
            (if y ∈ graphNbhd G Λ {anc i} l then Real.exp (-c₁ * (l : ℝ) ^ α) *
              ∑ z ∈ graphNbhd G Λ {anc i} l, d z (wordMap R m w B) else 0)) :=
          sum_le_sum fun i _ => sum_le_sum fun w _ => hstep i _
      _ = N * ∑ w : Fin m → ι, d y (wordMap R m w B) +
          ∑ z ∈ Λ, kernel G Λ anc C₂ c₁ α y z * ∑ w : Fin m → ι, d z (wordMap R m w B) := by
          simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
          congr 1
          rw [sum_comm]
          calc _ = ∑ w : Fin m → ι, ∑ z ∈ Λ,
                kernel G Λ anc C₂ c₁ α y z * d z (wordMap R m w B) :=
                sum_congr rfl fun w _ => sum_increment_eq Λ anc C₂ c₁ α y _
            _ = _ := by rw [sum_comm]; simp only [mul_sum]
      _ ≤ N * P * decay G Λ S a α y + ∑ z ∈ Λ, kernel G Λ anc C₂ c₁ α y z *
          (P * (decay G Λ S a α y *
            Real.exp (a * ((domainEDist G Λ y z).toNat : ℝ) ^ α))) :=
          add_le_add ((mul_le_mul_of_nonneg_left (ih y) (Nat.cast_nonneg _)).trans_eq
            (mul_assoc _ _ _).symm) (sum_le_sum hz)
      _ = P * decay G Λ S a α y * (N + ∑ z ∈ Λ, kernel G Λ anc C₂ c₁ α y z *
            Real.exp (a * ((domainEDist G Λ y z).toNat : ℝ) ^ α)) := by
          rw [mul_add, mul_sum]; congr 1; · ring
          exact sum_congr rfl fun z _ => by ring
      _ ≤ P * decay G Λ S a α y * (N + v) := by
          gcongr
          · exact mul_nonneg hP (decay_nonneg _ _ _ _ _)
          · exact step_10_2_8 (G := G) V hV hVK μ hα hα1 hC₂ hc₁ Λ anc hanc hμ y
      _ = 2 * ‖B‖ * (N + v) ^ (m + 1) * decay G Λ S a α y := by ring

/-- D10.2.10 (eq:amplification-omitted-event). For `i` with `d = d_Λ(a_i, S) > r`, `d < ∞`:
`𝔼‖(𝓔_i - id) B_u‖ ≤ C ‖B‖ e^{vu - c' d^α}`; word form
`∑_{|w| = m} ‖(𝓔_i - id) B_w‖ ≤ C ‖B‖ (N + v)^m e^{-c' d^α}`, `c' = a`, and `0` when
`d = ∞`. -/
theorem step_10_2_10 (V : ℕ → ℕ) (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {K₀ : ℝ} {m₀ : ℕ} (hVK : ∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) (μ : ℕ) {α C₂ c₁ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC₂ : 0 ≤ C₂) (hc₁ : 0 < c₁) :
    ∃ C'' : ℝ, 0 ≤ C'' ∧ ∀ (Λ S : Finset σ), S ⊆ Λ → ∀ {ι : Type u} [Fintype ι] (anc : ι → σ),
      (∀ i, anc i ∈ Λ) → (∀ y, #{i | anc i = y} ≤ μ) →
      ∀ {Xt : Type v} [NormedAddCommGroup Xt] (𝓔 : ι → Xt → Xt) (d : σ → Xt → ℝ),
      (∀ y B, 0 ≤ d y B) → (∀ y B, d y B ≤ 2 * ‖B‖) →
      (∀ i y B, d y (𝓔 i B) ≤ d y B + 2 * C₂ * ∑ l ∈ range (#Λ + 1),
        (if y ∈ graphNbhd G Λ {anc i} l then
          Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, d z B else 0)) →
      (∀ i B, ‖𝓔 i B - B‖ ≤ C₂ * ∑ l ∈ range (#Λ + 1),
        Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, d z B) →
      ∀ R : ι → Xt → Xt, (∀ i, R i = 𝓔 i ∨ R i = id) → ∀ B : Xt, (∀ y ∉ S, d y B = 0) →
      ∀ (m : ℕ) (i : ι),
        ∑ w : Fin m → ι, ‖𝓔 i (wordMap R m w B) - wordMap R m w B‖ ≤
          C'' * ‖B‖ * (Fintype.card ι + lightCone C₂ c₁ α μ K₀ m₀) ^ m *
            decay G Λ S (kernelExp c₁) α (anc i) := by
  have hK₀ : 0 ≤ K₀ := by have := hVK 0; simp at this; linarith [(V 0).cast_nonneg (α := ℝ)]
  have hb : 0 < 3 * c₁ / 4 := by positivity
  refine ⟨2 * C₂ * K₀ * polyExpSum m₀ (3 * c₁ / 4) α,
    by have := polyExpSum_nonneg m₀ (3 * c₁ / 4) α; positivity, ?_⟩
  intro Λ S hS ι _ anc hanc hμ Xt _ 𝓔 d hd0 hd2 hd7 hshell R hR B hB m i
  set a := kernelExp c₁
  set P := 2 * ‖B‖ * (Fintype.card ι + lightCone C₂ c₁ α μ K₀ m₀) ^ m
  set δ := decay G Λ S a α (anc i)
  have hP : 0 ≤ P := by have := lightCone_nonneg hC₂ c₁ α μ K₀ m₀; positivity
  have hδ : 0 ≤ δ := decay_nonneg _ _ _ _ _
  -- D10.2.9 at the sites of `N_l(a_i)`, with `d(z,S)^α ≥ δ^α - l^α`
  have hf : ∀ l, ∀ z ∈ graphNbhd G Λ {anc i} l, ∑ w : Fin m → ι, d z (wordMap R m w B) ≤
      P * (δ * Real.exp (a * (l : ℝ) ^ α)) := fun l z hz =>
    (step_10_2_9 G V hV hVK μ hα hα1 hC₂ hc₁ hS anc hanc hμ 𝓔 d hd0 hd2 hd7 R hR B hB m z).trans
      (mul_le_mul_of_nonneg_left (decay_le_mul (kernelExp_pos hc₁).le hα hα1
        ((domainEDist_comm G Λ _ _).trans_le ((mem_ball G).1 hz).2)) hP)
  calc ∑ w : Fin m → ι, ‖𝓔 i (wordMap R m w B) - wordMap R m w B‖ ≤
        ∑ w : Fin m → ι, C₂ * ∑ l ∈ range (#Λ + 1), Real.exp (-c₁ * (l : ℝ) ^ α) *
          ∑ z ∈ graphNbhd G Λ {anc i} l, d z (wordMap R m w B) :=
        sum_le_sum fun w _ => hshell i _
    _ = C₂ * ∑ l ∈ range (#Λ + 1), Real.exp (-c₁ * (l : ℝ) ^ α) *
          ∑ z ∈ graphNbhd G Λ {anc i} l, ∑ w : Fin m → ι, d z (wordMap R m w B) := by
        rw [← mul_sum]; congr 1
        rw [sum_comm]; refine sum_congr rfl fun l _ => ?_
        rw [← mul_sum, sum_comm]
    _ ≤ C₂ * ∑ l ∈ range (#Λ + 1), Real.exp (-c₁ * (l : ℝ) ^ α) *
          ∑ _z ∈ graphNbhd G Λ {anc i} l, P * (δ * Real.exp (a * (l : ℝ) ^ α)) := by
        gcongr with l _ z hz; exact hf l z hz
    _ ≤ C₂ * ∑ l ∈ range (#Λ + 1), P * δ * (K₀ * (((l : ℝ) + 1) ^ m₀ *
          Real.exp (-(3 * c₁ / 4) * (l : ℝ) ^ α))) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun l _ => ?_) hC₂
        rw [sum_const, nsmul_eq_mul]
        have hcard : (#(graphNbhd G Λ {anc i} l) : ℝ) ≤ K₀ * ((l : ℝ) + 1) ^ m₀ :=
          (Nat.cast_le.2 (hV Λ (anc i) l)).trans (hVK l)
        have he : Real.exp (-c₁ * (l : ℝ) ^ α) * Real.exp (a * (l : ℝ) ^ α) =
            Real.exp (-(3 * c₁ / 4) * (l : ℝ) ^ α) := by
          rw [← Real.exp_add]; congr 1; simp only [a, kernelExp]; ring
        calc Real.exp (-c₁ * (l : ℝ) ^ α) * (#(graphNbhd G Λ {anc i} l) *
              (P * (δ * Real.exp (a * (l : ℝ) ^ α)))) =
              P * δ * (#(graphNbhd G Λ {anc i} l) * Real.exp (-(3 * c₁ / 4) * (l : ℝ) ^ α)) := by
              rw [← he]; ring
          _ ≤ P * δ * (K₀ * ((l : ℝ) + 1) ^ m₀ * Real.exp (-(3 * c₁ / 4) * (l : ℝ) ^ α)) := by
              gcongr
          _ = _ := by ring
    _ ≤ C₂ * (P * δ * (K₀ * polyExpSum m₀ (3 * c₁ / 4) α)) := by
        rw [← mul_sum, ← mul_sum]
        gcongr
        exact sum_le_polyExpSum hb hα m₀ _
    _ = 2 * C₂ * K₀ * polyExpSum m₀ (3 * c₁ / 4) α * ‖B‖ *
          (Fintype.card ι + lightCone C₂ c₁ α μ K₀ m₀) ^ m * δ := by
        simp only [P]; ring

/-- D10.2.11 (eq:amplification-channel-omission). With `R_i = 𝓔_i` for retained labels
(`d_Λ(a_i, S) ≤ r`) and `id` otherwise, on the same clocks:
`𝔼‖𝓔_full(B) - 𝓔_ret(B)‖ ≤ C' t |S| ‖B‖ e^{vt - c'' r^α}`, finite. -/
theorem step_10_2_11 (V : ℕ → ℕ) (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {K₀ : ℝ} {m₀ : ℕ} (hVK : ∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) (μ : ℕ) {α C₂ c₁ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC₂ : 0 ≤ C₂) (hc₁ : 0 < c₁) :
    ∃ C' c' : ℝ, 0 ≤ C' ∧ 0 < c' ∧ ∀ (Λ S : Finset σ), S ⊆ Λ →
      ∀ {ι : Type u} [Fintype ι] (anc : ι → σ),
      (∀ i, anc i ∈ Λ) → (∀ y, #{i | anc i = y} ≤ μ) →
      ∀ {Xt : Type v} [NormedAddCommGroup Xt] (𝓔 : ι → Xt → Xt) (d : σ → Xt → ℝ),
      (∀ i B B', 𝓔 i (B - B') = 𝓔 i B - 𝓔 i B') → (∀ i B, ‖𝓔 i B‖ ≤ ‖B‖) →
      (∀ y B, 0 ≤ d y B) → (∀ y B, d y B ≤ 2 * ‖B‖) →
      (∀ i y B, d y (𝓔 i B) ≤ d y B + 2 * C₂ * ∑ l ∈ range (#Λ + 1),
        (if y ∈ graphNbhd G Λ {anc i} l then
          Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, d z B else 0)) →
      (∀ i B, ‖𝓔 i B - B‖ ≤ C₂ * ∑ l ∈ range (#Λ + 1),
        Real.exp (-c₁ * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {anc i} l, d z B) →
      ∀ (r : ℕ) (B : Xt), (∀ y ∉ S, d y B = 0) → ∀ t : ℝ, 0 ≤ t →
        let R : ι → Xt → Xt := fun i => if anc i ∈ graphNbhd G Λ S r then 𝓔 i else id
        Summable (fun m => clockWeight (Fintype.card ι) t m *
          ∑ w : Fin m → ι, ‖wordMap 𝓔 m w B - wordMap R m w B‖) ∧
        clockExp ι t (fun m w => ‖wordMap 𝓔 m w B - wordMap R m w B‖) ≤
          C' * t * #S * ‖B‖ *
            Real.exp (lightCone C₂ c₁ α μ K₀ m₀ * t - c' * (r : ℝ) ^ α) := by
  obtain ⟨C'', hC'', h10⟩ := step_10_2_10 G V hV hVK μ hα hα1 hC₂ hc₁
  have hK₀ : 0 ≤ K₀ := by have := hVK 0; simp at this; linarith [(V 0).cast_nonneg (α := ℝ)]
  have ha : 0 < kernelExp c₁ := kernelExp_pos hc₁
  refine ⟨C'' * μ * K₀ * polyExpSum m₀ (kernelExp c₁ / 2) α, kernelExp c₁ / 2,
    by have := polyExpSum_nonneg m₀ (kernelExp c₁ / 2) α; positivity, half_pos ha, ?_⟩
  intro Λ S hS ι _ anc hanc hμ Xt _ 𝓔 d h𝓔sub h𝓔 hd0 hd2 hd7 hshell r B hB t ht R
  set a := kernelExp c₁
  set N : ℝ := (Fintype.card ι : ℝ)
  set v := lightCone C₂ c₁ α μ K₀ m₀
  have hv : 0 ≤ v := lightCone_nonneg hC₂ c₁ α μ K₀ m₀
  have hRdef : ∀ i, R i = if anc i ∈ graphNbhd G Λ S r then 𝓔 i else id := fun i => rfl
  have hR : ∀ i, R i = 𝓔 i ∨ R i = id := fun i => by
    rw [hRdef]; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- the omitted labels' weights `Q = ∑_{i omitted} e^{-a d_i^α}`
  set Q := ∑ i, if anc i ∈ graphNbhd G Λ S r then 0 else decay G Λ S a α (anc i) with hQdef
  have hQ0 : 0 ≤ Q := sum_nonneg fun i _ => by
    split_ifs
    · exact le_rfl
    · exact decay_nonneg _ _ _ _ _
  -- anchors at distance `l > r` from `S`: at most `μ |S| V l` of them
  have hQ : Q ≤ #S * (μ * K₀ * Real.exp (-(a / 2) * (r : ℝ) ^ α)) *
      polyExpSum m₀ (a / 2) α := by
    have hpt : ∀ i, (if anc i ∈ graphNbhd G Λ S r then 0 else decay G Λ S a α (anc i)) ≤
        ∑ s ∈ S, ∑ l ∈ range (#Λ + 1), if domainEDist G Λ (anc i) s = l then
          Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l : ℝ) ^ α) else 0 := by
      intro i
      have h0 : ∀ s, ∀ l : ℕ, 0 ≤ if domainEDist G Λ (anc i) s = l then
          Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l : ℝ) ^ α) else 0 :=
        fun s l => by split_ifs <;> positivity
      split_ifs with hret
      · exact sum_nonneg fun s _ => sum_nonneg fun l _ => h0 s l
      by_cases htop : setDist G Λ S (anc i) = ⊤
      · rw [decay, if_pos htop]; exact sum_nonneg fun s _ => sum_nonneg fun l _ => h0 s l
      obtain ⟨s, hs, hs'⟩ := exists_setDist_eq G htop
      obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 htop
      have hD : domainEDist G Λ (anc i) s = l := hs'.symm.trans hl.symm
      have hlr : r < l := by
        by_contra h
        exact hret ((mem_graphNbhd_iff G).2 ⟨hanc i, by rw [← hl]; exact_mod_cast not_lt.1 h⟩)
      have hlΛ : l < #Λ := by
        have := domainEDist_lt_card G (by rw [hD]; exact ENat.natCast_ne_top l)
        rw [hD] at this; exact_mod_cast this
      have hrl : (r : ℝ) ^ α ≤ (l : ℝ) ^ α :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlr.le) hα.le
      calc decay G Λ S a α (anc i) ≤
            Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l : ℝ) ^ α) := by
            rw [decay, if_neg htop, ← hl, ENat.toNat_natCast, ← Real.exp_add, Real.exp_le_exp]
            have := mul_le_mul_of_nonneg_left hrl (half_pos ha).le
            linarith
        _ = if domainEDist G Λ (anc i) s = l then Real.exp (-(a / 2) * (r : ℝ) ^ α) *
              Real.exp (-(a / 2) * (l : ℝ) ^ α) else 0 := by rw [if_pos hD]
        _ ≤ ∑ l' ∈ range (#Λ + 1), if domainEDist G Λ (anc i) s = l' then
              Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l' : ℝ) ^ α) else 0 :=
            single_le_sum (f := fun l' : ℕ => if domainEDist G Λ (anc i) s = l' then
              Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l' : ℝ) ^ α) else 0)
              (fun l' _ => h0 s l') (mem_range.2 (by omega))
        _ ≤ _ := single_le_sum (f := fun s' => ∑ l' ∈ range (#Λ + 1),
              if domainEDist G Λ (anc i) s' = l' then Real.exp (-(a / 2) * (r : ℝ) ^ α) *
                Real.exp (-(a / 2) * (l' : ℝ) ^ α) else 0)
              (fun s' _ => sum_nonneg fun l' _ => h0 s' l') hs
    have hcnt : ∀ s ∈ S, ∀ l : ℕ,
        (#{i | domainEDist G Λ (anc i) s = l} : ℝ) ≤ μ * K₀ * ((l : ℝ) + 1) ^ m₀ := by
      intro s _ l
      have h1 : #{i | domainEDist G Λ (anc i) s = l} ≤ #{i | s ∈ graphNbhd G Λ {anc i} l} :=
        card_le_card fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi ⊢
          have hsΛ : s ∈ Λ := by
            by_contra h
            rw [show domainEDist G Λ (anc i) s = ⊤ from dif_neg fun h' => h h'.2] at hi
            exact ENat.natCast_ne_top l hi.symm
          exact (mem_ball G).2 ⟨hsΛ, ((domainEDist_comm G Λ _ _).trans hi).le⟩
      calc (#{i | domainEDist G Λ (anc i) s = l} : ℝ) ≤ ((μ * V l : ℕ) : ℝ) := by
            exact_mod_cast h1.trans (card_label_ball_le G V hV anc hanc hμ s l)
        _ ≤ μ * K₀ * ((l : ℝ) + 1) ^ m₀ := by
            push_cast; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hVK l) (Nat.cast_nonneg _)
    calc Q ≤ ∑ i, ∑ s ∈ S, ∑ l ∈ range (#Λ + 1), if domainEDist G Λ (anc i) s = l then
          Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l : ℝ) ^ α) else 0 :=
          sum_le_sum fun i _ => hpt i
      _ = ∑ s ∈ S, ∑ l ∈ range (#Λ + 1), (#{i | domainEDist G Λ (anc i) s = l} : ℝ) *
          (Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l : ℝ) ^ α)) := by
          rw [sum_comm]; refine sum_congr rfl fun s _ => ?_
          rw [sum_comm]; refine sum_congr rfl fun l _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ S, ∑ l ∈ range (#Λ + 1), μ * K₀ * ((l : ℝ) + 1) ^ m₀ *
          (Real.exp (-(a / 2) * (r : ℝ) ^ α) * Real.exp (-(a / 2) * (l : ℝ) ^ α)) := by
          gcongr with s hs l _; exact hcnt s hs l
      _ = #S * ∑ l ∈ range (#Λ + 1), (μ * K₀ * Real.exp (-(a / 2) * (r : ℝ) ^ α)) *
          (((l : ℝ) + 1) ^ m₀ * Real.exp (-(a / 2) * (l : ℝ) ^ α)) := by
          rw [sum_const, nsmul_eq_mul]; congr 1; exact sum_congr rfl fun l _ => by ring
      _ ≤ #S * (μ * K₀ * Real.exp (-(a / 2) * (r : ℝ) ^ α)) * polyExpSum m₀ (a / 2) α := by
          rw [← mul_sum, ← mul_assoc]
          gcongr
          exact sum_le_polyExpSum (half_pos ha) hα m₀ _
  -- D10.2.11: telescoping along the word, only omitted events contribute
  have hg : ∀ m, ∑ w : Fin m → ι, ‖wordMap 𝓔 m w B - wordMap R m w B‖ ≤
      C'' * ‖B‖ * Q * (m * (N + v) ^ (m - 1)) := by
    refine le_mul_pow_of_succ_le (N := N) (a := N + v) (X := C'' * ‖B‖ * Q) (by positivity)
      (by linarith) (by positivity) (by simp) fun m => ?_
    rw [sum_word_succ]
    simp only [wordMap_succ, Fin.cons_zero, Fin.tail_cons]
    have hpt : ∀ i (F R' : Xt), ‖𝓔 i F - R i R'‖ ≤
        ‖F - R'‖ + if anc i ∈ graphNbhd G Λ S r then 0 else ‖𝓔 i R' - R'‖ := by
      intro i F R'
      rw [hRdef]
      split_ifs with h
      · rw [← h𝓔sub, add_zero]; exact h𝓔 i _
      · calc ‖𝓔 i F - id R'‖ = ‖𝓔 i (F - R') + (𝓔 i R' - R')‖ := by
              rw [h𝓔sub, id]; abel_nf
          _ ≤ ‖F - R'‖ + ‖𝓔 i R' - R'‖ := (norm_add_le _ _).trans (by gcongr; exact h𝓔 i _)
    calc ∑ i, ∑ w : Fin m → ι, ‖𝓔 i (wordMap 𝓔 m w B) - R i (wordMap R m w B)‖ ≤
          ∑ i, ∑ w : Fin m → ι, (‖wordMap 𝓔 m w B - wordMap R m w B‖ +
            if anc i ∈ graphNbhd G Λ S r then 0 else
              ‖𝓔 i (wordMap R m w B) - wordMap R m w B‖) :=
          sum_le_sum fun i _ => sum_le_sum fun w _ => hpt i _ _
      _ = N * ∑ w : Fin m → ι, ‖wordMap 𝓔 m w B - wordMap R m w B‖ +
          ∑ i, if anc i ∈ graphNbhd G Λ S r then 0 else
            ∑ w : Fin m → ι, ‖𝓔 i (wordMap R m w B) - wordMap R m w B‖ := by
          simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
          congr 1
          exact sum_congr rfl fun i _ => by split_ifs <;> simp
      _ ≤ N * ∑ w : Fin m → ι, ‖wordMap 𝓔 m w B - wordMap R m w B‖ +
          ∑ i, if anc i ∈ graphNbhd G Λ S r then 0 else
            C'' * ‖B‖ * (N + v) ^ m * decay G Λ S a α (anc i) := by
          gcongr with i
          split_ifs
          · exact le_rfl
          · exact h10 Λ S hS anc hanc hμ 𝓔 d hd0 hd2 hd7 hshell R hR B hB m i
      _ = N * ∑ w : Fin m → ι, ‖wordMap 𝓔 m w B - wordMap R m w B‖ +
          C'' * ‖B‖ * Q * (N + v) ^ m := by
          congr 1
          rw [hQdef, mul_sum, sum_mul]
          exact sum_congr rfl fun i _ => by split_ifs <;> ring
  -- Campbell's formula, on the word law
  obtain ⟨hsum, hle⟩ := clockExp_le_of_sum_le_mul ht (fun m w => norm_nonneg _) hg
  refine ⟨hsum, hle.trans ?_⟩
  rw [show N + v - N = v by ring, sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]
  calc C'' * ‖B‖ * Q * (t * Real.exp (v * t)) =
        C'' * ‖B‖ * t * Real.exp (v * t) * Q := by ring
    _ ≤ C'' * ‖B‖ * t * Real.exp (v * t) * (#S * (μ * K₀ * Real.exp (-(a / 2) * (r : ℝ) ^ α)) *
          polyExpSum m₀ (a / 2) α) := by gcongr
    _ = _ := by ring

end Propagation

/-! ## D10.2.13 Proof of (A) and support -/

section ProofA

open Matrix
open scoped Matrix.Norms.L2Operator

-- helper
/-- A product of contractions is a contraction. -/
theorem norm_wordProd_le {ι n : Type*} [Fintype n] [DecidableEq n] {Gt : ι → Matrix n n ℂ}
    (hG : ∀ i, ‖Gt i‖ ≤ 1) : ∀ m (w : Fin m → ι), ‖wordProd Gt m w‖ ≤ 1
  | 0, _ => Arealaw.l2_opNorm_one_le
  | m + 1, _ => (norm_mul_le _ _).trans
      (mul_le_one₀ (hG _) (norm_nonneg _) (norm_wordProd_le hG m _))

/-- D10.2.13 ((A), abstract). If `‖G_i‖, ‖G_i'‖ ≤ 1` and `‖G_i - G_i'‖ ≤ δ` for retained `i`,
the products over the retained events satisfy `𝔼‖∏ G_{i_j} - ∏ G'_{i_j}‖ ≤ t |ret| δ`
(telescoping, contractions), and the expectation is finite. -/
theorem step_10_2_13 {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (Gf Gr : ι → Matrix n n ℂ) (hGf : ∀ i, ‖Gf i‖ ≤ 1) (hGr : ∀ i, ‖Gr i‖ ≤ 1)
    (ret : ι → Prop) [DecidablePred ret] {δ : ℝ} (hδ : 0 ≤ δ)
    (hret : ∀ i, ret i → ‖Gf i - Gr i‖ ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι,
      ‖wordProd (fun i => if ret i then Gf i else 1) m w -
        wordProd (fun i => if ret i then Gr i else 1) m w‖) ∧
    clockExp ι t (fun m w => ‖wordProd (fun i => if ret i then Gf i else 1) m w -
      wordProd (fun i => if ret i then Gr i else 1) m w‖) ≤ t * #{i | ret i} * δ := by
  set A := fun i => if ret i then Gf i else 1
  set B := fun i => if ret i then Gr i else 1
  have hA : ∀ i, ‖A i‖ ≤ 1 := fun i => by
    simp only [A]; split_ifs; exacts [hGf i, Arealaw.l2_opNorm_one_le]
  have hB : ∀ i, ‖B i‖ ≤ 1 := fun i => by
    simp only [B]; split_ifs; exacts [hGr i, Arealaw.l2_opNorm_one_le]
  have hAB : ∀ i, ‖A i - B i‖ ≤ if ret i then δ else 0 := fun i => by
    simp only [A, B]; split_ifs with h; exacts [hret i h, by simp]
  have hg : ∀ m, ∑ w : Fin m → ι, ‖wordProd A m w - wordProd B m w‖ ≤
      (#{i | ret i} * δ) * (m * (Fintype.card ι : ℝ) ^ (m - 1)) := by
    refine le_mul_pow_of_succ_le (N := (Fintype.card ι : ℝ)) (a := (Fintype.card ι : ℝ))
      (X := #{i | ret i} * δ) (by positivity) le_rfl (by positivity) (by simp) fun m => ?_
    rw [sum_word_succ]
    simp only [wordProd_succ, Fin.cons_zero, Fin.tail_cons]
    calc ∑ i, ∑ w : Fin m → ι, ‖A i * wordProd A m w - B i * wordProd B m w‖ ≤
          ∑ i, ∑ w : Fin m → ι, (‖wordProd A m w - wordProd B m w‖ +
            if ret i then δ else 0) := by
          gcongr with i _ w _
          calc ‖A i * wordProd A m w - B i * wordProd B m w‖ =
                ‖A i * (wordProd A m w - wordProd B m w) + (A i - B i) * wordProd B m w‖ := by
                congr 1; noncomm_ring
            _ ≤ ‖A i‖ * ‖wordProd A m w - wordProd B m w‖ + ‖A i - B i‖ * ‖wordProd B m w‖ :=
                (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
            _ ≤ 1 * ‖wordProd A m w - wordProd B m w‖ + (if ret i then δ else 0) * 1 := by
                gcongr
                · exact hA i
                · exact hAB i
                · exact norm_wordProd_le hB m w
            _ = _ := by ring
      _ = (Fintype.card ι : ℝ) * ∑ w : Fin m → ι, ‖wordProd A m w - wordProd B m w‖ +
          #{i | ret i} * δ * (Fintype.card ι : ℝ) ^ m := by
          simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun,
            Fintype.card_fin]
          congr 1
          rw [← mul_sum, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
          push_cast; ring
  obtain ⟨hsum, hle⟩ := clockExp_le_of_sum_le_mul ht (fun m w => norm_nonneg _) hg
  refine ⟨hsum, hle.trans_eq ?_⟩
  rw [sub_self, zero_mul, Real.exp_zero]; ring

end ProofA

section Support

open Arealaw Matrix

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

omit [∀ i, Fintype (loc i)] in
-- helper
theorem IsSupportedOn.one {S T : Finset σ} (h : S ⊆ T) :
    OpenAI.IsSupportedOn h (1 : Matrix (Reg loc T) (Reg loc T) ℂ) :=
  ⟨1, (extendId_one h).symm⟩

-- helper
theorem IsSupportedOn.mul {S T : Finset σ} {h : S ⊆ T} {A B : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hA : OpenAI.IsSupportedOn h A) (hB : OpenAI.IsSupportedOn h B) :
    OpenAI.IsSupportedOn h (A * B) := by
  obtain ⟨A', rfl⟩ := hA
  obtain ⟨B', rfl⟩ := hB
  exact ⟨A' * B', (extendId_mul h A' B').symm⟩

omit [∀ i, Fintype (loc i)] in
-- helper
theorem IsSupportedOn.mono {S S' T : Finset σ} {h : S ⊆ T}
    {A : Matrix (Reg loc T) (Reg loc T) ℂ} (hA : OpenAI.IsSupportedOn h A) (hSS' : S ⊆ S')
    (h' : S' ⊆ T) : OpenAI.IsSupportedOn h' A := by
  obtain ⟨A', rfl⟩ := hA
  exact ⟨extendId hSS' A', (Arealaw.extendId_extendId hSS' h' A').symm⟩

/-- D10.2.13 (support). If each retained factor `G_{i,r}` is supported on `N_r(a_i)` and
retained anchors satisfy `d_Λ(a_i, S) ≤ r`, the product over the retained events is supported
on `N_{2r}(S)`. -/
theorem isSupportedOn_wordProd (G : SimpleGraph σ) {Λ S : Finset σ} {r : ℕ} {ι : Type*}
    (anc : ι → σ) (ret : ι → Prop) [DecidablePred ret]
    (hret : ∀ i, ret i → anc i ∈ graphNbhd G Λ S r)
    (Gr : ι → Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (hGr : ∀ i, ret i → OpenAI.IsSupportedOn (graphNbhd_subset G Λ {anc i} r) (Gr i)) :
    ∀ m (w : Fin m → ι), OpenAI.IsSupportedOn (graphNbhd_subset G Λ S (2 * r))
      (wordProd (fun i => if ret i then Gr i else 1) m w)
  | 0, _ => IsSupportedOn.one _
  | m + 1, w => by
    refine IsSupportedOn.mul ?_ (isSupportedOn_wordProd G anc ret hret Gr hGr m _)
    dsimp only
    split_ifs with h
    · refine IsSupportedOn.mono (hGr _ h) (fun x hx => ?_) _
      obtain ⟨hxΛ, hx'⟩ := (mem_ball G).1 hx
      obtain ⟨-, ha⟩ := (mem_graphNbhd_iff G).1 (hret _ h)
      refine (mem_graphNbhd_iff G).2 ⟨hxΛ, (setDist_le_add G Λ S x (anc (w 0))).trans ?_⟩
      calc domainEDist G Λ x (anc (w 0)) + setDist G Λ S (anc (w 0)) ≤ r + r :=
            add_le_add hx' ha
        _ = (2 * r : ℕ) := by push_cast; ring
    · exact IsSupportedOn.one _

end Support

/-! ## D10.2 Lemma 10.1 -/

section Lemma101

open Arealaw Matrix
open scoped Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

-- helper
/-- A nonnegative observable below a summable one has a summable, smaller expectation. -/
theorem clockExp_mono {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t)
    {F F' : ∀ m : ℕ, (Fin m → ι) → ℝ} (hF : ∀ m w, 0 ≤ F m w)
    (hFF' : ∀ m w, F m w ≤ F' m w)
    (hs : Summable fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F' m w) :
    Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w) ∧
      clockExp ι t F ≤ clockExp ι t F' := by
  have hle : ∀ m, clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w ≤
      clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F' m w := fun m =>
    mul_le_mul_of_nonneg_left (sum_le_sum fun w _ => hFF' m w) (clockWeight_nonneg _ ht m)
  have hs' := Summable.of_nonneg_of_le (fun m => mul_nonneg (clockWeight_nonneg _ ht m)
    (sum_nonneg fun w _ => hF m w)) hle hs
  exact ⟨hs', hs'.tsum_le_tsum hle hs⟩

-- helper
theorem dotProduct_tensVec {n κ : Type*} [Fintype n] [Fintype κ] (Ω : n → ℂ) (ξ : κ → ℂ) :
    star (tensVec Ω ξ) ⬝ᵥ tensVec Ω ξ = (star Ω ⬝ᵥ Ω) * (star ξ ⬝ᵥ ξ) := by
  simp only [dotProduct, tensVec, Pi.star_apply, star_mul', Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

-- helper
theorem norm_sqrt_one_sub_le {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (h0 : 0 ≤ M) : ‖CFC.sqrt (1 - M)‖ ≤ 1 :=
  l2_opNorm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _)
    (by simpa using CFC.sqrt_le_sqrt (1 - M) 1 (by simpa using h0))

-- helper
/-- The positive square root commutes with extension by the identity. -/
theorem sqrt_extendId {S T : Finset σ} (h : S ⊆ T) {Z : Matrix (Reg loc S) (Reg loc S) ℂ}
    (hZ : 0 ≤ Z) : CFC.sqrt (extendId h Z) = extendId h (CFC.sqrt Z) := by
  have hext : 0 ≤ extendId h Z := by
    rw [Matrix.nonneg_iff_posSemidef] at hZ ⊢; exact posSemidef_extendId h hZ
  have hsqrt : 0 ≤ extendId h (CFC.sqrt Z) := by
    have := CFC.sqrt_nonneg Z
    rw [Matrix.nonneg_iff_posSemidef] at this ⊢; exact posSemidef_extendId h this
  refine (CFC.sqrt_eq_iff _ _ hext hsqrt).mpr ?_
  rw [← extendId_mul, CFC.sqrt_mul_sqrt_self Z hZ]

-- helper
/-- D10.2.13. `G_{i,l} = (I - E_{i,l} k_i)^{1/2}` is supported on `N_l(a_i)`. -/
theorem isSupportedOn_sqrt_one_sub_E [∀ i, Nonempty (loc i)] (G : SimpleGraph σ) {Λ : Finset σ}
    (a : σ) (l : ℕ)
    {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk : k ≤ 1) :
    OpenAI.IsSupportedOn (graphNbhd_subset G Λ {a} l) (CFC.sqrt (1 - E G Λ a l k)) := by
  set h := graphNbhd_subset G Λ {a} l
  set Z := (Fintype.card (Reg loc (Λ \ graphNbhd G Λ {a} l)) : ℂ)⁻¹ • ptrace h (1 - k)
  have hZ : 0 ≤ Z := by
    have h1 : 0 ≤ 1 - k := sub_nonneg.2 hk
    rw [Matrix.nonneg_iff_posSemidef] at h1 ⊢
    exact (posSemidef_ptrace h h1).smul (by positivity)
  have hE : 1 - E G Λ a l k = extendId h Z := by
    rw [← (eq_quasilocal_ce (G := G) Λ a l).1, ← E_sub]
    simp only [E, OpenAI.condExpect, Z, extendId_smul]
  rw [hE, sqrt_extendId h hZ]
  exact ⟨_, rfl⟩

/-- D10.2 (Lemma 10.1, `lem:amplification-local-products`). Let `k_i` be positive contractions
anchored at `a_i ∈ Λ`, at most `μ` labels per anchor, with
`‖k_i - E_{i,l} k_i‖ ≤ C e^{-c l^α}` (`l ≥ 0`). Put `G_i = (I - k_i)^{1/2}`. Fix `t ≥ 0`,
`r ≥ 1`, `S ⊆ Λ`, rate-one Poisson clocks at the labels on `[0, t]`, later factors on the left:
`D` the product of all `G_i` over events, `D_ret` over events with `d_Λ(a_i, S) ≤ r` only, `L`
the product of `G_{i,r} = (I - E_{i,r} k_i)^{1/2}` over the same retained events. There are
`C, c, v > 0`, independent of `|Λ|` and of spectator dimensions, with
`𝔼‖D_ret - L‖ ≤ C t |S| (1+r)^{m₀} e^{-c r^α}` (A); `L` is a contraction supported on
`N_{2r}(S)`; if `k_i Ω = 0` and `B` is supported on `S ∪` spectators, then for every unit
spectator vector `ξ`, `𝔼‖(D - D_ret) B (Ω ⊗ ξ)‖ ≤ C t |S| ‖B‖ e^{vt - c r^α}` (B). (A), (B)
hold on the same clock space. -/
theorem lemma_10_1 (G : SimpleGraph σ) (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {K₀ : ℝ} {m₀ : ℕ}
    (hVK : ∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) (μ : ℕ) {α C c : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hc : 0 < c) [∀ i, Nonempty (loc i)] :
    ∃ C' c' v : ℝ, 0 ≤ C' ∧ 0 < c' ∧ 0 ≤ v ∧
    ∀ (Λ : Finset σ) (ι : Type) [Fintype ι] [DecidableEq ι] (anc : ι → σ), (∀ i, anc i ∈ Λ) →
      (∀ y, #{i | anc i = y} ≤ μ) → ∀ k : ι → Matrix (Reg loc Λ) (Reg loc Λ) ℂ,
      (∀ i, 0 ≤ k i ∧ k i ≤ 1) →
      (∀ i (l : ℕ), 0 ≤ E G Λ (anc i) l (k i) ∧ E G Λ (anc i) l (k i) ≤ 1 ∧
        ‖k i - E G Λ (anc i) l (k i)‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α)) →
    ∀ (t : ℝ), 0 ≤ t → ∀ (r : ℕ), 1 ≤ r → ∀ S : Finset σ, S ⊆ Λ →
      let ret := fun i => anc i ∈ graphNbhd G Λ S r
      let D := wordProd (fun i => CFC.sqrt (1 - k i))
      let Dret := wordProd (fun i => if ret i then CFC.sqrt (1 - k i) else 1)
      let L := wordProd (fun i => if ret i then CFC.sqrt (1 - E G Λ (anc i) r (k i)) else 1)
      -- (A)
      (Summable (fun m => clockWeight (Fintype.card ι) t m *
          ∑ w : Fin m → ι, ‖Dret m w - L m w‖) ∧
        clockExp ι t (fun m w => ‖Dret m w - L m w‖) ≤
          C' * t * #S * ((r : ℝ) + 1) ^ m₀ * Real.exp (-c' * (r : ℝ) ^ α)) ∧
      -- `L` is a contraction supported on `N_{2r}(S)`
      (∀ m w, ‖L m w‖ ≤ 1 ∧ OpenAI.IsSupportedOn (graphNbhd_subset G Λ S (2 * r)) (L m w)) ∧
      -- (B)
      ∀ (Ω : Reg loc Λ → ℂ), (∀ i, k i *ᵥ Ω = 0) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
        (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
        (∀ A : Matrix (Reg loc (Λ \ S)) (Reg loc (Λ \ S)) ℂ,
          Commute (extendId (Finset.sdiff_subset : Λ \ S ⊆ Λ) A ⊗ₖ (1 : Matrix κ κ ℂ)) B) →
        ∀ ξ : κ → ℂ, star Ω ⬝ᵥ Ω = 1 → star ξ ⬝ᵥ ξ = 1 →
        Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι,
          vnorm (((D m w - Dret m w) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ (B *ᵥ tensVec Ω ξ))) ∧
        clockExp ι t (fun m w =>
            vnorm (((D m w - Dret m w) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ (B *ᵥ tensVec Ω ξ))) ≤
          C' * t * #S * ‖B‖ * Real.exp (v * t - c' * (r : ℝ) ^ α) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, h11⟩ :=
    step_10_2_11 G V hV hVK μ hα hα1 (shellConst_nonneg C c) (half_pos hc)
  have hK₀ : 0 ≤ K₀ := by have := hVK 0; simp at this; linarith [(V 0).cast_nonneg (α := ℝ)]
  refine ⟨max (2 * μ * K₀ * √C) C₁, min (c / 2) c₁,
    lightCone (shellConst C c) (c / 2) α μ K₀ m₀, le_max_of_le_right hC₁,
    lt_min (half_pos hc) hc₁, lightCone_nonneg (shellConst_nonneg C c) _ _ _ _ _, ?_⟩
  intro Λ ι _ _ anc hanc hμ k hk hE t ht r _ S hS ret D Dret L
  have hEi : ∀ i l, 0 ≤ E G Λ (anc i) l (k i) ∧ E G Λ (anc i) l (k i) ≤ 1 :=
    fun i l => ⟨(hE i l).1, (hE i l).2.1⟩
  have htail : ∀ i (l : ℕ), ‖k i - E G Λ (anc i) l (k i)‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α) :=
    fun i l => (hE i l).2.2
  have hrα : 0 ≤ (r : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg r) α
  refine ⟨?_, fun m w => ⟨norm_wordProd_le (fun i => ?_) m w, ?_⟩, ?_⟩
  · -- D10.2.13 (A): same events, `‖G_i - G_{i,r}‖ ≤ 2√C e^{-(c/2) r^α}` (D4.10.3)
    obtain ⟨hs, hA⟩ := step_10_2_13 (fun i => CFC.sqrt (1 - k i))
      (fun i => CFC.sqrt (1 - E G Λ (anc i) r (k i)))
      (fun i => norm_sqrt_one_sub_le (hk i).1)
      (fun i => norm_sqrt_one_sub_le (hEi i r).1) ret
      (δ := 2 * √C * Real.exp (-(c / 2) * (r : ℝ) ^ α)) (by positivity)
      (fun i _ => norm_sqrt_sub_sqrt_E_le (hk i) (hEi i r) (htail i r)) ht
    refine ⟨hs, hA.trans ?_⟩
    -- retained labels: anchors in `N_r(S)`, at most `μ |S| V r`
    have hcard : (#{i | ret i} : ℝ) ≤ μ * #S * (K₀ * ((r : ℝ) + 1) ^ m₀) := by
      have := card_retained_le G V hV Λ S anc hμ r
      calc (#{i | ret i} : ℝ) ≤ ((μ * #S * V r : ℕ) : ℝ) := by exact_mod_cast this
        _ ≤ _ := by push_cast; exact mul_le_mul_of_nonneg_left (hVK r) (by positivity)
    have hexp : Real.exp (-(c / 2) * (r : ℝ) ^ α) ≤ Real.exp (-min (c / 2) c₁ * (r : ℝ) ^ α) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left (c / 2) c₁])
    calc t * #{i | ret i} * (2 * √C * Real.exp (-(c / 2) * (r : ℝ) ^ α)) ≤
          t * (μ * #S * (K₀ * ((r : ℝ) + 1) ^ m₀)) *
            (2 * √C * Real.exp (-(c / 2) * (r : ℝ) ^ α)) := by gcongr
      _ = (2 * μ * K₀ * √C) * t * #S * ((r : ℝ) + 1) ^ m₀ *
            Real.exp (-(c / 2) * (r : ℝ) ^ α) := by ring
      _ ≤ max (2 * μ * K₀ * √C) C₁ * t * #S * ((r : ℝ) + 1) ^ m₀ *
            Real.exp (-min (c / 2) c₁ * (r : ℝ) ^ α) := by
          gcongr
          exact le_max_left _ _
  · -- `G_{i,r}` is a positive contraction
    change ‖(if anc i ∈ graphNbhd G Λ S r then CFC.sqrt (1 - E G Λ (anc i) r (k i)) else 1)‖ ≤ 1
    split_ifs
    · exact norm_sqrt_one_sub_le (hEi i r).1
    · exact l2_opNorm_one_le
  · -- support: `G_{i,r}` on `N_r(a_i) ⊆ N_{2r}(S)`
    exact isSupportedOn_wordProd G anc ret (fun i h => h) _
      (fun i _ => isSupportedOn_sqrt_one_sub_E G (anc i) r (hk i).2) m w
  · -- D10.2.12 (B): D10.2.11 evaluated on `Ω ⊗ ξ` through D10.2.1
    intro Ω hkΩ κ _ _ B hB ξ hΩ hξ
    have h := h11 Λ S hS anc hanc hμ (Xt := Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ)
      (fun i => chan (k i)) (fun y => osc κ y) (fun i => chan_sub (k i))
      (fun i => norm_chan_le (hk i)) (fun y => osc_nonneg y) (fun y => osc_le y)
      (fun i => step_10_2_7 (hk i) (hEi i) (htail i) hc hα hα1)
      (fun i => step_10_2_10_shell (hk i) (hEi i) (htail i) hc hα hα1)
      r B (fun y hy => osc_eq_zero_of_support hB hy) t ht
    dsimp only at h
    have hv : vnorm (tensVec Ω ξ) = 1 :=
      vnorm_eq_one (by rw [dotProduct_tensVec, hΩ, hξ, one_mul])
    have hG : ∀ i (B' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
        chan (k i) B' *ᵥ tensVec Ω ξ =
          (CFC.sqrt (1 - k i) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ (B' *ᵥ tensVec Ω ξ) :=
      fun i B' => step_10_2_1 (hk i) (hkΩ i) B' ξ
    have hGr : ∀ i (B' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
        (if anc i ∈ graphNbhd G Λ S r then chan (k i) else id) B' *ᵥ tensVec Ω ξ =
          ((if anc i ∈ graphNbhd G Λ S r then CFC.sqrt (1 - k i) else 1) ⊗ₖ
            (1 : Matrix κ κ ℂ)) *ᵥ (B' *ᵥ tensVec Ω ξ) := by
      intro i B'
      split_ifs
      · exact hG i B'
      · rw [Matrix.one_kronecker_one, Matrix.one_mulVec]; rfl
    have hpt : ∀ m (w : Fin m → ι),
        vnorm (((D m w - Dret m w) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ (B *ᵥ tensVec Ω ξ)) ≤
          ‖wordMap (fun i => chan (k i)) m w B -
            wordMap (fun i => if anc i ∈ graphNbhd G Λ S r then chan (k i) else id) m w B‖ := by
      intro m w
      have e1 := wordMap_mulVec hG m w B
      have e2 := wordMap_mulVec hGr m w B
      rw [wordProd_kronecker_one] at e1 e2
      calc vnorm (((wordProd (fun i => CFC.sqrt (1 - k i)) m w -
              wordProd (fun i => if anc i ∈ graphNbhd G Λ S r then CFC.sqrt (1 - k i) else 1)
                m w) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ (B *ᵥ tensVec Ω ξ)) =
            vnorm ((wordMap (fun i => chan (k i)) m w B -
              wordMap (fun i => if anc i ∈ graphNbhd G Λ S r then chan (k i) else id) m w B) *ᵥ
                tensVec Ω ξ) := by
            rw [Matrix.sub_mulVec, e1, e2, ← sub_kronecker_one, Matrix.sub_mulVec]
        _ ≤ _ * vnorm (tensVec Ω ξ) := vnorm_mulVec_le _ _
        _ = _ := by rw [hv, mul_one]
    obtain ⟨hs, hle⟩ := clockExp_mono ht (fun m w => vnorm_nonneg _) hpt h.1
    refine ⟨hs, hle.trans (h.2.trans ?_)⟩
    have hexp : Real.exp (lightCone (shellConst C c) (c / 2) α μ K₀ m₀ * t -
          c₁ * (r : ℝ) ^ α) ≤
        Real.exp (lightCone (shellConst C c) (c / 2) α μ K₀ m₀ * t -
          min (c / 2) c₁ * (r : ℝ) ^ α) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right (c / 2) c₁])
    have hC : C₁ ≤ max (2 * μ * K₀ * √C) C₁ := le_max_right _ _
    have h0 : 0 ≤ t * #S * ‖B‖ := by positivity
    calc C₁ * t * #S * ‖B‖ *
          Real.exp (lightCone (shellConst C c) (c / 2) α μ K₀ m₀ * t - c₁ * (r : ℝ) ^ α) =
          C₁ * (t * #S * ‖B‖) *
            Real.exp (lightCone (shellConst C c) (c / 2) α μ K₀ m₀ * t - c₁ * (r : ℝ) ^ α) := by
          ring
      _ ≤ max (2 * μ * K₀ * √C) C₁ * (t * #S * ‖B‖) * Real.exp
            (lightCone (shellConst C c) (c / 2) α μ K₀ m₀ * t - min (c / 2) c₁ * (r : ℝ) ^ α) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hC h0) hexp (Real.exp_pos _).le
            (mul_nonneg (hC₁.trans hC) h0)
      _ = _ := by ring

end Lemma101


end AreaLaw
