import AreaLawRefactored.S09_Scanner.Scanner.Selection

/-!
# §9.2 Energy at the selected point (D9.13)

Digest `digest/09-scanner.md` D9.13, paper `paper/sections/08-scanner.tex` 492–532. Graph-level
(Map.md, Dimension: `any d`). Hölder's inequality (`8/7`, `8`) of D9.13.2 is used in its
pointwise form, Young's inequality `x^{1/8} ≤ (7/8) y + (1/8) y^{-7} x` (`y > 0`), integrated
against the split measure `ν` and evaluated at `y = δ^{1/8}`; this is the same bound.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Finset MeasureTheory Arealaw Entropy

namespace AreaLaw.Scanner

open Transport (Round EnergyTerms PYF MeanTree)
open Comparators (physReg dims)

universe u

/-- D9.13.2 (Hölder, pointwise): `x^{1/8} ≤ (7/8) y + (1/8) y^{-7} x` for `x ≥ 0`, `y > 0`. -/
theorem rpow_eighth_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ (1 / 8 : ℝ) ≤ 7 / 8 * y + 1 / 8 * y ^ (-7 : ℝ) * x := by
  have hy7 : 0 ≤ y ^ (-7 : ℝ) := Real.rpow_nonneg hy.le _
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 7 / 8) (w₂ := 1 / 8) (p₁ := y)
    (p₂ := y ^ (-7 : ℝ) * x) (by norm_num) (by norm_num) hy.le (mul_nonneg hy7 hx) (by norm_num)
  have e : y ^ (7 / 8 : ℝ) * (y ^ (-7 : ℝ) * x) ^ (1 / 8 : ℝ) = x ^ (1 / 8 : ℝ) := by
    rw [Real.mul_rpow hy7 hx, ← Real.rpow_mul hy.le, ← mul_assoc, ← Real.rpow_add hy]
    norm_num
  rw [e] at h
  linarith

section Round

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)] {K : ℕ}
  {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)] (R : Round V K H C)
  {t : ℝ} {k : ℕ} {pre : Transport.Config n k → ℂ} {p : unitInterval}

/-- `∫ m_s(u) ∫ (A + B f) dμ_{σ_{j,u}} du = A/2 + B ∫ m_s(u) ∫ f dμ_{σ_{j,u}} du`. -/
theorem integral_m_mul_integral_affine (hR : R.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : R.CrossBandCommute n t k) (hpreS : pre ∈ Replicas.S (fun v => Fin (n v)) k)
    (hpre : pre ≠ 0) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (j : Round.Leaf H C)
    {f : Replicas.Sphere (fun v => Fin (n v)) → ℝ} (hf : Continuous f) (A B : ℝ) :
    ∫ u, Transport.m (1 / 4) u * ∫ θ, (A + B * f θ)
        ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) =
      A / 2 + B * ∫ u, Transport.m (1 / 4) u *
        ∫ θ, f θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) := by
  have hint := integrable_m_mul_integral R hR ht hcomm hpreS hpre hp0 hp1 j hf
  have hm := Transport.integrable_m (s := 1 / 4) ⟨by norm_num, by norm_num⟩
  have e : ∀ u, Transport.m (1 / 4) u * ∫ θ, (A + B * f θ)
      ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u)) =
      A * Transport.m (1 / 4) u + B * (Transport.m (1 / 4) u *
        ∫ θ, f θ ∂(Replicas.μ (fun v => Fin (n v)) k (R.state n t k pre p j u))) := fun u => by
    have hσ := R.isSymDensity_state hR ht hcomm hpreS hpre hp0 hp1 j u
    have := Replicas.eq_replicas_husimi (fun v => Fin (n v)) k hσ.1 hσ.2.1 hσ.2.2
    rw [integral_add (integrable_const _) ((integrable_of_isSymDensity hσ hf).const_mul B),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    ring
  simp only [e]
  rw [integral_add (hm.const_mul A) (hint.const_mul B), integral_const_mul, integral_const_mul,
    Transport.integral_m_quarter]
  ring

end Round

/-! ## D9.13 -/

section Scan

variable {σ : Type u} [DecidableEq σ] (S : Scan σ) {nl : Comparators.Site S.Λ → ℕ}
  [∀ v, NeZero (nl v)] (E : EnergyTerms (Comparators.Site S.Λ) nl S.Term)

open Classical in
/-- D9.13.1–D9.13.3. The energy error of Proposition 7.4 (c) at a round `t` and `0 < p < 1`:
with the split weight `W_i(p) ≤ C D/m` (Lemma 9.1 (3)), `≤ C K n D` split terms per leaf
(Lemma 9.1 (2)), bad old histories of weight `≤ n^{-M}` (Lemma 9.1 (4)), new leaves of total
weight `p`, `η ≤ B`, and Hölder in the form `η^{1/8} ≤ (7/8) y + (1/8) y^{-7} η` on the good
old leaves (whose states are those of `𝒬`):
`∑_i W_i ∑_{j ∈ 𝒥_i} π_j ∫∫ η_{i,j}^{1/8} ≤ (C D/m)[(7/16) y CKnD + (1/8) y^{-7} 𝒬(p)
  + CKnD (B^{1/8}/2)(p + n^{-M})]`. -/
theorem energyError_le (hE : S.HasSupports E) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (h3 : S.Item3 C₂)
    (hcount : ∀ s, (#(univ.filter fun i : S.Term =>
      ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i))) : ℝ) ≤ C₂ * S.K * S.n * S.D)
    (t : Fin S.T) {Mt : ℝ}
    (htail : ∑ h ∈ univ.filter (fun h => ¬ S.Good t h), (S.histTree t).weight h ≤
      (S.n : ℝ) ^ (-Mt))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j θ, (S.round t).splitEta E i j θ ≤ B)
    {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hcomm : (S.round t).CrossBandCommute nl τ k)
    {pre : Transport.Config nl k → ℂ} (hpreS : pre ∈ Replicas.S (fun v => Fin (nl v)) k)
    (hpre : pre ≠ 0) {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {y : ℝ}
    (hy : 0 < y) :
    (S.round t).energyError nl E τ k pre p ≤ C₂ * S.D / S.m *
      (7 / 16 * y * (C₂ * S.K * S.n * S.D) + 1 / 8 * y ^ (-7 : ℝ) *
          step_9_10 (S.round t) E (S.Good t) τ k pre p +
        C₂ * S.K * S.n * S.D * (B ^ (1 / 8 : ℝ) / 2) * (p + (S.n : ℝ) ^ (-Mt))) := by
  set R := S.round t
  have hR := S.round_isAdmissible t
  set M := C₂ * S.K * S.n * S.D
  set B' := B ^ (1 / 8 : ℝ)
  have hB'0 : 0 ≤ B' := Real.rpow_nonneg hB0 _
  have hη0 := fun i j θ => splitEta_nonneg R E hR i j θ
  set I : S.Term → Round.Leaf (S.Hist t) (fun _ => S.Ch t) → ℝ := fun i j =>
    ∫ u, Transport.m (1 / 4) u * ∫ θ, R.splitEta E i j θ.1 ^ (1 / 8 : ℝ)
      ∂(Replicas.μ (fun v => Fin (nl v)) k (R.state nl τ k pre p j u))
  have hcont : ∀ i j, Continuous fun θ : Replicas.Sphere (fun v => Fin (nl v)) =>
      R.splitEta E i j θ.1 ^ (1 / 8 : ℝ) := fun i j =>
    (continuous_splitEta R E i j).rpow_const fun _ => Or.inr (by norm_num)
  have hI0 : ∀ i j, 0 ≤ I i j := fun i j =>
    integral_m_mul_integral_nonneg R j fun θ => Real.rpow_nonneg (hη0 i j θ.1) _
  have hIB : ∀ i j, I i j ≤ B' / 2 := fun i j =>
    integral_m_mul_integral_le R hR hτ hcomm hpreS hpre hp0 hp1 j (hcont i j) fun θ =>
      Real.rpow_le_rpow (hη0 i j θ.1) (hB i j θ.1) (by norm_num)
  -- the terms split at a leaf
  set sp : Round.Leaf (S.Hist t) (fun _ => S.Ch t) → Finset S.Term := fun j =>
    univ.filter fun i => j ∈ R.splitLeaves E i
  have hsp : ∀ j, (#(sp j) : ℝ) ≤ M := fun j => by
    refine le_trans ?_ (hcount ⟨t, j⟩)
    exact_mod_cast card_le_card fun i hi => by
      simp only [sp, Round.splitLeaves, mem_filter, mem_univ, true_and] at hi ⊢
      obtain ⟨g, hg⟩ := hi
      exact ⟨g, by rwa [← S.round_leafPart, ← hE i]⟩
  have hM0 : 0 ≤ M := le_trans (by positivity) (hsp ⟨Classical.arbitrary _, none⟩)
  -- D9.13.1: `W_i(p) ≤ C D/m`
  have h1 : R.energyError nl E τ k pre p ≤
      C₂ * S.D / S.m * ∑ j, (R.tree p).weight j * ∑ i ∈ sp j, I i j := by
    unfold Round.energyError
    refine (sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h3 t E hE i p)
      (sum_nonneg fun j _ => mul_nonneg ((R.tree p).weight_nonneg j) (hI0 i j))).trans
      (le_of_eq ?_)
    rw [← mul_sum]
    congr 1
    have hs : ∀ i, ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j * I i j =
        ∑ j, if j ∈ R.splitLeaves E i then (R.tree p).weight j * I i j else 0 := fun i => by
      rw [sum_ite_mem, univ_inter]
    simp only [hs]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum, sum_filter]
  -- D9.13.2: Hölder on the good old leaves
  have hgood : ∀ h, S.Good t h → ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ ≤
      7 / 16 * y * M + 1 / 8 * y ^ (-7 : ℝ) * ∫ u, Transport.m (1 / 4) u *
        ∫ θ, (∑ i ∈ splitAt R E h, R.splitEta E i ⟨h, none⟩ θ.1)
          ∂(Replicas.μ (fun v => Fin (nl v)) k (R.state nl τ k pre p ⟨h, none⟩ u)) := by
    intro h _
    have hspl : sp ⟨h, none⟩ = splitAt R E h := by
      ext i
      simp only [sp, splitAt, Round.splitLeaves, mem_filter, Finset.mem_univ, true_and]
      rfl
    have hY : ∀ i, I i ⟨h, none⟩ ≤ 7 / 8 * y / 2 + 1 / 8 * y ^ (-7 : ℝ) *
        ∫ u, Transport.m (1 / 4) u * ∫ θ, R.splitEta E i ⟨h, none⟩ θ.1
          ∂(Replicas.μ (fun v => Fin (nl v)) k (R.state nl τ k pre p ⟨h, none⟩ u)) := fun i => by
      rw [← integral_m_mul_integral_affine R hR hτ hcomm hpreS hpre hp0 hp1 _
        (continuous_splitEta R E i _)]
      exact integral_m_mul_integral_mono R hR hτ hcomm hpreS hpre hp0 hp1 _ (hcont i _)
        (continuous_const.add (continuous_const.mul (continuous_splitEta R E i _)))
        fun θ => rpow_eighth_le (hη0 i _ θ.1) hy
    refine (sum_le_sum fun i _ => hY i).trans ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
      ← integral_m_mul_integral_sum R hR hτ hcomm hpreS hpre hp0 hp1 _ _
        fun i => continuous_splitEta R E i _, hspl]
    have hc := hsp ⟨h, none⟩
    rw [hspl] at hc
    have : (#(splitAt R E h) : ℝ) * (7 / 8 * y / 2) ≤ M * (7 / 8 * y / 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  -- D9.13.3: all leaves; bad old histories and new leaves
  have hper : ∀ h, (R.tree p).weight ⟨h, none⟩ * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ +
      ∑ c, (R.tree p).weight ⟨h, some c⟩ * ∑ i ∈ sp ⟨h, some c⟩, I i ⟨h, some c⟩ ≤
      R.histTree.weight h * (7 / 16 * y * M) +
        (if S.Good t h then R.histTree.weight h * (1 / 8 * y ^ (-7 : ℝ) *
          ∫ u, Transport.m (1 / 4) u *
            ∫ θ, (∑ i ∈ splitAt R E h, R.splitEta E i ⟨h, none⟩ θ.1)
              ∂(Replicas.μ (fun v => Fin (nl v)) k (R.state nl τ k pre p ⟨h, none⟩ u)))
          else R.histTree.weight h * (M * (B' / 2))) +
        p * R.histTree.weight h * (M * (B' / 2)) := by
    intro h
    have hw := R.histTree.weight_nonneg h
    have hp1' : 0 ≤ 1 - (p : ℝ) := by linarith
    have hXB : ∀ j, ∑ i ∈ sp j, I i j ≤ M * (B' / 2) := fun j =>
      (sum_le_sum fun i _ => hIB i j).trans (by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hsp j) (by positivity))
    have hnew : ∑ c, (R.tree p).weight ⟨h, some c⟩ * ∑ i ∈ sp ⟨h, some c⟩, I i ⟨h, some c⟩ ≤
        p * R.histTree.weight h * (M * (B' / 2)) := by
      calc ∑ c, (R.tree p).weight ⟨h, some c⟩ * ∑ i ∈ sp ⟨h, some c⟩, I i ⟨h, some c⟩
          ≤ ∑ c, (p * R.histTree.weight h * (R.choiceTree h).weight c) * (M * (B' / 2)) :=
            sum_le_sum fun c _ => by
              rw [Round.weight_tree_new]
              exact mul_le_mul_of_nonneg_left (hXB _)
                (mul_nonneg (mul_nonneg p.2.1 hw) ((R.choiceTree h).weight_nonneg c))
        _ = p * R.histTree.weight h * (M * (B' / 2)) := by
            rw [← sum_mul, ← mul_sum, (R.choiceTree h).sum_weight, mul_one]
    rw [Round.weight_tree_old]
    have hX0 : 0 ≤ ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ := sum_nonneg fun i _ => hI0 i _
    split_ifs with hg
    · have h2 := hgood h hg
      have hG : 0 ≤ 1 / 8 * y ^ (-7 : ℝ) * ∫ u, Transport.m (1 / 4) u *
          ∫ θ, (∑ i ∈ splitAt R E h, R.splitEta E i ⟨h, none⟩ θ.1)
            ∂(Replicas.μ (fun v => Fin (nl v)) k (R.state nl τ k pre p ⟨h, none⟩ u)) :=
        mul_nonneg (by positivity) (integral_m_mul_integral_nonneg R _ fun θ =>
          sum_nonneg fun i _ => hη0 i _ θ.1)
      have : (1 - (p : ℝ)) * R.histTree.weight h * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ ≤
          R.histTree.weight h * (7 / 16 * y * M + 1 / 8 * y ^ (-7 : ℝ) *
            ∫ u, Transport.m (1 / 4) u *
              ∫ θ, (∑ i ∈ splitAt R E h, R.splitEta E i ⟨h, none⟩ θ.1)
                ∂(Replicas.μ (fun v => Fin (nl v)) k (R.state nl τ k pre p ⟨h, none⟩ u))) := by
        calc (1 - (p : ℝ)) * R.histTree.weight h * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩
            ≤ 1 * R.histTree.weight h * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ := by
              gcongr; linarith [p.2.1]
          _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left h2 hw
      nlinarith
    · have : (1 - (p : ℝ)) * R.histTree.weight h * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ ≤
          R.histTree.weight h * (M * (B' / 2)) := by
        calc (1 - (p : ℝ)) * R.histTree.weight h * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩
            ≤ 1 * R.histTree.weight h * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ := by
              gcongr; linarith [p.2.1]
          _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left (hXB _) hw
      have : 0 ≤ R.histTree.weight h * (7 / 16 * y * M) := by positivity
      linarith
  -- sum over the histories
  have h2 : ∑ j, (R.tree p).weight j * ∑ i ∈ sp j, I i j ≤
      7 / 16 * y * M + 1 / 8 * y ^ (-7 : ℝ) * step_9_10 R E (S.Good t) τ k pre p +
        M * (B' / 2) * (p + (S.n : ℝ) ^ (-Mt)) := by
    have hw := R.histTree.sum_weight
    have hMB : 0 ≤ M * (B' / 2) := by positivity
    have hbad : (∑ h ∈ univ.filter (fun h => ¬ S.Good t h), R.histTree.weight h) ≤
        (S.n : ℝ) ^ (-Mt) := by convert htail using 3; rfl
    have hite : ∑ h, (if S.Good t h then R.histTree.weight h * (1 / 8 * y ^ (-7 : ℝ) *
          ∫ u, Transport.m (1 / 4) u *
            ∫ θ, (∑ i ∈ splitAt R E h, R.splitEta E i ⟨h, none⟩ θ.1)
              ∂(Replicas.μ (fun v => Fin (nl v)) k (R.state nl τ k pre p ⟨h, none⟩ u)))
          else R.histTree.weight h * (M * (B' / 2))) =
        1 / 8 * y ^ (-7 : ℝ) * step_9_10 R E (S.Good t) τ k pre p +
          (∑ h ∈ univ.filter (fun h => ¬ S.Good t h), R.histTree.weight h) * (M * (B' / 2)) := by
      rw [sum_ite, step_9_10, mul_sum, sum_mul]
      congr 1
      exact sum_congr rfl fun h _ => by ring
    have e1 : ∑ h, R.histTree.weight h * (7 / 16 * y * M) = 7 / 16 * y * M := by
      rw [← sum_mul, hw, one_mul]
    have e3 : ∑ h, (p : ℝ) * R.histTree.weight h * (M * (B' / 2)) = p * (M * (B' / 2)) := by
      rw [← sum_mul, ← mul_sum, hw, mul_one]
    calc ∑ j, (R.tree p).weight j * ∑ i ∈ sp j, I i j
        = ∑ h, ((R.tree p).weight ⟨h, none⟩ * ∑ i ∈ sp ⟨h, none⟩, I i ⟨h, none⟩ +
          ∑ c, (R.tree p).weight ⟨h, some c⟩ * ∑ i ∈ sp ⟨h, some c⟩, I i ⟨h, some c⟩) := by
          rw [Fintype.sum_sigma]
          simp only [Fintype.sum_option]
      _ ≤ _ := sum_le_sum fun h _ => hper h
      _ = 7 / 16 * y * M + (1 / 8 * y ^ (-7 : ℝ) * step_9_10 R E (S.Good t) τ k pre p +
          (∑ h ∈ univ.filter (fun h => ¬ S.Good t h), R.histTree.weight h) * (M * (B' / 2))) +
          p * (M * (B' / 2)) := by
          rw [sum_add_distrib, sum_add_distrib, hite, e1, e3]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hbad hMB]
  calc R.energyError nl E τ k pre p ≤
        C₂ * S.D / S.m * ∑ j, (R.tree p).weight j * ∑ i ∈ sp j, I i j := h1
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (h2.trans (le_of_eq ?_)) (by positivity)
        ring

theorem rpow_eighth_pow {z : ℝ} (hz : 0 ≤ z) : (z ^ (1 / 8 : ℝ)) ^ 8 = z := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
  norm_num

open Classical in
/-- D9.13 (`scanner:energy-output`). At the selected point (`𝒬(p_k) ≤ KnD δ`, `δ ≤ Y⁸`,
`p_k ≤ ε`), Proposition 7.4 (c) `⟨v, H̄ v⟩ ≤ 2E₀ + C a² ℓ^C 𝓔 + r` with the energy error
`𝓔` of D9.13.1–D9.13.3 (Hölder at `y = Y`) gives
`⟨v, H̄ v⟩ ≤ 2E₀ + C a² ℓ^C (CD/m) KnD [Y (7C/16 + 1/8) + C (B^{1/8}/2)(ε + n^{-M})] + r`;
with `Y = δ^{1/8} + o_k(1)`, `B = C (log n)^C` and `a² (D/m) K n D = W² n D²/(mK) ≤ C W² n^ℓ D²`
(D9.13.4) this is the bound of Proposition 9.2. -/
theorem step_9_13 (hE : S.HasSupports E) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (h3 : S.Item3 C₂)
    (hcount : ∀ s, (#(univ.filter fun i : S.Term =>
      ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i))) : ℝ) ≤ C₂ * S.K * S.n * S.D)
    (t : Fin S.T) {Mt : ℝ}
    (htail : ∑ h ∈ univ.filter (fun h => ¬ S.Good t h), (S.histTree t).weight h ≤
      (S.n : ℝ) ^ (-Mt))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j θ, (S.round t).splitEta E i j θ ≤ B)
    {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hcomm : (S.round t).CrossBandCommute nl τ k)
    {pre : Transport.Config nl k → ℂ} (hpreS : pre ∈ Replicas.S (fun v => Fin (nl v)) k)
    (hpre : pre ≠ 0) {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {ε : ℝ}
    (hpε : (p : ℝ) ≤ ε) {δ Y : ℝ} (hY : 0 < Y) (hδY : δ ≤ Y ^ 8)
    (hQ : step_9_10 (S.round t) E (S.Good t) τ k pre p ≤ S.K * S.n * S.D * δ)
    {X E₀ Ce a ℓ r : ℝ} (hCe : 0 ≤ Ce)
    (hc : X ≤ 2 * E₀ + Ce * a ^ 2 * ℓ ^ 4 * (S.round t).energyError nl E τ k pre p + r) :
    X ≤ 2 * E₀ + Ce * a ^ 2 * ℓ ^ 4 * (C₂ * S.D / S.m) * (S.K * S.n * S.D) *
      (Y * (7 * C₂ / 16 + 1 / 8) + C₂ * (B ^ (1 / 8 : ℝ) / 2) * (ε + (S.n : ℝ) ^ (-Mt))) +
      r := by
  -- D9.13.1–D9.13.3 at `y = Y`
  have h := energyError_le S E hE hC₂ h3 hcount t htail hB0 hB hτ hcomm hpreS hpre hp0 hp1 hY
  -- D9.13.2: `(1/8) Y^{-7} 𝒬 ≤ (1/8) Y^{-7} KnD Y⁸ = KnD Y/8`
  have hY7 : 0 ≤ Y ^ (-7 : ℝ) := Real.rpow_nonneg hY.le _
  have hY8 : Y ^ (-7 : ℝ) * Y ^ 8 = Y := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hY]; norm_num
  have hKnD : (0 : ℝ) ≤ S.K * S.n * S.D := by positivity
  have hq : 1 / 8 * Y ^ (-7 : ℝ) * step_9_10 (S.round t) E (S.Good t) τ k pre p ≤
      1 / 8 * (S.K * S.n * S.D) * Y := by
    calc 1 / 8 * Y ^ (-7 : ℝ) * step_9_10 (S.round t) E (S.Good t) τ k pre p
        ≤ 1 / 8 * Y ^ (-7 : ℝ) * (S.K * S.n * S.D * Y ^ 8) := by
          gcongr; exact hQ.trans (mul_le_mul_of_nonneg_left hδY hKnD)
      _ = 1 / 8 * (S.K * S.n * S.D) * (Y ^ (-7 : ℝ) * Y ^ 8) := by ring
      _ = _ := by rw [hY8]
  have hB' : 0 ≤ B ^ (1 / 8 : ℝ) := Real.rpow_nonneg hB0 _
  have hn0 : 0 ≤ (S.n : ℝ) ^ (-Mt) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hEE : (S.round t).energyError nl E τ k pre p ≤ C₂ * S.D / S.m * (S.K * S.n * S.D) *
      (Y * (7 * C₂ / 16 + 1 / 8) + C₂ * (B ^ (1 / 8 : ℝ) / 2) * (ε + (S.n : ℝ) ^ (-Mt))) := by
    have hDm : 0 ≤ C₂ * S.D / S.m := by positivity
    have : C₂ * S.K * S.n * S.D * (B ^ (1 / 8 : ℝ) / 2) * (p + (S.n : ℝ) ^ (-Mt)) ≤
        C₂ * S.K * S.n * S.D * (B ^ (1 / 8 : ℝ) / 2) * (ε + (S.n : ℝ) ^ (-Mt)) := by
      gcongr
    calc _ ≤ _ := h
      _ ≤ C₂ * S.D / S.m * ((S.K * S.n * S.D) * (Y * (7 * C₂ / 16 + 1 / 8) +
          C₂ * (B ^ (1 / 8 : ℝ) / 2) * (ε + (S.n : ℝ) ^ (-Mt)))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hDm
      _ = _ := by ring
  have hCa : 0 ≤ Ce * a ^ 2 * ℓ ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left hEE hCa
  nlinarith

end Scan

/-! ## The selected point at fixed `n` (D9.12, D9.13) -/

section Asymptotics

open Filter Topology Asymptotics

theorem tendsto_log_add_div {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1 + c) / k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1 + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c (tendsto_atTop_add_const_right _ 1
      tendsto_natCast_atTop_atTop)
  have h2 := Real.isLittleO_log_id_atTop.comp_tendsto h1
  have h3 : (fun k : ℕ => (k : ℝ) + 1 + c) =O[atTop] fun k : ℕ => (k : ℝ) := by
    refine IsBigO.of_bound (2 + c) ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    nlinarith
  exact (h2.trans_isBigO h3).tendsto_div_nhds_zero

theorem tendsto_div_of_isBigO_log {β : ℕ → ℝ}
    (hβ : β =O[atTop] fun k : ℕ => Real.log ((k : ℝ) + 1)) :
    Tendsto (fun k : ℕ => β k / k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1 + 0) atTop atTop :=
    tendsto_atTop_add_const_right _ 0 (tendsto_atTop_add_const_right _ 1
      tendsto_natCast_atTop_atTop)
  have h2 := Real.isLittleO_log_id_atTop.comp_tendsto h1
  have h3 : (fun k : ℕ => (k : ℝ) + 1 + 0) =O[atTop] fun k : ℕ => (k : ℝ) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    linarith
  have h4 : (fun k : ℕ => Real.log ((k : ℝ) + 1)) =o[atTop] fun k : ℕ => (k : ℝ) := by
    have := h2.trans_isBigO h3
    simpa only [add_zero, Function.comp_def, id] using this
  exact (hβ.trans_isLittleO h4).tendsto_div_nhds_zero

end Asymptotics

section Point

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)] {K : ℕ}
  {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*} [∀ h, Fintype (C h)]
  [∀ h, DecidableEq (C h)] (R : Round V K H C) {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι)

theorem log_card_le_logDim (x : Finset V) :
    Real.log (Fintype.card (Reg (fun v => Fin (n v)) x)) ≤ Transport.logDim (n := n) x := by
  have h1 := one_le_card_reg (n := n) x
  rw [Transport.logDim, AreaLaw.ℓ, Real.log_mul (Real.exp_pos 1).ne' (by positivity),
    Real.log_exp]
  linarith

/-- D9.10. `η_{i,j} ≤ 2ℓ` for support-compatible terms whose split supports have `log(e dim) ≤ ℓ`:
at most one band splits a term. -/
theorem splitEta_le (hR : R.IsAdmissible) (hc : R.SupportCompatible E) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (i : ι) (hdim : ∀ j g, ¬ (R.leafPart j g).Contains (E.support i) →
      Transport.logDim (n := n) (E.support i) ≤ ℓ) (j : Round.Leaf H C)
    (θ : SiteConfig n → ℂ) : R.splitEta E i j θ ≤ 2 * ℓ := by
  classical
  unfold Round.splitEta
  set F := univ.filter fun g => ¬ (R.leafPart j g).Contains (E.support i)
  have hF : #F ≤ 1 := Finset.card_le_one.2 fun g hg g' hg' => by
    by_contra hne
    rcases hc j i g with h | ⟨-, h⟩
    · exact (mem_filter.1 hg).2 h
    · exact (mem_filter.1 hg').2 (h g' (Ne.symm hne))
  have hb : ∀ g ∈ F, Round.splitBandEta (R.leafPart j g) (E.support i) θ ≤ 2 * ℓ :=
    fun g hg => (splitBandEta_le (R.isPartition_leafPart hR j g) _ θ).trans (by
      have := log_card_le_logDim (n := n) (E.support i)
      linarith [hdim j g (mem_filter.1 hg).2])
  refine (sum_le_card_nsmul F _ (2 * ℓ) hb).trans ?_
  rw [nsmul_eq_mul]
  have : (#F : ℝ) ≤ 1 := by exact_mod_cast hF
  nlinarith

end Point

section Selected

open Filter Topology Asymptotics

variable {σ : Type u} [DecidableEq σ] (S : Scan σ) {nq : S.Λ → ℕ} [∀ v, NeZero (nq v)]
  (Dt : Comparators.PhysData nq) (E : Comparators.TypicalSet Dt S.X)
  (Et : EnergyTerms (Comparators.Site S.Λ) (dims nq E.d) S.Term)

open Classical in
/-- D9.12–D9.13 at fixed `n`: from Proposition 7.4 on every round (hypothesis `h74`), the leaf
floor (D6.9), `comparator:rough-upper` at the final tree and Lemma 9.1, for every `k ≥ 1` a
charge round and `p_k ∈ [ε/2, ε]` with
`E_def ≤ (Ẽ₀ + C a² ℓ⁴ (CD/m) KnD [δ^{1/8} (7C/16 + 1/8) + C ((2ℓ)^{1/8}/2)(ε + n^{-M})])/g̃
  + o_k(1)`,
`δ = (2 log d_* - log z + 2sW(2B_sh/z + 2B_exc) + 2nm C k a K a^{1/4} ℓ^C / k)/(nm (ε/2) a c K)`
(D9.12.3–D9.12.6). -/
theorem selected_point (hE : S.HasSupports Et)
    (hHbar : ∀ k, Comparators.Hbar Dt E.d k = Et.Hbar k)
    (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k)))
    (hl : ∀ k : ℕ, Comparators.pre Dt E.d k (l k) ∈ Replicas.S (fun f => Fin (dims nq E.d f)) k ∧
      Comparators.pre Dt E.d k (l k) ≠ 0 ∧
      (star (Comparators.pre Dt E.d k (l k)) ⬝ᵥ Comparators.pre Dt E.d k (l k)).re ≤ 1 ∧
      (0 < k → Comparators.Hbar Dt E.d k *ᵥ Comparators.pre Dt E.d k (l k) =
        (Dt.E₀ : ℂ) • Comparators.pre Dt E.d k (l k)))
    {c₁ C₂ Mt : ℝ} (hc₁ : 0 < c₁) (hC₂ : 0 ≤ C₂) (h3 : S.Item3 C₂) (h4 : S.Item4 c₁)
    (hcount : ∀ s, (#(univ.filter fun i : S.Term =>
      ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i))) : ℝ) ≤ C₂ * S.K * S.n * S.D)
    (htail : S.Tail Mt) (hn : 1 ≤ S.n) (hm : 1 ≤ S.m) (hK : 1 ≤ S.K) (hD : 1 ≤ S.D)
    {a ε ℓ : ℝ} (ha : 0 < a) (hε0 : 0 < ε) (hε1 : ε < 1) (hℓ : 1 ≤ ℓ)
    (hcomm : ∀ t k, (S.round t).CrossBandCommute (dims nq E.d) (a / 2) k)
    (hcomp : ∀ t, (S.round t).SupportCompatible Et)
    (hsplit : ∀ t i j g, ¬ ((S.round t).leafPart j g).Contains (Et.support i) →
      Transport.logDim (n := dims nq E.d) (Et.support i) ≤ ℓ)
    {Cg e₇ Ce₇ : ℝ} (hCe₇ : 0 ≤ Ce₇)
    (h74 : ∀ t : Fin S.T, ∃ β r : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧
      Tendsto r atTop (𝓝 0) ∧
      ∀ (k : ℕ) (pre : Transport.Config (dims nq E.d) k → ℂ),
        pre ∈ Replicas.S (fun v => Fin (dims nq E.d v)) k → pre ≠ 0 →
        (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 →
          (k : ℝ) * a * (S.round t).entropyGain (dims nq E.d) (a / 2) k pre p -
              Cg * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ e₇ - β k ≤
            (S.round t).exactDerivative (dims nq E.d) (a / 2) k pre p ∧
          ∀ E₀ : ℝ, Et.Hbar k *ᵥ pre = (E₀ : ℂ) • pre →
            (star ((S.round t).v (dims nq E.d) (a / 2) k pre p) ⬝ᵥ
                (Et.Hbar k *ᵥ (S.round t).v (dims nq E.d) (a / 2) k pre p)).re ≤
              2 * E₀ + Ce₇ * a ^ 2 * ℓ ^ 4 *
                (S.round t).energyError (dims nq E.d) Et (a / 2) k pre p + r k) ∧
        ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
          IntervalIntegrable (fun p => (S.round t).exactDerivative (dims nq E.d) (a / 2) k pre
              (Set.projIcc 0 1 zero_le_one p)) volume p₀ p₁ ∧
          Real.log ((S.round t).normSq (dims nq E.d) (a / 2) k pre p₀) -
              Real.log ((S.round t).normSq (dims nq E.d) (a / 2) k pre p₁) =
            ∫ p in p₀..p₁, (S.round t).exactDerivative (dims nq E.d) (a / 2) k pre
              (Set.projIcc 0 1 zero_le_one p))
    {Bsh Bexc : ℝ} (hU : Comparators.RoughUpper Dt S.Γ E a l Bsh Bexc) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
      ∃ t : Fin S.T, t.1 % 2 = 1 ∧ ∃ p : unitInterval, ε / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ ε ∧
        Comparators.Edef Dt S.Γ E (((S.round t).tree p).map (Sigma.mk t)) a k (l k) ≤
          (Dt.E₀ + Ce₇ * a ^ 2 * ℓ ^ 4 * (C₂ * S.D / S.m) * (S.K * S.n * S.D) *
            (max ((2 * Real.log E.d - Real.log E.z + 2 * (1 / 4) * (a * S.K) *
                (2 * Bsh / E.z + 2 * Bexc) + S.T * (Cg * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ e₇)) /
                (S.n * S.m * (ε / 2) * a * c₁ * S.K)) 0 ^ (1 / 8 : ℝ) * (7 * C₂ / 16 + 1 / 8) +
              C₂ * ((2 * ℓ) ^ (1 / 8 : ℝ) / 2) * (ε + (S.n : ℝ) ^ (-Mt)))) / Dt.g + r k := by
  -- Proposition 7.4 on every round
  choose β rc hβ hrc H using h74
  -- D9.12.2: the leaf floor (D6.9)
  obtain ⟨Cfl, hCfl, hfl⟩ := Replicas.eq_replicas_leaf_floor (n := dims nq E.d) (t := a / 2)
    (by positivity)
  -- D9.12.3: `comparator:rough-upper`
  obtain ⟨rU, hrU, hU'⟩ := hU
  have hn' : (1 : ℝ) ≤ S.n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ S.m := by exact_mod_cast hm
  have hK' : (1 : ℝ) ≤ S.K := by exact_mod_cast hK
  have hD' : (1 : ℝ) ≤ S.D := by exact_mod_cast hD
  have hT : 0 < S.T := by rw [Scan.T_eq]; exact Nat.mul_pos two_pos (Nat.mul_pos hn hm)
  have hg := Dt.gap_pos
  set den := (S.n : ℝ) * S.m * (ε / 2) * a * c₁ * S.K
  have hden : 0 < den := by positivity
  set XU := 2 * Real.log E.d - Real.log E.z + 2 * (1 / 4) * (a * S.K) *
    (2 * Bsh / E.z + 2 * Bexc)
  set δm := (XU + S.T * (Cg * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ e₇)) / den
  set ρ : ℕ → ℝ := fun k => ((S.K / 2 * Cfl * Real.log ((k : ℝ) + 2)) / k + rU k +
    (∑ t, β t k) / k) / den + 1 / k
  set ρ' : ℕ → ℝ := fun k => |ρ k| + 1 / k
  set A₁ := 7 * C₂ / 16 + 1 / 8
  set P₀ := Ce₇ * a ^ 2 * ℓ ^ 4 * (C₂ * S.D / S.m) * (S.K * S.n * S.D)
  have hP₀ : 0 ≤ P₀ := by positivity
  have hA₁ : 0 ≤ A₁ := by positivity
  refine ⟨fun k => (P₀ * A₁ * ρ' k ^ (1 / 8 : ℝ) + ∑ t, |rc t k|) / Dt.g, ?_, ?_⟩
  · -- the remainder is `o_k(1)` (D9.12.5: `O_fixed(log(k+2))/k = o_k(1)`)
    have h1 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2) / k) atTop (𝓝 0) := by
      have := tendsto_log_add_div (c := 1) zero_le_one
      refine this.congr fun k => ?_
      ring_nf
    have h2 : Tendsto (fun k : ℕ => (∑ t, β t k) / k) atTop (𝓝 0) := by
      have := tendsto_finsetSum (univ : Finset (Fin S.T)) fun t _ =>
        tendsto_div_of_isBigO_log (hβ t)
      simp only [sum_const_zero] at this
      refine this.congr fun k => ?_
      rw [sum_div]
    have h3 : Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hρ : Tendsto ρ atTop (𝓝 0) := by
      have := ((((h1.const_mul (S.K / 2 * Cfl)).add hrU).add h2).div_const den).add h3
      simp only [mul_zero, add_zero, zero_div] at this
      refine this.congr fun k => ?_
      simp only [ρ]
      ring
    have hρ' : Tendsto ρ' atTop (𝓝 0) := by
      have := hρ.abs.add h3
      simpa only [abs_zero, add_zero] using this
    have h8 := hρ'.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 8))
    rw [Real.zero_rpow (by norm_num)] at h8
    have hs : Tendsto (fun k => ∑ t, |rc t k|) atTop (𝓝 0) := by
      have := tendsto_finsetSum (univ : Finset (Fin S.T)) fun t _ => (hrc t).abs
      simpa only [abs_zero, sum_const_zero] using this
    have := ((h8.const_mul (P₀ * A₁)).add hs).div_const Dt.g
    simpa only [mul_zero, add_zero, zero_div] using this
  intro k hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hpS, hp0', hpn, hHE⟩ := hl k
  set pre := Comparators.pre Dt E.d k (l k)
  set Err : Fin S.T → ℝ := fun t => Cg * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ e₇ + β t k
  -- D9.12.2: the initial norm
  have hinit := log_normSq_le_of_floor (S.round ⟨0, hT⟩) (S.round_isAdmissible _)
    (t := a / 2) (by positivity) (hcomm _ k) hCfl
    (fun π hπ => (hfl k π.P π.Y π.F hπ.1 hπ.2.1 hπ.2.2.1 hπ.2.2.2).2.1) hp0' hpn 0
  -- D9.12.3: the final norm
  have hT1 : S.T - 1 < S.T := by omega
  have hfin0 := hU' k hk (((S.round ⟨S.T - 1, hT1⟩).tree 1).map (Sigma.mk _))
  rw [N2_map] at hfin0
  have hfin : -Real.log ((S.round ⟨S.T - 1, hT1⟩).normSq (dims nq E.d) (a / 2) k pre 1) ≤
      k * (XU + rU k) := by
    have hk0 : (0 : ℝ) < k := by linarith
    rw [div_le_iff₀ hk0] at hfin0
    have e : (((1 : unitInterval) : ℝ)) = 1 := rfl
    rw [e] at hfin0
    linarith
  -- D9.12: the selection
  obtain ⟨t, ht, p, hp1, hp2, hQ⟩ := step_9_12 S Et hE hc₁ h4 hn hm hK hD ha hε0 hε1 hk hpS hp0'
    (fun t => hcomm t k) Err (fun t p h0 h1 => by
      have := ((H t k pre hpS hp0').1 p h0 h1).1
      simp only [Err]
      linarith)
    (fun t => (H t k pre hpS hp0').2) hT hinit hfin
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1' : (p : ℝ) < 1 := by linarith
  -- the threshold is `δ + ρ_k`
  have hδ' : (S.K / 2 * Cfl * Real.log ((k : ℝ) + 2) + k * (XU + rU k) + ∑ t, Err t) /
      (S.n * S.m * (ε / 2) * k * a * c₁ * S.K) + 1 / k = δm + ρ k := by
    simp only [Err, δm, ρ, den, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hd0 : den ≠ 0 := hden.ne'
    simp only [den] at hd0
    field_simp
    ring
  rw [hδ'] at hQ
  set Y := max δm 0 ^ (1 / 8 : ℝ) + ρ' k ^ (1 / 8 : ℝ)
  have hρ'0 : 0 < ρ' k := by simp only [ρ']; positivity
  have hY : 0 < Y := add_pos_of_nonneg_of_pos (Real.rpow_nonneg (le_max_right _ _) _)
    (Real.rpow_pos_of_pos hρ'0 _)
  have hδY : δm + ρ k ≤ Y ^ 8 := by
    calc δm + ρ k ≤ max δm 0 + ρ' k := add_le_add (le_max_left _ _)
          ((le_abs_self _).trans (by simp only [ρ']; linarith [one_div_pos.2 (by linarith :
            (0 : ℝ) < k)]))
      _ = (max δm 0 ^ (1 / 8 : ℝ)) ^ 8 + (ρ' k ^ (1 / 8 : ℝ)) ^ 8 := by
          rw [rpow_eighth_pow (le_max_right _ _), rpow_eighth_pow hρ'0.le]
      _ ≤ Y ^ 8 := pow_add_pow_le (Real.rpow_nonneg (le_max_right _ _) _)
          (Real.rpow_nonneg hρ'0.le _) (by norm_num)
  -- D9.10: `η ≤ 2ℓ`
  have hB : ∀ i j θ, (S.round t).splitEta Et i j θ ≤ 2 * ℓ := fun i j θ =>
    splitEta_le (S.round t) Et (S.round_isAdmissible t) (hcomp t) (by linarith) i
      (fun j g hg => hsplit t i j g hg) j θ
  -- Proposition 7.4 (c) at the selected point
  have hc := ((H t k pre hpS hp0').1 p hp0 hp1').2 Dt.E₀ (by rw [← hHbar]; exact hHE hk)
  -- D9.13
  have h13 := step_9_13 S Et hE hC₂ h3 hcount t (htail t) (by linarith) hB (by positivity)
    (hcomm t k) hpS hp0' hp0 hp1' hp2 hY hδY hQ hCe₇ hc
  refine ⟨t, ht, p, hp1, hp2, ?_⟩
  rw [Edef_map S Dt E a k (l k) t p, hHbar k]
  have hrc : rc t k ≤ ∑ t, |rc t k| :=
    (le_abs_self _).trans (single_le_sum (fun t _ => abs_nonneg (rc t k)) (mem_univ t))
  beta_reduce
  rw [← add_div, div_le_div_iff_of_pos_right hg]
  have e : P₀ * (Y * A₁ + C₂ * ((2 * ℓ) ^ (1 / 8 : ℝ) / 2) * (ε + (S.n : ℝ) ^ (-Mt))) =
      P₀ * (max δm 0 ^ (1 / 8 : ℝ) * A₁ + C₂ * ((2 * ℓ) ^ (1 / 8 : ℝ) / 2) *
        (ε + (S.n : ℝ) ^ (-Mt))) + P₀ * A₁ * ρ' k ^ (1 / 8 : ℝ) := by
    simp only [Y]; ring
  simp only [P₀, A₁] at e ⊢
  linarith

end Selected

end AreaLaw.Scanner
