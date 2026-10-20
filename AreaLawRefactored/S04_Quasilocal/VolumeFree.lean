import AreaLawRefactored.S04_Quasilocal.Setup

/-!
# §4.3 D4.12 Volume-free summation of the truncation error

Digest `digest/04-quasilocal.md` (D4.12), paper `paper/sections/03-quasilocal.tex` 458–486.
Graph-level (`Map.md`, Dimension): ball growth `V` with `V r ≤ K (r+1)^m`.
-/

universe u v

namespace AreaLaw

open Finset GraphDomain Arealaw Real
open scoped Nat Matrix.Norms.L2Operator

/-- D4.12.6. `(u+1)^k e^{-b u^α} ≤ M` for `u ≥ 0`. -/
theorem step_4_12_6 {b α : ℝ} (hb : 0 < b) (hα : 0 < α) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 ≤ u → (u + 1) ^ k * exp (-(b * u ^ α)) ≤ M := by
  set m : ℕ := ⌈(k : ℝ) / α⌉₊
  have hm : (k : ℝ) ≤ α * m := by
    have := Nat.le_ceil ((k : ℝ) / α)
    rw [div_le_iff₀ hα] at this
    linarith
  refine ⟨2 ^ k * max 1 (m ! / b ^ m), by positivity, fun u hu => ?_⟩
  rcases le_total u 1 with h1 | h1
  · calc (u + 1) ^ k * exp (-(b * u ^ α)) ≤ 2 ^ k * 1 :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) k)
            (exp_le_one_iff.mpr (by have := rpow_nonneg hu α; nlinarith)) (exp_pos _).le
            (by positivity)
      _ ≤ 2 ^ k * max 1 (m ! / b ^ m) := by gcongr; exact le_max_left _ _
  · have hu0 : 0 < u := by linarith
    have hfac := pow_div_factorial_le_exp _ (by positivity : 0 ≤ b * u ^ α) m
    have hpow : (b * u ^ α) ^ m = b ^ m * u ^ (α * m) := by
      rw [mul_pow, ← rpow_natCast (u ^ α), ← rpow_mul hu]
    have huk : (u + 1) ^ k ≤ 2 ^ k * u ^ (α * m) :=
      calc (u + 1) ^ k ≤ (2 * u) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
        _ = 2 ^ k * u ^ (k : ℝ) := by rw [mul_pow, rpow_natCast]
        _ ≤ 2 ^ k * u ^ (α * m) := by gcongr
    have hupos : 0 < u ^ (α * m) := rpow_pos_of_pos hu0 _
    have hexp : exp (-(b * u ^ α)) ≤ m ! / (b ^ m * u ^ (α * m)) := by
      rw [exp_neg, le_div_iff₀ (by positivity), ← hpow, inv_mul_le_iff₀ (exp_pos _)]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < m !)] at hfac
      linarith
    calc (u + 1) ^ k * exp (-(b * u ^ α)) ≤
          2 ^ k * u ^ (α * m) * (m ! / (b ^ m * u ^ (α * m))) :=
          mul_le_mul huk hexp (exp_pos _).le (by positivity)
      _ = 2 ^ k * (m ! / b ^ m) := by field_simp
      _ ≤ 2 ^ k * max 1 (m ! / b ^ m) := by gcongr; exact le_max_right _ _

/-- D4.12.4–D4.12.5. `∑_{d<N} (d+1)^m e^{-c max{r₀,⌊d/2⌋}^α} ≤ A e^{-(c/2) r₀^α}`. -/
theorem step_4_12_5 {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r₀ N : ℕ,
      ∑ d ∈ range N, ((d : ℝ) + 1) ^ m * exp (-(c * (radius r₀ d : ℝ) ^ α)) ≤
        A * exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by
  obtain ⟨M, hM, hMb⟩ := step_4_12_6 (half_pos hc) hα (m + 2)
  have hsum : Summable fun d : ℕ => 1 / ((d : ℝ) + 1) ^ 2 := by
    simpa using (summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr one_lt_two)
  set S := ∑' d : ℕ, 1 / ((d : ℝ) + 1) ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun d : ℕ => by positivity
  refine ⟨2 ^ (m + 2) * M * S, by positivity, fun r₀ N => ?_⟩
  have hterm : ∀ d : ℕ, ((d : ℝ) + 1) ^ m * exp (-(c * (radius r₀ d : ℝ) ^ α)) ≤
      exp (-(c / 2 * (r₀ : ℝ) ^ α)) * (2 ^ (m + 2) * M * (1 / ((d : ℝ) + 1) ^ 2)) := by
    intro d
    set w : ℕ := d / 2
    have h1 : (r₀ : ℝ) ^ α ≤ (radius r₀ d : ℝ) ^ α :=
      rpow_le_rpow (by positivity) (by exact_mod_cast le_max_left _ _) hα.le
    have h2 : (w : ℝ) ^ α ≤ (radius r₀ d : ℝ) ^ α :=
      rpow_le_rpow (by positivity) (by exact_mod_cast le_max_right _ _) hα.le
    have hexp : exp (-(c * (radius r₀ d : ℝ) ^ α)) ≤
        exp (-(c / 2 * (r₀ : ℝ) ^ α)) * exp (-(c / 2 * (w : ℝ) ^ α)) := by
      rw [← exp_add]; exact exp_le_exp.mpr (by nlinarith)
    have hdu : (d : ℝ) + 1 ≤ 2 * ((w : ℝ) + 1) := by
      have : (d : ℝ) ≤ 2 * w + 1 := by exact_mod_cast (show d ≤ 2 * w + 1 by omega)
      linarith
    have hpoly : ((d : ℝ) + 1) ^ (m + 2) * exp (-(c / 2 * (w : ℝ) ^ α)) ≤ 2 ^ (m + 2) * M :=
      calc _ ≤ (2 * ((w : ℝ) + 1)) ^ (m + 2) * exp (-(c / 2 * (w : ℝ) ^ α)) := by gcongr
        _ = 2 ^ (m + 2) * (((w : ℝ) + 1) ^ (m + 2) * exp (-(c / 2 * (w : ℝ) ^ α))) := by
          rw [mul_pow]; ring
        _ ≤ 2 ^ (m + 2) * M := by gcongr; exact hMb _ (by positivity)
    calc ((d : ℝ) + 1) ^ m * exp (-(c * (radius r₀ d : ℝ) ^ α)) ≤
          ((d : ℝ) + 1) ^ m * (exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
            exp (-(c / 2 * (w : ℝ) ^ α))) := by gcongr
      _ = exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          (((d : ℝ) + 1) ^ (m + 2) * exp (-(c / 2 * (w : ℝ) ^ α)) / ((d : ℝ) + 1) ^ 2) := by
          field_simp; ring
      _ ≤ exp (-(c / 2 * (r₀ : ℝ) ^ α)) * (2 ^ (m + 2) * M / ((d : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ d ∈ range N, exp (-(c / 2 * (r₀ : ℝ) ^ α)) *
          (2 ^ (m + 2) * M * (1 / ((d : ℝ) + 1) ^ 2)) := sum_le_sum fun d _ => hterm d
    _ = exp (-(c / 2 * (r₀ : ℝ) ^ α)) * (2 ^ (m + 2) * M) *
        ∑ d ∈ range N, 1 / ((d : ℝ) + 1) ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
    _ ≤ exp (-(c / 2 * (r₀ : ℝ) ^ α)) * (2 ^ (m + 2) * M) * S := by
      gcongr; exact hsum.sum_le_tsum _ fun d _ => by positivity
    _ = _ := by ring

/-- D4.12. For any fixed `α > 0` for which `eq:quasilocal-positive-tail` holds, any integer
`r₀`, and `r_i` as in D4.11:
`‖H̃ - H_F‖ ≤ C |S₀| ∑_{d≥0} V(d) exp(-c max{r₀,⌊d/2⌋}^α) ≤ C' |S₀| e^{-c' r₀^α}`,
no factor `|Λ|`; `C', c'` depend only on `C, c, α, K, m, μ_R` (`V(r) ≤ K (r+1)^m`). -/
theorem step_4_12 {C c α K : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hK : 0 ≤ K)
    (m μ₀ : ℕ) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧
      ∀ {σ : Type u} [DecidableEq σ] (G : SimpleGraph σ) (V : ℕ → ℕ),
        (∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) →
        (∀ r : ℕ, (V r : ℝ) ≤ K * ((r : ℝ) + 1) ^ m) →
        ∀ R : ℕ, μ V R ≤ μ₀ →
        ∀ {loc : σ → Type v} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
          (Λ : Finset σ) (a : Finset σ → σ), (∀ X ∈ supports G Λ R, a X ∈ X) →
        ∀ k : Finset σ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ,
          (∀ X ∈ supports G Λ R, ∀ l : ℕ,
            ‖k X - E G Λ (a X) l (k X)‖ ≤ C * exp (-(c * (l : ℝ) ^ α))) →
        ∀ (r₀ : ℕ) (S₀ : Finset σ),
          ‖∑ X ∈ supports G Λ R, truncated G Λ S₀ r₀ (a X) (k X) -
              ∑ X ∈ supports G Λ R, k X‖ ≤ C' * #S₀ * exp (-(c' * (r₀ : ℝ) ^ α)) := by
  obtain ⟨A, hA0, hA⟩ := step_4_12_5 hc hα m
  refine ⟨C * μ₀ * K * A + 1, c / 2, by positivity, by positivity, ?_⟩
  intro σ _ G V hV hVpoly R hμ loc _ _ Λ a ha k htail r₀ S₀
  classical
  set D : Finset σ → ℕ := fun X => (setDist G Λ S₀ (a X)).toNat
  set F := (supports G Λ R).filter fun X => setDist G Λ S₀ (a X) ≠ ⊤
  set f : ℕ → ℝ := fun d => C * exp (-(c * (radius r₀ d : ℝ) ^ α))
  -- D4.12.1
  have hterm : ∀ X ∈ supports G Λ R, ‖truncated G Λ S₀ r₀ (a X) (k X) - k X‖ ≤
      if setDist G Λ S₀ (a X) ≠ ⊤ then f (D X) else 0 := by
    intro X hX
    by_cases hi : setDist G Λ S₀ (a X) = ⊤
    · simp [truncated, hi]
    · rw [truncated, if_neg hi, if_pos hi, norm_sub_rev]; exact htail X hX _
  -- D4.12.2
  have hcount : ∀ d : ℕ,
      (#(F.filter fun X => D X = d) : ℝ) ≤ μ₀ * (#S₀ * (K * ((d : ℝ) + 1) ^ m)) := by
    intro d
    have hsub : F.filter (fun X => D X = d) ⊆ (S₀.biUnion fun y => ball G Λ y d).biUnion
        fun x => (supports G Λ R).filter fun X => a X = x := by
      intro X hX
      simp only [F, mem_filter] at hX
      obtain ⟨⟨hX, hfin⟩, hD⟩ := hX
      have hne : S₀.Nonempty := nonempty_iff_ne_empty.2 fun h => hfin (by simp [setDist, h])
      obtain ⟨y, hy, he⟩ := exists_mem_eq_inf S₀ hne fun y => domainEDist G Λ (a X) y
      refine mem_biUnion.2 ⟨a X, mem_biUnion.2 ⟨y, hy, (GraphDomain.mem_ball G).2
        ⟨((GraphDomain.mem_supports G).1 hX).1 (ha X hX), ?_⟩⟩, mem_filter.2 ⟨hX, rfl⟩⟩
      rw [← he, ← hD]; exact (ENat.natCast_toNat hfin).ge
    have hN : #(F.filter fun X => D X = d) ≤ μ₀ * (#S₀ * V d) :=
      calc _ ≤ _ := card_le_card hsub
        _ ≤ ∑ x ∈ S₀.biUnion fun y => ball G Λ y d,
            #((supports G Λ R).filter fun X => a X = x) := card_biUnion_le
        _ ≤ ∑ _x ∈ S₀.biUnion fun y => ball G Λ y d, μ₀ :=
          sum_le_sum fun x _ => ((step_2_8 G V hV Λ R x).2.1 a ha).trans hμ
        _ ≤ (∑ y ∈ S₀, #(ball G Λ y d)) * μ₀ := by
          rw [sum_const, smul_eq_mul]; gcongr; exact card_biUnion_le
        _ ≤ (∑ _y ∈ S₀, V d) * μ₀ := by gcongr with y; exact hV Λ y d
        _ = μ₀ * (#S₀ * V d) := by rw [sum_const, smul_eq_mul, mul_comm]
    calc (#(F.filter fun X => D X = d) : ℝ) ≤ μ₀ * (#S₀ * V d) := by exact_mod_cast hN
      _ ≤ _ := by gcongr; exact hVpoly d
  -- D4.12.3
  calc _ = ‖∑ X ∈ supports G Λ R, (truncated G Λ S₀ r₀ (a X) (k X) - k X)‖ := by
        rw [sum_sub_distrib]
    _ ≤ ∑ X ∈ supports G Λ R, ‖truncated G Λ S₀ r₀ (a X) (k X) - k X‖ := norm_sum_le _ _
    _ ≤ ∑ X ∈ supports G Λ R, if setDist G Λ S₀ (a X) ≠ ⊤ then f (D X) else 0 :=
      sum_le_sum hterm
    _ = ∑ X ∈ F, f (D X) := by rw [sum_filter]
    _ = ∑ d ∈ F.image D, (#(F.filter fun X => D X = d) : ℝ) * f d := by
      rw [sum_comp]; simp [nsmul_eq_mul]
    _ ≤ ∑ d ∈ range ((F.image D).sup id + 1),
          (μ₀ * (#S₀ * (K * ((d : ℝ) + 1) ^ m))) * f d := by
      refine (sum_le_sum fun d _ => ?_).trans (sum_le_sum_of_subset_of_nonneg
        (fun d hd => ?_) fun d _ _ => ?_)
      · exact mul_le_mul_of_nonneg_right (hcount d) (by positivity)
      · exact mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hd))
      · positivity
    _ = C * μ₀ * K * #S₀ * ∑ d ∈ range ((F.image D).sup id + 1),
          ((d : ℝ) + 1) ^ m * exp (-(c * (radius r₀ d : ℝ) ^ α)) := by
      rw [mul_sum]; exact sum_congr rfl fun d _ => by simp only [f]; ring
    -- D4.12.4–D4.12.6
    _ ≤ C * μ₀ * K * #S₀ * (A * exp (-(c / 2 * (r₀ : ℝ) ^ α))) := by gcongr; exact hA r₀ _
    _ ≤ (C * μ₀ * K * A + 1) * #S₀ * exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by
      have : 0 ≤ (#S₀ : ℝ) * exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by positivity
      nlinarith

/-- D4.12.7. With `α = 1/2`, `|S₀| ≤ C₀ n^s` and `r₀ = ⌈C₁ (log n)²⌉`: for `C₁` large,
depending only on `C', c', C₀, g, s`, `C' C₀ n^s e^{-c' r₀^{1/2}} ≤ ε_n := min {n^{-1000}, g/4}`
for every real `n ≥ 2` (`eq:quasilocal-truncation-error`). -/
theorem step_4_12_7 {C' c' C₀ g s : ℝ} (hC' : 0 ≤ C') (hc' : 0 < c') (hC₀ : 0 ≤ C₀)
    (hg : 0 < g) (hs : 0 ≤ s) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℝ, 2 ≤ n →
      C' * C₀ * n ^ s * exp (-(c' * ((⌈C₁ * log n ^ 2⌉₊ : ℕ) : ℝ) ^ (1 / 2 : ℝ))) ≤
        min (n ^ (-1000 : ℝ)) (g / 4) := by
  set ε := min 1 (g / 4)
  have hε : 0 < ε := lt_min one_pos (by positivity)
  set L := 2 * (C' * C₀) / ε
  have hL : 0 ≤ L := by positivity
  set β := 1000 + s + L
  have hβ : 0 < β := by positivity
  refine ⟨(β / c') ^ 2, by positivity, fun n hn => ?_⟩
  have hn0 : 0 < n := by linarith
  have hlog : 0 < log n := log_pos (by linarith)
  set r₀ : ℕ := ⌈(β / c') ^ 2 * log n ^ 2⌉₊
  -- D4.12.7: `r₀^{1/2} ≥ √C₁ log n`, so `e^{-c' r₀^{1/2}} ≤ n^{-c'√C₁}`
  have hr : β / c' * log n ≤ (r₀ : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← sqrt_eq_rpow]
    exact le_sqrt_of_sq_le ((by ring : (β / c' * log n) ^ 2 = _).le.trans (Nat.le_ceil _))
  have hexp : exp (-(c' * (r₀ : ℝ) ^ (1 / 2 : ℝ))) ≤ n ^ (-β) := by
    rw [rpow_def_of_pos hn0]
    refine exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hr hc'.le
    have heq : c' * (β / c' * log n) = β * log n := by field_simp
    nlinarith
  have hbound : C' * C₀ * n ^ s * exp (-(c' * (r₀ : ℝ) ^ (1 / 2 : ℝ))) ≤
      C' * C₀ * n ^ (-L) * n ^ (-1000 : ℝ) :=
    calc _ ≤ C' * C₀ * n ^ s * n ^ (-β) := by gcongr
      _ = C' * C₀ * n ^ (-L) * n ^ (-1000 : ℝ) := by
        rw [mul_assoc _ (n ^ s), ← rpow_add hn0, mul_assoc _ (n ^ (-L)), ← rpow_add hn0]
        congr 2; simp only [β]; ring
  -- `C' C₀ 2^{-L} ≤ ε`, and the bound decreases in `n`
  have h2L : C' * C₀ * (2 : ℝ) ^ (-L) ≤ ε := by
    have hhalf : L / 2 ≤ (2 : ℝ) ^ L := by
      rw [rpow_def_of_pos two_pos]
      have := add_one_le_exp (log 2 * L)
      have : (1 / 2 : ℝ) < log 2 := by have := log_two_gt_d9; linarith
      nlinarith
    have h1 : C' * C₀ = ε * (L / 2) := by simp only [L]; field_simp
    rw [rpow_neg two_pos.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  have hLn : C' * C₀ * n ^ (-L) ≤ ε :=
    (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos two_pos hn (by linarith))
      (by positivity)).trans h2L
  have hn1000 : n ^ (-1000 : ℝ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hpos : 0 ≤ n ^ (-1000 : ℝ) := rpow_nonneg hn0.le _
  refine le_min (hbound.trans ?_) (hbound.trans ?_)
  · nlinarith [hLn.trans (min_le_left _ _)]
  · nlinarith [hLn.trans (min_le_right _ _)]

end AreaLaw
