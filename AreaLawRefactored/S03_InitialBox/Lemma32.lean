import AreaLawRefactored.S03_InitialBox.TrialNorm

/-!
# §3.2 Lemma 3.2 (D3.4, assembled per D3.14)

Digest `digest/03-initial-box.md` (D3.4, D3.14), paper `paper/sections/02-initial.tex`,
lines 219–586. D3.14.1 (`step_3_14_1`) is over any site type; `lemma_3_2` assembles D3.5,
D3.6, D3.10, D3.11, D3.12.1 (`step_3_12_1`), D3.13 (`eq_initial_norm_upper`) and D3.14 on
`ℤ × ℤ`.
-/

namespace AreaLaw

open Arealaw OpenAI Finset Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker

/-! ## Bookkeeping -/

/-- Shifting the index: `∑_{j<m} g(j+1) = ∑_{j=1}^m g(j)`. -/
theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m : ℕ) :
    ∑ j ∈ range m, g (j + 1) = ∑ j ∈ Icc 1 m, g j := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- A filtered sum over the subtype of a finset is the filtered sum over the finset. -/
theorem sum_filter_coe_sort {α M : Type*} [AddCommMonoid M] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (f : α → M) :
    ∑ i ∈ univ.filter (fun i : s ↦ p i.1), f i.1 = ∑ x ∈ s with p x, f x := by
  rw [sum_filter, sum_filter]
  exact sum_coe_sort s fun x ↦ if p x then f x else 0

/-- A filtered count over the subtype of a finset is the filtered count over the finset. -/
theorem card_filter_coe_sort {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    #(univ.filter (fun i : s ↦ p i.1)) = #(s.filter p) := by
  simp only [card_eq_sum_ones]
  exact sum_filter_coe_sort s p fun _ ↦ 1

/-- For an admissible interaction, `H = ∑_{X ∈ supports} h_X ⊗ 1`. -/
theorem hamiltonian_eq_sum_supports {q R : ℕ} {J : ℝ} {Λ : Finset (ℤ × ℤ)}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ}
    (hΦ : IsAdmissible Λ R J Φ) :
    hamiltonian Λ Φ = ∑ X : supports Λ R, extendId (mem_supports.1 X.2).1 (Φ X.1) := by
  set g : Finset (ℤ × ℤ) → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun X ↦ if h : X ⊆ Λ then extendId h (Φ X) else 0
  have h1 : hamiltonian Λ Φ = ∑ X ∈ Λ.powerset, g X := by
    rw [hamiltonian, ← sum_attach Λ.powerset g]
    exact sum_congr rfl fun X _ ↦ by simp only [g, dif_pos (mem_powerset.1 X.2)]
  rw [h1, ← sum_subset (filter_subset _ _ : supports Λ R ⊆ Λ.powerset) fun X hX hXs ↦ ?_,
    ← sum_coe_sort]
  · exact sum_congr rfl fun X _ ↦ dif_pos _
  · rw [mem_powerset] at hX
    simp only [g, dif_pos hX, (hΦ X hX).2.2 hXs, extendId_zero]

/-! ## D3.14.1 The lower and upper bounds on the optimized norm, combined -/

section D3141

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-- D3.14.1 (over any site type). Filters on the regions `X ∪ T_j ⊆ U` (`T_j` increasing),
weights `0 < a_j` (`a_j ≤ ½` for `j < m`), and the hypotheses of D3.11 (`step_3_11`). If the
zero-floor limit holds (`h1`, D3.12.1: a bound on every positive-floor feasible product bounds
every zero-floor one) and the trial-norm bound holds (`h2`, eq:initial-norm-upper:
a bound `B > 0` on every zero-floor product gives `-2 log B ≤ S(X) + ∑_j a_j S(T_j)`), then the
lower bound of D3.11 is at most the upper one:
`∑_j (a_j S(X ∪ T_j) - 1024 e ϑ 𝓑_j a_j²) - 2 m v ≤ S(X) + ∑_j a_j S(T_j)`. -/
theorem step_3_14_1 {U X : Finset σ} (hXU : X ⊆ U) (T : ℕ → Finset σ) (hTU : ∀ j, T j ⊆ U)
    (hT : ∀ j, T j ⊆ T (j + 1)) {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (m : ℕ)
    (ha2 : ∀ j < m, a j ≤ 1 / 2) (hne : ∀ j, Nonempty (Arealaw.Reg loc (X ∪ T j)))
    (Ω : Arealaw.Reg loc U → ℂ) (hΩ1 : star Ω ⬝ᵥ Ω = 1)
    {ι : Type*} (TT : Finset ι) {D : ι → Finset σ} (hD : ∀ t, D t ⊆ U)
    {Y : (t : ι) → Matrix (Arealaw.Reg loc (D t)) (Arealaw.Reg loc (D t)) ℂ}
    (hY : ∀ t, (Y t).IsHermitian) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hYc : ∀ t ∈ TT, (Fintype.card (Arealaw.Reg loc (D t)) : ℝ) ^ 2 * ‖Y t‖ ≤ c₀) {E₀ : ℝ}
    (hΩ : (∑ t ∈ TT, Arealaw.extendId (hD t) (Y t)) *ᵥ Ω = (E₀ : ℂ) • Ω) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : OpenAI.HasGlobalGap (∑ t ∈ TT, Arealaw.extendId (hD t) (Y t)) Ω E₀ Δ)
    (hd : ∀ t ∈ TT, ∀ j < m, (D t ∩ (X ∪ T j)).Nonempty → (D t \ (X ∪ T j)).Nonempty →
      D t ⊆ X ∪ T (j + 1) ∧ ∀ i < j, Disjoint (X ∪ T i) (D t))
    {C' : ℝ} (hC' : 0 ≤ C') {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hcount : ∀ j < m, ((TT.filter fun t ↦ (D t ∩ (X ∪ T j)).Nonempty ∧
      (D t \ (X ∪ T j)).Nonempty).card : ℝ) ≤ C' * w j)
    (hv : 16 / Real.exp 2 * c₀ * C' * (∑ j ∈ range m, w j * a j ^ 2) / Δ ≤ 1 / 4)
    {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {𝓑 : ℕ → ℝ} (h𝓑 : ∀ j, 0 ≤ 𝓑 j)
    (hM : ∀ j < m,
      let ρ := (OpenAI.pureState Ω hΩ1).toSubState.restrict (union_subset hXU (hTU j))
      let p := ρ.psd.isHermitian.eigenvalues
      Real.log (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < p i),
          p i * Real.exp (-(-a j / (1 - a j)) * Real.log (p i))) ≤
        -a j / (1 - a j) * ρ.entropy + 512 * Real.exp 1 * ϑ * 𝓑 j * (-a j / (1 - a j)) ^ 2)
    (h1 : ∀ {B : ℝ}, (∀ f : ℕ → ℝ, (∀ j, 0 < f j) →
      (∀ j, (Fintype.card (Arealaw.Reg loc (X ∪ T j)) : ℝ) * f j < 1) →
      ∀ L : (j : ℕ) → Matrix (Arealaw.Reg loc (X ∪ T j)) (Arealaw.Reg loc (X ∪ T j)) ℂ,
        (∀ j, IsFilter (f j) (a j) (L j)) →
        ‖toEuclideanLin (filterProd (fun j ↦ union_subset hXU (hTU j)) L m)
          (WithLp.toLp 2 Ω)‖ ≤ B) →
      ∀ L : (j : ℕ) → Matrix (Arealaw.Reg loc (X ∪ T j)) (Arealaw.Reg loc (X ∪ T j)) ℂ,
        (∀ j, IsFilter 0 (a j) (L j)) →
        ‖toEuclideanLin (filterProd (fun j ↦ union_subset hXU (hTU j)) L m)
          (WithLp.toLp 2 Ω)‖ ≤ B)
    (h2 : ∀ {B : ℝ}, 0 < B →
      (∀ L : (j : ℕ) → Matrix (Arealaw.Reg loc (X ∪ T j)) (Arealaw.Reg loc (X ∪ T j)) ℂ,
        (∀ j, IsFilter 0 (a j) (L j)) →
        ‖toEuclideanLin (filterProd (fun j ↦ union_subset hXU (hTU j)) L m)
          (WithLp.toLp 2 Ω)‖ ≤ B) →
      -2 * Real.log B ≤ (OpenAI.pureState Ω hΩ1).regionEntropy hXU +
        ∑ j ∈ range m, a j * (OpenAI.pureState Ω hΩ1).regionEntropy (hTU j)) :
    ∑ j ∈ range m, (a j * (OpenAI.pureState Ω hΩ1).regionEntropy (union_subset hXU (hTU j)) -
        1024 * Real.exp 1 * ϑ * 𝓑 j * a j ^ 2) -
      2 * m * (16 / Real.exp 2 * c₀ * C' * (∑ j ∈ range m, w j * a j ^ 2) / Δ) ≤
    (OpenAI.pureState Ω hΩ1).regionEntropy hXU +
      ∑ j ∈ range m, a j * (OpenAI.pureState Ω hΩ1).regionEntropy (hTU j) := by
  have hX : ∀ j, X ∪ T j ⊆ U := fun j ↦ union_subset hXU (hTU j)
  set LB := ∑ j ∈ range m, (a j * (OpenAI.pureState Ω hΩ1).regionEntropy (hX j) -
      1024 * Real.exp 1 * ϑ * 𝓑 j * a j ^ 2) -
    2 * m * (16 / Real.exp 2 * c₀ * C' * (∑ j ∈ range m, w j * a j ^ 2) / Δ)
  have hΩ0 : (WithLp.toLp 2 Ω : EuclideanSpace ℂ (Arealaw.Reg loc U)) ≠ 0 := by
    intro h0
    have : Ω = 0 := congrArg WithLp.ofLp h0
    rw [this] at hΩ1
    simp at hΩ1
  -- D3.11 for every positive floor: the optimized norm is at least `exp (LB/2)`, so every
  -- feasible product with that floor has norm at most `exp (-LB/2)`
  have hfloor : ∀ f : ℕ → ℝ, (∀ j, 0 < f j) →
      (∀ j, (Fintype.card (Arealaw.Reg loc (X ∪ T j)) : ℝ) * f j < 1) →
      ∀ L : (j : ℕ) → Matrix (Arealaw.Reg loc (X ∪ T j)) (Arealaw.Reg loc (X ∪ T j)) ℂ,
        (∀ j, IsFilter (f j) (a j) (L j)) →
        ‖toEuclideanLin (filterProd hX L m) (WithLp.toLp 2 Ω)‖ ≤ Real.exp (-LB / 2) := by
    intro f hf hcard L hL
    obtain ⟨L₀, hL₀, hmax, hpos⟩ := step_3_7_1 (X := fun j ↦ X ∪ T j) hX m hf
      (fun j ↦ (ha j).le) hne (fun j ↦ (hcard j).le) hΩ0
    have h : LB ≤ -2 * Real.log ‖toEuclideanLin (filterProd hX L₀ m) (WithLp.toLp 2 Ω)‖ :=
      step_3_11 (X := fun j ↦ X ∪ T j) hX (fun j ↦ union_subset_union_right (hT j)) hf
        (fun j ↦ (ha j).le) m (fun j hj ↦ ⟨ha j, ha2 j hj⟩) hne hcard Ω hΩ1 hL₀ hmax TT hD hY
        hc₀ hYc hΩ hΔ hgap hd hC' hw hcount hv hϑ h𝓑 hM
    refine (hmax L hL).trans ?_
    rw [← Real.log_le_iff_le_exp hpos]
    linarith
  -- D3.12.1: the bound passes to zero floors; eq:initial-norm-upper at `B = exp (-LB/2)`
  have := h2 (Real.exp_pos _) (h1 hfloor)
  rw [Real.log_exp] at this
  linarith

end D3141

section D314

/-! ## D3.4 Lemma 3.2 -/

/-- D3.4 (Lemma 3.2, lem:initial-buffer). There are an integer `C_pad ≥ 1` and a constant
`C_buf`, depending only on `q, R, J, Δ`, such that for every `D₀ > 2R + 10`, every admissible
Hamiltonian with gapped ground vector `Ω`, every cut `A`, every safe rectangle `Q`, every
`r ≥ 1` and every rectangle `Q₀` of size at most `r` with `Q₀^{+C_pad r} ⊆ Q`, the sets
`X = A ∩ Q₀` and `T = (A ∩ Q₀^{+C_pad r}) \ X` satisfy `S(X | T) ≤ S(X)/2 + C_buf r`.
2D only: the harmonic weights of D3.6 need the linear perimeter growth `|∂X_j| ≤ 4(r + 2d_j)`. -/
theorem lemma_3_2 {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    OpenAI.BufferDiscount ℂ q R J Δ := by
  -- D3.14.0: the constants `D` (D3.5), `c₀`, `C'`, `C` (D3.9), `C_pad` (D3.10), `C_buf`
  -- (D3.14.5), depending only on `q, R, J, Δ`
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = 2 * R + 3 := ⟨_, rfl⟩
  have hD0 : 0 < D := by omega
  have hDR : 2 * R + 2 < D := by omega
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = ((q : ℝ) ^ v 2 R) ^ 2 * J := ⟨_, rfl⟩
  obtain ⟨C', hC'def⟩ : ∃ C' : ℝ, C' = 16 * v 2 R * μ (v 2) R := ⟨_, rfl⟩
  have hc₀ : 0 ≤ c₀ := by rw [hc₀def]; positivity
  have hC'0 : 0 ≤ C' := by rw [hC'def]; positivity
  obtain ⟨Cpad, hC, hW⟩ :=
    eq_initial_weight_range q R D hD0 (C := 16 / Real.exp 2 * c₀ * C') hΔ hJ.le
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * (16 / Real.exp 2 * c₀ * C') / Δ +
    1024 * Real.exp 1 * (J / Δ) * C₂ q R := ⟨_, rfl⟩
  have hC₂ : 0 ≤ C₂ q R := by unfold C₂; positivity
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨Cpad, by omega, K * ((Cpad : ℝ) / D + 1) * (2 * D / Real.log ((Cpad + 1) / (2 + D))),
    fun D₀ hD₀ Λ Φ hΦ Ω hΩ E₀ heig hgap A hA Q hQ hs r hr Q₀ hQ₀ hQ₀r hQ₀Q ↦ ?_⟩
  have hRD₀ : (R : ℝ) < D₀ := by have : (0 : ℝ) ≤ R := Nat.cast_nonneg R; linarith
  -- D3.14.0: the regions of D3.5, `X_0 = A ∩ Q₀ ⊆ X_1 ⊆ ⋯ ⊆ X_m`
  obtain ⟨⟨hm1, -, hnest, -⟩, -, -, hsplit, hcnt⟩ :=
    step_3_5 hq hA hQ hs hRD₀ hr hQ₀ hQ₀r hDR hC hQ₀Q
  obtain ⟨n, hn⟩ : ∃ n, n = m Cpad r D := ⟨_, rfl⟩
  rw [← hn] at hm1 hsplit hcnt
  have hX0 : X_j A Q₀ r D 0 = A ∩ Q₀ := if_pos rfl
  have hXjA : ∀ k, X_j A Q₀ r D k ⊆ A := fun k ↦ by
    unfold X_j; split_ifs <;> exact inter_subset_left
  have hXU : A ∩ Q₀ ⊆ Λ := inter_subset_left.trans hA
  set Tj : ℕ → Finset (ℤ × ℤ) := fun j ↦ X_j A Q₀ r D (j + 1) \ (A ∩ Q₀) with hTjdef
  have hU : ∀ j, A ∩ Q₀ ∪ Tj j = X_j A Q₀ r D (j + 1) := fun j ↦
    union_sdiff_of_subset (hX0 ▸ hnest 0 (j + 1) (Nat.zero_le _))
  have hTU : ∀ j, Tj j ⊆ Λ := fun j ↦ sdiff_subset.trans ((hXjA _).trans hA)
  have hTmono : ∀ j, Tj j ⊆ Tj (j + 1) := fun j ↦
    sdiff_subset_sdiff (hnest _ _ (by omega)) le_rfl
  -- D3.6: the weights `a_{j+1}` of the filters on `X_{j+1}`
  have hZ : 0 < Z_r Cpad r D := by
    refine sum_pos (fun j _ ↦ one_div_pos.2 ?_) ⟨1, mem_Icc.2 ⟨le_rfl, hn ▸ hm1⟩⟩
    have : 0 < r + d r D j := by omega
    exact_mod_cast this
  have ha' : ∀ j, 0 < a Cpad r D (j + 1) := fun j ↦ by
    unfold a
    have : (0 : ℝ) < ((r + d r D (j + 1) : ℕ) : ℝ) := by
      have : 0 < r + d r D (j + 1) := by omega
      exact_mod_cast this
    positivity
  have ha2 : ∀ j < n, a Cpad r D (j + 1) ≤ 1 / 2 := fun j hj ↦
    ((hW r hr).2 (j + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).1
  have hne : ∀ S : Finset (ℤ × ℤ), Nonempty (Arealaw.Reg (OpenAI.Qudits q) S) :=
    fun S ↦ ⟨fun _ ↦ ⟨0, hq⟩⟩
  -- D3.9 data: the terms `Φ_X ⊗ 1` over the supports, `(dim ℋ_X)² ‖Φ_X‖ ≤ q^{2 v_R} J`
  have hDs : ∀ t : supports Λ R, (t : Finset (ℤ × ℤ)) ⊆ Λ := fun t ↦ (mem_supports.1 t.2).1
  have hH := hamiltonian_eq_sum_supports hΦ
  have hY : ∀ t : supports Λ R, (Φ t.1).IsHermitian := fun t ↦ (hΦ t.1 (hDs t)).1
  have hYc : ∀ t ∈ (univ : Finset (supports Λ R)),
      (Fintype.card (Arealaw.Reg (OpenAI.Qudits q) t.1) : ℝ) ^ 2 * ‖Φ t.1‖ ≤ c₀ := by
    intro t _
    have hc : (Fintype.card (Arealaw.Reg (OpenAI.Qudits q) t.1) : ℝ) = (q : ℝ) ^ #t.1 := by
      simp [Reg, Fintype.card_pi]
    have hv : #t.1 ≤ v 2 R := (step_2_8 squareLattice (v 2) eq_ball_count_two Λ R 0).2.2.2 t.1 t.2
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    rw [hc, hc₀def]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hq1 hv) 2)
      (hΦ t.1 (hDs t)).2.1 (norm_nonneg _) (by positivity)
  have heig' : (∑ t ∈ (univ : Finset (supports Λ R)), extendId (hDs t) (Φ t.1)) *ᵥ Ω =
      (E₀ : ℂ) • Ω := hH ▸ heig
  have hgap' : HasGlobalGap (∑ t ∈ (univ : Finset (supports Λ R)), extendId (hDs t) (Φ t.1))
      Ω E₀ Δ := hH ▸ hgap
  -- D3.5(d): a support split by `X_{j+1}` lies in `X_{j+2}` and misses `X_1, …, X_j`
  have hd : ∀ t ∈ (univ : Finset (supports Λ R)), ∀ j < n,
      ((t : Finset (ℤ × ℤ)) ∩ (A ∩ Q₀ ∪ Tj j)).Nonempty →
      ((t : Finset (ℤ × ℤ)) \ (A ∩ Q₀ ∪ Tj j)).Nonempty →
      (t : Finset (ℤ × ℤ)) ⊆ A ∩ Q₀ ∪ Tj (j + 1) ∧
        ∀ i < j, Disjoint (A ∩ Q₀ ∪ Tj i) (t : Finset (ℤ × ℤ)) := by
    intro t _ j hj h1 h2
    simp only [hU] at h1 h2 ⊢
    obtain ⟨hdis, hsub⟩ := hsplit t.1 t.2 (j + 1) (by omega) h1 h2
    exact ⟨hsub (j + 1 + 1) (by omega), fun i hi ↦ (hdis (i + 1) (by omega)).symm⟩
  -- D3.5(e): counts and `𝓑_j ≤ C₂ (r + d_{j+1})`
  set w : ℕ → ℝ := fun j ↦ ((r + d r D (j + 1) : ℕ) : ℝ) with hwdef
  have hw : ∀ j, 0 ≤ w j := fun j ↦ Nat.cast_nonneg _
  have hcount : ∀ j < n, ((univ.filter fun t : supports Λ R ↦
      ((t : Finset (ℤ × ℤ)) ∩ (A ∩ Q₀ ∪ Tj j)).Nonempty ∧
      ((t : Finset (ℤ × ℤ)) \ (A ∩ Q₀ ∪ Tj j)).Nonempty).card : ℝ) ≤ C' * w j := by
    intro j hj
    rw [card_filter_coe_sort (supports Λ R) fun X ↦ (X ∩ (A ∩ Q₀ ∪ Tj j)).Nonempty ∧
      (X \ (A ∩ Q₀ ∪ Tj j)).Nonempty, hU, hC'def, hwdef]
    push_cast
    exact (hcnt (j + 1) (by omega) (by omega)).1
  set 𝓑 : ℕ → ℝ := fun j ↦ 1 + ∑ i ∈ univ.filter (fun i : supports Λ R ↦
      ((i : Finset (ℤ × ℤ)) ∩ (A ∩ Q₀ ∪ Tj j)).Nonempty ∧
        ((i : Finset (ℤ × ℤ)) \ (A ∩ Q₀ ∪ Tj j)).Nonempty),
      Real.log (Real.exp 1 * Fintype.card (Arealaw.Reg (OpenAI.Qudits q) i.1)) ^ 2 with h𝓑def
  have h𝓑1 : ∀ j, 1 ≤ 𝓑 j := fun j ↦
    le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ sq_nonneg _)
  have h𝓑 : ∀ j < n, 𝓑 j ≤ C₂ q R * w j := by
    intro j hj
    simp only [h𝓑def, hwdef]
    rw [sum_filter_coe_sort (supports Λ R) (fun X ↦ (X ∩ (A ∩ Q₀ ∪ Tj j)).Nonempty ∧
      (X \ (A ∩ Q₀ ∪ Tj j)).Nonempty)
      (fun X ↦ Real.log (Real.exp 1 * Fintype.card (Arealaw.Reg (OpenAI.Qudits q) X)) ^ 2), hU]
    push_cast
    exact (hcnt (j + 1) (by omega) (by omega)).2
  -- D3.11.4 input: Lemma 3.1 at `u = -a/(1-a)` for the cut `X_{j+1}`, admissible by D3.10(iii)
  have hM : ∀ j < n,
      let ρ := (OpenAI.pureState Ω hΩ).toSubState.restrict (union_subset hXU (hTU j))
      let p := ρ.psd.isHermitian.eigenvalues
      Real.log (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < p i),
          p i * Real.exp (-(-a Cpad r D (j + 1) / (1 - a Cpad r D (j + 1))) * Real.log (p i))) ≤
        -a Cpad r D (j + 1) / (1 - a Cpad r D (j + 1)) * ρ.entropy +
          512 * Real.exp 1 * (J / Δ) * 𝓑 j *
            (-a Cpad r D (j + 1) / (1 - a Cpad r D (j + 1))) ^ 2 := by
    intro j hj
    set b := a Cpad r D (j + 1)
    have hb0 := ha' j
    have hb2 := ha2 j hj
    have hiii := ((hW r hr).2 (j + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).2
    have hu : |-b / (1 - b)| ≤ (32 * Real.sqrt ((1 + J / Δ) * 𝓑 j))⁻¹ := by
      rw [abs_of_nonpos (by rw [neg_div]; exact neg_nonpos.2 (div_nonneg hb0.le (by linarith))),
        neg_div, neg_neg]
      refine hiii.trans ?_
      rw [one_div]
      refine inv_anti₀ (by have := h𝓑1 j; positivity) (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (by positivity))) (by norm_num))
      have := h𝓑 j hj
      simp only [hwdef] at this
      push_cast at this
      exact this
    exact (lemma_3_1 (σ := ℤ × ℤ) (loc := OpenAI.Qudits q) Λ (supports Λ R) (fun t ↦ t.1) hDs
      (fun t ↦ extendId (hDs t) (Φ t.1)) J Δ E₀ Ω hΩ (fun t ↦ ⟨Φ t.1, rfl⟩)
      (fun t ↦ isHermitian_extendId _ (hY t)) hJ.le
      (fun t ↦ by
        refine le_trans ?_ (hΦ t.1 (hDs t)).2.1
        rw [extendId_eq_kronecker, l2_opNorm_submatrix]
        exact l2_opNorm_kronecker_one_le _)
      hΔ heig' hgap' _ (union_subset hXU (hTU j))).1 _ hu
  -- D3.10(i): the overlap budget `v = C ℰ / Δ ≤ ¼`
  have hsumE : ∑ j ∈ range n, w j * a Cpad r D (j + 1) ^ 2 = ℰ Cpad r D := by
    rw [ℰ, ← hn]
    exact sum_range_succ_eq_sum_Icc (fun j ↦ ((r + d r D j : ℕ) : ℝ) * a Cpad r D j ^ 2) n
  have hv : 16 / Real.exp 2 * c₀ * C' * (∑ j ∈ range n, w j * a Cpad r D (j + 1) ^ 2) / Δ ≤
      1 / 4 := by
    rw [hsumE]; exact (hW r hr).1
  -- D3.14.1: D3.11 against eq:initial-norm-upper (D3.13), through the zero-floor limit D3.12.1
  have hXT : ∀ j, Disjoint (A ∩ Q₀) (Tj j) := fun j ↦ disjoint_sdiff
  have h1 : ∀ {B : ℝ}, (∀ f : ℕ → ℝ, (∀ j, 0 < f j) →
      (∀ j, (Fintype.card (Arealaw.Reg (OpenAI.Qudits q) (A ∩ Q₀ ∪ Tj j)) : ℝ) * f j < 1) →
      ∀ L : (j : ℕ) → Matrix (Arealaw.Reg (OpenAI.Qudits q) (A ∩ Q₀ ∪ Tj j))
        (Arealaw.Reg (OpenAI.Qudits q) (A ∩ Q₀ ∪ Tj j)) ℂ,
        (∀ j, IsFilter (f j) (a Cpad r D (j + 1)) (L j)) →
        ‖toEuclideanLin (filterProd (fun j ↦ union_subset hXU (hTU j)) L n)
          (WithLp.toLp 2 Ω)‖ ≤ B) →
      ∀ L : (j : ℕ) → Matrix (Arealaw.Reg (OpenAI.Qudits q) (A ∩ Q₀ ∪ Tj j))
        (Arealaw.Reg (OpenAI.Qudits q) (A ∩ Q₀ ∪ Tj j)) ℂ,
        (∀ j, IsFilter 0 (a Cpad r D (j + 1)) (L j)) →
        ‖toEuclideanLin (filterProd (fun j ↦ union_subset hXU (hTU j)) L n)
          (WithLp.toLp 2 Ω)‖ ≤ B := by
    intro B hB L hL
    refine step_3_12_1 (X := fun j ↦ A ∩ Q₀ ∪ Tj j) (U := Λ) (loc := OpenAI.Qudits q)
      (fun j ↦ union_subset hXU (hTU j)) (a := fun j ↦ a Cpad r D (j + 1))
      (fun j ↦ (ha' j).le) (fun j ↦ hne _) (WithLp.toLp 2 Ω) n (B := B) ?_ (L := L) ?_
    · exact hB
    · exact hL
  have key := step_3_14_1 (loc := OpenAI.Qudits q) (D := fun t : supports Λ R ↦ t.1)
    (Y := fun t ↦ Φ t.1) (𝓑 := 𝓑) (w := w) (ϑ := J / Δ) (a := fun j ↦ a Cpad r D (j + 1))
    hXU Tj hTU hTmono ha' n ha2 (fun j ↦ hne _) Ω hΩ
    (univ : Finset (supports Λ R)) hDs hY hc₀ (fun t _ ↦ by convert hYc t (mem_univ _) using 4)
    heig' hΔ hgap' hd hC'0 hw hcount hv
    (div_nonneg hJ.le hΔ.le) (fun j ↦ (zero_le_one.trans (h𝓑1 j))) hM h1
    (fun hB0 hB ↦ eq_initial_norm_upper hXU Tj hTU hTmono hXT ha' n Ω hΩ hB0 hB)
  -- D3.14.2–D3.14.4: SSA with `T_j ⊆ T_m ⊆ T`, `∑_j a_j = 2`
  obtain ⟨f, hf⟩ : ∃ f : Finset (ℤ × ℤ) → ℝ, ∀ S (h : S ⊆ Λ),
      (OpenAI.pureState Ω hΩ).regionEntropy h = f S :=
    ⟨fun S ↦ if h : S ⊆ Λ then (OpenAI.pureState Ω hΩ).regionEntropy h else 0,
      fun S h ↦ (dif_pos h).symm⟩
  set T := (A ∩ ambientDilation Q₀ (Cpad * r)) \ (A ∩ Q₀) with hTdef
  have hTΛ : T ⊆ Λ := sdiff_subset.trans (inter_subset_left.trans hA)
  set Tj' : ℕ → Finset (ℤ × ℤ) := fun j ↦ X_j A Q₀ r D (min j n) \ (A ∩ Q₀) with hTj'def
  have hTT : ∀ j, Tj' j ⊆ T := fun j ↦ by
    simp only [hTj'def, hTdef]
    rcases Nat.eq_zero_or_pos (min j n) with h0 | h0
    · rw [h0, hX0, sdiff_self]; exact empty_subset _
    · refine sdiff_subset_sdiff ?_ le_rfl
      simp only [X_j, if_neg h0.ne']
      refine inter_subset_inter_left (ambientDilation_mono' ?_)
      have h1 : d r D (min j n) ≤ d r D n := by unfold d; gcongr; exact min_le_right _ _
      exact h1.trans (hn ▸ d_m_le hC)
  have hmono' : ∀ j ∈ Icc 1 n, Tj' j ⊆ Tj' n := fun j hj ↦
    sdiff_subset_sdiff (hnest _ _ (by simp only [min_self]; exact min_le_right _ _)) le_rfl
  have hTj : ∀ j, j < n → Tj j = Tj' (j + 1) := fun j hj ↦ by
    simp only [Tj, hTj'def, Nat.min_eq_left (show j + 1 ≤ n by omega)]
  have hsum2 : ∑ j ∈ Icc 1 n, a Cpad r D j = 2 := hn ▸ (eq_initial_harmonic_weights hD0 hC hr).1
  have ha1 : ∀ j ∈ Icc 1 n, 0 < a Cpad r D j := fun j hj ↦ by
    have := ha' (j - 1); rwa [Nat.sub_add_cancel (mem_Icc.1 hj).1] at this
  set v := 16 / Real.exp 2 * c₀ * C' * (∑ j ∈ range n, w j * a Cpad r D (j + 1) ^ 2) / Δ
  set E := ∑ j ∈ range n, 1024 * Real.exp 1 * (J / Δ) * 𝓑 j * a Cpad r D (j + 1) ^ 2 + 2 * n * v
  have hshift : ∀ g : Finset (ℤ × ℤ) → ℝ, ∑ j ∈ Icc 1 n, a Cpad r D j * g (Tj' j) =
      ∑ j ∈ range n, a Cpad r D (j + 1) * g (Tj j) := fun g ↦ by
    rw [← sum_range_succ_eq_sum_Icc]
    exact sum_congr rfl fun j hj ↦ by rw [hTj j (mem_range.1 hj)]
  have hshift' : ∀ g : Finset (ℤ × ℤ) → ℝ, ∑ j ∈ Icc 1 n, a Cpad r D j * g (A ∩ Q₀ ∪ Tj' j) =
      ∑ j ∈ range n, a Cpad r D (j + 1) * g (A ∩ Q₀ ∪ Tj j) := fun g ↦ by
    rw [← sum_range_succ_eq_sum_Icc]
    exact sum_congr rfl fun j hj ↦ by rw [hTj j (mem_range.1 hj)]
  have h314 := step_3_14 (OpenAI.pureState Ω hΩ) Tj' hXU hTΛ disjoint_sdiff hTT hmono'
    (a Cpad r D) ha1 hsum2 (E := E) (by
      simp only [hf] at key ⊢
      rw [hshift' f, hshift f]
      rw [sum_sub_distrib] at key
      linarith)
  -- D3.14.5: `E/2 ≤ C_buf r`
  have hE : E ≤ K * (n + 1) * ℰ Cpad r D := by
    have h1 : ∑ j ∈ range n, 1024 * Real.exp 1 * (J / Δ) * 𝓑 j * a Cpad r D (j + 1) ^ 2 ≤
        1024 * Real.exp 1 * (J / Δ) * C₂ q R * ℰ Cpad r D := by
      rw [← hsumE, mul_sum]
      refine sum_le_sum fun j hj ↦ ?_
      have h𝓑j := h𝓑 j (mem_range.1 hj)
      calc 1024 * Real.exp 1 * (J / Δ) * 𝓑 j * a Cpad r D (j + 1) ^ 2
          = 1024 * Real.exp 1 * (J / Δ) * (𝓑 j * a Cpad r D (j + 1) ^ 2) := by ring
        _ ≤ 1024 * Real.exp 1 * (J / Δ) * (C₂ q R * w j * a Cpad r D (j + 1) ^ 2) := by gcongr
        _ = _ := by ring
    have h2 : 2 * n * v = n * (2 * (16 / Real.exp 2 * c₀ * C') / Δ) * ℰ Cpad r D := by
      simp only [v, hsumE]; ring
    have hE0 : 0 ≤ ℰ Cpad r D := by unfold ℰ; positivity
    have hk1 : 0 ≤ 2 * (16 / Real.exp 2 * c₀ * C') / Δ := by positivity
    have hk2 : 0 ≤ 1024 * Real.exp 1 * (J / Δ) * C₂ q R := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc E ≤ 1024 * Real.exp 1 * (J / Δ) * C₂ q R * ℰ Cpad r D +
          n * (2 * (16 / Real.exp 2 * c₀ * C') / Δ) * ℰ Cpad r D := by
          simp only [E]; rw [h2]; linarith
      _ ≤ _ := by rw [hKdef]; nlinarith [mul_nonneg hn0 (mul_nonneg hk2 hE0),
          mul_nonneg hk1 hE0]
  have h5 := step_3_14_5 hD0 hC hr hK0
  rw [← hn] at h5
  simp only [hf] at h314 ⊢
  linarith

end D314

end AreaLaw
