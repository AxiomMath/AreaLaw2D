import AreaLaw.S04_Quasilocal.Positive

/-!
# §4.2 Lemma 4.4: square roots and local channels

Digest `digest/04-quasilocal.md` (D4.10), paper `paper/sections/03-quasilocal.tex`
lines 336–390.
-/

namespace AreaLaw

open Arealaw Matrix
open OpenAI (IsSupportedOn HasGlobalGap)
open scoped Finset
open scoped Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

section RootChannel

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- D4.10. `𝓔(B) = G B G + K B K`. -/
def rootChannel (G K B : Matrix n n ℂ) : Matrix n n ℂ :=
  G * B * G + K * B * K

omit [DecidableEq n] in
/-- D4.10.4. Each summand of `𝓔` is `B ↦ A^* B A` with `A` Hermitian, so `𝓔` is positive. -/
theorem rootChannel_nonneg {G K B : Matrix n n ℂ} (hG : G.IsHermitian) (hK : K.IsHermitian)
    (hB : 0 ≤ B) : 0 ≤ rootChannel G K B := by
  rw [nonneg_iff_posSemidef] at hB ⊢
  have h1 := hB.conjTranspose_mul_mul_same G
  have h2 := hB.conjTranspose_mul_mul_same K
  rw [hG.eq] at h1
  rw [hK.eq] at h2
  exact h1.add h2

/-- D4.10.6. `‖𝓔_{G,K}(B) − 𝓔_{G',K'}(B)‖ ≤ 2(‖G − G'‖ + ‖K − K'‖)‖B‖` for contractions. -/
theorem norm_rootChannel_sub_le {G K G' K' : Matrix n n ℂ} (hG : ‖G‖ ≤ 1) (hK : ‖K‖ ≤ 1)
    (hG' : ‖G'‖ ≤ 1) (hK' : ‖K'‖ ≤ 1) (B : Matrix n n ℂ) :
    ‖rootChannel G K B - rootChannel G' K' B‖ ≤ 2 * (‖G - G'‖ + ‖K - K'‖) * ‖B‖ := by
  have key : ∀ A A' : Matrix n n ℂ, ‖A‖ ≤ 1 → ‖A'‖ ≤ 1 →
      ‖A * B * A - A' * B * A'‖ ≤ 2 * ‖A - A'‖ * ‖B‖ := by
    intro A A' hA hA'
    have hd : A * B * A - A' * B * A' = (A - A') * B * A + A' * B * (A - A') := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [hd]
    calc ‖(A - A') * B * A + A' * B * (A - A')‖
        ≤ ‖A - A'‖ * ‖B‖ * ‖A‖ + ‖A'‖ * ‖B‖ * ‖A - A'‖ :=
          (norm_add_le _ _).trans (add_le_add
            ((l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
              (norm_nonneg _)))
            ((l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
              (norm_nonneg _))))
      _ ≤ ‖A - A'‖ * ‖B‖ * 1 + 1 * ‖B‖ * ‖A - A'‖ := by gcongr
      _ = 2 * ‖A - A'‖ * ‖B‖ := by ring
  have hs : rootChannel G K B - rootChannel G' K' B =
      (G * B * G - G' * B * G') + (K * B * K - K' * B * K') := by
    simp only [rootChannel]; abel
  rw [hs]
  calc _ ≤ 2 * ‖G - G'‖ * ‖B‖ + 2 * ‖K - K'‖ * ‖B‖ :=
        (norm_add_le _ _).trans (add_le_add (key G G' hG hG') (key K K' hK hK'))
    _ = _ := by ring

/-- D4.10.7. If `G * G + K * K = 1` and `B` commutes with `G` and `K`, then `𝓔(B) = B`. -/
theorem rootChannel_eq_self_of_commute {G K B : Matrix n n ℂ} (h : G * G + K * K = 1)
    (hG : Commute G B) (hK : Commute K B) : rootChannel G K B = B := by
  rw [rootChannel, hG.eq, hK.eq, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h,
    Matrix.mul_one]

omit [Fintype n] [DecidableEq n] in
/-- D4.10.6. `X ⊗ I - Y ⊗ I = (X - Y) ⊗ I`. -/
theorem sub_kronecker_one {κ : Type*} [DecidableEq κ] (X Y : Matrix n n ℂ) :
    X ⊗ₖ (1 : Matrix κ κ ℂ) - Y ⊗ₖ (1 : Matrix κ κ ℂ) = (X - Y) ⊗ₖ (1 : Matrix κ κ ℂ) := by
  ext
  simp [kroneckerMap_apply, sub_mul]

set_option linter.unusedDecidableInType false in
/-- D4.10.7. An operator commuting with `M ≥ 0` commutes with `√M`. -/
theorem commute_sqrt {M B : Matrix n n ℂ} (hM : 0 ≤ M) (hB : Commute M B) :
    Commute (CFC.sqrt M) B := by
  rw [CFC.sqrt_eq_real_sqrt M hM, cfcₙ_eq_cfc]
  exact hB.cfc_real _

set_option linter.unusedDecidableInType false in
/-- D4.10.7. An operator commuting with `M ⊗ I` (`M ≥ 0`) commutes with `√M ⊗ I`. -/
theorem commute_sqrt_kronecker_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix n n ℂ} {B : Matrix (n × κ) (n × κ) ℂ} (hM : 0 ≤ M)
    (hB : Commute (M ⊗ₖ (1 : Matrix κ κ ℂ)) B) :
    Commute (CFC.sqrt M ⊗ₖ (1 : Matrix κ κ ℂ)) B := by
  rw [sqrt_kronecker_one hM]
  exact commute_sqrt ((nonneg_iff_posSemidef.mp hM).kronecker PosSemidef.one).nonneg hB

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- D4.10.1, D4.10.5. Tensoring by an identity preserves the root data: `√M ⊗ I` is positive,
has norm at most `‖√M‖`, and `G ⊗ I, K ⊗ I` again satisfy `G² + K² = I`. -/
theorem sqrt_kronecker_one_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ] {M : Matrix n n ℂ}
    (hM : 0 ≤ M) : 0 ≤ CFC.sqrt M ⊗ₖ (1 : Matrix κ κ ℂ) := by
  rw [sqrt_kronecker_one hM]
  exact CFC.sqrt_nonneg _

theorem kronecker_one_mul_add {κ : Type*} [Fintype κ] [DecidableEq κ] {G K : Matrix n n ℂ}
    (h : G * G + K * K = 1) :
    (G ⊗ₖ (1 : Matrix κ κ ℂ)) * (G ⊗ₖ (1 : Matrix κ κ ℂ)) +
      (K ⊗ₖ (1 : Matrix κ κ ℂ)) * (K ⊗ₖ (1 : Matrix κ κ ℂ)) = 1 := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, ← add_kronecker, h,
    one_kronecker_one]

/-- D4.10.4–6 for one pair of roots `(G, K)` with `G² + K² = I`, `0 ≤ G, K ≤ I`, on one
algebra: `𝓔` is unital, positive, contractive. -/
theorem rootChannel_props {G K : Matrix n n ℂ} (hG : 0 ≤ G) (hK : 0 ≤ K)
    (h : G * G + K * K = 1) :
    rootChannel G K 1 = 1 ∧ (∀ B, 0 ≤ B → 0 ≤ rootChannel G K B) ∧
      ∀ B, ‖rootChannel G K B‖ ≤ ‖B‖ :=
  ⟨rootChannel_eq_self_of_commute h (Commute.one_right G) (Commute.one_right K),
    fun _ hB => rootChannel_nonneg (nonneg_iff_posSemidef.mp hG).isHermitian
      (nonneg_iff_posSemidef.mp hK).isHermitian hB,
    Matrix.norm_mul_mul_add_mul_mul_le (nonneg_iff_posSemidef.mp hG).isHermitian
      (nonneg_iff_posSemidef.mp hK).isHermitian h⟩

end RootChannel

/-- D4.10.3. `t ≤ C e^{-c x}` gives `√t ≤ √C e^{-(c/2) x}`. -/
theorem sqrt_le_of_le_exp {t C c x : ℝ} (ht : t ≤ C * Real.exp (-c * x)) :
    Real.sqrt t ≤ Real.sqrt C * Real.exp (-(c / 2) * x) := by
  have he : Real.exp (-c * x) = Real.exp (-(c / 2) * x) * Real.exp (-(c / 2) * x) := by
    rw [← Real.exp_add]; ring_nf
  calc Real.sqrt t ≤ Real.sqrt (C * Real.exp (-c * x)) := Real.sqrt_le_sqrt ht
    _ = _ := by
      rw [Real.sqrt_mul' _ (Real.exp_pos _).le, he, Real.sqrt_mul_self (Real.exp_pos _).le]

section Lemma44

open GraphDomain

/-- D4.10 (Lemma 4.4). For `k_i, k_{i,l}` of D4.6 define `G_i = (I - k_i)^{1/2}`,
`K_i = k_i^{1/2}`, `G_{i,l} = (I - k_{i,l})^{1/2}`, `K_{i,l} = k_{i,l}^{1/2}`. These are positive
contractions, `G_i Ω = Ω`, `K_i Ω = 0`, and
`‖G_i - G_{i,l}‖ + ‖K_i - K_{i,l}‖ ≤ C e^{-c l^α}`, `G_{i,l}^2 + K_{i,l}^2 = I`.
Define on the full operator algebra `𝓔_i(B) = G_i B G_i + K_i B K_i`,
`𝓔_{i,l}(B) = G_{i,l} B G_{i,l} + K_{i,l} B K_{i,l}`. Both are unital, completely positive,
operator-norm contractions, also after tensoring with `id` on any auxiliary matrix algebra, and
`‖𝓔_i - 𝓔_{i,l}‖_cb ≤ C e^{-c l^α}`, `‖·‖_cb` = supremum of operator norms over all auxiliary
extensions. `𝓔_{i,l}` fixes every operator commuting with the full algebra on `N_l(a_i)`,
including operators supported outside the ball. -/
theorem lemma_4_4 {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
    {loc : σ → Type} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)]
    {p : ℕ} (hp : 1 ≤ p) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∃ C c : ℝ, 0 < c ∧
    ∀ Λ : Finset σ, ∀ Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ,
      IsAdmissible G Λ R J Φ →
    ∀ (Ω : Reg loc Λ → ℂ) (_ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ anchor : Finset σ → σ, (∀ X ∈ supports G Λ R, anchor X ∈ X) →
    ∃ k : Finset σ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ,
      ((∀ X ∈ supports G Λ R, 0 ≤ k X ∧ k X ≤ 1 ∧ k X *ᵥ Ω = 0) ∧
      (cstar : ℂ)⁻¹ • (hamiltonian Λ Φ - (E₀ : ℂ) • 1) ≤ ∑ X ∈ supports G Λ R, k X ∧
      ((Δ / cstar : ℝ) : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤
        (cstar : ℂ)⁻¹ • (hamiltonian Λ Φ - (E₀ : ℂ) • 1) ∧
      (∀ X ∈ supports G Λ R, ∀ l : ℕ,
        0 ≤ E G Λ (anchor X) l (k X) ∧ E G Λ (anchor X) l (k X) ≤ 1 ∧
        ‖k X - E G Λ (anchor X) l (k X)‖ ≤ C * Real.exp (-c * (l : ℝ) ^ ((p : ℝ) / (p + 1)))) ∧
      ∀ X ∈ supports G Λ R, IsSupportedOn (component_subset G Λ (anchor X)) (k X)) ∧
      ∀ X ∈ supports G Λ R,
        let Gi := CFC.sqrt (1 - k X)
        let Ki := CFC.sqrt (k X)
        let Gil := fun l => CFC.sqrt (1 - E G Λ (anchor X) l (k X))
        let Kil := fun l => CFC.sqrt (E G Λ (anchor X) l (k X))
        ((0 ≤ Gi ∧ Gi ≤ 1) ∧ (0 ≤ Ki ∧ Ki ≤ 1) ∧
          ∀ l, (0 ≤ Gil l ∧ Gil l ≤ 1) ∧ (0 ≤ Kil l ∧ Kil l ≤ 1)) ∧
        (Gi *ᵥ Ω = Ω ∧ Ki *ᵥ Ω = 0) ∧
        (∀ l : ℕ, ‖Gi - Gil l‖ + ‖Ki - Kil l‖ ≤
          2 * Real.sqrt C * Real.exp (-(c / 2) * (l : ℝ) ^ ((p : ℝ) / (p + 1)))) ∧
        (∀ l, Gil l * Gil l + Kil l * Kil l = 1) ∧
        -- unital
        (rootChannel Gi Ki 1 = 1 ∧ (∀ l, rootChannel (Gil l) (Kil l) 1 = 1) ∧
          ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
            rootChannel (Gi ⊗ₖ (1 : Matrix κ κ ℂ)) (Ki ⊗ₖ 1) 1 = 1 ∧
            ∀ l, rootChannel (Gil l ⊗ₖ (1 : Matrix κ κ ℂ)) (Kil l ⊗ₖ 1) 1 = 1) ∧
        -- completely positive
        ((∀ B, 0 ≤ B → 0 ≤ rootChannel Gi Ki B ∧ ∀ l, 0 ≤ rootChannel (Gil l) (Kil l) B) ∧
          ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
            0 ≤ B → 0 ≤ rootChannel (Gi ⊗ₖ (1 : Matrix κ κ ℂ)) (Ki ⊗ₖ 1) B ∧
              ∀ l, 0 ≤ rootChannel (Gil l ⊗ₖ (1 : Matrix κ κ ℂ)) (Kil l ⊗ₖ 1) B) ∧
        -- operator-norm contractions
        ((∀ B, ‖rootChannel Gi Ki B‖ ≤ ‖B‖ ∧ ∀ l, ‖rootChannel (Gil l) (Kil l) B‖ ≤ ‖B‖) ∧
          ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
            ‖rootChannel (Gi ⊗ₖ (1 : Matrix κ κ ℂ)) (Ki ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
              ∀ l, ‖rootChannel (Gil l ⊗ₖ (1 : Matrix κ κ ℂ)) (Kil l ⊗ₖ 1) B‖ ≤ ‖B‖) ∧
        -- cb-norm tail
        ((∀ (l : ℕ) B, ‖rootChannel Gi Ki B - rootChannel (Gil l) (Kil l) B‖ ≤
            4 * Real.sqrt C * Real.exp (-(c / 2) * (l : ℝ) ^ ((p : ℝ) / (p + 1))) * ‖B‖) ∧
          ∀ (l : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
            (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
            ‖rootChannel (Gi ⊗ₖ (1 : Matrix κ κ ℂ)) (Ki ⊗ₖ 1) B -
                rootChannel (Gil l ⊗ₖ (1 : Matrix κ κ ℂ)) (Kil l ⊗ₖ 1) B‖ ≤
              4 * Real.sqrt C * Real.exp (-(c / 2) * (l : ℝ) ^ ((p : ℝ) / (p + 1))) * ‖B‖) ∧
        -- fixed points: the commutant of the algebra on `N_l(a)`
        (∀ l (B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ),
          (∀ A, Commute (extendId (graphNbhd_subset G Λ {anchor X} l) A) B) →
            rootChannel (Gil l) (Kil l) B = B) ∧
        ∀ l (κ : Type) [Fintype κ] [DecidableEq κ] (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
          (∀ A, Commute (extendId (graphNbhd_subset G Λ {anchor X} l) A ⊗ₖ (1 : Matrix κ κ ℂ)) B) →
            rootChannel (Gil l ⊗ₖ (1 : Matrix κ κ ℂ)) (Kil l ⊗ₖ 1) B = B := by
  obtain ⟨cstar, hcs, C, c, hc, hP⟩ := prop_4_3 G V hV (loc := loc) hp R J Δ hΔ
  refine ⟨cstar, hcs, C, c, hc, fun Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor => ?_⟩
  obtain ⟨kf, hkf, hsum, hgapk, htailf, hsupp⟩ := hP Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor
  refine ⟨kf, ⟨hkf, hsum, hgapk, htailf, hsupp⟩, fun X hX => ?_⟩
  obtain ⟨hk₀, hk₁, hkΩ⟩ := hkf X hX
  have hE : ∀ l, 0 ≤ E G Λ (anchor X) l (kf X) ∧ E G Λ (anchor X) l (kf X) ≤ 1 :=
    fun l => ⟨(htailf X hX l).1, (htailf X hX l).2.1⟩
  have htail := fun l => (htailf X hX l).2.2
  generalize anchor X = a at hE htail ⊢
  generalize kf X = k at hk₀ hk₁ hkΩ hE htail ⊢
  set α : ℝ := (p : ℝ) / (p + 1)
  intro Gi Ki Gil Kil
  -- D4.10.1
  have hroot : ∀ {M : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}, 0 ≤ M → M ≤ 1 →
      (0 ≤ CFC.sqrt (1 - M) ∧ CFC.sqrt (1 - M) ≤ 1) ∧ (0 ≤ CFC.sqrt M ∧ CFC.sqrt M ≤ 1) ∧
        CFC.sqrt (1 - M) * CFC.sqrt (1 - M) + CFC.sqrt M * CFC.sqrt M = 1 := by
    intro M h₀ h₁
    refine ⟨⟨CFC.sqrt_nonneg _, by simpa using CFC.sqrt_le_sqrt (1 - M) 1 (by simpa using h₀)⟩,
      ⟨CFC.sqrt_nonneg _, by simpa using CFC.sqrt_le_sqrt M 1 h₁⟩, ?_⟩
    rw [CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr h₁), CFC.sqrt_mul_sqrt_self _ h₀,
      sub_add_cancel]
  have h1 := hroot hk₀ hk₁
  have h1l := fun l => hroot (hE l).1 (hE l).2
  -- D4.10.2
  have h2G : Gi *ᵥ Ω = Ω := by
    have h := mulVec_eq_smul_of_mul_self_mulVec (CFC.sqrt_nonneg (1 - k)) zero_le_one (v := Ω)
      (by rw [CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hk₁), Matrix.sub_mulVec, hkΩ]; simp)
    simpa using h
  have h2K : Ki *ᵥ Ω = 0 := by
    have h := mulVec_eq_smul_of_mul_self_mulVec (CFC.sqrt_nonneg k) le_rfl (v := Ω)
      (by rw [CFC.sqrt_mul_sqrt_self k hk₀, hkΩ]; simp)
    simpa using h
  have h2 : Gi *ᵥ Ω = Ω ∧ Ki *ᵥ Ω = 0 := ⟨h2G, h2K⟩
  -- D4.10.3
  have h3 : ∀ l : ℕ, ‖Gi - Gil l‖ + ‖Ki - Kil l‖ ≤
      2 * Real.sqrt C * Real.exp (-(c / 2) * (l : ℝ) ^ α) := by
    intro l
    have hs := sqrt_le_of_le_exp (htail l)
    have hG := CFC.norm_sqrt_sub_sqrt_le (sub_nonneg.mpr hk₁) (sub_nonneg.mpr (hE l).2)
    rw [sub_sub_sub_cancel_left, norm_sub_rev (E G Λ a l k) k] at hG
    have hK := CFC.norm_sqrt_sub_sqrt_le hk₀ (hE l).1
    exact (add_le_add hG hK).trans (by linarith)
  -- D4.10.4, D4.10.5
  have h45 := rootChannel_props h1.1.1 h1.2.1.1 h1.2.2
  have h45l := fun l => rootChannel_props (h1l l).1.1 (h1l l).2.1.1 (h1l l).2.2
  have h45κ : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], _ := fun κ _ _ =>
    rootChannel_props (sqrt_kronecker_one_nonneg (κ := κ) (sub_nonneg.mpr hk₁))
      (sqrt_kronecker_one_nonneg (κ := κ) hk₀) (kronecker_one_mul_add h1.2.2)
  have h45lκ : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (l : ℕ), _ := fun κ _ _ l =>
    rootChannel_props (sqrt_kronecker_one_nonneg (κ := κ) (sub_nonneg.mpr (hE l).2))
      (sqrt_kronecker_one_nonneg (κ := κ) (hE l).1) (kronecker_one_mul_add (h1l l).2.2)
  -- D4.10.6
  have hn : ∀ {M : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}, 0 ≤ M → M ≤ 1 → ‖M‖ ≤ 1 :=
    fun h₀ h₁ => l2_opNorm_le_one_of_nonneg_of_le_one h₀ h₁
  have h6 : ∀ (l : ℕ) (B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ),
      ‖rootChannel Gi Ki B - rootChannel (Gil l) (Kil l) B‖ ≤
        4 * Real.sqrt C * Real.exp (-(c / 2) * (l : ℝ) ^ α) * ‖B‖ := by
    intro l B
    refine (norm_rootChannel_sub_le (hn h1.1.1 h1.1.2) (hn h1.2.1.1 h1.2.1.2)
      (hn (h1l l).1.1 (h1l l).1.2) (hn (h1l l).2.1.1 (h1l l).2.1.2) B).trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h3 l) zero_le_two)
      (norm_nonneg B)).trans_eq (by ring)
  have h6κ : ∀ (l : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
      ‖rootChannel (Gi ⊗ₖ (1 : Matrix κ κ ℂ)) (Ki ⊗ₖ 1) B -
          rootChannel (Gil l ⊗ₖ (1 : Matrix κ κ ℂ)) (Kil l ⊗ₖ 1) B‖ ≤
        4 * Real.sqrt C * Real.exp (-(c / 2) * (l : ℝ) ^ α) * ‖B‖ := by
    intro l κ _ _ B
    have hk1 : ∀ X : Matrix (Reg loc Λ) (Reg loc Λ) ℂ, ‖X ⊗ₖ (1 : Matrix κ κ ℂ)‖ ≤ ‖X‖ :=
      fun X => l2_opNorm_kronecker_one_le X
    refine (norm_rootChannel_sub_le ((hk1 _).trans (hn h1.1.1 h1.1.2))
      ((hk1 _).trans (hn h1.2.1.1 h1.2.1.2)) ((hk1 _).trans (hn (h1l l).1.1 (h1l l).1.2))
      ((hk1 _).trans (hn (h1l l).2.1.1 (h1l l).2.1.2)) B).trans ?_
    rw [sub_kronecker_one, sub_kronecker_one]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((add_le_add (hk1 _) (hk1 _)).trans (h3 l)) zero_le_two) (norm_nonneg B)).trans_eq
      (by ring)
  -- D4.10.7
  have h7 : ∀ l (B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ),
      (∀ A, Commute (extendId (graphNbhd_subset G Λ {a} l) A) B) →
        rootChannel (Gil l) (Kil l) B = B := by
    intro l B hB
    obtain ⟨A₀, hA₀⟩ := isSupportedOn_E (G := G) Λ a l k
    have hk : Commute (E G Λ a l k) B := hA₀ ▸ hB A₀
    have h1' : Commute (1 - E G Λ a l k) B := (Commute.one_left B).sub_left hk
    exact rootChannel_eq_self_of_commute (h1l l).2.2
      (commute_sqrt (sub_nonneg.mpr (hE l).2) h1') (commute_sqrt (hE l).1 hk)
  have h7κ : ∀ l (κ : Type) [Fintype κ] [DecidableEq κ]
      (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
      (∀ A, Commute (extendId (graphNbhd_subset G Λ {a} l) A ⊗ₖ (1 : Matrix κ κ ℂ)) B) →
        rootChannel (Gil l ⊗ₖ (1 : Matrix κ κ ℂ)) (Kil l ⊗ₖ 1) B = B := by
    intro l κ _ _ B hB
    obtain ⟨A₀, hA₀⟩ := isSupportedOn_E (G := G) Λ a l k
    have hk : Commute (E G Λ a l k ⊗ₖ (1 : Matrix κ κ ℂ)) B := hA₀ ▸ hB A₀
    have hone : Commute ((1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) B := by
      have h := hB 1
      rwa [extendId_one] at h
    have h1' : Commute ((1 - E G Λ a l k) ⊗ₖ (1 : Matrix κ κ ℂ)) B := by
      rw [← sub_kronecker_one]; exact hone.sub_left hk
    exact rootChannel_eq_self_of_commute (kronecker_one_mul_add (h1l l).2.2)
      (commute_sqrt_kronecker_one (sub_nonneg.mpr (hE l).2) h1')
      (commute_sqrt_kronecker_one (hE l).1 hk)
  refine ⟨⟨h1.1, h1.2.1, fun l => ⟨(h1l l).1, (h1l l).2.1⟩⟩, h2,
    h3,
    fun l => (h1l l).2.2,
    ⟨h45.1, fun l => (h45l l).1, fun κ _ _ => ⟨(h45κ κ).1, fun l => (h45lκ κ l).1⟩⟩,
    ⟨fun B hB => ⟨h45.2.1 B hB, fun l => (h45l l).2.1 B hB⟩,
      fun κ _ _ B hB => ⟨(h45κ κ).2.1 B hB, fun l => (h45lκ κ l).2.1 B hB⟩⟩,
    ⟨fun B => ⟨h45.2.2 B, fun l => (h45l l).2.2 B⟩,
      fun κ _ _ B => ⟨(h45κ κ).2.2 B, fun l => (h45lκ κ l).2.2 B⟩⟩,
    ⟨h6, h6κ⟩, h7, h7κ⟩

end Lemma44

end AreaLaw
