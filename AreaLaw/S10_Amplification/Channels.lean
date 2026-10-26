import AreaLaw.S10_Amplification.Setup

/-!
# §10.1 Lemma 10.1: deterministic channel facts (D10.2.1–D10.2.7, D10.2.10)

Digest `digest/10-amplification.md` (D10.2), paper `paper/sections/09-amplification.tex`
lines 42–235. Graph-level: a simple graph `G` on a site type `σ`; nothing here depends on a
ball-growth bound. Operators act on `Reg loc Λ × κ`, the spectator `κ` untouched.

Some declarations here come from the v1 file `OpenAI/LiebRobinson/GraphBallStabilization.lean`,
whose header records it as ported or adapted from `LionSR/TNLean` (see `NOTICE`).
-/

namespace AreaLaw

open Arealaw Matrix GraphDomain
open OpenAI (condExpect IsSupportedOn)
open scoped Finset Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-! ## Word lemmas (D10.2.1) -/

section Words

variable {ι n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

/-- D10.2.1. If each map acts on `v` as `C ↦ G̃_i C`, a word of maps acts as the word
product: `wordMap 𝓔 w B v = wordProd G̃ w (B v)`. -/
theorem wordMap_mulVec {𝓔 : ι → Matrix n n ℂ → Matrix n n ℂ} {Gt : ι → Matrix n n ℂ}
    {v : n → ℂ} (h : ∀ i C, 𝓔 i C *ᵥ v = Gt i *ᵥ (C *ᵥ v)) :
    ∀ (m : ℕ) (w : Fin m → ι) (B : Matrix n n ℂ),
      wordMap 𝓔 m w B *ᵥ v = wordProd Gt m w *ᵥ (B *ᵥ v)
  | 0, _, B => by simp
  | m + 1, w, B => by
    rw [wordMap_succ, wordProd_succ, h, wordMap_mulVec h m, mulVec_mulVec]

/-- A word product of `A_i ⊗ I` is the word product of `A_i`, tensored with `I`. -/
theorem wordProd_kronecker_one (A : ι → Matrix n n ℂ) :
    ∀ (m : ℕ) (w : Fin m → ι),
      wordProd (fun i => A i ⊗ₖ (1 : Matrix κ κ ℂ)) m w = wordProd A m w ⊗ₖ 1
  | 0, _ => by simp
  | m + 1, w => by
    rw [wordProd_succ, wordProd_succ, wordProd_kronecker_one A m, ← mul_kronecker_mul,
      Matrix.mul_one]

omit [DecidableEq n] in
/-- `(A ⊗ I)(Ω ⊗ ξ) = (A Ω) ⊗ ξ`. -/
theorem kronecker_one_mulVec_tensVec (A : Matrix n n ℂ) (Ω : n → ℂ) (ξ : κ → ℂ) :
    (A ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ tensVec Ω ξ = tensVec (A *ᵥ Ω) ξ := by
  ext ⟨i, j⟩
  simp only [mulVec, dotProduct, tensVec, kroneckerMap_apply, Fintype.sum_prod_type,
    one_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]
  simp [mul_assoc]

end Words

/-! ## The channels `𝓔_i`, `𝓔_{i,l}` and the shells `Δ_{i,l}` -/

section Channels

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) {loc : σ → Type}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {Λ : Finset σ} {κ : Type} [Fintype κ]
  [DecidableEq κ]

/-- D10.2. `𝓔_i(B) = G_i B G_i + K_i B K_i`, `G_i = (I - k_i)^{1/2}`, `K_i = k_i^{1/2}`, on
`Reg loc Λ × κ` (spectators untouched). -/
noncomputable def chan (k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ :=
  rootChannel (CFC.sqrt (1 - k) ⊗ₖ (1 : Matrix κ κ ℂ)) (CFC.sqrt k ⊗ₖ (1 : Matrix κ κ ℂ)) B

/-- D10.2. `𝓔_{i,l}`: the same with `k_{i,l} = E_{i,l} k_i`. -/
noncomputable def chanL (a : σ) (l : ℕ) (k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ :=
  chan (E G Λ a l k) B

/-- D10.2.3. `Δ_{i,l} = 𝓔_{i,l} - 𝓔_{i,l-1}`, `𝓔_{i,-1} = id`. -/
noncomputable def shell (a : σ) (l : ℕ) (k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ :=
  chanL G a l k B - (if l = 0 then B else chanL G a (l - 1) k B)

/-- D10.2.3. The shell constant `2 + 4√C (1 + e^{c/2})`. -/
noncomputable def shellConst (C c : ℝ) : ℝ := 2 + 4 * √C * (1 + Real.exp (c / 2))

theorem shellConst_nonneg (C c : ℝ) : 0 ≤ shellConst C c := by
  unfold shellConst; positivity

variable {G}

/-- The root data of `0 ≤ M ≤ I`: `√(I - M) ⊗ I`, `√M ⊗ I` are contractions with
`G² + K² = I`. -/
theorem root_data {M : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hM : 0 ≤ M ∧ M ≤ 1) :
    ‖CFC.sqrt (1 - M) ⊗ₖ (1 : Matrix κ κ ℂ)‖ ≤ 1 ∧ ‖CFC.sqrt M ⊗ₖ (1 : Matrix κ κ ℂ)‖ ≤ 1 ∧
      (CFC.sqrt (1 - M) ⊗ₖ (1 : Matrix κ κ ℂ)) * (CFC.sqrt (1 - M) ⊗ₖ 1) +
        (CFC.sqrt M ⊗ₖ (1 : Matrix κ κ ℂ)) * (CFC.sqrt M ⊗ₖ 1) = 1 := by
  have h1 : CFC.sqrt (1 - M) ≤ 1 := by
    simpa using CFC.sqrt_le_sqrt (1 - M) 1 (by simpa using hM.1)
  have h2 : CFC.sqrt M ≤ 1 := by simpa using CFC.sqrt_le_sqrt M 1 hM.2
  refine ⟨(l2_opNorm_kronecker_one_le _).trans
      (l2_opNorm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) h1),
    (l2_opNorm_kronecker_one_le _).trans
      (l2_opNorm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) h2),
    kronecker_one_mul_add ?_⟩
  rw [CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hM.2), CFC.sqrt_mul_sqrt_self _ hM.1,
    sub_add_cancel]

/-- D10.2. `𝓔_i` is linear. -/
theorem chan_sub (k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (B B' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    chan k (B - B') = chan k B - chan k B' := by
  simp only [chan, rootChannel, Matrix.mul_sub, Matrix.sub_mul]; abel

/-- D4.10.5. `𝓔_i` is an operator-norm contraction. -/
theorem norm_chan_le {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk : 0 ≤ k ∧ k ≤ 1)
    (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) : ‖chan k B‖ ≤ ‖B‖ :=
  (rootChannel_props (sqrt_kronecker_one_nonneg (sub_nonneg.mpr hk.2))
    (sqrt_kronecker_one_nonneg hk.1) (root_data hk).2.2).2.2 B

/-- D4.10.4. `𝓔_i` is unital. -/
theorem chan_one {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk : 0 ≤ k ∧ k ≤ 1) :
    chan k (1 : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) = 1 :=
  rootChannel_eq_self_of_commute (root_data hk).2.2 (Commute.one_right _) (Commute.one_right _)

theorem chanL_sub (a : σ) (l : ℕ) (k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (B B' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    chanL G a l k (B - B') = chanL G a l k B - chanL G a l k B' :=
  chan_sub _ B B'

theorem norm_chanL_le {a : σ} {l : ℕ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hE : 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    ‖chanL G a l k B‖ ≤ ‖B‖ :=
  norm_chan_le hE B

theorem shell_sub (a : σ) (l : ℕ) (k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ)
    (B B' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    shell G a l k (B - B') = shell G a l k B - shell G a l k B' := by
  simp only [shell, chanL_sub]
  split_ifs <;> abel

/-- D10.2.1. If `k_i Ω = 0` then `𝓔_i(C)(Ω ⊗ ξ) = G_i C (Ω ⊗ ξ)`. -/
theorem step_10_2_1 {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk : 0 ≤ k ∧ k ≤ 1)
    {Ω : Reg loc Λ → ℂ} (hkΩ : k *ᵥ Ω = 0) :
    ∀ (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) (ξ : κ → ℂ),
      chan k B *ᵥ tensVec Ω ξ =
        (CFC.sqrt (1 - k) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ (B *ᵥ tensVec Ω ξ) := by
  intro B ξ
  -- D4.10.2: `G_i Ω = Ω`, `K_i Ω = 0`
  have hG2 : (CFC.sqrt (1 - k) * CFC.sqrt (1 - k)) *ᵥ Ω = (((1 : ℝ) ^ 2 : ℝ) : ℂ) • Ω := by
    rw [CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hk.2), Matrix.sub_mulVec, hkΩ]; simp
  have hK2 : (CFC.sqrt k * CFC.sqrt k) *ᵥ Ω = (((0 : ℝ) ^ 2 : ℝ) : ℂ) • Ω := by
    rw [CFC.sqrt_mul_sqrt_self k hk.1, hkΩ]; simp
  have hG : CFC.sqrt (1 - k) *ᵥ Ω = Ω := by
    simpa using mulVec_eq_smul_of_mul_self_mulVec (CFC.sqrt_nonneg (1 - k)) zero_le_one hG2
  have hK : CFC.sqrt k *ᵥ Ω = 0 := by
    simpa using mulVec_eq_smul_of_mul_self_mulVec (CFC.sqrt_nonneg k) le_rfl hK2
  have h0 : tensVec (0 : Reg loc Λ → ℂ) ξ = 0 := by funext p; simp [tensVec]
  simp only [chan, rootChannel, Matrix.add_mulVec, ← mulVec_mulVec,
    kronecker_one_mulVec_tensVec, hG, hK, h0, mulVec_zero, add_zero]

variable {C c α : ℝ}

/-- D4.10.3. `‖G_i - G_{i,l}‖ ≤ 2√C e^{-(c/2) l^α}`. -/
theorem norm_sqrt_sub_sqrt_E_le {a : σ} {l : ℕ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : 0 ≤ k ∧ k ≤ 1) (hE : 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1)
    (htail : ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α)) :
    ‖CFC.sqrt (1 - k) - CFC.sqrt (1 - E G Λ a l k)‖ ≤
      2 * √C * Real.exp (-(c / 2) * (l : ℝ) ^ α) := by
  have hG := CFC.norm_sqrt_sub_sqrt_le (sub_nonneg.mpr hk.2) (sub_nonneg.mpr hE.2)
  rw [sub_sub_sub_cancel_left, norm_sub_rev (E G Λ a l k) k] at hG
  have := sqrt_le_of_le_exp htail
  have : 0 ≤ √C * Real.exp (-(c / 2) * (l : ℝ) ^ α) := by positivity
  linarith

/-- D10.2.2 (D4.10.6). `‖𝓔_i - 𝓔_{i,l}‖_cb ≤ 4√C e^{-(c/2) l^α}`, spectators included. -/
theorem step_10_2_2 {a : σ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hk : 0 ≤ k ∧ k ≤ 1)
    (hE : ∀ l, 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α)) :
    ∀ (l : ℕ) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
      ‖chan k B - chanL G a l k B‖ ≤ 4 * √C * Real.exp (-(c / 2) * (l : ℝ) ^ α) * ‖B‖ := by
  intro l B
  have hK : ‖CFC.sqrt k - CFC.sqrt (E G Λ a l k)‖ ≤ √C * Real.exp (-(c / 2) * (l : ℝ) ^ α) :=
    (CFC.norm_sqrt_sub_sqrt_le hk.1 (hE l).1).trans (sqrt_le_of_le_exp (htail l))
  have hG : ‖CFC.sqrt (1 - k) - CFC.sqrt (1 - E G Λ a l k)‖ ≤
      √C * Real.exp (-(c / 2) * (l : ℝ) ^ α) := by
    have h := CFC.norm_sqrt_sub_sqrt_le (sub_nonneg.mpr hk.2) (sub_nonneg.mpr (hE l).2)
    rw [sub_sub_sub_cancel_left, norm_sub_rev (E G Λ a l k) k] at h
    exact h.trans (sqrt_le_of_le_exp (htail l))
  have hr := root_data (κ := κ) hk
  have hrl := root_data (κ := κ) (hE l)
  refine (norm_rootChannel_sub_le hr.1 hr.2.1 hrl.1 hrl.2.1 B).trans ?_
  rw [sub_kronecker_one, sub_kronecker_one]
  have h1 := l2_opNorm_kronecker_one_le (p := κ)
    (CFC.sqrt (1 - k) - CFC.sqrt (1 - E G Λ a l k))
  have h2 := l2_opNorm_kronecker_one_le (p := κ) (CFC.sqrt k - CFC.sqrt (E G Λ a l k))
  have hB := norm_nonneg B
  have : 0 ≤ √C * Real.exp (-(c / 2) * (l : ℝ) ^ α) := by positivity
  have h3 := add_le_add (h1.trans hG) (h2.trans hK)
  calc _ ≤ 2 * (√C * Real.exp (-(c / 2) * (l : ℝ) ^ α) +
        √C * Real.exp (-(c / 2) * (l : ℝ) ^ α)) * ‖B‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 zero_le_two) hB
    _ = _ := by ring

/-- `e^{-(c/2)(l-1)^α} ≤ e^{c/2} e^{-(c/2) l^α}`, from `l^α - (l-1)^α ≤ 1` (`0 ≤ α ≤ 1`). -/
theorem exp_le_exp_mul_exp (hc : 0 < c) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    Real.exp (-(c / 2) * (n : ℝ) ^ α) ≤
      Real.exp (c / 2) * Real.exp (-(c / 2) * ((n + 1 : ℕ) : ℝ) ^ α) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := Real.rpow_add_le_add_rpow (Nat.cast_nonneg n) zero_le_one hα.le hα1
  rw [Real.one_rpow] at h
  have := mul_le_mul_of_nonneg_left h (half_pos hc).le
  push_cast
  linarith

/-- D10.2.4. For `L ≥ |Λ|` (`N_L(a) = Γ`, the component of `a`): `E_{i,L} k_i = k_i`. -/
theorem step_10_2_4 [∀ i, Nonempty (loc i)] {a : σ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hc : 0 < c) (hα : 0 < α)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α)) :
    ∀ L, #Λ ≤ L → E G Λ a L k = k := by
  intro L hL
  -- D4.6.9: `k` is supported in the component `Γ = N_L(a)`
  have hsupp : IsSupportedOn (component_subset G Λ a) k :=
    isSupportedOn_component_of_tail G hc hα htail
  have hN : graphNbhd G Λ {a} L = component G Λ a := graphNbhd_eq_component G hL
  have key : ∀ (N : Finset σ) (h : N ⊆ Λ), N = component G Λ a → IsSupportedOn h k := by
    intro N h e; subst e; exact hsupp
  exact (eq_quasilocal_ce (G := G) Λ a L).2.2.2 k (key _ _ hN)

theorem chanL_of_card_le [∀ i, Nonempty (loc i)] {a : σ}
    {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} (hc : 0 < c) (hα : 0 < α)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α)) {L : ℕ}
    (hL : #Λ ≤ L) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    chanL G a L k B = chan k B := by
  rw [chanL, step_10_2_4 hc hα htail L hL]

/-- D10.2.3. (a) `‖Δ_{i,l}‖_cb ≤ C' e^{-(c/2) l^α}` for all `l ≥ 0`; (b) telescoping:
`𝓔_i = 𝓔_{i,m-1} + ∑_{l ≥ m} Δ_{i,l}` for every `m ≥ 0` (the sum is finite: `Δ_{i,l} = 0` for
`l > |Λ|`). -/
theorem step_10_2_3 [∀ i, Nonempty (loc i)] {a : σ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : 0 ≤ k ∧ k ≤ 1) (hE : ∀ l, 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α))
    (hc : 0 < c) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ (l : ℕ) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
      ‖shell G a l k B‖ ≤ shellConst C c * Real.exp (-(c / 2) * (l : ℝ) ^ α) * ‖B‖) ∧
    ∀ (m : ℕ) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
      chan k B = (if m = 0 then B else chanL G a (m - 1) k B) +
        ∑ l ∈ Finset.Ico m (#Λ + 1), shell G a l k B := by
  refine ⟨fun l B => ?_, fun m B => ?_⟩
  · have hB := norm_nonneg B
    rcases l with _ | n
    · -- `l = 0`: both maps are contractions
      have h : ‖chanL G a 0 k B - B‖ ≤ ‖B‖ + ‖B‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_chanL_le (hE 0) B) _)
      have h2 : 2 ≤ shellConst C c := le_add_of_nonneg_right (by positivity)
      have h3 : shell G a 0 k B = chanL G a 0 k B - B := by simp [shell]
      rw [h3, Nat.cast_zero, Real.zero_rpow hα.ne', mul_zero, Real.exp_zero, mul_one]
      calc _ ≤ ‖B‖ + ‖B‖ := h
        _ = 2 * ‖B‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 hB
    · have hs : shell G a (n + 1) k B = chanL G a (n + 1) k B - chanL G a n k B := by
        simp only [shell, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      have hs2 : chanL G a (n + 1) k B - chanL G a n k B =
          (chan k B - chanL G a n k B) - (chan k B - chanL G a (n + 1) k B) := by
        abel
      have h1 := step_10_2_2 (κ := κ) hk hE htail (n + 1) B
      have h2 := step_10_2_2 (κ := κ) hk hE htail n B
      set e := Real.exp (-(c / 2) * ((n + 1 : ℕ) : ℝ) ^ α)
      have h4 : 4 * √C * Real.exp (-(c / 2) * (n : ℝ) ^ α) * ‖B‖ ≤
          4 * √C * (Real.exp (c / 2) * e) * ‖B‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (exp_le_exp_mul_exp hc hα hα1 n) (by positivity)) hB
      have h5 : 4 * √C * (Real.exp (c / 2) * e) * ‖B‖ + 4 * √C * e * ‖B‖ ≤
          shellConst C c * e * ‖B‖ := by
        have h6 : 4 * √C * (Real.exp (c / 2) * e) * ‖B‖ + 4 * √C * e * ‖B‖ =
            (4 * √C * (1 + Real.exp (c / 2))) * (e * ‖B‖) := by ring
        have h7 : 4 * √C * (1 + Real.exp (c / 2)) ≤ shellConst C c :=
          le_add_of_nonneg_left zero_le_two
        rw [h6, mul_assoc (shellConst C c)]
        exact mul_le_mul_of_nonneg_right h7 (mul_nonneg (Real.exp_pos _).le hB)
      rw [hs, hs2]
      exact (norm_sub_le _ _).trans ((add_le_add (h2.trans h4) h1).trans h5)
  · -- D10.2.3 (b): telescoping, `𝓔_{i,L} = 𝓔_i` for `L ≥ |Λ|` (D10.2.4)
    set g : ℕ → Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ :=
      fun l => if l = 0 then B else chanL G a (l - 1) k B with hg
    have hsh : ∀ l, shell G a l k B = g (l + 1) - g l := fun l => by
      simp [shell, hg]
    simp only [hsh]
    by_cases hm : m ≤ #Λ + 1
    · rw [Finset.sum_Ico_sub g hm]
      have : g (#Λ + 1) = chan k B := by
        simp only [hg, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
        exact (chanL_of_card_le hc hα htail le_rfl B)
      rw [this]; abel
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero,
        if_neg (by omega)]
      exact (chanL_of_card_le hc hα htail (by omega) B).symm

end Channels

/-! ## D10.2.5 The oscillation `d_y` -/

section Oscillation

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ : Finset σ} {κ : Type} [Fintype κ] [DecidableEq κ]

/-- A site operator `U_y = U ⊗ I` has norm at most `‖U‖`. -/
theorem norm_site_le {y : σ} (hy : y ∈ Λ) (U : Matrix (Reg loc {y}) (Reg loc {y}) ℂ) :
    ‖extendId (Finset.singleton_subset_iff.2 hy) U ⊗ₖ (1 : Matrix κ κ ℂ)‖ ≤ ‖U‖ :=
  (l2_opNorm_kronecker_one_le _).trans (norm_extendId_le _ _)

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [DecidableEq σ] in
/-- `‖[V, B]‖ ≤ 2‖B‖` for a contraction `V`. -/
theorem norm_mul_sub_mul_le_two_mul {n : Type*} [Fintype n] [DecidableEq n] {V : Matrix n n ℂ}
    (hV : ‖V‖ ≤ 1) (B : Matrix n n ℂ) : ‖V * B - B * V‖ ≤ 2 * ‖B‖ := by
  have h1 : ‖V * B‖ ≤ ‖B‖ := (l2_opNorm_mul V B).trans
    (by simpa using mul_le_mul_of_nonneg_right hV (norm_nonneg B))
  have h2 : ‖B * V‖ ≤ ‖B‖ := (l2_opNorm_mul B V).trans
    (by simpa using mul_le_mul_of_nonneg_left hV (norm_nonneg B))
  exact (norm_sub_le _ _).trans (by linarith)

/-- D10.2.5. `d_y(B) ≤ r` as soon as every `‖[U_y, B]‖ ≤ r`, `‖U‖ ≤ 1`, and `r ≥ 0`. -/
theorem osc_le_of_forall {y : σ} {B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ} {r : ℝ}
    (h : ∀ (hy : y ∈ Λ) (U : Matrix (Reg loc {y}) (Reg loc {y}) ℂ), ‖U‖ ≤ 1 →
      ‖(extendId (Finset.singleton_subset_iff.2 hy) U ⊗ₖ (1 : Matrix κ κ ℂ)) * B -
        B * (extendId (Finset.singleton_subset_iff.2 hy) U ⊗ₖ (1 : Matrix κ κ ℂ))‖ ≤ r)
    (hr : 0 ≤ r) : osc κ y B ≤ r := by
  unfold osc
  split_ifs with hy
  · have : Nonempty {U : Matrix (Reg loc {y}) (Reg loc {y}) ℂ // ‖U‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
    exact ciSup_le fun U => h hy U.1 U.2
  · exact hr

/-- D10.2.5. `d_y ≥ 0`. -/
theorem osc_nonneg (y : σ) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) : 0 ≤ osc κ y B := by
  unfold osc
  split_ifs
  · exact Real.iSup_nonneg fun _ => norm_nonneg _
  · exact le_rfl

/-- D10.2.5. `d_y(B) ≤ 2‖B‖`. -/
theorem osc_le (y : σ) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    osc κ y B ≤ 2 * ‖B‖ :=
  osc_le_of_forall (fun hy U hU => norm_mul_sub_mul_le_two_mul ((norm_site_le hy U).trans hU) B)
    (by positivity)

/-- D10.2.5. `‖[U_y, B]‖ ≤ d_y(B)` for every contraction `U` at `y ∈ Λ`. -/
theorem norm_commutator_le_osc {y : σ} (hy : y ∈ Λ) {U : Matrix (Reg loc {y}) (Reg loc {y}) ℂ}
    (hU : ‖U‖ ≤ 1) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    ‖(extendId (Finset.singleton_subset_iff.2 hy) U ⊗ₖ (1 : Matrix κ κ ℂ)) * B -
      B * (extendId (Finset.singleton_subset_iff.2 hy) U ⊗ₖ (1 : Matrix κ κ ℂ))‖ ≤
      osc κ y B := by
  rw [osc, dif_pos hy]
  refine le_ciSup (f := fun U : {U : Matrix (Reg loc {y}) (Reg loc {y}) ℂ // ‖U‖ ≤ 1} =>
    ‖(extendId (Finset.singleton_subset_iff.2 hy) U.1 ⊗ₖ (1 : Matrix κ κ ℂ)) * B -
      B * (extendId (Finset.singleton_subset_iff.2 hy) U.1 ⊗ₖ (1 : Matrix κ κ ℂ))‖)
    ⟨2 * ‖B‖, ?_⟩ ⟨U, hU⟩
  rintro _ ⟨V, rfl⟩
  exact norm_mul_sub_mul_le_two_mul ((norm_site_le hy V.1).trans V.2) B

/-- D10.2.5. `d_y(B) = 0` if `B` commutes with all operators at `y`. -/
theorem osc_eq_zero_of_commute {y : σ} {B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ}
    (h : ∀ (hy : y ∈ Λ) (U : Matrix (Reg loc {y}) (Reg loc {y}) ℂ),
      Commute (extendId (Finset.singleton_subset_iff.2 hy) U ⊗ₖ (1 : Matrix κ κ ℂ)) B) :
    osc κ y B = 0 :=
  le_antisymm (osc_le_of_forall (fun hy U _ => by rw [(h hy U).eq, sub_self, norm_zero])
    le_rfl) (osc_nonneg y B)

/-- D10.2.5. An operator supported on `S ∪` spectators (it commutes with every operator on
`Λ \ S`) has `d_y = 0` for `y ∉ S`. -/
theorem osc_eq_zero_of_support {S : Finset σ} {B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ}
    (hB : ∀ A : Matrix (Reg loc (Λ \ S)) (Reg loc (Λ \ S)) ℂ,
      Commute (extendId (Finset.sdiff_subset : Λ \ S ⊆ Λ) A ⊗ₖ (1 : Matrix κ κ ℂ)) B)
    {y : σ} (hyS : y ∉ S) : osc κ y B = 0 := by
  refine osc_eq_zero_of_commute fun hy U => ?_
  have hyΛS : ({y} : Finset σ) ⊆ Λ \ S :=
    Finset.singleton_subset_iff.2 (Finset.mem_sdiff.2 ⟨hy, hyS⟩)
  have h := hB (extendId hyΛS U)
  rwa [Arealaw.extendId_extendId] at h

/-- `d_y(X) ≤ d_y(X') + 2‖X - X'‖`. -/
theorem osc_le_osc_add (y : σ) (X X' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    osc κ y X ≤ osc κ y X' + 2 * ‖X - X'‖ := by
  refine osc_le_of_forall (fun hy U hU => ?_) (add_nonneg (osc_nonneg y X') (by positivity))
  set V := extendId (Finset.singleton_subset_iff.2 hy) U ⊗ₖ (1 : Matrix κ κ ℂ)
  have hd : V * X - X * V = (V * X' - X' * V) + (V * (X - X') - (X - X') * V) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [hd]
  exact (norm_add_le _ _).trans (add_le_add (norm_commutator_le_osc hy hU X')
    (norm_mul_sub_mul_le_two_mul ((norm_site_le hy U).trans hU) _))

end Oscillation

/-! ## D10.2.6 Single-site twirls and the commutant of a region -/

section Twirl

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ : Finset σ} {κ : Type} [Fintype κ] [DecidableEq κ]

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [Fintype κ] [DecidableEq κ] in
/-- If `P(e ·, e ·)` and `Q(e ·, e ·)` commute, so do `P` and `Q`. -/
theorem commute_of_commute_submatrix {α β : Type*} [Fintype α] [Fintype β]
    {P Q : Matrix β β ℂ} (e : α ≃ β) (h : Commute (P.submatrix e e) (Q.submatrix e e)) :
    Commute P Q := by
  have h' : (P * Q).submatrix e e = (Q * P).submatrix e e := by
    rw [← submatrix_mul_equiv P Q e e e, ← submatrix_mul_equiv Q P e e e]; exact h.eq
  ext i j
  simpa using congrFun (congrFun h' (e.symm i)) (e.symm j)

/-- `(X ⊗ I) (Y ⊗ I) = XY ⊗ I` for extensions of site operators. -/
theorem extendId_kronecker_mul {S : Finset σ} (h : S ⊆ Λ) (A B : Matrix (Reg loc S) (Reg loc S) ℂ) :
    (extendId h A ⊗ₖ (1 : Matrix κ κ ℂ)) * (extendId h B ⊗ₖ (1 : Matrix κ κ ℂ)) =
      extendId h (A * B) ⊗ₖ (1 : Matrix κ κ ℂ) := by
  rw [← mul_kronecker_mul, Matrix.mul_one, extendId_mul]

/-- Operators at disjoint sets of sites commute, spectators included. -/
theorem commute_extendId_kronecker {S U : Finset σ} (hS : S ⊆ Λ) (hU : U ⊆ Λ)
    (hd : Disjoint S U) (A : Matrix (Reg loc S) (Reg loc S) ℂ)
    (B : Matrix (Reg loc U) (Reg loc U) ℂ) :
    Commute (extendId hS A ⊗ₖ (1 : Matrix κ κ ℂ)) (extendId hU B ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  rw [Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul,
    (commute_extendId_extendId hS hU hd A B).eq]

/-- The coordinates `((Λ \ {z}) × κ) × {z}` of `Reg loc Λ × κ`. -/
def siteEquiv {z : σ} (hz : z ∈ Λ) :
    (Reg loc (Λ \ {z}) × κ) × Reg loc {z} ≃ Reg loc Λ × κ :=
  (Equiv.prodComm _ _).trans ((Equiv.prodAssoc _ _ _).symm.trans
    ((glueEquiv (Finset.singleton_subset_iff.2 hz)).prodCongr (Equiv.refl κ)))

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [Fintype κ] [DecidableEq κ] in
theorem siteEquiv_apply {z : σ} (hz : z ∈ Λ) (r : Reg loc (Λ \ {z})) (s : κ)
    (x : Reg loc {z}) : siteEquiv hz ((r, s), x) = (glue x r, s) := rfl

omit [Fintype κ] [∀ i, Fintype (loc i)] in
/-- In the coordinates `siteEquiv`, `U_z = I ⊗ U`. -/
theorem site_submatrix {z : σ} (hz : z ∈ Λ) (W : Matrix (Reg loc {z}) (Reg loc {z}) ℂ) :
    (extendId (Finset.singleton_subset_iff.2 hz) W ⊗ₖ (1 : Matrix κ κ ℂ)).submatrix
        (siteEquiv hz) (siteEquiv hz) =
      (1 : Matrix (Reg loc (Λ \ {z}) × κ) (Reg loc (Λ \ {z}) × κ) ℂ) ⊗ₖ W := by
  ext ⟨⟨r, s⟩, x⟩ ⟨⟨r', s'⟩, x'⟩
  simp only [submatrix_apply, siteEquiv_apply, kroneckerMap_apply, extendId_apply_glue,
    one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- D10.2.6. The twirl `𝒯_z(X) = d_z⁻² ∑_{a,b} W_{ab} X W_{ab}^*` over the Weyl operators at
`z`: `‖X - 𝒯_z X‖ ≤ d_z(X)`; `𝒯_z X` commutes with every operator at `z`; `𝒯_z` does not
increase `d_y`, `y ≠ z`, and keeps commuting with the operators at `y ≠ z`. -/
theorem exists_siteTwirl [∀ i, Nonempty (loc i)] {z : σ} (hz : z ∈ Λ)
    (X : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    ∃ X' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ, ‖X - X'‖ ≤ osc κ z X ∧
      (∀ A : Matrix (Reg loc {z}) (Reg loc {z}) ℂ,
        Commute (extendId (Finset.singleton_subset_iff.2 hz) A ⊗ₖ (1 : Matrix κ κ ℂ)) X') ∧
      (∀ y, y ≠ z → osc κ y X' ≤ osc κ y X) ∧
      ∀ y (hy : y ∈ Λ), y ≠ z → ∀ A : Matrix (Reg loc {y}) (Reg loc {y}) ℂ,
        Commute (extendId (Finset.singleton_subset_iff.2 hy) A ⊗ₖ (1 : Matrix κ κ ℂ)) X →
        Commute (extendId (Finset.singleton_subset_iff.2 hy) A ⊗ₖ (1 : Matrix κ κ ℂ)) X' := by
  set d := Fintype.card (Reg loc {z})
  have : NeZero d := ⟨Fintype.card_ne_zero⟩
  set e₀ : Reg loc {z} ≃ ZMod d := (Fintype.equivFin _).trans (ZMod.finEquiv d).toEquiv
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
  have hζ : IsPrimitiveRoot ζ d := Complex.isPrimitiveRoot_exp _ (NeZero.ne d)
  have hz' := Finset.singleton_subset_iff.2 hz
  set U : ZMod d → ZMod d → Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ :=
    fun a b => extendId hz' (Matrix.reindexedWeyl e₀ ζ a b) ⊗ₖ (1 : Matrix κ κ ℂ) with hUdef
  have hWu := fun a b => Matrix.reindexedWeyl_mem_unitary e₀ hζ a b
  have hW1 : ∀ a b, ‖Matrix.reindexedWeyl e₀ ζ a b‖ ≤ 1 := fun a b =>
    (CStarRing.norm_of_mem_unitary (hWu a b)).le
  have hUstar : ∀ a b, (U a b)ᴴ =
      extendId hz' (Matrix.reindexedWeyl e₀ ζ a b)ᴴ ⊗ₖ (1 : Matrix κ κ ℂ) := fun a b => by
    rw [hUdef, conjTranspose_kronecker, conjTranspose_one, extendId_conjTranspose]
  have hUU : ∀ a b, U a b * (U a b)ᴴ = 1 := fun a b => by
    rw [hUstar, hUdef, extendId_kronecker_mul, ← star_eq_conjTranspose,
      Unitary.mul_star_self_of_mem (hWu a b), extendId_one, one_kronecker_one]
  have hUn : ∀ a b, ‖U a b‖ ≤ 1 := fun a b => (norm_site_le hz _).trans (hW1 a b)
  have hUsn : ∀ a b, ‖(U a b)ᴴ‖ ≤ 1 := fun a b => by
    rw [hUstar]
    exact (norm_site_le hz _).trans (by rw [← star_eq_conjTranspose, norm_star]; exact hW1 a b)
  set c : ℂ := ((d : ℂ) ^ 2)⁻¹
  set T : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ → Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ :=
    fun Y => c • ∑ a, ∑ b, U a b * Y * (U a b)ᴴ with hT
  have hc : ‖c‖ * ((d : ℝ) * d) = 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast, ← sq,
      inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast NeZero.ne d))]
  -- contractivity
  have hTn : ∀ Y, ‖T Y‖ ≤ ‖Y‖ := fun Y => by
    have hterm : ∀ a b, ‖U a b * Y * (U a b)ᴴ‖ ≤ ‖Y‖ := fun a b =>
      (l2_opNorm_mul _ _).trans (by
        have h1 := (l2_opNorm_mul (U a b) Y).trans
          (mul_le_mul_of_nonneg_right (hUn a b) (norm_nonneg Y))
        have h2 := mul_le_mul h1 (hUsn a b) (norm_nonneg _) (by positivity)
        simpa using h2)
    rw [hT, norm_smul]
    calc ‖c‖ * ‖∑ a, ∑ b, U a b * Y * (U a b)ᴴ‖ ≤ ‖c‖ * ∑ _a : ZMod d, ∑ _b : ZMod d, ‖Y‖ :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hterm a b))) (norm_nonneg _)
      _ = (‖c‖ * ((d : ℝ) * d)) * ‖Y‖ := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
      _ = ‖Y‖ := by rw [hc, one_mul]
  -- `T` commutes with commutators by operators commuting with every `W_{ab}`, `W_{ab}^*`
  have hTc : ∀ V Y, (∀ a b, Commute V (U a b) ∧ Commute V (U a b)ᴴ) →
      T (V * Y - Y * V) = V * T Y - T Y * V := fun V Y hV => by
    have hterm : ∀ a b, U a b * (V * Y - Y * V) * (U a b)ᴴ =
        V * (U a b * Y * (U a b)ᴴ) - U a b * Y * (U a b)ᴴ * V := fun a b => by
      have e1 := (hV a b).1.eq
      have e2 := (hV a b).2.eq
      calc U a b * (V * Y - Y * V) * (U a b)ᴴ =
            (U a b * V) * Y * (U a b)ᴴ - U a b * Y * (V * (U a b)ᴴ) := by noncomm_ring
        _ = (V * U a b) * Y * (U a b)ᴴ - U a b * Y * ((U a b)ᴴ * V) := by rw [e1, e2]
        _ = _ := by noncomm_ring
    simp only [hT, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, smul_sub,
      Matrix.mul_smul, Matrix.smul_mul]
  -- in the coordinates `siteEquiv`, `T` is the complementary Weyl twirl
  have hTe : ∀ Y, (T Y).submatrix (siteEquiv hz) (siteEquiv hz) =
      ((d : ℂ)⁻¹ • (Y.submatrix (siteEquiv hz) (siteEquiv hz)).traceRight) ⊗ₖ
        (1 : Matrix (Reg loc {z}) (Reg loc {z}) ℂ) := fun Y => by
    rw [← Matrix.complementaryWeylTwirl_eq_smul_traceRight_kronecker_one e₀ hζ,
      Matrix.complementaryWeylTwirl]
    have key : ∀ a b, ((1 : Matrix (Reg loc (Λ \ {z}) × κ) (Reg loc (Λ \ {z}) × κ) ℂ) ⊗ₖ
        Matrix.reindexedWeyl e₀ ζ a b) * Y.submatrix (siteEquiv hz) (siteEquiv hz) *
        ((1 : Matrix (Reg loc (Λ \ {z}) × κ) (Reg loc (Λ \ {z}) × κ) ℂ) ⊗ₖ
        Matrix.reindexedWeyl e₀ ζ a b)ᴴ =
        (U a b * Y * (U a b)ᴴ).submatrix (siteEquiv hz) (siteEquiv hz) := fun a b => by
      rw [← site_submatrix hz, conjTranspose_submatrix, submatrix_mul_equiv,
        submatrix_mul_equiv]
    simp only [key]
    ext i j
    simp [hT, Matrix.sum_apply, c]
  refine ⟨T X, ?_, fun A => ?_, fun y hy => ?_, fun y hy hyz A hA => ?_⟩
  · -- `‖X - 𝒯_z X‖ ≤ d_z(X)`
    have hterm : ∀ a b, ‖X - U a b * X * (U a b)ᴴ‖ ≤ osc κ z X := fun a b => by
      have heq : X - U a b * X * (U a b)ᴴ = (X * U a b - U a b * X) * (U a b)ᴴ := by
        rw [Matrix.sub_mul, Matrix.mul_assoc X, hUU, Matrix.mul_one]
      rw [heq, ← norm_neg, ← neg_mul, neg_sub]
      exact (l2_opNorm_mul _ _).trans ((mul_le_mul_of_nonneg_left (hUsn a b)
        (norm_nonneg _)).trans (by rw [mul_one]; exact norm_commutator_le_osc hz (hW1 a b) X))
    have hdiff : X - T X = c • ∑ a, ∑ b, (X - U a b * X * (U a b)ᴴ) := by
      simp_rw [Finset.sum_sub_distrib, smul_sub]
      rw [Matrix.inv_sq_smul_sum_sum_const]
    rw [hdiff, norm_smul]
    calc ‖c‖ * ‖∑ a, ∑ b, (X - U a b * X * (U a b)ᴴ)‖ ≤
          ‖c‖ * ∑ _a : ZMod d, ∑ _b : ZMod d, osc κ z X :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hterm a b))) (norm_nonneg _)
      _ = (‖c‖ * ((d : ℝ) * d)) * osc κ z X := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
      _ = _ := by rw [hc, one_mul]
  · -- `𝒯_z X` commutes with the operators at `z` (Weyl completeness)
    refine commute_of_commute_submatrix (siteEquiv hz) ?_
    rw [site_submatrix hz, hTe, Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  · -- `d_y(𝒯_z X) ≤ d_y(X)` for `y ≠ z`
    refine osc_le_of_forall (fun hyΛ V hV => ?_) (osc_nonneg y X)
    have hcomm : ∀ a b, Commute (extendId (Finset.singleton_subset_iff.2 hyΛ) V ⊗ₖ
        (1 : Matrix κ κ ℂ)) (U a b) ∧ Commute (extendId (Finset.singleton_subset_iff.2 hyΛ) V ⊗ₖ
        (1 : Matrix κ κ ℂ)) (U a b)ᴴ := fun a b => by
      have hd : Disjoint ({y} : Finset σ) {z} := Finset.disjoint_singleton.2 hy
      rw [hUstar]
      exact ⟨commute_extendId_kronecker _ _ hd _ _, commute_extendId_kronecker _ _ hd _ _⟩
    rw [← hTc _ _ hcomm]
    exact (hTn _).trans (norm_commutator_le_osc hyΛ hV X)
  · -- `𝒯_z` keeps commuting with the operators at `y ≠ z`
    have hd : Disjoint ({y} : Finset σ) {z} := Finset.disjoint_singleton.2 hyz
    have hcomm : ∀ a b, Commute (extendId (Finset.singleton_subset_iff.2 hy) A ⊗ₖ
        (1 : Matrix κ κ ℂ)) (U a b) ∧ Commute (extendId (Finset.singleton_subset_iff.2 hy) A ⊗ₖ
        (1 : Matrix κ κ ℂ)) (U a b)ᴴ := fun a b => by
      rw [hUstar]
      exact ⟨commute_extendId_kronecker _ _ hd _ _, commute_extendId_kronecker _ _ hd _ _⟩
    have h0 := hTc _ X hcomm
    rw [hA.eq, sub_self] at h0
    have hT0 : T 0 = 0 := by simp [hT]
    rw [hT0] at h0
    exact (sub_eq_zero.1 h0.symm)

end Twirl

/-! ## The commutant of the single-site algebras of a region -/

section Generation

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {T : Finset σ} {κ : Type} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
/-- Matrix-unit decomposition along a disjoint union `S ∪ U ⊆ T`:
`A ⊗ I = ∑_{x,x'} (|x⟩⟨x'| ⊗ I) (A_{x x'} ⊗ I)`, `A_{x x'}` the `(x, x')` block of `A`. -/
theorem extendId_union_eq_sum {S U : Finset σ} (hd : Disjoint S U) (hS : S ⊆ T) (hU : U ⊆ T)
    (hSU : S ∪ U ⊆ T) (A : Matrix (Reg loc (S ∪ U)) (Reg loc (S ∪ U)) ℂ) :
    extendId hSU A = ∑ x : Reg loc S, ∑ x' : Reg loc S,
      extendId hS (Matrix.single x x' 1) * extendId hU (Matrix.of fun u u' =>
        A ((unionEquiv hd).symm (x, u)) ((unionEquiv hd).symm (x', u'))) := by
  ext w w'
  have hw : ∀ v : Reg loc T, (unionEquiv hd).symm (restr hS v, restr hU v) = restr hSU v :=
    fun v => (unionEquiv hd).symm_apply_eq.2 rfl
  have hcond : restr (S := T \ (S ∪ U)) Finset.sdiff_subset w =
      restr (S := T \ (S ∪ U)) Finset.sdiff_subset w' ↔
      ∀ i : T, i.1 ∉ S → i.1 ∉ U → w i = w' i := by
    refine ⟨fun h i hiS hiU => congrFun h ⟨i, Finset.mem_sdiff.2 ⟨i.2, by simp [hiS, hiU]⟩⟩,
      fun h => funext fun j => ?_⟩
    have hj := (Finset.mem_sdiff.1 j.2).2
    simp only [Finset.mem_union, not_or] at hj
    exact h ⟨j, (Finset.mem_sdiff.1 j.2).1⟩ hj.1 hj.2
  simp only [Matrix.sum_apply, extendId_mul_extendId_apply hS hU hd]
  by_cases hc : ∀ i : T, i.1 ∉ S → i.1 ∉ U → w i = w' i
  · simp only [if_pos hc, Matrix.single_apply, ite_and, ite_mul, one_mul, zero_mul]
    simp [extendId, hcond.2 hc, hw, -unionEquiv_symm_apply]
  · simp only [if_neg hc, Finset.sum_const_zero]
    simp [extendId, mt hcond.1 hc]

/-- An operator commuting with all operators of `S` and all operators of `U` (disjoint)
commutes with all operators of `S ∪ U`, spectators untouched. -/
theorem commute_extendId_union {S U : Finset σ} (hd : Disjoint S U) (hS : S ⊆ T) (hU : U ⊆ T)
    {M : Matrix (Reg loc T × κ) (Reg loc T × κ) ℂ}
    (h₁ : ∀ A, Commute (extendId hS A ⊗ₖ (1 : Matrix κ κ ℂ)) M)
    (h₂ : ∀ A, Commute (extendId hU A ⊗ₖ (1 : Matrix κ κ ℂ)) M) (hSU : S ∪ U ⊆ T)
    (A : Matrix (Reg loc (S ∪ U)) (Reg loc (S ∪ U)) ℂ) :
    Commute (extendId hSU A ⊗ₖ (1 : Matrix κ κ ℂ)) M := by
  have hadd : ∀ X Y : Matrix (Reg loc T) (Reg loc T) ℂ, Commute (X ⊗ₖ (1 : Matrix κ κ ℂ)) M →
      Commute (Y ⊗ₖ (1 : Matrix κ κ ℂ)) M → Commute ((X + Y) ⊗ₖ (1 : Matrix κ κ ℂ)) M :=
    fun X Y hX hY => by rw [add_kronecker]; exact hX.add_left hY
  have h0 : Commute ((0 : Matrix (Reg loc T) (Reg loc T) ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) M := by
    rw [zero_kronecker]; exact Commute.zero_left M
  rw [extendId_union_eq_sum hd hS hU hSU]
  refine Finset.sum_induction _ (fun X => Commute (X ⊗ₖ (1 : Matrix κ κ ℂ)) M) hadd h0
    (fun x _ => Finset.sum_induction _ (fun X => Commute (X ⊗ₖ (1 : Matrix κ κ ℂ)) M) hadd h0
      (fun x' _ => ?_))
  rw [← Matrix.mul_one (1 : Matrix κ κ ℂ), mul_kronecker_mul]
  exact (h₁ _).mul_left (h₂ _)

/-- D10.2.6. An operator commuting with every single-site operator at every site of `Q`
commutes with every operator on `Q`, spectators untouched. -/
theorem commute_extendId_of_forall_site {M : Matrix (Reg loc T × κ) (Reg loc T × κ) ℂ} :
    ∀ Q : Finset σ, (∀ z (hz : z ∈ T), z ∈ Q → ∀ A : Matrix (Reg loc {z}) (Reg loc {z}) ℂ,
      Commute (extendId (Finset.singleton_subset_iff.2 hz) A ⊗ₖ (1 : Matrix κ κ ℂ)) M) →
    ∀ (hQ : Q ⊆ T) (A : Matrix (Reg loc Q) (Reg loc Q) ℂ),
      Commute (extendId hQ A ⊗ₖ (1 : Matrix κ κ ℂ)) M := by
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    intro _ hQ A
    have hsub : ∀ i j : Reg loc (∅ : Finset σ), i = j := fun i j =>
      funext fun x => absurd x.2 (Finset.notMem_empty _)
    obtain ⟨x₀⟩ : Nonempty (Reg loc (∅ : Finset σ)) :=
      ⟨fun x => absurd x.2 (Finset.notMem_empty _)⟩
    have hA : A = A x₀ x₀ • (1 : Matrix (Reg loc (∅ : Finset σ)) (Reg loc ∅) ℂ) := by
      ext i j
      rw [hsub i x₀, hsub j x₀]; simp
    rw [hA, extendId_smul, extendId_one, smul_kronecker, one_kronecker_one]
    exact (Commute.one_left M).smul_left _
  | insert z Q hzQ ih =>
    intro h
    rw [Finset.insert_eq]
    intro hQ A
    have hz : z ∈ T := hQ (Finset.mem_union_left _ (Finset.mem_singleton_self z))
    exact commute_extendId_union (Finset.disjoint_singleton_left.2 hzQ)
      (Finset.singleton_subset_iff.2 hz) (Finset.union_subset_right hQ)
      (fun A => h z hz (Finset.mem_insert_self z Q) A)
      (ih (fun z' hz' hmem => h z' hz' (Finset.mem_insert_of_mem hmem))
        (Finset.union_subset_right hQ)) hQ A

end Generation

/-! ## D10.2.6, D10.2.7, D10.2.10: shells against oscillations -/

section Shells

variable {σ : Type*} [DecidableEq σ] {G : SimpleGraph σ} {loc : σ → Type}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] {Λ : Finset σ} {κ : Type} [Fintype κ]
  [DecidableEq κ] {C c α : ℝ}

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
theorem graphNbhd_mono {S : Finset σ} {l l' : ℕ} (h : l ≤ l') :
    graphNbhd G Λ S l ⊆ graphNbhd G Λ S l' := fun x hx => by
  simp only [graphNbhd, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans (by exact_mod_cast h)⟩

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
/-- If `G`, `K` commute with `V`, so does `𝓔 = G · G + K · K` with the commutator by `V`. -/
theorem rootChannel_commutator {n : Type*} [Fintype n] {Gm K V B : Matrix n n ℂ}
    (hG : Commute Gm V) (hK : Commute K V) :
    rootChannel Gm K (V * B - B * V) = V * rootChannel Gm K B - rootChannel Gm K B * V := by
  have e1 : Gm * V * B * Gm = V * Gm * B * Gm := by rw [hG.eq]
  have e2 : Gm * B * (V * Gm) = Gm * B * Gm * V := by rw [← hG.eq]; noncomm_ring
  have e3 : K * V * B * K = V * K * B * K := by rw [hK.eq]
  have e4 : K * B * (V * K) = K * B * K * V := by rw [← hK.eq]; noncomm_ring
  calc rootChannel Gm K (V * B - B * V)
      = Gm * V * B * Gm - Gm * B * (V * Gm) + (K * V * B * K - K * B * (V * K)) := by
        simp only [rootChannel]; noncomm_ring
    _ = V * Gm * B * Gm - Gm * B * Gm * V + (V * K * B * K - K * B * K * V) := by
        rw [e1, e2, e3, e4]
    _ = _ := by simp only [rootChannel]; noncomm_ring

/-- D10.2.7. `𝓔_{i,l}` has support `N_l(a_i)`: for `y ∉ N_l(a_i)` it does not increase `d_y`. -/
theorem osc_chanL_le {a : σ} {l : ℕ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hE : 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1) {y : σ} (hy : y ∉ graphNbhd G Λ {a} l)
    (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    osc κ y (chanL G a l k B) ≤ osc κ y B := by
  refine osc_le_of_forall (fun hyΛ U hU => ?_) (osc_nonneg y B)
  set V := extendId (Finset.singleton_subset_iff.2 hyΛ) U ⊗ₖ (1 : Matrix κ κ ℂ)
  obtain ⟨A₀, hA₀⟩ := isSupportedOn_E (G := G) Λ a l k
  have hk : Commute (E G Λ a l k ⊗ₖ (1 : Matrix κ κ ℂ)) V := by
    rw [hA₀]
    exact commute_extendId_kronecker _ _ (Finset.disjoint_singleton_right.2 hy) _ _
  have h1 : Commute ((1 - E G Λ a l k) ⊗ₖ (1 : Matrix κ κ ℂ)) V := by
    rw [← sub_kronecker_one, one_kronecker_one]; exact (Commute.one_left V).sub_left hk
  have hc := rootChannel_commutator (B := B) (commute_sqrt_kronecker_one (sub_nonneg.mpr hE.2) h1)
    (commute_sqrt_kronecker_one hE.1 hk)
  rw [chanL, chan, ← hc]
  exact (norm_chan_le hE _).trans (norm_commutator_le_osc hyΛ hU B)

/-- D10.2.6 (fixed points, D4.10.7). `𝓔_{i,l}` fixes every operator commuting with the
algebra on `N_l(a_i)`, spectators included. -/
theorem chanL_eq_self_of_commute {a : σ} {l : ℕ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hE : 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1) {B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ}
    (hB : ∀ A, Commute (extendId (graphNbhd_subset G Λ {a} l) A ⊗ₖ (1 : Matrix κ κ ℂ)) B) :
    chanL G a l k B = B := by
  obtain ⟨A₀, hA₀⟩ := isSupportedOn_E (G := G) Λ a l k
  have hk : Commute (E G Λ a l k ⊗ₖ (1 : Matrix κ κ ℂ)) B := hA₀ ▸ hB A₀
  have hone : Commute ((1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) B := by
    have h := hB 1
    rwa [extendId_one] at h
  have h1' : Commute ((1 - E G Λ a l k) ⊗ₖ (1 : Matrix κ κ ℂ)) B := by
    rw [← sub_kronecker_one]; exact hone.sub_left hk
  exact rootChannel_eq_self_of_commute (root_data hE).2.2
    (commute_sqrt_kronecker_one (sub_nonneg.mpr hE.2) h1')
    (commute_sqrt_kronecker_one hE.1 hk)

/-- D10.2.6. `Δ_{i,l}` vanishes on operators commuting with every single-site operator of
`N_l(a_i)`: both `𝓔_{i,l}` and `𝓔_{i,l-1}` fix them (`N_{l-1} ⊆ N_l`; `𝓔_{i,-1} = id`). -/
theorem shell_eq_zero_of_commute {a : σ} {l : ℕ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hE : ∀ l, 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1) {B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ}
    (hB : ∀ z (hz : z ∈ Λ), z ∈ graphNbhd G Λ {a} l → ∀ A : Matrix (Reg loc {z}) (Reg loc {z}) ℂ,
      Commute (extendId (Finset.singleton_subset_iff.2 hz) A ⊗ₖ (1 : Matrix κ κ ℂ)) B) :
    shell G a l k B = 0 := by
  have hl := chanL_eq_self_of_commute (hE l)
    (commute_extendId_of_forall_site _ hB (graphNbhd_subset G Λ {a} l))
  have hl' := chanL_eq_self_of_commute (hE (l - 1))
    (commute_extendId_of_forall_site _
      (fun z hz hmem => hB z hz (graphNbhd_mono (Nat.sub_le l 1) hmem))
      (graphNbhd_subset G Λ {a} (l - 1)))
  unfold shell
  split_ifs <;> simp [hl, hl']

variable [∀ i, Nonempty (loc i)]

/-- D10.2.6. Composing the twirls `𝒯_z` over `Q`: `B̂` commutes with every single-site
operator of `Q`, `‖B - B̂‖ ≤ ∑_{z ∈ Q} d_z(B)`, and `d_y(B̂) ≤ d_y(B)` off `Q`. -/
theorem exists_twirl (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) :
    ∀ Q : Finset σ, Q ⊆ Λ → ∃ B' : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ,
      ‖B - B'‖ ≤ ∑ z ∈ Q, osc κ z B ∧
      (∀ z (hz : z ∈ Λ), z ∈ Q → ∀ A : Matrix (Reg loc {z}) (Reg loc {z}) ℂ,
        Commute (extendId (Finset.singleton_subset_iff.2 hz) A ⊗ₖ (1 : Matrix κ κ ℂ)) B') ∧
      ∀ y ∉ Q, osc κ y B' ≤ osc κ y B := by
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨B, by simp, fun z _ h => absurd h (Finset.notMem_empty z), fun _ _ => le_rfl⟩
  | insert z Q hzQ ih =>
    intro hQ
    obtain ⟨B', h1, h2, h3⟩ := ih ((Finset.subset_insert z Q).trans hQ)
    have hz : z ∈ Λ := hQ (Finset.mem_insert_self z Q)
    obtain ⟨B'', t1, t2, t3, t4⟩ := exists_siteTwirl hz B'
    refine ⟨B'', ?_, fun z' hz' hmem A => ?_, fun y hy => ?_⟩
    · rw [Finset.sum_insert hzQ, add_comm]
      exact (norm_sub_le_norm_sub_add_norm_sub B B' B'').trans
        (add_le_add h1 (t1.trans (h3 z hzQ)))
    · rcases Finset.mem_insert.1 hmem with rfl | hmem'
      · exact t2 A
      · exact t4 z' hz' (fun h => hzQ (h ▸ hmem')) A (h2 z' hz' hmem' A)
    · rw [Finset.mem_insert, not_or] at hy
      exact (t3 y hy.1).trans (h3 y hy.2)

/-- D10.2.6 (eq:amplification-shell-oscillation).
`‖Δ_{i,l}(B)‖ ≤ C e^{-c l^α} ∑_{z ∈ N_l(a_i)} d_z(B)`. -/
theorem step_10_2_6 {a : σ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : 0 ≤ k ∧ k ≤ 1) (hE : ∀ l, 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α))
    (hc : 0 < c) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (l : ℕ) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
      ‖shell G a l k B‖ ≤ shellConst C c * Real.exp (-(c / 2) * (l : ℝ) ^ α) *
        ∑ z ∈ graphNbhd G Λ {a} l, osc κ z B := by
  intro l B
  -- `B̂ = 𝒯_{z_m} ⋯ 𝒯_{z_1} B` over `Q = N_l(a_i)`
  obtain ⟨B', h1, h2, -⟩ := exists_twirl B (graphNbhd G Λ {a} l) (graphNbhd_subset G Λ {a} l)
  -- `Δ_{i,l}` vanishes on the commutant of `N_l(a_i)`
  have h0 : shell G a l k B' = 0 := shell_eq_zero_of_commute hE h2
  -- `Δ_{i,l}(B) = Δ_{i,l}(B - B̂)`
  have hs : shell G a l k B = shell G a l k (B - B') := by rw [shell_sub, h0, sub_zero]
  rw [hs]
  exact ((step_10_2_3 hk hE htail hc hα hα1).1 l (B - B')).trans
    (mul_le_mul_of_nonneg_left h1 (mul_nonneg (shellConst_nonneg C c) (Real.exp_pos _).le))

/-- D10.2.7 (eq:amplification-oscillation-increment). With `m = d_Λ(a_i, y)`,
`d_y(𝓔_i B) ≤ d_y(B) + C ∑_{l ≥ m} e^{-c l^α} ∑_{z ∈ N_l(a_i)} d_z(B)`; `y ∈ N_l(a_i)` iff
`l ≥ m`, and for `m = ∞` (another component) `d_y` does not increase. -/
theorem step_10_2_7 {a : σ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : 0 ≤ k ∧ k ≤ 1) (hE : ∀ l, 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α))
    (hc : 0 < c) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (y : σ) (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ),
      osc κ y (chan k B) ≤ osc κ y B + 2 * shellConst C c *
        ∑ l ∈ Finset.range (#Λ + 1), (if y ∈ graphNbhd G Λ {a} l then
          Real.exp (-(c / 2) * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {a} l, osc κ z B else 0) := by
  intro y B
  set F : ℕ → ℝ := fun l => Real.exp (-(c / 2) * (l : ℝ) ^ α) *
    ∑ z ∈ graphNbhd G Λ {a} l, osc κ z B with hF
  have hF0 : ∀ l, 0 ≤ F l := fun l =>
    mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun z _ => osc_nonneg z B)
  have hsum0 : 0 ≤ ∑ l ∈ Finset.range (#Λ + 1),
      (if y ∈ graphNbhd G Λ {a} l then F l else 0) :=
    Finset.sum_nonneg fun l _ => by split_ifs <;> simp [hF0 l]
  have h2K : 0 ≤ 2 * shellConst C c := mul_nonneg zero_le_two (shellConst_nonneg C c)
  by_cases hex : ∃ l, y ∈ graphNbhd G Λ {a} l ∧ l ≤ #Λ
  · -- `m < ∞`: `𝓔_i = 𝓔_{i,m-1} + ∑_{l ≥ m} Δ_{i,l}` (D10.2.3)
    have hP : ∃ l, y ∈ graphNbhd G Λ {a} l := ⟨hex.choose, hex.choose_spec.1⟩
    set m := Nat.find hP
    have hm : y ∈ graphNbhd G Λ {a} m := Nat.find_spec hP
    have hmin : ∀ l < m, y ∉ graphNbhd G Λ {a} l := fun l hl => Nat.find_min hP hl
    have hmΛ : m ≤ #Λ := (Nat.find_min' hP hex.choose_spec.1).trans hex.choose_spec.2
    have hb := (step_10_2_3 (κ := κ) hk hE htail hc hα hα1).2 m B
    set X' := if m = 0 then B else chanL G a (m - 1) k B
    -- `d_y(𝓔_{i,m-1} B) ≤ d_y(B)`: support `N_{m-1}(a_i) ∌ y`
    have hX' : osc κ y X' ≤ osc κ y B := by
      by_cases h0 : m = 0
      · simp [X', h0]
      · simp only [X', if_neg h0]
        exact osc_chanL_le (hE _) (hmin _ (by omega)) B
    -- remainder: `d_y ≤ 2‖·‖` and D10.2.6
    have hrem : ‖chan k B - X'‖ ≤ shellConst C c * ∑ l ∈ Finset.Ico m (#Λ + 1), F l := by
      rw [hb, add_sub_cancel_left, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [← mul_assoc]
      exact step_10_2_6 hk hE htail hc hα hα1 l B
    have hIco : ∑ l ∈ Finset.Ico m (#Λ + 1), F l = ∑ l ∈ Finset.range (#Λ + 1),
        (if y ∈ graphNbhd G Λ {a} l then F l else 0) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr (Finset.ext fun l => ?_) fun _ _ => rfl
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
      refine ⟨fun h => ⟨h.2, graphNbhd_mono h.1 hm⟩, fun h => ⟨?_, h.1⟩⟩
      by_contra hl
      exact hmin l (by omega) h.2
    calc osc κ y (chan k B) ≤ osc κ y X' + 2 * ‖chan k B - X'‖ := osc_le_osc_add y _ _
      _ ≤ osc κ y B + 2 * (shellConst C c * ∑ l ∈ Finset.Ico m (#Λ + 1), F l) :=
          add_le_add hX' (mul_le_mul_of_nonneg_left hrem zero_le_two)
      _ = _ := by rw [hIco, mul_assoc]
  · -- `m = ∞`: `y` is outside the component `N_{|Λ|}(a_i)` of the support of `k_i` (D10.2.4)
    push Not at hex
    rw [← chanL_of_card_le hc hα htail le_rfl B]
    exact (osc_chanL_le (hE _) (fun h => (hex _ h).ne rfl |>.elim) B).trans
      (le_add_of_nonneg_right (mul_nonneg h2K hsum0))

/-- D10.2.10 (shell part). By D10.2.3 and D10.2.6,
`‖(𝓔_i - id) B‖ ≤ C ∑_{l ≥ 0} e^{-c l^α} ∑_{z ∈ N_l(a_i)} d_z(B)`. -/
theorem step_10_2_10_shell {a : σ} {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hk : 0 ≤ k ∧ k ≤ 1) (hE : ∀ l, 0 ≤ E G Λ a l k ∧ E G Λ a l k ≤ 1)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α))
    (hc : 0 < c) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ,
      ‖chan k B - B‖ ≤ shellConst C c * ∑ l ∈ Finset.range (#Λ + 1),
        Real.exp (-(c / 2) * (l : ℝ) ^ α) * ∑ z ∈ graphNbhd G Λ {a} l, osc κ z B := by
  intro B
  -- D10.2.3 (b) at `m = 0`: `𝓔_i - id = ∑_{l ≥ 0} Δ_{i,l}`
  have hb := (step_10_2_3 (κ := κ) hk hE htail hc hα hα1).2 0 B
  rw [if_pos rfl, ← Finset.range_eq_Ico] at hb
  rw [hb, add_sub_cancel_left, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [← mul_assoc]
  -- D10.2.6
  exact step_10_2_6 hk hE htail hc hα hα1 l B

end Shells

end AreaLaw
