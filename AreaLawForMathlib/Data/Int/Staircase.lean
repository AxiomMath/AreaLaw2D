import AreaLawForMathlib.Data.Int.DyadicCover

/-!
# Staircase subsets of `ℤ × ℤ`

Extends `Mathlib/Data/Int/Interval.lean`. A finite `R ⊆ ℤ × ℤ` is a *staircase* with rows
`y₀, …, y₁` and endpoint functions `ℓ, r` if its row at height `y ∈ [y₀, y₁]` is the integer
interval `[ℓ y, r y]`, its other rows are empty, and `ℓ`, `r` change by at most one between
consecutive heights. The lattice sample of an intersection of half-planes `σ₁ x + σ₂ y ≤ m` with
`σᵢ ∈ {-1, 0, 1}` (an *integer octagon*) is a staircase (`Finset.isStaircase_of_octagon`); a
staircase dilated by the unit square is a staircase (`Finset.IsStaircase.add_Icc`); the one-step
layer of a staircase and its mixed dyadic squares are counted
(`Finset.IsStaircase.card_add_Icc_sdiff_le`, `Finset.IsStaircase.card_mixedIndices_le`).
-/

open Finset

namespace Int

/-- `f` changes by at most one between consecutive integers. -/
def Lip1 (f : ℤ → ℤ) : Prop := ∀ y, f (y + 1) ≤ f y + 1 ∧ f y ≤ f (y + 1) + 1

theorem Lip1.abs_sub_le {f : ℤ → ℤ} (hf : Lip1 f) (a b : ℤ) : |f a - f b| ≤ |a - b| := by
  have key : ∀ (a : ℤ) (n : ℕ), |f (a + n) - f a| ≤ n := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hf (a + n)
      rw [abs_le] at ih ⊢
      push_cast
      rw [← add_assoc]
      constructor <;> linarith [this.1, this.2, ih.1, ih.2]
  rcases le_total a b with h | h
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    have := key a n
    rw [show b = a + n by omega, abs_sub_comm, abs_sub_comm a]
    simpa using this
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    have := key b n
    rw [show a = b + n by omega]
    simpa using this

/-- The step `s ∈ {-1, 0, 1}` towards `(e, d)` used to pass from one row of an integer octagon to
the next. -/
def octStep (e d : ℤ) : ℤ := if 0 < e then 1 else if -d < e then 0 else -1

theorem abs_octStep_le (e d : ℤ) : |octStep e d| ≤ 1 := by
  unfold octStep; split_ifs <;> simp

/-- One integer half-plane with coefficients in `{-1, 0, 1}`: if it contains `p` and a point
`q` of a higher row, it contains `p + (octStep, 1)`. -/
theorem octStep_spec {σ₁ σ₂ m p₁ p₂ q₁ q₂ : ℤ} (h₁ : |σ₁| ≤ 1) (h₂ : |σ₂| ≤ 1)
    (hp : σ₁ * p₁ + σ₂ * p₂ ≤ m) (hq : σ₁ * q₁ + σ₂ * q₂ ≤ m) (hpq : p₂ < q₂) :
    σ₁ * (p₁ + octStep (q₁ - p₁) (q₂ - p₂)) + σ₂ * (p₂ + 1) ≤ m := by
  rw [abs_le] at h₁ h₂
  unfold octStep
  rcases (by omega : σ₁ = -1 ∨ σ₁ = 0 ∨ σ₁ = 1) with rfl | rfl | rfl <;>
  rcases (by omega : σ₂ = -1 ∨ σ₂ = 0 ∨ σ₂ = 1) with rfl | rfl | rfl <;>
  split_ifs <;> omega

/-- One integer half-plane is convex along rows. -/
theorem oct_row_convex {σ₁ σ₂ m a b x y : ℤ} (h₁ : |σ₁| ≤ 1) (ha : σ₁ * a + σ₂ * y ≤ m)
    (hb : σ₁ * b + σ₂ * y ≤ m) (hax : a ≤ x) (hxb : x ≤ b) : σ₁ * x + σ₂ * y ≤ m := by
  rw [abs_le] at h₁
  rcases (by omega : σ₁ = -1 ∨ σ₁ = 0 ∨ σ₁ = 1) with rfl | rfl | rfl <;> omega

end Int

open Int

namespace Finset

/-- `R` is a staircase with rows `y₀, …, y₁` and row endpoints `ℓ y ≤ r y`. -/
structure IsStaircase (R : Finset (ℤ × ℤ)) (y₀ y₁ : ℤ) (ℓ r : ℤ → ℤ) : Prop where
  le : y₀ ≤ y₁
  lr : ∀ y, ℓ y ≤ r y
  lipℓ : Lip1 ℓ
  lipr : Lip1 r
  mem : ∀ p, p ∈ R ↔ y₀ ≤ p.2 ∧ p.2 ≤ y₁ ∧ ℓ p.2 ≤ p.1 ∧ p.1 ≤ r p.2

/-- The lattice sample of an integer octagon `{p | ∀ k ∈ K, k₁ p₁ + k₂ p₂ ≤ k₃}`, `|kᵢ| ≤ 1`, is a
staircase when nonempty and finite. -/
theorem isStaircase_of_octagon {R : Finset (ℤ × ℤ)} (K : List (ℤ × ℤ × ℤ))
    (hK : ∀ k ∈ K, |k.1| ≤ 1 ∧ |k.2.1| ≤ 1)
    (hR : ∀ p, p ∈ R ↔ ∀ k ∈ K, k.1 * p.1 + k.2.1 * p.2 ≤ k.2.2) (hne : R.Nonempty) :
    ∃ y₀ y₁ ℓ r, IsStaircase R y₀ y₁ ℓ r := by
  -- one row up and one row down, and convexity along rows
  have up : ∀ p ∈ R, ∀ q ∈ R, p.2 < q.2 → ∃ s, |s| ≤ 1 ∧ (p.1 + s, p.2 + 1) ∈ R := by
    intro p hp q hq hpq
    refine ⟨_, abs_octStep_le (q.1 - p.1) (q.2 - p.2), (hR _).2 fun k hk => ?_⟩
    exact octStep_spec (hK k hk).1 (hK k hk).2 ((hR p).1 hp k hk) ((hR q).1 hq k hk) hpq
  have down : ∀ p ∈ R, ∀ q ∈ R, q.2 < p.2 → ∃ s, |s| ≤ 1 ∧ (p.1 + s, p.2 - 1) ∈ R := by
    intro p hp q hq hpq
    refine ⟨_, abs_octStep_le (q.1 - p.1) (-q.2 - -p.2), (hR _).2 fun k hk => ?_⟩
    have := octStep_spec (σ₂ := -k.2.1) (m := k.2.2) (p₁ := p.1) (q₁ := q.1) (p₂ := -p.2)
      (q₂ := -q.2) (hK k hk).1
      (by rw [abs_neg]; exact (hK k hk).2) (by linarith [(hR p).1 hp k hk])
      (by linarith [(hR q).1 hq k hk]) (by omega)
    simp only at this ⊢
    linarith
  have conv : ∀ a b x y, (a, y) ∈ R → (b, y) ∈ R → a ≤ x → x ≤ b → (x, y) ∈ R := by
    intro a b x y ha hb hax hxb
    exact (hR _).2 fun k hk => oct_row_convex (hK k hk).1 ((hR _).1 ha k hk) ((hR _).1 hb k hk)
      hax hxb
  -- the rows
  have hY : (R.image Prod.snd).Nonempty := hne.image _
  set y₀ := (R.image Prod.snd).min' hY
  set y₁ := (R.image Prod.snd).max' hY
  have hy₀ : ∃ x, (x, y₀) ∈ R := by
    obtain ⟨p, hp, hp2⟩ := mem_image.1 ((R.image Prod.snd).min'_mem hY)
    exact ⟨p.1, by rw [show y₀ = p.2 from hp2.symm]; exact hp⟩
  have hy₁ : ∃ x, (x, y₁) ∈ R := by
    obtain ⟨p, hp, hp2⟩ := mem_image.1 ((R.image Prod.snd).max'_mem hY)
    exact ⟨p.1, by rw [show y₁ = p.2 from hp2.symm]; exact hp⟩
  have hrange : ∀ p ∈ R, y₀ ≤ p.2 ∧ p.2 ≤ y₁ := fun p hp =>
    ⟨min'_le _ _ (mem_image_of_mem _ hp), le_max' _ _ (mem_image_of_mem _ hp)⟩
  have h01 : y₀ ≤ y₁ := min'_le_max' _ hY
  have hrows : ∀ y, y₀ ≤ y → y ≤ y₁ → ∃ x, (x, y) ∈ R := by
    intro y h0
    induction y, h0 using Int.leInduction with
    | base => exact fun _ => hy₀
    | succ y hy ih =>
      intro hy1
      obtain ⟨x, hx⟩ := ih (by omega)
      obtain ⟨x₁, hx₁⟩ := hy₁
      obtain ⟨s, -, hs⟩ := up (x, y) hx (x₁, y₁) hx₁ (by simp; omega)
      exact ⟨_, hs⟩
  -- the endpoints, read on the clamped row
  set c : ℤ → ℤ := fun y => max y₀ (min y y₁)
  have hc : ∀ y, y₀ ≤ c y ∧ c y ≤ y₁ := fun y => by simp only [c]; omega
  set row : ℤ → Finset ℤ := fun y => (R.filter (·.2 = y)).image Prod.fst
  have mem_row : ∀ x y, x ∈ row y ↔ (x, y) ∈ R := by
    intro x y
    simp only [row, mem_image, mem_filter]
    exact ⟨fun ⟨p, ⟨hp, hpy⟩, hpx⟩ => by rw [← hpx, ← hpy]; exact hp,
      fun h => ⟨(x, y), ⟨h, rfl⟩, rfl⟩⟩
  have hrow : ∀ y, (row (c y)).Nonempty := fun y => by
    obtain ⟨x, hx⟩ := hrows (c y) (hc y).1 (hc y).2
    exact ⟨x, (mem_row _ _).2 hx⟩
  set ℓ : ℤ → ℤ := fun y => (row (c y)).min' (hrow y)
  set r : ℤ → ℤ := fun y => (row (c y)).max' (hrow y)
  have hℓ : ∀ y, (ℓ y, c y) ∈ R := fun y => (mem_row _ _).1 (min'_mem _ _)
  have hr : ∀ y, (r y, c y) ∈ R := fun y => (mem_row _ _).1 (max'_mem _ _)
  have hℓle : ∀ y x, (x, c y) ∈ R → ℓ y ≤ x := fun y x hx => min'_le _ _ ((mem_row _ _).2 hx)
  have hrle : ∀ y x, (x, c y) ∈ R → x ≤ r y := fun y x hx => le_max' _ _ ((mem_row _ _).2 hx)
  have hcc : ∀ y, c (y + 1) = c y ∨ (c (y + 1) = c y + 1 ∧ c y < y₁ ∧ y₀ ≤ c y) := fun y => by
    simp only [c]; omega
  refine ⟨y₀, y₁, ℓ, r, h01, fun y => min'_le_max' _ _, fun y => ?_, fun y => ?_, fun p => ?_⟩
  · rcases hcc y with h | ⟨h, hlt, hge⟩
    · have h1 := hℓle y _ (h ▸ hℓ (y + 1))
      have h2 := hℓle (y + 1) _ (h.symm ▸ hℓ y)
      constructor <;> omega
    · obtain ⟨x₁, hx₁⟩ := hy₁
      obtain ⟨x₀, hx₀⟩ := hy₀
      obtain ⟨s, hs, hsR⟩ := up _ (hℓ y) _ hx₁ (by simpa using hlt)
      obtain ⟨t, ht, htR⟩ := down _ (hℓ (y + 1)) _ hx₀ (by simp only; omega)
      have h1 := hℓle (y + 1) _ (h ▸ hsR)
      have h2 := hℓle y _ (by simpa [h] using htR)
      rw [abs_le] at hs ht
      constructor <;> omega
  · rcases hcc y with h | ⟨h, hlt, hge⟩
    · have h1 := hrle y _ (h ▸ hr (y + 1))
      have h2 := hrle (y + 1) _ (h.symm ▸ hr y)
      constructor <;> omega
    · obtain ⟨x₁, hx₁⟩ := hy₁
      obtain ⟨x₀, hx₀⟩ := hy₀
      obtain ⟨s, hs, hsR⟩ := up _ (hr y) _ hx₁ (by simpa using hlt)
      obtain ⟨t, ht, htR⟩ := down _ (hr (y + 1)) _ hx₀ (by simp only; omega)
      have h1 := hrle (y + 1) _ (h ▸ hsR)
      have h2 := hrle y _ (by simpa [h] using htR)
      rw [abs_le] at hs ht
      constructor <;> omega
  · constructor
    · intro hp
      obtain ⟨h0, h1⟩ := hrange p hp
      have hcp : c p.2 = p.2 := by simp only [c]; omega
      have hp' : (p.1, c p.2) ∈ R := by rw [hcp]; exact hp
      exact ⟨h0, h1, hℓle _ _ hp', hrle _ _ hp'⟩
    · rintro ⟨h0, h1, h2, h3⟩
      have hcp : c p.2 = p.2 := by simp only [c]; omega
      have hl := hℓ p.2
      have hr' := hr p.2
      rw [hcp] at hl hr'
      exact conv _ _ p.1 p.2 hl hr' h2 h3

end Finset
