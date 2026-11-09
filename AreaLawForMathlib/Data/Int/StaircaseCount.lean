import AreaLawForMathlib.Data.Int.Staircase
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Dilations, layers and mixed dyadic squares of staircases

Extends `AreaLawForMathlib/Data/Int/Staircase.lean`. A staircase dilated by the unit square is a
staircase (`Finset.IsStaircase.add_Icc`); its one-step layer has at most four sites per row plus
two rows (`Finset.IsStaircase.card_add_Icc_sdiff_le`); a staircase of diameter `d` meets at most
`6 (d / 2^k + 2)` mixed dyadic squares of side `2^k` (`Finset.IsStaircase.card_mixedIndices_le`).
-/

open Finset Int
open scoped Pointwise

namespace Finset

/-! ### Dilation by the unit square -/

theorem mem_add_Icc_one {R : Finset (ℤ × ℤ)} {p : ℤ × ℤ} :
    p ∈ R + Icc (-1, -1) (1, 1) ↔ ∃ x ∈ R, |p.1 - x.1| ≤ 1 ∧ |p.2 - x.2| ≤ 1 := by
  simp only [mem_add, mem_Icc]
  constructor
  · rintro ⟨x, hx, z, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    refine ⟨x, hx, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, abs_le] at * <;> omega
  · rintro ⟨x, hx, h1, h2⟩
    rw [abs_le] at h1 h2
    exact ⟨x, hx, p - x, ⟨⟨by simp; omega, by simp; omega⟩, by simp; omega, by simp; omega⟩,
      add_sub_cancel x p⟩

/-- D9.16.4. A staircase dilated by the unit square `[-1, 1]²` is a staircase, with one more row
on each side. -/
theorem IsStaircase.add_Icc {R : Finset (ℤ × ℤ)} {y₀ y₁ : ℤ} {ℓ r : ℤ → ℤ}
    (h : IsStaircase R y₀ y₁ ℓ r) :
    ∃ ℓ' r', IsStaircase (R + Icc (-1, -1) (1, 1)) (y₀ - 1) (y₁ + 1) ℓ' r' := by
  have h01 := h.le
  set c : ℤ → ℤ := fun y => max y₀ (min y y₁)
  have hc : ∀ y, y₀ ≤ c y ∧ c y ≤ y₁ := fun y => by simp only [c]; omega
  set L : ℤ → ℤ := fun y => ℓ (c y)
  set U : ℤ → ℤ := fun y => r (c y)
  have hcc : ∀ y, c (y + 1) = c y ∨ c (y + 1) = c y + 1 := fun y => by simp only [c]; omega
  have hL : Lip1 L := fun y => by
    rcases hcc y with e | e <;> simp only [L, e]
    · omega
    · exact h.lipℓ (c y)
  have hU : Lip1 U := fun y => by
    rcases hcc y with e | e <;> simp only [U, e]
    · omega
    · exact h.lipr (c y)
  have hLU : ∀ y, L y ≤ U y := fun y => h.lr _
  -- a site within one row of a clamped row, between its dilated endpoints, is in `R_1`
  have wit : ∀ (p : ℤ × ℤ) (y : ℤ), |p.2 - c y| ≤ 1 → L y - 1 ≤ p.1 → p.1 ≤ U y + 1 →
      ∃ x ∈ R, |p.1 - x.1| ≤ 1 ∧ |p.2 - x.2| ≤ 1 := by
    intro p y hy h1 h2
    refine ⟨(max (L y) (min p.1 (U y)), c y), (h.mem _).2 ⟨(hc y).1, (hc y).2, le_max_left _ _,
      max_le (hLU y) (min_le_right _ _)⟩, ?_, hy⟩
    rw [abs_le]; constructor <;> omega
  refine ⟨fun y => min (min (L (y - 1)) (L y)) (L (y + 1)) - 1,
    fun y => max (max (U (y - 1)) (U y)) (U (y + 1)) + 1, by omega,
    fun y => ?_, fun y => ?_, fun y => ?_, fun p => ?_⟩
  · have := hLU y; omega
  · have h1 := hL (y - 1); have h2 := hL y; have h3 := hL (y + 1)
    simp only [sub_add_cancel] at h1
    simp only [add_sub_cancel_right]
    constructor <;> omega
  · have h1 := hU (y - 1); have h2 := hU y; have h3 := hU (y + 1)
    simp only [sub_add_cancel] at h1
    simp only [add_sub_cancel_right]
    constructor <;> omega
  · rw [mem_add_Icc_one]
    constructor
    · rintro ⟨⟨x₁, x₂⟩, hx, h1, h2⟩
      obtain ⟨hx0, hx1, hx2, hx3⟩ := (h.mem _).1 hx
      simp only at hx0 hx1 hx2 hx3 h1 h2 ⊢
      rw [abs_le] at h1 h2
      have hcx : c x₂ = x₂ := by simp only [c]; omega
      have hLx : L x₂ = ℓ x₂ := by simp only [L, hcx]
      have hUx : U x₂ = r x₂ := by simp only [U, hcx]
      rcases (by omega : x₂ = p.2 - 1 ∨ x₂ = p.2 ∨ x₂ = p.2 + 1) with e | e | e <;>
        subst e <;> refine ⟨by omega, by omega, ?_, ?_⟩ <;> omega
    · rintro ⟨h0, h1, h2, h3⟩
      have hd : ∀ t, t = p.2 - 1 ∨ t = p.2 ∨ t = p.2 + 1 → |p.2 - c t| ≤ 1 := by
        rintro t (rfl | rfl | rfl) <;> (simp only [c]; rw [abs_le]; constructor <;> omega)
      have l1 := hL (p.2 - 1); have l2 := hL p.2
      have u1 := hU (p.2 - 1); have u2 := hU p.2
      simp only [sub_add_cancel] at l1 u1
      have := hLU (p.2 - 1); have := hLU p.2; have := hLU (p.2 + 1)
      rcases (by omega : (L (p.2 - 1) - 1 ≤ p.1 ∧ p.1 ≤ U (p.2 - 1) + 1) ∨
          (L p.2 - 1 ≤ p.1 ∧ p.1 ≤ U p.2 + 1) ∨
          (L (p.2 + 1) - 1 ≤ p.1 ∧ p.1 ≤ U (p.2 + 1) + 1)) with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact wit p _ (hd _ (Or.inl rfl)) k1 k2
      · exact wit p _ (hd _ (Or.inr (Or.inl rfl))) k1 k2
      · exact wit p _ (hd _ (Or.inr (Or.inr rfl))) k1 k2

/-! ### Diameter and layers -/

/-- All sites of `R` are within sup-norm distance `d` of each other. -/
def HasDiam (R : Finset (ℤ × ℤ)) (d : ℤ) : Prop :=
  ∀ p ∈ R, ∀ q ∈ R, |p.1 - q.1| ≤ d ∧ |p.2 - q.2| ≤ d

theorem HasDiam.mono {R R' : Finset (ℤ × ℤ)} {d : ℤ} (h : HasDiam R d) (hR : R' ⊆ R) :
    HasDiam R' d := fun p hp q hq => h p (hR hp) q (hR hq)

theorem HasDiam.add_Icc {R : Finset (ℤ × ℤ)} {d : ℤ} (h : HasDiam R d) :
    HasDiam (R + Icc (-1, -1) (1, 1)) (d + 2) := by
  intro p hp q hq
  obtain ⟨x, hx, h1, h2⟩ := mem_add_Icc_one.1 hp
  obtain ⟨x', hx', h1', h2'⟩ := mem_add_Icc_one.1 hq
  obtain ⟨t1, t2⟩ := h x hx x' hx'
  rw [abs_le] at h1 h2 h1' h2' t1 t2
  rw [abs_le, abs_le]
  omega

/-- A set of diameter `d` in one row has at most `2d + 1` sites. -/
theorem card_le_of_hasDiam_row {F : Finset (ℤ × ℤ)} {d y : ℤ} (hd : HasDiam F d)
    (hF : ∀ p ∈ F, p.2 = y) : #F ≤ (2 * d + 1).toNat := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  refine (card_le_card_of_injOn Prod.fst (t := Icc (p₀.1 - d) (p₀.1 + d)) (fun p hp => ?_)
    (fun p hp p' hp' e => Prod.ext e ((hF p hp).trans (hF p' hp').symm))).trans
    (by rw [Int.card_Icc]; omega)
  have := (hd p hp p₀ hp₀).1
  rw [abs_le] at this
  simp only [coe_Icc, Set.mem_Icc]
  omega

/-- A set of diameter `d` has at most `(2d + 1)²` sites. -/
theorem card_le_of_hasDiam {F : Finset (ℤ × ℤ)} {d : ℤ} (hd : HasDiam F d) :
    #F ≤ (2 * d + 1).toNat ^ 2 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  refine (card_le_card (t := Icc (p₀.1 - d, p₀.2 - d) (p₀.1 + d, p₀.2 + d)) fun p hp => ?_).trans
    ?_
  · have := hd p hp p₀ hp₀
    rw [abs_le, abs_le] at this
    rw [mem_Icc, Prod.le_def, Prod.le_def]
    omega
  · rw [Icc_prod_def, card_product, Int.card_Icc, Int.card_Icc, sq]
    apply le_of_eq; congr 1 <;> omega

/-- D9.16.5. The one-step layer of a staircase: at most four new sites on each of its rows and two
new rows. -/
theorem IsStaircase.card_add_Icc_sdiff_le {R : Finset (ℤ × ℤ)} {y₀ y₁ : ℤ} {ℓ r : ℤ → ℤ}
    (h : IsStaircase R y₀ y₁ ℓ r) {d : ℤ} (hd : HasDiam (R + Icc (-1, -1) (1, 1)) d) :
    #((R + Icc (-1, -1) (1, 1)) \ R) ≤ 4 * (y₁ + 1 - y₀).toNat + 2 * (2 * d + 1).toNat := by
  set R₁ := R + Icc (-1, -1) (1, 1)
  have hsub : R₁ \ R ⊆ ((Icc y₀ y₁).biUnion fun y =>
      ({(ℓ y - 2, y), (ℓ y - 1, y), (r y + 1, y), (r y + 2, y)} : Finset (ℤ × ℤ))) ∪
      ((R₁ \ R).filter (·.2 = y₀ - 1) ∪ (R₁ \ R).filter (·.2 = y₁ + 1)) := by
    intro p hp
    obtain ⟨hp1, hpR⟩ := mem_sdiff.1 hp
    obtain ⟨⟨x₁, x₂⟩, hx, h1, h2⟩ := mem_add_Icc_one.1 hp1
    obtain ⟨hx0, hx1, hx2, hx3⟩ := (h.mem _).1 hx
    simp only at hx0 hx1 hx2 hx3 h1 h2
    rw [h.mem] at hpR
    have hx₂ : |x₂ - p.2| ≤ 1 := by rw [abs_sub_comm]; exact h2
    have hℓ := (h.lipℓ.abs_sub_le x₂ p.2).trans hx₂
    have hr := (h.lipr.abs_sub_le x₂ p.2).trans hx₂
    rw [abs_le] at h1 h2 hℓ hr
    by_cases hy : y₀ ≤ p.2 ∧ p.2 ≤ y₁
    · refine mem_union_left _ (mem_biUnion.2 ⟨p.2, mem_Icc.2 hy, ?_⟩)
      simp only [mem_insert, mem_singleton, Prod.ext_iff, and_true]
      omega
    · refine mem_union_right _ ?_
      rw [mem_union, mem_filter, mem_filter]
      rcases (by omega : p.2 = y₀ - 1 ∨ p.2 = y₁ + 1) with e | e
      exacts [Or.inl ⟨hp, e⟩, Or.inr ⟨hp, e⟩]
  refine (card_le_card hsub).trans ((card_union_le _ _).trans
    (add_le_add ?_ ((card_union_le _ _).trans ?_)))
  · refine card_biUnion_le.trans ((sum_le_sum fun y _ => card_le_four).trans ?_)
    rw [sum_const, Int.card_Icc, smul_eq_mul, mul_comm]
  · have := card_le_of_hasDiam_row (F := (R₁ \ R).filter (·.2 = y₀ - 1)) (y := y₀ - 1)
      (hd.mono ((filter_subset _ _).trans sdiff_subset)) (fun p hp => (mem_filter.1 hp).2)
    have := card_le_of_hasDiam_row (F := (R₁ \ R).filter (·.2 = y₁ + 1)) (y := y₁ + 1)
      (hd.mono ((filter_subset _ _).trans sdiff_subset)) (fun p hp => (mem_filter.1 hp).2)
    omega

/-! ### Mixed dyadic squares -/

/-- A discrete intermediate value step: a property true at `a` and false at `b ≥ a` switches off
between two consecutive integers of `[a, b]`. -/
theorem _root_.Int.exists_switch {P : ℤ → Prop} {a b : ℤ} (hab : a ≤ b) (ha : P a) (hb : ¬P b) :
    ∃ y, a ≤ y ∧ y < b ∧ P y ∧ ¬P (y + 1) := by
  by_contra hc
  push Not at hc
  have : ∀ y, a ≤ y → y ≤ b → P y := by
    intro y hy
    induction y, hy using Int.leInduction with
    | base => exact fun _ => ha
    | succ y hy ih => exact fun hyb => hc y hy (by omega) (ih (by omega))
  exact hb (this b hab le_rfl)

/-- Integers at distance `< u` have quotients by `u` at distance `≤ 1`. -/
theorem _root_.Int.abs_ediv_sub_ediv_le {a b u : ℤ} (hu : 0 < u) (h : |a - b| < u) :
    |a / u - b / u| ≤ 1 := by
  have ha := Int.mul_ediv_add_emod a u
  have hb := Int.mul_ediv_add_emod b u
  have h1 := Int.emod_nonneg a hu.ne'
  have h2 := Int.emod_lt_of_pos a hu
  have h3 := Int.emod_nonneg b hu.ne'
  have h4 := Int.emod_lt_of_pos b hu
  rw [abs_lt] at h
  rw [abs_le]
  constructor
  · by_contra hc
    have : 2 * u ≤ (b / u - a / u) * u := by nlinarith
    nlinarith
  · by_contra hc
    have : 2 * u ≤ (a / u - b / u) * u := by nlinarith
    nlinarith

/-- Integers with the same quotient by `u` are at distance `< u`. -/
theorem _root_.Int.abs_sub_lt_of_ediv_eq {a b u : ℤ} (hu : 0 < u) (h : a / u = b / u) :
    |a - b| < u := by
  have ha := Int.mul_ediv_add_emod a u
  have hb := Int.mul_ediv_add_emod b u
  have := Int.emod_nonneg a hu.ne'
  have := Int.emod_lt_of_pos a hu
  have := Int.emod_nonneg b hu.ne'
  have := Int.emod_lt_of_pos b hu
  rw [h] at ha
  rw [abs_lt]
  constructor <;> linarith

/-- The quotients by `u` of an integer interval `[a, b]`: at most `(b - a) / u + 2`. -/
theorem card_image_ediv_Icc_le {a b u : ℤ} (hu : 0 < u) (hab : a ≤ b) :
    (#((Icc a b).image (· / u)) : ℝ) ≤ (b - a) / u + 2 := by
  have hsub : (Icc a b).image (· / u) ⊆ Icc (a / u) (b / u) := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    rw [mem_Icc] at hy ⊢
    exact ⟨Int.ediv_le_ediv hu hy.1, Int.ediv_le_ediv hu hy.2⟩
  have h1 := card_le_card hsub
  rw [Int.card_Icc] at h1
  have hle : a / u ≤ b / u := Int.ediv_le_ediv hu hab
  have hb : b / u * u ≤ b := Int.ediv_mul_le b hu.ne'
  have ha : a < (a / u + 1) * u := Int.lt_ediv_add_one_mul_self a hu
  have hq : ((b / u - a / u : ℤ) : ℝ) * u < (b - a) + u := by
    have : (b / u - a / u) * u < b - a + u := by nlinarith
    exact_mod_cast this
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hq' : ((b / u - a / u : ℤ) : ℝ) < (b - a) / u + 1 := by
    rw [div_add_one hu'.ne', lt_div_iff₀ hu']; exact hq
  have h2 : (#((Icc a b).image (· / u)) : ℝ) ≤ ((b / u + 1 - a / u : ℤ) : ℝ) := by
    have : ((b / u + 1 - a / u).toNat : ℤ) = b / u + 1 - a / u := Int.toNat_of_nonneg (by omega)
    rw [← this]; exact_mod_cast h1
  push_cast at hq' h2
  linarith

/-- Row endpoints moving by at most one meet at most two square columns per strip of rows. -/
theorem card_image_lip_le {ℓ : ℤ → ℤ} (hℓ : Lip1 ℓ) {u : ℤ} (hu : 0 < u) (s : Finset ℤ) :
    #(s.image fun y => (ℓ y / u, y / u)) ≤ 2 * #(s.image (· / u)) := by
  set t := s.image fun y => (ℓ y / u, y / u)
  have himg : t.image Prod.snd = s.image (· / u) := by
    simp only [t, image_image, Function.comp_def]
  rw [← himg]
  refine card_le_mul_card_image t 2 fun b _ => ?_
  rcases (t.filter (·.2 = b)).eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  obtain ⟨w₀, hw₀, hmin⟩ := (t.filter (·.2 = b)).exists_min_image Prod.fst hne
  refine (card_le_card_of_injOn Prod.fst (t := Icc w₀.1 (w₀.1 + 1)) ?_ ?_).trans
    (by rw [Int.card_Icc]; omega)
  · intro w hw
    have hmw := hmin w hw
    obtain ⟨hwt, hwb⟩ := mem_filter.1 hw
    obtain ⟨hw't, hw'b⟩ := mem_filter.1 hw₀
    obtain ⟨y, -, rfl⟩ := mem_image.1 hwt
    obtain ⟨y', -, rfl⟩ := mem_image.1 hw't
    simp only at hwb hw'b hmw ⊢
    have hyy : |y - y'| < u := Int.abs_sub_lt_of_ediv_eq hu (hwb.trans hw'b.symm)
    have := Int.abs_ediv_sub_ediv_le hu ((hℓ.abs_sub_le y y').trans_lt hyy)
    rw [abs_le] at this
    rw [coe_Icc, Set.mem_Icc]
    omega
  · intro w hw w' hw' e
    exact Prod.ext e ((mem_filter.1 hw).2.trans (mem_filter.1 hw').2.symm)

/-- D9.17.1–2. A dyadic square meeting a staircase and its complement contains an endpoint of a
row or a site of the top or bottom row. -/
theorem IsStaircase.mixedIndices_subset {R : Finset (ℤ × ℤ)} {y₀ y₁ : ℤ} {ℓ r : ℤ → ℤ}
    (h : IsStaircase R y₀ y₁ ℓ r) (k : ℕ) :
    mixedIndices R k ⊆
      ((((Icc y₀ y₁).image fun y => (ℓ y, y)) ∪ (Icc y₀ y₁).image fun y => (r y, y)) ∪
        (((Icc (ℓ y₁) (r y₁)).image fun x => (x, y₁)) ∪
          (Icc (ℓ y₀) (r y₀)).image fun x => (x, y₀))).image (dyadicIndex k) := by
  intro z hz
  obtain ⟨⟨p, hpR, hpz⟩, q, hqR, hqz⟩ := mem_mixedIndices.1 hz
  obtain ⟨u, hu_def⟩ : ∃ u : ℤ, u = 2 ^ k := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; positivity
  obtain ⟨X, hX⟩ : ∃ X, X = u * z.1 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = u * z.2 := ⟨_, rfl⟩
  have sq : ∀ o : ℤ × ℤ, o ∈ dyadicSquare k z ↔
      X ≤ o.1 ∧ o.1 ≤ X + (u - 1) ∧ Y ≤ o.2 ∧ o.2 ≤ Y + (u - 1) := fun o => by
    rw [hX, hY, hu_def]; simp only [dyadicSquare, mem_Icc, Prod.le_def]; tauto
  by_contra hO
  have hO' : ∀ o, o ∈ ((((Icc y₀ y₁).image fun y => (ℓ y, y)) ∪
      (Icc y₀ y₁).image fun y => (r y, y)) ∪ (((Icc (ℓ y₁) (r y₁)).image fun x => (x, y₁)) ∪
      (Icc (ℓ y₀) (r y₀)).image fun x => (x, y₀))) → o ∉ dyadicSquare k z :=
    fun o ho hoz => hO (mem_image.2 ⟨o, ho, mem_dyadicSquare.1 hoz⟩)
  have h01 := h.le
  -- D9.17.1: inside the square every row is all in or all out
  have hom : ∀ x x' y, (x, y) ∈ dyadicSquare k z → (x', y) ∈ dyadicSquare k z →
      (x, y) ∈ R → (x', y) ∈ R := by
    intro x x' y hx hx' hxR
    by_contra hx'R
    obtain ⟨h0, h1, h2, h3⟩ := (h.mem _).1 hxR
    rw [h.mem] at hx'R
    rw [sq] at hx hx'
    simp only at h0 h1 h2 h3 hx'R hx hx'
    rcases (by omega : x' < ℓ y ∨ r y < x') with c | c
    · exact hO' (ℓ y, y) (mem_union_left _ (mem_union_left _ (mem_image.2
        ⟨y, mem_Icc.2 ⟨h0, h1⟩, rfl⟩))) ((sq _).2 ⟨by omega, by omega, hx.2.2⟩)
    · exact hO' (r y, y) (mem_union_left _ (mem_union_right _ (mem_image.2
        ⟨y, mem_Icc.2 ⟨h0, h1⟩, rfl⟩))) ((sq _).2 ⟨by omega, by omega, hx.2.2⟩)
  have hp := (sq p).1 hpz
  have hq := (sq q).1 hqz
  have hu2 : 2 ≤ u := by
    by_contra hu1
    exact hqR (by rw [show q = p from Prod.ext (by omega) (by omega)]; exact hpR)
  have hp' : (X, p.2) ∈ R := hom p.1 X p.2 hpz ((sq _).2 ⟨le_rfl, by omega, hp.2.2⟩) hpR
  have hq' : (X, q.2) ∉ R := fun hX' => hqR (hom X q.1 q.2 ((sq _).2 ⟨le_rfl, by omega, hq.2.2⟩)
    hqz hX')
  -- D9.17.2: an all-in row next to an all-out row is the top or bottom row
  have hfull : ∀ y, Y ≤ y → y ≤ Y + (u - 1) → (X, y) ∈ R →
      y₀ ≤ y ∧ y ≤ y₁ ∧ ℓ y ≤ X ∧ X + (u - 1) ≤ r y := by
    intro y hy1 hy2 hyR
    obtain ⟨h0, h1, h2, -⟩ := (h.mem _).1 hyR
    obtain ⟨-, -, -, h3⟩ := (h.mem _).1 (hom X (X + (u - 1)) y
      ((sq _).2 ⟨le_rfl, by omega, hy1, hy2⟩) ((sq _).2 ⟨by omega, le_rfl, hy1, hy2⟩) hyR)
    exact ⟨h0, h1, h2, h3⟩
  rcases le_or_gt p.2 q.2 with hpq | hpq
  · obtain ⟨y, hy1, hy2, hin, hout⟩ := Int.exists_switch (P := fun y => (X, y) ∈ R) hpq hp' hq'
    obtain ⟨h0, h1, h2, h3⟩ := hfull y (by omega) (by omega) hin
    rcases eq_or_lt_of_le h1 with e | e
    · subst e
      exact hO' (X, y) (mem_union_right _ (mem_union_left _ (mem_image.2
        ⟨X, mem_Icc.2 ⟨h2, by omega⟩, rfl⟩))) ((sq _).2 ⟨le_rfl, by omega, by omega, by omega⟩)
    · have hl := h.lipℓ y
      have hr := h.lipr y
      have hlr := h.lr (y + 1)
      have hmem : (max X (ℓ (y + 1)), y + 1) ∈ R :=
        (h.mem _).2 ⟨by simp only; omega, by simp only; omega, le_max_right _ _,
          max_le (by simp only; omega) hlr⟩
      exact hout (hom _ X (y + 1) ((sq _).2 ⟨le_max_left _ _, (by simp only; omega),
        (by simp only; omega), (by simp only; omega)⟩) ((sq _).2 ⟨le_rfl, by omega, by omega,
        by omega⟩) hmem)
  · obtain ⟨t, ht1, ht2, hin, hout⟩ := Int.exists_switch (P := fun t => (X, -t) ∈ R)
      (by omega : -p.2 ≤ -q.2) (by simpa using hp') (by simpa using hq')
    simp only [neg_add] at hin hout
    obtain ⟨h0, h1, h2, h3⟩ := hfull (-t) (by omega) (by omega) hin
    rcases eq_or_lt_of_le h0 with e | e
    · rw [← e] at h2 h3
      exact hO' (X, y₀) (mem_union_right _ (mem_union_right _ (mem_image.2
        ⟨X, mem_Icc.2 ⟨h2, by omega⟩, rfl⟩))) ((sq _).2 ⟨le_rfl, by omega, by omega, by omega⟩)
    · have hl := h.lipℓ (-t + -1)
      have hr := h.lipr (-t + -1)
      have hlr := h.lr (-t + -1)
      simp only [show -t + -1 + 1 = -t by ring] at hl hr
      have hmem : (max X (ℓ (-t + -1)), -t + -1) ∈ R :=
        (h.mem _).2 ⟨by simp only; omega, by simp only; omega, le_max_right _ _,
          max_le (by simp only; omega) hlr⟩
      exact hout (hom _ X (-t + -1) ((sq _).2 ⟨le_max_left _ _, (by simp only; omega),
        (by simp only; omega), (by simp only; omega)⟩) ((sq _).2 ⟨le_rfl, by omega, by omega,
        by omega⟩) hmem)

/-- D9.17.1–2. A staircase of diameter `d` meets at most `6 (d / 2^k + 2)` mixed dyadic squares of
side `2^k`. -/
theorem IsStaircase.card_mixedIndices_le {R : Finset (ℤ × ℤ)} {y₀ y₁ : ℤ} {ℓ r : ℤ → ℤ}
    (h : IsStaircase R y₀ y₁ ℓ r) {d : ℤ} (hd : HasDiam R d) (k : ℕ) :
    (#(mixedIndices R k) : ℝ) ≤ 6 * (d / 2 ^ k + 2) := by
  obtain ⟨u, hu_def⟩ : ∃ u : ℤ, u = 2 ^ k := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; positivity
  have h01 := h.le
  have m0 : (ℓ y₀, y₀) ∈ R := (h.mem _).2 ⟨le_rfl, h01, le_rfl, h.lr _⟩
  have m1 : (ℓ y₁, y₁) ∈ R := (h.mem _).2 ⟨h01, le_rfl, le_rfl, h.lr _⟩
  have m0' : (r y₀, y₀) ∈ R := (h.mem _).2 ⟨le_rfl, h01, h.lr _, le_rfl⟩
  have m1' : (r y₁, y₁) ∈ R := (h.mem _).2 ⟨h01, le_rfl, h.lr _, le_rfl⟩
  have dy : y₁ - y₀ ≤ d := by have := (hd _ m1 _ m0).2; rw [abs_le] at this; simp at this; omega
  have d1 : r y₁ - ℓ y₁ ≤ d := by
    have := (hd _ m1' _ m1).1; rw [abs_le] at this; simp at this; omega
  have d0 : r y₀ - ℓ y₀ ≤ d := by
    have := (hd _ m0' _ m0).1; rw [abs_le] at this; simp at this; omega
  have hQ := card_image_ediv_Icc_le hu h01
  have hT := card_image_ediv_Icc_le hu (h.lr y₁)
  have hB := card_image_ediv_Icc_le hu (h.lr y₀)
  have cL := card_image_lip_le h.lipℓ hu (Icc y₀ y₁)
  have cR := card_image_lip_le h.lipr hu (Icc y₀ y₁)
  have cT : #(((Icc (ℓ y₁) (r y₁)).image fun x => (x, y₁)).image (dyadicIndex k)) ≤
      #((Icc (ℓ y₁) (r y₁)).image (· / u)) := by
    rw [image_image, show ((dyadicIndex k ∘ fun x => (x, y₁)) : ℤ → ℤ × ℤ) =
      (fun t => (t, y₁ / u)) ∘ (· / u) by rw [hu_def]; rfl, ← image_image]
    exact card_image_le
  have cB : #(((Icc (ℓ y₀) (r y₀)).image fun x => (x, y₀)).image (dyadicIndex k)) ≤
      #((Icc (ℓ y₀) (r y₀)).image (· / u)) := by
    rw [image_image, show ((dyadicIndex k ∘ fun x => (x, y₀)) : ℤ → ℤ × ℤ) =
      (fun t => (t, y₀ / u)) ∘ (· / u) by rw [hu_def]; rfl, ← image_image]
    exact card_image_le
  have eL : ((Icc y₀ y₁).image fun y => (ℓ y, y)).image (dyadicIndex k) =
      (Icc y₀ y₁).image fun y => (ℓ y / u, y / u) := by
    rw [image_image, hu_def]; rfl
  have eR : ((Icc y₀ y₁).image fun y => (r y, y)).image (dyadicIndex k) =
      (Icc y₀ y₁).image fun y => (r y / u, y / u) := by
    rw [image_image, hu_def]; rfl
  have hsub := card_le_card (h.mixedIndices_subset k)
  simp only [image_union] at hsub
  have hcard := hsub.trans ((card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans
    (add_le_add le_rfl le_rfl)) (card_union_le _ _)))
  rw [eL, eR] at hcard
  have hd' : ((y₁ - y₀ : ℤ) : ℝ) ≤ d := by exact_mod_cast dy
  have hd1 : ((r y₁ - ℓ y₁ : ℤ) : ℝ) ≤ d := by exact_mod_cast d1
  have hd0 : ((r y₀ - ℓ y₀ : ℤ) : ℝ) ≤ d := by exact_mod_cast d0
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  push_cast at hQ hT hB hd' hd1 hd0
  have q1 : ((y₁ : ℝ) - y₀) / u ≤ d / u := div_le_div_of_nonneg_right hd' hu'.le
  have q2 : ((r y₁ : ℝ) - ℓ y₁) / u ≤ d / u := div_le_div_of_nonneg_right hd1 hu'.le
  have q3 : ((r y₀ : ℝ) - ℓ y₀) / u ≤ d / u := div_le_div_of_nonneg_right hd0 hu'.le
  have : (#(mixedIndices R k) : ℝ) ≤ 2 * #((Icc y₀ y₁).image (· / u)) +
      2 * #((Icc y₀ y₁).image (· / u)) + (#((Icc (ℓ y₁) (r y₁)).image (· / u)) +
      #((Icc (ℓ y₀) (r y₀)).image (· / u))) := by
    exact_mod_cast hcard.trans (by omega)
  have hu2 : ((u : ℤ) : ℝ) = 2 ^ k := by rw [hu_def]; push_cast; rfl
  rw [hu2] at q1 q2 q3 hQ hT hB
  linarith

/-- The rows of a staircase of diameter `d` span at most `d`. -/
theorem IsStaircase.sub_le_of_hasDiam {R : Finset (ℤ × ℤ)} {y₀ y₁ : ℤ} {ℓ r : ℤ → ℤ}
    (h : IsStaircase R y₀ y₁ ℓ r) {d : ℤ} (hd : HasDiam R d) : y₁ - y₀ ≤ d := by
  have := (hd _ ((h.mem (ℓ y₁, y₁)).2 ⟨h.le, le_rfl, le_rfl, h.lr _⟩) _
    ((h.mem (ℓ y₀, y₀)).2 ⟨le_rfl, h.le, le_rfl, h.lr _⟩)).2
  rw [abs_le] at this
  exact this.2

end Finset
