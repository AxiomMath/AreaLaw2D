import AreaLaw.S09_Scanner.Interfaces
import AreaLawForMathlib.Data.Int.StaircaseCount
import AreaLawForMathlib.QuantumInfo.Entropy.Subadditivity

/-!
# §9.3 Geometric targets and entropy inputs

Digest `digest/09-scanner.md`, D9.14–D9.18 and D9.21.2: Definition 9.3 (templates), Lemma 9.4
(rows, coverings and shell entropy) through its steps D9.16 (one piece), D9.17 (mixed squares),
D9.18 (covering and shell entropy), and the shell entropy of a safe rectangle used by
Proposition 9.5.
-/

open scoped Pointwise Matrix
open Finset OpenAI Arealaw Int

namespace AreaLaw.Scanner

/-! ## D9.14 Definition 9.3 -/

/-- D9.14 **Definition 9.3** (template). For `s₀ ≥ 1`, `n` positive integers, a template with
parameters `(n, s₀)` is a nonempty finite `T = ⋃_{a ≤ N₀} (P_a ∩ ℤ²)`, `n ≥ C_tpl N₀ (s₀ + 1)`,
`diam_∞ T ≤ n`, `N₀ ≥ 1`, each `P_a` a closed convex rectangle or triangle of sup-norm diameter
`≤ s₀` with all sides of slope `0, ∞, 1` or `-1`. `T` is separated from the cut if
`dist_∞(T, Z) > 4 D₀ s₀` (`OpenAI.IsSeparatedFromCut`).
2D only: the pieces are planar polygons with sides of slopes `0, ∞, ±1`. -/
abbrev def_9_3 (Ctpl : ℝ) (n s₀ : ℕ) (T : Finset (ℤ × ℤ)) : Prop := IsTemplate Ctpl n s₀ T

/-! ## Template pieces as intersections of half-planes -/

/-- The set cut out by finitely many closed half-planes `w · p ≤ c`. -/
def halfPlanes (H : List ((ℝ × ℝ) × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∀ h ∈ H, h.1.1 * p.1 + h.1.2 * p.2 ≤ h.2}

theorem convex_halfPlanes (H : List ((ℝ × ℝ) × ℝ)) : Convex ℝ (halfPlanes H) := by
  intro x hx y hy a b ha hb hab h hH
  have h1 := mul_le_mul_of_nonneg_left (hx h hH) ha
  have h2 := mul_le_mul_of_nonneg_left (hy h hH) hb
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination h1 + h2 + h.2 * hab

/-- The normal `t (v₂, -v₁)` of a template direction `v` is a template direction. -/
theorem hasTemplateSlope_perp {v : ℝ × ℝ} (hv : HasTemplateSlope v) (t : ℝ) :
    HasTemplateSlope (t * v.2, -(t * v.1)) := by
  unfold HasTemplateSlope at *
  simp only
  rcases hv with h | h | h | h
  · exact Or.inr (Or.inl (by rw [h, mul_zero]))
  · exact Or.inl (by rw [h, mul_zero, neg_zero])
  · exact Or.inr (Or.inr (Or.inr (by rw [h])))
  · exact Or.inr (Or.inr (Or.inl (by rw [h]; ring)))

theorem hasTemplateSlope_neg {v : ℝ × ℝ} (hv : HasTemplateSlope v) : HasTemplateSlope (-v) := by
  unfold HasTemplateSlope at *
  simp only [Prod.fst_neg, Prod.snd_neg]
  rcases hv with h | h | h | h <;> simp [h]

theorem mem_convexHull_of_sum {s : Set (ℝ × ℝ)} {n : ℕ} (w : Fin n → ℝ) (z : Fin n → ℝ × ℝ)
    (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) (hz : ∀ i, z i ∈ s) :
    ∑ i, w i • z i ∈ convexHull ℝ s :=
  (convex_convexHull ℝ s).sum_mem (fun i _ => hw i) h1 fun i _ => subset_convexHull ℝ s (hz i)

/-- D9.16.1 (triangles). A triangle with template sides is cut out by three half-planes with
template normals (barycentric coordinates). -/
theorem triangle_eq_halfPlanes {a b c : ℝ × ℝ} (hba : HasTemplateSlope (b - a))
    (hcb : HasTemplateSlope (c - b)) (hac : HasTemplateSlope (a - c))
    (hD : (b - a).1 * (c - a).2 - (b - a).2 * (c - a).1 ≠ 0) :
    ∃ H : List ((ℝ × ℝ) × ℝ), (∀ h ∈ H, HasTemplateSlope h.1) ∧
      convexHull ℝ {a, b, c} = halfPlanes H := by
  obtain ⟨D, hDdef⟩ : ∃ D, (b - a).1 * (c - a).2 - (b - a).2 * (c - a).1 = D := ⟨_, rfl⟩
  have hca : HasTemplateSlope (c - a) := by simpa using hasTemplateSlope_neg hac
  refine ⟨[((-D * (c - a).2, -(-D * (c - a).1)), -D * (c - a).2 * a.1 + -(-D * (c - a).1) * a.2),
    ((D * (b - a).2, -(D * (b - a).1)), D * (b - a).2 * a.1 + -(D * (b - a).1) * a.2),
    ((D * (c - b).2, -(D * (c - b).1)), D * (c - b).2 * a.1 + -(D * (c - b).1) * a.2 + D ^ 2)],
    ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro h (rfl | rfl | rfl)
    exacts [hasTemplateSlope_perp hca _, hasTemplateSlope_perp hba _, hasTemplateSlope_perp hcb _]
  rw [hDdef] at hD
  simp only [Prod.fst_sub, Prod.snd_sub] at hDdef ⊢
  have hD2 : 0 < D ^ 2 := by positivity
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_halfPlanes _)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    simp only [halfPlanes, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
      forall_eq_or_imp, forall_eq]
    rcases hp with rfl | rfl | rfl
    · exact ⟨le_rfl, le_rfl, by nlinarith⟩
    · exact ⟨by linear_combination sq_nonneg D + (-D) * hDdef, le_of_eq (by ring),
        by linear_combination D * hDdef⟩
    · exact ⟨le_of_eq (by ring), by linear_combination sq_nonneg D + (-D) * hDdef,
        by linear_combination D * hDdef⟩
  · intro p hp
    simp only [halfPlanes, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
      forall_eq_or_imp, forall_eq] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    have key : ∀ x : ℝ, D * x ≥ 0 → 0 ≤ x / D := fun x hx => by
      rw [show x / D = D * x / D ^ 2 by field_simp]; exact div_nonneg hx hD2.le
    have hα := key ((p.1 - a.1) * (c.2 - a.2) - (p.2 - a.2) * (c.1 - a.1)) (by nlinarith)
    have hβ := key ((b.1 - a.1) * (p.2 - a.2) - (b.2 - a.2) * (p.1 - a.1)) (by nlinarith)
    have hγ := key (D - ((p.1 - a.1) * (c.2 - a.2) - (p.2 - a.2) * (c.1 - a.1)) -
      ((b.1 - a.1) * (p.2 - a.2) - (b.2 - a.2) * (p.1 - a.1))) (by nlinarith)
    have := mem_convexHull_of_sum (s := {a, b, c}) ![_, _, _] ![a, b, c]
      (by intro i; fin_cases i; exacts [hγ, hα, hβ])
      (by simp [Fin.sum_univ_three]; field_simp; ring) (by intro i; fin_cases i <;> simp)
    convert this using 1
    simp only [Fin.sum_univ_three]
    ext <;> simp <;> field_simp
    · linear_combination (a.1 - p.1) * hDdef
    · linear_combination (a.2 - p.2) * hDdef

/-- D9.16.1 (rectangles). A rectangle with template sides is cut out by four half-planes with
template normals. -/
theorem rectangle_eq_halfPlanes {a u v : ℝ × ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u.1 * v.1 + u.2 * v.2 = 0) (hsu : HasTemplateSlope u) (hsv : HasTemplateSlope v) :
    ∃ H : List ((ℝ × ℝ) × ℝ), (∀ h ∈ H, HasTemplateSlope h.1) ∧
      convexHull ℝ {a, a + u, a + u + v, a + v} = halfPlanes H := by
  obtain ⟨D, hDdef⟩ : ∃ D, u.1 * v.2 - u.2 * v.1 = D := ⟨_, rfl⟩
  have hD2 : 0 < D ^ 2 := by
    have hu2 : 0 < u.1 ^ 2 + u.2 ^ 2 := by
      by_contra h; exact hu (Prod.ext (by simp; nlinarith) (by simp; nlinarith))
    have hv2 : 0 < v.1 ^ 2 + v.2 ^ 2 := by
      by_contra h; exact hv (Prod.ext (by simp; nlinarith) (by simp; nlinarith))
    have : D ^ 2 = (u.1 ^ 2 + u.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2) := by
      rw [← hDdef]; linear_combination (-(u.1 * v.1 + u.2 * v.2)) * huv
    rw [this]; positivity
  have hD0 : D ≠ 0 := by rintro rfl; simp at hD2
  refine ⟨[((-D * v.2, -(-D * v.1)), -D * v.2 * a.1 + -(-D * v.1) * a.2),
    ((D * v.2, -(D * v.1)), D * v.2 * a.1 + -(D * v.1) * a.2 + D ^ 2),
    ((D * u.2, -(D * u.1)), D * u.2 * a.1 + -(D * u.1) * a.2),
    ((-D * u.2, -(-D * u.1)), -D * u.2 * a.1 + -(-D * u.1) * a.2 + D ^ 2)], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro h (rfl | rfl | rfl | rfl) <;> apply hasTemplateSlope_perp <;> assumption
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_halfPlanes _)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    simp only [halfPlanes, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
      forall_eq_or_imp, forall_eq]
    rcases hp with rfl | rfl | rfl | rfl <;> try simp only [Prod.fst_add, Prod.snd_add]
    all_goals refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first
      | nlinarith
      | linear_combination sq_nonneg D + (-D) * hDdef
      | linear_combination sq_nonneg D + D * hDdef
      | linear_combination (-D) * hDdef
      | linear_combination D * hDdef
  · intro p hp
    simp only [halfPlanes, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
      forall_eq_or_imp, forall_eq] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have key : ∀ x : ℝ, D * x ≥ 0 → 0 ≤ x / D := fun x hx => by
      rw [show x / D = D * x / D ^ 2 by field_simp]; exact div_nonneg hx hD2.le
    set α := ((p.1 - a.1) * v.2 - (p.2 - a.2) * v.1) / D with hαdef
    set β := (u.1 * (p.2 - a.2) - u.2 * (p.1 - a.1)) / D with hβdef
    have hα : 0 ≤ α := key _ (by nlinarith)
    have hα' : 0 ≤ 1 - α := by
      rw [show 1 - α = (D - ((p.1 - a.1) * v.2 - (p.2 - a.2) * v.1)) / D by
        rw [hαdef]; field_simp]
      exact key _ (by nlinarith)
    have hβ : 0 ≤ β := key _ (by nlinarith)
    have hβ' : 0 ≤ 1 - β := by
      rw [show 1 - β = (D - (u.1 * (p.2 - a.2) - u.2 * (p.1 - a.1))) / D by
        rw [hβdef]; field_simp]
      exact key _ (by nlinarith)
    have := mem_convexHull_of_sum (s := {a, a + u, a + u + v, a + v})
      ![(1 - α) * (1 - β), α * (1 - β), α * β, (1 - α) * β] ![a, a + u, a + u + v, a + v]
      (by intro i; fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val] <;> positivity)
      (by simp [Fin.sum_univ_four]; ring)
      (by intro i; fin_cases i <;> simp)
    convert this using 1
    simp only [Fin.sum_univ_four]
    ext <;> simp [hαdef, hβdef] <;> field_simp
    · linear_combination (a.1 - p.1) * D * hDdef
    · linear_combination (a.2 - p.2) * D * hDdef

/-- D9.16.1. A template piece is a finite intersection of half-planes with template normals. -/
theorem exists_halfPlanes_of_isTemplatePiece {P : Set (ℝ × ℝ)} (hP : IsTemplatePiece P) :
    ∃ H : List ((ℝ × ℝ) × ℝ), (∀ h ∈ H, HasTemplateSlope h.1) ∧ P = halfPlanes H := by
  rcases hP with ⟨a, u, v, hu, hv, huv, hsu, hsv, rfl⟩ | ⟨a, b, c, hD, hba, hcb, hac, rfl⟩
  · exact rectangle_eq_halfPlanes hu hv huv hsu hsv
  · exact triangle_eq_halfPlanes hba hcb hac hD

/-! ## D9.16.1 Rounding to integer half-planes -/

/-- On integers, `t s ≤ c` is `ε s ≤ m` for some `ε ∈ {-1, 0, 1}` and integer `m`. -/
theorem exists_int_le_iff (t c : ℝ) :
    ∃ ε m : ℤ, |ε| ≤ 1 ∧ ∀ s : ℤ, (t * s ≤ c ↔ ε * s ≤ m) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · refine ⟨-1, ⌊c / -t⌋, by norm_num, fun s => ?_⟩
    rw [Int.le_floor, le_div_iff₀ (by linarith)]
    push_cast
    constructor <;> intro h <;> nlinarith
  · by_cases hc : 0 ≤ c
    · exact ⟨0, 0, by norm_num, fun s => by simp [hc]⟩
    · exact ⟨0, -1, by norm_num, fun s => by simp [hc]⟩
  · refine ⟨1, ⌊c / t⌋, by norm_num, fun s => ?_⟩
    rw [one_mul, Int.le_floor, le_div_iff₀ ht, mul_comm]

/-- D9.16.1. On integer points, a half-plane with template normal is an integer half-plane
`σ₁ x + σ₂ y ≤ m` with `σᵢ ∈ {-1, 0, 1}` (rounding is independent of `y` since `ε y ∈ ℤ`). -/
theorem exists_int_halfPlane {w : ℝ × ℝ} (hw : HasTemplateSlope w) (c : ℝ) :
    ∃ k : ℤ × ℤ × ℤ, (|k.1| ≤ 1 ∧ |k.2.1| ≤ 1) ∧
      ∀ z : ℤ × ℤ, (w.1 * z.1 + w.2 * z.2 ≤ c ↔ k.1 * z.1 + k.2.1 * z.2 ≤ k.2.2) := by
  rcases hw with h | h | h | h
  · obtain ⟨ε, m, hε, hs⟩ := exists_int_le_iff w.1 c
    exact ⟨(ε, 0, m), ⟨hε, by simp⟩, fun z => by simpa [h] using hs z.1⟩
  · obtain ⟨ε, m, hε, hs⟩ := exists_int_le_iff w.2 c
    exact ⟨(0, ε, m), ⟨by simp, hε⟩, fun z => by simpa [h] using hs z.2⟩
  · obtain ⟨ε, m, hε, hs⟩ := exists_int_le_iff w.1 c
    refine ⟨(ε, ε, m), ⟨hε, hε⟩, fun z => ?_⟩
    have := hs (z.1 + z.2)
    push_cast at this
    simp only [h]
    rw [← mul_add, this, mul_add]
  · obtain ⟨ε, m, hε, hs⟩ := exists_int_le_iff w.1 c
    refine ⟨(ε, -ε, m), ⟨hε, by rwa [abs_neg]⟩, fun z => ?_⟩
    have := hs (z.1 - z.2)
    push_cast at this
    simp only [h]
    rw [show w.1 * z.1 + -w.1 * z.2 = w.1 * (z.1 - z.2) by ring, this]
    constructor <;> intro h' <;> linarith

/-- D9.16.1. The lattice points of an intersection of half-planes with template normals form an
integer octagon. -/
theorem exists_octagon (H : List ((ℝ × ℝ) × ℝ)) (hH : ∀ h ∈ H, HasTemplateSlope h.1) :
    ∃ K : List (ℤ × ℤ × ℤ), (∀ k ∈ K, |k.1| ≤ 1 ∧ |k.2.1| ≤ 1) ∧
      ∀ z : ℤ × ℤ, (((z.1 : ℝ), (z.2 : ℝ)) ∈ halfPlanes H ↔
        ∀ k ∈ K, k.1 * z.1 + k.2.1 * z.2 ≤ k.2.2) := by
  induction H with
  | nil => exact ⟨[], by simp, fun z => by simp [halfPlanes]⟩
  | cons h H ih =>
    obtain ⟨K, hK, hKz⟩ := ih fun h' hh' => hH h' (List.mem_cons_of_mem _ hh')
    obtain ⟨k, hk, hkz⟩ := exists_int_halfPlane (hH h List.mem_cons_self) h.2
    refine ⟨k :: K, fun k' hk' => ?_, fun z => ?_⟩
    · rcases List.mem_cons.1 hk' with rfl | hk'
      exacts [hk, hK k' hk']
    · have := hKz z
      simp only [halfPlanes, Set.mem_ofPred_eq, List.mem_cons, forall_eq_or_imp] at this ⊢
      rw [hkz z, this]

/-! ## Ambient dilations and edge counts -/

theorem ambientDilation_zero (T : Finset (ℤ × ℤ)) : ambientDilation T 0 = T := by
  ext p
  rw [mem_ambientDilation]
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    simp only [CharP.cast_eq_zero, abs_nonpos_iff, sub_eq_zero] at h1 h2
    rwa [show p = x from Prod.ext h1 h2]
  · exact fun hp => ⟨p, hp, by simp, by simp⟩

/-- `T_{j+1} = T_j + [-1, 1]²`. -/
theorem ambientDilation_succ (T : Finset (ℤ × ℤ)) (j : ℕ) :
    ambientDilation T (j + 1) = ambientDilation T j + Icc (-1, -1) (1, 1) := by
  ext p
  rw [mem_ambientDilation, mem_add_Icc_one]
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    rw [abs_le] at h1 h2
    push_cast at h1 h2
    refine ⟨(x.1 + max (-(j : ℤ)) (min (p.1 - x.1) j), x.2 + max (-(j : ℤ)) (min (p.2 - x.2) j)),
      mem_ambientDilation.2 ⟨x, hx, ?_, ?_⟩, ?_, ?_⟩ <;> simp only [abs_le] <;> omega
  · rintro ⟨y, hy, h1, h2⟩
    obtain ⟨x, hx, h3, h4⟩ := mem_ambientDilation.1 hy
    rw [abs_le] at h1 h2 h3 h4
    exact ⟨x, hx, by rw [abs_le]; push_cast; omega, by rw [abs_le]; push_cast; omega⟩

theorem ambientDilation_biUnion {ι : Type*} (s : Finset ι) (S : ι → Finset (ℤ × ℤ)) (j : ℕ) :
    ambientDilation (s.biUnion S) j = s.biUnion fun i => ambientDilation (S i) j := by
  ext p
  simp only [mem_ambientDilation, mem_biUnion]
  constructor
  · rintro ⟨x, ⟨i, hi, hx⟩, h⟩; exact ⟨i, hi, x, hx, h⟩
  · rintro ⟨i, hi, x, hx, h⟩; exact ⟨x, ⟨i, hi, hx⟩, h⟩

theorem ambientDilation_empty (j : ℕ) : ambientDilation ∅ j = ∅ := by
  simp [ambientDilation]

/-- Each site has at most four lattice neighbours: `|∂(A, B)| ≤ 4 |B|`. -/
theorem card_interedges_le (A B : Finset (ℤ × ℤ)) : #(squareLattice.interedges A B) ≤ 4 * #B := by
  refine (card_le_mul_card_image (f := Prod.snd) _ 4 fun y _ => ?_).trans
    (Nat.mul_le_mul_left _ (card_le_card fun y hy => ?_))
  · refine (card_le_card_of_injOn Prod.fst
      (t := {y + (1, 0), y - (1, 0), y + (0, 1), y - (0, 1)}) (fun e he => ?_)
      (fun e he e' he' h => Prod.ext h ((mem_filter.1 he).2.trans (mem_filter.1 he').2.symm))).trans
      card_le_four
    have hy : e.2 = y := (mem_filter.1 he).2
    obtain ⟨-, -, hadj⟩ := (SimpleGraph.mem_interedges_iff _).1 (mem_filter.1 he).1
    subst hy
    simp only [squareLattice, SimpleGraph.boxProd_adj, SimpleGraph.hasse_adj,
      Order.covBy_iff_add_one_eq] at hadj
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    omega
  · obtain ⟨e, he, rfl⟩ := mem_image.1 hy
    exact ((SimpleGraph.mem_interedges_iff _).1 he).2.1

/-- Lattice neighbours are within sup-distance one, so `x ∈ T`, `x ~ y` gives `y ∈ T_1`. -/
theorem mem_ambientDilation_one_of_adj {T : Finset (ℤ × ℤ)} {x y : ℤ × ℤ} (hx : x ∈ T)
    (h : squareLattice.Adj x y) : y ∈ ambientDilation T 1 := by
  simp only [squareLattice, SimpleGraph.boxProd_adj, SimpleGraph.hasse_adj,
    Order.covBy_iff_add_one_eq] at h
  exact mem_ambientDilation.2 ⟨x, hx, by rw [abs_le]; push_cast; omega,
    by rw [abs_le]; push_cast; omega⟩

/-! ## D9.16 One piece -/

/-- The lattice sample of a piece of sup-norm diameter `≤ s₀` has diameter `≤ s₀`. -/
theorem hasDiam_of_ediam {P : Set (ℝ × ℝ)} {s₀ : ℕ} (hP : Metric.ediam P ≤ s₀)
    {S : Finset (ℤ × ℤ)} (hS : ∀ z ∈ S, ((z.1 : ℝ), (z.2 : ℝ)) ∈ P) : HasDiam S s₀ := by
  intro p hp q hq
  have h := (Metric.edist_le_ediam_of_mem (hS p hp) (hS q hq)).trans hP
  rw [Prod.edist_eq, max_le_iff, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
    ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)] at h
  simp only at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem hasDiam_ambientDilation {S : Finset (ℤ × ℤ)} {d : ℤ} (h : HasDiam S d) (j : ℕ) :
    HasDiam (ambientDilation S j) (d + 2 * j) := by
  induction j with
  | zero => simpa [ambientDilation_zero] using h
  | succ j ih =>
    rw [ambientDilation_succ]
    convert ih.add_Icc using 1
    push_cast; ring

/-- D9.16 (one piece: row intervals and dilations). For one piece `P` with lattice sample `S`
and its dilation `S_j`: (i) every row of `S_j` is an integer interval and its nonempty rows are
consecutive; (ii) the endpoints move by at most one between consecutive rows; (iii) the layer
`|S_{j+1} \ S_j|` and the edge boundary of `S_j` are `≤ C (s₀ + j + 1)`.
2D only: rows of a planar polygon whose sides have slopes `0, ∞, ±1`. -/
theorem step_9_16 {P : Set (ℝ × ℝ)} {s₀ : ℕ} (hP : IsTemplatePiece P)
    (hdiam : Metric.ediam P ≤ s₀) {S : Finset (ℤ × ℤ)}
    (hS : ∀ z, z ∈ S ↔ ((z.1 : ℝ), (z.2 : ℝ)) ∈ P) (j : ℕ) :
    (S.Nonempty → ∃ y₀ y₁ ℓ r, IsStaircase (ambientDilation S j) y₀ y₁ ℓ r) ∧
      #(ambientDilation S (j + 1) \ ambientDilation S j) ≤ 16 * (s₀ + j + 1) ∧
      #(GraphDomain.edgeBoundary squareLattice (ambientDilation S (j + 1))
        (ambientDilation S j)) ≤ 64 * (s₀ + j + 1) := by
  -- D9.16.1: `P` is an intersection of template half-planes; on `ℤ²` an integer octagon
  obtain ⟨H, hH, rfl⟩ := exists_halfPlanes_of_isTemplatePiece hP
  obtain ⟨K, hK, hKz⟩ := exists_octagon H hH
  -- D9.16.2–3: rows are intervals, consecutive, with endpoints moving by at most one
  have hstair : S.Nonempty → ∀ j, ∃ y₀ y₁ ℓ r, IsStaircase (ambientDilation S j) y₀ y₁ ℓ r := by
    intro hne j
    induction j with
    | zero =>
      rw [ambientDilation_zero]
      exact isStaircase_of_octagon K hK (fun z => (hS z).trans (hKz z)) hne
    | succ j ih =>
      -- D9.16.4: the dilation by one more step is again a staircase
      obtain ⟨y₀, y₁, ℓ, r, h⟩ := ih
      rw [ambientDilation_succ]
      exact ⟨_, _, h.add_Icc⟩
  have hdS : HasDiam S s₀ := hasDiam_of_ediam hdiam fun z hz => (hS z).1 hz
  -- D9.16.5: the layer, at most four sites per old row and two new rows of length `≤ s₀+2j+3`
  have hlayer : #(ambientDilation S (j + 1) \ ambientDilation S j) ≤ 16 * (s₀ + j + 1) := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [ambientDilation_empty]
    obtain ⟨y₀, y₁, ℓ, r, h⟩ := hstair hne j
    have h1 := h.sub_le_of_hasDiam (hasDiam_ambientDilation hdS j)
    have h2 := h.card_add_Icc_sdiff_le (d := s₀ + 2 * (j + 1 : ℕ))
      (by rw [← ambientDilation_succ]; exact hasDiam_ambientDilation hdS (j + 1))
    rw [← ambientDilation_succ] at h2
    refine h2.trans ?_
    push_cast at h1 ⊢
    omega
  refine ⟨fun hne => hstair hne j, hlayer, ?_⟩
  exact (card_interedges_le _ _).trans (by omega)

/-! ## D9.17 Mixed squares -/

/-- The lattice samples `S_a = P_a ∩ ℤ²` of the pieces of a template. -/
theorem exists_pieces {Ctpl : ℝ} {n s₀ : ℕ} {T : Finset (ℤ × ℤ)} (hT : IsTemplate Ctpl n s₀ T) :
    ∃ (N₀ : ℕ) (P : Fin N₀ → Set (ℝ × ℝ)) (S : Fin N₀ → Finset (ℤ × ℤ)), 1 ≤ N₀ ∧
      Ctpl * N₀ * (s₀ + 1) ≤ n ∧ (∀ i, IsTemplatePiece (P i) ∧ Metric.ediam (P i) ≤ s₀) ∧
      (∀ i z, z ∈ S i ↔ ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i) ∧ T = univ.biUnion S := by
  classical
  obtain ⟨-, -, -, N₀, P, hN₀, hP, hTP, hn, -⟩ := hT
  have hmem : ∀ z, z ∈ T ↔ ∃ i, ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i := fun z => by
    rw [← mem_coe, hTP, Set.mem_iUnion]; rfl
  refine ⟨N₀, P, fun i => T.filter fun z => ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i, hN₀, hn, hP,
    fun i z => ?_, ?_⟩
  · rw [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(hmem z).2 ⟨i, h⟩, h⟩⟩
  · ext z
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    exact ⟨fun h => ((hmem z).1 h).imp fun i hi => ⟨h, hi⟩, fun ⟨i, h, _⟩ => h⟩

theorem card_biUnion_le_real {ι : Type*} (s : Finset ι) (f : ι → Finset (ℤ × ℤ)) :
    (#(s.biUnion f) : ℝ) ≤ ∑ i ∈ s, (#(f i) : ℝ) := by
  exact_mod_cast card_biUnion_le

/-- D9.17 (mixed squares). In the partition of `ℤ²` into dyadic squares of side `u = 2^k`, the
number of squares containing a site of a dilated piece `S_j` and a site outside it is
`≤ 6 ((s₀ + 2j)/u + 2)`. Consequently, for `T`, `T_j` and `T_j \ T` (`j ≤ s₀`), the number of
mixed squares of side `u` is `≤ C (N₀ + n/u)`.
2D only: counts rows and columns of planar staircases. -/
theorem step_9_17 {Ctpl : ℝ} (hC : 1 ≤ Ctpl) {n s₀ N₀ : ℕ} {P : Fin N₀ → Set (ℝ × ℝ)}
    {S : Fin N₀ → Finset (ℤ × ℤ)} (hP : ∀ i, IsTemplatePiece (P i) ∧ Metric.ediam (P i) ≤ s₀)
    (hS : ∀ i z, z ∈ S i ↔ ((z.1 : ℝ), (z.2 : ℝ)) ∈ P i) (hn : Ctpl * N₀ * (s₀ + 1) ≤ n)
    {j : ℕ} (hj : j ≤ s₀) (k : ℕ) :
    (∀ i, (#(mixedIndices (ambientDilation (S i) j) k) : ℝ) ≤ 6 * ((s₀ + 2 * j) / 2 ^ k + 2)) ∧
      (#(mixedIndices (univ.biUnion S) k) : ℝ) ≤ 24 * (N₀ + n / 2 ^ k) ∧
      (#(mixedIndices (ambientDilation (univ.biUnion S) j) k) : ℝ) ≤ 24 * (N₀ + n / 2 ^ k) ∧
      (#(mixedIndices (ambientDilation (univ.biUnion S) j \ univ.biUnion S) k) : ℝ) ≤
        24 * (N₀ + n / 2 ^ k) := by
  have hu : (0 : ℝ) < 2 ^ k := by positivity
  -- D9.17.1–2: one dilated piece is a staircase of diameter `s₀ + 2j`
  have piece : ∀ i j, (#(mixedIndices (ambientDilation (S i) j) k) : ℝ) ≤
      6 * ((s₀ + 2 * j) / 2 ^ k + 2) := by
    intro i j
    rcases (S i).eq_empty_or_nonempty with he | hne
    · rw [he, ambientDilation_empty]
      simp only [mixedIndices, image_empty, filter_empty, card_empty, Nat.cast_zero]
      positivity
    obtain ⟨y₀, y₁, ℓ, r, h⟩ := (step_9_16 (hP i).1 (hP i).2 (hS i) j).1 hne
    have := h.card_mixedIndices_le
      (hasDiam_ambientDilation (hasDiam_of_ediam (hP i).2 fun z hz => (hS i z).1 hz) j) k
    push_cast at this
    exact this
  -- D9.17.3: a square mixed for a union is mixed for a piece, one mixed for `T_j \ T` is mixed
  -- for `T_j` or for `T`
  have hdil : ∀ j, (#(mixedIndices (ambientDilation (univ.biUnion S) j) k) : ℝ) ≤
      N₀ * (6 * ((s₀ + 2 * j) / 2 ^ k + 2)) := by
    intro j
    rw [ambientDilation_biUnion]
    refine (Nat.cast_le.2 (card_le_card (mixedIndices_biUnion_subset _ _ _))).trans
      ((card_biUnion_le_real _ _).trans ?_)
    refine (sum_le_sum fun i _ => piece i j).trans ?_
    simp
  have hNs : (N₀ : ℝ) * s₀ ≤ n := by
    have : (N₀ : ℝ) * s₀ ≤ Ctpl * N₀ * (s₀ + 1) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hC) (Nat.cast_nonneg (α := ℝ) N₀))
        (by positivity : (0 : ℝ) ≤ s₀ + 1), Nat.cast_nonneg (α := ℝ) N₀]
    linarith
  have hNs' : (N₀ : ℝ) * s₀ / 2 ^ k ≤ n / 2 ^ k := div_le_div_of_nonneg_right hNs hu.le
  have hj' : (j : ℝ) ≤ s₀ := by exact_mod_cast hj
  have h0 := hdil 0
  rw [ambientDilation_zero] at h0
  have hjj := hdil j
  have e1 : (N₀ : ℝ) * (6 * ((s₀ + 2 * j) / 2 ^ k + 2)) ≤ 18 * (N₀ * s₀ / 2 ^ k) + 12 * N₀ := by
    have : (s₀ + 2 * j : ℝ) / 2 ^ k ≤ 3 * s₀ / 2 ^ k := div_le_div_of_nonneg_right (by linarith)
      hu.le
    have h3 : (N₀ : ℝ) * (3 * s₀ / 2 ^ k) = 3 * (N₀ * s₀ / 2 ^ k) := by ring
    nlinarith [Nat.cast_nonneg (α := ℝ) N₀]
  have e0 : (N₀ : ℝ) * (6 * ((s₀ + 2 * (0 : ℕ)) / 2 ^ k + 2)) =
      6 * (N₀ * s₀ / 2 ^ k) + 12 * N₀ := by push_cast; ring
  refine ⟨fun i => piece i j, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · refine (Nat.cast_le.2 ((card_le_card (mixedIndices_sdiff_subset _ _ k)).trans
      (card_union_le _ _))).trans ?_
    push_cast
    nlinarith

/-! ## D9.18 Covering and shell entropy -/

theorem ambientEDist_mono {Y Y' Z : Finset (ℤ × ℤ)} (h : Y ⊆ Y') :
    ambientEDist Y' Z ≤ ambientEDist Y Z := by
  simp only [ambientEDist]; exact biInf_mono fun x hx => h hx

/-- `dist_∞(T, Z) > c + j` gives `dist_∞(T_j, Z) > c`. -/
theorem ofReal_lt_ambientEDist_dilation {T Z : Finset (ℤ × ℤ)} {c : ℝ} (hc : 0 ≤ c) {j : ℕ}
    (h : ENNReal.ofReal (c + j) < ambientEDist T Z) :
    ENNReal.ofReal c < ambientEDist (ambientDilation T j) Z := by
  simp only [ambientEDist, ← Finset.inf_eq_iInf] at h ⊢
  rw [Finset.lt_inf_iff ENNReal.ofReal_lt_top] at h ⊢
  intro x hx
  obtain ⟨t, ht, h1, h2⟩ := mem_ambientDilation.1 hx
  have hd : edist t x ≤ j := by
    rw [edist_dist, Prod.dist_eq, Int.dist_eq, Int.dist_eq, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal (max_le ?_ ?_)
    · rw [abs_sub_comm]; exact_mod_cast h1
    · rw [abs_sub_comm]; exact_mod_cast h2
  have := (h t ht).trans_le (Metric.infEDist_le_infEDist_add_edist.trans (add_le_add le_rfl hd))
  rw [ENNReal.ofReal_add hc (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.add_lt_add_iff_right (ENNReal.natCast_ne_top j)] at this
  exact this

theorem isIntRect_dyadicSquare (k : ℕ) (z : ℤ × ℤ) : IsIntRect (dyadicSquare k z) := by
  refine ⟨_, _, ?_, rfl⟩
  have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  exact Prod.le_def.2 ⟨by simp only; omega, by simp only; omega⟩

theorem boxSize_dyadicSquare (k : ℕ) (z : ℤ × ℤ) : boxSize (dyadicSquare k z) = 2 ^ k := by
  have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  rw [dyadicSquare, boxSize_Icc (Prod.le_def.2 ⟨by simp only; omega, by simp only; omega⟩)]
  have h (a : ℤ) : (2 ^ k * a + (2 ^ k - 1) + 1 - 2 ^ k * a).toNat = 2 ^ k := by
    rw [show 2 ^ k * a + (2 ^ k - 1) + 1 - 2 ^ k * a = ((2 ^ k : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  simp only [h, max_self]

theorem rpow_two_pow_comm (k : ℕ) (e : ℝ) : ((2 : ℝ) ^ k) ^ e = ((2 : ℝ) ^ e) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- D9.18 (covering and shell entropy), the covering core. Let `Y ⊂ ℤ²` be finite and `2^K` a
cap side with `|Y| ≤ B 2^K`, at most `B / u` mixed dyadic squares of each side `u = 2^{k+1} ≤ 2^K`,
and `dist_∞(Y, Z) > D₀ 2^K` (each square of side `≤ 2^K` inside `Y` is safe at its own size).
If `F_box(r) ≤ C_e r^{1+e}` for `r ≥ 1`, `e > 0`, then
`S_Ω(A ∩ Y) ≤ C_e (1 + 2/(2^e - 1)) B (2^K)^e`.
2D only: `F_box` and safety are statements about rectangles of `ℤ²`. -/
theorem step_9_18 {q R : ℕ} {J Δ e Ce D₀ : ℝ} (he : 0 < e) (hCe : 0 ≤ Ce)
    (hD₀ : 2 * R + 10 < D₀) (hF : ∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e))
    {Λ : Finset (ℤ × ℤ)}
    {Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ}
    (hΦ : IsAdmissible Λ R J Φ) {Ω : Reg (Qudits q) Λ → ℂ} (hΩ : star Ω ⬝ᵥ Ω = 1) {E₀ : ℝ}
    (hE : hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω) (hgap : HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Λ) (Y : Finset (ℤ × ℤ)) (K : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hY : (#Y : ℝ) ≤ B * 2 ^ K)
    (hmix : ∀ k < K, (#(mixedIndices Y (k + 1)) : ℝ) ≤ B / 2 ^ (k + 1))
    (hclear : ENNReal.ofReal (D₀ * 2 ^ K) < ambientEDist Y (cutEndpoints Λ A)) :
    (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ Y ⊆ Λ) ≤
      Ce * (1 + 2 / (2 ^ e - 1)) * B * ((2 : ℝ) ^ K) ^ e := by
  set cover := dyadicCover Y K
  have hD₀' : 0 ≤ D₀ := by linarith [Nat.cast_nonneg (α := ℝ) R]
  -- D9.18.1: the maximal dyadic squares of side `≤ 2^K` inside `Y` partition `Y`
  have hcov : cover.biUnion (fun c => dyadicSquare c.1 c.2) = Y := biUnion_dyadicCover
  have hset : A ∩ Y = ∅ ∪ cover.biUnion fun c => A ∩ dyadicSquare c.1 c.2 := by
    ext x
    rw [empty_union, mem_inter, ← hcov, mem_biUnion, mem_biUnion]
    simp only [mem_inter]
    exact ⟨fun ⟨hx, c, hc, hxc⟩ => ⟨c, hc, hx, hxc⟩, fun ⟨c, hc, hx, hxc⟩ => ⟨hx, c, hc, hxc⟩⟩
  have hdisj : (cover : Set (ℕ × (ℤ × ℤ))).PairwiseDisjoint
      fun c => A ∩ dyadicSquare c.1 c.2 :=
    pairwiseDisjoint_dyadicCover.mono fun c => inter_subset_right
  -- D9.18.4: every square of the cover is safe at its own size
  have hbox : ∀ c ∈ cover, (pureState Ω hΩ).regionEntropy
      (inter_subset_left.trans hA : A ∩ dyadicSquare c.1 c.2 ⊆ Λ) ≤
        Ce * ((2 : ℝ) ^ c.1) ^ (1 + e) := by
    intro c hc
    obtain ⟨hcK, hcY⟩ := mem_dyadicCover hc
    have hsafe : IsSafe D₀ Λ A (dyadicSquare c.1 c.2) := by
      refine lt_of_le_of_lt ?_ (hclear.trans_le (ambientEDist_mono hcY))
      rw [boxSize_dyadicSquare]
      push_cast
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hcK) hD₀')
    have := (le_F_box hD₀ hΦ hΩ hE hgap hA (isIntRect_dyadicSquare c.1 c.2) hsafe
      (boxSize_dyadicSquare c.1 c.2).le).trans (hF _ Nat.one_le_two_pow)
    push_cast at this
    exact this
  -- the sum by level: `N_k` maximal squares of side `2^k`
  have hlev : ∀ c ∈ cover, c.1 ∈ Finset.range (K + 1) := fun c hc =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (mem_dyadicCover hc).1)
  set N : ℕ → ℝ := fun k => (#(cover.filter (·.1 = k)) : ℝ)
  have hsum : ∑ c ∈ cover, Ce * ((2 : ℝ) ^ c.1) ^ (1 + e) =
      ∑ k ∈ Finset.range (K + 1), N k * (Ce * ((2 : ℝ) ^ k) ^ (1 + e)) := by
    rw [← sum_fiberwise_of_maps_to hlev]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], sum_const, nsmul_eq_mul]
  have hpow : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (1 + e) = 2 ^ k * ((2 : ℝ) ^ k) ^ e := fun k => by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  have h2e : 1 < (2 : ℝ) ^ e := Real.one_lt_rpow (by norm_num) he
  -- D9.18.2: at the cap, `N_K 4^K ≤ |Y| ≤ B 2^K`
  have hcap : N K * (Ce * ((2 : ℝ) ^ K) ^ (1 + e)) ≤ Ce * B * ((2 : ℝ) ^ K) ^ e := by
    have h1 : N K * 4 ^ K ≤ B * 2 ^ K := by
      have := Nat.cast_le (α := ℝ) |>.2 (card_dyadicCover_eq_mul_le (Y := Y) (K := K))
      push_cast at this
      exact this.trans hY
    have h4 : (4 : ℝ) ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
    rw [h4] at h1
    have h1' : N K * 2 ^ K ≤ B :=
      le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < 2 ^ K)
    rw [hpow]
    have : 0 ≤ Ce * ((2 : ℝ) ^ K) ^ e := by positivity
    nlinarith
  -- D9.18.3: below the cap the parents are mixed: `N_k ≤ 4 · B/2^{k+1}`
  have hbelow : ∀ k ∈ Finset.range K, N k * (Ce * ((2 : ℝ) ^ k) ^ (1 + e)) ≤
      2 * Ce * B * ((2 : ℝ) ^ e) ^ k := by
    intro k hk
    have hk := Finset.mem_range.1 hk
    have h0 := Nat.cast_le (α := ℝ) |>.2 (card_dyadicCover_lt (Y := Y) hk)
    push_cast at h0
    have h1 : N k ≤ 4 * (B / 2 ^ (k + 1)) := h0.trans (by linarith [hmix k hk])
    have h2 : 4 * (B / 2 ^ (k + 1)) * 2 ^ k = 2 * B := by
      rw [pow_succ]; field_simp; ring
    rw [hpow, ← rpow_two_pow_comm]
    have : 0 ≤ Ce * ((2 : ℝ) ^ k) ^ e := by positivity
    have hNk : N k * 2 ^ k ≤ 2 * B := h2 ▸ mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith
  -- geometric sum, `C'_e` depending on `e` through `(2^e - 1)^{-1}`
  have hgeom : ∑ k ∈ Finset.range K, ((2 : ℝ) ^ e) ^ k ≤ ((2 : ℝ) ^ K) ^ e / (2 ^ e - 1) := by
    rw [geom_sum_eq h2e.ne', rpow_two_pow_comm]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ Y ⊆ Λ)
      = (pureState Ω hΩ).regionEntropy (union_subset (empty_subset Λ)
          (biUnion_subset.2 fun c _ => inter_subset_left.trans hA)) :=
        (pureState Ω hΩ).regionEntropy_congr hset _ _
    _ ≤ (pureState Ω hΩ).regionEntropy (empty_subset Λ) +
          ∑ c ∈ cover, (pureState Ω hΩ).regionEntropy
            (inter_subset_left.trans hA : A ∩ dyadicSquare c.1 c.2 ⊆ Λ) :=
        regionEntropy_union_biUnion_le _ (empty_subset Λ) cover
          (fun c => inter_subset_left.trans hA) (fun _ _ => disjoint_empty_left _) hdisj
    _ ≤ ∑ c ∈ cover, Ce * ((2 : ℝ) ^ c.1) ^ (1 + e) := by
        rw [MState.regionEntropy_empty, zero_add]; exact sum_le_sum hbox
    _ = ∑ k ∈ Finset.range K, N k * (Ce * ((2 : ℝ) ^ k) ^ (1 + e)) +
          N K * (Ce * ((2 : ℝ) ^ K) ^ (1 + e)) := by rw [hsum, sum_range_succ]
    _ ≤ ∑ k ∈ Finset.range K, 2 * Ce * B * ((2 : ℝ) ^ e) ^ k + Ce * B * ((2 : ℝ) ^ K) ^ e :=
        add_le_add (sum_le_sum hbelow) hcap
    _ = 2 * Ce * B * ∑ k ∈ Finset.range K, ((2 : ℝ) ^ e) ^ k + Ce * B * ((2 : ℝ) ^ K) ^ e := by
        rw [mul_sum]
    _ ≤ 2 * Ce * B * (((2 : ℝ) ^ K) ^ e / (2 ^ e - 1)) + Ce * B * ((2 : ℝ) ^ K) ^ e := by
        gcongr
    _ = Ce * (1 + 2 / (2 ^ e - 1)) * B * ((2 : ℝ) ^ K) ^ e := by ring

/-! ## D9.15 Lemma 9.4 -/

theorem ambientDilation_one (X : Finset (ℤ × ℤ)) :
    ambientDilation X 1 = X + Icc (-1, -1) (1, 1) := by
  simp [ambientDilation]

theorem ambientDilation_add_one (T : Finset (ℤ × ℤ)) (j : ℕ) :
    ambientDilation T (j + 1) = ambientDilation (ambientDilation T j) 1 := by
  rw [ambientDilation_succ, ambientDilation_one]

/-- D9.15, first part (from D9.16): `|T| ≤ C n s₀`, the layers `|T_{j+1} \ T_j| ≤ n` and the
boundaries `|∂_{ℤ²} T_j| ≤ 4n` (`j ≤ s₀`), for `C_tpl ≥ 32`. -/
theorem template_geometry {Ctpl : ℝ} (hC : 32 ≤ Ctpl) {n s₀ : ℕ} {T : Finset (ℤ × ℤ)}
    (hT : IsTemplate Ctpl n s₀ T) :
    (#T : ℝ) ≤ 9 * n * s₀ ∧ (∀ j ≤ s₀, #(ambientDilation T (j + 1) \ ambientDilation T j) ≤ n) ∧
      ∀ j ≤ s₀, #(GraphDomain.edgeBoundary squareLattice (ambientDilation T (j + 1))
        (ambientDilation T j)) ≤ 4 * n := by
  have hs₁ : 1 ≤ s₀ := hT.2.1
  obtain ⟨N₀, P, S, -, hn, hP, hS, rfl⟩ := exists_pieces hT
  have h32 : 32 * N₀ * (s₀ + 1) ≤ n := by
    have : (32 : ℝ) * N₀ * (s₀ + 1) ≤ n := le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) (by positivity)) hn
    exact_mod_cast this
  have hlayer : ∀ j ≤ s₀, #(ambientDilation (univ.biUnion S) (j + 1) \
      ambientDilation (univ.biUnion S) j) ≤ n := by
    intro j hj
    have hsub : ambientDilation (univ.biUnion S) (j + 1) \ ambientDilation (univ.biUnion S) j ⊆
        univ.biUnion fun i => ambientDilation (S i) (j + 1) \ ambientDilation (S i) j := by
      intro x hx
      rw [mem_sdiff, ambientDilation_biUnion, ambientDilation_biUnion, mem_biUnion,
        mem_biUnion] at hx
      obtain ⟨⟨i, -, hi⟩, hni⟩ := hx
      exact mem_biUnion.2 ⟨i, mem_univ _, mem_sdiff.2 ⟨hi, fun h => hni ⟨i, mem_univ _, h⟩⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    refine (sum_le_sum fun i _ => (step_9_16 (hP i).1 (hP i).2 (hS i) j).2.1).trans ?_
    rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    calc N₀ * (16 * (s₀ + j + 1)) ≤ N₀ * (32 * (s₀ + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 32 * N₀ * (s₀ + 1) := by ring
      _ ≤ n := h32
  refine ⟨?_, hlayer, fun j hj => (card_interedges_le _ _).trans (by have := hlayer j hj; omega)⟩
  have hcard : #(univ.biUnion S) ≤ N₀ * (2 * s₀ + 1) ^ 2 := by
    refine card_biUnion_le.trans ((sum_le_sum fun i _ =>
      card_le_of_hasDiam (hasDiam_of_ediam (hP i).2 fun z hz => (hS i z).1 hz)).trans ?_)
    rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      show (2 * (s₀ : ℤ) + 1).toNat = 2 * s₀ + 1 by omega]
  have : N₀ * (2 * s₀ + 1) ^ 2 ≤ 9 * n * s₀ := by
    have h1 : (2 * s₀ + 1) ^ 2 ≤ 9 * (s₀ + 1) * s₀ := by nlinarith
    calc N₀ * (2 * s₀ + 1) ^ 2 ≤ N₀ * (9 * (s₀ + 1) * s₀) := Nat.mul_le_mul_left _ h1
      _ = 9 * (N₀ * (s₀ + 1)) * s₀ := by ring
      _ ≤ 9 * n * s₀ := by
          gcongr
          exact le_trans (by rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)) h32
  exact_mod_cast hcard.trans this

/-- A site of `T_j` is not a cut endpoint when `dist_∞(T, Z) > j`. -/
theorem not_mem_cutEndpoints_of_mem_dilation {Λ A T : Finset (ℤ × ℤ)} {j : ℕ}
    (h : ENNReal.ofReal j < ambientEDist T (cutEndpoints Λ A)) {x : ℤ × ℤ}
    (hx : x ∈ ambientDilation T j) : x ∉ cutEndpoints Λ A := by
  intro hxZ
  have := ofReal_lt_ambientEDist_dilation le_rfl (by simpa using h)
  rw [ENNReal.ofReal_zero] at this
  have h0 : ambientEDist (ambientDilation T j) (cutEndpoints Λ A) ≤ 0 :=
    (iInf₂_le x hx).trans (Metric.infEDist_zero_of_mem (mem_coe.2 hxZ)).le
  exact (lt_of_lt_of_le this h0).false

/-- D9.18.6. Near `T` no edge crosses the cut, so the physical boundary of `A ∩ W`, `W ⊆ T_j`,
consists of ambient boundary edges of `W`. -/
theorem edgeBoundary_inter_subset {Λ A T W : Finset (ℤ × ℤ)} {j : ℕ}
    (h : ENNReal.ofReal j < ambientEDist T (cutEndpoints Λ A)) (hW : W ⊆ ambientDilation T j)
    {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : e ∈ OpenAI.edgeBoundary Λ (A ∩ W)) :
    e.1 ∈ A ∩ W ∧ e.2 ∈ A \ W ∧ squareLattice.Adj e.1 e.2 := by
  obtain ⟨h1, h2, hadj⟩ := (SimpleGraph.mem_interedges_iff _).1 he
  obtain ⟨h2Λ, h2A⟩ := mem_sdiff.1 h2
  have hyA : e.2 ∈ A := by
    by_contra hyA
    have hcut : e ∈ OpenAI.edgeBoundary Λ A :=
      (SimpleGraph.mem_interedges_iff _).2 ⟨(mem_inter.1 h1).1, mem_sdiff.2 ⟨h2Λ, hyA⟩, hadj⟩
    exact not_mem_cutEndpoints_of_mem_dilation h (hW (mem_inter.1 h1).2)
      (mem_union_left _ (mem_image_of_mem _ hcut))
  exact ⟨h1, mem_sdiff.2 ⟨hyA, fun hyW => h2A (mem_inter.2 ⟨hyA, hyW⟩)⟩, hadj⟩

/-- D9.15 **Lemma 9.4** (rows, coverings and shell entropy). For `C_tpl` large there is a
numerical `C` such that every template `T` with parameters `(n, s₀)` has `|T| ≤ C n s₀`,
`|T_j \ T_{j-1}| ≤ n` (`1 ≤ j ≤ s₀`), `|∂_{ℤ²} T_j| ≤ C n` (`0 ≤ j ≤ s₀`). If moreover `T` is
separated from the cut and `F_box(r) ≤ C_e r^{1+e}` for all `r ≥ 1` (`0 < e < 1`), then for every
`1 ≤ L ≤ s₀`: `S_Ω(X) ≤ C'_e n s₀^e`, `S_Ω(Q_j) ≤ C'_e n L^e` (`0 ≤ j ≤ L`); the same shell bound
with an extra `n log q` holds for every prefix of all depth rows before one row and a subset of
that row; the physical cuts of `X`, `Q_j`, `A ∩ T_j` (`j ≤ s₀`) have at most `C n` edges.
2D only: templates are unions of planar pieces of slopes `0, ∞, ±1`. -/
theorem lemma_9_4 : Lemma_9_4 := by
  refine ⟨32, fun Ctpl hC => ⟨9, by norm_num, fun n s₀ T hT => ?_, ?_⟩⟩
  · -- D9.16: rows, layers and boundaries of the pieces, summed over the pieces
    obtain ⟨h1, h2, h3⟩ := template_geometry hC hT
    refine ⟨h1, fun j hj1 hj2 => ?_, fun j hj => ?_⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj1
      simpa [add_comm] using h2 i (by omega)
    · have := h3 j hj
      have : (#(GraphDomain.edgeBoundary squareLattice (ambientDilation T (j + 1))
          (ambientDilation T j)) : ℝ) ≤ 4 * n := by exact_mod_cast this
      linarith [Nat.cast_nonneg (α := ℝ) n]
  intro q R J Δ e Ce he he1 hCe
  have hce : 0 < 1 + 2 / ((2 : ℝ) ^ e - 1) := by
    have : 1 < (2 : ℝ) ^ e := Real.one_lt_rpow (by norm_num) he
    have : 0 < 2 / ((2 : ℝ) ^ e - 1) := div_pos (by norm_num) (by linarith)
    linarith
  refine ⟨48 * (Ce * (1 + 2 / (2 ^ e - 1))), by positivity, fun D₀ hD₀ hF Λ Φ hΦ Ω hΩ E₀ hE hgap
    A hA T n s₀ hT hsep => ?_⟩
  have hD₀' : 10 < D₀ := by linarith [Nat.cast_nonneg (α := ℝ) R]
  have hs₁ : 1 ≤ s₀ := hT.2.1
  obtain ⟨hTcard, hlayer, hbd⟩ := template_geometry hC hT
  obtain ⟨N₀, P, S, -, hn, hP, hS, hTS⟩ := exists_pieces hT
  have h32 : (32 : ℝ) * N₀ * (s₀ + 1) ≤ n := le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) (by positivity)) hn
  set Z := cutEndpoints Λ A
  -- clearance `dist_∞(T, Z) > 4 D₀ s₀ ≥ D₀ s₀ + s₀`
  have hsep' : ∀ c : ℝ, 0 ≤ c → c ≤ 4 * D₀ * s₀ → ENNReal.ofReal c < ambientEDist T Z :=
    fun c _ hc => (ENNReal.ofReal_le_ofReal hc).trans_lt hsep
  have hs₀r : (1 : ℝ) ≤ s₀ := by exact_mod_cast hs₁
  -- the dyadic mixed-square counts of D9.17, as `≤ 48 n / u` for `u ≤ s₀`
  have hmixed : ∀ j ≤ s₀, ∀ k : ℕ, 2 ^ k ≤ s₀ →
      (#(mixedIndices (ambientDilation T j \ T) k) : ℝ) ≤ 48 * n / 2 ^ k ∧
        (#(mixedIndices T k) : ℝ) ≤ 48 * n / 2 ^ k := by
    intro j hj k hk
    have hu : (0 : ℝ) < 2 ^ k := by positivity
    obtain ⟨-, hT0, -, hTj⟩ := step_9_17 (by linarith) hP hS hn hj k
    rw [← hTS] at hT0 hTj
    have hk' : (2 : ℝ) ^ k ≤ s₀ + 1 := by exact_mod_cast hk.trans (Nat.le_succ _)
    have hN : (N₀ : ℝ) ≤ n / 2 ^ k := by
      rw [le_div_iff₀ hu]
      nlinarith [Nat.cast_nonneg (α := ℝ) N₀]
    have : 24 * ((N₀ : ℝ) + n / 2 ^ k) ≤ 48 * n / 2 ^ k := by
      rw [mul_div_assoc]; linarith
    exact ⟨hTj.trans this, hT0.trans this⟩
  -- `K = ⌊log₂ m⌋`: `2^K ≤ m < 2^{K+1}`
  have hlog : ∀ m : ℕ, 1 ≤ m → (2 : ℝ) ^ Nat.log 2 m ≤ m ∧ (m : ℝ) < 2 * 2 ^ Nat.log 2 m := by
    intro m hm
    refine ⟨by exact_mod_cast Nat.pow_log_le_self 2 (by omega), ?_⟩
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    rw [pow_succ] at this
    exact_mod_cast (by linarith : m < 2 * 2 ^ Nat.log 2 m)
  have hrpow : ∀ (K m : ℕ), (2 : ℝ) ^ K ≤ m → ((2 : ℝ) ^ K) ^ e ≤ (m : ℝ) ^ e := fun K m h =>
    Real.rpow_le_rpow (by positivity) h he.le
  have hCe' : 0 ≤ Ce * (1 + 2 / (2 ^ e - 1)) := by positivity
  -- the shell `Q_j`, `j ≤ L ≤ s₀`: D9.18.1–D9.18.4 with cap `≤ L`
  have hshell : ∀ L' : ℕ, 1 ≤ L' → L' ≤ s₀ → ∀ j ≤ L',
      (pureState Ω hΩ).regionEntropy
          (inter_subset_left.trans hA : A ∩ (ambientDilation T j \ T) ⊆ Λ) ≤
        48 * (Ce * (1 + 2 / (2 ^ e - 1))) * n * (L' : ℝ) ^ e := by
    intro L' hL1 hL2 j hj
    obtain ⟨hK1, hK2⟩ := hlog L' hL1
    set K := Nat.log 2 L'
    have hKs : (2 : ℝ) ^ K ≤ s₀ := hK1.trans (by exact_mod_cast hL2)
    -- D9.18.2: `|T_j \ T| ≤ n j ≤ n L`
    have hY : (#(ambientDilation T j \ T) : ℝ) ≤ 48 * n * 2 ^ K := by
      have : ∀ i ≤ s₀, #(ambientDilation T i \ T) ≤ n * i := by
        intro i hi
        induction i with
        | zero => simp [ambientDilation_zero]
        | succ i ih =>
          have hsub : ambientDilation T (i + 1) \ T ⊆
              (ambientDilation T (i + 1) \ ambientDilation T i) ∪ (ambientDilation T i \ T) := by
            intro x hx
            by_cases h : x ∈ ambientDilation T i
            · exact mem_union_right _ (mem_sdiff.2 ⟨h, (mem_sdiff.1 hx).2⟩)
            · exact mem_union_left _ (mem_sdiff.2 ⟨(mem_sdiff.1 hx).1, h⟩)
          refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
          have := hlayer i (by omega)
          have := ih (by omega)
          rw [mul_add, mul_one]; omega
      have h1 : (#(ambientDilation T j \ T) : ℝ) ≤ n * j := by
        exact_mod_cast this j (by omega)
      have hj' : (j : ℝ) ≤ L' := by exact_mod_cast hj
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    -- D9.18.3: mixed parents, `≤ 48 n / 2^{k+1}`
    have hmix : ∀ k < K, (#(mixedIndices (ambientDilation T j \ T) (k + 1)) : ℝ) ≤
        48 * n / 2 ^ (k + 1) := fun k hk => (hmixed j (by omega) (k + 1)
          (by exact_mod_cast (show (2 : ℝ) ^ (k + 1) ≤ s₀ from le_trans
            (pow_le_pow_right₀ (by norm_num) hk) hKs))).1
    -- D9.18.4: clearance `D₀ 2^K + j ≤ D₀ s₀ + s₀ ≤ 4 D₀ s₀`
    have hclear : ENNReal.ofReal (D₀ * 2 ^ K) < ambientEDist (ambientDilation T j \ T) Z := by
      refine (ofReal_lt_ambientEDist_dilation (by positivity) (hsep' _ (by positivity) ?_)).trans_le
        (ambientEDist_mono sdiff_subset)
      have : (j : ℝ) ≤ s₀ := by exact_mod_cast hj.trans hL2
      nlinarith
    have := step_9_18 he hCe.le hD₀ hF hΦ hΩ hE hgap hA _ K (by positivity) hY
      (fun k hk => by have := hmix k hk; rwa [mul_div_assoc] at this ⊢) hclear
    calc _ ≤ Ce * (1 + 2 / (2 ^ e - 1)) * (48 * n) * ((2 : ℝ) ^ K) ^ e := this
      _ ≤ Ce * (1 + 2 / (2 ^ e - 1)) * (48 * n) * (L' : ℝ) ^ e := by
          gcongr
      _ = _ := by ring
  refine ⟨?_, fun L' hL1 hL2 j hj => ⟨hshell L' hL1 hL2 j hj, fun Z' hZ' => ?_⟩, fun j hj => ?_⟩
  · -- D9.18.5: the target, the same cover of `T` with cap `≤ s₀`
    obtain ⟨hK1, hK2⟩ := hlog s₀ hs₁
    set K := Nat.log 2 s₀
    have hY : (#T : ℝ) ≤ 48 * n * 2 ^ K := by
      have := mul_le_mul_of_nonneg_left hK2.le (by positivity : (0 : ℝ) ≤ 9 * n)
      nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_pos (two_pos (α := ℝ)) K]
    have hmix : ∀ k < K, (#(mixedIndices T (k + 1)) : ℝ) ≤ 48 * n / 2 ^ (k + 1) :=
      fun k hk => (hmixed 0 (Nat.zero_le _) (k + 1) (by exact_mod_cast (show (2 : ℝ) ^ (k + 1) ≤ s₀
        from le_trans (pow_le_pow_right₀ (by norm_num) hk) hK1))).2
    have hclear : ENNReal.ofReal (D₀ * 2 ^ K) < ambientEDist T Z :=
      hsep' _ (by positivity) (by nlinarith)
    have := step_9_18 he hCe.le hD₀ hF hΦ hΩ hE hgap hA T K (by positivity) hY
      (fun k hk => by have := hmix k hk; rwa [mul_div_assoc] at this ⊢) hclear
    calc _ ≤ Ce * (1 + 2 / (2 ^ e - 1)) * (48 * n) * ((2 : ℝ) ^ K) ^ e := this
      _ ≤ Ce * (1 + 2 / (2 ^ e - 1)) * (48 * n) * (s₀ : ℝ) ^ e := by
          gcongr
      _ = _ := by ring
  · -- D9.18.6: an extra part of the next row, by subadditivity, costs `≤ n log q`
    have hZT : Z' ⊆ ambientDilation T (j + 1) \ ambientDilation T j := hZ'.trans inter_subset_right
    have hdisj : Disjoint (A ∩ (ambientDilation T j \ T)) Z' := by
      refine disjoint_left.2 fun x hx hxZ => (mem_sdiff.1 (hZT hxZ)).2 ?_
      exact (mem_sdiff.1 (mem_inter.1 hx).2).1
    have hsub := regionEntropy_union_le (pureState Ω hΩ) hdisj (inter_subset_left.trans hA)
      ((hZ'.trans inter_subset_left).trans hA)
    have hZent : (pureState Ω hΩ).regionEntropy ((hZ'.trans inter_subset_left).trans hA) ≤
        #Z' * Real.log q := by
      have h := ((pureState Ω hΩ).restrict
        ((hZ'.trans inter_subset_left).trans hA)).entropy_le_log_card
      rwa [card_reg_const (fun _ => Fintype.card_fin q), Nat.cast_pow, Real.log_pow] at h
    have hZn : (#Z' : ℝ) ≤ n := by exact_mod_cast (card_le_card hZT).trans (hlayer j (by omega))
    have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have := hshell L' hL1 hL2 j hj
    calc _ ≤ _ := hsub
      _ ≤ 48 * (Ce * (1 + 2 / (2 ^ e - 1))) * n * (L' : ℝ) ^ e + n * Real.log q := by
          nlinarith [mul_le_mul_of_nonneg_right hZn hlogq]
  · -- D9.18.6: the cuts of `X`, `Q_j`, `A ∩ T_j` are ambient boundaries of `T` and `T_j`
    have hsepj : ∀ i ≤ s₀, ENNReal.ofReal i < ambientEDist T Z :=
      fun i hi => hsep' _ (by positivity) (by
        have : (i : ℝ) ≤ s₀ := by exact_mod_cast hi
        nlinarith)
    have hbdT := hbd 0 (Nat.zero_le _)
    rw [ambientDilation_zero] at hbdT
    have hbdj := hbd j hj
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    -- `∂_Λ (A ∩ W) ⊆ ∂_{ℤ²}(W ⊆ W_1)` for `W = T, T_j`
    have hW : ∀ i ≤ s₀, OpenAI.edgeBoundary Λ (A ∩ ambientDilation T i) ⊆
        GraphDomain.edgeBoundary squareLattice (ambientDilation T (i + 1))
          (ambientDilation T i) := by
      intro i hi e he
      obtain ⟨h1, h2, hadj⟩ := edgeBoundary_inter_subset (hsepj i hi) subset_rfl he
      refine (SimpleGraph.mem_interedges_iff _).2 ⟨(mem_inter.1 h1).2, mem_sdiff.2 ⟨?_,
        (mem_sdiff.1 h2).2⟩, hadj⟩
      rw [ambientDilation_add_one]
      exact mem_ambientDilation_one_of_adj (mem_inter.1 h1).2 hadj
    have hX := card_le_card (hW 0 (Nat.zero_le _))
    rw [ambientDilation_zero] at hX
    have hXj := card_le_card (hW j hj)
    refine ⟨?_, ?_, ?_⟩
    · have : (#(OpenAI.edgeBoundary Λ (A ∩ T)) : ℝ) ≤ 4 * n := by
        exact_mod_cast hX.trans (by simpa [ambientDilation_zero] using hbdT)
      linarith
    · -- an edge out of `A ∩ (T_j \ T)` leaves `T_j` or enters `T`
      have hsub : OpenAI.edgeBoundary Λ (A ∩ (ambientDilation T j \ T)) ⊆
          GraphDomain.edgeBoundary squareLattice (ambientDilation T (j + 1)) (ambientDilation T j) ∪
            (GraphDomain.edgeBoundary squareLattice (ambientDilation T 1) T).image Prod.swap := by
        intro e he
        obtain ⟨h1, h2, hadj⟩ := edgeBoundary_inter_subset (hsepj j hj) sdiff_subset he
        obtain ⟨hxA, hxj, hxT⟩ := by simpa [mem_inter, mem_sdiff] using h1
        obtain ⟨hyA, hy⟩ := mem_sdiff.1 h2
        by_cases hyj : e.2 ∈ ambientDilation T j
        · have hyT : e.2 ∈ T := by by_contra h; exact hy (mem_sdiff.2 ⟨hyj, h⟩)
          refine mem_union_right _ (mem_image.2 ⟨e.swap, ?_, Prod.swap_swap e⟩)
          exact (SimpleGraph.mem_interedges_iff _).2 ⟨hyT, mem_sdiff.2
            ⟨mem_ambientDilation_one_of_adj hyT hadj.symm, hxT⟩, hadj.symm⟩
        · refine mem_union_left _ ((SimpleGraph.mem_interedges_iff _).2 ⟨hxj, mem_sdiff.2 ⟨?_,
            hyj⟩, hadj⟩)
          rw [ambientDilation_add_one]
          exact mem_ambientDilation_one_of_adj hxj hadj
      have := (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add hbdj
        (card_image_le.trans (by simpa [ambientDilation_zero] using hbdT))))
      have : (#(OpenAI.edgeBoundary Λ (A ∩ (ambientDilation T j \ T))) : ℝ) ≤ 8 * n := by
        exact_mod_cast this.trans (by omega)
      linarith
    · have : (#(OpenAI.edgeBoundary Λ (A ∩ ambientDilation T j)) : ℝ) ≤ 4 * n := by
        exact_mod_cast hXj.trans hbdj
      linarith

/-! ## D9.21.2 The shell of a safe rectangle (input of Proposition 9.5) -/

theorem isStaircase_ambientDilation {R : Finset (ℤ × ℤ)} {y₀ y₁ : ℤ} {ℓ r : ℤ → ℤ}
    (h : IsStaircase R y₀ y₁ ℓ r) (j : ℕ) :
    ∃ y₀' y₁' ℓ' r', IsStaircase (ambientDilation R j) y₀' y₁' ℓ' r' := by
  induction j with
  | zero => exact ⟨y₀, y₁, ℓ, r, by rwa [ambientDilation_zero]⟩
  | succ j ih =>
    obtain ⟨_, _, _, _, h'⟩ := ih
    rw [ambientDilation_succ]
    exact ⟨_, _, h'.add_Icc⟩

theorem ambientDilation_Icc {a b : ℤ × ℤ} (hab : a ≤ b) (j : ℕ) :
    ambientDilation (Icc a b) j = Icc (a.1 - j, a.2 - j) (b.1 + j, b.2 + j) := by
  ext y
  rw [mem_ambientDilation_Icc hab, mem_Icc, Prod.le_def, Prod.le_def]
  simp only
  tauto

/-- D9.21.2 (with the D9.21.1 geometry). Let `D₀ > 2R + 10`, `T` a safe integer rectangle of size
`s₀ = size(T)` (`dist_∞(T, Z) > D₀ s₀`) and `F_box(r) ≤ C_e r^{1+e}` (`r ≥ 1`, `0 < e`). Then
`|T| ≤ s₀²` and `|T_j \ T_{j-1}| ≤ 4 s₀ + 8 j` (D9.21.1); and for `L ≥ 1` with `(D₀ + 1) L ≤ D₀ s₀`
(squares of side `≤ L` at distance `≥ D₀ s₀ - L > D₀ L` from `Z`, the safe clearance `D₀ s₀`
sufficing) and `n ≥ 4 s₀ + 8 (L + 1)`: `S_Ω(A ∩ (T_j \ T)) ≤ C'_e n L^e` for `j ≤ L`, and the same
with an extra `n log q` after adding any part of the next row. `C'_e` depends only on `e, C_e`.
2D only: `F_box` and safe rectangles are planar. -/
theorem step_9_21_2 (q R : ℕ) (J Δ e Ce : ℝ) (he : 0 < e) (hCe : 0 < Ce) :
    ∃ Ce' : ℝ, 0 < Ce' ∧ ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
      (∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e)) →
      ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ),
        IsAdmissible Λ R J Φ →
      ∀ (Ω : Reg (Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
        hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
      ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)), IsIntRect T → IsSafe D₀ Λ A T →
        (#T ≤ boxSize T ^ 2 ∧
          ∀ j, 1 ≤ j → #(ambientDilation T j \ ambientDilation T (j - 1)) ≤ 4 * boxSize T + 8 * j) ∧
        ∀ L n : ℕ, 1 ≤ L → (D₀ + 1) * L ≤ D₀ * boxSize T → 4 * boxSize T + 8 * (L + 1) ≤ n →
          ∀ j ≤ L,
            (pureState Ω hΩ).regionEntropy
                (inter_subset_left.trans hA : A ∩ (ambientDilation T j \ T) ⊆ Λ) ≤
              Ce' * n * (L : ℝ) ^ e ∧
            ∀ (Z' : Finset (ℤ × ℤ))
              (hZ : Z' ⊆ A ∩ (ambientDilation T (j + 1) \ ambientDilation T j)),
              (pureState Ω hΩ).regionEntropy
                  (union_subset (inter_subset_left.trans hA)
                    ((hZ.trans inter_subset_left).trans hA) :
                    A ∩ (ambientDilation T j \ T) ∪ Z' ⊆ Λ) ≤
                Ce' * n * (L : ℝ) ^ e + n * Real.log q := by
  have hce : 0 < 1 + 2 / ((2 : ℝ) ^ e - 1) := by
    have : 1 < (2 : ℝ) ^ e := Real.one_lt_rpow (by norm_num) he
    have : 0 < 2 / ((2 : ℝ) ^ e - 1) := div_pos (by norm_num) (by linarith)
    linarith
  refine ⟨9 * (Ce * (1 + 2 / (2 ^ e - 1))), by positivity, fun D₀ hD₀ hF Λ Φ hΦ Ω hΩ E₀ hE hgap
    A hA T hT hsafe => ?_⟩
  obtain ⟨a, b, hab, rfl⟩ := hT
  have hab' := Prod.le_def.1 hab
  set s₀ := boxSize (Icc a b)
  have hs₀ : s₀ = max (b.1 + 1 - a.1).toNat (b.2 + 1 - a.2).toNat := boxSize_Icc hab
  have hw : b.1 + 1 - a.1 ≤ s₀ := by rw [hs₀]; omega
  have hh : b.2 + 1 - a.2 ≤ s₀ := by rw [hs₀]; omega
  -- D9.21.1: `|T_i| = (w + 2i)(h + 2i)`
  have hcard : ∀ i : ℕ, ((#(ambientDilation (Icc a b) i) : ℕ) : ℤ) =
      (b.1 + 1 - a.1 + 2 * i) * (b.2 + 1 - a.2 + 2 * i) := by
    intro i
    rw [ambientDilation_Icc hab, Icc_prod_def, card_product, Int.card_Icc, Int.card_Icc]
    push_cast
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    ring
  have hlayer : ∀ j, 1 ≤ j →
      #(ambientDilation (Icc a b) j \ ambientDilation (Icc a b) (j - 1)) ≤ 4 * s₀ + 8 * j := by
    intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [show 1 + i - 1 = i by omega, card_sdiff_of_subset (ambientDilation_mono' (by omega))]
    have h1 := hcard (1 + i)
    have h2 := hcard i
    have hle := card_le_card (ambientDilation_mono' (T := Icc a b) (by omega : i ≤ 1 + i))
    zify [hle]
    rw [h1, h2]
    push_cast
    nlinarith
  refine ⟨⟨card_le_boxSize_sq _, hlayer⟩, fun L n hL hLs hn j hj => ?_⟩
  have hn' : (4 * s₀ + 8 * (L + 1) : ℝ) ≤ n := by exact_mod_cast hn
  -- D9.21.2: the shell `T_j \ T` has area `≤ n L`
  have hYcard : (#(ambientDilation (Icc a b) j \ Icc a b) : ℝ) ≤ n * L := by
    have hsub : Icc a b ⊆ ambientDilation (Icc a b) j := by
      have := ambientDilation_mono' (T := Icc a b) (Nat.zero_le j)
      rwa [ambientDilation_zero] at this
    have e1 := hcard j
    have e0 := hcard 0
    rw [ambientDilation_zero] at e0
    have : ((#(ambientDilation (Icc a b) j \ Icc a b) : ℕ) : ℤ) ≤ n * L := by
      rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub), e1, e0]
      have : (j : ℤ) ≤ L := by exact_mod_cast hj
      have : ((4 * s₀ + 8 * (L + 1) : ℕ) : ℤ) ≤ n := by exact_mod_cast hn
      push_cast at this ⊢
      nlinarith
    exact_mod_cast this
  obtain ⟨hK1, hK2⟩ : (2 : ℝ) ^ Nat.log 2 L ≤ L ∧ (L : ℝ) < 2 * 2 ^ Nat.log 2 L := by
    refine ⟨by exact_mod_cast Nat.pow_log_le_self 2 (by omega), ?_⟩
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) L
    rw [pow_succ] at this
    exact_mod_cast (by linarith : L < 2 * 2 ^ Nat.log 2 L)
  set K := Nat.log 2 L
  have hY : (#(ambientDilation (Icc a b) j \ Icc a b) : ℝ) ≤ 9 * n * 2 ^ K := by
    have := mul_le_mul_of_nonneg_left hK2.le (Nat.cast_nonneg (α := ℝ) n)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  -- D9.21.2: `T` and `T_j` are rectangles, so `O(n/u + 1)` mixed squares (boundary-line count)
  have hstT : IsStaircase (Icc a b) a.2 b.2 (fun _ => a.1) (fun _ => b.1) :=
    ⟨hab'.2, fun _ => hab'.1, fun _ => by omega, fun _ => by omega, fun p => by
      rw [mem_Icc, Prod.le_def, Prod.le_def]; tauto⟩
  have hdT : HasDiam (Icc a b) s₀ := fun p hp q hq => by
    rw [mem_Icc, Prod.le_def, Prod.le_def] at hp hq
    rw [abs_le, abs_le]; omega
  obtain ⟨_, _, _, _, hstj⟩ := isStaircase_ambientDilation hstT j
  have hmix : ∀ k < K, (#(mixedIndices (ambientDilation (Icc a b) j \ Icc a b) (k + 1)) : ℝ) ≤
      9 * n / 2 ^ (k + 1) := by
    intro k hk
    have hu : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    have huL : (2 : ℝ) ^ (k + 1) ≤ L := le_trans (pow_le_pow_right₀ (by norm_num) hk) hK1
    have h1 := hstj.card_mixedIndices_le (hasDiam_ambientDilation hdT j) (k + 1)
    have h2 := hstT.card_mixedIndices_le hdT (k + 1)
    have h3 : (#(mixedIndices (ambientDilation (Icc a b) j \ Icc a b) (k + 1)) : ℝ) ≤
        #(mixedIndices (ambientDilation (Icc a b) j) (k + 1)) + #(mixedIndices (Icc a b) (k + 1)) :=
      by exact_mod_cast (card_le_card (mixedIndices_sdiff_subset _ _ _)).trans (card_union_le _ _)
    have hj' : (j : ℝ) ≤ L := by exact_mod_cast hj
    push_cast at h1 h2
    have key : 6 * (((s₀ : ℝ) + 2 * j) / 2 ^ (k + 1) + 2) + 6 * ((s₀ : ℝ) / 2 ^ (k + 1) + 2) =
        (12 * s₀ + 12 * j + 24 * 2 ^ (k + 1)) / 2 ^ (k + 1) := by
      field_simp; ring
    have key2 : (12 * (s₀ : ℝ) + 12 * j + 24 * 2 ^ (k + 1)) / 2 ^ (k + 1) ≤ 9 * n / 2 ^ (k + 1) :=
      div_le_div_of_nonneg_right (by nlinarith) hu.le
    linarith
  -- D9.21.2: the squares are safe, `D₀ 2^K + j ≤ (D₀ + 1) L ≤ D₀ s₀`
  have hclear : ENNReal.ofReal (D₀ * 2 ^ K) <
      ambientEDist (ambientDilation (Icc a b) j \ Icc a b) (cutEndpoints Λ A) := by
    have hD₀' : 0 ≤ D₀ := by linarith [Nat.cast_nonneg (α := ℝ) R]
    refine (ofReal_lt_ambientEDist_dilation (by positivity) ((ENNReal.ofReal_le_ofReal ?_).trans_lt
      hsafe)).trans_le (ambientEDist_mono sdiff_subset)
    have : (j : ℝ) ≤ L := by exact_mod_cast hj
    nlinarith
  have hshell := step_9_18 he hCe.le hD₀ hF hΦ hΩ hE hgap hA _ K (by positivity) hY
    (fun k hk => by have := hmix k hk; rwa [mul_div_assoc] at this ⊢) hclear
  have hent : (pureState Ω hΩ).regionEntropy
      (inter_subset_left.trans hA : A ∩ (ambientDilation (Icc a b) j \ Icc a b) ⊆ Λ) ≤
        9 * (Ce * (1 + 2 / (2 ^ e - 1))) * n * (L : ℝ) ^ e := by
    calc _ ≤ Ce * (1 + 2 / (2 ^ e - 1)) * (9 * n) * ((2 : ℝ) ^ K) ^ e := hshell
      _ ≤ Ce * (1 + 2 / (2 ^ e - 1)) * (9 * n) * (L : ℝ) ^ e := by
          gcongr
      _ = _ := by ring
  refine ⟨hent, fun Z' hZ' => ?_⟩
  -- D9.21.3: a partial row costs `O(n)`
  have hZT : Z' ⊆ ambientDilation (Icc a b) (j + 1) \ ambientDilation (Icc a b) j :=
    hZ'.trans inter_subset_right
  have hdisj : Disjoint (A ∩ (ambientDilation (Icc a b) j \ Icc a b)) Z' :=
    disjoint_left.2 fun x hx hxZ => (mem_sdiff.1 (hZT hxZ)).2 (mem_sdiff.1 (mem_inter.1 hx).2).1
  have hsub := regionEntropy_union_le (pureState Ω hΩ) hdisj (inter_subset_left.trans hA)
    ((hZ'.trans inter_subset_left).trans hA)
  have hZent : (pureState Ω hΩ).regionEntropy ((hZ'.trans inter_subset_left).trans hA) ≤
      #Z' * Real.log q := by
    have h := ((pureState Ω hΩ).restrict
      ((hZ'.trans inter_subset_left).trans hA)).entropy_le_log_card
    rwa [card_reg_const (fun _ => Fintype.card_fin q), Nat.cast_pow, Real.log_pow] at h
  have hZn : (#Z' : ℝ) ≤ n := by
    have := (card_le_card hZT).trans (hlayer (j + 1) (by omega))
    exact_mod_cast this.trans (by omega)
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  calc _ ≤ _ := hsub
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hZn hlogq]

end AreaLaw.Scanner
