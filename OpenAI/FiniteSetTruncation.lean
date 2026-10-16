/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported and adapted from LionSR/TNLean commit
fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/FiniteSetTruncation.lean`. Apache 2.0; adapted to the
frozen `OpenAI.domainEDist`, `OpenAI.graphNbhd`, and `OpenAI.condExpect` interfaces.
-/
import OpenAI.ConditionalExpectation
import OpenAI.SupportCounting
import OpenAI.TruncationSeries

/-!
# Truncation of positive constraints near a finite set

The geometric shell count and volume-free operator error used in Proposition 4.5 of OAI265.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw

/-- The induced-domain graph distance from a site to a finite set. -/
noncomputable def setDist (Λ S₀ : Finset (ℤ × ℤ)) (x : ℤ × ℤ) : ℕ∞ :=
  S₀.inf fun y => domainEDist Λ x y

/-- A finite distance to `S₀` is attained at a point of `S₀`. -/
theorem exists_mem_domainEDist_eq_setDist {Λ S₀ : Finset (ℤ × ℤ)} {x : ℤ × ℤ}
    (hx : setDist Λ S₀ x ≠ ⊤) : ∃ y ∈ S₀, domainEDist Λ x y = setDist Λ S₀ x := by
  have hne : S₀.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [setDist, h] at hx
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf S₀ hne fun y => domainEDist Λ x y
  exact ⟨y, hy, he.symm⟩

/-- A finite induced-domain distance forces its left endpoint into the domain. -/
theorem mem_of_domainEDist_ne_top_left {Λ : Finset (ℤ × ℤ)} {x y : ℤ × ℤ}
    (h : domainEDist Λ x y ≠ ⊤) : x ∈ Λ := by
  by_contra hx
  exact h (domainEDist_of_not_mem_left hx)

/-- Membership in a singleton graph neighbourhood. -/
theorem mem_graphNbhd_singleton_iff {Λ : Finset (ℤ × ℤ)} {x y : ℤ × ℤ} {r : ℕ} :
    x ∈ graphNbhd Λ {y} r ↔ x ∈ Λ ∧ domainEDist Λ x y ≤ r := by
  simp [graphNbhd]

/-- An induced square-lattice ball lies in the ambient sup-norm box of the same radius. -/
theorem graphNbhd_singleton_subset_Icc (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ) (d : ℕ) :
    graphNbhd Λ {a} d ⊆
      Finset.Icc (a - ((d : ℤ), (d : ℤ))) (a + ((d : ℤ), (d : ℤ))) := by
  intro x hx
  have hd : dist x a ≤ d :=
    dist_le_of_domainEDist_le (mem_graphNbhd_singleton_iff.1 hx).2
  obtain ⟨h1, h2⟩ := dist_le_natCast_iff.1 hd
  rw [abs_le] at h1 h2
  rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  omega

/-- Induced square-lattice balls grow at most quadratically, uniformly in the domain. -/
theorem card_graphNbhd_singleton_le (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ) (d : ℕ) :
    (graphNbhd Λ {a} d).card ≤ (2 * d + 1) ^ 2 := by
  exact (Finset.card_le_card (graphNbhd_singleton_subset_Icc Λ a d)).trans
    (by rw [card_Icc_sub_add])

/-- A real-valued ball bound convenient for the truncation estimates. -/
theorem card_graphNbhd_singleton_le_four (Λ : Finset (ℤ × ℤ)) (a : ℤ × ℤ) (d : ℕ) :
    ((graphNbhd Λ {a} d).card : ℝ) ≤ 4 * ((d : ℝ) + 1) ^ 2 := by
  calc
    ((graphNbhd Λ {a} d).card : ℝ) ≤ ((2 * d + 1) ^ 2 : ℕ) := by
      exact_mod_cast card_graphNbhd_singleton_le Λ a d
    _ ≤ 4 * ((d : ℝ) + 1) ^ 2 := by
      push_cast
      nlinarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]

/-- Choosing one anchor in every admissible support has uniformly bounded multiplicity. -/
theorem card_anchor_fiber_le (Λ : Finset (ℤ × ℤ)) (R : ℕ)
    (anchor : supports Λ R → ℤ × ℤ) (hanchor : ∀ X, anchor X ∈ X.1) (x : ℤ × ℤ) :
    (Finset.univ.filter fun X => anchor X = x).card ≤ 2 ^ (2 * R + 1) ^ 2 := by
  classical
  let s := Finset.univ.filter fun X : supports Λ R => anchor X = x
  have hcard : s.card ≤ ((supports Λ R).filter fun X => x ∈ X).card := by
    refine Finset.card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn
    intro X hX
    change X ∈ s at hX
    change X.1 ∈ (supports Λ R).filter fun Y => x ∈ Y
    rw [Finset.mem_filter] at hX ⊢
    refine ⟨X.2, ?_⟩
    rw [← hX.2]
    exact hanchor X
  change s.card ≤ _
  exact hcard.trans (card_filter_mem_supports_le Λ R x)

/-- The variable truncation radius `max {r₀, ⌊d/2⌋}`. -/
def truncationRadius (r₀ d : ℕ) : ℕ := max r₀ (d / 2)

/-- A constraint truncated to the variable-radius neighbourhood of its anchor. -/
noncomputable def truncatedConstraint (q : ℕ) (Λ S₀ : Finset (ℤ × ℤ)) (r₀ : ℕ)
    (a : ℤ × ℤ) (k : Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ) :
    Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
  if setDist Λ S₀ a = ⊤ then k
  else condExpect (graphNbhd_subset Λ {a}
    (truncationRadius r₀ (setDist Λ S₀ a).toNat)) k

/-- At most `μ |S₀| K_b (d+1)²` labels have anchors at distance `d` from `S₀`. -/
theorem card_label_shell_le {κ : Type*} [Fintype κ] (Λ S₀ : Finset (ℤ × ℤ))
    (a : κ → ℤ × ℤ) {Kb μ : ℝ}
    (hBall : ∀ x (d : ℕ), ((graphNbhd Λ {x} d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) (d : ℕ) :
    ((Finset.univ.filter fun i => setDist Λ S₀ (a i) = d).card : ℝ) ≤
      μ * (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2)) := by
  classical
  have hμ : 0 ≤ μ := (Nat.cast_nonneg _).trans (hMult (0, 0))
  set B := S₀.biUnion fun y => graphNbhd Λ {y} d
  have hBcard : (B.card : ℝ) ≤ S₀.card * (Kb * ((d : ℝ) + 1) ^ 2) := by
    calc
      (B.card : ℝ) ≤ ∑ y ∈ S₀, ((graphNbhd Λ {y} d).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ S₀, Kb * ((d : ℝ) + 1) ^ 2 :=
        Finset.sum_le_sum fun y _ => hBall y d
      _ = S₀.card * (Kb * ((d : ℝ) + 1) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  let L := Finset.univ.filter fun i => setDist Λ S₀ (a i) = d
  have hL : L ⊆ B.biUnion fun x => Finset.univ.filter fun i => a i = x := by
    intro i hi
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨y, hy, he⟩ := exists_mem_domainEDist_eq_setDist
      (Λ := Λ) (S₀ := S₀) (x := a i) (by rw [hi]; exact ENat.natCast_ne_top d)
    have hai : a i ∈ Λ :=
      mem_of_domainEDist_ne_top_left (by rw [he, hi]; exact ENat.natCast_ne_top d)
    have haB : a i ∈ B := Finset.mem_biUnion.mpr ⟨y, hy,
      mem_graphNbhd_singleton_iff.mpr ⟨hai, by rw [he, hi]⟩⟩
    exact Finset.mem_biUnion.mpr
      ⟨a i, haB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  change (L.card : ℝ) ≤ _
  calc
    (L.card : ℝ) ≤
        ((B.biUnion fun x => Finset.univ.filter fun i => a i = x).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hL
    _ ≤ ∑ x ∈ B, ((Finset.univ.filter fun i => a i = x).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ B, μ := Finset.sum_le_sum fun x _ => hMult x
    _ = B.card * μ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2)) * μ :=
      mul_le_mul_of_nonneg_right hBcard hμ
    _ = μ * (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2)) := by ring

/-- The volume-free truncation error of Proposition 4.5. -/
theorem norm_sum_truncatedConstraint_sub_le {q : ℕ} {κ : Type*} [Fintype κ]
    (Λ S₀ : Finset (ℤ × ℤ)) (a : κ → ℤ × ℤ)
    (k : κ → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ)
    {C c α Kb μ A : ℝ} (hC : 0 ≤ C) (hKb : 0 ≤ Kb) (hμ : 0 ≤ μ)
    (htail : ∀ i (l : ℕ),
      ‖k i - condExpect (graphNbhd_subset Λ {a i} l) (k i)‖ ≤
        C * Real.exp (-(c * (l : ℝ) ^ α)))
    (hBall : ∀ x (d : ℕ), ((graphNbhd Λ {x} d).card : ℝ) ≤
      Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ)
    (hA : ∀ r₀ N : ℕ, ∑ d ∈ Finset.range N, ((d : ℝ) + 1) ^ 2 *
        Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α)) ≤
      A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α))) (r₀ : ℕ) :
    ‖∑ i, truncatedConstraint q Λ S₀ r₀ (a i) (k i) - ∑ i, k i‖ ≤
      C * μ * Kb * S₀.card * A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by
  classical
  set D : κ → ℕ := fun i => (setDist Λ S₀ (a i)).toNat
  set F := Finset.univ.filter fun i => setDist Λ S₀ (a i) ≠ ⊤
  set f : ℕ → ℝ := fun d => C * Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α))
  have hterm : ∀ i, ‖truncatedConstraint q Λ S₀ r₀ (a i) (k i) - k i‖ ≤
      if setDist Λ S₀ (a i) ≠ ⊤ then f (D i) else 0 := by
    intro i
    by_cases hi : setDist Λ S₀ (a i) = ⊤
    · simp [truncatedConstraint, hi]
    · simp only [truncatedConstraint, hi, ite_false, ne_eq, not_false_eq_true, ite_true]
      rw [norm_sub_rev]
      exact htail i _
  calc
    ‖∑ i, truncatedConstraint q Λ S₀ r₀ (a i) (k i) - ∑ i, k i‖ =
        ‖∑ i, (truncatedConstraint q Λ S₀ r₀ (a i) (k i) - k i)‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖truncatedConstraint q Λ S₀ r₀ (a i) (k i) - k i‖ := norm_sum_le _ _
    _ ≤ ∑ i, if setDist Λ S₀ (a i) ≠ ⊤ then f (D i) else 0 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i ∈ F, f (D i) := by rw [Finset.sum_filter]
    _ = ∑ d ∈ F.image D, ((F.filter fun i => D i = d).card : ℝ) * f d := by
      rw [Finset.sum_comp]
      simp [nsmul_eq_mul]
    _ ≤ ∑ d ∈ Finset.range ((F.image D).sup id + 1),
          (μ * (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2))) * f d := by
      refine (Finset.sum_le_sum fun d _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (fun d hd => ?_) fun d _ _ => ?_)
      · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine le_trans ?_ (card_label_shell_le Λ S₀ a hBall hMult d)
        exact_mod_cast Finset.card_le_card fun i hi => by
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          rw [← hi.2]
          exact (ENat.natCast_toNat hi.1).symm
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hd))
      · positivity
    _ = C * μ * Kb * S₀.card * ∑ d ∈ Finset.range ((F.image D).sup id + 1),
          ((d : ℝ) + 1) ^ 2 *
            Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [f]
      ring
    _ ≤ C * μ * Kb * S₀.card *
        (A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α))) := by
      gcongr
      exact hA r₀ _
    _ = C * μ * Kb * S₀.card * A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by ring

end OpenAI
