/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Adapted from LionSR/TNLean commit fc565830cec69e8226e521d56c86d39845d45576,
`TNLean/PEPS/AreaLaw/GraphPropagation.lean` and
`TNLean/PEPS/AreaLaw/PositiveConstraints.lean`.  The finite-graph propagation theorem is
specialized here to the existing `OpenAI.IsAdmissible` Hamiltonian and `OpenAI.condExpect`.
-/
import OpenAI.ConditionalExpectation
import OpenAI.LiebRobinson.GraphPropagation
import OpenAI.SpectralFilter.MatrixFilter
import OpenAI.SupportCounting

/-!
# Hamiltonian localization on the induced square lattice

This file specializes the abstract finite-graph Lieb--Robinson estimate to admissible
Hamiltonians on `Λ`, then uses the complementary-Weyl characterization of `condExpect` to
obtain the dynamical localization estimate needed by Proposition 4.3.
-/

namespace OpenAI

open Arealaw Matrix SimpleGraph
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LiebRobinson

private def supportInDomain {Λ : Finset (ℤ × ℤ)} {R : ℕ} (X : supports Λ R) : Finset Λ :=
  X.1.subtype (· ∈ Λ)

@[simp] private theorem mem_supportInDomain {Λ : Finset (ℤ × ℤ)} {R : ℕ}
    (X : supports Λ R) (x : Λ) : x ∈ supportInDomain X ↔ x.1 ∈ X.1 :=
  Finset.mem_subtype

private theorem card_supportInDomain {Λ : Finset (ℤ × ℤ)} {R : ℕ}
    (X : supports Λ R) : (supportInDomain X).card = X.1.card := by
  rw [supportInDomain, Finset.card_subtype, Finset.filter_eq_self.2]
  exact fun x hx => subset_of_mem_supports X.2 hx

private theorem disjoint_of_disjoint_supportInDomain {Λ A B : Finset (ℤ × ℤ)}
    (hA : A ⊆ Λ)
    (h : Disjoint (A.subtype (· ∈ Λ)) (B.subtype (· ∈ Λ))) : Disjoint A B := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hxA hxB
  exact h (a := ⟨x, hA hxA⟩) (by simpa using hxA) (by simpa using hxB)

private theorem isSupportedOn_self {σ : Type*} [DecidableEq σ] {loc : σ → Type*}
    [∀ i, DecidableEq (loc i)] {T : Finset σ}
    (A : Matrix (Reg loc T) (Reg loc T) ℂ) :
    IsSupportedOn (show T ⊆ T from Finset.Subset.rfl) A := by
  refine ⟨A, ?_⟩
  letI : Subsingleton (Reg loc (T \ T)) := ⟨fun u v => funext fun i => by
    have : False := by simpa using i.2
    exact this.elim⟩
  ext x y
  change A x y = if restr (show T \ T ⊆ T from Finset.sdiff_subset) x =
    restr (show T \ T ⊆ T from Finset.sdiff_subset) y then
    A (restr (show T ⊆ T from Finset.Subset.rfl) x)
      (restr (show T ⊆ T from Finset.Subset.rfl) y) else 0
  have hx : restr (show T ⊆ T from Finset.Subset.rfl) x = x := by rfl
  have hy : restr (show T ⊆ T from Finset.Subset.rfl) y = y := by rfl
  rw [if_pos (Subsingleton.elim _ _), hx, hy]

private def supportedOnSubmodule {q : ℕ} {Λ X : Finset (ℤ × ℤ)} (hX : X ⊆ Λ) :
    Submodule ℂ (Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ) where
  carrier := {A | IsSupportedOn hX A}
  zero_mem' := isSupportedOn_zero hX
  add_mem' := fun hA hB => hA.add hB
  smul_mem' := fun c _ hA => hA.smul c

/-- The volume-independent prefactor in the square-lattice propagation estimate. -/
noncomputable def localizationPrefactor (R : ℕ) : ℝ :=
  2 * Real.exp R

/-- The velocity in the square-lattice propagation estimate, using the box-counting bound
`2^((2R+1)^2)` for the number of supports meeting one site. -/
noncomputable def localizationVelocity (R : ℕ) (J : ℝ) : ℝ :=
  2 * ((2 * R + 1) ^ 2 : ℕ) * (2 ^ (2 * R + 1) ^ 2 * J) * Real.exp (2 * R)

theorem localizationPrefactor_nonneg (R : ℕ) : 0 ≤ localizationPrefactor R := by
  unfold localizationPrefactor
  positivity

theorem localizationVelocity_pos {R : ℕ} {J : ℝ} (hJ : 0 < J) :
    0 < localizationVelocity R J := by
  unfold localizationVelocity
  positivity

/-- **Square-lattice dynamical localization.**  A local Hamiltonian term evolved for time `t`
is within the standard Lieb--Robinson minimum of its normalized conditional expectation onto
the graph ball of radius `l` about its chosen anchor. -/
theorem norm_heisenberg_sub_condExpect_graphNbhd_le
    {q R : ℕ} {J : ℝ} (hq : 1 ≤ q) (hJ : 0 < J)
    {Λ : Finset (ℤ × ℤ)}
    {Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ}
    (hΦ : IsAdmissible Λ R J Φ)
    (anchor : Finset (ℤ × ℤ) → ℤ × ℤ)
    (hanchor : ∀ Y ∈ supports Λ R, anchor Y ∈ Y)
    (X : supports Λ R) (l : ℕ) (t : ℝ) :
    let A := extendId (subset_of_mem_supports X.2) (Φ X)
    ‖hermitianUnitaryPath (hamiltonian Λ Φ) t * A *
          hermitianUnitaryPath (hamiltonian Λ Φ) (-t) -
        condExpect (graphNbhd_subset Λ {anchor X.1} l)
          (hermitianUnitaryPath (hamiltonian Λ Φ) t * A *
            hermitianUnitaryPath (hamiltonian Λ Φ) (-t))‖ ≤
      ‖A‖ * min 2 (localizationPrefactor R *
        Real.exp (localizationVelocity R J * |t| - (l : ℝ))) := by
  dsimp only
  classical
  letI : NeZero q := ⟨by omega⟩
  let G := (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))
  let Xs : supports Λ R → Finset Λ := supportInDomain
  let a : supports Λ R → Λ := fun Y =>
    ⟨anchor Y.1, subset_of_mem_supports Y.2 (hanchor Y.1 Y.2)⟩
  let term : supports Λ R → Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ :=
    fun Y => extendId (subset_of_mem_supports Y.2) (Φ Y)
  let S : supports Λ R → Submodule ℂ
      (Matrix (Reg (Qudits q) Λ) (Reg (Qudits q) Λ) ℂ) :=
    fun Y => supportedOnSubmodule (subset_of_mem_supports Y.2)
  let vR : ℕ := (2 * R + 1) ^ 2
  let b₀ : ℝ := 2 ^ (2 * R + 1) ^ 2 * J
  have ha : ∀ Y, a Y ∈ Xs Y := by
    intro Y
    simp only [a, Xs, mem_supportInDomain]
    exact hanchor Y.1 Y.2
  have hHerm : ∀ Y, (term Y).IsHermitian := fun Y => hΦ.isHermitian_extendId Y
  have hSupport : ∀ Y, term Y ∈ S Y := by
    intro Y
    exact isSupportedOn_extendId _ _
  have hComm : ∀ i j, Disjoint (Xs i : Set Λ) (Xs j : Set Λ) →
      ∀ A ∈ S i, Commute (term j) A := by
    intro i j hij A hA
    change IsSupportedOn (subset_of_mem_supports i.2) A at hA
    have hij' : Disjoint j.1 i.1 :=
      disjoint_of_disjoint_supportInDomain (subset_of_mem_supports j.2)
        (by simpa only [Xs, supportInDomain] using (Finset.disjoint_coe.1 hij.symm))
    exact (isSupportedOn_extendId (subset_of_mem_supports j.2) (Φ j)).commute hA hij'
  have hDiam : ∀ Y, ∀ x ∈ Xs Y, ∀ z ∈ Xs Y, G.edist x z ≤ R := by
    intro Y x hx z hz
    have hx' : x.1 ∈ Y.1 := by simpa only [Xs, mem_supportInDomain] using hx
    have hz' : z.1 ∈ Y.1 := by simpa only [Xs, mem_supportInDomain] using hz
    have hd := (domainEDiam_le_iff.1 (mem_supports_iff.1 Y.2).2.2) x.1 hx' z.1 hz'
    rw [domainEDist_of_mem x.2 z.2] at hd
    exact hd
  have hCard : ∀ Y, (Xs Y).card ≤ vR := by
    intro Y
    rw [show (Xs Y).card = Y.1.card by exact card_supportInDomain Y]
    exact card_le_of_mem_supports Y.2
  have hBudget : ∀ x, ∑ Y ∈ Finset.univ.filter (fun Y => x ∈ Xs Y), ‖term Y‖ ≤ b₀ := by
    intro x
    simpa only [Xs, term, b₀, mem_supportInDomain] using
      hΦ.sum_norm_extendId_containing_le hJ.le x
  let N := graphNbhd Λ {anchor X.1} l
  let Y : Finset Λ := (Λ \ N).subtype (· ∈ Λ)
  have hExp :
      ‖hermitianUnitaryPath (hamiltonian Λ Φ) t * term X *
            hermitianUnitaryPath (hamiltonian Λ Φ) (-t) -
          condExpect (graphNbhd_subset Λ {anchor X.1} l)
            (hermitianUnitaryPath (hamiltonian Λ Φ) t * term X *
              hermitianUnitaryPath (hamiltonian Λ Φ) (-t))‖ ≤
        ‖term X‖ * (localizationPrefactor R *
          Real.exp (localizationVelocity R J * |t| - (l : ℝ))) := by
    apply norm_sub_condExpect_le_of_forall_commutator
    intro B hB hBnorm
    by_cases hY : Y.Nonempty
    · have hBComm : ∀ i, Disjoint (Xs i : Set Λ) (Y : Set Λ) →
          ∀ A ∈ S i, Commute A B := by
        intro i hi A hA
        change IsSupportedOn (subset_of_mem_supports i.2) A at hA
        have hi' : Disjoint i.1 (Λ \ N) :=
          disjoint_of_disjoint_supportInDomain (subset_of_mem_supports i.2)
            (by simpa only [Xs, Y, supportInDomain] using (Finset.disjoint_coe.1 hi))
        exact hA.commute hB hi'
      have hm : ∀ y ∈ Y, (l : ℕ∞) ≤ G.edist (a X) y := by
        intro y hy
        have hy' : y.1 ∈ Λ \ N := by simpa only [Y, Finset.mem_subtype] using hy
        have hyN : y.1 ∉ N := (Finset.mem_sdiff.1 hy').2
        have hnot : ¬domainEDist Λ (anchor X.1) y.1 ≤ l := by
          intro hd
          apply hyN
          simp only [N, graphNbhd, Finset.mem_filter, y.2, true_and,
            domainEDist_comm]
          simpa using hd
        have hd : (l : ℕ∞) ≤ domainEDist Λ (anchor X.1) y.1 :=
          (lt_of_not_ge hnot).le
        rw [domainEDist_of_mem (a X).2 y.2] at hd
        exact hd
      have hraw :
          ‖heisenbergEvolution (∑ i, term i) t (term X) * B -
              B * heisenbergEvolution (∑ i, term i) t (term X)‖ ≤
            2 * Real.exp R * ‖term X‖ * ‖B‖ *
              Real.exp (localizationVelocity R J * |t| - (l : ℝ)) := by
        rcases le_or_gt 0 t with ht | ht
        · have hb := norm_heisenberg_commutator_le_graphDistance_finset G Xs a ha term S
            hHerm hSupport hComm R hDiam vR hCard b₀ hBudget X (hSupport X) Y hY hBComm
            1 zero_le_one l hm t ht
          convert hb using 1 <;>
            simp only [one_mul, localizationVelocity, vR, b₀, Nat.cast_pow, Nat.cast_add,
              Nat.cast_mul, Nat.cast_one] <;> ring
        · have hb := norm_heisenberg_commutator_le_graphDistance_finset G Xs a ha
            (fun i => -term i) S (fun i => (hHerm i).neg)
            (fun i => Submodule.neg_mem _ (hSupport i))
            (fun i j hij A hA => (hComm i j hij A hA).neg_left) R hDiam vR hCard b₀
            (fun x => by simpa only [norm_neg] using hBudget x) X (hSupport X) Y hY hBComm
            1 zero_le_one l hm (-t) (by linarith)
          convert hb using 1 <;>
            simp only [Finset.sum_neg_distrib, heisenbergEvolution, smul_neg, neg_smul,
              neg_neg, abs_neg, one_mul, localizationVelocity, vR, b₀,
              Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_one] <;> ring
      rw [← hΦ.hamiltonian_eq_sum_supports] at hraw
      calc
        _ ≤ 2 * Real.exp R * ‖term X‖ * ‖B‖ *
            Real.exp (localizationVelocity R J * |t| - (l : ℝ)) := hraw
        _ ≤ 2 * Real.exp R * ‖term X‖ * 1 *
            Real.exp (localizationVelocity R J * |t| - (l : ℝ)) := by
          gcongr
        _ = ‖term X‖ * (localizationPrefactor R *
            Real.exp (localizationVelocity R J * |t| - (l : ℝ))) := by
          rw [localizationPrefactor]
          ring
    · have hYempty : Λ \ N = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        intro hne
        obtain ⟨y, hy⟩ := hne
        apply hY
        exact ⟨⟨y, (Finset.mem_sdiff.1 hy).1⟩, by simpa only [Y, Finset.mem_subtype]⟩
      have hfull := isSupportedOn_self
        (hermitianUnitaryPath (hamiltonian Λ Φ) t * term X *
          hermitianUnitaryPath (hamiltonian Λ Φ) (-t))
      have hd : Disjoint Λ (Λ \ N) := by rw [hYempty]; exact Finset.disjoint_empty_right _
      have hc := hfull.commute hB hd
      rw [hc.eq, sub_self, norm_zero]
      exact mul_nonneg (norm_nonneg _) <|
        mul_nonneg (localizationPrefactor_nonneg R) (Real.exp_pos _).le
  have hTrivial :
      ‖hermitianUnitaryPath (hamiltonian Λ Φ) t * term X *
            hermitianUnitaryPath (hamiltonian Λ Φ) (-t) -
          condExpect (graphNbhd_subset Λ {anchor X.1} l)
            (hermitianUnitaryPath (hamiltonian Λ Φ) t * term X *
              hermitianUnitaryPath (hamiltonian Λ Φ) (-t))‖ ≤
        ‖term X‖ * 2 := by
    calc
      _ ≤ ‖hermitianUnitaryPath (hamiltonian Λ Φ) t * term X *
              hermitianUnitaryPath (hamiltonian Λ Φ) (-t)‖ +
            ‖condExpect (graphNbhd_subset Λ {anchor X.1} l)
              (hermitianUnitaryPath (hamiltonian Λ Φ) t * term X *
                hermitianUnitaryPath (hamiltonian Λ Φ) (-t))‖ := norm_sub_le _ _
      _ ≤ ‖term X‖ + ‖term X‖ := by
        gcongr
        · exact (SpectralFilter.norm_hermitianUnitaryPath_conj
            hΦ.isHermitian_hamiltonian (term X) t).le
        · exact (norm_condExpect_le _ _).trans_eq
            (SpectralFilter.norm_hermitianUnitaryPath_conj
              hΦ.isHermitian_hamiltonian (term X) t)
      _ = ‖term X‖ * 2 := by ring
  rw [mul_min_of_nonneg _ _ (norm_nonneg (term X))]
  exact le_min hTrivial hExp

end LiebRobinson

end OpenAI
