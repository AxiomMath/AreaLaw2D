import AreaLawForMathlib.Analysis.Matrix.BlockDiagonalMean
import AreaLawForMathlib.Analysis.Matrix.PositiveMap
import Mathlib.Topology.UnitInterval

/-!
# §7.1 Positive matrix means and their derivatives

Digest `digest/07-transport.md` D7.1–D7.5, paper `paper/sections/06-transport.tex` 18–177.
The vertex operation `A #_p B` (D7.1) is the library's `Matrix.geomMean`
(`AreaLawForMathlib/Analysis/Matrix/WeightedGeometricMean.lean`), with its Kubo–Ando vertex
properties; the trees (D7.2), Lemma 7.1 (D7.3), the CP vocabulary (D7.4) and Lemma 7.2 (D7.5)
are here. No geometry: every statement is over an arbitrary finite index type `n`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Filter Topology

namespace AreaLaw.Transport

open Matrix

/-! ## D7.1 The weighted geometric mean -/

-- D7.1 (`transport:mean-def`): `A #_p B = A^{1/2} (A^{-1/2} B A^{-1/2})^p A^{1/2}` for positive
-- definite `A, B`, `0 ≤ p ≤ 1`, is the library `Matrix.geomMean p A B` (Kubo–Ando, Standard).

/-! ## D7.2 Weighted binary trees -/

/-- D7.2. A weighted binary tree: a finite rooted binary tree, a parameter `p ∈ [0, 1]` at each
internal vertex, outgoing edges of weights `1 - p` (first child) and `p` (second child); leaves
carry labels in `ι` (a label may occur at several leaves). -/
inductive MeanTree (ι : Type*) where
  /-- A terminal leaf with label `j`. -/
  | leaf (j : ι) : MeanTree ι
  /-- An internal vertex with parameter `p`, first child `l`, second child `r`. -/
  | node (p : I) (l r : MeanTree ι) : MeanTree ι

namespace MeanTree

variable {ι κ : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-- D7.2. The root `𝒯(A_j : j)`: leaves evaluated at their inputs, each internal vertex by
D7.1. -/
noncomputable def eval (A : ι → Matrix n n ℂ) : MeanTree ι → Matrix n n ℂ
  | leaf j => A j
  | node p l r => geomMean p (l.eval A) (r.eval A)

@[simp] theorem eval_leaf (A : ι → Matrix n n ℂ) (j : ι) : (leaf j).eval A = A j := rfl

@[simp] theorem eval_node (A : ι → Matrix n n ℂ) (p : I) (l r : MeanTree ι) :
    (node p l r).eval A = geomMean p (l.eval A) (r.eval A) := rfl

/-- D7.2. The terminal weights `w_j`: products of edge weights on root-to-leaf paths, summed
over the leaves carrying label `j`. -/
noncomputable def weight [DecidableEq ι] : MeanTree ι → ι → ℝ
  | leaf j => Pi.single j 1
  | node p l r => (1 - (p : ℝ)) • l.weight + (p : ℝ) • r.weight

theorem weight_node [DecidableEq ι] (p : I) (l r : MeanTree ι) (j : ι) :
    (node p l r).weight j = (1 - (p : ℝ)) * l.weight j + p * r.weight j := rfl

theorem weight_nonneg [DecidableEq ι] (T : MeanTree ι) (j : ι) : 0 ≤ T.weight j := by
  induction T with
  | leaf i => by_cases h : j = i <;> simp [weight, h]
  | node p l r ihl ihr =>
    rw [weight_node]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.2.2) ihl) (mul_nonneg p.2.1 ihr)

/-- D7.2. `∑_j w_j = 1`. -/
theorem sum_weight [DecidableEq ι] [Fintype ι] (T : MeanTree ι) : ∑ j, T.weight j = 1 := by
  induction T with
  | leaf j => simp [weight]
  | node p l r ihl ihr =>
    simp only [weight_node, Finset.sum_add_distrib, ← Finset.mul_sum, ihl, ihr]
    ring

/-- D7.2. The root of a tree with positive definite inputs is positive definite. -/
theorem posDef_eval {A : ι → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) (T : MeanTree ι) :
    (T.eval A).PosDef := by
  induction T with
  | leaf j => exact hA j
  | node p l r ihl ihr => exact ihl.geomMean ihr p

/-- Substitute the tree `f j` at every leaf `j` (used to attach choice trees, D7.9). -/
def bind : MeanTree ι → (ι → MeanTree κ) → MeanTree κ
  | leaf j, f => f j
  | node p l r, f => node p (l.bind f) (r.bind f)

/-- Relabel the leaves. -/
def map (f : ι → κ) (T : MeanTree ι) : MeanTree κ := T.bind fun j => leaf (f j)

theorem eval_bind (A : κ → Matrix n n ℂ) (T : MeanTree ι) (f : ι → MeanTree κ) :
    (T.bind f).eval A = T.eval fun j => (f j).eval A := by
  induction T with
  | leaf j => rfl
  | node p l r ihl ihr => simp only [bind, eval, ihl, ihr]

theorem eval_map (A : κ → Matrix n n ℂ) (T : MeanTree ι) (f : ι → κ) :
    (T.map f).eval A = T.eval (A ∘ f) :=
  eval_bind A T _

/-- A label of some leaf. -/
def someLabel : MeanTree ι → ι
  | leaf j => j
  | node _ l _ => l.someLabel

theorem eval_const {X : Matrix n n ℂ} (hX : X.PosDef) (T : MeanTree ι) :
    T.eval (fun _ ↦ X) = X := by
  induction T with
  | leaf j => rfl
  | node p l r ihl ihr => rw [eval_node, ihl, ihr, geomMean_self hX]

/-- A matrix commuting with every input commutes with the root. -/
theorem commute_eval_right {A : ι → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) {X : Matrix n n ℂ}
    (hX : ∀ j, Commute X (A j)) (T : MeanTree ι) : Commute X (T.eval A) := by
  induction T with
  | leaf j => exact hX j
  | node p l r ihl ihr =>
    exact Commute.geomMean_right (posDef_eval hA l) (posDef_eval hA r) ihl ihr p

/-- Roots of trees whose inputs commute across two families commute. -/
theorem commute_eval_eval {ι' : Type*} {A : ι → Matrix n n ℂ} {B : ι' → Matrix n n ℂ}
    (hA : ∀ j, (A j).PosDef) (hB : ∀ j, (B j).PosDef) (hAB : ∀ j j', Commute (A j) (B j'))
    (T : MeanTree ι) (T' : MeanTree ι') : Commute (T.eval A) (T'.eval B) :=
  commute_eval_right hB (fun j' ↦ (commute_eval_right hA (fun j ↦ (hAB j j').symm) T).symm) T'

end MeanTree

/-! ## D7.3 Lemma 7.1 -/

open MeanTree

variable {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n] {A A' : ι → Matrix n n ℂ}

/-- D7.3 Lemma 7.1 (1). Congruence: `𝒯(S^* A_j S : j) = S^* M S` for invertible `S`. -/
theorem lemma_7_1_1 (hA : ∀ j, (A j).PosDef) {S : Matrix n n ℂ} (hS : IsUnit S)
    (T : MeanTree ι) : T.eval (fun j ↦ star S * A j * S) = star S * T.eval A * S := by
  induction T with
  | leaf j => rfl
  | node p l r ihl ihr =>
    -- D7.3.7 (vertexwise), D7.3.1
    rw [eval_node, eval_node, ihl, ihr,
      geomMean_star_conj (posDef_eval hA l) (posDef_eval hA r) hS]

/-- D7.3 Lemma 7.1 (2). The root is monotone in each input. -/
theorem lemma_7_1_2 (hA : ∀ j, (A j).PosDef) (hAA' : ∀ j, A j ≤ A' j) (T : MeanTree ι) :
    T.eval A ≤ T.eval A' := by
  have hA' : ∀ j, (A' j).PosDef := fun j ↦ by
    simpa using (hA j).add_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hAA' j)))
  induction T with
  | leaf j => exact hAA' j
  | node p l r ihl ihr =>
    -- D7.3.7 (vertexwise), D7.3.4 (monotone in `B`; in `A` by D7.3.2)
    calc geomMean p (l.eval A) (r.eval A)
        ≤ geomMean p (l.eval A) (r.eval A') :=
          geomMean_mono_right (posDef_eval hA l) p.2 ihr
      _ ≤ geomMean p (l.eval A') (r.eval A') :=
          geomMean_mono_left (posDef_eval hA l) (posDef_eval hA' r) p.2 ihl

/-- D7.3 Lemma 7.1 (3). `𝒯(c_j A_j : j) = (∏_j c_j^{w_j}) M` for `c_j > 0`. -/
theorem lemma_7_1_3 [DecidableEq ι] [Fintype ι] (hA : ∀ j, (A j).PosDef) {c : ι → ℝ}
    (hc : ∀ j, 0 < c j) (T : MeanTree ι) :
    T.eval (fun j ↦ c j • A j) = (∏ j, c j ^ T.weight j) • T.eval A := by
  induction T with
  | leaf j =>
    simp only [eval_leaf, weight]
    rw [Finset.prod_eq_single j (fun i _ hij ↦ by simp [hij]) (by simp)]
    simp
  | node p l r ihl ihr =>
    have hpos : ∀ T : MeanTree ι, 0 < ∏ j, c j ^ T.weight j := fun T ↦
      Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hc j) _
    -- D7.3.5: the vertex scales by `c_L^{1-p} c_R^p`
    rw [eval_node, eval_node, ihl, ihr, geomMean_smul (posDef_eval hA l) (posDef_eval hA r)
      (hpos l) (hpos r)]
    congr 1
    -- D7.3.7: the exponent of `c_j` is `(1-p) w^L_j + p w^R_j`, the terminal weight
    rw [← Real.finsetProd_rpow _ _ (fun j _ ↦ (Real.rpow_pos_of_pos (hc j) _).le),
      ← Real.finsetProd_rpow _ _ (fun j _ ↦ (Real.rpow_pos_of_pos (hc j) _).le),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← Real.rpow_mul (hc j).le, ← Real.rpow_mul (hc j).le, ← Real.rpow_add (hc j),
      weight_node]
    ring_nf

private theorem prod_rpow_mul_prod_rpow [Fintype ι] {a u v : ι → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∏ j, a j ^ u j) ^ s * (∏ j, a j ^ v j) ^ t = ∏ j, a j ^ (s * u j + t * v j) := by
  rw [← Real.finsetProd_rpow _ _ (fun j _ ↦ Real.rpow_nonneg (ha j) _),
    ← Real.finsetProd_rpow _ _ (fun j _ ↦ Real.rpow_nonneg (ha j) _),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← Real.rpow_mul (ha j), ← Real.rpow_mul (ha j),
    ← Real.rpow_add_of_nonneg (ha j) (mul_nonneg (hu j) hs) (mul_nonneg (hv j) ht)]
  ring_nf

/-- D7.3 Lemma 7.1 (4). For every unit `z`: `⟨z, M z⟩ ≤ ∏_j ⟨z, A_j z⟩^{w_j}` (here for every
`z`). -/
theorem lemma_7_1_4 [DecidableEq ι] [Fintype ι] (hA : ∀ j, (A j).PosDef) (T : MeanTree ι)
    (z : n → ℂ) :
    (star z ⬝ᵥ (T.eval A *ᵥ z)).re ≤ ∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ T.weight j := by
  have hq : ∀ X : Matrix n n ℂ, X.PosDef → 0 ≤ (star z ⬝ᵥ (X *ᵥ z)).re :=
    fun X hX ↦ hX.posSemidef.re_dotProduct_nonneg z
  induction T with
  | leaf j =>
    simp only [eval_leaf, weight]
    rw [Finset.prod_eq_single j (fun i _ hij ↦ by simp [hij]) (by simp)]
    simp
  | node p l r ihl ihr =>
    have hp0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
    calc (star z ⬝ᵥ (geomMean p (l.eval A) (r.eval A) *ᵥ z)).re
        -- D7.3.6
        ≤ (star z ⬝ᵥ (l.eval A *ᵥ z)).re ^ (1 - (p : ℝ)) *
            (star z ⬝ᵥ (r.eval A *ᵥ z)).re ^ (p : ℝ) :=
          re_dotProduct_geomMean_le (posDef_eval hA l) (posDef_eval hA r) p.2 z
      -- D7.3.7: induction on the subtrees, `x ↦ x^{1-p}, x^p` monotone
      _ ≤ (∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ l.weight j) ^ (1 - (p : ℝ)) *
            (∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ r.weight j) ^ (p : ℝ) := by
          gcongr <;> first
            | exact hq _ (posDef_eval hA l)
            | exact hq _ (posDef_eval hA r)
            | exact Real.rpow_nonneg (hq _ (posDef_eval hA r)) _
            | exact p.2.1
            | exact Real.rpow_nonneg (Finset.prod_nonneg fun j _ ↦
                Real.rpow_nonneg (hq _ (hA j)) _) _
      _ = ∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ (node p l r).weight j := by
          rw [prod_rpow_mul_prod_rpow (fun j ↦ hq _ (hA j)) l.weight_nonneg r.weight_nonneg
            hp0 p.2.1]
          simp only [weight_node]

/-- D7.3 Lemma 7.1 (5). If `P` is an orthogonal projection and `A_j ≥ c_j P`, `c_j > 0`, then
`M ≥ (∏_j c_j^{w_j}) P`. -/
theorem lemma_7_1_5 [DecidableEq ι] [Fintype ι] (hA : ∀ j, (A j).PosDef)
    {P : Matrix n n ℂ} (hP : IsStarProjection P) {c : ι → ℝ} (hc : ∀ j, 0 < c j)
    (hAP : ∀ j, c j • P ≤ A j) (T : MeanTree ι) :
    (∏ j, c j ^ T.weight j) • P ≤ T.eval A := by
  have hP0 : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP.nonneg
  cases isEmpty_or_nonempty n with
  | inl _ => exact le_of_eq (Subsingleton.elim _ _)
  | inr _ =>
  set K := ∏ j, c j ^ T.weight j
  have hK : 0 < K := Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hc j) _
  have hlow : ∀ j, ∃ r : ℝ, 0 < r ∧ r • (1 : Matrix n n ℂ) ≤ A j := fun j ↦ by
    obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff
      (a := A j) (hA j).isHermitian.isSelfAdjoint).mpr fun x hx ↦
        (hA j).isStrictlyPositive.spectrum_pos hx
    exact ⟨r, hr, by simpa [Algebra.algebraMap_eq_smul_one] using hle⟩
  choose lam hlam hlamA using hlow
  have hstep : ∀ ε : ℝ, 0 < ε → ε < 1 → ((1 - ε) * K) • P ≤ T.eval A := by
    intro ε hε0 hε1
    have h1ε : 0 < 1 - ε := sub_pos.mpr hε1
    -- D7.3.9: a common `δ > 0` with `(1 - ε) c_j δ ≤ ε λ_min(A_j)` for all leaves
    set δ : ℝ := Finset.univ.inf' ⟨T.someLabel, Finset.mem_univ _⟩
      (fun j ↦ ε * lam j / ((1 - ε) * c j))
    have hδ : 0 < δ := by
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' ⟨T.someLabel, Finset.mem_univ _⟩
        (fun j ↦ ε * lam j / ((1 - ε) * c j))
      rw [show δ = _ from hj]
      exact div_pos (mul_pos hε0 (hlam j)) (mul_pos h1ε (hc j))
    have hδle : ∀ j, (1 - ε) * c j * δ ≤ ε * lam j := fun j ↦ by
      have : δ ≤ ε * lam j / ((1 - ε) * c j) := Finset.inf'_le _ (Finset.mem_univ j)
      rwa [le_div_iff₀ (mul_pos h1ε (hc j)), mul_comm] at this
    set Q : Matrix n n ℂ := P + δ • 1
    have hQ : Q.PosDef := by simpa [Q, add_comm] using (PosDef.one.smul hδ).add_posSemidef hP0
    -- D7.3.9: `A_j - (1-ε) c_j P = (1-ε)(A_j - c_j P) + ε A_j ≥ ε λ_min(A_j) I`, hence
    -- `A_j ≥ (1-ε) c_j (P + δ I)`, strictly positive
    have hin : ∀ j, ((1 - ε) * c j) • Q ≤ A j := fun j ↦ by
      have hsplit : A j - ((1 - ε) * c j) • Q =
          (1 - ε) • (A j - c j • P) + (ε • A j - ((1 - ε) * c j * δ) • 1) := by
        simp only [Q, smul_add, smul_smul, smul_sub]
        module
      rw [← sub_nonneg, hsplit]
      refine add_nonneg (smul_nonneg h1ε.le (sub_nonneg.mpr (hAP j))) ?_
      rw [sub_nonneg]
      calc ((1 - ε) * c j * δ) • (1 : Matrix n n ℂ) ≤ (ε * lam j) • 1 :=
            smul_le_smul_of_nonneg_right (hδle j) zero_le_one
        _ = ε • (lam j • 1) := by rw [smul_smul]
        _ ≤ ε • A j := smul_le_smul_of_nonneg_left (hlamA j) hε0.le
    -- D7.3.9: monotonicity (2), homogeneity (3) and idempotence D7.3.8
    have hmono := lemma_7_1_2 (A := fun j ↦ ((1 - ε) * c j) • Q)
      (fun j ↦ hQ.smul (mul_pos h1ε (hc j))) hin T
    rw [lemma_7_1_3 (fun _ ↦ hQ) (fun j ↦ mul_pos h1ε (hc j)), eval_const hQ] at hmono
    have hprod : ∏ j, ((1 - ε) * c j) ^ T.weight j = (1 - ε) * K := by
      simp only [K]
      rw [Finset.prod_congr rfl (fun j _ ↦ Real.mul_rpow h1ε.le (hc j).le),
        Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos h1ε, T.sum_weight, Real.rpow_one]
    rw [hprod] at hmono
    exact le_trans (smul_le_smul_of_nonneg_left (le_add_of_nonneg_right
      (smul_nonneg hδ.le zero_le_one)) (mul_pos h1ε hK).le) hmono
  -- D7.3.9: let `ε ↓ 0`
  have htend : Tendsto (fun k : ℕ ↦ ((1 - 1 / ((k : ℝ) + 2)) * K) • P) atTop (𝓝 (K • P)) := by
    have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun k ↦ ?_
      simp only [Function.comp, Nat.cast_add, Nat.cast_one]
      ring_nf
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub h0).mul_const K).smul_const P
  refine le_of_tendsto' htend fun k ↦ hstep _ (by positivity) ?_
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

private theorem posDef_listProd_ofFn {K : ℕ} {D : Fin K → Matrix n n ℂ}
    (hD : ∀ g, (D g).PosDef) (hcomm : ∀ g g', g ≠ g' → Commute (D g) (D g')) :
    (List.ofFn D).prod.PosDef := by
  induction K with
  | zero => simpa using PosDef.one
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine (hD 0).mul_of_commute (ih (D := fun g ↦ D g.succ) (fun g ↦ hD _)
      (fun g g' h ↦ hcomm _ _ (fun h' ↦ h (Fin.succ_injective _ h'))))
      (Commute.list_prod_right _ _ fun y hy ↦ ?_)
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
    exact hcomm _ _ (Fin.succ_ne_zero g).symm

/-- D7.3 Lemma 7.1 (6). If `A_j = ∏_{g=1}^K A_{j,g}` with positive definite factors and every
factor of band `g` commutes with every factor of band `g' ≠ g` (all leaves), then
`M = ∏_g M_g`, `M_g` the root of the same tree on the inputs `(A_{j,g})_j`, and the `M_g`
commute. -/
theorem lemma_7_1_6 {K : ℕ} {D : ι → Fin K → Matrix n n ℂ} (hD : ∀ j g, (D j g).PosDef)
    (hcomm : ∀ j j' g g', g ≠ g' → Commute (D j g) (D j' g')) (T : MeanTree ι) :
    T.eval (fun j ↦ (List.ofFn (D j)).prod) = (List.ofFn fun g ↦ T.eval (D · g)).prod ∧
      ∀ g g', g ≠ g' → Commute (T.eval (D · g)) (T.eval (D · g')) := by
  -- D7.3.11: the `M_g` commute
  refine ⟨?_, fun g g' hgg' ↦ commute_eval_eval (fun j ↦ hD j g) (fun j ↦ hD j g')
    (fun j j' ↦ hcomm j j' g g' hgg') T T⟩
  induction K with
  | zero => simpa using eval_const PosDef.one T
  | succ K ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    have hrest : ∀ j, (List.ofFn fun g : Fin K ↦ D j g.succ).prod.PosDef := fun j ↦
      posDef_listProd_ofFn (fun g ↦ hD j _)
        (fun g g' h ↦ hcomm j j _ _ (fun h' ↦ h (Fin.succ_injective _ h')))
    have hAB : ∀ j j', Commute (D j 0) (List.ofFn fun g : Fin K ↦ D j' g.succ).prod :=
      fun j j' ↦ Commute.list_prod_right _ _ fun y hy ↦ by
        obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
        exact hcomm _ _ _ _ (Fin.succ_ne_zero g).symm
    -- D7.3.10 at every vertex (band `0` against the product of the others), D7.3.11
    have hmul : ∀ T : MeanTree ι,
        T.eval (fun j ↦ D j 0 * (List.ofFn fun g : Fin K ↦ D j g.succ).prod) =
          T.eval (D · 0) * T.eval (fun j ↦ (List.ofFn fun g : Fin K ↦ D j g.succ).prod) := by
      intro T
      induction T with
      | leaf j => rfl
      | node p l r ihl ihr =>
        rw [eval_node, eval_node, eval_node, ihl, ihr]
        exact geomMean_mul_of_commute (posDef_eval (fun j ↦ hD j 0) l) (posDef_eval hrest l)
          (posDef_eval (fun j ↦ hD j 0) r) (posDef_eval hrest r)
          (commute_eval_eval (fun j ↦ hD j 0) hrest hAB l l)
          (commute_eval_eval (fun j ↦ hD j 0) hrest hAB l r)
          (commute_eval_eval (fun j ↦ hD j 0) hrest hAB r l)
          (commute_eval_eval (fun j ↦ hD j 0) hrest hAB r r) p
    rw [hmul, ih (D := fun j g ↦ D j g.succ) (fun j g ↦ hD j _)
      (fun j j' g g' h ↦ hcomm _ _ _ _ (fun h' ↦ h (Fin.succ_injective _ h')))]

/-- D7.3 **Lemma 7.1** (properties of a finite mean tree). `𝒯` a weighted binary tree with
terminal weights `w_j`, positive definite inputs `A_j`, root `M`:
1. `𝒯(S^* A_j S : j) = S^* M S` for invertible `S`;
2. `M` is monotone in each input;
3. `𝒯(c_j A_j : j) = (∏_j c_j^{w_j}) M` for `c_j > 0`;
4. for every unit `z`: `⟨z, M z⟩ ≤ ∏_j ⟨z, A_j z⟩^{w_j}`;
5. if `P` is an orthogonal projection and `A_j ≥ c_j P`, `c_j > 0`, then
   `M ≥ (∏_j c_j^{w_j}) P`;
6. if `A_j = ∏_{g=1}^K A_{j,g}` with positive definite factors and every factor of band `g`
   commutes with every factor of band `g' ≠ g` (all leaves), then `M = ∏_g M_g`, `M_g` the root
   of the same tree on the inputs `(A_{j,g})_j`, and the `M_g` commute. -/
theorem lemma_7_1 [DecidableEq ι] [Fintype ι] (hA : ∀ j, (A j).PosDef) (T : MeanTree ι) :
    (∀ S : Matrix n n ℂ, IsUnit S →
      T.eval (fun j ↦ star S * A j * S) = star S * T.eval A * S) ∧
    (∀ A' : ι → Matrix n n ℂ, (∀ j, A j ≤ A' j) → T.eval A ≤ T.eval A') ∧
    (∀ c : ι → ℝ, (∀ j, 0 < c j) →
      T.eval (fun j ↦ c j • A j) = (∏ j, c j ^ T.weight j) • T.eval A) ∧
    (∀ z : n → ℂ, star z ⬝ᵥ z = 1 →
      (star z ⬝ᵥ (T.eval A *ᵥ z)).re ≤ ∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ T.weight j) ∧
    (∀ (P : Matrix n n ℂ) (c : ι → ℝ), IsStarProjection P → (∀ j, 0 < c j) →
      (∀ j, c j • P ≤ A j) → (∏ j, c j ^ T.weight j) • P ≤ T.eval A) ∧
    (∀ (K : ℕ) (D : ι → Fin K → Matrix n n ℂ), (∀ j g, (D j g).PosDef) →
      (∀ j j' g g', g ≠ g' → Commute (D j g) (D j' g')) → (∀ j, A j = (List.ofFn (D j)).prod) →
      T.eval A = (List.ofFn fun g ↦ T.eval (D · g)).prod ∧
        ∀ g g', g ≠ g' → Commute (T.eval (D · g)) (T.eval (D · g'))) :=
  ⟨fun _ hS ↦ lemma_7_1_1 hA hS T, fun _ h ↦ lemma_7_1_2 hA h T,
    fun _ hc ↦ lemma_7_1_3 hA hc T, fun z _ ↦ lemma_7_1_4 hA T z,
    fun _ _ hP hc hAP ↦ lemma_7_1_5 hA hP hc hAP T,
    fun _ D hD hcomm hAD ↦ by
      obtain rfl : A = fun j ↦ (List.ofFn (D j)).prod := funext hAD
      exact lemma_7_1_6 hD hcomm T⟩

/-! ## D7.4 Completely positive and unital maps

D7.4: a linear map on matrices is completely positive if its entrywise action on every matrix
amplification preserves positive semidefinite matrices (the library `IsCompletelyPositive`,
`AreaLawForMathlib/Analysis/Matrix/NPositiveMap.lean`); unital: it maps `I` to `I`. -/

/-! ## D7.5 Lemma 7.2: normalized derivative maps -/

namespace MeanTree

variable [DecidableEq ι]

/-- The labels of the leaves, from left to right. -/
def labels : MeanTree ι → List ι
  | leaf j => [j]
  | node _ l r => l.labels ++ r.labels

theorem weight_eq_zero_of_not_mem {T : MeanTree ι} {j : ι} (hj : j ∉ T.labels) :
    T.weight j = 0 := by
  induction T with
  | leaf i =>
    simp only [labels, List.mem_singleton] at hj
    simp [weight, hj]
  | node p l r ihl ihr =>
    simp only [labels, List.mem_append, not_or] at hj
    rw [weight_node, ihl hj.1, ihr hj.2]; ring

theorem eval_update_of_not_mem {T : MeanTree ι} {j : ι} (hj : j ∉ T.labels)
    (X : Matrix n n ℂ) : T.eval (Function.update A j X) = T.eval A := by
  induction T with
  | leaf i =>
    simp only [labels, List.mem_singleton] at hj
    simp [Function.update_of_ne (Ne.symm hj)]
  | node p l r ihl ihr =>
    simp only [labels, List.mem_append, not_or] at hj
    rw [eval_node, eval_node, ihl hj.1, ihr hj.2]

omit [DecidableEq ι] in
theorem isHermitian_eval (hA : ∀ i, (A i).IsHermitian) (T : MeanTree ι) :
    (T.eval A).IsHermitian := by
  cases T with
  | leaf i => exact hA i
  | node p l r => exact isHermitian_geomMean _ _ _

/-- `∂_{A_j} M`: at each vertex the partial derivatives of the mean in its two children,
composed with the derivatives of the subtrees (chain rule). -/
noncomputable def derivLabel (A : ι → Matrix n n ℂ) (j : ι) :
    MeanTree ι → Matrix n n ℂ →L[ℂ] Matrix n n ℂ
  | leaf i => if i = j then ContinuousLinearMap.id ℂ _ else 0
  | node p l r =>
    geomMeanDerivLeft p (l.eval A) (r.eval A) ∘L l.derivLabel A j +
      geomMeanDerivRight p (l.eval A) (r.eval A) ∘L r.derivLabel A j

theorem derivLabel_of_not_mem {T : MeanTree ι} {j : ι} (hj : j ∉ T.labels) :
    T.derivLabel A j = 0 := by
  induction T with
  | leaf i =>
    simp only [labels, List.mem_singleton] at hj
    simp [derivLabel, Ne.symm hj]
  | node p l r ihl ihr =>
    simp only [labels, List.mem_append, not_or] at hj
    simp [derivLabel, ihl hj.1, ihr hj.2]

private theorem HasFDerivWithinAt.comp_of_eq' {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G]
    [NormedSpace ℂ G] {g : F → G} {g' : F →L[ℂ] G} {f : E → F} {f' : E →L[ℂ] F}
    {s : Set E} {t : Set F} {x : E} {y : F} (hg : HasFDerivWithinAt g g' t y)
    (hf : HasFDerivWithinAt f f' s x) (hst : Set.MapsTo f s t) (hy : f x = y) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x := by
  subst hy; exact hg.comp x hf hst

/-- D7.5.6 (chain rule). For distinct leaf labels and positive definite inputs, the root is
Fréchet differentiable in the input `A_j` along Hermitian matrices, with derivative
`derivLabel A j`. -/
theorem hasFDerivWithinAt_eval_update (hA : ∀ i, (A i).PosDef) (T : MeanTree ι)
    (hT : T.labels.Nodup) (j : ι) :
    HasFDerivWithinAt (fun X ↦ T.eval (Function.update A j X)) (T.derivLabel A j)
      (hermitianSet n) (A j) := by
  induction T with
  | leaf i =>
    by_cases hij : i = j
    · subst hij
      simp only [derivLabel, ↓reduceIte, eval_leaf, Function.update_self]
      exact hasFDerivWithinAt_id (𝕜 := ℂ) (A i) (hermitianSet n)
    · simpa [derivLabel, hij, Function.update_of_ne hij] using
        hasFDerivWithinAt_const (𝕜 := ℂ) (A i) (A j) (hermitianSet n)
  | node p l r ihl ihr =>
    simp only [labels, List.nodup_append] at hT
    obtain ⟨hl, hr, hdisj⟩ := hT
    have hmaps : ∀ T' : MeanTree ι, Set.MapsTo (fun X ↦ T'.eval (Function.update A j X))
        (hermitianSet n) (hermitianSet n) := fun T' X hX ↦ by
      refine isHermitian_eval (fun i ↦ ?_) T'
      by_cases hij : i = j
      · subst hij; simpa [hermitianSet] using hX
      · simpa [Function.update_of_ne hij] using (hA i).isHermitian
    have hpt : ∀ T' : MeanTree ι, T'.eval (Function.update A j (A j)) = T'.eval A := by
      intro T'; rw [Function.update_eq_self]
    by_cases hjl : j ∈ l.labels
    · have hjr : j ∉ r.labels := fun h ↦ hdisj j hjl j h rfl
      have hfun : (fun X ↦ (node p l r).eval (Function.update A j X)) =
          (fun Y ↦ geomMean p Y (r.eval A)) ∘ fun X ↦ l.eval (Function.update A j X) := by
        ext1 X; simp [eval_update_of_not_mem hjr]
      rw [hfun]
      have := HasFDerivWithinAt.comp_of_eq'
        (hasFDerivWithinAt_geomMean_left (posDef_eval hA l) (posDef_eval hA r) p.2)
        (ihl hl) (hmaps l) (hpt l)
      simpa [derivLabel, derivLabel_of_not_mem hjr] using this
    · have hfun : (fun X ↦ (node p l r).eval (Function.update A j X)) =
          (fun Y ↦ geomMean p (l.eval A) Y) ∘ fun X ↦ r.eval (Function.update A j X) := by
        ext1 X; simp [eval_update_of_not_mem hjl]
      rw [hfun]
      have := HasFDerivWithinAt.comp_of_eq'
        (hasFDerivWithinAt_geomMean_right (posDef_eval hA l) (posDef_eval hA r) p.2)
        (ihr hr) (hmaps r) (hpt r)
      simpa [derivLabel, derivLabel_of_not_mem hjl] using this

/-- D7.5.5 along the tree: `∂_{A_j} M[A_j] = w_j M`. -/
theorem derivLabel_self (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) (j : ι) :
    T.derivLabel A j (A j) = T.weight j • T.eval A := by
  induction T with
  | leaf i =>
    by_cases hij : i = j
    · subst hij; simp [derivLabel, weight]
    · simp [derivLabel, weight, hij, Ne.symm hij]
  | node p l r ihl ihr =>
    simp only [derivLabel, _root_.add_apply, ContinuousLinearMap.comp_apply,
      ihl, ihr, ContinuousLinearMap.map_smul_of_tower, eval_node]
    rw [geomMeanDerivLeft_self (posDef_eval hA l) (posDef_eval hA r) p.2,
      geomMeanDerivRight_self (posDef_eval hA l) (posDef_eval hA r) p.2, weight_node,
      smul_smul, smul_smul, ← add_smul]
    congr 1; ring

/-- D7.5.3–D7.5.4 along the tree: `∂_{A_j} M` is completely positive. -/
theorem isNPositiveMap_derivLabel (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) (j : ι)
    (k : ℕ) : IsNPositiveMap k (T.derivLabel A j).toLinearMap := by
  induction T with
  | leaf i =>
    unfold derivLabel
    split_ifs
    · exact isNPositiveMap_id k
    · simpa using IsNPositiveMap.zero (n := n) k
  | node p l r ihl ihr =>
    have h1 := isNPositiveMap_geomMeanDerivLeft (posDef_eval hA l) (posDef_eval hA r) p.2 k
    have h2 := isNPositiveMap_geomMeanDerivRight (posDef_eval hA l) (posDef_eval hA r) p.2 k
    rw [derivLabel, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_comp]
    exact (IsNPositiveMap.comp h1 ihl).add (IsNPositiveMap.comp h2 ihr)

/-- D7.5 (`transport:leaf-map`). The normalized leaf map
`Φ_j(Z) = w_j⁻¹ M^{-1/2} ∂_{A_j} M[A_j^{1/2} Z A_j^{1/2}] M^{-1/2}`. -/
noncomputable def leafMap (A : ι → Matrix n n ℂ) (j : ι) (T : MeanTree ι) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  normalizedDerivMap (T.derivLabel A j) (T.weight j) (T.eval A) (A j)

/-- D7.5 (`transport:edge-map`). The normalized map `Φ_D` at the first child `D` of
`node p l r` (edge weight `1 - p`). -/
noncomputable def edgeMapLeft (A : ι → Matrix n n ℂ) (p : I) (l r : MeanTree ι) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  normalizedDerivMap (geomMeanDerivLeft p (l.eval A) (r.eval A)) (1 - p)
    ((node p l r).eval A) (l.eval A)

/-- D7.5 (`transport:edge-map`). The normalized map `Φ_D` at the second child `D` of
`node p l r` (edge weight `p`). -/
noncomputable def edgeMapRight (A : ι → Matrix n n ℂ) (p : I) (l r : MeanTree ι) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  normalizedDerivMap (geomMeanDerivRight p (l.eval A) (r.eval A)) p
    ((node p l r).eval A) (r.eval A)

/-- D7.5.6: the square-root normalizations cancel at the middle vertex. -/
private theorem normalizedDerivMap_comp {L₁ L₂ : Matrix n n ℂ →L[ℂ] Matrix n n ℂ}
    {w₁ w₂ : ℝ} {M D E : Matrix n n ℂ} (hD : D.PosDef) (Z : Matrix n n ℂ) :
    normalizedDerivMap L₁ w₁ M D (normalizedDerivMap L₂ w₂ D E Z) =
      normalizedDerivMap (L₁ ∘L L₂) (w₁ * w₂) M E Z := by
  have key : ∀ Y : Matrix n n ℂ,
      D ^ (1 / 2 : ℝ) * (D ^ (-(1 / 2) : ℝ) * Y * D ^ (-(1 / 2) : ℝ)) * D ^ (1 / 2 : ℝ) = Y := by
    intro Y
    calc D ^ (1 / 2 : ℝ) * (D ^ (-(1 / 2) : ℝ) * Y * D ^ (-(1 / 2) : ℝ)) * D ^ (1 / 2 : ℝ)
        = (D ^ (1 / 2 : ℝ) * D ^ (-(1 / 2) : ℝ)) * Y *
            (D ^ (-(1 / 2) : ℝ) * D ^ (1 / 2 : ℝ)) := by noncomm_ring
      _ = Y := by rw [hD.rpow_mul_rpow_neg, hD.rpow_neg_mul_rpow, one_mul, mul_one]
  simp only [normalizedDerivMap, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, sandwichL_apply]
  rw [mul_smul_comm, smul_mul_assoc, key, ContinuousLinearMap.map_smul_of_tower, mul_smul_comm,
    smul_mul_assoc, smul_smul, mul_inv]

theorem leafMap_leaf (hA : ∀ i, (A i).PosDef) (j : ι) (Z : Matrix n n ℂ) :
    (leaf j : MeanTree ι).leafMap A j Z = Z := by
  simp only [leafMap, normalizedDerivMap, derivLabel, ↓reduceIte, weight,
    Pi.single_eq_same, inv_one, one_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, sandwichL_apply, eval_leaf]
  calc A j ^ (-(1 / 2) : ℝ) * (A j ^ (1 / 2 : ℝ) * Z * A j ^ (1 / 2 : ℝ)) *
        A j ^ (-(1 / 2) : ℝ)
      = (A j ^ (-(1 / 2) : ℝ) * A j ^ (1 / 2 : ℝ)) * Z *
          (A j ^ (1 / 2 : ℝ) * A j ^ (-(1 / 2) : ℝ)) := by noncomm_ring
    _ = Z := by rw [(hA j).rpow_neg_mul_rpow, (hA j).rpow_mul_rpow_neg, one_mul, mul_one]

theorem leafMap_node_left (hA : ∀ i, (A i).PosDef) (p : I) (l r : MeanTree ι) {j : ι}
    (hjr : j ∉ r.labels) (Z : Matrix n n ℂ) :
    (node p l r).leafMap A j Z = edgeMapLeft A p l r (l.leafMap A j Z) := by
  simp only [edgeMapLeft, leafMap]
  rw [normalizedDerivMap_comp (posDef_eval hA l)]
  simp [derivLabel, derivLabel_of_not_mem hjr, weight_node, weight_eq_zero_of_not_mem hjr]

theorem leafMap_node_right (hA : ∀ i, (A i).PosDef) (p : I) (l r : MeanTree ι) {j : ι}
    (hjl : j ∉ l.labels) (Z : Matrix n n ℂ) :
    (node p l r).leafMap A j Z = edgeMapRight A p l r (r.leafMap A j Z) := by
  simp only [edgeMapRight, leafMap]
  rw [normalizedDerivMap_comp (posDef_eval hA r)]
  simp [derivLabel, derivLabel_of_not_mem hjl, weight_node, weight_eq_zero_of_not_mem hjl]

omit [DecidableEq ι] in
/-- D7.5.7: a tree with block-diagonal inputs has block-diagonal root, the roots of the two
trees of diagonal blocks. -/
theorem eval_fromBlocks_diag {m : Type*} [Fintype m] [DecidableEq m] {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef) (T : MeanTree ι) :
    T.eval (fun i ↦ fromBlocks (A i) 0 0 (B i)) = fromBlocks (T.eval A) 0 0 (T.eval B) := by
  induction T with
  | leaf i => rfl
  | node p l r ihl ihr =>
    rw [eval_node, eval_node, eval_node, ihl, ihr]
    exact geomMean_fromBlocks_diag (posDef_eval hA l) (posDef_eval hB l) (posDef_eval hA r)
      (posDef_eval hB r) p

theorem isBlockDiagonalMap_derivLabel {m : Type*} [Fintype m] [DecidableEq m]
    {B : ι → Matrix m m ℂ} (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (T : MeanTree ι) (j : ι) :
    IsBlockDiagonalMap (T.derivLabel (fun i ↦ fromBlocks (A i) 0 0 (B i)) j)
      (T.derivLabel A j) (T.derivLabel B j) := by
  induction T with
  | leaf i =>
    unfold derivLabel
    split_ifs
    · exact IsBlockDiagonalMap.id
    · exact IsBlockDiagonalMap.zero
  | node p l r ihl ihr =>
    unfold derivLabel
    rw [eval_fromBlocks_diag hA hB l, eval_fromBlocks_diag hA hB r]
    exact ((isBlockDiagonalMap_geomMeanDerivLeft (posDef_eval hA l) (posDef_eval hB l)
      (posDef_eval hA r) (posDef_eval hB r) p.2).comp ihl).add
      ((isBlockDiagonalMap_geomMeanDerivRight (posDef_eval hA l) (posDef_eval hB l)
        (posDef_eval hA r) (posDef_eval hB r) p.2).comp ihr)

/-- The leaf identity `M^{-1/2} ∂_{A_j} M[A_j^{1/2} Z A_j^{1/2}] M^{-1/2} = w_j Φ_j(Z)`. -/
theorem sandwich_derivLabel_eq_smul_leafMap (T : MeanTree ι) {j : ι} (hw : T.weight j ≠ 0)
    (Z : Matrix n n ℂ) :
    T.eval A ^ (-(1 / 2) : ℝ) * T.derivLabel A j (A j ^ (1 / 2 : ℝ) * Z * A j ^ (1 / 2 : ℝ)) *
        T.eval A ^ (-(1 / 2) : ℝ) = T.weight j • T.leafMap A j Z := by
  simp only [leafMap, normalizedDerivMap, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, sandwichL_apply, smul_smul, mul_inv_cancel₀ hw, one_smul]

/-- The trace-pairing dual `Φ_j^*`, `Tr(Φ_j^*(σ) Z) = Tr(σ Φ_j(Z))`. -/
noncomputable def leafDual (A : ι → Matrix n n ℂ) (j : ι) (T : MeanTree ι) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  traceAdjointMap (T.leafMap A j).toLinearMap

end MeanTree

/-- D7.5 **Lemma 7.2** (normalized derivative maps). At a binary vertex with output `M` and a
child `D` of positive edge weight `w`, `Φ_D(Z) = w⁻¹ M^{-1/2} ∂_D M[D^{1/2} Z D^{1/2}] M^{-1/2}`
(`∂_D` the Fréchet derivative in `D`, other child and weight fixed) is unital and CP. Composing
these maps from terminal leaf `j` to the root gives a unital CP map `Φ_j` with
`M^{-1/2} ∂_{A_j} M[A_j^{1/2} Z A_j^{1/2}] M^{-1/2} = w_j Φ_j(Z)`. If all inputs are block
diagonal for a fixed orthogonal decomposition, the maps preserve each block: the `(a,b)` block
of `Φ_j(Z)` depends only on the `(a,b)` block of `Z`, and on the first diagonal block `Φ_j` is
the normalized derivative map of the tree of first diagonal blocks, independent of the other
diagonal blocks. -/
theorem lemma_7_2 [DecidableEq ι] (hA : ∀ j, (A j).PosDef) (T : MeanTree ι)
    (hT : T.labels.Nodup) :
    -- the vertex maps
    (∀ (p : I) (D E : Matrix n n ℂ), D.PosDef → E.PosDef →
      HasFDerivWithinAt (fun X ↦ geomMean p X E) (geomMeanDerivLeft p D E)
        (hermitianSet n) D ∧
      HasFDerivWithinAt (fun X ↦ geomMean p D X) (geomMeanDerivRight p D E)
        (hermitianSet n) E ∧
      ((p : ℝ) < 1 → normalizedDerivMap (geomMeanDerivLeft p D E) (1 - p) (geomMean p D E) D 1 = 1
        ∧ IsCompletelyPositive
          (normalizedDerivMap (geomMeanDerivLeft p D E) (1 - p) (geomMean p D E) D).toLinearMap) ∧
      (0 < (p : ℝ) → normalizedDerivMap (geomMeanDerivRight p D E) p (geomMean p D E) E 1 = 1 ∧
        IsCompletelyPositive
          (normalizedDerivMap (geomMeanDerivRight p D E) p (geomMean p D E) E).toLinearMap)) ∧
    -- composition from the leaf to the root
    (∀ j, (∀ Z, (leaf j : MeanTree ι).leafMap A j Z = Z) ∧
      ∀ (p : I) (l r : MeanTree ι) (Z : Matrix n n ℂ),
        (j ∉ r.labels → (node p l r).leafMap A j Z = edgeMapLeft A p l r (l.leafMap A j Z)) ∧
        (j ∉ l.labels → (node p l r).leafMap A j Z = edgeMapRight A p l r (r.leafMap A j Z))) ∧
    -- the leaf identity, unital, CP
    (∀ j, HasFDerivWithinAt (fun X ↦ T.eval (Function.update A j X)) (T.derivLabel A j)
        (hermitianSet n) (A j) ∧
      (0 < T.weight j → ∀ Z, T.eval A ^ (-(1 / 2) : ℝ) *
          T.derivLabel A j (A j ^ (1 / 2 : ℝ) * Z * A j ^ (1 / 2 : ℝ)) *
          T.eval A ^ (-(1 / 2) : ℝ) = T.weight j • T.leafMap A j Z) ∧
      IsCompletelyPositive (T.leafMap A j).toLinearMap ∧
      (0 < T.weight j → T.leafMap A j 1 = 1)) ∧
    -- blocks
    (∀ {m : Type*} [Fintype m] [DecidableEq m] (B : ι → Matrix m m ℂ), (∀ j, (B j).PosDef) →
      ∀ j, IsBlockDiagonalMap (T.leafMap (fun i ↦ fromBlocks (A i) 0 0 (B i)) j)
        (T.leafMap A j) (T.leafMap B j)) := by
  refine ⟨fun p D E hD hE ↦ ⟨?_, ?_, fun hp ↦ ⟨?_, fun k ↦ ?_⟩, fun hp ↦ ⟨?_, fun k ↦ ?_⟩⟩,
    fun j ↦ ⟨leafMap_leaf hA j, fun p l r Z ↦ ⟨fun hjr ↦ leafMap_node_left hA p l r hjr Z,
      fun hjl ↦ leafMap_node_right hA p l r hjl Z⟩⟩, fun j ↦ ⟨?_, fun hw Z ↦ ?_, fun k ↦ ?_, ?_⟩,
    fun B hB j ↦ ?_⟩
  -- D7.5.1–D7.5.2: the power `C ↦ C^p` is Fréchet differentiable (integral formula), hence so
  -- is the vertex in each child; D7.5.4 for the first child by exchange symmetry
  · exact hasFDerivWithinAt_geomMean_left hD hE p.2
  · exact hasFDerivWithinAt_geomMean_right hD hE p.2
  -- D7.5.5: unital, by homogeneity (first child, weight `1 - p`)
  · exact normalizedDerivMap_left_one hD hE ⟨p.2.1, hp⟩
  -- D7.5.4: CP for the first child by exchange symmetry
  · exact isNPositiveMap_normalizedDerivMap_left hD hE p.2 k
  -- D7.5.5: unital (second child, weight `p`)
  · exact normalizedDerivMap_right_one hD hE ⟨hp, p.2.2⟩
  -- D7.5.3: CP for the second child (sandwich integral of CP maps)
  · exact isNPositiveMap_normalizedDerivMap_right hD hE p.2 k
  -- D7.5.6: chain rule along the path from leaf `j` to the root
  · exact hasFDerivWithinAt_eval_update hA T hT j
  · simp only [leafMap, normalizedDerivMap, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, sandwichL_apply, smul_smul, mul_inv_cancel₀ hw.ne',
      one_smul]
  -- D7.5.6: compositions of CP maps are CP
  · exact isNPositiveMap_normalizedDerivMap (isNPositiveMap_derivLabel hA T j k)
      (T.weight_nonneg j) (posDef_eval hA T) (hA j)
  -- D7.5.6: `∏_i w_i = w_j`, unital
  · exact fun hw ↦ normalizedDerivMap_one hw.ne' (posDef_eval hA T) (hA j) (derivLabel_self hA T j)
  -- D7.5.7: blocks
  · unfold MeanTree.leafMap
    rw [eval_fromBlocks_diag hA hB T]
    exact (isBlockDiagonalMap_derivLabel hA hB T j).normalizedDerivMap _ (posDef_eval hA T)
      (posDef_eval hB T) (hA j) (hB j)

/-- D7.5 Output, used by D7.16.7: for unital CP `Φ_j`, the dual `Φ_j^*` maps positive
semidefinite matrices to positive semidefinite matrices and preserves the trace. -/
theorem leafDual_posSemidef_trace [DecidableEq ι] (hA : ∀ j, (A j).PosDef) (T : MeanTree ι)
    (j : ι) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (T.leafDual A j ρ).PosSemidef ∧ (0 < T.weight j → (T.leafDual A j ρ).trace = ρ.trace) ∧
      ∀ Z, (T.leafDual A j ρ * Z).trace = (ρ * T.leafMap A j Z).trace := by
  refine ⟨(isNPositiveMap_one_iff_isPositiveMap.mp (isNPositiveMap_normalizedDerivMap
    (isNPositiveMap_derivLabel hA T j 1) (T.weight_nonneg j) (posDef_eval hA T) (hA j))
    ).traceAdjointMap ρ hρ, fun hw ↦ ?_, fun Z ↦ trace_traceAdjointMap_mul _ ρ Z⟩
  have h := trace_traceAdjointMap_mul (T.leafMap A j).toLinearMap ρ 1
  have h1 : T.leafMap A j 1 = 1 :=
    normalizedDerivMap_one hw.ne' (posDef_eval hA T) (hA j) (derivLabel_self hA T j)
  rwa [Matrix.mul_one, ContinuousLinearMap.coe_coe, h1, Matrix.mul_one] at h

end AreaLaw.Transport
