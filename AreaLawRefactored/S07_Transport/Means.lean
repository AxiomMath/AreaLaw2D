import AreaLawForMathlib.Analysis.Matrix.WeightedGeometricMean
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

end MeanTree

end AreaLaw.Transport
