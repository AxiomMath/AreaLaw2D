/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/GraphLatticeDistance.lean`. Apache 2.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Int.NatAbs

/-!
# Ambient lattice distance along graph walks

The integer lattice distance is the sum of coordinate displacements. It satisfies the triangle
inequality, and a graph whose edges have ambient displacement at most one has walk displacement
at most the walk length. A finite extended graph distance therefore bounds ambient
displacement, including for graphs with holes or disconnected components. This is the
displacement comparison preceding the ball count `eq:ball-count` of [OAI265, §2.2].

## Implementation notes

The graph is an arbitrary `SimpleGraph V` with a coordinate map `V → ℤ × ℤ`, so the lemmas
apply to the induced graph `(hasse ℤ □ hasse ℤ).induce Λ` of `OpenAI.domainEDist` through
`Subtype.val`. The repository's other distance on `ℤ × ℤ` is Mathlib's sup metric `dist`,
which is not the `ℓ¹` distance used here.
-/

namespace OpenAI

/-- The ambient integer lattice distance, measured by the sum of coordinate displacements. -/
def latticeL1Distance (a b : ℤ × ℤ) : ℕ :=
  (a.1 - b.1).natAbs + (a.2 - b.2).natAbs

@[simp]
theorem latticeL1Distance_self (a : ℤ × ℤ) : latticeL1Distance a a = 0 := by
  simp [latticeL1Distance]

/-- Ambient lattice distance satisfies the triangle inequality. -/
theorem latticeL1Distance_triangle (a b c : ℤ × ℤ) :
    latticeL1Distance a c ≤ latticeL1Distance a b + latticeL1Distance b c := by
  have hx : (a.1 - c.1).natAbs ≤ (a.1 - b.1).natAbs + (b.1 - c.1).natAbs := by
    have he : a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) := by omega
    rw [he]
    exact Int.natAbs_add_le _ _
  have hy : (a.2 - c.2).natAbs ≤ (a.2 - b.2).natAbs + (b.2 - c.2).natAbs := by
    have he : a.2 - c.2 = (a.2 - b.2) + (b.2 - c.2) := by omega
    rw [he]
    exact Int.natAbs_add_le _ _
  dsimp only [latticeL1Distance]
  omega

variable {V : Type*} {G : SimpleGraph V} (coord : V → ℤ × ℤ)

/-- A walk has ambient displacement at most its length when each edge has displacement at most
one [OAI265, §2.2]. -/
theorem latticeL1Distance_le_walk_length
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    {a b : V} (p : G.Walk a b) : latticeL1Distance (coord a) (coord b) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
      calc
        latticeL1Distance (coord a) (coord c) ≤
            latticeL1Distance (coord a) (coord b) +
              latticeL1Distance (coord b) (coord c) :=
          latticeL1Distance_triangle _ _ _
        _ ≤ 1 + p.length := Nat.add_le_add (hstep hab) ih
        _ = (SimpleGraph.Walk.cons hab p).length := by simp [Nat.add_comm]

/-- A finite upper bound on extended graph distance also bounds ambient displacement
[OAI265, §2.2]. The extended distance is `⊤` between different components. -/
theorem latticeL1Distance_le_of_edist_le
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    {a b : V} {R : ℕ} (hdist : G.edist a b ≤ (R : ℕ∞)) :
    latticeL1Distance (coord a) (coord b) ≤ R := by
  have hfinite : G.edist a b < ⊤ := lt_of_le_of_lt hdist (by simp)
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top (ne_of_lt hfinite)
  have hlength : p.length ≤ R := by
    exact ENat.natCast_le_natCast.mp (hp.le.trans hdist)
  exact (latticeL1Distance_le_walk_length coord hstep p).trans hlength

end OpenAI
