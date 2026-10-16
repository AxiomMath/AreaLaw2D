import OpenAI.Geometry.DistanceLayers

/-!
# Bridge from planar layer distances to the frozen ambient lattice distance

The dyadic construction is carried out in the real plane with Mathlib's sup
product metric, while `OpenAI.TwoFamilyDecomposition` states clearance using
`OpenAI.ambientEDist` on finite subsets of `ℤ × ℤ`.  These lemmas make that
conversion explicit and keep `ambientEDist` as the only exported clearance
notion.
-/

namespace OpenAI.Geometry

/-- The integer-point embedding preserves the sup product distance. -/
@[simp] theorem dist_integerPoint (x y : ℤ × ℤ) :
    dist (integerPoint x) (integerPoint y) = dist x y := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Int.dist_eq, Int.dist_eq]
  rfl

/-- A pointwise strict planar separation gives the frozen `ENNReal`
set-to-set clearance. -/
theorem ofReal_lt_ambientEDist_of_integerPoint_dist {c : ℝ} (hc : 0 ≤ c)
    {T Z : Finset (ℤ × ℤ)}
    (h : ∀ x ∈ T, ∀ z ∈ Z, c < dist (integerPoint x) (integerPoint z)) :
    ENNReal.ofReal c < OpenAI.ambientEDist T Z := by
  rw [OpenAI.lt_ambientEDist_iff ENNReal.ofReal_lt_top]
  intro x hx z hz
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff']
  exact ⟨h x hx z hz, hc.trans_lt (h x hx z hz)⟩

/-- A finite lattice subset of a closed layer inherits that layer's lower
clearance from every endpoint. -/
theorem ofReal_lt_ambientEDist_of_subset_dyadicLayer {c : ℝ} (hc : 0 ≤ c)
    (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (T : Finset (ℤ × ℤ))
    (hT : ∀ x ∈ T, integerPoint x ∈ closure (dyadicLayer o k Z C))
    (hscale : c < (C : ℝ) * (2 : ℝ) ^ k) :
    ENNReal.ofReal c < OpenAI.ambientEDist T Z := by
  apply ofReal_lt_ambientEDist_of_integerPoint_dist hc
  intro x hx z hz
  exact hscale.trans_le (dyadicLayer_dist_lower o k Z C (integerPoint x) (hT x hx) z hz)

/-- Finite lattice subsets of nonadjacent closed layers inherit the planar
nonadjacent-layer separation in the frozen `ambientEDist` convention. -/
theorem ofReal_lt_ambientEDist_of_nonadjacent_dyadicLayers {c : ℝ} (hc : 0 ≤ c)
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (T U : Finset (ℤ × ℤ)) (hkh : k + 2 ≤ h)
    (hT : ∀ x ∈ T, integerPoint x ∈ closure (dyadicLayer o k Z C))
    (hU : ∀ y ∈ U, integerPoint y ∈ closure (dyadicLayer o h Z C))
    (hscale : c < ((C : ℝ) - 1) / 2 * (2 : ℝ) ^ h) :
    ENNReal.ofReal c < OpenAI.ambientEDist T U := by
  apply ofReal_lt_ambientEDist_of_integerPoint_dist hc
  intro x hx y hy
  exact hscale.trans_le
    (dyadicLayer_dist_nonadjacent o k h Z C (integerPoint x) (integerPoint y)
      hkh (hT x hx) (hU y hy))

end OpenAI.Geometry
