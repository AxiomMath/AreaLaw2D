/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the TNLean LICENSE.
Authors: TNLean contributors
-/
import OpenAI.Statements
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology

/-!
# Concrete polygons for the frozen template predicate

Extracted from `LionSR/TNLean` commit
`fc565830cec69e8226e521d56c86d39845d45576`,
`TNLean/PEPS/AreaLaw/Geometry/Templates.lean` (Apache 2.0).  Only the concrete
polygon datatype is retained; TNLean's parallel `Template` and partition
structures are deliberately not copied.  `IsAllowedSlope` is a transparent
abbreviation for frozen `OpenAI.HasTemplateSlope`, and every polygon region is
proved to satisfy frozen `OpenAI.IsTemplatePiece`.
-/

namespace OpenAI.Geometry

/-- Source-compatible name for the frozen permitted-slope predicate. -/
abbrev IsAllowedSlope := OpenAI.HasTemplateSlope

/-- A nondegenerate triangle or rectangle carrying the exact witnesses used
by `OpenAI.IsTemplatePiece`. -/
inductive TemplatePolygon where
  | triangle (a b c : ℝ × ℝ)
      (noncollinear : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0)
      (ab : IsAllowedSlope (b - a)) (bc : IsAllowedSlope (c - b))
      (ca : IsAllowedSlope (a - c))
  | rectangle (a u v : ℝ × ℝ) (u_ne_zero : u ≠ 0) (v_ne_zero : v ≠ 0)
      (orthogonal : u.1 * v.1 + u.2 * v.2 = 0)
      (u_slope : IsAllowedSlope u) (v_slope : IsAllowedSlope v)

/-- The closed convex region represented by a concrete polygon. -/
noncomputable def TemplatePolygon.region : TemplatePolygon → Set (ℝ × ℝ)
  | .triangle a b c _ _ _ _ => convexHull ℝ {a, b, c}
  | .rectangle a u v _ _ _ _ _ => convexHull ℝ {a, a + u, a + u + v, a + v}

/-- Concrete polygons feed the frozen template-piece interface directly. -/
theorem TemplatePolygon.isTemplatePiece (P : TemplatePolygon) :
    OpenAI.IsTemplatePiece P.region := by
  cases P with
  | triangle a b c hnon hab hbc hca =>
      exact Or.inr ⟨a, b, c, hnon, hab, hbc, hca, rfl⟩
  | rectangle a u v hu hv hort hus hvs =>
      exact Or.inl ⟨a, u, v, hu, hv, hort, hus, hvs, rfl⟩

/-- The concrete polygon region is compact because its vertex set is finite. -/
theorem TemplatePolygon.isCompact_region (P : TemplatePolygon) : IsCompact P.region := by
  cases P <;> exact (Set.toFinite _).isCompact_convexHull ℝ

end OpenAI.Geometry
