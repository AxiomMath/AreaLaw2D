/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Geometry/Exponents.lean` (Apache 2.0): only the scanner exponents
`scannerMu`, `scannerEll` and `scannerKappa`, which `OpenAI.Scan.BadOldHistoryDecay` uses and
`OpenAI.Geometry.Exponents` lacks. Namespace `TNLean.PEPS.AreaLaw.Exponents` renamed to
`OpenAI.Exponents`, the namespace of `OpenAI.Geometry.Exponents`.
-/
import Mathlib.Tactic.NormNum

/-!
# Scanner exponents of the final area-law argument

The scanner exponents `μ`, `ℓ` and `κ` are rational numbers; their real values are obtained
by coercion.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `scanner:final-parameters`,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace OpenAI.Exponents

/-- Scanner exponent `μ`. Source: `scanner:final-parameters`. -/
def scannerMu : ℚ := 1 / 4

/-- Scanner exponent `ℓ`. Source: `scanner:final-parameters`. -/
def scannerEll : ℚ := 1 / 100000

/-- Scanner exponent `κ`. Source: `scanner:final-parameters`. -/
def scannerKappa : ℚ := 1 / 1000000

end OpenAI.Exponents
