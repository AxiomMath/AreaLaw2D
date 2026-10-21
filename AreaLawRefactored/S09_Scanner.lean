import AreaLawRefactored.S09_Scanner.Interfaces
import AreaLawRefactored.S09_Scanner.Scan
import AreaLawRefactored.S09_Scanner.Histories
import AreaLawRefactored.S09_Scanner.Truncation
import AreaLawRefactored.S09_Scanner.ComparatorData
import AreaLawRefactored.S09_Scanner.Scanner
import AreaLawRefactored.S09_Scanner.Templates
import AreaLawRefactored.S09_Scanner.Planar
import AreaLawRefactored.S09_Scanner.SmallBox
import AreaLawRefactored.S09_Scanner.Collar

/-!
# §9 Scanning collars and improving the entropy bound

Digest `digest/09-scanner.md`, paper `paper/sections/08-scanner.tex`.

* `Interfaces`: the scales (D9.2), the test geometry (D9.3) and the statements one subsection
  file cites from another (`Prop_9_2`, `Lemma_9_4`, `Prop_9_5`).
* `Scan`, `Histories`, `Histories/*`: §9.0–9.1, the scan (D9.4–D9.7) and Lemma 9.1 (D9.8).
* `Truncation`, `ComparatorData`, `Scanner`, `Scanner/*`: §9.2, Proposition 9.2 (D9.9–D9.13).
* `Templates`: §9.3, Definition 9.3 and Lemma 9.4 (D9.14–D9.18), the safe-rectangle shells of
  D9.21.2.
* `Planar`, `SmallBox`: §9.4, the `ℤ²` instance of Proposition 9.2 and Proposition 9.5
  (D9.19–D9.24).
* `Collar`: §9.5, Proposition 9.6 (D9.25–D9.30).

Lemma 9.1 and Proposition 9.2 are graph-level; Definition 9.3, Lemma 9.4 and the frozen
`CollarBound` are on `ℤ × ℤ`. This file discharges the interfaces.
-/

namespace AreaLaw.Scanner

/-- D9.19 **Proposition 9.5** (improved safe-box estimate): `F_box(r) ≤ C r^{1+e_*}`,
`e_* = 2·10⁻⁶`, `C` depending only on `q, R, J, Δ`. -/
theorem prop_9_5 : Prop_9_5 := prop_9_5_of prop_9_2'

/-- D9.25 **Proposition 9.6** (a sublinear collar bound): for a template `T` separated from the
cut, `L = ⌊n^{1-10⁻⁵}⌋ ≤ s₀`, `X = A ∩ T`, `S₀ = A ∩ T_L`, for all large `n`,
`I_Ω(X : Λ \ S₀) ≤ C n^{1-ε}`, `ε = 10⁻⁵`; the cuts of `X`, `S₀`, `S₀ \ X` have `O(n)` edges and
`|S₀| = O(n²)`; constant and threshold independent of `T, s₀, n, Λ, A`. 2D only: the frozen
statement and the templates are on `ℤ × ℤ`. -/
theorem prop_9_6 {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    OpenAI.CollarBound ℂ q R J Δ :=
  prop_9_6_of prop_9_2' lemma_9_4 prop_9_5 hq hJ hΔ

end AreaLaw.Scanner
