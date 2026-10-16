import OpenAI.Scan.ActualSharpPrevector
import OpenAI.Scan.ActualReplicaDefect
import OpenAI.Scan.RadiusAsymptotics
import OpenAI.Scan.ScannerExponents
import OpenAI.Scan.SharpMomentScale
import OpenAI.Scan.BootstrapParameters
import OpenAI.TypicalSet
import OpenAI.GapSurprisal
import OpenAI.Geometry.Exponents
import OpenAI.SupportCounting

/-!
# The collar scan at the source scales

The collar scan of [OAI265, §9.1] for a finite domain `Λ`, a cut `A`, a nonempty target `T` and
a scale `n`: the induced lattice graph of `Λ`, depth the ambient sup-norm distance to `T`, one
designated anchor in each admissible support, and the scales `m = ⌊n^μ⌋`, `K = ⌊L/(8m)⌋`,
`D = ⌈n^κ⌉`, `r₀ = ⌈C_tr log² n⌉` of eq. (9.1).  This file fixes that scan, the two exponent
tuples of §9.4 and §9.5, the property of a label sequence produced by the Schmidt–Bell selection
of Proposition 8.1.

## Main definitions

* `OpenAI.Scan.sourceScan`: the collar scan at scale `n`.
* `OpenAI.Scan.finalExponents`, `OpenAI.Scan.bootstrapExponents`: the exponents of
  eq. (9.17) and eq. (9.13).
* `OpenAI.Scan.IsSchmidtBellLabels`: the conclusions of the Schmidt–Bell label selection.

## Main statements

* `OpenAI.Scan.sourceScan_anchor_card_le`: each site anchors boundedly many supports.
* `OpenAI.Scan.exists_isSchmidtBellLabels`: the selection exists.

## Implementation notes

The scan's charge capacity constant is `C₁ = 3 μ_R` with `μ_R = 2^{(2R+1)²}` a bound on the
number of supports sharing an anchor, the form the ported charge-slot lemmas require
(`3 μ ≤ C₁`).  The paper takes "a uniform constant `C₁` large enough" (line 129).

-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-! ## The scan -/

/-- The designated anchor of an admissible support: a chosen site of it. -/
noncomputable def supportAnchor {Λ : Finset (ℤ × ℤ)} {R : ℕ} (i : supports Λ R) :
    ↥(Λ : Set (ℤ × ℤ)) :=
  ⟨(mem_supports_iff.1 i.2).2.1.choose,
    (mem_supports_iff.1 i.2).1 (mem_supports_iff.1 i.2).2.1.choose_spec⟩

theorem supportAnchor_mem {Λ : Finset (ℤ × ℤ)} {R : ℕ} (i : supports Λ R) :
    (supportAnchor i).1 ∈ i.val :=
  (mem_supports_iff.1 i.2).2.1.choose_spec

/-- A bound `μ_R = 2^{(2R+1)²}` on the number of admissible supports of range `R` sharing an
anchor: each lies in the sup-norm ball of radius `R` about it. -/
def anchorMultiplicityBound (R : ℕ) : ℕ := 2 ^ (2 * R + 1) ^ 2

/-- **The collar scan** at scale `n` [OAI265, §9.1, eq. (9.1)]: induced lattice graph of `Λ`,
cut `A ∩ Λ`, depth `dist_∞(·, T)`, the support anchors, `n` slots per depth row, `m = ⌊n^μ⌋`,
`K = ⌊L / (8m)⌋`, `D = ⌈n^κ⌉`, `r₀ = ⌈C_tr log² n⌉` and charge capacity `⌈C₁ n D⌉`. -/
noncomputable def sourceScan (X : ScannerExponents) (Ctr : ℝ) (R : ℕ)
    (Λ A T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (n : ℕ) :
    CollarScan ↥(Λ : Set (ℤ × ℤ)) (supports Λ R) where
  graph := (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))
  A := A.subtype (· ∈ (Λ : Set (ℤ × ℤ)))
  depth x := ambientDepth T hT x.val
  anchor := supportAnchor
  n := n
  m := X.m n
  K := X.K n
  D := X.D n
  r₀ := roundedLogRadius Ctr n
  C₁ := 3 * anchorMultiplicityBound R

/-- **Bounded anchor multiplicity** [OAI265, §9.1, line 128]: at most `μ_R` admissible supports
share an anchor. -/
theorem sourceScan_anchor_card_le (X : ScannerExponents) (Ctr : ℝ) (R : ℕ)
    (Λ A T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (n : ℕ) (y : ↥(Λ : Set (ℤ × ℤ))) :
    (Finset.univ.filter fun i => (sourceScan X Ctr R Λ A T hT n).anchor i = y).card ≤
      anchorMultiplicityBound R := by
  classical
  refine le_trans ?_ (card_filter_mem_supports_le Λ R y.1)
  refine Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => ?_)
    (fun i _ j _ h => Subtype.ext h)
  rw [Finset.mem_coe, Finset.mem_filter] at hi ⊢
  refine ⟨i.2, ?_⟩
  have h := supportAnchor_mem i
  rw [show supportAnchor i = y from hi.2] at h
  exact h

/-! ## The two exponent tuples -/

/-- The final scanner exponents of [OAI265, eq. (9.17)]: `ℓ = 10⁻⁵`, `κ = 10⁻⁶`, `μ = 1/4`,
`ν = 10⁻³`, with entropy input exponent `e_* = 2·10⁻⁶`. -/
noncomputable def finalExponents : ScannerExponents where
  ell := (Exponents.scannerEll : ℝ)
  kappa := (Exponents.scannerKappa : ℝ)
  mu := (Exponents.scannerMu : ℝ)
  nu := (Exponents.scannerNu : ℝ)
  e := (Exponents.boxError : ℝ)
  ell_pos := by norm_num [Exponents.scannerEll]
  ell_lt_one := by norm_num [Exponents.scannerEll]
  kappa_pos := by norm_num [Exponents.scannerKappa]
  kappa_lt_mu := by norm_num [Exponents.scannerKappa, Exponents.scannerMu]
  mu_lt_one_sub_ell := by norm_num [Exponents.scannerMu, Exponents.scannerEll]
  nu_pos := by norm_num [Exponents.scannerNu]
  e_pos := by norm_num [Exponents.boxError]
  e_lt_one := by norm_num [Exponents.boxError]
  kappa_le_e := by norm_num [Exponents.scannerKappa, Exponents.boxError]

/-- The final collar depth is the collar width `⌊n^{1-10⁻⁵}⌋` of Proposition 9.6. -/
theorem finalExponents_L (n : ℕ) : finalExponents.L n = collarWidth n := by
  simp only [ScannerExponents.L, finalExponents, collarWidth, Exponents.scannerEll]
  norm_num

/-- The bootstrap exponents of [OAI265, eq. (9.13)] for an initial exponent `e_* < e₀ < 1`:
`ℓ = ν/100`, `κ = min(ℓ, e_*/4)`, `μ = 1 - g₀`, `ν = g₀/1000` with `g₀ = (1 - e₀)/2`, and
entropy input exponent `e₀`. -/
noncomputable def bootstrapExponents (e₀ : ℝ) (he₀ : (Exponents.boxError : ℝ) < e₀)
    (he₀₁ : e₀ < 1) : ScannerExponents :=
  have he₀pos : 0 < e₀ := lt_trans (by norm_num [Exponents.boxError]) he₀
  have hb := BootstrapParameters.parameter_bounds he₀pos he₀₁
  have hℓg₀ : BootstrapParameters.ell e₀ < BootstrapParameters.g0 e₀ :=
    (div_lt_self (div_pos hb.1 (by norm_num : (0 : ℝ) < 1000))
      (by norm_num : (1 : ℝ) < 100)).trans
      (div_lt_self hb.1 (by norm_num : (1 : ℝ) < 1000))
  { ell := BootstrapParameters.ell e₀
    kappa := BootstrapParameters.kappa e₀
    mu := BootstrapParameters.mu e₀
    nu := BootstrapParameters.nu e₀
    e := e₀
    ell_pos := hb.2.2.1
    ell_lt_one := hb.2.2.2.1
    kappa_pos := hb.2.2.2.2
    kappa_lt_mu := by
      linarith [show BootstrapParameters.kappa e₀ ≤ BootstrapParameters.ell e₀ from
        min_le_left _ _, show BootstrapParameters.mu e₀ = 1 - BootstrapParameters.g0 e₀ from rfl]
    mu_lt_one_sub_ell := sub_lt_sub_left hℓg₀ 1
    nu_pos := div_pos hb.1 (by norm_num)
    e_pos := he₀pos
    e_lt_one := he₀₁
    kappa_le_e :=
      (show BootstrapParameters.kappa e₀ ≤ (Exponents.boxError : ℝ) / 4 from
        min_le_right _ _).trans
        ((show (Exponents.boxError : ℝ) / 4 ≤ (Exponents.boxError : ℝ) by
          norm_num [Exponents.boxError]).trans he₀.le) }

/-! ## The Schmidt–Bell label sequence -/

open Classical in
/-- The conclusions of the Schmidt–Bell label selection [OAI265, Proposition 8.1,
eqs. (8.7) and (8.15)] for a unit eigenvector `Ω` of `H` with eigenvalue `E₀` and a spectral set
`E` of its marginal on `X`: the replica prevector is nonzero of norm at most one, an exact
replica-energy eigenvector, symmetric and fixed by both auxiliary label projections; the
selected label retains a polynomial fraction of the typical product; and
`log dim λ_k = k S' + o(k)`, with `S'` the entropy of the selected typical vector. -/
def IsSchmidtBellLabels {q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix (ι → Fin q) (ι → Fin q) ℂ) (Ω : EuclideanSpace ℂ (ι → Fin q)) (E₀ : ℝ)
    (X : Finset ι) (E : Finset (FiniteProduct.Configuration (fun _ : ι => Fin q) X))
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) : Prop :=
  let β := fun _ : ι => Fin q
  let split := FiniteProduct.splitEquiv β X
  let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ω
  let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x =>
    compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
  (∀ k : ℕ, 0 < k →
    let d := E.card
    let eₖ := TensorPower.globalReplicaCopiesEquiv β (Fin d) (Fin d) k
    let ξ := WithLp.toLp 2
      (TensorPower.replicaPrevector Ω d k (ell k) ∘ eₖ)
    let L := PermutationRepresentation.labelProj
      (TensorPower.copyPerm (Fin d) k) (ell k)
    let I := (1 : Matrix (Fin k → ι → Fin q) (Fin k → ι → Fin q) ℂ)
    let Pe := PermutationRepresentation.symProj
      (TensorPower.copyPerm
        ((v : Option (Option ι)) →
          TensorPower.addedSiteSpace (TensorPower.addedSiteSpace β (Fin d))
            (Fin d) v) k)
    ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 ∧
      (((((k : ℝ)⁻¹ • Matrix.replicaHamiltonian H k) ⊗ₖ
        (1 : Matrix ((Fin k → Fin d) × (Fin k → Fin d))
          ((Fin k → Fin d) × (Fin k → Fin d)) ℂ)).submatrix eₖ eₖ) *ᵥ ξ =
        (E₀ : ℂ) • ξ.ofLp) ∧
      Pe *ᵥ ξ = ξ.ofLp ∧
      ((I ⊗ₖ (L ⊗ₖ (1 : Matrix (Fin k → Fin d)
        (Fin k → Fin d) ℂ))).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp ∧
      ((I ⊗ₖ ((1 : Matrix (Fin k → Fin d)
        (Fin k → Fin d) ℂ) ⊗ₖ L)).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp) ∧
  (∀ᶠ k : ℕ in Filter.atTop,
    (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
      ‖WithLp.toLp 2
        (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
          (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
          PermutationRepresentation.labelProj
            (TensorPower.copyPerm (Fin E.card) k) (ell k)) *ᵥ
          (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
            (Fin k → Fin E.card) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
  Asymptotics.IsLittleO Filter.atTop
    (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) *
      Arealaw.vonNeumann
        (Matrix.posSemidef_vecMulVec_self_star ψ).traceLeft.isHermitian)
    (fun k : ℕ => (k : ℝ))

open Classical in
/-- **The Schmidt–Bell label selection** [OAI265, Proposition 8.1]: a unit eigenvector and a
spectral set of positive mass determine a label sequence with the properties
`IsSchmidtBellLabels`. -/
theorem exists_isSchmidtBellLabels {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix (ι → Fin q) (ι → Fin q) ℂ) (Ω : EuclideanSpace ℂ (ι → Fin q)) (E₀ : ℝ)
    (hΩ : ‖Ω‖ = 1) (hE : H *ᵥ Ω.ofLp = (E₀ : ℂ) • Ω.ofLp)
    (X : Finset ι) (E : Finset (FiniteProduct.Configuration (fun _ : ι => Fin q) X))
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef (fun _ : ι => Fin q) Ω
      X).isHermitian.spectralRestrictionMass E) :
    ∃ ell, IsSchmidtBellLabels H Ω E₀ X E ell :=
  exists_global_schmidtBellPrevector H Ω E₀ hΩ hE X E hz

end OpenAI.Scan
