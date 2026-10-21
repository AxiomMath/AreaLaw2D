import AreaLawForMathlib.RepresentationTheory.PermutationRepresentation
import AreaLawForMathlib.Analysis.Matrix.OrthogonalResolutionCfc
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.IsotypicDimension

/-!
# Calculus of label observables

Extends `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`.

Label observables `f(F) = ∑_λ f(λ) π^λ` multiply, subtract, order and take `cfc` pointwise.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace PermutationRepresentation

variable {G Y : Type*} [Group G] [Fintype G] [Fintype Y] [DecidableEq Y] (φ : G →* Equiv.Perm Y)

/-- The label projectors form an orthogonal resolution of the identity. -/
theorem labelProj_isOrthogonalResolution :
    IsOrthogonalResolution fun l : IrrepLabel G => labelProj φ l where
  mul_eq := labelProj_mul_labelProj φ
  sum_eq := sum_labelProj φ

theorem labelObservable_eq_resolutionHom (f : IrrepLabel G → ℝ) :
    labelObservable φ f = (labelProj_isOrthogonalResolution φ).hom fun l => (f l : ℂ) := by
  rw [IsOrthogonalResolution.hom_apply, labelObservable]

theorem labelObservable_mul_labelObservable (f g : IrrepLabel G → ℝ) :
    labelObservable φ f * labelObservable φ g = labelObservable φ (f * g) := by
  rw [labelObservable_eq_resolutionHom, labelObservable_eq_resolutionHom,
    labelObservable_eq_resolutionHom, ← map_mul]
  congr 1; ext l; simp

/-- The label indicator of a set of labels is an orthogonal projection. -/
theorem labelObservable_indicator_proj (p : IrrepLabel G → Prop) [DecidablePred p] :
    (labelObservable φ fun l => if p l then 1 else 0).IsHermitian ∧
      labelObservable φ (fun l => if p l then 1 else 0) *
          labelObservable φ (fun l => if p l then 1 else 0) =
        labelObservable φ fun l => if p l then 1 else 0 := by
  refine ⟨isHermitian_labelObservable _ _, ?_⟩
  rw [labelObservable_mul_labelObservable]
  congr 1; ext l; by_cases h : p l <;> simp [h]

theorem one_sub_labelObservable_indicator (p : IrrepLabel G → Prop) [DecidablePred p] :
    1 - labelObservable φ (fun l => if p l then 1 else 0) =
      labelObservable φ fun l => if p l then 0 else 1 := by
  rw [← sum_labelProj φ, labelObservable, labelObservable, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => by by_cases h : p l <;> simp [h]

/-- `‖f(F) v‖² ≤ M² ‖v‖²` when `|f(λ)| ≤ M` on the labels occurring in `v`. -/
theorem re_dotProduct_labelObservable_mulVec_le {f : IrrepLabel G → ℝ} {M : ℝ}
    (v : Y → ℂ) (h : ∀ l, labelProj φ l *ᵥ v ≠ 0 → |f l| ≤ M) :
    (star (labelObservable φ f *ᵥ v) ⬝ᵥ (labelObservable φ f *ᵥ v)).re ≤
      M ^ 2 * (star v ⬝ᵥ v).re := by
  have hP := labelProj_isOrthogonalResolution φ
  have hH := isHermitian_labelProj φ
  rw [labelObservable_eq_resolutionHom]
  have e := hP.re_star_dotProduct_hom_mulVec_self hH (fun l => (f l : ℂ)) v
  simp only [RCLike.re_to_complex] at e
  rw [e, ← RCLike.re_to_complex, ← hP.sum_weight v, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : labelProj φ l *ᵥ v = 0
  · simp [IsOrthogonalResolution.weight, hl]
  · refine mul_le_mul_of_nonneg_right ?_ (hP.weight_nonneg hH v l)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h l hl) 2

theorem labelProj_eq_labelObservable_ite (l : IrrepLabel G) :
    labelProj φ l = labelObservable φ fun l' => if l' = l then 1 else 0 := by
  rw [labelObservable, Finset.sum_eq_single l]
  · simp
  · intro l' _ h; simp [h]
  · simp

omit [Fintype G] in
/-- A matrix whose entries are invariant under `ψ g` commutes with `U(g)`. -/
theorem commute_permOp_of_apply (ψ : G →* Equiv.Perm Y) (g : G) {M : Matrix Y Y ℂ}
    (h : ∀ x y, M (ψ g x) (ψ g y) = M x y) : Commute (permOp ψ g) M := by
  ext x y
  simp only [Matrix.mul_apply, permOp_apply_apply]
  rw [Finset.sum_eq_single ((ψ g).symm x), Finset.sum_eq_single (ψ g y)]
  · simp only [Equiv.apply_symm_apply, if_true, one_mul, mul_one]
    rw [← h ((ψ g).symm x) y, Equiv.apply_symm_apply]
  · intro z _ hz; rw [if_neg (Ne.symm hz), mul_zero]
  · simp
  · intro z _ hz; rw [if_neg (fun h' => hz (by rw [← h', Equiv.symm_apply_apply])), zero_mul]
  · simp

theorem cfc_labelObservable (h : ℝ → ℝ) (f : IrrepLabel G → ℝ) :
    cfc h (labelObservable φ f) = labelObservable φ (h ∘ f) := by
  rw [labelObservable_eq_resolutionHom, labelObservable_eq_resolutionHom,
    (labelProj_isOrthogonalResolution φ).cfc_hom (isHermitian_labelProj φ)]
  rfl

theorem labelObservable_sub (f g : IrrepLabel G → ℝ) :
    labelObservable φ g - labelObservable φ f = labelObservable φ (g - f) := by
  rw [labelObservable_eq_resolutionHom, labelObservable_eq_resolutionHom,
    labelObservable_eq_resolutionHom, ← map_sub]
  congr 1; ext l; simp

theorem labelObservable_le_labelObservable {f g : IrrepLabel G → ℝ} (hfg : ∀ l, f l ≤ g l) :
    labelObservable φ f ≤ labelObservable φ g := by
  rw [Matrix.le_iff, labelObservable_sub, labelObservable_eq_resolutionHom]
  exact (labelProj_isOrthogonalResolution φ).posSemidef_hom (isHermitian_labelProj φ)
    fun l => sub_nonneg.mpr (hfg l)

theorem labelObservable_const_mul (c : ℝ) (f : IrrepLabel G → ℝ) :
    labelObservable φ (fun l => c * f l) = c • labelObservable φ f := by
  rw [labelObservable, labelObservable, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← Complex.coe_smul, smul_smul, Complex.ofReal_mul]

/-- A label occurring in a permutation module has dimension at most the module's dimension. -/
theorem labelDim_le_card {l : IrrepLabel G} (h : labelProj φ l ≠ 0) : l.dim ≤ Fintype.card Y := by
  refine (dim_le_finrank_of_invariant (φ := φ) (W := LinearMap.range (toLin' (labelProj φ l))) l
    (by rintro g _ ⟨v, rfl⟩; exact ⟨permOp φ g *ᵥ v, by
      simp only [toLin'_apply, mulVec_mulVec, (commute_labelProj_permOp φ l g).eq]⟩)
    (by rintro _ ⟨v, rfl⟩; simp only [toLin'_apply, mulVec_mulVec, labelProj_mul_self])
    (by rwa [Ne, LinearMap.range_eq_bot, ← map_zero toLin', toLin'.injective.eq_iff])).trans ?_
  exact (Submodule.finrank_le _).trans_eq (Module.finrank_fintype_fun_eq_card ℂ)

end PermutationRepresentation
