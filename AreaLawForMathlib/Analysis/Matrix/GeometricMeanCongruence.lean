import AreaLawForMathlib.Analysis.Matrix.GeometricMeanDerivative
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Infinitesimal congruence covariance of the weighted geometric mean

Extends `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`.

Congruence covariance `S^* (A #_p B) S = (S^* A S) #_p (S^* B S)` along `S = e^{tX}`,
differentiated at `t = 0`:
`∂_A(A #_p B)[X^* A + A X] + ∂_B(A #_p B)[X^* B + B X] = X^* (A #_p B) + (A #_p B) X`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Set Filter Topology NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem hasDerivAt_star_exp_mul_mul_exp (X P : Matrix m m ℂ) :
    HasDerivAt (fun t : ℝ => star (exp (t • X)) * P * exp (t • X)) (Xᴴ * P + P * X) 0 := by
  have hexp : ∀ Y : Matrix m m ℂ, HasDerivAt (fun t : ℝ => exp (t • Y)) Y 0 := fun Y => by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
  have hstar : ∀ t : ℝ, star (exp (t • X)) = exp (t • Xᴴ) := by
    intro t
    rw [star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial]
  simp_rw [hstar]
  have := ((hexp Xᴴ).mul_const P).mul (hexp X)
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul] at this
  exact this

/-- **Infinitesimal congruence covariance** of the weighted geometric mean. -/
theorem geomMeanDeriv_congr {P R : Matrix m m ℂ} (hP : P.PosDef) (hR : R.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (X : Matrix m m ℂ) :
    geomMeanDerivLeft p P R (Xᴴ * P + P * X) + geomMeanDerivRight p P R (Xᴴ * R + R * X) =
      Xᴴ * geomMean p P R + geomMean p P R * X := by
  set S : ℝ → Matrix m m ℂ := fun t => exp (t • X)
  set V : ℝ → Matrix m m ℂ := fun t => exp (t • -X)
  have hinv : ∀ t : ℝ, V t * S t = 1 := by
    intro t
    simp only [V, S]
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left t).smul_right t),
      ← smul_add, neg_add_cancel, smul_zero, NormedSpace.exp_zero]
  have hSu : ∀ t, IsUnit (S t) := fun t => Matrix.isUnit_exp _
  have hVu : ∀ t, IsUnit (V t) := fun t => Matrix.isUnit_exp _
  have hherm : ∀ (Q : Matrix m m ℂ) (W : Matrix m m ℂ), Q.IsHermitian →
      (star W * Q * W) ∈ hermitianSet m := by
    intro Q W hQ
    change (star W * Q * W).IsHermitian
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
      hQ.eq, Matrix.mul_assoc]
  have hid : ∀ t, geomMean p (star (S t) * P * S t) R =
      star (S t) * geomMean p P (star (V t) * R * V t) * S t := by
    intro t
    have h := geomMean_star_conj hP ((Matrix.IsUnit.posDef_star_left_conjugate_iff (hVu t)).mpr hR)
      (hSu t) p
    have hR' : star (S t) * (star (V t) * R * V t) * S t = R := by
      calc _ = star (V t * S t) * R * (V t * S t) := by rw [star_mul]; noncomm_ring
        _ = R := by rw [hinv, star_one, Matrix.one_mul, Matrix.mul_one]
    rwa [hR'] at h
  have ha := hasDerivAt_star_exp_mul_mul_exp X P
  have hb := hasDerivAt_star_exp_mul_mul_exp (-X) R
  have hS0 : S 0 = 1 := by simp [S]
  have hV0 : V 0 = 1 := by simp [V]
  have hL : HasDerivAt (fun t => geomMean p (star (S t) * P * S t) R)
      (geomMeanDerivLeft p P R (Xᴴ * P + P * X)) 0 := by
    have h1 := (hasFDerivWithinAt_geomMean_left hP hR hp).restrictScalars ℝ
    have h2 : HasDerivWithinAt (fun t : ℝ => star (S t) * P * S t) (Xᴴ * P + P * X) univ 0 :=
      ha.hasDerivWithinAt
    have h3 := HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ) h1 h2
      (fun t _ => hherm P (S t) hP.isHermitian) (by simp [hS0])
    exact h3.hasDerivAt Filter.univ_mem
  have hψ : HasDerivAt (fun t => geomMean p P (star (V t) * R * V t))
      (geomMeanDerivRight p P R ((-X)ᴴ * R + R * -X)) 0 := by
    have h1 := (hasFDerivWithinAt_geomMean_right hP hR hp).restrictScalars ℝ
    have h2 : HasDerivWithinAt (fun t : ℝ => star (V t) * R * V t) ((-X)ᴴ * R + R * -X) univ 0 :=
      hb.hasDerivWithinAt
    have h3 := HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ) h1 h2
      (fun t _ => hherm R (V t) hR.isHermitian) (by simp [hV0])
    exact h3.hasDerivAt Filter.univ_mem
  have hexpX : HasDerivAt S X 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have hstarS : HasDerivAt (fun t => star (S t)) Xᴴ 0 := by
    have hst : ∀ t : ℝ, star (S t) = exp (t • Xᴴ) := by
      intro t
      rw [star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial]
    simp_rw [hst]
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ 0
  have hRd := (hstarS.mul hψ).mul hexpX
  have hfun : (fun t => geomMean p (star (S t) * P * S t) R) =
      fun t => star (S t) * geomMean p P (star (V t) * R * V t) * S t := funext hid
  rw [hfun] at hL
  have heq := hL.unique hRd
  simp only [Pi.mul_apply, hS0, hV0, star_one, Matrix.one_mul, Matrix.mul_one, conjTranspose_neg,
    Matrix.neg_mul, Matrix.mul_neg, ← neg_add, map_neg] at heq
  rw [heq]; abel

end Matrix
