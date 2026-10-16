import Arealaw.State

/-!
# The Bell pair

The Bell state `(|00⟩ + |11⟩)/√2` has coefficient matrix `bell = (1/√2) • 1` on
`Fin 2 ⊗ Fin 2`, reduced density operator the maximally mixed qubit `½ · 1`, and hence
`EE bell = log 2`.

Two deviations from Brandão–Horodecki, arXiv:1309.3789.  Its Fig. 1a caption writes the pair
as `½(|00⟩ + |11⟩)`, not a unit
vector, so we read the `½` as a typo for the `1/√2` used here.  Its logs are in base 2, where
`EE` is in nats.
-/

namespace Arealaw

open Matrix

/-- Coefficient matrix of the Bell state `(|00⟩ + |11⟩)/√2`. -/
noncomputable def bell : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- The Bell coefficient matrix is a unit vector: `∑ a b, ‖bell a b‖² = 1`. -/
theorem bell_normalized : ∑ a, ∑ b, ‖bell a b‖ ^ 2 = 1 := by
  norm_num [bell]

private theorem half_scalar : (((1 : ℝ) / Real.sqrt 2 : ℝ) : ℂ) * star
    (((1 : ℝ) / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  simp [← mul_inv, ← Complex.ofReal_mul]

private theorem half_one_eq_diagonal : (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
    diagonal (RCLike.ofReal ∘ (fun _ : Fin 2 => (1 / 2 : ℝ))) := by
  simp [smul_one_eq_diagonal]

/-- The reduced density operator of the Bell state is the maximally mixed qubit
`ρ_A = ½ · 1 = diagonal (½, ½)`. -/
theorem rhoA_bell : rhoA bell = diagonal (RCLike.ofReal ∘ (fun _ : Fin 2 => (1 / 2 : ℝ))) := by
  rw [rhoA, bell, conjTranspose_smul, conjTranspose_one, smul_mul_smul_comm, one_mul,
    ← half_one_eq_diagonal, half_scalar]

/-- The (constant) entropy of two outcomes of probability `½` is `log 2`. -/
theorem H_half : H (fun _ : Fin 2 => (1 / 2 : ℝ)) = Real.log 2 := by
  simp [H, Real.negMulLog]

/-- **One ebit across the bond**: `EE bell = log 2`. -/
theorem EE_bell : EE bell = Real.log 2 := (EE_eq_of_diag rhoA_bell).trans H_half

end Arealaw
