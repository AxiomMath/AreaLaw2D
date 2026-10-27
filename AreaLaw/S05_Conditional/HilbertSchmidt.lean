import AreaLaw.S05_Conditional.Spectral
import AreaLaw.S05_Conditional.Compression

/-!
# §5.2 Hilbert–Schmidt instantiation of the resolvent compression (D5.12.1–4, D5.13–D5.14)

Digest `digest/05-conditional.md` (D5.12–D5.14). Hilbert–Schmidt space of `n × n` matrices is
`EuclideanSpace ℂ (n × n)` (`hs`, `⟪hs X, hs Y⟫ = Tr Xᴴ Y`). For faithful `ρ_f, M_f` on `m` and
`ρ_s, M_s` on `n`, a unital `*`-multiplicative `J` (the extension `X ↦ X ⊗ I_F`) with
`Tr ρ_f J(Y) = Tr ρ_s Y` and `Tr M_f J(Y) = Tr M_s Y`, and `d > 0`, `hsCompression` is the
`ResolventCompression` of D5.12.1–4 with `σ_f = M_f / d`, `σ_s = M_s / d`; its eigenbasis is
`u_i w_jᴴ` (`prodBasis`).
-/

namespace AreaLaw

open Arealaw Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

namespace Conditional

section HS

variable {m : Type*}

/-- The Hilbert–Schmidt vector of a matrix. -/
noncomputable def hs (X : Matrix m m ℂ) : EuclideanSpace ℂ (m × m) :=
  WithLp.toLp 2 fun p ↦ X p.1 p.2

/-- The matrix of a Hilbert–Schmidt vector. -/
noncomputable def unhs (x : EuclideanSpace ℂ (m × m)) : Matrix m m ℂ := of fun i j ↦ x (i, j)

@[simp] theorem hs_unhs (x : EuclideanSpace ℂ (m × m)) : hs (unhs x) = x := rfl

@[simp] theorem unhs_hs (X : Matrix m m ℂ) : unhs (hs X) = X := rfl

theorem hs_add (X Y : Matrix m m ℂ) : hs (X + Y) = hs X + hs Y := rfl

theorem hs_sub (X Y : Matrix m m ℂ) : hs (X - Y) = hs X - hs Y := rfl

theorem hs_smul (c : ℂ) (X : Matrix m m ℂ) : hs (c • X) = c • hs X := rfl

theorem unhs_add (x y : EuclideanSpace ℂ (m × m)) : unhs (x + y) = unhs x + unhs y := rfl

theorem unhs_smul (c : ℂ) (x : EuclideanSpace ℂ (m × m)) : unhs (c • x) = c • unhs x := rfl

variable [Fintype m]

/-- `⟪X, Y⟫ = Tr(Xᴴ Y)`. -/
theorem inner_hs (X Y : Matrix m m ℂ) : ⟪hs X, hs Y⟫_ℂ = (Xᴴ * Y).trace := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, hs, trace, mul_apply, conjTranspose_apply,
    Fintype.sum_prod_type, diag_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- `‖X‖₂ = √(Re Tr(Xᴴ X))`. -/
theorem norm_hs (X : Matrix m m ℂ) : ‖hs X‖ = √(Xᴴ * X).trace.re := by
  rw [← inner_hs, ← RCLike.re_to_complex, inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

variable [DecidableEq m]

/-- Two-sided unitary conjugation `X ↦ U* X W` as a linear isometry of Hilbert–Schmidt space. -/
noncomputable def conjIso {U W : Matrix m m ℂ} (hU : U ∈ unitary (Matrix m m ℂ))
    (hW : W ∈ unitary (Matrix m m ℂ)) : EuclideanSpace ℂ (m × m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (m × m) :=
  LinearEquiv.isometryOfInner
    { toFun := fun x ↦ hs (star U * unhs x * W)
      invFun := fun x ↦ hs (U * unhs x * star W)
      map_add' := fun x y ↦ by simp only [unhs_add, Matrix.mul_add, Matrix.add_mul, hs_add]
      map_smul' := fun c x ↦ by simp [unhs_smul, hs_smul]
      left_inv := fun x ↦ by
        simp only [unhs_hs, ← Matrix.mul_assoc, Unitary.mul_star_self_of_mem hU, Matrix.one_mul]
        simp only [Matrix.mul_assoc, Unitary.mul_star_self_of_mem hW, Matrix.mul_one, hs_unhs]
      right_inv := fun x ↦ by
        simp only [unhs_hs, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.one_mul]
        simp only [Matrix.mul_assoc, Unitary.star_mul_self_of_mem hW, Matrix.mul_one, hs_unhs] }
    fun x y ↦ by
      change ⟪hs _, hs _⟫_ℂ = _
      rw [inner_hs, ← hs_unhs x, ← hs_unhs y, inner_hs]
      simp only [unhs_hs, ← star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U, Unitary.mul_star_self_of_mem hU, Matrix.one_mul, trace_mul_comm,
        Matrix.mul_assoc, Matrix.mul_assoc, Unitary.mul_star_self_of_mem hW, Matrix.mul_one]

/-- The orthonormal basis `u_i w_jᴴ` of Hilbert–Schmidt space, for eigenbases `u`, `w` of
Hermitian `P`, `Q`. -/
noncomputable def prodBasis {P Q : Matrix m m ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    OrthonormalBasis (m × m) ℂ (EuclideanSpace ℂ (m × m)) :=
  .ofRepr (conjIso hP.eigenvectorUnitary.2 hQ.eigenvectorUnitary.2)

/-- `f(λ_i) g(μ_j)` in the basis `u_i w_jᴴ` is `X ↦ f(P) X g(Q)`. -/
theorem spec_prodBasis {P Q : Matrix m m ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f g : ℝ → ℂ) (X : Matrix m m ℂ) :
    spec (prodBasis hP hQ) (fun p ↦ f (hP.eigenvalues p.1) * g (hQ.eigenvalues p.2)) (hs X) =
      hs (specFun hP f * X * specFun hQ g) := by
  set e := prodBasis hP hQ
  have h1 : spec e (fun p ↦ f (hP.eigenvalues p.1) * g (hQ.eigenvalues p.2)) (hs X) =
      e.repr.symm (WithLp.toLp 2 fun p ↦
        f (hP.eigenvalues p.1) * g (hQ.eigenvalues p.2) * ⟪e p, hs X⟫_ℂ) := by
    rw [← OrthonormalBasis.sum_repr_symm]; rfl
  rw [h1]
  change hs (_ * _ * _) = _
  congr 1
  have h2 : unhs (WithLp.toLp 2 fun p ↦
        f (hP.eigenvalues p.1) * g (hQ.eigenvalues p.2) * ⟪e p, hs X⟫_ℂ) =
      diagonal (fun i ↦ f (hP.eigenvalues i)) *
        (star (hP.eigenvectorUnitary : Matrix m m ℂ) * X * hQ.eigenvectorUnitary) *
        diagonal (fun j ↦ g (hQ.eigenvalues j)) := by
    ext i j
    simp only [unhs, of_apply, ← OrthonormalBasis.repr_apply_apply, diagonal_mul, mul_diagonal]
    change _ * (hs (star (hP.eigenvectorUnitary : Matrix m m ℂ) * unhs (hs X) * _)) (i, j) = _
    rw [unhs_hs]
    exact mul_right_comm _ _ _
  rw [h2]
  simp only [specFun, Matrix.mul_assoc]

end HS

section Spec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
  (e : OrthonormalBasis ι ℂ E)

/-- `spec e f` as a linear map. -/
noncomputable def specLin (f : ι → ℂ) : E →ₗ[ℂ] E where
  toFun := spec e f
  map_add' x y := by
    simp only [spec, inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [spec, inner_smul_right, Finset.smul_sum, smul_smul, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by ring_nf

theorem spec_apply_basis (f : ι → ℂ) (i : ι) : spec e f (e i) = f i • e i := by
  classical
  simp [spec, orthonormal_iff_ite.1 e.orthonormal]

theorem spec_sub (f g : ι → ℂ) (x : E) : spec e (f - g) x = spec e f x - spec e g x := by
  simp only [spec, Pi.sub_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

end Spec

section Pow

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

theorem hfun_of_pos {t : ℝ} (ht : 0 < t) (z : ℂ) : hfun z t = Complex.exp (z * Real.log t) :=
  if_pos ht

theorem specFun_const_mul (h : ρ.IsHermitian) (c : ℂ) (f : ℝ → ℂ) :
    specFun h (fun t ↦ c * f t) = c • specFun h f := by
  have hd : (diagonal fun i ↦ c * f (h.eigenvalues i)) =
      c • diagonal fun i ↦ f (h.eigenvalues i) := by
    rw [← diagonal_smul]; rfl
  rw [specFun, specFun, hd, Matrix.mul_smul, Matrix.smul_mul]

/-- `Tr g(ρ) = ∑ g(λᵢ)`. -/
theorem trace_specFun (h : ρ.IsHermitian) (g : ℝ → ℂ) :
    (specFun h g).trace = ∑ i, g (h.eigenvalues i) := by
  rw [specFun, trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]

/-- For `ρ > 0`, a spectral function agreeing with `t ↦ t^z` on `(0,∞)` is `ρ̂^z`. -/
theorem specFun_eq_hatPow (hρ : ρ.PosDef) {g : ℝ → ℂ} {z : ℂ}
    (hg : ∀ t > 0, g t = Complex.exp (z * Real.log t)) : specFun hρ.1 g = hatPow ρ z := by
  rw [hatPow_eq hρ.1]
  exact specFun_congr _ fun i ↦ by
    rw [hg _ (hρ.eigenvalues_pos i), hfun_of_pos (hρ.eigenvalues_pos i)]

/-- `c(ρ) = c`. -/
theorem specFun_const (h : ρ.IsHermitian) (c : ℂ) : specFun h (fun _ ↦ c) = c • 1 := by
  rw [← specFun_one h, ← specFun_const_mul]
  simp only [Pi.one_apply, mul_one]

/-- `ρ̂^1 = ρ` for `ρ > 0`. -/
theorem hatPow_one_of_posDef (hρ : ρ.PosDef) : hatPow ρ 1 = ρ := by
  rw [← specFun_eq_hatPow hρ (g := fun t ↦ (t : ℂ)) fun t ht ↦ by
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log ht],
    specFun_ofReal]

/-- `ρ̂^{1/2} = √ρ` for `ρ > 0`. -/
theorem hatPow_half_of_posDef (hρ : ρ.PosDef) : hatPow ρ (1 / 2) = CFC.sqrt ρ := by
  rw [← bracketPow_half hρ.posSemidef, bracketPow_eq hρ.1, hatPow_eq hρ.1]
  exact specFun_congr _ fun i ↦ by
    simp [hfun, bfun, hρ.eigenvalues_pos i]

/-- `(ρ̂^s)ᴴ = ρ̂^s` for real `s`. -/
theorem conjTranspose_hatPow_ofReal (ρ : Matrix n n ℂ) (s : ℝ) :
    (hatPow ρ s)ᴴ = hatPow ρ s :=
  isHermitian_hatPow_ofReal ρ s

/-- `ρ̂^z ρ = ρ̂^{z+1}` for `ρ > 0`. -/
theorem hatPow_mul_self (hρ : ρ.PosDef) (z : ℂ) : hatPow ρ z * ρ = hatPow ρ (z + 1) := by
  rw [← hatPow_mul_hatPow, hatPow_one_of_posDef hρ]

/-- `ρ̂^{-1} = ρ⁻¹` for `ρ > 0`. -/
theorem hatPow_neg_one_of_posDef (hρ : ρ.PosDef) : hatPow ρ (-1) = ρ⁻¹ :=
  (inv_eq_left_inv (by rw [hatPow_mul_self hρ, neg_add_cancel, hatPow_zero])).symm

/-- `(ρ̂^{1/2})ᴴ = ρ̂^{1/2}`. -/
theorem conjTranspose_hatPow_half (ρ : Matrix n n ℂ) : (hatPow ρ (1 / 2))ᴴ = hatPow ρ (1 / 2) := by
  simpa using conjTranspose_hatPow_ofReal ρ (1 / 2)

/-- `(ρ̂^{-1/2})ᴴ = ρ̂^{-1/2}`. -/
theorem conjTranspose_hatPow_neg_half (ρ : Matrix n n ℂ) :
    (hatPow ρ (-(1 / 2)))ᴴ = hatPow ρ (-(1 / 2)) := by
  simpa using conjTranspose_hatPow_ofReal ρ (-(1 / 2))

/-- `ρ^{1/2} ρ^{1/2} = ρ` for `ρ > 0`. -/
theorem hatPow_half_mul_half (hρ : ρ.PosDef) : hatPow ρ (1 / 2) * hatPow ρ (1 / 2) = ρ := by
  rw [hatPow_mul_hatPow, show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num, hatPow_one_of_posDef hρ]

/-- `ρ^{-1/2} ρ ρ^{-1/2} = 1` for `ρ > 0`. -/
theorem hatPow_neg_half_conj (hρ : ρ.PosDef) :
    hatPow ρ (-(1 / 2)) * ρ * hatPow ρ (-(1 / 2)) = 1 := by
  rw [hatPow_mul_self hρ, hatPow_mul_hatPow, show (-(1 / 2) + 1 + -(1 / 2) : ℂ) = 0 by ring,
    hatPow_zero]

end Pow

section Order

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Conjugation by a Hermitian matrix is monotone in real trace. -/
theorem re_trace_conj_le {R A B : Matrix n n ℂ} (hR : R.IsHermitian) (hAB : A ≤ B) :
    (R * A * R).trace.re ≤ (R * B * R).trace.re := by
  have h := ((le_iff.1 hAB).conjTranspose_mul_mul_same R).trace_nonneg
  rw [hR.eq, Matrix.mul_sub, Matrix.sub_mul, trace_sub] at h
  linarith [(Complex.nonneg_iff.1 h).1, Complex.sub_re (R * B * R).trace (R * A * R).trace]

/-- `ρ ≤ c M` with `ρ, M > 0`, `c > 0` gives `M⁻¹ ≤ c ρ⁻¹`. -/
theorem inv_le_smul_inv {ρ M : Matrix n n ℂ} (hρ : ρ.PosDef) (hM : M.PosDef) {c : ℝ} (hc : 0 < c)
    (h : ρ ≤ (c : ℂ) • M) : M⁻¹ ≤ (c : ℂ) • ρ⁻¹ := by
  have hcM : ((c : ℂ) • M).PosDef := hM.smul (by exact_mod_cast hc)
  have hinv := CStarAlgebra.inv_le_inv (a := hρ.isUnit.unit) (b := hcM.isUnit.unit)
    (nonneg_iff_posSemidef.2 hρ.posSemidef) h
  simp only [coe_units_inv, IsUnit.unit_spec] at hinv
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e : ((c : ℂ) • M)⁻¹ = (c : ℂ)⁻¹ • M⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc', one_smul,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hM.isUnit)]
  rw [e, le_iff] at hinv
  rw [le_iff, show (c : ℂ) • ρ⁻¹ - M⁻¹ = (c : ℂ) • (ρ⁻¹ - (c : ℂ)⁻¹ • M⁻¹) by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hc', one_smul]]
  exact hinv.smul (by exact_mod_cast hc.le)

end Order

/-! ## D5.12.1–4 The Hilbert–Schmidt compression -/

section Compression

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {ρf Mf : Matrix m m ℂ} {ρs Ms : Matrix n n ℂ} (J : Matrix n n ℂ →ₐ[ℂ] Matrix m m ℂ)

/-- D5.12.1. `V(Y) = (Y ρ_s^{-1/2} ⊗ I_F) √ρ_f`, so that `V(X √ρ_s) = (X ⊗ I_F) √ρ_f`. -/
noncomputable def hsVLin (ρf : Matrix m m ℂ) (ρs : Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) →ₗ[ℂ] EuclideanSpace ℂ (m × m) where
  toFun y := hs (J (unhs y * hatPow ρs (-(1 / 2))) * hatPow ρf (1 / 2))
  map_add' x y := by simp only [unhs_add, Matrix.add_mul, map_add, hs_add]
  map_smul' c x := by
    simp only [unhs_smul, Matrix.smul_mul, map_smul, hs_smul, RingHom.id_apply]

theorem hsVLin_hs (ρf : Matrix m m ℂ) (ρs : Matrix n n ℂ) (Y : Matrix n n ℂ) :
    hsVLin J ρf ρs (hs Y) = hs (J (Y * hatPow ρs (-(1 / 2))) * hatPow ρf (1 / 2)) := rfl

variable {J} (hρf : ρf.PosDef) (hρs : ρs.PosDef) (hJ : ∀ Y, J Yᴴ = (J Y)ᴴ)
  (hJρ : ∀ Y, (ρf * J Y).trace = (ρs * Y).trace)

include hρf hρs hJ hJρ in
/-- D5.12.2. `V` is an isometry: `‖V(X√ρ_s)‖₂² = Tr(X*X ⊗ I)ρ_f = Tr X*X ρ_s`. -/
theorem inner_hsVLin (x y : EuclideanSpace ℂ (n × n)) :
    ⟪hsVLin J ρf ρs x, hsVLin J ρf ρs y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← hs_unhs x, ← hs_unhs y, hsVLin_hs, hsVLin_hs, inner_hs, inner_hs]
  set r := hatPow ρs (-(1 / 2))
  set s := hatPow ρf (1 / 2)
  set X := unhs x
  set Y := unhs y
  have hs' : sᴴ = s := conjTranspose_hatPow_half ρf
  have hr' : rᴴ = r := conjTranspose_hatPow_neg_half ρs
  calc ((J (X * r) * s)ᴴ * (J (Y * r) * s)).trace = (s * (J (r * (Xᴴ * Y) * r) * s)).trace := by
        rw [conjTranspose_mul, hs', ← hJ, Matrix.mul_assoc, ← Matrix.mul_assoc (J _), ← map_mul,
          conjTranspose_mul, hr']
        simp only [Matrix.mul_assoc]
    _ = (ρf * J (r * (Xᴴ * Y) * r)).trace := by
        rw [trace_mul_comm, Matrix.mul_assoc, hatPow_half_mul_half hρf, trace_mul_comm]
    _ = (Xᴴ * Y).trace := by
        rw [hJρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
          ← Matrix.mul_assoc r, hatPow_neg_half_conj hρs, Matrix.one_mul]

/-- D5.12.2. The isometry `V : H_s → H_f`. -/
noncomputable def hsV : EuclideanSpace ℂ (n × n) →ₗᵢ[ℂ] EuclideanSpace ℂ (m × m) :=
  (hsVLin J ρf ρs).isometryOfInner (inner_hsVLin hρf hρs hJ hJρ)

omit [Fintype n] [DecidableEq n] in
/-- D5.12.1. The eigenvalue `s_i / p_j` of `L_σ R_{ρ⁻¹}` on `u_i w_jᴴ`, `σ = M / d`. -/
noncomputable def hsLam {M ρ : Matrix m m ℂ} (d : ℝ) (hM : M.IsHermitian) (hρ : ρ.IsHermitian)
    (p : m × m) : ℝ :=
  hM.eigenvalues p.1 / d * (hρ.eigenvalues p.2)⁻¹

omit [Fintype n] [DecidableEq n] in
/-- A function of `L_σ R_{ρ⁻¹}` that factors on `(0,∞)²` as `f(s) g(p)` is `X ↦ f(M) X g(ρ)`. -/
theorem spec_hsLam {M ρ : Matrix m m ℂ} {d : ℝ} (hM : M.PosDef) (hρ : ρ.PosDef) {G : ℝ → ℂ}
    {f g : ℝ → ℂ} (hG : ∀ a > 0, ∀ b > 0, G (a / d * b⁻¹) = f a * g b) (X : Matrix m m ℂ) :
    spec (prodBasis hM.1 hρ.1) (fun p ↦ G (hsLam d hM.1 hρ.1 p)) (hs X) =
      hs (specFun hM.1 f * X * specFun hρ.1 g) := by
  rw [← spec_prodBasis]
  exact congrArg₂ _ (funext fun p ↦ hG _ (hM.eigenvalues_pos _) _ (hρ.eigenvalues_pos _)) rfl

omit [Fintype n] [DecidableEq n] in
/-- D5.13.3. `log(L_σ R_{ρ⁻¹}) = L_{log σ} - R_{log ρ}`, so
`⟨√ρ, log(L_σ R_{ρ⁻¹}) √ρ⟩ = Tr ρ log M - log d Tr ρ - Tr ρ log ρ` for `σ = M / d`. -/
theorem inner_spec_log_hsLam {M ρ : Matrix m m ℂ} {d : ℝ} (hM : M.PosDef) (hρ : ρ.PosDef)
    (hd : 0 < d) :
    ⟪hs (hatPow ρ (1 / 2)), spec (prodBasis hM.1 hρ.1)
      (fun p ↦ ((Real.log (hsLam d hM.1 hρ.1 p) : ℝ) : ℂ)) (hs (hatPow ρ (1 / 2)))⟫_ℂ =
    (ρ * specFun hM.1 (fun t ↦ (Real.log t : ℂ))).trace - Real.log d * ρ.trace -
      (ρ * specFun hρ.1 (fun t ↦ (Real.log t : ℂ))).trace := by
  set L : ℝ → ℂ := fun t ↦ (Real.log t : ℂ)
  have hF : (fun p ↦ ((Real.log (hsLam d hM.1 hρ.1 p) : ℝ) : ℂ)) =
      (fun p ↦ L (hM.1.eigenvalues p.1) * (1 : ℝ → ℂ) (hρ.1.eigenvalues p.2)) -
      (fun p ↦ (Real.log d : ℂ) * (1 : ℝ → ℂ) (hρ.1.eigenvalues p.2)) -
      (fun p ↦ (1 : ℝ → ℂ) (hM.1.eigenvalues p.1) * L (hρ.1.eigenvalues p.2)) := by
    funext p
    have := hM.eigenvalues_pos p.1
    have := hρ.eigenvalues_pos p.2
    simp only [hsLam, Pi.sub_apply, Pi.one_apply, mul_one, one_mul, L]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) hd.ne',
      Real.log_inv]
    push_cast; ring
  have hsq := hatPow_half_mul_half hρ
  rw [hF, spec_sub, spec_sub, spec_prodBasis, spec_prodBasis hM.1 hρ.1 (fun _ ↦ (Real.log d : ℂ)) 1,
    spec_prodBasis, inner_sub_right,
    inner_sub_right, inner_hs, inner_hs, inner_hs, specFun_one, specFun_one, specFun_const,
    conjTranspose_hatPow_half]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
    smul_eq_mul, ← Matrix.mul_assoc, hsq]
  rw [trace_mul_comm, ← Matrix.mul_assoc, hsq]

omit [Fintype n] [DecidableEq n] in
/-- `A(X) = σ X ρ⁻¹` with `σ = M / d`. -/
theorem spec_hsLam_id {M ρ : Matrix m m ℂ} {d : ℝ} (hM : M.PosDef) (hρ : ρ.PosDef)
    (X : Matrix m m ℂ) :
    spec (prodBasis hM.1 hρ.1) (fun p ↦ (hsLam d hM.1 hρ.1 p : ℂ)) (hs X) =
      hs ((d⁻¹ : ℂ) • M * X * hatPow ρ (-1)) := by
  rw [spec_hsLam hM hρ (f := fun a ↦ (d : ℂ)⁻¹ * a) (g := fun b ↦ (b⁻¹ : ℂ))
    (fun a _ b _ ↦ by push_cast; ring), specFun_const_mul, specFun_ofReal,
    specFun_eq_hatPow hρ fun t ht ↦ by
      rw [neg_one_mul, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log ht]]

variable (hMf : Mf.PosDef) (hMs : Ms.PosDef) (hJM : ∀ Y, (Mf * J Y).trace = (Ms * Y).trace)
  (d : ℝ)

include hρf hρs hJ hJM in
/-- D5.12.3. `V* A V = B`: `⟪V(X√ρ_s), A V(Y√ρ_s)⟫ = Tr(X⊗I)* σ_f (Y⊗I) = Tr X* σ_s Y`, as
`Tr_F σ_f = σ_s`. -/
theorem hs_compress (x y : EuclideanSpace ℂ (n × n)) :
    ⟪hsVLin J ρf ρs x, spec (prodBasis hMf.1 hρf.1) (fun p ↦ (hsLam d hMf.1 hρf.1 p : ℂ))
      (hsVLin J ρf ρs y)⟫_ℂ =
    ⟪x, spec (prodBasis hMs.1 hρs.1) (fun p ↦ (hsLam d hMs.1 hρs.1 p : ℂ)) y⟫_ℂ := by
  rw [← hs_unhs x, ← hs_unhs y, hsVLin_hs, hsVLin_hs, spec_hsLam_id hMf hρf, spec_hsLam_id hMs hρs,
    inner_hs, inner_hs]
  set r := hatPow ρs (-(1 / 2))
  set s := hatPow ρf (1 / 2)
  set X := unhs x
  set Y := unhs y
  have hs' : sᴴ = s := conjTranspose_hatPow_half ρf
  have hr' : rᴴ = r := conjTranspose_hatPow_neg_half ρs
  have hsi : s * hatPow ρf (-1) * s = 1 := by
    rw [hatPow_mul_hatPow, hatPow_mul_hatPow, show (1 / 2 + -1 + 1 / 2 : ℂ) = 0 by ring,
      hatPow_zero]
  have hrr : r * r = hatPow ρs (-1) := by
    rw [hatPow_mul_hatPow, show (-(1 / 2) + -(1 / 2) : ℂ) = -1 by ring]
  calc ((J (X * r) * s)ᴴ * ((d⁻¹ : ℂ) • Mf * (J (Y * r) * s) * hatPow ρf (-1))).trace
      = (d⁻¹ : ℂ) * (s * (J (r * Xᴴ) * (Mf * (J (Y * r) * (s * hatPow ρf (-1)))))).trace := by
        rw [conjTranspose_mul, hs', ← hJ, conjTranspose_mul, hr']
        simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul, Matrix.mul_assoc]
    _ = (d⁻¹ : ℂ) * (Mf * J (Y * hatPow ρs (-1) * Xᴴ)).trace := by
        congr 1
        rw [trace_mul_comm]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc s, hsi, Matrix.mul_one, trace_mul_comm, Matrix.mul_assoc, ← map_mul,
          ← hrr]
        simp only [Matrix.mul_assoc]
    _ = (Xᴴ * ((d⁻¹ : ℂ) • Ms * Y * hatPow ρs (-1))).trace := by
        rw [hJM]
        simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
        rw [trace_mul_comm Xᴴ]
        simp only [Matrix.mul_assoc]

variable {d}

/-- D5.12.1–4. The resolvent compression of Lemma 5.2 on Hilbert–Schmidt spaces:
`A = L_{σ_f} R_{ρ_f⁻¹}`, `B = L_{σ_s} R_{ρ_s⁻¹}` (`σ_f = M_f / d`, `σ_s = M_s / d`), `V` of
`hsV`, `b₀ = √ρ_s`. -/
noncomputable def hsCompression (hd : 0 < d) :
    ResolventCompression (EuclideanSpace ℂ (m × m)) (EuclideanSpace ℂ (n × n)) (m × m) (n × n) where
  A := specLin (prodBasis hMf.1 hρf.1) fun p ↦ (hsLam d hMf.1 hρf.1 p : ℂ)
  B := specLin (prodBasis hMs.1 hρs.1) fun p ↦ (hsLam d hMs.1 hρs.1 p : ℂ)
  eA := prodBasis hMf.1 hρf.1
  eB := prodBasis hMs.1 hρs.1
  lam := hsLam d hMf.1 hρf.1
  mu := hsLam d hMs.1 hρs.1
  lam_pos p := by
    have := hMf.eigenvalues_pos p.1; have := hρf.eigenvalues_pos p.2; unfold hsLam; positivity
  mu_pos p := by
    have := hMs.eigenvalues_pos p.1; have := hρs.eigenvalues_pos p.2; unfold hsLam; positivity
  apply_eA := spec_apply_basis _ _
  apply_eB := spec_apply_basis _ _
  V := hsV hρf hρs hJ hJρ
  compress := hs_compress hρf hρs hJ hMf hMs hJM d
  b₀ := hs (hatPow ρs (1 / 2))

variable (hd : 0 < d)

/-- D5.12.4. `a₀ = V b₀ = √ρ_f`. -/
theorem hsCompression_a₀ :
    (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).a₀ = hs (hatPow ρf (1 / 2)) := by
  change hs (J (hatPow ρs (1 / 2) * hatPow ρs (-(1 / 2))) * hatPow ρf (1 / 2)) = _
  rw [hatPow_mul_hatPow, add_neg_cancel, hatPow_zero, map_one, Matrix.one_mul]

/-- D5.14.2. `⟨b₀, B b₀⟩ = Tr σ_s = Tr M_s / d`. -/
theorem hsCompression_quadB :
    (⟪(hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).b₀,
      (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).B
        (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).b₀⟫_ℂ) = (d⁻¹ : ℂ) * Ms.trace := by
  change ⟪hs _, spec _ _ (hs _)⟫_ℂ = _
  rw [spec_hsLam_id hMs hρs, inner_hs, conjTranspose_hatPow_half]
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [hatPow_mul_hatPow, hatPow_mul_hatPow, show (1 / 2 + (-1 + 1 / 2) : ℂ) = 0 by ring,
    hatPow_zero, Matrix.mul_one]

include hd in
/-- D5.14.1. `ρ_f ≤ d(I ⊗ ρ_{UF}) = d² σ_f` gives `⟨a₀, A⁻¹ a₀⟩ = Tr ρ_f² σ_f⁻¹ ≤ d² Tr ρ_f`. -/
theorem hsCompression_invA_le (hdom : ρf ≤ (d : ℂ) • Mf) :
    (⟪(hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).a₀,
      (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).invA
        (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).a₀⟫_ℂ).re ≤ d ^ 2 * ρf.trace.re := by
  rw [hsCompression_a₀]
  change (⟪hs _, spec (prodBasis hMf.1 hρf.1) (fun p ↦ ((hsLam d hMf.1 hρf.1 p)⁻¹ : ℝ))
    (hs _)⟫_ℂ).re ≤ _
  rw [spec_hsLam hMf hρf (G := fun t ↦ ((t⁻¹ : ℝ) : ℂ)) (f := fun a ↦ (d : ℂ) * (a : ℂ)⁻¹)
    (g := fun b ↦ (b : ℂ))
    (fun a _ b _ ↦ by push_cast; field_simp), specFun_const_mul, specFun_ofReal,
    specFun_eq_hatPow hMf (z := -1) fun t ht ↦ by
      rw [neg_one_mul, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log ht],
    hatPow_neg_one_of_posDef hMf, inner_hs, conjTranspose_hatPow_half]
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
  have e : (hatPow ρf (1 / 2) * (Mf⁻¹ * (hatPow ρf (1 / 2) * ρf))).trace =
      (ρf * Mf⁻¹ * ρf).trace := by
    rw [trace_mul_comm, Matrix.mul_assoc, hatPow_mul_self hρf, hatPow_mul_hatPow,
      show (1 / 2 + 1 + 1 / 2 : ℂ) = 1 + 1 by ring, ← hatPow_mul_hatPow,
      hatPow_one_of_posDef hρf, ← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [Matrix.mul_assoc (Mf⁻¹), e, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have h := re_trace_conj_le hρf.1 (inv_le_smul_inv hρf hMf hd hdom)
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1
    hρf.isUnit), Matrix.one_mul, trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  nlinarith

/-- D5.13.3–4. `-⟨a₀, log A a₀⟩ + ⟨b₀, log B b₀⟩ = D(ρ_f‖σ_f) - D(ρ_s‖σ_s)`, written with
`Tr ρ log ρ` and `Tr ρ log M`; the `log d` terms cancel. -/
theorem hsCompression_logGap :
    -(⟪(hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).a₀,
      (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).logA
        (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).a₀⟫_ℂ).re +
      (⟪(hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).b₀,
      (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).logB
        (hsCompression hρf hρs hJ hJρ hMf hMs hJM hd).b₀⟫_ℂ).re =
    ((ρf * specFun hρf.1 (fun t ↦ (Real.log t : ℂ))).trace -
      (ρf * specFun hMf.1 (fun t ↦ (Real.log t : ℂ))).trace -
      (ρs * specFun hρs.1 (fun t ↦ (Real.log t : ℂ))).trace +
      (ρs * specFun hMs.1 (fun t ↦ (Real.log t : ℂ))).trace).re := by
  rw [hsCompression_a₀]
  have hA := inner_spec_log_hsLam hMf hρf hd
  have hB := inner_spec_log_hsLam hMs hρs hd
  have htr : ρf.trace = ρs.trace := by simpa using hJρ 1
  change -(⟪hs _, spec (prodBasis hMf.1 hρf.1)
      (fun p ↦ ((Real.log (hsLam d hMf.1 hρf.1 p) : ℝ) : ℂ)) (hs _)⟫_ℂ).re +
    (⟪hs _, spec (prodBasis hMs.1 hρs.1)
      (fun p ↦ ((Real.log (hsLam d hMs.1 hρs.1 p) : ℝ) : ℂ)) (hs _)⟫_ℂ).re = _
  rw [hA, hB, htr]
  simp only [Complex.sub_re, Complex.add_re]
  ring

end Compression

end Conditional

end AreaLaw
