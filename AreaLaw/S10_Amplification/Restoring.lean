import AreaLaw.S10_Amplification.Setup

/-!
# §10 The restoring and column operators

Digest `digest/10-amplification.md` (D10.6–D10.10), paper `paper/sections/09-amplification.tex`
lines 324–447. No geometry: any site type.

Setting: `X, Y ⊆ Λ` disjoint, `S₀ = X ∪ Y`, `Ω` a unit vector on `Λ`; spectators
`s', e'` (first and second factor of `Reg loc X × Reg loc X`). `ρ_X = ∑_x p_x |x⟩⟨x|` with
`|x⟩ = U · x` the columns of the eigenvector unitary; `|0⟩` the blank configuration.

Some declarations here come from the v1 files `OpenAI/FinSum.lean`, `OpenAI/RestoringNorm.lean`,
whose header records them as ported or adapted from `LionSR/QICLean` (see `NOTICE`).
-/

namespace AreaLaw

open Arealaw Matrix Finset Amplification
open OpenAI (pureState)
open scoped Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-! ## Helpers on vectors, unitaries and regions -/

section Helpers

variable {m n m' n' : Type*}

-- helper
theorem kronecker_mulVec_tensVec [Fintype m'] [Fintype n'] (A : Matrix m m' ℂ)
    (B : Matrix n n' ℂ) (u : m' → ℂ) (v : n' → ℂ) :
    (A ⊗ₖ B) *ᵥ tensVec u v = tensVec (A *ᵥ u) (B *ᵥ v) := by
  ext ⟨i, j⟩
  simp only [mulVec, dotProduct, tensVec, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

-- helper
theorem star_tensVec_dotProduct [Fintype m] [Fintype n] (u u' : m → ℂ) (v v' : n → ℂ) :
    star (tensVec u v) ⬝ᵥ tensVec u' v' = (star u ⬝ᵥ u') * (star v ⬝ᵥ v') := by
  simp only [dotProduct, tensVec, Pi.star_apply, star_mul', Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

-- helper
theorem star_sum_smul_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype n]
    (c : ι → ℂ) (w : ι → n → ℂ) (hw : ∀ i j, star (w i) ⬝ᵥ w j = if i = j then 1 else 0) :
    star (∑ i, c i • w i) ⬝ᵥ (∑ i, c i • w i) = ∑ i, star (c i) * c i := by
  simp only [star_sum, star_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, hw, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq', mul_comm]

-- helper
theorem vnorm_tensVec [Fintype m] [Fintype n] {Ω : m → ℂ} (hΩ : star Ω ⬝ᵥ Ω = 1)
    (ξ : n → ℂ) : vnorm (tensVec Ω ξ) = vnorm ξ := by
  rw [vnorm_eq_sqrt, vnorm_eq_sqrt, star_tensVec_dotProduct, hΩ, one_mul]

-- helper
theorem tensVec_smul_right (u : m → ℂ) (c : ℂ) (v : n → ℂ) :
    tensVec u (c • v) = c • tensVec u v := by
  ext ⟨i, j⟩
  simp only [tensVec, Pi.smul_apply, smul_eq_mul]
  ring

-- helper
theorem tensVec_smul_left (u : m → ℂ) (c : ℂ) (v : n → ℂ) :
    tensVec (c • u) v = c • tensVec u v := by
  ext ⟨i, j⟩
  simp only [tensVec, Pi.smul_apply, smul_eq_mul]
  ring

-- helper
theorem tensVec_sum_right {ι : Type*} (u : m → ℂ) (s : Finset ι) (v : ι → n → ℂ) :
    tensVec u (∑ i ∈ s, v i) = ∑ i ∈ s, tensVec u (v i) := by
  ext ⟨a, b⟩
  simp [tensVec, Finset.sum_apply, Finset.mul_sum]

-- helper
theorem sum_sum_smul_tensVec {ι κ : Type*} (Ω : m → ℂ) (s : Finset ι) (t : Finset κ)
    (a : ι → κ → ℂ) (w : ι → κ → n → ℂ) :
    ∑ x ∈ s, ∑ y ∈ t, a x y • tensVec Ω (w x y) = tensVec Ω (∑ x ∈ s, ∑ y ∈ t, a x y • w x y) := by
  simp only [tensVec_sum_right, tensVec_smul_right]

-- helper
theorem tensVec_zero_left (v : n → ℂ) : tensVec (0 : m → ℂ) v = 0 := by
  ext ⟨i, j⟩
  simp [tensVec]

-- helper
theorem tensVec_ite_left (c : Prop) [Decidable c] (a : m → ℂ) (v : n → ℂ) :
    tensVec (if c then a else 0) v = if c then tensVec a v else 0 := by
  split_ifs <;> simp [tensVec_zero_left]

-- helper
theorem vecMulVec_mulVec' [Fintype n] (u : m → ℂ) (v w : n → ℂ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

-- helper
theorem vecMulVec_mul_vecMulVec' [Fintype n] (u : m → ℂ) (v w : n → ℂ) (x : m' → ℂ) :
    vecMulVec u v * vecMulVec w x = (v ⬝ᵥ w) • vecMulVec u x := by
  rw [vecMulVec_mul_vecMulVec]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

variable [Fintype n] [DecidableEq n]

-- helper
theorem sum_star_mul_unitary (U : unitaryGroup n ℂ) (x x' : n) :
    ∑ s, star ((U : Matrix n n ℂ) s x) * (U : Matrix n n ℂ) s x' = if x = x' then 1 else 0 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self U) x) x'
  rw [mul_apply, one_apply] at h
  exact h

-- helper
theorem sum_mul_star_unitary (U : unitaryGroup n ℂ) (s s' : n) :
    ∑ x, (U : Matrix n n ℂ) s x * star ((U : Matrix n n ℂ) s' x) = if s = s' then 1 else 0 := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self U) s) s'
  rw [mul_apply, one_apply] at h
  exact h

-- helper
theorem star_unitary_mulVec_dotProduct (U : unitaryGroup n ℂ) (a : n → ℂ) :
    star ((U : Matrix n n ℂ) *ᵥ a) ⬝ᵥ ((U : Matrix n n ℂ) *ᵥ a) = star a ⬝ᵥ a := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
    Unitary.coe_star_mul_self, one_mulVec]

end Helpers

/-! ## Helpers on the Loewner order and Gram matrices -/

section Loewner

variable {m n ι : Type*}

-- helper
theorem posSemidef_of_proj [Fintype n] {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) :
    P.PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self P
  rwa [hP, hPP] at h

-- helper
theorem posSemidef_one_sub_of_proj [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : Pᴴ = P) (hPP : P * P = P) : (1 - P).PosSemidef := by
  refine posSemidef_of_proj (by rw [conjTranspose_sub, conjTranspose_one, hP]) ?_
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]
  simp

-- helper
theorem smul_le_smul_of_le_of_posSemidef {a b : ℝ} (hab : a ≤ b) {Z : Matrix n n ℂ}
    (hZ : Z.PosSemidef) : (a : ℂ) • Z ≤ (b : ℂ) • Z := by
  rw [Matrix.le_iff, ← sub_smul, ← Complex.ofReal_sub]
  exact hZ.smul (by exact_mod_cast sub_nonneg.2 hab)

-- helper
theorem smul_le_smul_of_nonneg {a : ℝ} (ha : 0 ≤ a) {Z W : Matrix n n ℂ} (h : Z ≤ W) :
    (a : ℂ) • Z ≤ (a : ℂ) • W := by
  rw [Matrix.le_iff, ← smul_sub]
  exact Matrix.PosSemidef.smul h (by exact_mod_cast ha)

-- helper
theorem submatrix_le_submatrix {Z W : Matrix n n ℂ} (h : Z ≤ W) (e : m ≃ n) :
    Z.submatrix e e ≤ W.submatrix e e := by
  exact (Matrix.PosSemidef.submatrix h e :)

-- helper
theorem sum_kronecker (s : Finset ι) (A : ι → Matrix m m ℂ) (P : Matrix n n ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ P = ∑ i ∈ s, A i ⊗ₖ P := by
  ext a b
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

-- helper
theorem submatrix_sum (s : Finset ι) (A : ι → Matrix n n ℂ) (e : m ≃ n) :
    (∑ i ∈ s, A i).submatrix e e = ∑ i ∈ s, (A i).submatrix e e := by
  ext a b
  simp [Matrix.sum_apply]

/-- D10.8.1 (shape). The Gram matrix of `∑_i A_i ⊗ B_i` with `B_iᴴ B_j = δ_{ij} P`. -/
theorem gram_sum_kronecker [Fintype m] [Fintype n] [DecidableEq ι] (s : Finset ι)
    (A : ι → Matrix m m ℂ) (B : ι → Matrix n n ℂ) (P : Matrix n n ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, (B i)ᴴ * B j = if i = j then P else 0) :
    (∑ i ∈ s, A i ⊗ₖ B i)ᴴ * (∑ i ∈ s, A i ⊗ₖ B i) = (∑ i ∈ s, (A i)ᴴ * A i) ⊗ₖ P := by
  rw [conjTranspose_sum, Finset.sum_mul_sum, sum_kronecker]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => ?_]
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hB i hi i hi, if_pos rfl]
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hB i hi j hj, if_neg (Ne.symm hji),
      kronecker_zero]

/-- `Rᴴ R ≤ c` gives `‖R‖ ≤ √c` (`‖R‖² = ‖Rᴴ R‖`, D10.8.5). -/
theorem norm_le_sqrt_of_gram_le [Fintype n] [DecidableEq n] {R : Matrix n n ℂ} {c : ℝ}
    (hc : 0 ≤ c) (h : Rᴴ * R ≤ (c : ℂ) • 1) : ‖R‖ ≤ Real.sqrt c := by
  have h0 : 0 ≤ Rᴴ * R := (posSemidef_conjTranspose_mul_self R).nonneg
  have h1 : ‖Rᴴ * R‖ ≤ c := by
    rw [CStarAlgebra.norm_le_iff_le_algebraMap _ hc h0, Algebra.algebraMap_eq_smul_one]
    rwa [Complex.coe_smul] at h
  rw [l2_opNorm_conjTranspose_mul_self] at h1
  exact (Real.le_sqrt (norm_nonneg _) hc).2 (by nlinarith)

-- helper
theorem kronecker_le_smul_one [Finite m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {G : Matrix m m ℂ} {P : Matrix n n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hG : G ≤ (c : ℂ) • 1) (hP : Pᴴ = P) (hPP : P * P = P) : G ⊗ₖ P ≤ (c : ℂ) • 1 := by
  have he : (c : ℂ) • ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ)) - G ⊗ₖ P =
      ((c : ℂ) • 1 - G) ⊗ₖ P + (c : ℂ) • ((1 : Matrix m m ℂ) ⊗ₖ (1 - P)) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  rw [Matrix.le_iff, ← one_kronecker_one, he]
  exact (Matrix.PosSemidef.kronecker hG (posSemidef_of_proj hP hPP)).add
    ((Matrix.PosSemidef.kronecker Matrix.PosSemidef.one
      (posSemidef_one_sub_of_proj hP hPP)).smul (by exact_mod_cast hc))

-- helper
theorem star_single_one [DecidableEq m] (b : m) :
    star (Pi.single b (1 : ℂ) : m → ℂ) = Pi.single b 1 := by
  ext a
  by_cases h : a = b <;> simp [h]

-- helper
theorem conj_le_conj [Fintype n] {k : Type*} [Finite k] {A B : Matrix n n ℂ} (h : A ≤ B)
    (L : Matrix n k ℂ) :
    Lᴴ * A * L ≤ Lᴴ * B * L := by
  have := Matrix.PosSemidef.conjTranspose_mul_mul_same h L
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this

-- helper
theorem kronecker_le_kronecker_left [Finite m] [Finite n] {E : Matrix m m ℂ} (hE : E.PosSemidef)
    {A B : Matrix n n ℂ} (h : A ≤ B) : E ⊗ₖ A ≤ E ⊗ₖ B := by
  have he : E ⊗ₖ B - E ⊗ₖ A = E ⊗ₖ (B - A) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp [kroneckerMap_apply, mul_sub]
  rw [Matrix.le_iff, he]
  exact hE.kronecker h

/-- `|u⟩ ⊗ 1 : ℋ_k → ℋ_m ⊗ ℋ_k`; `(|u⟩ ⊗ 1)ᴴ N (|u⟩ ⊗ 1) = ⟨u|N|u⟩` is the partial matrix
element. -/
def ketOne {k : Type*} [DecidableEq k] (u : m → ℂ) : Matrix (m × k) k ℂ :=
  Matrix.of fun ay y' => u ay.1 * (1 : Matrix k k ℂ) ay.2 y'

-- helper
theorem ketOne_conj_apply {k : Type*} [Fintype m] [Fintype k] [DecidableEq k] (u : m → ℂ)
    (N : Matrix (m × k) (m × k) ℂ) (y y' : k) :
    ((ketOne (k := k) u)ᴴ * N * ketOne (k := k) u) y y' =
      ∑ c, ∑ c', star (u c) * N (c, y) (c', y') * u c' := by
  simp only [mul_apply, conjTranspose_apply, ketOne, of_apply, one_apply, Fintype.sum_prod_type,
    apply_ite star, star_zero, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `∑_x ⟨x|N|x⟩ = Tr₁ N` for an orthonormal basis `|x⟩`. -/
theorem sum_ketOne_conj {k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (U : unitaryGroup m ℂ) (N : Matrix (m × k) (m × k) ℂ) :
    ∑ x, (ketOne (k := k) (fun s => (U : Matrix m m ℂ) s x))ᴴ * N *
      ketOne (k := k) (fun s => (U : Matrix m m ℂ) s x) = traceLeft N := by
  ext y y'
  simp only [Matrix.sum_apply, ketOne_conj_apply, traceLeft, of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have h : ∀ c', ∑ x, star ((U : Matrix m m ℂ) c x) * N (c, y) (c', y') * (U : Matrix m m ℂ) c' x
      = (if c' = c then 1 else 0) * N (c, y) (c', y') := by
    intro c'
    rw [← sum_mul_star_unitary U c' c, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `(|u⟩⟨b| ⊗ T)ᴴ N (|u⟩⟨b| ⊗ T) = |b⟩⟨b| ⊗ Tᴴ ⟨u|N|u⟩ T`. -/
theorem vecMulVec_kronecker_conj {k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (u : m → ℂ) (b : m) (T : Matrix k k ℂ) (N : Matrix (m × k) (m × k) ℂ) :
    (vecMulVec u (Pi.single b 1) ⊗ₖ T)ᴴ * N * (vecMulVec u (Pi.single b 1) ⊗ₖ T) =
      vecMulVec (Pi.single b 1) (Pi.single b 1) ⊗ₖ
        (Tᴴ * ((ketOne (k := k) u)ᴴ * N * ketOne (k := k) u) * T) := by
  set W : Matrix k (m × k) ℂ := Matrix.of fun z ay => (Pi.single b (1 : ℂ) : m → ℂ) ay.1 * T z ay.2
  have hKW : vecMulVec u (Pi.single b 1) ⊗ₖ T = ketOne (k := k) u * W := by
    ext ⟨c, d⟩ ⟨a, y⟩
    simp [W, mul_apply, ketOne, kroneckerMap_apply, vecMulVec_apply, one_apply, ite_mul]
    ring
  rw [hKW, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc N,
    ← Matrix.mul_assoc (ketOne (k := k) u)ᴴ, ← Matrix.mul_assoc]
  ext ⟨a, y⟩ ⟨a', y'⟩
  simp only [mul_apply, conjTranspose_apply, W, of_apply, kroneckerMap_apply, vecMulVec_apply,
    star_mul', Finset.sum_mul, Finset.mul_sum, Pi.single_apply, apply_ite star, star_one,
    star_zero]
  refine Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- D10.8.3. `B_Y = ∑_{x sel} p_x^{-1} T₀⟨x|Q|x⟩T₀ ≤ e^{a₁+a₂+a₃} T₀`, from `p_x^{-1} ≤ e^{a₁}`,
`Q ≤ e^{a₂} ρ` and `T₀ Tr_X(ρ) T₀ ≤ e^{a₃} T₀` (`ρ` on `X × Y`). -/
theorem step_10_8_3 {k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (U : unitaryGroup m ℂ) (p : m → ℝ) (sel : Finset m) (ρ Q : Matrix (m × k) (m × k) ℂ)
    (T₀ : Matrix k k ℂ) (a₁ a₂ a₃ : ℝ) (hρ : ρ.PosSemidef)
    (h1 : ∀ x ∈ sel, 0 < p x ∧ (p x)⁻¹ ≤ Real.exp a₁) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hQ : Q ≤ (Real.exp a₂ : ℂ) • ρ) (hTh : T₀ᴴ = T₀)
    (hT : T₀ * traceLeft ρ * T₀ ≤ (Real.exp a₃ : ℂ) • T₀) :
    ∑ x ∈ sel, (((p x)⁻¹ : ℝ) : ℂ) • (T₀ * ((ketOne (k := k) (fun s => (U : Matrix m m ℂ) s x))ᴴ
      * Q * ketOne (k := k) (fun s => (U : Matrix m m ℂ) s x)) * T₀) ≤
      (Real.exp (a₁ + a₂ + a₃) : ℂ) • T₀ := by
  set L := fun x => ketOne (k := k) (fun s => (U : Matrix m m ℂ) s x) * T₀
  have hL : ∀ M : Matrix (m × k) (m × k) ℂ, ∀ x,
      T₀ * ((ketOne (k := k) (fun s => (U : Matrix m m ℂ) s x))ᴴ * M *
        ketOne (k := k) (fun s => (U : Matrix m m ℂ) s x)) * T₀ = (L x)ᴴ * M * L x :=
    fun M x => by
    simp only [L, conjTranspose_mul, hTh, Matrix.mul_assoc]
  simp only [hL]
  have hLρ : ∀ x, ((L x)ᴴ * ρ * L x).PosSemidef := fun x => hρ.conjTranspose_mul_mul_same _
  -- D10.8.2: `p_x^{-1} ≤ e^{a₁}` and `Q ≤ e^{a₂} ρ`, compressed by `⟨x| ⊗ T₀`
  have hx : ∀ x ∈ sel, (((p x)⁻¹ : ℝ) : ℂ) • ((L x)ᴴ * Q * L x) ≤
      ((Real.exp a₁ * Real.exp a₂ : ℝ) : ℂ) • ((L x)ᴴ * ρ * L x) := by
    intro x hx
    have hQL : ((L x)ᴴ * Q * L x).PosSemidef :=
      (posSemidef_of_proj hQh hQQ).conjTranspose_mul_mul_same _
    have hc := conj_le_conj hQ (L x)
    rw [Matrix.mul_smul, Matrix.smul_mul] at hc
    calc (((p x)⁻¹ : ℝ) : ℂ) • ((L x)ᴴ * Q * L x)
        ≤ (Real.exp a₁ : ℂ) • ((L x)ᴴ * Q * L x) :=
          smul_le_smul_of_le_of_posSemidef (h1 x hx).2 hQL
      _ ≤ (Real.exp a₁ : ℂ) • ((Real.exp a₂ : ℂ) • ((L x)ᴴ * ρ * L x)) :=
          smul_le_smul_of_nonneg (Real.exp_pos _).le hc
      _ = _ := by rw [smul_smul, Complex.ofReal_mul]
  -- D10.8.3: selected `x` `≤` all `x`; `∑_x ⟨x|ρ|x⟩ = Tr_X ρ`
  have hsum : ∑ x, (L x)ᴴ * ρ * L x = T₀ * traceLeft ρ * T₀ := by
    rw [← sum_ketOne_conj U ρ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => (hL ρ x).symm
  calc ∑ x ∈ sel, (((p x)⁻¹ : ℝ) : ℂ) • ((L x)ᴴ * Q * L x)
      ≤ ∑ x ∈ sel, ((Real.exp a₁ * Real.exp a₂ : ℝ) : ℂ) • ((L x)ᴴ * ρ * L x) :=
        Finset.sum_le_sum hx
    _ = ((Real.exp a₁ * Real.exp a₂ : ℝ) : ℂ) • ∑ x ∈ sel, (L x)ᴴ * ρ * L x :=
        (Finset.smul_sum ..).symm
    _ ≤ ((Real.exp a₁ * Real.exp a₂ : ℝ) : ℂ) • ∑ x, (L x)ᴴ * ρ * L x :=
        smul_le_smul_of_nonneg (by positivity) (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun x _ _ => (hLρ x).nonneg)
    _ ≤ ((Real.exp a₁ * Real.exp a₂ : ℝ) : ℂ) • ((Real.exp a₃ : ℂ) • T₀) :=
        smul_le_smul_of_nonneg (by positivity) (hsum ▸ hT)
    _ = _ := by rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]

-- helper
theorem submatrix_smul' {l o : Type*} (r : ℂ) (A : Matrix n n ℂ) (e : l → n) (f : o → n) :
    (r • A).submatrix e f = r • A.submatrix e f := rfl

-- helper
theorem dotProduct_col_unitary [Fintype n] [DecidableEq n] (U : unitaryGroup n ℂ) (x x' : n) :
    (star fun s => (U : Matrix n n ℂ) s x) ⬝ᵥ (fun s => (U : Matrix n n ℂ) s x') =
      if x = x' then 1 else 0 :=
  sum_star_mul_unitary U x x'

-- helper
theorem single_dotProduct_single' [Fintype n] [DecidableEq n] (y y' : n) :
    Pi.single y (1 : ℂ) ⬝ᵥ Pi.single y' 1 = if y = y' then 1 else 0 := by
  rw [single_dotProduct, one_mul, Pi.single_apply, eq_comm]

-- helper
theorem kronecker_sum (s : Finset ι) (E : Matrix m m ℂ) (A : ι → Matrix n n ℂ) :
    E ⊗ₖ (∑ i ∈ s, A i) = ∑ i ∈ s, E ⊗ₖ A i := by
  ext a b
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

-- helper
theorem mul_submatrix_equiv' [Fintype m] [Fintype n] (M : Matrix n n ℂ) (K : Matrix m m ℂ)
    (e : n ≃ m) : M * K.submatrix e e = (M.submatrix e.symm e.symm * K).submatrix e e := by
  rw [← submatrix_mul_equiv (M.submatrix e.symm e.symm) K e e e]
  simp

-- helper
theorem conj_proj_submatrix [Fintype m] [Fintype n] {Q : Matrix n n ℂ} (hQh : Qᴴ = Q)
    (hQQ : Q * Q = Q) (K : Matrix m m ℂ) (e : n ≃ m) :
    (Q * K.submatrix e e)ᴴ * (Q * K.submatrix e e) =
      (Kᴴ * Q.submatrix e.symm e.symm * K).submatrix e e := by
  rw [conjTranspose_mul, conjTranspose_submatrix, hQh, Matrix.mul_assoc, ← Matrix.mul_assoc Q,
    hQQ, mul_submatrix_equiv', submatrix_mul_equiv, Matrix.mul_assoc]

-- helper
theorem proj_vecMulVec_single [Fintype m] [DecidableEq m] (b : m) :
    (vecMulVec (Pi.single b (1 : ℂ)) (Pi.single b 1))ᴴ =
        vecMulVec (Pi.single b (1 : ℂ)) (Pi.single b 1) ∧
      vecMulVec (Pi.single b (1 : ℂ)) (Pi.single b 1) *
        vecMulVec (Pi.single b (1 : ℂ)) (Pi.single b 1) =
        vecMulVec (Pi.single b (1 : ℂ)) (Pi.single b 1) := by
  refine ⟨by rw [conjTranspose_vecMulVec, star_single_one], ?_⟩
  rw [vecMulVec_mul_vecMulVec']
  simp

-- helper
theorem proj_kronecker [Fintype m] [Fintype n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : Aᴴ = A ∧ A * A = A) (hB : Bᴴ = B ∧ B * B = B) :
    (A ⊗ₖ B)ᴴ = A ⊗ₖ B ∧ (A ⊗ₖ B) * (A ⊗ₖ B) = A ⊗ₖ B := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hA.1, hA.2, hB.1, hB.2]
  exact ⟨rfl, rfl⟩

-- helper
theorem le_one_of_proj [Fintype n] [DecidableEq n] {P : Matrix n n ℂ} (hP : Pᴴ = P ∧ P * P = P) :
    P ≤ 1 :=
  posSemidef_one_sub_of_proj hP.1 hP.2

/-- D10.10.3. If `0 ≤ m ≤ diag(p)`, then `∑_z p_z^{-1} |m_{zx}|² ≤ m_{xx}` for every `x`: the
diagonal of `m ρ⁺ m ≤ m`, `ρ = diag(p)`, `ρ⁺ = diag(p⁻¹)` (`p⁻¹ = 0` on the kernel). -/
theorem sum_inv_mul_star_mul_le [Fintype n] [DecidableEq n] {m : Matrix n n ℂ}
    (hm : m.PosSemidef) {p : n → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hmp : m ≤ diagonal (fun x => (p x : ℂ))) (x : n) :
    ∑ z, (((p z)⁻¹ : ℝ) : ℂ) * (star (m z x) * m z x) ≤ m x x := by
  have hdiag : m x x ≤ (p x : ℂ) := by
    have := (Matrix.le_iff.mp hmp).diag_nonneg (i := x)
    simpa [sub_nonneg] using this
  by_cases hpx : p x = 0
  · -- `M_X` vanishes on `ker ρ_X`
    have h0 : m x x = 0 := le_antisymm (by simpa [hpx] using hdiag) hm.diag_nonneg
    have hcol : m *ᵥ Pi.single x 1 = 0 :=
      (hm.dotProduct_mulVec_zero_iff _).1 (by simp [h0])
    have hz : ∀ z, m z x = 0 := fun z => by simpa [mulVec_single_one] using congrFun hcol z
    simp [hz]
  · have hpx' : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx)
    set d : n → ℂ := fun z => (((Real.sqrt (p z))⁻¹ : ℝ) : ℂ) with hd
    have hdd : ∀ z, d z * d z = (((p z)⁻¹ : ℝ) : ℂ) := fun z => by
      simp only [d, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (hp z)]
    have hD : (diagonal d)ᴴ = diagonal d := by
      rw [diagonal_conjTranspose]
      congr 1
      funext z
      simp [d, Complex.conj_ofReal]
    -- `A_X = ρ_X^{-1/2} M_X ρ_X^{-1/2}`, `0 ≤ A_X ≤ I`
    set N := diagonal d * m * diagonal d with hN
    have hN0 : 0 ≤ N := by
      rw [Matrix.nonneg_iff_posSemidef]
      have := hm.conjTranspose_mul_mul_same (diagonal d)
      rwa [hD] at this
    have hN1 : N ≤ 1 := by
      have h := conj_le_conj hmp (diagonal d)
      rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal] at h
      refine h.trans ?_
      rw [Matrix.le_iff, ← diagonal_one, diagonal_sub, posSemidef_diagonal_iff]
      intro z
      rw [mul_right_comm, hdd, ← Complex.ofReal_mul]
      by_cases hz : p z = 0
      · simp [hz]
      · rw [inv_mul_cancel₀ hz]
        simp
    have hN2 : N * N ≤ N := by
      have := CStarAlgebra.pow_antitone hN0 hN1 (show 1 ≤ 2 by norm_num)
      simpa [sq] using this
    -- `M_X ρ_X⁺ M_X = ρ_X^{1/2} A_X² ρ_X^{1/2} ≤ ρ_X^{1/2} A_X ρ_X^{1/2} = M_X`, at `(x, x)`
    have hxx := (Matrix.le_iff.mp hN2).diag_nonneg (i := x)
    have hNab : ∀ a b, N a b = d a * m a b * d b := fun a b => by
      simp [hN, diagonal_mul, mul_diagonal]
    rw [Matrix.sub_apply, mul_apply] at hxx
    simp only [hNab] at hxx
    have key : ∑ z, d x * m x z * d z * (d z * m z x * d x) =
        (d x * d x) * ∑ z, (((p z)⁻¹ : ℝ) : ℂ) * (star (m z x) * m z x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← hdd z, ← hm.isHermitian.apply x z]
      ring
    rw [key, show d x * m x x * d x = (d x * d x) * m x x by ring, ← mul_sub, hdd] at hxx
    have h := mul_nonneg (show (0 : ℂ) ≤ (p x : ℂ) by exact_mod_cast hp x) hxx
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpx, Complex.ofReal_one, one_mul] at h
    exact sub_nonneg.1 h

/-- D10.10.4. If `0 ≤ m ≤ diag(p)`, then `∑_x p_x^{-1} ∑_z |m_{zx}|² ≤ Tr m`. -/
theorem sum_inv_mul_sum_star_mul_le_trace [Fintype n] [DecidableEq n] {m : Matrix n n ℂ}
    (hm : m.PosSemidef) {p : n → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hmp : m ≤ diagonal (fun x => (p x : ℂ))) :
    ∑ x, (((p x)⁻¹ : ℝ) : ℂ) * ∑ z, star (m z x) * m z x ≤ m.trace := by
  have h : ∀ x z, star (m z x) * m z x = star (m x z) * m x z := fun x z => by
    rw [← hm.isHermitian.apply x z, ← hm.isHermitian.apply z x, star_star, mul_comm]
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm, Matrix.trace]
  exact Finset.sum_le_sum fun z _ => sum_inv_mul_star_mul_le hm hp hmp z

-- helper
theorem star_finset_sum_smul_dotProduct {ι : Type*} [DecidableEq ι] [Fintype n] (s : Finset ι)
    (c : ι → ℂ) (w : ι → n → ℂ) (hw : ∀ i j, star (w i) ⬝ᵥ w j = if i = j then 1 else 0) :
    star (∑ i ∈ s, c i • w i) ⬝ᵥ (∑ i ∈ s, c i • w i) = ∑ i ∈ s, star (c i) * c i := by
  simp only [star_sum, star_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, hw, smul_eq_mul, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_ite_eq', if_pos hi, mul_comm]

-- helper
theorem star_sum_sum_smul_dotProduct {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype n]
    (s : Finset ι) (t : Finset κ) (c : ι → κ → ℂ) (w : ι → κ → n → ℂ)
    (hw : ∀ i j i' j', star (w i j) ⬝ᵥ w i' j' = if i = i' ∧ j = j' then 1 else 0) :
    star (∑ i ∈ s, ∑ j ∈ t, c i j • w i j) ⬝ᵥ (∑ i ∈ s, ∑ j ∈ t, c i j • w i j) =
      ∑ i ∈ s, ∑ j ∈ t, star (c i j) * c i j := by
  have := star_finset_sum_smul_dotProduct (s ×ˢ t) (fun q => c q.1 q.2) (fun q => w q.1 q.2)
    (fun q q' => by simpa [Prod.ext_iff] using hw q.1 q.2 q'.1 q'.2)
  rw [← Finset.sum_product' s t, this]
  exact Finset.sum_product' s t (fun i j => star (c i j) * c i j)

-- helper
theorem traceRight_one_kronecker_mul_comm {k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    (B : Matrix k k ℂ) (N : Matrix (m × k) (m × k) ℂ) :
    traceRight (((1 : Matrix m m ℂ) ⊗ₖ B) * N) = traceRight (N * ((1 : Matrix m m ℂ) ⊗ₖ B)) := by
  have hl : ∀ a b j, (((1 : Matrix m m ℂ) ⊗ₖ B) * N) (a, b) j = ∑ d, B b d * N (a, d) j := by
    intro a b j
    simp only [mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hr : ∀ i a b, (N * ((1 : Matrix m m ℂ) ⊗ₖ B)) i (a, b) = ∑ d, N i (a, d) * B d b := by
    intro i a b
    simp only [mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, ite_mul, one_mul,
      zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ext a a'
  simp only [traceRight, of_apply, hl, hr]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- D10.10.2. `Tr_Y[(1 ⊗ T₀) Q ρ Q (1 ⊗ T₀)] ≤ Tr_Y ρ` for projections `Q` commuting with `ρ`
and `T₀`: `ρ_X - M_X = Tr_Y[(1-T)ρ(1-T)] + Tr_Y[T(1-Q)ρ(1-Q)T]`. -/
theorem traceRight_conj_le {k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    {ρ Q : Matrix (m × k) (m × k) ℂ} {T₀ : Matrix k k ℂ} (hρ : ρ.PosSemidef) (hQh : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hQρ : Q * ρ = ρ * Q) (hTh : T₀ᴴ = T₀) (hTT : T₀ * T₀ = T₀) :
    traceRight (((1 : Matrix m m ℂ) ⊗ₖ T₀) * (Q * ρ * Q) * ((1 : Matrix m m ℂ) ⊗ₖ T₀)) ≤
      traceRight ρ := by
  classical
  set T := (1 : Matrix m m ℂ) ⊗ₖ T₀ with hTdef
  have hT : Tᴴ = T ∧ T * T = T := proj_kronecker ⟨conjTranspose_one, Matrix.mul_one 1⟩ ⟨hTh, hTT⟩
  have hcyc := traceRight_one_kronecker_mul_comm (m := m) T₀
  have hQρQ : Q * ρ * Q = ρ * Q := by rw [hQρ, Matrix.mul_assoc, hQQ]
  have h1Q : (1 - Q) * ρ * (1 - Q) = ρ - Q * ρ * Q := by
    rw [hQρQ, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      hQρ, Matrix.mul_assoc, hQQ]
    abel
  have he : traceRight ρ - traceRight (T * (Q * ρ * Q) * T) =
      traceRight ((1 - T) * ρ * (1 - T)) + traceRight (T * ((1 - Q) * ρ * (1 - Q)) * T) := by
    have h2 : traceRight (T * ρ * T) = traceRight (ρ * T) := by
      rw [Matrix.mul_assoc, hTdef, hcyc, ← hTdef, Matrix.mul_assoc, hT.2]
    have h3 : traceRight (T * ρ) = traceRight (ρ * T) := hcyc ρ
    rw [h1Q]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, traceRight_sub]
    rw [h2, h3]
    abel
  rw [Matrix.le_iff, he]
  refine Matrix.PosSemidef.add (Matrix.PosSemidef.traceRight ?_) (Matrix.PosSemidef.traceRight ?_)
  · have := hρ.conjTranspose_mul_mul_same (1 - T)
    rwa [conjTranspose_sub, conjTranspose_one, hT.1] at this
  · have := hρ.conjTranspose_mul_mul_same ((1 - Q) * T)
    rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hT.1, hQh] at this
    simpa only [Matrix.mul_assoc] using this

end Loewner




section Region


variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {Λ X Y : Finset σ}

-- helper (the statement of `AreaLaw.extendId_kronUnion` in §3, not imported here)
theorem extendId_union_kronUnion (hX : X ⊆ Λ) (hY : Y ⊆ Λ) (hXY : Disjoint X Y)
    (A : Matrix (Reg loc X) (Reg loc X) ℂ) (B : Matrix (Reg loc Y) (Reg loc Y) ℂ) :
    extendId (Finset.union_subset hX hY) ((A ⊗ₖ B).submatrix (unionEquiv hXY) (unionEquiv hXY)) =
      extendId hX A * extendId hY B := by
  change extendId _ (kronUnion hXY A B) = _
  ext w w'
  rw [extendId_mul_extendId_apply hX hY hXY]
  simp only [extendId, kronUnion, of_apply, unionEquiv_apply]
  have : restr (S := Λ \ (X ∪ Y)) Finset.sdiff_subset w =
      restr (S := Λ \ (X ∪ Y)) Finset.sdiff_subset w' ↔
        ∀ i : Λ, i.1 ∉ X → i.1 ∉ Y → w i = w' i := by
    refine ⟨fun h i hX hY ↦ ?_, fun h ↦ funext fun i ↦ ?_⟩
    · exact congrFun h ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, by simp [hX, hY]⟩⟩
    · have := (Finset.mem_sdiff.1 i.2).2
      exact h ⟨i.1, Finset.sdiff_subset i.2⟩ (fun h' ↦ this (Finset.mem_union_left _ h'))
        (fun h' ↦ this (Finset.mem_union_right _ h'))
  simp only [this]
  rfl

-- helper
theorem extendId_mulVec_glue (hX : X ⊆ Λ) (A : Matrix (Reg loc X) (Reg loc X) ℂ)
    (v : Reg loc Λ → ℂ) (a : Reg loc X) (z : Reg loc (Λ \ X)) :
    (extendId hX A *ᵥ v) (glue a z) = ∑ b, A a b * v (glue b z) := by
  simp only [mulVec, dotProduct]
  rw [← (glueEquiv hX).sum_comp, Fintype.sum_prod_type]
  simp [extendId_apply_glue, ite_mul]

variable [∀ i, Nonempty (loc i)]

omit [∀ i, Fintype (loc i)] in
-- helper
theorem copyVec_apply_glue (hX : X ⊆ Λ) (v : Reg loc Λ → ℂ) (a : Reg loc X)
    (z : Reg loc (Λ \ X)) (s e : Reg loc X) :
    copyVec hX v (glue a z, (s, e)) = if a = blank X ∧ s = blank X then v (glue e z) else 0 := by
  simp [copyVec]

/-- `φ = 𝓡_X v = ∑_e (|0⟩⟨e|_X v) ⊗ |0⟩_{s'} |e⟩_{e'}`. -/
theorem copyVec_eq_sum (hX : X ⊆ Λ) (v : Reg loc Λ → ℂ) :
    copyVec hX v = ∑ e : Reg loc X, tensVec
      (extendId hX (vecMulVec (Pi.single (blank X) 1) (Pi.single e 1)) *ᵥ v)
      (tensVec (Pi.single (blank X) 1) (Pi.single e 1)) := by
  ext ⟨w, s, e'⟩
  obtain ⟨⟨a, z⟩, rfl⟩ := (glueEquiv hX).surjective w
  simp only [glueEquiv_apply, copyVec_apply_glue, Finset.sum_apply, tensVec,
    extendId_mulVec_glue, vecMulVec_apply, Pi.single_apply]
  by_cases ha : a = blank X <;> by_cases hs : s = blank X <;> simp [ha, hs]

/-- `𝓡_X` is an isometry. -/
theorem vnorm_copyVec_eq (hX : X ⊆ Λ) (v : Reg loc Λ → ℂ) :
    vnorm (copyVec hX v) = vnorm v := by
  have h : star (copyVec hX v) ⬝ᵥ copyVec hX v = star v ⬝ᵥ v := by
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply]
    rw [← (glueEquiv hX).sum_comp, ← (glueEquiv hX).sum_comp]
    simp only [Fintype.sum_prod_type, glueEquiv_apply, copyVec_apply_glue]
    conv_rhs => rw [Finset.sum_comm]
    simp [ite_and]
  rw [vnorm_eq_sqrt, vnorm_eq_sqrt, h]

omit [DecidableEq σ] [∀ i, Fintype (loc i)] in
/-- `|00⟩_{s'e'} = |0⟩_{s'} ⊗ |0⟩_{e'}`. -/
theorem blankVec_eq (X : Finset σ) :
    blankVec (loc := loc) X = tensVec (Pi.single (blank X) 1) (Pi.single (blank X) 1) := by
  ext ⟨s, e⟩
  by_cases hs : s = blank X <;> by_cases he : e = blank X <;> simp [blankVec, tensVec, hs, he]

omit [∀ i, Fintype (loc i)] in
/-- `𝓡_X` is linear. -/
theorem copyVec_sub (hX : X ⊆ Λ) (u v : Reg loc Λ → ℂ) :
    copyVec hX (u - v) = copyVec hX u - copyVec hX v := by
  ext w
  simp only [copyVec, Pi.sub_apply]
  split_ifs <;> simp

end Region

/-! ## The setting of Proposition 10.2 -/

section Setting

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] {Λ X Y : Finset σ}
  (hX : X ⊆ Λ) (hY : Y ⊆ Λ) (hXY : Disjoint X Y) (Ω : Reg loc Λ → ℂ)
  (hΩ : star Ω ⬝ᵥ Ω = 1)

/-! ### D10.6 Unit vectors -/

include hΩ in
/-- D10.6. `φ` is a unit vector. -/
theorem vnorm_copyVec : vnorm (copyVec hX Ω) = 1 := by
  rw [vnorm_copyVec_eq, vnorm_eq_one hΩ]

include hΩ in
/-- D10.6. `Ω ⊗ |00⟩` is a unit vector. -/
theorem vnorm_tensVec_blankVec : vnorm (tensVec Ω (blankVec (loc := loc) X)) = 1 := by
  rw [vnorm_tensVec hΩ]
  refine vnorm_eq_one ?_
  simp [dotProduct, blankVec, apply_ite star]

omit [∀ i, Nonempty (loc i)] in
/-- D10.6. `η = Ω ⊗ ∑_x √p_x |x⟩_{s'} |x⟩_{e'}`. -/
theorem restoredVec_eq : restoredVec hX Ω hΩ = tensVec Ω (∑ x,
    ((Real.sqrt ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x) : ℂ)) • tensVec
      (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)
      (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)) := by
  ext ⟨w, s, e⟩
  simp [restoredVec, tensVec, Finset.sum_apply, mul_assoc]

omit [∀ i, Nonempty (loc i)] in
/-- D10.6. `η` is a unit vector. -/
theorem vnorm_restoredVec : vnorm (restoredVec hX Ω hΩ) = 1 := by
  set U := (marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary
  set p := (marg Ω hΩ hX).psd.isHermitian.eigenvalues
  rw [restoredVec_eq, vnorm_tensVec hΩ]
  refine vnorm_eq_one ?_
  have hU : ∀ x x', star (tensVec (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x)
      (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x)) ⬝ᵥ
      tensVec (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x')
      (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x') = if x = x' then 1 else 0 := by
    intro x x'
    rw [star_tensVec_dotProduct]
    have h := sum_star_mul_unitary U x x'
    simp only [dotProduct, Pi.star_apply, h]
    split_ifs <;> simp
  rw [star_sum_smul_dotProduct _ _ hU, ← Complex.ofReal_one,
    ← MState.sum_eigenvalues_eq_one ((pureState Ω hΩ).restrict hX), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hp : 0 ≤ p x := (marg Ω hΩ hX).psd.eigenvalues_nonneg x
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hp]
  rfl

/-! ### D10.7 The restoring and column operators -/

/-- D10.7. `R₀ = ∑_{x sel} p_x^{-1/2} |x⟩⟨0|_{s'} ⊗ Q(|x⟩⟨0|_X ⊗ T₀)` (trivial on `e'`,
`Λ \ S₀`). -/
noncomputable def restoringOp (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) :
    Matrix (Reg loc Λ × (Reg loc X × Reg loc X)) (Reg loc Λ × (Reg loc X × Reg loc X)) ℂ :=
  ∑ x ∈ sel, (((Real.sqrt ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x))⁻¹ : ℝ) : ℂ) •
    (extendId (Finset.union_subset hX hY) (Q * (vecMulVec
        (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)
        (Pi.single (blank X) 1) ⊗ₖ T₀).submatrix (unionEquiv hXY) (unionEquiv hXY)) ⊗ₖ
      (vecMulVec (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)
        (Pi.single (blank X) 1) ⊗ₖ (1 : Matrix (Reg loc X) (Reg loc X) ℂ)))

/-- D10.7. `B₀ = ∑_{x sel, y} p_x^{-1/2} |x⟩⟨0|_{s'} ⊗ |y⟩⟨0|_{e'} ⊗ Q(|x⟩⟨y|_X ⊗ T₀)`, `y` over
the configurations of `X`. -/
noncomputable def columnOp (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) :
    Matrix (Reg loc Λ × (Reg loc X × Reg loc X)) (Reg loc Λ × (Reg loc X × Reg loc X)) ℂ :=
  ∑ x ∈ sel, ∑ y : Reg loc X,
    (((Real.sqrt ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x))⁻¹ : ℝ) : ℂ) •
    (extendId (Finset.union_subset hX hY) (Q * (vecMulVec
        (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)
        (Pi.single y 1) ⊗ₖ T₀).submatrix (unionEquiv hXY) (unionEquiv hXY)) ⊗ₖ
      (vecMulVec (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)
        (Pi.single (blank X) 1) ⊗ₖ vecMulVec (Pi.single y 1) (Pi.single (blank X) 1)))

omit [∀ i, Nonempty (loc i)] in
-- helper
theorem extendId_mul_extendId_vecMulVec (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ)
    (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ) (u w : Reg loc X → ℂ) (b : Reg loc X) :
    extendId (Finset.union_subset hX hY)
        (Q * (vecMulVec u (Pi.single b 1) ⊗ₖ T₀).submatrix (unionEquiv hXY) (unionEquiv hXY)) *
      extendId hX (vecMulVec (Pi.single b 1) w) =
    extendId (Finset.union_subset hX hY)
        (Q * (vecMulVec u w ⊗ₖ T₀).submatrix (unionEquiv hXY) (unionEquiv hXY)) := by
  have h1 : extendId hX (vecMulVec (Pi.single b 1) w) = extendId (Finset.union_subset hX hY)
      ((vecMulVec (Pi.single b (1 : ℂ)) w ⊗ₖ (1 : Matrix (Reg loc Y) (Reg loc Y) ℂ)).submatrix
        (unionEquiv hXY) (unionEquiv hXY)) := by
    rw [extendId_union_kronUnion hX hY hXY, extendId_one, Matrix.mul_one]
  rw [h1, ← extendId_mul, Matrix.mul_assoc, submatrix_mul_equiv, ← mul_kronecker_mul,
    vecMulVec_mul_vecMulVec', Matrix.mul_one]
  simp

omit [∀ i, Nonempty (loc i)] in
-- helper
theorem single_dotProduct_single (b : Reg loc X) : Pi.single b (1 : ℂ) ⬝ᵥ Pi.single b 1 = 1 := by
  simp

/-- D10.7.1–2. `R₀ φ = B₀ (Ω ⊗ |00⟩)`. -/
theorem step_10_7 (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) :
    restoringOp hX hY hXY Ω hΩ sel T₀ Q *ᵥ copyVec hX Ω =
      columnOp hX hY hXY Ω hΩ sel T₀ Q *ᵥ tensVec Ω (blankVec X) := by
  have hb := blankVec_eq (loc := loc) X
  -- D10.7.1: `φ = ∑_e (|0⟩⟨e|_X Ω) ⊗ |0⟩_{s'} |e⟩_{e'}`
  rw [copyVec_eq_sum, hb, restoringOp, columnOp, Matrix.sum_mulVec, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun x _ => ?_
  -- D10.7.2: both sides are `∑_y p_x^{-1/2} Q(|x⟩⟨y|_X ⊗ T₀) Ω ⊗ |x⟩_{s'} |y⟩_{e'}`
  rw [Matrix.mulVec_sum, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mulVec, smul_mulVec, kronecker_mulVec_tensVec, kronecker_mulVec_tensVec,
    kronecker_mulVec_tensVec, kronecker_mulVec_tensVec, mulVec_mulVec,
    extendId_mul_extendId_vecMulVec hX hY hXY, vecMulVec_mulVec', vecMulVec_mulVec', one_mulVec,
    single_dotProduct_single, one_smul, one_smul]

/-- D10.7. `B₀` acts trivially on `Λ \ S₀`. -/
theorem columnOp_support (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ)
    (A : Matrix (Reg loc (Λ \ (X ∪ Y))) (Reg loc (Λ \ (X ∪ Y))) ℂ) :
    Commute (extendId (Finset.sdiff_subset : Λ \ (X ∪ Y) ⊆ Λ) A ⊗ₖ
      (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ))
      (columnOp hX hY hXY Ω hΩ sel T₀ Q) := by
  refine Commute.sum_right _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => ?_
  refine Commute.smul_right ?_ _
  have hc := commute_extendId_extendId (Finset.sdiff_subset : Λ \ (X ∪ Y) ⊆ Λ)
    (Finset.union_subset hX hY) Finset.sdiff_disjoint A
    (Q * (vecMulVec (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
      Matrix _ _ ℂ) s x) (Pi.single y 1) ⊗ₖ T₀).submatrix (unionEquiv hXY) (unionEquiv hXY))
  rw [Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul, hc.eq, Matrix.one_mul,
    Matrix.mul_one]

omit [∀ i, Fintype (loc i)] [∀ i, Nonempty (loc i)] in
-- helper
theorem extendId_kronecker_eq_submatrix {N : Finset σ} (hN : N ⊆ Λ)
    (A : Matrix (Reg loc N) (Reg loc N) ℂ) (B : Matrix (Reg loc X) (Reg loc X) ℂ) :
    extendId hN A ⊗ₖ (B ⊗ₖ (1 : Matrix (Reg loc X) (Reg loc X) ℂ)) =
      ((A ⊗ₖ B) ⊗ₖ (1 : Matrix (Reg loc (Λ \ N) × Reg loc X)
        (Reg loc (Λ \ N) × Reg loc X) ℂ)).submatrix (splitN hN X) (splitN hN X) := by
  ext ⟨w, s, e⟩ ⟨w', s', e'⟩
  simp only [kroneckerMap_apply, submatrix_apply, splitN, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, glueEquiv_symm_apply,
    Equiv.prodProdProdComm_apply, extendId, of_apply, one_apply, Prod.mk.injEq]
  by_cases h1 : restr (S := Λ \ N) Finset.sdiff_subset w = restr Finset.sdiff_subset w' <;>
    by_cases h2 : e = e' <;> simp [h1, h2, mul_comm]

/-- D10.7. `R₀` acts on `S₀ ∪ s'` only. -/
theorem restoringOp_actsOn (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) :
    ActsOn (Finset.union_subset hX hY) X (restoringOp hX hY hXY Ω hΩ sel T₀ Q) := by
  refine ⟨∑ x ∈ sel, (((Real.sqrt ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x))⁻¹ : ℝ) : ℂ) •
    ((Q * (vecMulVec
        (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)
        (Pi.single (blank X) 1) ⊗ₖ T₀).submatrix (unionEquiv hXY) (unionEquiv hXY)) ⊗ₖ
      vecMulVec (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)
        (Pi.single (blank X) 1)), ?_⟩
  rw [restoringOp]
  simp only [extendId_kronecker_eq_submatrix]
  ext v v'
  simp only [Matrix.sum_apply, Matrix.smul_apply, submatrix_apply, kroneckerMap_apply,
    smul_eq_mul, Finset.sum_mul, mul_assoc]

/-! ### D10.8 Norm bounds -/

omit [∀ i, Nonempty (loc i)] in
include hXY in
/-- D10.8.4. Purity of `Ω`: `S(X) + S(S₀) - S(Y) = I(X : Λ \ S₀)`. -/
theorem step_10_8_4 :
    (marg Ω hΩ hX).entropy + (marg Ω hΩ (Finset.union_subset hX hY)).entropy -
      (marg Ω hΩ hY).entropy =
    (pureState Ω hΩ).toSubState.mutualInfo hX (Finset.sdiff_subset : Λ \ (X ∪ Y) ⊆ Λ) := by
  have h1 := MState.regionEntropy_pureState_sdiff Ω hΩ (Finset.union_subset hX hY)
  have h2 := MState.regionEntropy_pureState_sdiff Ω hΩ hY
  have hset : Λ \ Y = X ∪ Λ \ (X ∪ Y) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hi, hiY⟩
      by_cases hiX : i ∈ X
      · exact Or.inl hiX
      · exact Or.inr ⟨hi, fun h => h.elim hiX hiY⟩
    · rintro (hiX | ⟨hi, hiXY⟩)
      · exact ⟨hX hiX, Finset.disjoint_left.1 hXY hiX⟩
      · exact ⟨hi, fun hiY => hiXY (Or.inr hiY)⟩
  rw [SubState.regionEntropy_congr _ hset _ (Finset.union_subset hX Finset.sdiff_subset)] at h2
  rw [SubState.mutualInfo_def]
  change SubState.regionEntropy _ hX + SubState.regionEntropy _ _ -
    SubState.regionEntropy _ hY = _
  linarith

omit [∀ i, Nonempty (loc i)] [∀ i, DecidableEq (loc i)] in
include hXY in
/-- `ρ_X = Tr_Y ρ_{S₀}` in the coordinates `X × Y` of `S₀`. -/
theorem marg_X_eq_traceRight :
    (marg Ω hΩ hX).M = traceRight (((marg Ω hΩ (Finset.union_subset hX hY)).M).submatrix
      (unionEquiv hXY).symm (unionEquiv hXY).symm) := by
  rw [← ptrace_eq_traceRight hXY]
  exact (ptrace_ptrace Finset.subset_union_left (Finset.union_subset hX hY) _).symm

omit [∀ i, Nonempty (loc i)] [∀ i, DecidableEq (loc i)] in
include hXY in
/-- `ρ_Y = Tr_X ρ_{S₀}` in the coordinates `X × Y` of `S₀`. -/
theorem marg_Y_eq_traceLeft :
    (marg Ω hΩ hY).M = traceLeft (((marg Ω hΩ (Finset.union_subset hX hY)).M).submatrix
      (unionEquiv hXY).symm (unionEquiv hXY).symm) := by
  rw [← ptrace_eq_traceLeft hXY]
  exact (ptrace_ptrace Finset.subset_union_right (Finset.union_subset hX hY) _).symm

omit [∀ i, Nonempty (loc i)] [∀ i, Fintype (loc i)] in
-- helper
theorem extendId_le_extendId [∀ i, Finite (loc i)] {N : Finset σ} (hN : N ⊆ Λ)
    {A B : Matrix (Reg loc N) (Reg loc N) ℂ}
    (h : A ≤ B) : extendId hN A ≤ extendId hN B := by
  have he : extendId hN B - extendId hN A = extendId hN (B - A) := by
    rw [sub_eq_iff_eq_add', ← extendId_add]
    congr 1
    abel
  rw [Matrix.le_iff, he]
  exact posSemidef_extendId hN h

omit [∀ i, Nonempty (loc i)] [∀ i, Fintype (loc i)] in
-- helper
theorem extendId_sum {N : Finset σ} (hN : N ⊆ Λ) {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Reg loc N) (Reg loc N) ℂ) :
    extendId hN (∑ i ∈ s, A i) = ∑ i ∈ s, extendId hN (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, extendId_add, ih]

/-- D10.8. `B_Y = ∑_{x sel} p_x^{-1} T₀ ⟨x|Q|x⟩ T₀`, an operator on `Y` (`⟨x|Q|x⟩` the partial
matrix element in the `X` factor of `S₀ = X ∪ Y`). -/
noncomputable def gramY (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) : Matrix (Reg loc Y) (Reg loc Y) ℂ :=
  ∑ x ∈ sel, ((((marg Ω hΩ hX).psd.isHermitian.eigenvalues x)⁻¹ : ℝ) : ℂ) •
    (T₀ * ((ketOne (k := Reg loc Y) (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x))ᴴ *
      Q.submatrix (unionEquiv hXY).symm (unionEquiv hXY).symm *
      ketOne (k := Reg loc Y) (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
        Matrix (Reg loc X) (Reg loc X) ℂ) s x)) * T₀)

omit [∀ i, Nonempty (loc i)] in
-- helper
theorem star_inv_sqrt_mul (p : ℝ) (hp : 0 ≤ p) :
    star (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (((Real.sqrt p)⁻¹ : ℝ) : ℂ) = ((p⁻¹ : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hp]

/-- D10.8.1. `R₀ᴴ R₀ = |0⟩⟨0|_{s'} ⊗ |0⟩⟨0|_X ⊗ B_Y` (identity on `e'` and `Λ \ S₀`). -/
theorem step_10_8_1_R (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hTh : T₀ᴴ = T₀) :
    (restoringOp hX hY hXY Ω hΩ sel T₀ Q)ᴴ * restoringOp hX hY hXY Ω hΩ sel T₀ Q =
      (extendId hX (vecMulVec (Pi.single (blank X) 1) (Pi.single (blank X) 1)) *
        extendId hY (gramY hX hXY Ω hΩ sel T₀ Q)) ⊗ₖ
      (vecMulVec (Pi.single (blank X) 1) (Pi.single (blank X) 1) ⊗ₖ
        (1 : Matrix (Reg loc X) (Reg loc X) ℂ)) := by
  set U := (marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary
  set p := (marg Ω hΩ hX).psd.isHermitian.eigenvalues
  have hp : ∀ x, 0 ≤ p x := (marg Ω hΩ hX).psd.eigenvalues_nonneg
  rw [restoringOp]
  simp only [← smul_kronecker]
  rw [gram_sum_kronecker]
  · congr 1
    rw [← extendId_union_kronUnion hX hY hXY, gramY, kronecker_sum, submatrix_sum, extendId_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    -- D10.8.1: `Q² = Q`, `⟨x|x⟩ = 1`
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_inv_sqrt_mul _ (hp x),
      ← extendId_conjTranspose, ← extendId_mul, conj_proj_submatrix hQh hQQ,
      vecMulVec_kronecker_conj, hTh, kronecker_smul, submatrix_smul', extendId_smul]
  · intro x _ x' _
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, conjTranspose_vecMulVec, star_single_one,
      vecMulVec_mul_vecMulVec', conjTranspose_one, Matrix.mul_one, dotProduct_col_unitary]
    split_ifs <;> simp

/-- D10.8.1. `B₀ᴴ B₀ = |00⟩⟨00|_{s'e'} ⊗ I_X ⊗ B_Y` (identity on `Λ \ S₀`). -/
theorem step_10_8_1_B (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hTh : T₀ᴴ = T₀) :
    (columnOp hX hY hXY Ω hΩ sel T₀ Q)ᴴ * columnOp hX hY hXY Ω hΩ sel T₀ Q =
      extendId hY (gramY hX hXY Ω hΩ sel T₀ Q) ⊗ₖ
      (vecMulVec (Pi.single (blank X) 1) (Pi.single (blank X) 1) ⊗ₖ
        vecMulVec (Pi.single (blank X) 1) (Pi.single (blank X) 1)) := by
  set U := (marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary
  set p := (marg Ω hΩ hX).psd.isHermitian.eigenvalues
  have hp : ∀ x, 0 ≤ p x := (marg Ω hΩ hX).psd.eigenvalues_nonneg
  have hone : ∑ y : Reg loc X, vecMulVec (Pi.single y (1 : ℂ)) (Pi.single y 1) = 1 := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply, h, one_apply]
  rw [columnOp, ← Finset.sum_product']
  simp only [← smul_kronecker]
  rw [gram_sum_kronecker]
  · congr 1
    rw [Finset.sum_product]
    have h1 : extendId hY (gramY hX hXY Ω hΩ sel T₀ Q) = extendId (Finset.union_subset hX hY)
        (((1 : Matrix (Reg loc X) (Reg loc X) ℂ) ⊗ₖ gramY hX hXY Ω hΩ sel T₀ Q).submatrix
          (unionEquiv hXY) (unionEquiv hXY)) := by
      rw [extendId_union_kronUnion hX hY hXY, extendId_one, Matrix.one_mul]
    rw [h1, gramY, kronecker_sum, submatrix_sum, extendId_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    -- D10.8.1: `Q² = Q`, `∑_y |y⟩⟨y| = I_X`
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← extendId_conjTranspose, ← extendId_mul, conj_proj_submatrix hQh hQQ,
      vecMulVec_kronecker_conj, hTh]
    rw [← Finset.smul_sum, ← extendId_sum, ← submatrix_sum, ← sum_kronecker, hone,
      kronecker_smul, submatrix_smul', extendId_smul]
    congr 1
    rw [mul_comm]
    exact star_inv_sqrt_mul _ (hp x)
  · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _
    rw [conjTranspose_kronecker, ← mul_kronecker_mul]
    simp only [conjTranspose_vecMulVec, star_single_one]
    rw [vecMulVec_mul_vecMulVec', vecMulVec_mul_vecMulVec', dotProduct_col_unitary,
      single_dotProduct_single']
    by_cases hx : x = x' <;> by_cases hy : y = y' <;> simp [hx, hy]

/-- D10.8. `‖R₀‖, ‖B₀‖ ≤ e^{(a₁+a₂+a₃)/2}` under the spectral inequalities of D10.8.2:
`p_x^{-1} ≤ e^{a₁}` on the selection, `Q ≤ e^{a₂} ρ_{S₀}`, `T₀ ρ_Y T₀ ≤ e^{a₃} T₀`
(`Q`, `T₀` projections). With `a₁ + a₂ + a₃ = 𝓘 + 3w` (D10.8.4) this is `M₀`. -/
theorem step_10_8 (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) (a₁ a₂ a₃ : ℝ)
    (h1 : ∀ x ∈ sel, 0 < (marg Ω hΩ hX).psd.isHermitian.eigenvalues x ∧
      ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x)⁻¹ ≤ Real.exp a₁)
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hQ : Q ≤ (Real.exp a₂ : ℂ) • (marg Ω hΩ (Finset.union_subset hX hY)).M)
    (hTh : T₀ᴴ = T₀) (hTT : T₀ * T₀ = T₀)
    (hT : T₀ * (marg Ω hΩ hY).M * T₀ ≤ (Real.exp a₃ : ℂ) • T₀) :
    ‖restoringOp hX hY hXY Ω hΩ sel T₀ Q‖ ≤ Real.exp ((a₁ + a₂ + a₃) / 2) ∧
      ‖columnOp hX hY hXY Ω hΩ sel T₀ Q‖ ≤ Real.exp ((a₁ + a₂ + a₃) / 2) := by
  set e := (unionEquiv (loc := loc) hXY).symm
  have hc : 0 ≤ Real.exp (a₁ + a₂ + a₃) := (Real.exp_pos _).le
  -- D10.8.2–3, in the coordinates `X × Y` of `S₀`
  have hB : gramY hX hXY Ω hΩ sel T₀ Q ≤ (Real.exp (a₁ + a₂ + a₃) : ℂ) • T₀ := by
    have hQ' : Q.submatrix e e ≤ (Real.exp a₂ : ℂ) •
        ((marg Ω hΩ (Finset.union_subset hX hY)).M).submatrix e e := by
      have := submatrix_le_submatrix hQ e
      rwa [submatrix_smul'] at this
    have hT' : T₀ * traceLeft (((marg Ω hΩ (Finset.union_subset hX hY)).M).submatrix e e) * T₀ ≤
        (Real.exp a₃ : ℂ) • T₀ := by
      rw [← marg_Y_eq_traceLeft hX hY hXY Ω hΩ]
      exact hT
    exact step_10_8_3 (marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary
      (marg Ω hΩ hX).psd.isHermitian.eigenvalues sel _ (Q.submatrix e e) T₀ a₁ a₂ a₃
      ((marg Ω hΩ (Finset.union_subset hX hY)).psd.submatrix e) h1
      (by rw [conjTranspose_submatrix, hQh]) (by rw [submatrix_mul_equiv, hQQ]) hQ' hTh hT'
  have hB1 : gramY hX hXY Ω hΩ sel T₀ Q ≤ (Real.exp (a₁ + a₂ + a₃) : ℂ) • 1 :=
    hB.trans (smul_le_smul_of_nonneg hc (le_one_of_proj ⟨hTh, hTT⟩))
  have hE := proj_vecMulVec_single (blank (loc := loc) X)
  have h1p : (1 : Matrix (Reg loc X) (Reg loc X) ℂ)ᴴ = 1 ∧
      (1 : Matrix (Reg loc X) (Reg loc X) ℂ) * 1 = 1 := ⟨conjTranspose_one, Matrix.mul_one 1⟩
  -- D10.8.5: `‖R‖² = ‖Rᴴ R‖`
  rw [Real.exp_half]
  refine ⟨norm_le_sqrt_of_gram_le hc ?_, norm_le_sqrt_of_gram_le hc ?_⟩
  · rw [step_10_8_1_R hX hY hXY Ω hΩ sel T₀ Q hQh hQQ hTh, ← extendId_union_kronUnion hX hY hXY]
    refine kronecker_le_smul_one hc ?_ (proj_kronecker hE h1p).1 (proj_kronecker hE h1p).2
    have hk : vecMulVec (Pi.single (blank X) (1 : ℂ) : Reg loc X → ℂ)
        (Pi.single (blank X) (1 : ℂ) : Reg loc X → ℂ) ⊗ₖ
        gramY hX hXY Ω hΩ sel T₀ Q ≤ (Real.exp (a₁ + a₂ + a₃) : ℂ) • 1 := by
      refine (kronecker_le_kronecker_left (posSemidef_of_proj hE.1 hE.2) hB1).trans ?_
      rw [kronecker_smul]
      exact smul_le_smul_of_nonneg hc (le_one_of_proj (proj_kronecker hE ⟨conjTranspose_one,
        Matrix.mul_one 1⟩))
    refine (extendId_le_extendId _ (submatrix_le_submatrix hk _)).trans_eq ?_
    rw [submatrix_smul', submatrix_one_equiv, extendId_smul, extendId_one]
  · rw [step_10_8_1_B hX hY hXY Ω hΩ sel T₀ Q hQh hQQ hTh]
    refine kronecker_le_smul_one hc ?_ (proj_kronecker hE hE).1 (proj_kronecker hE hE).2
    refine (extendId_le_extendId hY hB1).trans_eq ?_
    rw [extendId_smul, extendId_one]

/-! ### D10.9 The adjoint identity -/

omit [∀ i, Nonempty (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Fintype (loc i)] in
-- helper
theorem specProj_apply {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (sel : Finset n) (e b : n) :
    specProj hA sel e b = ∑ x ∈ sel, (hA.eigenvectorUnitary : Matrix n n ℂ) e x *
      star ((hA.eigenvectorUnitary : Matrix n n ℂ) b x) := by
  simp [specProj, mul_apply, diagonal, star_apply]
omit [∀ i, Nonempty (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Fintype (loc i)] in
-- helper
theorem specProj_proj {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (sel : Finset n) :
    (specProj hA sel)ᴴ = specProj hA sel ∧ specProj hA sel * specProj hA sel = specProj hA sel := by
  set D : Matrix n n ℂ := diagonal fun j => if j ∈ sel then (1 : ℂ) else 0 with hD
  have hd : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    funext j
    by_cases h : j ∈ sel <;> simp [h]
  have hDD : D * D = D := by
    rw [hD, diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j ∈ sel <;> simp [h]
  refine ⟨?_, ?_⟩
  · rw [specProj, ← hD, conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose, star_star,
      hd, ← star_eq_conjTranspose, Matrix.mul_assoc]
  · simp only [specProj, ← hD, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix n n ℂ)),
      Unitary.coe_star_mul_self, Matrix.one_mul, ← Matrix.mul_assoc D D, hDD]

omit [∀ i, Nonempty (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Fintype (loc i)] in
-- helper
theorem vnorm_proj_mulVec_le {n : Type*} [Fintype n] {P : Matrix n n ℂ}
    (hP : Pᴴ = P ∧ P * P = P) (v : n → ℂ) : vnorm (P *ᵥ v) ≤ vnorm v := by
  classical
  have h : ‖P‖ ≤ 1 := by
    have := norm_le_sqrt_of_gram_le zero_le_one (c := 1) (by
      rw [hP.1, hP.2, Complex.ofReal_one, one_smul]
      exact le_one_of_proj hP)
    rwa [Real.sqrt_one] at this
  exact (vnorm_mulVec_le P v).trans (mul_le_of_le_one_left (vnorm_nonneg v) h)

omit [∀ i, Nonempty (loc i)] in
-- helper
theorem proj_extendId {N : Finset σ} (hN : N ⊆ Λ) {P : Matrix (Reg loc N) (Reg loc N) ℂ}
    (hP : Pᴴ = P ∧ P * P = P) :
    (extendId hN P)ᴴ = extendId hN P ∧ extendId hN P * extendId hN P = extendId hN P := by
  rw [← extendId_conjTranspose, ← extendId_mul, hP.1, hP.2]
  exact ⟨rfl, rfl⟩

/-- D10.9.1. `R₀ᴴ (L'ᴴ ⊗ 1) η = 𝓡_X (P_X ⊗ T₀) Q L'ᴴ Ω`, exactly. -/
theorem step_10_9_1 (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ)
    (hsel : ∀ x ∈ sel, 0 < (marg Ω hΩ hX).psd.isHermitian.eigenvalues x)
    (hTh : T₀ᴴ = T₀) (hQh : Qᴴ = Q) (L' : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :
    (restoringOp hX hY hXY Ω hΩ sel T₀ Q)ᴴ *ᵥ ((L'ᴴ ⊗ₖ
      (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ restoredVec hX Ω hΩ) =
    copyVec hX ((extendId hX (specProj (marg Ω hΩ hX).psd.isHermitian sel) * extendId hY T₀ *
      extendId (Finset.union_subset hX hY) Q) *ᵥ (L'ᴴ *ᵥ Ω)) := by
  set U := (marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary
  set p := (marg Ω hΩ hX).psd.isHermitian.eigenvalues
  set v := (extendId hY T₀ * extendId (Finset.union_subset hX hY) Q) *ᵥ (L'ᴴ *ᵥ Ω)
  have hp : ∀ x, 0 ≤ p x := (marg Ω hΩ hX).psd.eigenvalues_nonneg
  -- D10.9.1: `(L')ᴴ η = ((L')ᴴ Ω) ⊗ ∑_x √p_x |x⟩_{s'} |x⟩_{e'}`
  rw [restoredVec_eq, kronecker_mulVec_tensVec, one_mulVec, restoringOp, conjTranspose_sum,
    Matrix.sum_mulVec]
  have hL : ∑ x ∈ sel, tensVec (extendId hX (vecMulVec (Pi.single (blank (loc := loc) X) 1)
      (star fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x)) *ᵥ v)
      (tensVec (Pi.single (blank (loc := loc) X) 1)
        (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x)) =
      copyVec hX (extendId hX (specProj (marg Ω hΩ hX).psd.isHermitian sel) *ᵥ v) := by
    -- `|0⟩_{s'} ∑_{x' sel} |x'⟩_{e'} ⊗ |0⟩_X⟨x'|_X v` is `𝓡_X P_X v`
    ext ⟨w, s, e⟩
    obtain ⟨⟨a, z⟩, rfl⟩ := (glueEquiv hX).surjective w
    simp only [glueEquiv_apply, copyVec_apply_glue, Finset.sum_apply, tensVec,
      extendId_mulVec_glue, vecMulVec_apply, specProj_apply, Pi.star_apply]
    by_cases ha : a = blank X <;> by_cases hs : s = blank X <;> simp only [ha, hs,
      Pi.single_apply, if_true, if_false, and_true, and_false, one_mul, zero_mul,
      mul_zero, Finset.sum_const_zero]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => by ring
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← hL]
  refine Finset.sum_congr rfl fun x hx => ?_
  -- contracting `⟨x|_{s'}` picks `x' = x`; `p_x^{-1/2} √p_x = 1`
  have hc : ((((Real.sqrt (p x))⁻¹ : ℝ) : ℂ)) * (Real.sqrt (p x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.2 (hsel x hx)).ne', Complex.ofReal_one]
  have hs : (vecMulVec (Pi.single (blank (loc := loc) X) 1)
      (star fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x) ⊗ₖ
      (1 : Matrix (Reg loc X) (Reg loc X) ℂ)) *ᵥ ∑ x', ((Real.sqrt (p x') : ℂ)) •
        tensVec (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x')
          (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x') =
      (Real.sqrt (p x) : ℂ) • tensVec (Pi.single (blank (loc := loc) X) 1)
        (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x) := by
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, kronecker_mulVec_tensVec, vecMulVec_mulVec',
      one_mulVec, dotProduct_col_unitary, ite_smul, one_smul, zero_smul, tensVec_ite_left,
      smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hA : (extendId (Finset.union_subset hX hY) (Q * (vecMulVec
      (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x) (Pi.single (blank (loc := loc) X) 1) ⊗ₖ
        T₀).submatrix (unionEquiv hXY) (unionEquiv hXY)))ᴴ =
      extendId hX (vecMulVec (Pi.single (blank (loc := loc) X) 1)
      (star fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x)) * extendId hY T₀ *
      extendId (Finset.union_subset hX hY) Q := by
    rw [← extendId_conjTranspose, conjTranspose_mul, conjTranspose_submatrix, hQh,
      conjTranspose_kronecker, conjTranspose_vecMulVec, star_single_one, hTh, extendId_mul,
      extendId_union_kronUnion hX hY hXY]
  rw [conjTranspose_smul, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_vecMulVec, star_single_one, smul_mulVec, kronecker_mulVec_tensVec, hs, hA,
    tensVec_smul_right, smul_smul, Complex.star_def, Complex.conj_ofReal, hc, one_smul,
    Matrix.mul_assoc, ← mulVec_mulVec]

include hΩ in
/-- D10.9.2–3. `‖R₀ᴴ (L'ᴴ ⊗ 1) η - φ‖ ≤ ‖(1-P_X)Ω‖ + ‖(1-T₀)Ω‖ + ‖(1-Q)Ω‖ + ‖L'ᴴΩ - Ω‖`. -/
theorem step_10_9 (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ)
    (hsel : ∀ x ∈ sel, 0 < (marg Ω hΩ hX).psd.isHermitian.eigenvalues x)
    (hTh : T₀ᴴ = T₀) (hTT : T₀ * T₀ = T₀) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (L' : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :
    vnorm ((restoringOp hX hY hXY Ω hΩ sel T₀ Q)ᴴ *ᵥ ((L'ᴴ ⊗ₖ
      (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ restoredVec hX Ω hΩ) -
        copyVec hX Ω) ≤
      vnorm ((1 - extendId hX (specProj (marg Ω hΩ hX).psd.isHermitian sel)) *ᵥ Ω) +
      vnorm ((1 - extendId hY T₀) *ᵥ Ω) +
      vnorm ((1 - extendId (Finset.union_subset hX hY) Q) *ᵥ Ω) + vnorm (L'ᴴ *ᵥ Ω - Ω) := by
  set P := extendId hX (specProj (marg Ω hΩ hX).psd.isHermitian sel)
  set T := extendId hY T₀
  set Q' := extendId (Finset.union_subset hX hY) Q
  have hP := proj_extendId hX (specProj_proj (marg Ω hΩ hX).psd.isHermitian sel)
  have hT := proj_extendId hY ⟨hTh, hTT⟩
  have hQ := proj_extendId (Finset.union_subset hX hY) ⟨hQh, hQQ⟩
  -- D10.9.2: `φ = 𝓡_X Ω`, `𝓡_X` an isometry
  rw [step_10_9_1 hX hY hXY Ω hΩ sel T₀ Q hsel hTh hQh L', ← copyVec_sub, vnorm_copyVec_eq]
  -- D10.9.3: telescope `P T Q ψ - Ω = P T Q (ψ - Ω) + P T (Q Ω - Ω) + P (T Ω - Ω) + (P Ω - Ω)`
  have he : (P * T * Q') *ᵥ (L'ᴴ *ᵥ Ω) - Ω = P *ᵥ (T *ᵥ (Q' *ᵥ (L'ᴴ *ᵥ Ω - Ω))) +
      P *ᵥ (T *ᵥ (Q' *ᵥ Ω - Ω)) + P *ᵥ (T *ᵥ Ω - Ω) + (P *ᵥ Ω - Ω) := by
    simp only [← mulVec_mulVec, mulVec_sub]
    abel
  have h1 : ∀ (M : Matrix (Reg loc Λ) (Reg loc Λ) ℂ), vnorm ((1 - M) *ᵥ Ω) = vnorm (M *ᵥ Ω - Ω) :=
    fun M => by rw [sub_mulVec, one_mulVec, vnorm_sub_rev]
  rw [he, h1, h1, h1]
  have hA : vnorm (P *ᵥ (T *ᵥ (Q' *ᵥ (L'ᴴ *ᵥ Ω - Ω)))) ≤ vnorm (L'ᴴ *ᵥ Ω - Ω) :=
    (vnorm_proj_mulVec_le hP _).trans ((vnorm_proj_mulVec_le hT _).trans
      (vnorm_proj_mulVec_le hQ _))
  have hB : vnorm (P *ᵥ (T *ᵥ (Q' *ᵥ Ω - Ω))) ≤ vnorm (Q' *ᵥ Ω - Ω) :=
    (vnorm_proj_mulVec_le hP _).trans (vnorm_proj_mulVec_le hT _)
  have hC : vnorm (P *ᵥ (T *ᵥ Ω - Ω)) ≤ vnorm (T *ᵥ Ω - Ω) := vnorm_proj_mulVec_le hP _
  have h3 := vnorm_add_le (P *ᵥ (T *ᵥ (Q' *ᵥ (L'ᴴ *ᵥ Ω - Ω))) + P *ᵥ (T *ᵥ (Q' *ᵥ Ω - Ω)) +
    P *ᵥ (T *ᵥ Ω - Ω)) (P *ᵥ Ω - Ω)
  have h4 := vnorm_add_le (P *ᵥ (T *ᵥ (Q' *ᵥ (L'ᴴ *ᵥ Ω - Ω))) + P *ᵥ (T *ᵥ (Q' *ᵥ Ω - Ω)))
    (P *ᵥ (T *ᵥ Ω - Ω))
  have h5 := vnorm_add_le (P *ᵥ (T *ᵥ (Q' *ᵥ (L'ᴴ *ᵥ Ω - Ω)))) (P *ᵥ (T *ᵥ (Q' *ᵥ Ω - Ω)))
  linarith

/-! ### D10.10 The ground component -/

/-- D10.7.2. `B₀ (Ω ⊗ |00⟩) = ∑_{x sel, y} p_x^{-1/2} Q(|x⟩⟨y|_X ⊗ T₀)Ω ⊗ |x⟩_{s'} |y⟩_{e'}`. -/
theorem columnOp_mulVec (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ) :
    columnOp hX hY hXY Ω hΩ sel T₀ Q *ᵥ tensVec Ω (blankVec X) = ∑ x ∈ sel, ∑ y : Reg loc X,
      (((Real.sqrt ((marg Ω hΩ hX).psd.isHermitian.eigenvalues x))⁻¹ : ℝ) : ℂ) •
      tensVec (extendId (Finset.union_subset hX hY) (Q * (vecMulVec
        (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
          Matrix (Reg loc X) (Reg loc X) ℂ) s x) (Pi.single y 1) ⊗ₖ T₀).submatrix
            (unionEquiv hXY) (unionEquiv hXY)) *ᵥ Ω)
        (tensVec (fun s => ((marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary :
          Matrix (Reg loc X) (Reg loc X) ℂ) s x) (Pi.single y 1)) := by
  rw [blankVec_eq, columnOp, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mulVec, kronecker_mulVec_tensVec, kronecker_mulVec_tensVec, vecMulVec_mulVec',
    vecMulVec_mulVec', single_dotProduct_single, one_smul, one_smul]

/-- D10.10. The ground component of `R₀ φ` has norm at most `1`: `‖(P_Ω ⊗ I_{s'e'}) R₀ φ‖ ≤ 1`,
for projections `Q` (commuting with `ρ_{S₀}`) and `T₀`. -/
theorem step_10_10 (sel : Finset (Reg loc X)) (T₀ : Matrix (Reg loc Y) (Reg loc Y) ℂ)
    (Q : Matrix (Reg loc (X ∪ Y)) (Reg loc (X ∪ Y)) ℂ)
    (_hsel : ∀ x ∈ sel, 0 < (marg Ω hΩ hX).psd.isHermitian.eigenvalues x)
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hQρ : Commute Q (marg Ω hΩ (Finset.union_subset hX hY)).M)
    (hTh : T₀ᴴ = T₀) (hTT : T₀ * T₀ = T₀) :
    vnorm ((vecMulVec Ω (star Ω) ⊗ₖ
      (1 : Matrix (Reg loc X × Reg loc X) (Reg loc X × Reg loc X) ℂ)) *ᵥ
        (restoringOp hX hY hXY Ω hΩ sel T₀ Q *ᵥ copyVec hX Ω)) ≤ 1 := by
  rw [step_10_7, columnOp_mulVec, Matrix.mulVec_sum]
  set U := (marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary with hU
  set p := (marg Ω hΩ hX).psd.isHermitian.eigenvalues with hpdef
  have hp : ∀ x, 0 ≤ p x := (marg Ω hΩ hX).psd.eigenvalues_nonneg
  set e := (unionEquiv (loc := loc) hXY).symm with he
  set ρ := (marg Ω hΩ (Finset.union_subset hX hY)).M with hρdef
  set ρ' := ρ.submatrix e e with hρ'
  set Q' := Q.submatrix e e with hQ'
  set T := (1 : Matrix (Reg loc X) (Reg loc X) ℂ) ⊗ₖ T₀ with hTdef
  set M := traceRight (T * (Q' * ρ' * Q') * T) with hM
  set mt := star (U : Matrix (Reg loc X) (Reg loc X) ℂ) * M * U with hmt
  have hT : Tᴴ = T ∧ T * T = T := proj_kronecker ⟨conjTranspose_one, Matrix.mul_one 1⟩ ⟨hTh, hTT⟩
  have hcyc := traceRight_one_kronecker_mul_comm (m := Reg loc X) T₀
  have hQ'h : Q'ᴴ = Q' := by rw [hQ', conjTranspose_submatrix, hQh]
  have hQ'Q' : Q' * Q' = Q' := by rw [hQ', submatrix_mul_equiv, hQQ]
  have hQ'ρ' : Q' * ρ' = ρ' * Q' := by
    rw [hQ', hρ', submatrix_mul_equiv, submatrix_mul_equiv, hQρ.eq]
  have hρ'psd : ρ'.PosSemidef := (marg Ω hΩ (Finset.union_subset hX hY)).psd.submatrix e
  -- D10.10.2: `0 ≤ M_X ≤ ρ_X`
  have hMpsd : M.PosSemidef := by
    refine Matrix.PosSemidef.traceRight ?_
    have := hρ'psd.conjTranspose_mul_mul_same (Q' * T)
    rw [conjTranspose_mul, hT.1, hQ'h] at this
    simpa only [Matrix.mul_assoc] using this
  have hMle : M ≤ (marg Ω hΩ hX).M := by
    rw [marg_X_eq_traceRight hX hY hXY Ω hΩ]
    exact traceRight_conj_le hρ'psd hQ'h hQ'Q' hQ'ρ' hTh hTT
  have hdiag : star (U : Matrix (Reg loc X) (Reg loc X) ℂ) * (marg Ω hΩ hX).M * U =
      diagonal (fun x => (p x : ℂ)) := by
    have := (marg Ω hΩ hX).psd.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_star_apply] at this
  have hmtpsd : mt.PosSemidef := by
    have := hMpsd.conjTranspose_mul_mul_same (U : Matrix (Reg loc X) (Reg loc X) ℂ)
    rwa [← star_eq_conjTranspose] at this
  have hmtle : mt ≤ diagonal (fun x => (p x : ℂ)) := by
    have := conj_le_conj hMle (U : Matrix (Reg loc X) (Reg loc X) ℂ)
    rwa [← star_eq_conjTranspose, hdiag] at this
  -- D10.10.1: `⟨Ω|Q(|x⟩⟨y|_X ⊗ T₀)|Ω⟩ = Tr[(|x⟩⟨y| ⊗ T₀) ρ Q] = (M_X)_{yx}`
  have hcoef : ∀ x y, star Ω ⬝ᵥ (extendId (Finset.union_subset hX hY) (Q * (vecMulVec
      (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x) (Pi.single y 1) ⊗ₖ T₀).submatrix
        (unionEquiv hXY) (unionEquiv hXY)) *ᵥ Ω) =
      ((U : Matrix (Reg loc X) (Reg loc X) ℂ) *ᵥ fun z => mt z x) y := by
    intro x y
    set V := vecMulVec (fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x)
      (Pi.single y (1 : ℂ)) with hV
    have hK : V ⊗ₖ T₀ = (V ⊗ₖ (1 : Matrix (Reg loc Y) (Reg loc Y) ℂ)) * T := by
      rw [hTdef, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    have hNQ : Q' * ρ' * Q' = ρ' * Q' := by rw [hQ'ρ', Matrix.mul_assoc, hQ'Q']
    have hTM : traceRight (T * ρ' * Q') = M := by
      calc traceRight (T * ρ' * Q') = traceRight (T * (T * (Q' * ρ' * Q'))) := by
            rw [hNQ, ← Matrix.mul_assoc, hT.2, Matrix.mul_assoc]
        _ = M := by rw [hM, hTdef, hcyc]
    have hUM : ((U : Matrix (Reg loc X) (Reg loc X) ℂ) *ᵥ fun z => mt z x) =
        M *ᵥ fun s => (U : Matrix (Reg loc X) (Reg loc X) ℂ) s x := by
      have hUU : (U : Matrix (Reg loc X) (Reg loc X) ℂ) * star (U : Matrix _ _ ℂ) = 1 :=
        Unitary.mul_star_self_of_mem U.2
      have h : (U : Matrix (Reg loc X) (Reg loc X) ℂ) * mt = M * U := by
        rw [hmt, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
      ext i
      have := congrFun (congrFun h i) x
      simpa [mul_apply, mulVec, dotProduct] using this
    rw [dotProduct_extendId_mulVec, hUM]
    change (ρ * (Q * _)).trace = _
    rw [mul_submatrix_equiv' Q, mul_submatrix_equiv' ρ, trace_submatrix, ← hQ', ← hρ', hK]
    calc (ρ' * (Q' * ((V ⊗ₖ (1 : Matrix (Reg loc Y) (Reg loc Y) ℂ)) * T))).trace
        = ((T * ρ' * Q') * (V ⊗ₖ (1 : Matrix (Reg loc Y) (Reg loc Y) ℂ))).trace := by
          rw [← Matrix.mul_assoc Q', ← Matrix.mul_assoc ρ', Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = (traceRight (T * ρ' * Q') * V).trace := trace_mul_kron_one_right _ _
      _ = _ := by rw [hTM, hV, mul_vecMulVec, trace_vecMulVec, dotProduct_single_one]
  -- D10.10.1: `P_Ω R₀ φ = Ω ⊗ ∑_{x sel, y} c_{xy} |x⟩_{s'} |y⟩_{e'}`
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, kronecker_mulVec_tensVec, vecMulVec_mulVec',
    one_mulVec, tensVec_smul_left, smul_smul, hcoef]
  rw [sum_sum_smul_tensVec, vnorm_tensVec hΩ, vnorm_eq_sqrt, star_sum_sum_smul_dotProduct]
  swap
  · intro x y x' y'
    rw [star_tensVec_dotProduct, dotProduct_col_unitary, star_single_one,
      single_dotProduct_single']
    by_cases hx : x = x' <;> by_cases hy : y = y' <;> simp [hx, hy]
  -- D10.10.4: `‖P_Ω R₀ φ‖² = ∑_{x sel, y} |(M_X)_{yx}|²/p_x ≤ Tr(M_X ρ_X⁺ M_X) ≤ Tr M_X ≤ 1`
  have hcol : ∀ x, ∑ y, star (((U : Matrix (Reg loc X) (Reg loc X) ℂ) *ᵥ fun z => mt z x) y) *
      ((U : Matrix (Reg loc X) (Reg loc X) ℂ) *ᵥ fun z => mt z x) y =
      ∑ z, star (mt z x) * mt z x := fun x => star_unitary_mulVec_dotProduct U _
  have hterm : ∀ x, ∑ y, star ((((Real.sqrt (p x))⁻¹ : ℝ) : ℂ) *
      ((U : Matrix (Reg loc X) (Reg loc X) ℂ) *ᵥ fun z => mt z x) y) *
      ((((Real.sqrt (p x))⁻¹ : ℝ) : ℂ) *
        ((U : Matrix (Reg loc X) (Reg loc X) ℂ) *ᵥ fun z => mt z x) y) =
      (((p x)⁻¹ : ℝ) : ℂ) * ∑ z, star (mt z x) * mt z x := fun x => by
    rw [← hcol, Finset.mul_sum, ← star_inv_sqrt_mul _ (hp x)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [star_mul']
    ring
  simp only [hterm]
  have h0 : ∀ x, 0 ≤ (((p x)⁻¹ : ℝ) : ℂ) * ∑ z, star (mt z x) * mt z x := fun x =>
    mul_nonneg (by exact_mod_cast inv_nonneg.2 (hp x))
      (Finset.sum_nonneg fun z _ => star_mul_self_nonneg _)
  have htr : mt.trace ≤ 1 := by
    have h1 : mt.trace = M.trace := by
      rw [hmt, Matrix.trace_mul_cycle, Unitary.mul_star_self_of_mem U.2, Matrix.one_mul]
    have h2 : M.trace ≤ (marg Ω hΩ hX).M.trace := by
      have := (Matrix.le_iff.mp hMle).trace_nonneg
      rwa [trace_sub, sub_nonneg] at this
    rw [h1]
    exact h2.trans_eq ((pureState Ω hΩ).restrict hX).trace_eq_one
  have hle : ∑ x ∈ sel, (((p x)⁻¹ : ℝ) : ℂ) * ∑ z, star (mt z x) * mt z x ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => h0 x).trans
      ((sum_inv_mul_sum_star_mul_le_trace hmtpsd hp hmtle).trans htr)
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by simpa using (Complex.le_def.1 hle).1)

end Setting


end AreaLaw

