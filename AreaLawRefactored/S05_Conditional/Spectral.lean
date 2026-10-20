import AreaLawRefactored.S05_Conditional.Defs

/-!
# §5 D5.1: spectral powers, support, Schmidt mirroring

The matrix API of `bracketPow` (`ρ^{[z]}`) and `hatPow` (`ρ̂^z`) used by Lemmas 5.1–5.3, and the
digest-only facts (F1) and (F2) of D5.1 for the marginals `marg θ hD` of a vector `θ`.
-/

namespace AreaLaw

open Arealaw Matrix
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Spectral functions in a diagonalization -/

section SpecFun

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- An intertwiner of two diagonalized matrices intertwines every function of them. -/
theorem Conditional.diagonal_intertwine {U U' : Matrix m m ℂ} {W W' : Matrix n n ℂ}
    (hU : U' * U = 1) (hU' : U * U' = 1) (hW : W' * W = 1) (hW' : W * W' = 1)
    {a : m → ℝ} {b : n → ℝ} (V : Matrix m n ℂ)
    (hV : U * diagonal (fun i ↦ (a i : ℂ)) * U' * V = V * (W * diagonal (fun j ↦ (b j : ℂ)) * W'))
    (g : ℝ → ℂ) :
    U * diagonal (fun i ↦ g (a i)) * U' * V = V * (W * diagonal (fun j ↦ g (b j)) * W') := by
  set K := U' * V * W
  have hK : V = U * K * W' := by
    simp only [K, ← Matrix.mul_assoc, hU', Matrix.one_mul]
    simp only [Matrix.mul_assoc, hW', Matrix.mul_one]
  have hdK : diagonal (fun i ↦ (a i : ℂ)) * K = K * diagonal (fun j ↦ (b j : ℂ)) := by
    have e1 (X : Matrix m n ℂ) : U' * (U * X) = X := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    have e2 (X : Matrix n n ℂ) : W' * (W * X) = X := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
    have h := congrArg (fun T ↦ U' * T * W) hV
    simp only [hK, Matrix.mul_assoc] at h
    simpa only [e1, e2, ← Matrix.mul_assoc K W' W, hW, Matrix.mul_one, Matrix.mul_assoc] using h
  have hg : diagonal (fun i ↦ g (a i)) * K = K * diagonal (fun j ↦ g (b j)) := by
    ext i j
    have h := congrFun (congrFun hdK i) j
    simp only [diagonal_mul, mul_diagonal] at h ⊢
    by_cases hab : a i = b j
    · rw [hab, mul_comm]
    · have : K i j = 0 := (mul_eq_zero.1 (show ((a i : ℂ) - b j) * K i j = 0 by
        linear_combination h)).resolve_left (by simpa [sub_eq_zero] using hab)
      simp [this]
  rw [hK]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc U' U, hU, ← Matrix.mul_assoc W' W, hW, Matrix.one_mul]
  simp only [← Matrix.mul_assoc, hg]

/-- `g(ρ) = U diag(g ∘ λ) U*` for a Hermitian `ρ` and `g : ℝ → ℂ`, in the eigenbasis of `ρ`. -/
noncomputable def specFun {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) (g : ℝ → ℂ) : Matrix n n ℂ :=
  (h.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i ↦ g (h.eigenvalues i)) *
    star (h.eigenvectorUnitary : Matrix n n ℂ)

variable {ρ : Matrix n n ℂ} (h : ρ.IsHermitian)

private theorem star_U_mul_U :
    star (h.eigenvectorUnitary : Matrix n n ℂ) * (h.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
  Unitary.coe_star_mul_self _

private theorem U_mul_star_U :
    (h.eigenvectorUnitary : Matrix n n ℂ) * star (h.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
  Unitary.coe_mul_star_self _

/-- `f(ρ) g(ρ) = (fg)(ρ)`. -/
theorem specFun_mul (f g : ℝ → ℂ) : specFun h f * specFun h g = specFun h (f * g) := by
  simp only [specFun, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star _) (h.eigenvectorUnitary : Matrix n n ℂ), star_U_mul_U,
    Matrix.one_mul, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
  rfl

/-- `f(ρ) + g(ρ) = (f + g)(ρ)`. -/
theorem specFun_add (f g : ℝ → ℂ) : specFun h f + specFun h g = specFun h (f + g) := by
  simp only [specFun, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  rfl

/-- `f(ρ) - g(ρ) = (f - g)(ρ)`. -/
theorem specFun_sub (f g : ℝ → ℂ) : specFun h f - specFun h g = specFun h (f - g) := by
  simp only [specFun, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rfl

/-- `1(ρ) = 1`. -/
theorem specFun_one : specFun h 1 = 1 := by
  simp only [specFun, Pi.one_apply, diagonal_one, Matrix.mul_one, U_mul_star_U]

/-- `g(ρ)* = ḡ(ρ)`. -/
theorem star_specFun (g : ℝ → ℂ) : star (specFun h g) = specFun h (star g) := by
  simp only [specFun, star_mul, star_star, Matrix.mul_assoc]
  rw [star_eq_conjTranspose (diagonal _), diagonal_conjTranspose]
  rfl

/-- `id(ρ) = ρ`. -/
theorem specFun_ofReal : specFun h (fun t ↦ (t : ℂ)) = ρ := by
  conv_rhs => rw [h.spectral_theorem]
  rfl

/-- For a real `f`, `specFun` is Mathlib's `cfc f ρ`. -/
theorem specFun_ofReal_comp (f : ℝ → ℝ) : specFun h (fun t ↦ (f t : ℂ)) = cfc f ρ := by
  rw [h.cfc_eq]
  rfl

/-- `specFun` only sees the values of `g` on the eigenvalues. -/
theorem specFun_congr {f g : ℝ → ℂ} (hfg : ∀ i, f (h.eigenvalues i) = g (h.eigenvalues i)) :
    specFun h f = specFun h g := by
  simp only [specFun, hfg]

/-- `f(ρ)` and `g(ρ)` commute. -/
theorem specFun_commute (f g : ℝ → ℂ) : Commute (specFun h f) (specFun h g) := by
  rw [Commute, SemiconjBy, specFun_mul, specFun_mul, mul_comm]

/-- `A V = V B` for Hermitian `A, B` gives `g(A) V = V g(B)`. -/
theorem specFun_mul_intertwine {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (V : Matrix m n ℂ) (hV : A * V = V * B) (g : ℝ → ℂ) :
    specFun hA g * V = V * specFun hB g :=
  Conditional.diagonal_intertwine (star_U_mul_U hA) (U_mul_star_U hA) (star_U_mul_U hB)
    (U_mul_star_U hB) V (by rw [← specFun_ofReal hA, ← specFun_ofReal hB] at hV; exact hV) g

/-- `g(ρ)ᵀ = g(ρᵀ)`. -/
theorem specFun_transpose (g : ℝ → ℂ) : (specFun h g)ᵀ = specFun h.transpose g := by
  set U := (h.eigenvectorUnitary : Matrix n n ℂ)
  have key := Conditional.diagonal_intertwine (star_U_mul_U h.transpose)
    (U_mul_star_U h.transpose) (W := (star U)ᵀ) (W' := Uᵀ) (b := h.eigenvalues)
    (by rw [← transpose_mul, star_U_mul_U, transpose_one])
    (by rw [← transpose_mul, U_mul_star_U, transpose_one]) (1 : Matrix n n ℂ) (by
      rw [Matrix.mul_one, Matrix.one_mul]
      change specFun h.transpose (fun t ↦ (t : ℂ)) = _
      rw [specFun_ofReal]
      conv_lhs => rw [← specFun_ofReal h]
      simp only [specFun, transpose_mul, diagonal_transpose, Matrix.mul_assoc, U]) g
  rw [Matrix.mul_one, Matrix.one_mul] at key
  change specFun h.transpose g = _ at key
  rw [key]
  simp only [specFun, transpose_mul, diagonal_transpose, Matrix.mul_assoc, U]

/-- Unitary covariance: `g(W ρ W*) = W g(ρ) W*`. -/
theorem specFun_unitary_conj {W : Matrix n n ℂ} (hW : W ∈ unitary (Matrix n n ℂ))
    (h' : (W * ρ * star W).IsHermitian) (g : ℝ → ℂ) :
    specFun h' g = W * specFun h g * star W := by
  calc specFun h' g = specFun h' g * (W * star W) := by
        rw [Unitary.mul_star_self_of_mem hW, Matrix.mul_one]
    _ = W * specFun h g * star W := by
        rw [← Matrix.mul_assoc, specFun_mul_intertwine h' h W
          (by rw [Matrix.mul_assoc, Unitary.star_mul_self_of_mem hW, Matrix.mul_one])]

/-- `g(ρ)` is unitary when `|g| = 1` on the spectrum. -/
theorem specFun_mem_unitary {g : ℝ → ℂ}
    (hg : ∀ i, star (g (h.eigenvalues i)) * g (h.eigenvalues i) = 1) :
    specFun h g ∈ unitary (Matrix n n ℂ) := by
  have h1 : specFun h (star g * g) = 1 := (specFun_congr h (g := 1) hg).trans (specFun_one h)
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩
  · rw [star_specFun, specFun_mul, h1]
  · rw [star_specFun, specFun_mul, mul_comm, h1]

/-- Entries of `g_z(ρ)` are entire in `z` when each `z ↦ g_z(t)` is. -/
theorem differentiable_specFun_apply {G : ℂ → ℝ → ℂ} (hG : ∀ t, Differentiable ℂ (G · t))
    (i j : n) : Differentiable ℂ fun z ↦ specFun h (G z) i j := by
  simp only [specFun, mul_apply, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  fun_prop

end SpecFun

/-! ## D5.1 API of `ρ^{[z]}` and `ρ̂^z` -/

section D51

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

namespace Conditional

/-- The scalar bracket power `t^{[z]}`: `t^z` for `t > 0`, `0` otherwise. -/
noncomputable def bfun (z : ℂ) (t : ℝ) : ℂ := if 0 < t then Complex.exp (z * Real.log t) else 0

/-- The scalar hat power: `t^z` for `t > 0`, `1` otherwise. -/
noncomputable def hfun (z : ℂ) (t : ℝ) : ℂ := if 0 < t then Complex.exp (z * Real.log t) else 1

/-- `t^{[z]} t^{[w]} = t^{[z+w]}`. -/
theorem bfun_mul_bfun (z w : ℂ) : bfun z * bfun w = bfun (z + w) := by
  funext t; simp only [Pi.mul_apply, bfun]; split_ifs <;> simp [← Complex.exp_add, add_mul]

/-- `t̂^z t̂^w = t̂^{z+w}`. -/
theorem hfun_mul_hfun (z w : ℂ) : hfun z * hfun w = hfun (z + w) := by
  funext t; simp only [Pi.mul_apply, hfun]; split_ifs <;> simp [← Complex.exp_add, add_mul]

/-- `t̂^z t^{[w]} = t^{[z+w]}`. -/
theorem hfun_mul_bfun (z w : ℂ) : hfun z * bfun w = bfun (z + w) := by
  funext t; simp only [Pi.mul_apply, hfun, bfun]; split_ifs <;> simp [← Complex.exp_add, add_mul]

/-- `t^{[z]} t̂^w = t^{[z+w]}`. -/
theorem bfun_mul_hfun (z w : ℂ) : bfun z * hfun w = bfun (z + w) := by
  funext t; simp only [Pi.mul_apply, hfun, bfun]; split_ifs <;> simp [← Complex.exp_add, add_mul]

/-- `conj t^{[z]} = t^{[z̄]}`. -/
theorem star_bfun (z : ℂ) : star (bfun z) = bfun (starRingEnd ℂ z) := by
  funext t; simp only [Pi.star_apply, bfun]
  split_ifs <;> simp [← Complex.exp_conj]

/-- `conj t̂^z = t̂^{z̄}`. -/
theorem star_hfun (z : ℂ) : star (hfun z) = hfun (starRingEnd ℂ z) := by
  funext t; simp only [Pi.star_apply, hfun]
  split_ifs <;> simp [← Complex.exp_conj]

/-- `t̂^z = t^{[z]} + (1 - t^{[0]})`. -/
theorem hfun_eq (z : ℂ) : hfun z = bfun z + (1 - bfun 0) := by
  funext t; simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, hfun, bfun]
  split_ifs <;> simp

/-- `t̂^0 = 1`. -/
theorem hfun_zero : hfun 0 = 1 := by funext t; simp [hfun]

/-- `t^{[a]} = t^a` for real `a ≠ 0`, `t ≥ 0`. -/
theorem bfun_ofReal {a : ℝ} (ha : a ≠ 0) {t : ℝ} (ht : 0 ≤ t) : bfun a t = ((t ^ a : ℝ) : ℂ) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [bfun, Real.zero_rpow ha]
  · rw [bfun, if_pos ht, Real.rpow_def_of_pos ht, Complex.ofReal_exp]
    push_cast; ring_nf

/-- `t^{[1]} = t` for `t ≥ 0`. -/
theorem bfun_one {t : ℝ} (ht : 0 ≤ t) : bfun 1 t = t := by
  simpa using bfun_ofReal one_ne_zero ht

end Conditional

open Conditional

variable {ρ : Matrix n n ℂ}

/-- `ρ^{[z]}` as a spectral function of a Hermitian `ρ`. -/
theorem bracketPow_eq (h : ρ.IsHermitian) (z : ℂ) : bracketPow ρ z = specFun h (bfun z) := by
  rw [bracketPow, dif_pos h]; rfl

/-- `ρ̂^z` as a spectral function of a Hermitian `ρ`. -/
theorem hatPow_eq (h : ρ.IsHermitian) (z : ℂ) : hatPow ρ z = specFun h (hfun z) := by
  rw [hatPow, dif_pos h]; rfl

/-- Junk value: `ρ^{[z]} = 0` for non-Hermitian `ρ`. -/
theorem bracketPow_of_not_isHermitian (h : ¬ ρ.IsHermitian) (z : ℂ) : bracketPow ρ z = 0 :=
  dif_neg h

/-- Junk value: `ρ̂^z = 1` for non-Hermitian `ρ`. -/
theorem hatPow_of_not_isHermitian (h : ¬ ρ.IsHermitian) (z : ℂ) : hatPow ρ z = 1 :=
  dif_neg h

/-- D5.1. `ρ^{[z]} ρ^{[w]} = ρ^{[z+w]}`. -/
theorem bracketPow_mul_bracketPow (ρ : Matrix n n ℂ) (z w : ℂ) :
    bracketPow ρ z * bracketPow ρ w = bracketPow ρ (z + w) := by
  by_cases h : ρ.IsHermitian
  · simp only [bracketPow_eq h, specFun_mul, bfun_mul_bfun]
  · simp [bracketPow_of_not_isHermitian h]

/-- D5.1. `ρ̂^z ρ̂^w = ρ̂^{z+w}`. -/
theorem hatPow_mul_hatPow (ρ : Matrix n n ℂ) (z w : ℂ) :
    hatPow ρ z * hatPow ρ w = hatPow ρ (z + w) := by
  by_cases h : ρ.IsHermitian
  · simp only [hatPow_eq h, specFun_mul, hfun_mul_hfun]
  · simp [hatPow_of_not_isHermitian h]

/-- D5.1. `ρ̂^z ρ^{[w]} = ρ^{[z+w]}`. -/
theorem hatPow_mul_bracketPow (ρ : Matrix n n ℂ) (z w : ℂ) :
    hatPow ρ z * bracketPow ρ w = bracketPow ρ (z + w) := by
  by_cases h : ρ.IsHermitian
  · simp only [hatPow_eq h, bracketPow_eq h, specFun_mul, hfun_mul_bfun]
  · simp [hatPow_of_not_isHermitian h, bracketPow_of_not_isHermitian h]

/-- D5.1. `ρ^{[z]} ρ̂^w = ρ^{[z+w]}`. -/
theorem bracketPow_mul_hatPow (ρ : Matrix n n ℂ) (z w : ℂ) :
    bracketPow ρ z * hatPow ρ w = bracketPow ρ (z + w) := by
  by_cases h : ρ.IsHermitian
  · simp only [hatPow_eq h, bracketPow_eq h, specFun_mul, bfun_mul_hfun]
  · simp [hatPow_of_not_isHermitian h, bracketPow_of_not_isHermitian h]

/-- D5.1. `ρ̂^{-z} ρ̂^z = 1`. -/
theorem hatPow_neg_mul_hatPow (ρ : Matrix n n ℂ) (z : ℂ) : hatPow ρ (-z) * hatPow ρ z = 1 := by
  rw [hatPow_mul_hatPow, neg_add_cancel, hatPow_zero]

/-- D5.1. `ρ̂^z ρ̂^{-z} = 1`. -/
theorem hatPow_mul_hatPow_neg (ρ : Matrix n n ℂ) (z : ℂ) : hatPow ρ z * hatPow ρ (-z) = 1 := by
  rw [hatPow_mul_hatPow, add_neg_cancel, hatPow_zero]

/-- D5.1. `(ρ^{[z]})* = ρ^{[z̄]}`. -/
theorem star_bracketPow (ρ : Matrix n n ℂ) (z : ℂ) :
    star (bracketPow ρ z) = bracketPow ρ (starRingEnd ℂ z) := by
  by_cases h : ρ.IsHermitian
  · rw [bracketPow_eq h, bracketPow_eq h, star_specFun, star_bfun]
  · simp [bracketPow_of_not_isHermitian h]

/-- D5.1. `(ρ^{[z]})ᴴ = ρ^{[z̄]}`. -/
theorem conjTranspose_bracketPow (ρ : Matrix n n ℂ) (z : ℂ) :
    (bracketPow ρ z)ᴴ = bracketPow ρ (starRingEnd ℂ z) :=
  star_bracketPow ρ z

/-- D5.1. `(ρ̂^z)* = ρ̂^{z̄}`. -/
theorem star_hatPow (ρ : Matrix n n ℂ) (z : ℂ) :
    star (hatPow ρ z) = hatPow ρ (starRingEnd ℂ z) := by
  by_cases h : ρ.IsHermitian
  · rw [hatPow_eq h, hatPow_eq h, star_specFun, star_hfun]
  · simp [hatPow_of_not_isHermitian h]

/-- D5.1. `(ρ̂^z)ᴴ = ρ̂^{z̄}`. -/
theorem conjTranspose_hatPow (ρ : Matrix n n ℂ) (z : ℂ) :
    (hatPow ρ z)ᴴ = hatPow ρ (starRingEnd ℂ z) :=
  star_hatPow ρ z

/-- D5.1. `ρ^{[s]}` is Hermitian for real `s`. -/
theorem isHermitian_bracketPow_ofReal (ρ : Matrix n n ℂ) (s : ℝ) :
    (bracketPow ρ s).IsHermitian := by
  rw [IsHermitian, conjTranspose_bracketPow, Complex.conj_ofReal]

/-- D5.1. `ρ̂^s` is Hermitian for real `s`. -/
theorem isHermitian_hatPow_ofReal (ρ : Matrix n n ℂ) (s : ℝ) : (hatPow ρ s).IsHermitian := by
  rw [IsHermitian, conjTranspose_hatPow, Complex.conj_ofReal]

/-- D5.1. `ρ̂^{iu}` is unitary for real `u`. -/
theorem hatPow_mul_I_mem_unitary (ρ : Matrix n n ℂ) (u : ℝ) :
    hatPow ρ (u * Complex.I) ∈ unitary (Matrix n n ℂ) := by
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩ <;>
  · rw [star_hatPow, hatPow_mul_hatPow, ← hatPow_zero ρ]
    congr 1
    simp

/-- D5.1. `ρ^{[0]} = Π_{supp ρ}` is a Hermitian projection. -/
theorem isHermitian_bracketPow_zero (ρ : Matrix n n ℂ) : (bracketPow ρ 0).IsHermitian := by
  simpa using isHermitian_bracketPow_ofReal ρ 0

/-- D5.1. `ρ^{[0]}` is idempotent. -/
theorem bracketPow_zero_mul_self (ρ : Matrix n n ℂ) :
    bracketPow ρ 0 * bracketPow ρ 0 = bracketPow ρ 0 := by
  rw [bracketPow_mul_bracketPow, add_zero]

/-- D5.1. `ρ̂^z = ρ^{[z]} + Π_{ker ρ}`, `Π_{ker ρ} = 1 - ρ^{[0]}`. -/
theorem hatPow_eq_bracketPow_add (ρ : Matrix n n ℂ) (z : ℂ) :
    hatPow ρ z = bracketPow ρ z + (1 - bracketPow ρ 0) := by
  by_cases h : ρ.IsHermitian
  · rw [hatPow_eq h, bracketPow_eq h, bracketPow_eq h, ← specFun_one h, specFun_sub,
      specFun_add, hfun_eq]
  · simp [hatPow_of_not_isHermitian h, bracketPow_of_not_isHermitian h]

/-- D5.1. `ρ^{[0]} ρ^{[z]} = ρ^{[z]}`. -/
theorem bracketPow_zero_mul (ρ : Matrix n n ℂ) (z : ℂ) :
    bracketPow ρ 0 * bracketPow ρ z = bracketPow ρ z := by
  rw [bracketPow_mul_bracketPow, zero_add]

/-- D5.1. `Π_{ker ρ} ρ^{[z]} = 0`. -/
theorem one_sub_bracketPow_zero_mul (ρ : Matrix n n ℂ) (z : ℂ) :
    (1 - bracketPow ρ 0) * bracketPow ρ z = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, bracketPow_zero_mul, sub_self]

/-- D5.1. `ρ̂^z = 1` on `ker ρ`: `ρ̂^z Π_{ker ρ} = Π_{ker ρ}`. -/
theorem hatPow_mul_one_sub_bracketPow_zero (ρ : Matrix n n ℂ) (z : ℂ) :
    hatPow ρ z * (1 - bracketPow ρ 0) = 1 - bracketPow ρ 0 := by
  rw [hatPow_eq_bracketPow_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one,
    bracketPow_mul_bracketPow, add_zero, sub_self, zero_add, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_sub, Matrix.mul_one, bracketPow_zero_mul_self, sub_self, sub_zero]

/-- D5.1. On `supp ρ` (`ρ^{[0]} v = v`) brackets and hats agree: `ρ^{[s]} v = ρ̂^s v`. -/
theorem bracketPow_mulVec_eq_hatPow_mulVec (ρ : Matrix n n ℂ) (s : ℂ) {v : n → ℂ}
    (hv : bracketPow ρ 0 *ᵥ v = v) : bracketPow ρ s *ᵥ v = hatPow ρ s *ᵥ v := by
  rw [hatPow_eq_bracketPow_add, add_mulVec, sub_mulVec, hv, one_mulVec, sub_self, add_zero]

/-- D5.1. Brackets omitted for positive real powers: `ρ^{[a]} = ρ^a` (`CFC.rpow`), `ρ ≥ 0`,
`a ≠ 0`. -/
theorem bracketPow_ofReal (hρ : ρ.PosSemidef) {a : ℝ} (ha : a ≠ 0) :
    bracketPow ρ a = ρ ^ a := by
  rw [CFC.rpow_eq_cfc_real hρ.nonneg, ← specFun_ofReal_comp hρ.isHermitian,
    bracketPow_eq hρ.isHermitian]
  exact specFun_congr _ fun i ↦ bfun_ofReal ha (hρ.eigenvalues_nonneg i)

/-- D5.1. `ρ^{[1]} = ρ` for `ρ ≥ 0`. -/
theorem bracketPow_one (hρ : ρ.PosSemidef) : bracketPow ρ 1 = ρ := by
  rw [bracketPow_eq hρ.isHermitian]
  conv_rhs => rw [← specFun_ofReal hρ.isHermitian]
  exact specFun_congr _ fun i ↦ bfun_one (hρ.eigenvalues_nonneg i)

/-- D5.1. `ρ^{[1/2]} = √ρ` for `ρ ≥ 0`. -/
theorem bracketPow_half (hρ : ρ.PosSemidef) : bracketPow ρ (1 / 2) = CFC.sqrt ρ := by
  rw [CFC.sqrt_eq_rpow, ← bracketPow_ofReal hρ (by norm_num)]
  push_cast; rfl

/-- D5.1. `ρ^{[0]} ρ = ρ` for `ρ ≥ 0`. -/
theorem bracketPow_zero_mul_self_eq (hρ : ρ.PosSemidef) : bracketPow ρ 0 * ρ = ρ := by
  simpa only [bracketPow_one hρ] using bracketPow_zero_mul ρ 1

/-- D5.1. `Π_{ker ρ} ρ = 0` for `ρ ≥ 0`. -/
theorem one_sub_bracketPow_zero_mul_self (hρ : ρ.PosSemidef) : (1 - bracketPow ρ 0) * ρ = 0 := by
  simpa only [bracketPow_one hρ] using one_sub_bracketPow_zero_mul ρ 1

/-- D5.1. `z ↦ ρ^{[z]}_{ij}` is entire. -/
theorem differentiable_bracketPow_apply (ρ : Matrix n n ℂ) (i j : n) :
    Differentiable ℂ fun z ↦ bracketPow ρ z i j := by
  by_cases h : ρ.IsHermitian
  · simp only [bracketPow_eq h]
    refine differentiable_specFun_apply h (fun t ↦ ?_) i j
    simp only [bfun]
    split_ifs <;> fun_prop
  · simp only [bracketPow_of_not_isHermitian h]
    fun_prop

/-- D5.1. `z ↦ ρ̂^z_{ij}` is entire. -/
theorem differentiable_hatPow_apply (ρ : Matrix n n ℂ) (i j : n) :
    Differentiable ℂ fun z ↦ hatPow ρ z i j := by
  simp only [hatPow_eq_bracketPow_add, Matrix.add_apply]
  exact (differentiable_bracketPow_apply ρ i j).add (differentiable_const _)

/-- D5.1. `ρ^{[z]}` commutes with `ρ`. -/
theorem commute_bracketPow_self (ρ : Matrix n n ℂ) (z : ℂ) : Commute (bracketPow ρ z) ρ := by
  by_cases h : ρ.IsHermitian
  · conv_rhs => rw [← specFun_ofReal h]
    rw [bracketPow_eq h]
    exact specFun_commute h _ _
  · simp [bracketPow_of_not_isHermitian h]

/-- D5.1. `ρ^{[z]}` commutes with `ρ^{[w]}`. -/
theorem commute_bracketPow_bracketPow (ρ : Matrix n n ℂ) (z w : ℂ) :
    Commute (bracketPow ρ z) (bracketPow ρ w) := by
  rw [Commute, SemiconjBy, bracketPow_mul_bracketPow, bracketPow_mul_bracketPow, add_comm]

/-- D5.1. `ρ̂^z` commutes with `ρ̂^w`. -/
theorem commute_hatPow_hatPow (ρ : Matrix n n ℂ) (z w : ℂ) :
    Commute (hatPow ρ z) (hatPow ρ w) := by
  rw [Commute, SemiconjBy, hatPow_mul_hatPow, hatPow_mul_hatPow, add_comm]

/-- D5.1. `ρ^{[z]}` commutes with `ρ̂^w`. -/
theorem commute_bracketPow_hatPow (ρ : Matrix n n ℂ) (z w : ℂ) :
    Commute (bracketPow ρ z) (hatPow ρ w) := by
  rw [Commute, SemiconjBy, bracketPow_mul_hatPow, hatPow_mul_bracketPow, add_comm]

/-- D5.1. `ρ̂^z` commutes with `ρ`. -/
theorem commute_hatPow_self (ρ : Matrix n n ℂ) (z : ℂ) : Commute (hatPow ρ z) ρ := by
  rw [hatPow_eq_bracketPow_add]
  exact ((commute_bracketPow_self ρ z).add_left
    ((Commute.one_left ρ).sub_left (commute_bracketPow_self ρ 0)))

/-- D5.1. `(ρ^{[z]})ᵀ = (ρᵀ)^{[z]}`. -/
theorem transpose_bracketPow (h : ρ.IsHermitian) (z : ℂ) :
    (bracketPow ρ z)ᵀ = bracketPow ρᵀ z := by
  rw [bracketPow_eq h, bracketPow_eq h.transpose, specFun_transpose]

/-- D5.1. `(ρ̂^z)ᵀ = (ρᵀ)^̂z`. -/
theorem transpose_hatPow (h : ρ.IsHermitian) (z : ℂ) : (hatPow ρ z)ᵀ = hatPow ρᵀ z := by
  rw [hatPow_eq h, hatPow_eq h.transpose, specFun_transpose]

/-- D5.1. An intertwiner `A V = V B` of Hermitian `A, B` intertwines brackets. -/
theorem bracketPow_mul_intertwine {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (V : Matrix m n ℂ) (hV : A * V = V * B) (z : ℂ) :
    bracketPow A z * V = V * bracketPow B z := by
  rw [bracketPow_eq hA, bracketPow_eq hB, specFun_mul_intertwine hA hB V hV]

/-- D5.1. An intertwiner `A V = V B` of Hermitian `A, B` intertwines hats. -/
theorem hatPow_mul_intertwine {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (V : Matrix m n ℂ) (hV : A * V = V * B) (z : ℂ) :
    hatPow A z * V = V * hatPow B z := by
  rw [hatPow_eq hA, hatPow_eq hB, specFun_mul_intertwine hA hB V hV]

private theorem isHermitian_unitary_conj_iff {W : Matrix n n ℂ} (hW : W ∈ unitary (Matrix n n ℂ)) :
    (W * ρ * star W).IsHermitian ↔ ρ.IsHermitian := by
  refine ⟨fun h ↦ ?_, fun h ↦ isHermitian_mul_mul_conjTranspose W h⟩
  have := isHermitian_conjTranspose_mul_mul W h
  rwa [← star_eq_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc,
    Unitary.star_mul_self_of_mem hW, Matrix.mul_one, ← Matrix.mul_assoc,
    Unitary.star_mul_self_of_mem hW, Matrix.one_mul] at this

/-- D5.1. Unitary covariance: `(W ρ W*)^{[z]} = W ρ^{[z]} W*`. -/
theorem bracketPow_unitary_conj {W : Matrix n n ℂ} (hW : W ∈ unitary (Matrix n n ℂ)) (z : ℂ) :
    bracketPow (W * ρ * star W) z = W * bracketPow ρ z * star W := by
  by_cases h : ρ.IsHermitian
  · have h' := (isHermitian_unitary_conj_iff hW).2 h
    rw [bracketPow_eq h, bracketPow_eq h', specFun_unitary_conj h hW]
  · rw [bracketPow_of_not_isHermitian h, bracketPow_of_not_isHermitian
      (mt (isHermitian_unitary_conj_iff hW).1 h)]
    simp

/-- D5.1. Unitary covariance: `(W ρ W*)^̂z = W ρ̂^z W*`. -/
theorem hatPow_unitary_conj {W : Matrix n n ℂ} (hW : W ∈ unitary (Matrix n n ℂ)) (z : ℂ) :
    hatPow (W * ρ * star W) z = W * hatPow ρ z * star W := by
  by_cases h : ρ.IsHermitian
  · have h' := (isHermitian_unitary_conj_iff hW).2 h
    rw [hatPow_eq h, hatPow_eq h', specFun_unitary_conj h hW]
  · rw [hatPow_of_not_isHermitian h, hatPow_of_not_isHermitian
      (mt (isHermitian_unitary_conj_iff hW).1 h), Matrix.mul_one,
      Unitary.mul_star_self_of_mem hW]

end D51

/-! ## Marginals of a vector: (F1), support, (F2) -/

section Marginal

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  {Λ D D' : Finset σ}

/-- `ρ_D ≥ 0`. -/
theorem posSemidef_marg (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) : (marg θ hD).PosSemidef :=
  posSemidef_ptrace hD (posSemidef_vecMulVec_self_star θ)

/-- `ρ_D` is Hermitian. -/
theorem isHermitian_marg (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) : (marg θ hD).IsHermitian :=
  (posSemidef_marg θ hD).isHermitian

/-- `Tr ρ_D = ⟨θ, θ⟩`. -/
theorem trace_marg (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) : (marg θ hD).trace = star θ ⬝ᵥ θ := by
  rw [marg, trace_ptrace, trace_vecMulVec, dotProduct_comm]

variable [∀ i, DecidableEq (loc i)]

/-- `‖v‖² = Re ⟨v, v⟩` in `EuclideanSpace`. -/
theorem Conditional.norm_toLp_sq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 = (star v ⬝ᵥ v).re := by
  rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- D5.1 (F1). For `T` on `D ⊆ Λ`: `‖(T ⊗ I) θ‖² = Tr(T* T ρ_D)`. -/
theorem step_5_1_F1 (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (T : Matrix (Reg loc D) (Reg loc D) ℂ) :
    star (extendId hD T *ᵥ θ) ⬝ᵥ (extendId hD T *ᵥ θ) = (Tᴴ * T * marg θ hD).trace := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← extendId_conjTranspose, ← extendId_mul,
    dotProduct_extendId_mulVec, trace_mul_comm]
  rfl

/-- D5.1 (F1), Hilbert–Schmidt form: `‖(T ⊗ I) θ‖² = ‖T √ρ_D‖₂²`. -/
theorem step_5_1_F1_sqrt (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ)
    (T : Matrix (Reg loc D) (Reg loc D) ℂ) :
    star (extendId hD T *ᵥ θ) ⬝ᵥ (extendId hD T *ᵥ θ) =
      ((T * CFC.sqrt (marg θ hD))ᴴ * (T * CFC.sqrt (marg θ hD))).trace := by
  have hs : (CFC.sqrt (marg θ hD))ᴴ = CFC.sqrt (marg θ hD) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  rw [step_5_1_F1, conjTranspose_mul, hs, ← Matrix.mul_assoc, Matrix.mul_assoc _ Tᴴ T,
    Matrix.mul_assoc (CFC.sqrt _), trace_mul_comm (CFC.sqrt (marg θ hD)),
    Matrix.mul_assoc (Tᴴ * T), CFC.sqrt_mul_sqrt_self _ (posSemidef_marg θ hD).nonneg]

/-- D5.1 (F1), norm form: `‖(T ⊗ I) θ‖² = Re Tr(T* T ρ_D)`. -/
theorem step_5_1_F1_norm (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ)
    (T : Matrix (Reg loc D) (Reg loc D) ℂ) :
    ‖(WithLp.toLp 2 (extendId hD T *ᵥ θ) : EuclideanSpace ℂ (Reg loc Λ))‖ ^ 2 =
      (Tᴴ * T * marg θ hD).trace.re := by
  rw [Conditional.norm_toLp_sq, step_5_1_F1]

/-- D5.1. `Π_{ker ρ_D} θ = 0`. -/
theorem extendId_one_sub_bracketPow_marg_mulVec (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) :
    extendId hD (1 - bracketPow (marg θ hD) 0) *ᵥ θ = 0 := by
  set Q := 1 - bracketPow (marg θ hD) 0
  have hQ : Qᴴ = Q := by
    rw [conjTranspose_sub, conjTranspose_one, (isHermitian_bracketPow_zero _).eq]
  have h0 := step_5_1_F1 θ hD Q
  rw [hQ, Matrix.mul_assoc, one_sub_bracketPow_zero_mul_self (posSemidef_marg θ hD),
    Matrix.mul_zero, trace_zero] at h0
  exact dotProduct_star_self_eq_zero.1 h0

/-- D5.1. `θ ∈ supp ρ_D ⊗ (Λ \ D)`: `(ρ_D^{[0]} ⊗ I) θ = θ`. -/
theorem extendId_bracketPow_zero_marg_mulVec (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) :
    extendId hD (bracketPow (marg θ hD) 0) *ᵥ θ = θ := by
  have h : extendId hD (bracketPow (marg θ hD) 0) =
      1 - extendId hD (1 - bracketPow (marg θ hD) 0) := by
    rw [eq_sub_iff_add_eq, ← extendId_add, add_sub_cancel, extendId_one]
  rw [h, sub_mulVec, one_mulVec, extendId_one_sub_bracketPow_marg_mulVec, sub_zero]

/-- D5.1. On a purification of `ρ_D`, applied innermost, hats and brackets agree:
`(ρ̂_D^s ⊗ I) θ = (ρ_D^{[s]} ⊗ I) θ`. -/
theorem extendId_hatPow_marg_mulVec (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (s : ℂ) :
    extendId hD (hatPow (marg θ hD) s) *ᵥ θ = extendId hD (bracketPow (marg θ hD) s) *ᵥ θ := by
  rw [hatPow_eq_bracketPow_add, extendId_add, add_mulVec,
    extendId_one_sub_bracketPow_marg_mulVec, add_zero]

/-- D5.1. An operator on `D` disjoint from `Y` keeps `θ` in `supp ρ_Y ⊗ (Λ \ Y)`:
`(ρ_Y^{[0]} ⊗ I)(A ⊗ I) θ = (A ⊗ I) θ`. -/
theorem extendId_bracketPow_zero_marg_mulVec_extendId {Y : Finset σ} (θ : Reg loc Λ → ℂ)
    (hY : Y ⊆ Λ) (hD : D ⊆ Λ) (hd : Disjoint D Y) (A : Matrix (Reg loc D) (Reg loc D) ℂ) :
    extendId hY (bracketPow (marg θ hY) 0) *ᵥ (extendId hD A *ᵥ θ) = extendId hD A *ᵥ θ := by
  rw [mulVec_mulVec, ← (commute_extendId_extendId hD hY hd A _).eq, ← mulVec_mulVec,
    extendId_bracketPow_zero_marg_mulVec]

namespace Conditional

omit [∀ i, Fintype (loc i)] in
/-- Nested extension: `(A ⊗ 1_{T∖S}) ⊗ 1_{V∖T} = A ⊗ 1_{V∖S}`. -/
theorem extendId_extendId {S T V : Finset σ} (hST : S ⊆ T) (hTV : T ⊆ V)
    (A : Matrix (Reg loc S) (Reg loc S) ℂ) :
    extendId hTV (extendId hST A) = extendId (hST.trans hTV) A := by
  ext w w'
  have hiff : (restr (S := V \ T) Finset.sdiff_subset w = restr Finset.sdiff_subset w' ∧
      restr (S := T \ S) Finset.sdiff_subset (restr hTV w) =
        restr Finset.sdiff_subset (restr hTV w')) ↔
      restr (S := V \ S) Finset.sdiff_subset w = restr Finset.sdiff_subset w' := by
    simp only [restr, Finset.restrict₂, funext_iff, Subtype.forall, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩ i ⟨hiV, hiS⟩
      by_cases hiT : i ∈ T
      · exact h2 i ⟨hiT, hiS⟩
      · exact h1 i ⟨hiV, hiT⟩
    · intro h
      exact ⟨fun i hi ↦ h i ⟨hi.1, fun hS ↦ hi.2 (hST hS)⟩, fun i hi ↦ h i ⟨hTV hi.1, hi.2⟩⟩
  simp only [extendId, of_apply]
  split_ifs <;> first | rfl | (exfalso; tauto)

end Conditional

namespace Conditional

variable (θ : Reg loc (D ∪ D') → ℂ) (hd : Disjoint D D')

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] in
/-- The coefficient matrix `C_{ab} = θ(a, b)` of `θ` on `D ⊔ D'`. -/
noncomputable def coeff : Matrix (Reg loc D) (Reg loc D') ℂ :=
  Matrix.of fun a b ↦ θ ((unionEquiv hd).symm (a, b))

/-- `((A ⊗ I) θ)(a, b) = (A C)_{ab}`. -/
theorem extendId_mulVec_unionEquiv_symm (hD : D ⊆ D ∪ D') (A : Matrix (Reg loc D) (Reg loc D) ℂ)
    (a : Reg loc D) (b : Reg loc D') :
    (extendId hD A *ᵥ θ) ((unionEquiv hd).symm (a, b)) = (A * coeff θ hd) a b := by
  simp only [mulVec, dotProduct, ← (unionEquiv hd).symm.sum_comp, Fintype.sum_prod_type,
    unionEquiv_symm_apply, extendId_apply_glue, EmbeddingLike.apply_eq_iff_eq, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_apply, coeff, of_apply]

/-- `((I ⊗ B) θ)(a, b) = (C Bᵀ)_{ab}`. -/
theorem extendId_mulVec_unionEquiv_symm' (hD' : D' ⊆ D ∪ D')
    (B : Matrix (Reg loc D') (Reg loc D') ℂ) (a : Reg loc D) (b : Reg loc D') :
    (extendId hD' B *ᵥ θ) ((unionEquiv hd).symm (a, b)) = (coeff θ hd * Bᵀ) a b := by
  simp only [mulVec, dotProduct, ← (unionEquiv hd).symm.sum_comp, Fintype.sum_prod_type,
    unionEquiv_symm_apply_eq_glue_right, extendId_apply_glue, EmbeddingLike.apply_eq_iff_eq,
    ite_mul, zero_mul, mul_apply, coeff, of_apply, transpose_apply, mul_comm]
  rw [Finset.sum_comm]
  simp

omit [∀ i, DecidableEq (loc i)] in
/-- `ρ_D = C C*`. -/
theorem marg_eq_coeff (hD : D ⊆ D ∪ D') :
    marg θ hD = coeff θ hd * (coeff θ hd)ᴴ := by
  rw [marg, ptrace_eq_traceRight hd]
  ext a a'
  simp only [traceRight, of_apply, submatrix_apply, vecMulVec_apply, mul_apply,
    conjTranspose_apply, coeff, Pi.star_apply]

omit [∀ i, DecidableEq (loc i)] in
/-- `ρ_{D'} = (C* C)ᵀ`. -/
theorem marg_eq_coeff' (hD' : D' ⊆ D ∪ D') :
    marg θ hD' = ((coeff θ hd)ᴴ * coeff θ hd)ᵀ := by
  rw [marg, ptrace_eq_traceLeft hd]
  ext b b'
  simp only [traceLeft, of_apply, submatrix_apply, vecMulVec_apply, transpose_apply, mul_apply,
    conjTranspose_apply, coeff, Pi.star_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- Schmidt mirroring at the level of the coefficient matrix. -/
theorem extendId_mulVec_eq_of_coeff (hD : D ⊆ D ∪ D') (hD' : D' ⊆ D ∪ D')
    {A : Matrix (Reg loc D) (Reg loc D) ℂ} {B : Matrix (Reg loc D') (Reg loc D') ℂ}
    (h : A * coeff θ hd = coeff θ hd * Bᵀ) : extendId hD A *ᵥ θ = extendId hD' B *ᵥ θ := by
  funext w
  obtain ⟨⟨a, b⟩, rfl⟩ := (unionEquiv hd).symm.surjective w
  rw [extendId_mulVec_unionEquiv_symm, extendId_mulVec_unionEquiv_symm', h]

end Conditional

open Conditional in
/-- D5.1 (F2). Schmidt mirroring: for `Λ = D ⊔ D'` and every `s ∈ ℂ`,
`ρ_D^{[s]} θ = ρ_{D'}^{[s]} θ` (same non-zero spectrum, matched eigenvectors). -/
theorem step_5_1_F2 (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (hD' : D' ⊆ Λ) (hd : Disjoint D D')
    (hΛ : D ∪ D' = Λ) (s : ℂ) :
    extendId hD (bracketPow (marg θ hD) s) *ᵥ θ =
      extendId hD' (bracketPow (marg θ hD') s) *ᵥ θ := by
  subst hΛ
  set C := coeff θ hd
  refine extendId_mulVec_eq_of_coeff θ hd hD hD' ?_
  rw [marg_eq_coeff θ hd, marg_eq_coeff' θ hd,
    transpose_bracketPow (isHermitian_conjTranspose_mul_self C).transpose, transpose_transpose]
  exact bracketPow_mul_intertwine (isHermitian_mul_conjTranspose_self C)
    (isHermitian_conjTranspose_mul_self C) C (by simp only [Matrix.mul_assoc]) s

open Conditional in
/-- D5.1 (F2), hats: for `Λ = D ⊔ D'` and every `s ∈ ℂ`, `ρ̂_D^s θ = ρ̂_{D'}^s θ`. -/
theorem step_5_1_F2_hat (θ : Reg loc Λ → ℂ) (hD : D ⊆ Λ) (hD' : D' ⊆ Λ) (hd : Disjoint D D')
    (hΛ : D ∪ D' = Λ) (s : ℂ) :
    extendId hD (hatPow (marg θ hD) s) *ᵥ θ = extendId hD' (hatPow (marg θ hD') s) *ᵥ θ := by
  rw [extendId_hatPow_marg_mulVec, extendId_hatPow_marg_mulVec, step_5_1_F2 θ hD hD' hd hΛ]

/-- D5.1 (F2), support: for `Λ = D ⊔ D'` and `Y ⊆ D'`, `ρ_{D'}^{[s]} θ ∈ supp ρ_Y ⊗ (Λ \ Y)`:
`(ρ_Y^{[0]} ⊗ I)(ρ_{D'}^{[s]} ⊗ I) θ = (ρ_{D'}^{[s]} ⊗ I) θ`. -/
theorem extendId_bracketPow_zero_marg_mulVec_bracketPow {Y : Finset σ} (θ : Reg loc Λ → ℂ)
    (hD : D ⊆ Λ) (hD' : D' ⊆ Λ) (hd : Disjoint D D') (hΛ : D ∪ D' = Λ) (hY : Y ⊆ Λ)
    (hYD' : Y ⊆ D') (s : ℂ) :
    extendId hY (bracketPow (marg θ hY) 0) *ᵥ (extendId hD' (bracketPow (marg θ hD') s) *ᵥ θ) =
      extendId hD' (bracketPow (marg θ hD') s) *ᵥ θ := by
  rw [← step_5_1_F2 θ hD hD' hd hΛ, extendId_bracketPow_zero_marg_mulVec_extendId θ hY hD
    (hd.mono_right hYD')]

/-- D5.1 (F2), support, hats: for `Λ = D ⊔ D'` and `Y ⊆ D'`,
`(ρ_Y^{[0]} ⊗ I)(ρ̂_{D'}^s ⊗ I) θ = (ρ̂_{D'}^s ⊗ I) θ`. -/
theorem extendId_bracketPow_zero_marg_mulVec_hatPow {Y : Finset σ} (θ : Reg loc Λ → ℂ)
    (hD : D ⊆ Λ) (hD' : D' ⊆ Λ) (hd : Disjoint D D') (hΛ : D ∪ D' = Λ) (hY : Y ⊆ Λ)
    (hYD' : Y ⊆ D') (s : ℂ) :
    extendId hY (bracketPow (marg θ hY) 0) *ᵥ (extendId hD' (hatPow (marg θ hD') s) *ᵥ θ) =
      extendId hD' (hatPow (marg θ hD') s) *ᵥ θ := by
  rw [extendId_hatPow_marg_mulVec,
    extendId_bracketPow_zero_marg_mulVec_bracketPow θ hD hD' hd hΛ hY hYD']

end Marginal

end AreaLaw
