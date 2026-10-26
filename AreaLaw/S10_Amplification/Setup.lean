import AreaLaw.S04_Quasilocal

/-!
# §10.0 Standing choices; the clock law

Digest `digest/10-amplification.md` (D10.1), paper `paper/sections/09-amplification.tex`
lines 14–30. No geometry.

The rate-one Poisson clocks of D10.2, D10.3 and D10.12 enter only through the law of their
event word (route difference, `RefactoringResult.md` §5): with `N` labels and time `t`, the
number of events is Poisson with mean `N t` and, given it, the labels are independent and
uniform, so a word `w : Fin m → ι` (`w 0` the latest event) has probability
`e^{-N t} t^m / m!`. The paper's jump formula and Gronwall become recursions in `m` summed
against these weights.
-/

namespace AreaLaw

open Finset

/-! ## D10.1 The standing exponents -/

/-- D10.1. `ε = 10⁻⁵`. -/
noncomputable def ε : ℝ := 1 / 100000

/-- D10.1. `β = 1 - 2·10⁻⁶`. -/
noncomputable def β : ℝ := 1 - 2 / 1000000

/-- D10.1. `α = p/(p+1)`, `p` the integer of Proposition 4.3. -/
noncomputable def α (p : ℕ) : ℝ := p / (p + 1)

theorem α_pos {p : ℕ} (hp : 1 ≤ p) : 0 < α p := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  unfold α; positivity

theorem α_lt_one (p : ℕ) : α p < 1 := by
  unfold α; rw [div_lt_one (by positivity)]; linarith

theorem α_le_one (p : ℕ) : α p ≤ 1 := (α_lt_one p).le

/-- D10.1. `p ≥ 10⁶` gives `α > 1 - 10⁻⁶`. -/
theorem lt_α {p : ℕ} (hp : 10 ^ 6 ≤ p) : 1 - 1 / 1000000 < α p := by
  have h : (10 : ℝ) ^ 6 ≤ p := by exact_mod_cast hp
  unfold α
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- D10.16.2. `(1 - ε)/α < β` and `1 - ε < β` for `p ≥ 10⁶`. -/
theorem exponent_gap {p : ℕ} (hp : 10 ^ 6 ≤ p) : (1 - ε) / α p < β ∧ 1 - ε < β := by
  have h := lt_α hp
  have h0 : 0 < α p := by linarith
  refine ⟨?_, by norm_num [ε, β]⟩
  rw [div_lt_iff₀ h0]
  have : (1 - 2 / 1000000 : ℝ) * (1 - 1 / 1000000) ≤ β * α p :=
    mul_le_mul_of_nonneg_left h.le (by norm_num [β])
  nlinarith [show (1 : ℝ) - 1 / 100000 < (1 - 2 / 1000000) * (1 - 1 / 1000000) by norm_num,
    show ε = 1 / 100000 from rfl]

/-! ## The clock law (route of D10.2.9, D10.2.11, D10.3.3, D10.12) -/

/-- The probability `e^{-N t} t^m / m!` of one word of length `m`. -/
noncomputable def clockWeight (N : ℕ) (t : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-(N * t)) * t ^ m / m.factorial

/-- `𝔼_t F = ∑_m e^{-N t} t^m/m! ∑_{w : Fin m → ι} F m w`, `N = |ι|`: expectation over the
event word of independent rate-one clocks at the labels `ι` on `[0, t]`. -/
noncomputable def clockExp (ι : Type*) [Fintype ι] (t : ℝ) (F : ∀ m : ℕ, (Fin m → ι) → ℝ) :
    ℝ :=
  ∑' m, clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w

/-- The product of `G` along a word, later events on the left:
`wordProd G w = G (w 0) * G (w 1) * ⋯`. -/
def wordProd {ι n : Type*} [Fintype n] [DecidableEq n] (G : ι → Matrix n n ℂ) :
    ∀ m : ℕ, (Fin m → ι) → Matrix n n ℂ
  | 0, _ => 1
  | m + 1, w => G (w 0) * wordProd G m (Fin.tail w)

/-- Maps `𝓔 i` applied along a word, the earliest event first:
`wordMap 𝓔 w B = 𝓔 (w 0) (𝓔 (w 1) (⋯ B))`. -/
def wordMap {ι X : Type*} (𝓔 : ι → X → X) : ∀ m : ℕ, (Fin m → ι) → X → X
  | 0, _ => id
  | m + 1, w => fun B => 𝓔 (w 0) (wordMap 𝓔 m (Fin.tail w) B)

section Words

variable {ι : Type*}

@[simp] theorem wordProd_zero {n : Type*} [Fintype n] [DecidableEq n] (G : ι → Matrix n n ℂ)
    (w : Fin 0 → ι) : wordProd G 0 w = 1 := rfl

theorem wordProd_succ {n : Type*} [Fintype n] [DecidableEq n] (G : ι → Matrix n n ℂ) (m : ℕ)
    (w : Fin (m + 1) → ι) : wordProd G (m + 1) w = G (w 0) * wordProd G m (Fin.tail w) := rfl

@[simp] theorem wordMap_zero {X : Type*} (𝓔 : ι → X → X) (w : Fin 0 → ι) (B : X) :
    wordMap 𝓔 0 w B = B := rfl

theorem wordMap_succ {X : Type*} (𝓔 : ι → X → X) (m : ℕ) (w : Fin (m + 1) → ι) (B : X) :
    wordMap 𝓔 (m + 1) w B = 𝓔 (w 0) (wordMap 𝓔 m (Fin.tail w) B) := rfl

end Words

section Clock

variable {ι : Type*} [Fintype ι]

/-- Words of length `m + 1` are a latest label and a word of length `m`. -/
theorem sum_word_succ {M : Type*} [AddCommMonoid M] (m : ℕ) (f : (Fin (m + 1) → ι) → M) :
    ∑ w : Fin (m + 1) → ι, f w = ∑ i, ∑ w : Fin m → ι, f (Fin.cons i w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => ι) _ _ fun _ => rfl).symm

theorem clockWeight_nonneg (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : 0 ≤ clockWeight N t m := by
  unfold clockWeight; positivity

/-- `∑_m e^{-N t} t^m/m! a^m = e^{(a - N) t}`. -/
theorem hasSum_clockWeight_mul_pow (N : ℕ) (t a : ℝ) :
    HasSum (fun m => clockWeight N t m * a ^ m) (Real.exp ((a - N) * t)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x := a * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h' := h.mul_left (Real.exp (-(N * t)))
  rw [← Real.exp_add, show -(↑N * t) + a * t = (a - N) * t by ring] at h'
  refine h'.congr_fun fun m => ?_
  simp only [clockWeight, mul_pow]
  ring

/-- `∑_m e^{-N t} t^m/m! · m a^{m-1} = t e^{(a - N) t}`. -/
theorem hasSum_clockWeight_mul_mul_pow (N : ℕ) (t a : ℝ) :
    HasSum (fun m => clockWeight N t m * (m * a ^ (m - 1))) (t * Real.exp ((a - N) * t)) := by
  have h := (hasSum_clockWeight_mul_pow N t a).mul_left t
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, mul_zero,
    sub_zero]
  refine h.congr_fun fun m => ?_
  simp only [clockWeight, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.cast_mul, pow_succ]
  field_simp

/-- The clock law has total mass one. -/
theorem clockExp_one (t : ℝ) : clockExp ι t (fun _ _ => 1) = 1 := by
  have h := hasSum_clockWeight_mul_pow (Fintype.card ι) t (Fintype.card ι)
  rw [sub_self, zero_mul, Real.exp_zero] at h
  refine (h.congr_fun fun m => ?_).tsum_eq
  simp [Finset.card_univ]

/-- If `∑_w F m w ≤ A a^m` for nonnegative `F`, the expectation is finite (summable) and
`𝔼_t F ≤ A e^{(a - N) t}`. -/
theorem clockExp_le_of_sum_le {t : ℝ} (ht : 0 ≤ t) {F : ∀ m : ℕ, (Fin m → ι) → ℝ}
    (hF : ∀ m w, 0 ≤ F m w) {A a : ℝ} (hb : ∀ m, ∑ w, F m w ≤ A * a ^ m) :
    Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w) ∧
      clockExp ι t F ≤ A * Real.exp ((a - Fintype.card ι) * t) := by
  have hs := (hasSum_clockWeight_mul_pow (Fintype.card ι) t a).mul_left A
  have hle : ∀ m, clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w ≤
      A * (clockWeight (Fintype.card ι) t m * a ^ m) := fun m => by
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hb m) (clockWeight_nonneg _ ht m)
  have h0 : ∀ m, 0 ≤ clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w := fun m =>
    mul_nonneg (clockWeight_nonneg _ ht m) (Finset.sum_nonneg fun w _ => hF m w)
  have hsum := Summable.of_nonneg_of_le h0 hle hs.summable
  exact ⟨hsum, (hsum.tsum_le_tsum hle hs.summable).trans_eq hs.tsum_eq⟩

/-- If `∑_w F m w ≤ A m a^{m-1}` for nonnegative `F`, then `𝔼_t F ≤ A t e^{(a - N) t}`. -/
theorem clockExp_le_of_sum_le_mul {t : ℝ} (ht : 0 ≤ t) {F : ∀ m : ℕ, (Fin m → ι) → ℝ}
    (hF : ∀ m w, 0 ≤ F m w) {A a : ℝ} (hb : ∀ m, ∑ w, F m w ≤ A * (m * a ^ (m - 1))) :
    Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w) ∧
      clockExp ι t F ≤ A * (t * Real.exp ((a - Fintype.card ι) * t)) := by
  have hs := (hasSum_clockWeight_mul_mul_pow (Fintype.card ι) t a).mul_left A
  have hle : ∀ m, clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w ≤
      A * (clockWeight (Fintype.card ι) t m * (m * a ^ (m - 1))) := fun m => by
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hb m) (clockWeight_nonneg _ ht m)
  have h0 : ∀ m, 0 ≤ clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F m w := fun m =>
    mul_nonneg (clockWeight_nonneg _ ht m) (Finset.sum_nonneg fun w _ => hF m w)
  have hsum := Summable.of_nonneg_of_le h0 hle hs.summable
  exact ⟨hsum, (hsum.tsum_le_tsum hle hs.summable).trans_eq hs.tsum_eq⟩

/-- D10.12 (selection of one realization). If three nonnegative observables have summable
expectations `𝔼 F_j ≤ e_j` and `e₁/x₁ + e₂/x₂ + e₃/x₃ < 1`, one word has `F_j ≤ x_j` for all
three. -/
theorem exists_word_le {t : ℝ} (ht : 0 ≤ t) {F₁ F₂ F₃ : ∀ m : ℕ, (Fin m → ι) → ℝ}
    (h₁ : ∀ m w, 0 ≤ F₁ m w) (h₂ : ∀ m w, 0 ≤ F₂ m w) (h₃ : ∀ m w, 0 ≤ F₃ m w)
    (s₁ : Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F₁ m w))
    (s₂ : Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F₂ m w))
    (s₃ : Summable (fun m => clockWeight (Fintype.card ι) t m * ∑ w : Fin m → ι, F₃ m w))
    {e₁ e₂ e₃ x₁ x₂ x₃ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (he₁ : clockExp ι t F₁ ≤ e₁) (he₂ : clockExp ι t F₂ ≤ e₂) (he₃ : clockExp ι t F₃ ≤ e₃)
    (he : e₁ / x₁ + e₂ / x₂ + e₃ / x₃ < 1) :
    ∃ m, ∃ w : Fin m → ι, F₁ m w ≤ x₁ ∧ F₂ m w ≤ x₂ ∧ F₃ m w ≤ x₃ := by
  by_contra hcon
  push Not at hcon
  set c := clockWeight (Fintype.card ι) t
  have hpt : ∀ m (w : Fin m → ι), 1 ≤ F₁ m w / x₁ + F₂ m w / x₂ + F₃ m w / x₃ := by
    intro m w
    by_cases a₁ : F₁ m w ≤ x₁
    · by_cases a₂ : F₂ m w ≤ x₂
      · have := (one_le_div hx₃).2 (hcon m w a₁ a₂).le
        have := div_nonneg (h₁ m w) hx₁.le; have := div_nonneg (h₂ m w) hx₂.le; linarith
      · have := (one_le_div hx₂).2 (not_le.1 a₂).le
        have := div_nonneg (h₁ m w) hx₁.le; have := div_nonneg (h₃ m w) hx₃.le; linarith
    · have := (one_le_div hx₁).2 (not_le.1 a₁).le
      have := div_nonneg (h₂ m w) hx₂.le; have := div_nonneg (h₃ m w) hx₃.le; linarith
  have hsum : Summable fun m => c m * ∑ w : Fin m → ι,
      (F₁ m w / x₁ + F₂ m w / x₂ + F₃ m w / x₃) := by
    have := ((s₁.div_const x₁).add (s₂.div_const x₂)).add (s₃.div_const x₃)
    refine this.congr fun m => ?_
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]; ring
  have h1 : (1 : ℝ) ≤ clockExp ι t fun m w => F₁ m w / x₁ + F₂ m w / x₂ + F₃ m w / x₃ := by
    rw [← clockExp_one (ι := ι) t]
    have hs1 := (hasSum_clockWeight_mul_pow (Fintype.card ι) t (Fintype.card ι)).summable
    refine (hs1.congr fun m => ?_).tsum_le_tsum (fun m => ?_) hsum
    · simp [Finset.card_univ]
    · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => hpt m w)
        (clockWeight_nonneg _ ht m)
  have h2 : (clockExp ι t fun m w => F₁ m w / x₁ + F₂ m w / x₂ + F₃ m w / x₃) =
      clockExp ι t F₁ / x₁ + clockExp ι t F₂ / x₂ + clockExp ι t F₃ / x₃ := by
    unfold clockExp
    rw [← tsum_div_const, ← tsum_div_const, ← tsum_div_const,
      ← (s₁.div_const _).tsum_add (s₂.div_const _),
      ← ((s₁.div_const _).add (s₂.div_const _)).tsum_add (s₃.div_const _)]
    congr 1; funext m
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]; ring
  have := div_le_div_of_nonneg_right he₁ hx₁.le
  have := div_le_div_of_nonneg_right he₂ hx₂.le
  have := div_le_div_of_nonneg_right he₃ hx₃.le
  linarith

end Clock

/-! ## Vector norms -/

section VNorm

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Euclidean norm `‖v‖` of a vector `v : n → ℂ`. -/
noncomputable def vnorm (v : n → ℂ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖

theorem vnorm_nonneg (v : n → ℂ) : 0 ≤ vnorm v := norm_nonneg _

theorem vnorm_eq_sqrt (v : n → ℂ) : vnorm v = √(star v ⬝ᵥ v).re := by
  rw [vnorm, EuclideanSpace.norm_eq]
  congr 1
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem vnorm_sq (v : n → ℂ) : vnorm v ^ 2 = (star v ⬝ᵥ v).re := by
  rw [vnorm_eq_sqrt, Real.sq_sqrt]
  exact (Complex.le_def.mp (dotProduct_star_self_nonneg v)).1

theorem vnorm_add_le (u v : n → ℂ) : vnorm (u + v) ≤ vnorm u + vnorm v := norm_add_le _ _

theorem vnorm_sub_le (u v : n → ℂ) : vnorm (u - v) ≤ vnorm u + vnorm v := norm_sub_le _ _

theorem vnorm_sub_rev (u v : n → ℂ) : vnorm (u - v) = vnorm (v - u) := norm_sub_rev _ _

theorem vnorm_neg (v : n → ℂ) : vnorm (-v) = vnorm v := norm_neg _

theorem vnorm_mulVec_le [DecidableEq n] (A : Matrix m n ℂ) (v : n → ℂ) :
    vnorm (A *ᵥ v) ≤ ‖A‖ * vnorm v :=
  l2_opNorm_mulVec A (WithLp.toLp 2 v)

theorem vnorm_eq_one {v : n → ℂ} (hv : star v ⬝ᵥ v = 1) : vnorm v = 1 := by
  rw [vnorm_eq_sqrt, hv]; simp

end VNorm

/-! ## Shared objects of §10

Operators carry a finite spectator factor `κ`: an operator `A` on the physical region `Λ`
acts on `Reg loc Λ × κ` as `A ⊗ₖ 1`. In Proposition 10.2, `κ = Reg loc X × Reg loc X`, the
copies `s'` (first factor) and `e'` (second factor) of the Hilbert space on `X`. -/

section Objects

open Arealaw Matrix
open OpenAI (pureState)
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-- D10.2.5. The oscillation `d_y(B) = sup_{‖U‖ ≤ 1} ‖[U_y, B]‖` at a site `y ∈ Λ`, with
`U_y = U ⊗ I` on the on-site space at `y`, spectators untouched (`0` for `y ∉ Λ`). The paper
takes the supremum over unitaries; the contractions give the same facts. -/
noncomputable def osc {Λ : Finset σ} (κ : Type*) [Fintype κ] [DecidableEq κ] (y : σ)
    (B : Matrix (Reg loc Λ × κ) (Reg loc Λ × κ) ℂ) : ℝ :=
  if hy : y ∈ Λ then
    ⨆ U : {U : Matrix (Reg loc {y}) (Reg loc {y}) ℂ // ‖U‖ ≤ 1},
      ‖(extendId (Finset.singleton_subset_iff.2 hy) U.1 ⊗ₖ (1 : Matrix κ κ ℂ)) * B -
        B * (extendId (Finset.singleton_subset_iff.2 hy) U.1 ⊗ₖ (1 : Matrix κ κ ℂ))‖
  else 0

/-- The splitting `(w, (s, e)) ↦ ((w|_N, s), (w|_{Λ∖N}, e))` of
`ℋ_Λ ⊗ ℋ_{s'} ⊗ ℋ_{e'}` into `(ℋ_N ⊗ ℋ_{s'}) ⊗ (ℋ_{Λ∖N} ⊗ ℋ_{e'})`. -/
def splitN {Λ N : Finset σ} (hN : N ⊆ Λ) (X : Finset σ) :
    Reg loc Λ × (Reg loc X × Reg loc X) ≃
      (Reg loc N × Reg loc X) × (Reg loc (Λ \ N) × Reg loc X) :=
  ((glueEquiv hN).symm.prodCongr (Equiv.refl _)).trans
    (Equiv.prodProdProdComm _ _ _ _)

/-- D10.14. An operator acts on `N ∪ s'` (and trivially on `Λ \ N` and `e'`): in the
coordinates of `splitN` it is `M ⊗ I`. -/
def ActsOn {Λ N : Finset σ} (hN : N ⊆ Λ) (X : Finset σ)
    (R : Matrix (Reg loc Λ × (Reg loc X × Reg loc X))
      (Reg loc Λ × (Reg loc X × Reg loc X)) ℂ) : Prop :=
  ∃ M : Matrix (Reg loc N × Reg loc X) (Reg loc N × Reg loc X) ℂ,
    R = (M ⊗ₖ (1 : Matrix (Reg loc (Λ \ N) × Reg loc X)
      (Reg loc (Λ \ N) × Reg loc X) ℂ)).submatrix (splitN hN X) (splitN hN X)

/-- The product vector `Ω ⊗ ξ` on `n × κ`. -/
def tensVec {n κ : Type*} (Ω : n → ℂ) (ξ : κ → ℂ) : n × κ → ℂ := fun p => Ω p.1 * ξ p.2

/-- The spectral projection `∑_{j ∈ sel} |u_j⟩⟨u_j|` of a Hermitian matrix onto the
eigenvectors `u_j` (columns of `eigenvectorUnitary`) indexed by `sel`. -/
noncomputable def specProj {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (sel : Finset n) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun j => if j ∈ sel then 1 else 0) *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

variable [∀ i, Nonempty (loc i)]

/-- D10.6. The blank configuration `|0⟩` of a region. -/
noncomputable def blank (X : Finset σ) : Reg loc X := fun _ => Classical.arbitrary _

/-- D10.6. The blank vector `|00⟩_{s'e'}`. -/
noncomputable def blankVec (X : Finset σ) : Reg loc X × Reg loc X → ℂ :=
  fun v => if v = (blank X, blank X) then 1 else 0

/-- D2.1. The marginal `ρ_X` of `|Ω⟩⟨Ω|`. -/
noncomputable abbrev Amplification.marg {Λ X : Finset σ} (Ω : Reg loc Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (hX : X ⊆ Λ) : SubState (Reg loc X) ℂ :=
  (pureState Ω hΩ).toSubState.restrict hX

/-- D10.6. `φ = 𝓡_X Ω = |0⟩_X |0⟩_{s'} ∑_y √p_y |y⟩_{e'} |ω_y⟩`: the configuration of `X`
moved to `e'`, blanks on `X` and `s'`. -/
noncomputable def copyVec {Λ X : Finset σ} (hX : X ⊆ Λ) (Ω : Reg loc Λ → ℂ) :
    Reg loc Λ × (Reg loc X × Reg loc X) → ℂ :=
  fun v => if ((glueEquiv hX).symm v.1).1 = blank X ∧ v.2.1 = blank X then
    Ω (glueEquiv hX (v.2.2, ((glueEquiv hX).symm v.1).2)) else 0

/-- D10.6. `η = Ω ⊗ ∑_x √p_x |x⟩_{s'} |x⟩_{e'}`, with `ρ_X = ∑_x p_x |x⟩⟨x|` the
eigendecomposition (`|x⟩` the columns of the eigenvector unitary). -/
noncomputable def restoredVec {Λ X : Finset σ} (hX : X ⊆ Λ) (Ω : Reg loc Λ → ℂ)
    (hΩ : star Ω ⬝ᵥ Ω = 1) : Reg loc Λ × (Reg loc X × Reg loc X) → ℂ :=
  fun v => Ω v.1 * ∑ x,
    (Real.sqrt ((Amplification.marg Ω hΩ hX).psd.isHermitian.eigenvalues x) : ℂ) *
    ((Amplification.marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary : Matrix _ _ ℂ) v.2.1 x *
    ((Amplification.marg Ω hΩ hX).psd.isHermitian.eigenvectorUnitary : Matrix _ _ ℂ) v.2.2 x

end Objects

end AreaLaw
