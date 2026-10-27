import AreaLaw.S04_Quasilocal.CenteredFilter
import AreaLawForMathlib.Analysis.ODE.LiebRobinson

/-!
# §4.1 Graph-distance propagation (Lemma 4.1)

Digest `digest/04-quasilocal.md` (D4.4), paper `paper/sections/03-quasilocal.tex` lines 52–128.
Graph-level (`Map.md`, Dimension): a simple graph `G` on a site type `σ`, the induced distance
`d_Λ`, ball growth `V`.

Some declarations here come from the v1 file `OpenAI/LiebRobinson/GraphPropagation.lean`, whose
header records it as ported or adapted from `LionSR/TNLean` (see `NOTICE`).
-/

namespace AreaLaw

open Arealaw Matrix Finset LiebRobinson Set
open OpenAI (IsSupportedOn)
open scoped Matrix.Norms.L2Operator

/-! ## The weighted recursion on an abstract finite graph -/

namespace GraphDomain

section Abstract

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [DecidableEq ι] [Fintype κ]

theorem toNat_min_le_toNat_min_add (n r : ℕ) (a b : ℕ∞) (h : a ≤ b + r) :
    (min (n : ℕ∞) a).toNat ≤ (min (n : ℕ∞) b).toNat + r := by
  induction b using ENat.recTopCoe with
  | top =>
    have : (min (n : ℕ∞) a).toNat ≤ n := ENat.toNat_le_of_le_natCast (min_le_left _ _)
    simp only [min_top_right, ENat.toNat_natCast]
    omega
  | coe m =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe k =>
      have hk : k ≤ m + r := by exact_mod_cast h
      have e : ∀ p q : ℕ, (min (p : ℕ∞) q).toNat = min p q := fun p q => by
        rcases le_total p q with hpq | hpq
        · rw [min_eq_left (by exact_mod_cast hpq), min_eq_left hpq, ENat.toNat_natCast]
        · rw [min_eq_right (by exact_mod_cast hpq), min_eq_right hpq, ENat.toNat_natCast]
      rw [e, e]
      omega

/-- D4.4.5. The norms of the terms meeting a support `X k` sum to at most `|X k| b₀`. -/
theorem sum_norm_meeting_le (X : κ → Finset ι) (h : κ → Matrix n n ℂ) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀) (k : κ)
    [DecidablePred fun j => Disjoint (X k : Set ι) (X j : Set ι)] :
    ∑ j, (if Disjoint (X k : Set ι) (X j : Set ι) then 0 else ‖h j‖) ≤ #(X k) * b₀ := by
  classical
  calc
    _ ≤ ∑ j, ∑ x ∈ X k, (if x ∈ X j then ‖h j‖ else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hkj
      · exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp
      · obtain ⟨x, hxk, hxj⟩ := Set.not_disjoint_iff.mp hkj
        have hle := Finset.single_le_sum (f := fun x => if x ∈ X j then ‖h j‖ else 0)
          (fun x _ => by split_ifs <;> simp) (Finset.mem_coe.mp hxk)
        simpa only [Finset.mem_coe.mp hxj, ite_true] using hle
    _ = ∑ x ∈ X k, ∑ j ∈ univ.filter (fun j => x ∈ X j), ‖h j‖ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ _x ∈ X k, b₀ := Finset.sum_le_sum fun x _ => hBudget x
    _ = #(X k) * b₀ := by rw [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq ι] in
/-- The distance `d(x, Y) = min_{y ∈ Y} d(x, y)` is `1`-Lipschitz. -/
theorem inf_edist_le_add (Gi : SimpleGraph ι) (Y : Finset ι) (x x' : ι) :
    Y.inf (Gi.edist x) ≤ Gi.edist x x' + Y.inf (Gi.edist x') := by
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp
  obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_inf Y hY (Gi.edist x')
  rw [hy']
  exact (Finset.inf_le hy).trans SimpleGraph.edist_triangle

/-- The standing hypotheses of D4.4 on an abstract finite graph `Gi`: terms `h k` on nonempty
supports `X k` of diameter `≤ R`, at most `vR` sites, per-site budget `b₀`, `S k` the operators
on `X k`; `B` commutes with every operator on a support avoiding the set `Y` (a site `y` in
`eq:quasilocal-lr`, `Y = Λ \ N_l(a_i)` in `eq:quasilocal-lr-ce`). -/
structure Standing (Gi : SimpleGraph ι) (X : κ → Finset ι) (h : κ → Matrix n n ℂ)
    (S : κ → Submodule ℂ (Matrix n n ℂ)) (R vR : ℕ) (b₀ : ℝ) (B : Matrix n n ℂ) (Y : Finset ι) :
    Prop where
  nonempty : ∀ k, (X k).Nonempty
  herm : ∀ k, (h k).IsHermitian
  mem : ∀ k, h k ∈ S k
  comm : ∀ i j, Disjoint (X i : Set ι) (X j : Set ι) → ∀ A ∈ S i, Commute (h j) A
  diam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, Gi.edist x z ≤ R
  card : ∀ k, #(X k) ≤ vR
  budget : ∀ x, ∑ j ∈ univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀
  commB : ∀ k, Disjoint (X k) Y → ∀ A ∈ S k, Commute A B

/-- D4.4.4–7 for `t ≥ 0`: the recursion `eq:quasilocal-lr-recursion`, weighted by
`e^{-μ d(X_k, Y)}` and closed by the Volterra comparison. -/
theorem commutatorNorm_le_of_nonneg {Gi : SimpleGraph ι} {X : κ → Finset ι}
    {h : κ → Matrix n n ℂ} {S : κ → Submodule ℂ (Matrix n n ℂ)} {R vR : ℕ} {b₀ : ℝ}
    {B : Matrix n n ℂ} {Y : Finset ι} (hs : Standing Gi X h S R vR b₀ B Y)
    {μ : ℝ} (hμ : 0 ≤ μ) (N : ℕ) (i : κ) {a : ι} (ha : a ∈ X i)
    (hN : ∀ y ∈ Y, (N : ℕ∞) ≤ Gi.edist a y) {t : ℝ} (ht : 0 ≤ t) :
    heisenbergCommutatorNorm (∑ k, h k) B (S i) t ≤
      2 * ‖B‖ * Real.exp (μ * R) * Real.exp (-(μ * N)) *
        Real.exp (2 * vR * b₀ * Real.exp (μ * R) * t) := by
  classical
  have hb₀ : 0 ≤ b₀ := (Finset.sum_nonneg fun j _ => norm_nonneg (h j)).trans
    (hs.budget (hs.nonempty i).choose)
  -- D4.4.1: `near k` realises `d(X_k, Y)`; `D k = min(N, d(X_k, Y))`.
  let ρ (x : ι) : ℕ∞ := Y.inf (Gi.edist x)
  have hρ : (N : ℕ∞) ≤ ρ a := Finset.le_inf hN
  let near (k : κ) : ι :=
    Classical.choose (Finset.exists_min_image (X k) ρ (hs.nonempty k))
  have hnear_mem (k : κ) : near k ∈ X k :=
    (Classical.choose_spec (Finset.exists_min_image (X k) ρ (hs.nonempty k))).1
  have hnear_le (k : κ) {x : ι} (hx : x ∈ X k) : ρ (near k) ≤ ρ x :=
    (Classical.choose_spec (Finset.exists_min_image (X k) ρ (hs.nonempty k))).2 x hx
  let D (k : κ) : ℕ := (min (N : ℕ∞) (ρ (near k))).toNat
  let w (k : κ) : ℝ := Real.exp (-(μ * D k))
  let f (s : ℝ) (k : κ) : ℝ := heisenbergCommutatorNorm (∑ k, h k) B (S k) s
  let coeff (k j : κ) : ℝ := if Disjoint (X k : Set ι) (X j : Set ι) then 0 else 2 * ‖h j‖
  let v : ℝ := 2 * vR * b₀ * Real.exp (μ * R)
  have hf : Continuous f := continuous_pi fun k => continuous_heisenbergCommutatorNorm _ B _
  have hCoeff : ∀ k j, 0 ≤ coeff k j := fun k j => by
    dsimp only [coeff]; split_ifs <;> positivity
  have hw : ∀ k, 0 < w k := fun k => Real.exp_pos _
  -- D4.4.6: intersecting supports have comparable distances to `Y`.
  have hWeight : ∀ k j, ¬Disjoint (X k : Set ι) (X j : Set ι) →
      w j ≤ Real.exp (μ * R) * w k := by
    intro k j hkj
    obtain ⟨x, hxk, hxj⟩ := Set.not_disjoint_iff.mp hkj
    have hD : D k ≤ D j + R := by
      apply toNat_min_le_toNat_min_add
      calc ρ (near k) ≤ ρ x := hnear_le k hxk
        _ ≤ Gi.edist x (near j) + ρ (near j) := inf_edist_le_add Gi Y _ _
        _ ≤ R + ρ (near j) := add_le_add_left (hs.diam j _ hxj _ (hnear_mem j)) _
        _ = _ := add_comm _ _
    have hD' : (D k : ℝ) ≤ D j + R := by exact_mod_cast hD
    dsimp only [w]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  -- D4.4.5: the row sums are at most `v`.
  have hRow : ∀ k, ∑ j, coeff k j * w j ≤ v * w k := by
    intro k
    calc
      ∑ j, coeff k j * w j ≤ ∑ j, (2 * Real.exp (μ * R) * w k) *
          (if Disjoint (X k : Set ι) (X j : Set ι) then 0 else ‖h j‖) := by
        refine Finset.sum_le_sum fun j _ => ?_
        dsimp only [coeff]
        split_ifs with hkj
        · simp
        · nlinarith [hWeight k j hkj, norm_nonneg (h j)]
      _ = (2 * Real.exp (μ * R) * w k) *
          ∑ j, (if Disjoint (X k : Set ι) (X j : Set ι) then 0 else ‖h j‖) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * Real.exp (μ * R) * w k) * (vR * b₀) := by
        refine mul_le_mul_of_nonneg_left ((sum_norm_meeting_le X h b₀ hs.budget k).trans ?_)
          (by positivity)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs.card k) hb₀
      _ = v * w k := by dsimp only [v]; ring
  -- D4.4.4: `f(0) ≤ 2‖B‖ 1_{Y ∩ X ≠ ∅}`.
  have hInit : ∀ k, f 0 k ≤ 2 * ‖B‖ * w k := by
    intro k
    by_cases hyk : ¬Disjoint (X k) Y
    · obtain ⟨y, hyk, hyY⟩ := Finset.not_disjoint_iff.1 hyk
      have hDk : D k = 0 := by
        have := ENat.toNat_le_of_le_natCast ((min_le_right (N : ℕ∞) _).trans
          ((hnear_le k hyk).trans ((Finset.inf_le hyY).trans_eq
            (SimpleGraph.edist_self (G := Gi) (v := y)))))
        dsimp only [D]
        exact_mod_cast Nat.le_zero.mp (by exact_mod_cast this)
      have hw1 : w k = 1 := by simp [w, hDk]
      rw [hw1, mul_one]
      exact heisenbergCommutatorNorm_zero_le _ B _
    · rw [show f 0 k = 0 from heisenbergCommutatorNorm_zero_of_commute _ B (S k)
        (hs.commB k (not_not.1 hyk))]
      exact mul_nonneg (by positivity) (hw k).le
  have hBound : ∀ s ∈ Icc 0 t, ∀ k,
      f s k ≤ 2 * ‖B‖ * w k + ∑ j, coeff k j * ∫ u in (0 : ℝ)..s, f u j := by
    intro s hs' k
    have hRec := heisenbergCommutatorNorm_le_integral h S
      (fun i j => Disjoint (X i : Set ι) (X j : Set ι)) hs.herm hs.mem hs.comm B k s hs'.1
    have hEq : 2 * ∑ j, (if Disjoint (X k : Set ι) (X j : Set ι) then 0 else
        ‖h j‖ * ∫ u in (0 : ℝ)..s, heisenbergCommutatorNorm (∑ k, h k) B (S j) u) =
        ∑ j, coeff k j * ∫ u in (0 : ℝ)..s, f u j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [coeff, f]
      split_ifs <;> ring
    rw [hEq] at hRec
    exact hRec.trans (add_le_add_left (hInit k) _)
  -- D4.4.5–7: Volterra comparison in place of the chain sum.
  have hMain := finite_volterra_le_weight_mul_exp f hf coeff hCoeff w hw (2 * ‖B‖) v t
    (by positivity) (by positivity) hRow
    (fun s _ k => heisenbergCommutatorNorm_nonneg _ B _ s) hBound t ⟨ht, le_rfl⟩ i
  have hwi : w i ≤ Real.exp (μ * R) * Real.exp (-(μ * N)) := by
    have hD : N ≤ D i + R := by
      have h1 := toNat_min_le_toNat_min_add N R (ρ a) (ρ (near i)) (by
        calc ρ a ≤ Gi.edist a (near i) + ρ (near i) := inf_edist_le_add Gi Y _ _
          _ ≤ R + ρ (near i) := add_le_add_left (hs.diam i _ ha _ (hnear_mem i)) _
          _ = _ := add_comm _ _)
      rwa [min_eq_left hρ, ENat.toNat_natCast] at h1
    have hD' : (N : ℝ) ≤ D i + R := by exact_mod_cast hD
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc f t i ≤ 2 * ‖B‖ * w i * Real.exp (v * t) := hMain
    _ ≤ 2 * ‖B‖ * (Real.exp (μ * R) * Real.exp (-(μ * N))) * Real.exp (v * t) := by
      gcongr
    _ = _ := by dsimp only [v]; ring

/-- D4.4.1–7 for every `t` (`t < 0`: replace `H → -H`), times `‖A‖` by homogeneity. -/
theorem norm_commutator_le {Gi : SimpleGraph ι} {X : κ → Finset ι}
    {h : κ → Matrix n n ℂ} {S : κ → Submodule ℂ (Matrix n n ℂ)} {R vR : ℕ} {b₀ : ℝ}
    {B : Matrix n n ℂ} {Y : Finset ι} (hs : Standing Gi X h S R vR b₀ B Y)
    {μ : ℝ} (hμ : 0 ≤ μ) (N : ℕ) (i : κ) {a : ι} (ha : a ∈ X i)
    (hN : ∀ y ∈ Y, (N : ℕ∞) ≤ Gi.edist a y) {A : Matrix n n ℂ} (hA : A ∈ S i) (t : ℝ) :
    ‖heisenbergEvolution (∑ k, h k) t A * B - B * heisenbergEvolution (∑ k, h k) t A‖ ≤
      2 * Real.exp (μ * R) * ‖A‖ * ‖B‖ *
        Real.exp (2 * vR * b₀ * Real.exp (μ * R) * |t| - μ * N) := by
  have hNorm : heisenbergCommutatorNorm (∑ k, h k) B (S i) t ≤
      2 * ‖B‖ * Real.exp (μ * R) * Real.exp (-(μ * N)) *
        Real.exp (2 * vR * b₀ * Real.exp (μ * R) * |t|) := by
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact commutatorNorm_le_of_nonneg hs hμ N i ha hN ht
    · have hs' : Standing Gi X (fun k => -h k) S R vR b₀ B Y :=
        { hs with
          herm := fun k => (hs.herm k).neg
          mem := fun k => Submodule.neg_mem _ (hs.mem k)
          comm := fun i j hij A hA => (hs.comm i j hij A hA).neg_left
          budget := by simpa only [norm_neg] using hs.budget }
      have hBound := commutatorNorm_le_of_nonneg hs' hμ N i ha hN (t := -t) (by linarith)
      rw [Finset.sum_neg_distrib, ← heisenbergCommutatorNorm_neg_time, neg_neg] at hBound
      rwa [abs_of_neg ht]
  calc
    _ ≤ heisenbergCommutatorNorm (∑ k, h k) B (S i) t * ‖A‖ :=
      norm_heisenberg_commutator_le_heisenbergCommutatorNorm _ B _ t hA
    _ ≤ (2 * ‖B‖ * Real.exp (μ * R) * Real.exp (-(μ * N)) *
        Real.exp (2 * vR * b₀ * Real.exp (μ * R) * |t|)) * ‖A‖ :=
      mul_le_mul_of_nonneg_right hNorm (norm_nonneg A)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

end Abstract


section Hamiltonian

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)]

/-- The operators on `Λ` supported in `X ⊆ Λ`, as a subspace. -/
def supportedOn {Λ X : Finset σ} (hX : X ⊆ Λ) :
    Submodule ℂ (Matrix (Reg loc Λ) (Reg loc Λ) ℂ) where
  carrier := {A | IsSupportedOn hX A}
  zero_mem' := ⟨0, (extendId_zero hX).symm⟩
  add_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A + B, (extendId_add hX A B).symm⟩
  smul_mem' := by
    rintro c _ ⟨A, rfl⟩
    exact ⟨c • A, (extendId_smul hX c A).symm⟩

/-- `τ_t` is the Heisenberg evolution of `AreaLawForMathlib`. -/
theorem τ_eq_heisenbergEvolution {m : Type*} [Fintype m] [DecidableEq m] (H : Matrix m m ℂ)
    (t : ℝ) (A : Matrix m m ℂ) : τ H t A = heisenbergEvolution H t A := by
  have e : ∀ s : ℝ, ((s : ℂ) * Complex.I) • H = s • (Complex.I • H) := fun s => by
    rw [mul_smul, Complex.coe_smul]
  rw [τ, heisenbergEvolution, show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, e, e]

variable (G : SimpleGraph σ)

/-- For admissible `Φ`, `H = ∑_{X ∈ supports} h_X ⊗ 1`. -/
theorem hamiltonian_eq_sum_supports {Λ : Finset σ} {R : ℕ} {J : ℝ}
    {Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ} (hΦ : IsAdmissible G Λ R J Φ) :
    hamiltonian Λ Φ =
      ∑ Y : supports G Λ R, extendId ((mem_supports G).1 Y.2).1 (Φ Y.1) := by
  classical
  let F : Finset σ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ := fun X =>
    if h : X ⊆ Λ then extendId h (Φ X) else 0
  have h1 : hamiltonian Λ Φ = ∑ X ∈ Λ.powerset, F X := by
    rw [hamiltonian, ← Finset.sum_attach Λ.powerset F]
    exact Finset.sum_congr rfl fun X _ => by simp [F, dif_pos (mem_powerset.1 X.2)]
  have h2 : ∑ Y : supports G Λ R, extendId ((mem_supports G).1 Y.2).1 (Φ Y.1) =
      ∑ X ∈ supports G Λ R, F X := by
    rw [← Finset.sum_coe_sort (supports G Λ R) F]
    exact Finset.sum_congr rfl fun Y _ => by simp [F, dif_pos ((mem_supports G).1 Y.2).1]
  rw [h1, h2]
  refine (Finset.sum_subset (fun X hX => mem_powerset.2 ((mem_supports G).1 hX).1) ?_).symm
  intro X hXp hXs
  simp [F, dif_pos (mem_powerset.1 hXp), (hΦ X (mem_powerset.1 hXp)).2.2 hXs]

end Hamiltonian

end GraphDomain


/-! ## D4.4, `eq:quasilocal-lr` -/

section LR

open GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) (V : ℕ → ℕ)
  (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
  {loc : σ → Type} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

private theorem disjoint_of_subtype {Λ A B : Finset σ} (hA : A ⊆ Λ)
    (h : Disjoint ((A.subtype (· ∈ (Λ : Set σ)) : Finset (Λ : Set σ)) : Set (Λ : Set σ))
      ((B.subtype (· ∈ (Λ : Set σ)) : Finset (Λ : Set σ)) : Set (Λ : Set σ))) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  let x' : (Λ : Set σ) := ⟨x, Finset.mem_coe.2 (hA hxA)⟩
  have h1 : x' ∈ ((A.subtype (· ∈ (Λ : Set σ)) : Finset (Λ : Set σ)) : Set (Λ : Set σ)) :=
    Finset.mem_coe.2 (Finset.mem_subtype.2 hxA)
  have h2 : x' ∈ ((B.subtype (· ∈ (Λ : Set σ)) : Finset (Λ : Set σ)) : Set (Λ : Set σ)) :=
    Finset.mem_coe.2 (Finset.mem_subtype.2 hxB)
  exact Set.disjoint_left.1 h h1 h2

open Classical in
include hV in
/-- D4.1–D4.3: the standing hypotheses of D4.4 on the graph induced on `Λ`, for `B`
supported in `Yr ⊆ Λ`. -/
theorem standing_induce (R : ℕ) (J : ℝ) {Λ : Finset σ}
    {Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ} (hΦ : IsAdmissible G Λ R J Φ)
    {Yr : Finset σ} (hY : Yr ⊆ Λ) {B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hB : IsSupportedOn hY B) :
    Standing (G.induce (Λ : Set σ)) (fun Y : supports G Λ R => Y.1.subtype (· ∈ (Λ : Set σ)))
      (fun Y => extendId ((GraphDomain.mem_supports G).1 Y.2).1 (Φ Y.1))
      (fun Y => supportedOn ((GraphDomain.mem_supports G).1 Y.2).1) R (V R) (J * μ V R) B
      (Yr.subtype (· ∈ (Λ : Set σ))) := by
  let Xs : supports G Λ R → Finset (Λ : Set σ) := fun Y => Y.1.subtype (· ∈ (Λ : Set σ))
  let term : supports G Λ R → Matrix (Reg loc Λ) (Reg loc Λ) ℂ :=
    fun Y => extendId ((GraphDomain.mem_supports G).1 Y.2).1 (Φ Y.1)
  have hsub : ∀ Y : supports G Λ R, Y.1 ⊆ Λ := fun Y => ((GraphDomain.mem_supports G).1 Y.2).1
  have hmem : ∀ (Y : supports G Λ R) (x : (Λ : Set σ)), x ∈ Xs Y ↔ x.1 ∈ Y.1 := fun Y x =>
    Finset.mem_subtype
  exact
    { nonempty := fun Y => by
        obtain ⟨x, hx⟩ := ((GraphDomain.mem_supports G).1 Y.2).2.1
        exact ⟨⟨x, Finset.mem_coe.2 (hsub Y hx)⟩, (hmem Y _).2 hx⟩
      herm := fun Y => isHermitian_extendId _ (hΦ Y.1 (hsub Y)).1
      mem := fun Y => ⟨Φ Y.1, rfl⟩
      comm := by
        rintro i j hij _ ⟨A', rfl⟩
        exact commute_extendId_extendId (hsub j) (hsub i)
          (disjoint_of_subtype (hsub j) hij.symm) _ _
      diam := fun Y x hx z hz => by
        have := GraphDomain.domainEDist_le_of_mem_supports G Y.2 ((hmem Y x).1 hx) ((hmem Y z).1 hz)
        rwa [GraphDomain.domainEDist_eq G ⟨x.1, x.2⟩ ⟨z.1, z.2⟩] at this
      card := fun Y => by
        rw [Finset.card_subtype, Finset.filter_true_of_mem fun x hx => Finset.mem_coe.2 (hsub Y hx)]
        exact (step_2_8 G V hV Λ R (((GraphDomain.mem_supports G).1 Y.2).2.1).choose).2.2.2
          Y.1 Y.2
      budget := fun x => by
        calc ∑ j ∈ univ.filter (fun j => x ∈ Xs j), ‖term j‖
            ≤ ∑ j ∈ univ.filter (fun j : supports G Λ R => x.1 ∈ j.1), ‖Φ j.1‖ := by
              rw [Finset.filter_congr fun j _ => hmem j x]
              exact Finset.sum_le_sum fun j _ => norm_extendId_le _ _
          _ = ∑ X ∈ supports G Λ R with x.1 ∈ X, ‖Φ X‖ := by
              rw [Finset.sum_filter, Finset.sum_filter]
              exact Finset.sum_coe_sort (supports G Λ R) fun X => if x.1 ∈ X then ‖Φ X‖ else 0
          _ ≤ J * μ V R := (step_2_8 G V hV Λ R x.1).2.2.1 J Φ hΦ
      commB := by
        rintro k hyk _ ⟨A', rfl⟩
        obtain ⟨B', rfl⟩ := hB
        refine commute_extendId_extendId (hsub k) _ (disjoint_of_subtype (hsub k) ?_) _ _
        exact Finset.disjoint_coe.2 hyk }

include hV in
/-- D4.4.1–7 on `Λ`, for `B` supported in `Yr ⊆ Λ`: the bound of `eq:quasilocal-lr` with any
`N ≤ d_Λ(a, Yr)` in the exponent. -/
theorem norm_commutator_le_of_le (R : ℕ) (J : ℝ) {c : ℝ} (hc : 0 ≤ c) {Λ : Finset σ}
    {Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ} (hΦ : IsAdmissible G Λ R J Φ)
    {X : Finset σ} (hX : X ∈ supports G Λ R) {a : σ} (ha : a ∈ X)
    {A : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hA : IsSupportedOn ((GraphDomain.mem_supports G).1 hX).1 A)
    {Yr : Finset σ} (hY : Yr ⊆ Λ) {B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hB : IsSupportedOn hY B) (N : ℕ)
    (hN : ∀ y ∈ Yr, (N : ℕ∞) ≤ domainEDist G Λ a y) (t : ℝ) :
    ‖τ (hamiltonian Λ Φ) t A * B - B * τ (hamiltonian Λ Φ) t A‖ ≤
      2 * Real.exp (c * R) * ‖A‖ * ‖B‖ *
        Real.exp (2 * (V R * J * μ V R) * Real.exp (c * R) * |t| - c * N) := by
  have hs := standing_induce G V hV R J hΦ hY hB
  have haΛ : a ∈ (Λ : Set σ) := Finset.mem_coe.2 (((GraphDomain.mem_supports G).1 hX).1 ha)
  have hN' : ∀ y ∈ Yr.subtype (· ∈ (Λ : Set σ)),
      (N : ℕ∞) ≤ (G.induce (Λ : Set σ)).edist ⟨a, haΛ⟩ y := fun y hy =>
    (hN y.1 (Finset.mem_subtype.1 hy)).trans_eq (GraphDomain.domainEDist_eq G ⟨a, haΛ⟩ ⟨y.1, y.2⟩)
  have h := norm_commutator_le hs hc N ⟨X, hX⟩ (Finset.mem_subtype.2 ha) hN' hA t
  rw [← hamiltonian_eq_sum_supports G hΦ, ← τ_eq_heisenbergEvolution] at h
  convert h using 3
  ring

theorem domainEDist_comm (Λ : Finset σ) (x y : σ) :
    domainEDist G Λ x y = domainEDist G Λ y x := by
  unfold domainEDist
  by_cases h : x ∈ Λ ∧ y ∈ Λ
  · rw [dif_pos h, dif_pos h.symm, SimpleGraph.edist_comm]
  · rw [dif_neg h, dif_neg fun h' => h h'.symm]

/-- Sites outside `N_l(a)` are at distance `> l` from `a`. -/
theorem le_domainEDist_of_mem_sdiff {Λ : Finset σ} {a y : σ} {l : ℕ}
    (hy : y ∈ Λ \ graphNbhd G Λ {a} l) : ((l + 1 : ℕ) : ℕ∞) ≤ domainEDist G Λ a y := by
  have hy' : ¬ domainEDist G Λ y a ≤ l := by
    simpa [graphNbhd, (Finset.mem_sdiff.1 hy).1] using (Finset.mem_sdiff.1 hy).2
  rw [domainEDist_comm]
  push_cast
  exact Order.add_one_le_of_lt (not_le.1 hy')

theorem isHermitian_hamiltonian {R : ℕ} {J : ℝ} {Λ : Finset σ}
    {Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ} (hΦ : IsAdmissible G Λ R J Φ) :
    (hamiltonian Λ Φ).IsHermitian := by
  rw [hamiltonian_eq_sum_supports G hΦ]
  exact Finset.sum_induction _ IsHermitian (fun _ _ => IsHermitian.add) isHermitian_zero
    fun Y _ => isHermitian_extendId _ (hΦ Y.1 ((GraphDomain.mem_supports G).1 Y.2).1).1

include hV in
/-- D4.4 Lemma 4.1. For every `c > 0`, with `κ = V_R J μ_R`, `v = 2κe^{cR}` and
`C = 2e^{cR}`: for every label `X ∈ supports` with anchor `a ∈ X`, every `A` supported in `X`
and every `t ∈ ℝ`, (eq:quasilocal-lr) for every site `y` and every operator `B_y` on site `y`,
`‖[τ_t(A), B_y]‖ ≤ C ‖A‖ ‖B_y‖ e^{v|t| - c d_Λ(a,y)}`, and the commutator is `0` if
`d_Λ(a,y) = ∞`; (eq:quasilocal-lr-ce) for every integer `l ≥ 0`,
`‖τ_t(A) - E_{i,l}(τ_t(A))‖ ≤ ‖A‖ min {2, C e^{v|t| - c l}}`. Here `τ_t` is the evolution under
`H = ∑_X h_X` with `Φ` admissible. -/
theorem lemma_4_1 [∀ i, Nonempty (loc i)] (R : ℕ) (J : ℝ) {c : ℝ} (hc : 0 < c) {Λ : Finset σ}
    {Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ} (hΦ : IsAdmissible G Λ R J Φ)
    {X : Finset σ} (hX : X ∈ supports G Λ R) {a : σ} (ha : a ∈ X)
    {A : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hA : IsSupportedOn ((GraphDomain.mem_supports G).1 hX).1 A) (t : ℝ) :
    let κ : ℝ := V R * J * μ V R
    let v : ℝ := 2 * κ * Real.exp (c * R)
    let C : ℝ := 2 * Real.exp (c * R)
    (∀ {y : σ} (hy : y ∈ Λ) {B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ},
      IsSupportedOn (Finset.singleton_subset_iff.2 hy) B →
      ‖τ (hamiltonian Λ Φ) t A * B - B * τ (hamiltonian Λ Φ) t A‖ ≤
          C * ‖A‖ * ‖B‖ * Real.exp (v * |t| - c * (domainEDist G Λ a y).toNat) ∧
        (domainEDist G Λ a y = ⊤ →
          τ (hamiltonian Λ Φ) t A * B = B * τ (hamiltonian Λ Φ) t A)) ∧
    ∀ l : ℕ, ‖τ (hamiltonian Λ Φ) t A - E G Λ a l (τ (hamiltonian Λ Φ) t A)‖ ≤
      ‖A‖ * min 2 (C * Real.exp (v * |t| - c * l)) := by
  intro κ v C
  refine ⟨fun {y} hy {B} hB => ?_, fun l => ?_⟩
  · have hN := fun (N : ℕ) (hN : (N : ℕ∞) ≤ domainEDist G Λ a y) =>
      norm_commutator_le_of_le G V hV R J hc.le hΦ hX ha hA (Finset.singleton_subset_iff.2 hy)
        hB N (fun y' hy' => (Finset.mem_singleton.1 hy') ▸ hN)
    refine ⟨hN _ (ENat.natCast_toNat_le_self _) t, fun htop => ?_⟩
    -- D4.4.8: the bound holds for every `N`, and `e^{-cN} → 0`.
    have hlim : Filter.Tendsto (fun N : ℕ => C * ‖A‖ * ‖B‖ * Real.exp (v * |t|) *
        Real.exp (-(c * N))) Filter.atTop (nhds 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc)).const_mul
          (C * ‖A‖ * ‖B‖ * Real.exp (v * |t|))
    have hle := ge_of_tendsto' hlim fun N => (hN N (htop ▸ le_top) t).trans_eq (by
      rw [sub_eq_add_neg, Real.exp_add]; ring)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)
  · have hτ : ‖τ (hamiltonian Λ Φ) t A‖ = ‖A‖ := norm_τ (isHermitian_hamiltonian G hΦ) t A
    rw [mul_min_of_nonneg _ _ (norm_nonneg A)]
    refine le_min ?_ ?_
    · -- D4.4.11
      calc _ ≤ ‖τ (hamiltonian Λ Φ) t A‖ + ‖E G Λ a l (τ (hamiltonian Λ Φ) t A)‖ :=
            norm_sub_le _ _
        _ ≤ ‖A‖ + ‖A‖ := add_le_add hτ.le ((norm_E_le _ _ _ _).trans hτ.le)
        _ = ‖A‖ * 2 := by ring
    · -- D4.4.9–10: `B = τ_t(A)` against the contractions `U` on `Y = Λ \ N_l(a)`
      refine norm_sub_condExpect_le (graphNbhd_subset G Λ {a} l) _ _ fun U hU hU1 => ?_
      calc _ ≤ 2 * Real.exp (c * R) * ‖A‖ * ‖U‖ *
            Real.exp (2 * (V R * J * μ V R) * Real.exp (c * R) * |t| - c * (l + 1 : ℕ)) :=
            norm_commutator_le_of_le G V hV R J hc.le hΦ hX ha hA Finset.sdiff_subset hU (l + 1)
              (fun y hy => le_domainEDist_of_mem_sdiff G hy) t
        _ ≤ 2 * Real.exp (c * R) * ‖A‖ * 1 *
            Real.exp (2 * (V R * J * μ V R) * Real.exp (c * R) * |t| - c * l) := by
            gcongr
            linarith
        _ = ‖A‖ * (C * Real.exp (v * |t| - c * l)) := by ring

end LR

end AreaLaw

