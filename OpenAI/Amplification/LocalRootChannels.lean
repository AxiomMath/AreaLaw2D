/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,
`TNLean/PEPS/AreaLaw/Amplification/LocalRootChannels.lean` (Apache 2.0).  Adaptations:
QICLean `rootChannel` is `Matrix.rootChannel` (OpenAI/RootChannel.lean);
`spectatorRootChannel` is stated for operators on any finite index type `n`, not only on
`ι → Fin q`; the localized channels live on a region `T : Finset σ`, with TNLean
`siteExpectation q K` replaced by `OpenAI.condExpect (h : K ⊆ T)`, so `localRootChannel` takes
`h : K ⊆ T` and `localRootChannelShell` takes, besides `regions : ℕ → Finset σ`, the proof
`hregions : ∀ l, regions l ⊆ T`; `supportedOperators q K` is `OpenAI.IsSupportedOn h` and
`supportedOperators q Kᶜ` is `IsSupportedOn (Finset.sdiff_subset : T \ K ⊆ T)`; `[NeZero q]`
is `[∀ i, Nonempty (loc i)]`; TNLean `sqrt_mem_supportedOperators` is
`OpenAI.IsSupportedOn.cfcSqrt`.  The field is `ℂ`, as for `Matrix.rootChannel`.
-/
import OpenAI.RootChannel
import OpenAI.SiteExpectationOrder

/-!
# Local root channels and their shells, with spectators

For a positive contraction `k` the root channel `B ↦ G B G + K B K` with `G = √(1 - k)`,
`K = √k`, both tensored with the identity on a finite spectator, is a contraction.  Its local
version replaces `k` by the conditional expectation `E_S(k)` onto `S ⊆ T`; the error
`‖k - E_S(k)‖ ≤ ε` bounds the distance of the two channels by `4 √ε`, uniformly in the
spectator [OAI265, Lemma 4.4].  The local channel fixes the commutant of the operators on `S`
and intertwines commutators with it.

For a sequence of regions the zeroth shell is the first local channel minus the identity and
the successor shells are the differences of consecutive local channels
[OAI265, §10.1, eq. (10.7)].  They are bounded by the localization errors, and for nested
regions each shell vanishes on the commutant of the operators on its region.

## Main definitions

* `OpenAI.spectatorRootChannel`, `OpenAI.localRootChannel`, `OpenAI.localRootChannelShell`.

## Main statements

* `OpenAI.norm_spectatorRootChannel_sub_localRootChannel_le`: the `4 √ε` estimate.
* `OpenAI.localRootChannel_eq_self_of_forall_commute`,
  `OpenAI.localRootChannel_commutator`.
* `OpenAI.norm_localRootChannelShell_zero_le`, `OpenAI.norm_localRootChannelShell_succ_le`,
  `OpenAI.localRootChannelShell_eq_zero_of_forall_commute`.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace OpenAI

open Arealaw Matrix

section Root

variable {n Aux : Type*} [Fintype n] [DecidableEq n] [Fintype Aux] [DecidableEq Aux]

/-- The root channel of `√(1 - k)` and `√k`, extended by the identity on a finite spectator
[OAI265, Lemma 4.4]. -/
noncomputable def spectatorRootChannel (k : Matrix n n ℂ) (B : Matrix (n × Aux) (n × Aux) ℂ) :
    Matrix (n × Aux) (n × Aux) ℂ :=
  rootChannel (CFC.sqrt (1 - k) ⊗ₖ (1 : Matrix Aux Aux ℂ)) (CFC.sqrt k ⊗ₖ (1 : Matrix Aux Aux ℂ))
    B

theorem spectatorRootChannel_sub (k : Matrix n n ℂ) (B C : Matrix (n × Aux) (n × Aux) ℂ) :
    spectatorRootChannel k (B - C) = spectatorRootChannel k B - spectatorRootChannel k C := by
  simp only [spectatorRootChannel, rootChannel, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The root channel of a positive contraction is a contraction for every finite spectator
[OAI265, Lemma 4.4]. -/
theorem norm_spectatorRootChannel_le {k : Matrix n n ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix (n × Aux) (n × Aux) ℂ) : ‖spectatorRootChannel k B‖ ≤ ‖B‖ :=
  norm_rootChannel_kronecker_le (CFC.sqrt_nonneg (1 - k)).isSelfAdjoint
    (CFC.sqrt_nonneg k).isSelfAdjoint (sqrt_one_sub_mul_add_sqrt_mul hk₀ hk₁) B

/-- The root channels of two positive contractions differ by at most
`4 √‖k - k'‖`, uniformly in the spectator. -/
private theorem norm_spectatorRootChannel_sub_le {k k' : Matrix n n ℂ} (hk₀ : 0 ≤ k)
    (hk₁ : k ≤ 1) (hk'₀ : 0 ≤ k') (hk'₁ : k' ≤ 1) {ε : ℝ} (hε : ‖k - k'‖ ≤ ε)
    (B : Matrix (n × Aux) (n × Aux) ℂ) :
    ‖spectatorRootChannel k B - spectatorRootChannel k' B‖ ≤ 4 * Real.sqrt ε * ‖B‖ := by
  have hsqrt {a : Matrix n n ℂ} (ha : a ≤ 1) : ‖CFC.sqrt a‖ ≤ 1 :=
    l2_opNorm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) (sqrt_le_one ha)
  have hG := hsqrt (sub_le_self 1 hk₀)
  have hKr := hsqrt hk₁
  have hGl := hsqrt (sub_le_self 1 hk'₀)
  have hKl := hsqrt hk'₁
  have htG : ‖CFC.sqrt (1 - k) - CFC.sqrt (1 - k')‖ ≤ Real.sqrt ε :=
    (norm_sqrt_one_sub_sub_le hk₁ hk'₁).trans (Real.sqrt_le_sqrt hε)
  have htK : ‖CFC.sqrt k - CFC.sqrt k'‖ ≤ Real.sqrt ε :=
    (norm_sqrt_sub_le hk₀ hk'₀).trans (Real.sqrt_le_sqrt hε)
  refine (norm_rootChannel_kronecker_sub_le _ _ _ _ B).trans ?_
  have h₁ : (‖CFC.sqrt (1 - k)‖ + ‖CFC.sqrt (1 - k')‖) *
      ‖CFC.sqrt (1 - k) - CFC.sqrt (1 - k')‖ ≤ 2 * Real.sqrt ε :=
    mul_le_mul (by linarith) htG (norm_nonneg _) (by norm_num)
  have h₂ : (‖CFC.sqrt k‖ + ‖CFC.sqrt k'‖) * ‖CFC.sqrt k - CFC.sqrt k'‖ ≤
      2 * Real.sqrt ε :=
    mul_le_mul (by linarith) htK (norm_nonneg _) (by norm_num)
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg B)

end Root

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {K L T : Finset σ}
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The local root channel: the root channel of `E_K(k)`, with a spectator identity
[OAI265, §10.1, the channels `ℰ_{i,l}` before eq. (10.7)]. -/
noncomputable def localRootChannel (h : K ⊆ T) (k : Matrix (Reg loc T) (Reg loc T) ℂ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ :=
  spectatorRootChannel (condExpect h k) B

theorem localRootChannel_sub (h : K ⊆ T) (k : Matrix (Reg loc T) (Reg loc T) ℂ)
    (B C : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    localRootChannel h k (B - C) = localRootChannel h k B - localRootChannel h k C :=
  spectatorRootChannel_sub _ B C

section Nonempty

variable [∀ i, Nonempty (loc i)]

/-- The local root channel is a contraction, uniformly in the spectator
[OAI265, §10.1, before eq. (10.7)]. -/
theorem norm_localRootChannel_le (h : K ⊆ T) {k : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannel h k B‖ ≤ ‖B‖ :=
  norm_spectatorRootChannel_le (condExpect_nonneg h hk₀) (condExpect_le_one h hk₁) B

/-- The error `‖k - E_K(k)‖ ≤ ε` gives the completely bounded estimate `4 √ε` between the full
and the local root channel [OAI265, Lemma 4.4]. -/
theorem norm_spectatorRootChannel_sub_localRootChannel_le (h : K ⊆ T)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) {ε : ℝ}
    (hε : ‖k - condExpect h k‖ ≤ ε) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖spectatorRootChannel k B - localRootChannel h k B‖ ≤ 4 * Real.sqrt ε * ‖B‖ :=
  norm_spectatorRootChannel_sub_le hk₀ hk₁ (condExpect_nonneg h hk₀)
    (condExpect_le_one h hk₁) hε B

/-- The local roots `√(1 - E_K(k))` and `√(E_K(k))` are supported on `K`. -/
private theorem isSupportedOn_localRoots (h : K ⊆ T) {k : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) :
    IsSupportedOn h (CFC.sqrt (1 - condExpect h k)) ∧
      IsSupportedOn h (CFC.sqrt (condExpect h k)) :=
  ⟨((isSupportedOn_one h).sub (isSupportedOn_condExpect h k)).cfcSqrt
      (sub_nonneg.mpr (condExpect_le_one h hk₁)),
    (isSupportedOn_condExpect h k).cfcSqrt (condExpect_nonneg h hk₀)⟩

/-- The local channel fixes every operator commuting with the operators on `K`, also when it
acts on the spectator [OAI265, §10.1, after eq. (10.7)]. -/
theorem localRootChannel_eq_self_of_forall_commute (h : K ⊆ T)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ}
    (hB : ∀ A : Matrix (Reg loc T) (Reg loc T) ℂ, IsSupportedOn h A →
      Commute (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) B) : localRootChannel h k B = B := by
  have hl₀ := condExpect_nonneg h hk₀
  have hl₁ := condExpect_le_one h hk₁
  obtain ⟨hG, hK⟩ := isSupportedOn_localRoots h hk₀ hk₁
  exact rootChannel_eq_self_of_commute
    (rootChannel_kronecker_hyp (sqrt_one_sub_mul_add_sqrt_mul hl₀ hl₁)) (hB _ hG) (hB _ hK)

/-- The local channel intertwines the commutator with any operator commuting with the operators
on `K` [OAI265, §10.1, before eq. (10.9)]. -/
theorem localRootChannel_commutator_of_forall_commute (h : K ⊆ T)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {A : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ}
    (hA : ∀ C : Matrix (Reg loc T) (Reg loc T) ℂ, IsSupportedOn h C →
      Commute (C ⊗ₖ (1 : Matrix Aux Aux ℂ)) A)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    A * localRootChannel h k B - localRootChannel h k B * A =
      localRootChannel h k (A * B - B * A) := by
  obtain ⟨hGs, hKs⟩ := isSupportedOn_localRoots h hk₀ hk₁
  have hG := hA _ hGs
  have hKr := hA _ hKs
  have hleft (R : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ)
      (hR : Commute R A) : R * (A * B) * R = A * (R * B * R) := by
    rw [hR.left_comm, mul_assoc]
  have hright (R : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ)
      (hR : Commute R A) : R * (B * A) * R = R * B * R * A := by
    rw [← mul_assoc, hR.symm.right_comm]
  simp only [localRootChannel, spectatorRootChannel, rootChannel, mul_sub, sub_mul,
    hleft _ hG, hleft _ hKr, hright _ hG, hright _ hKr, mul_add, add_mul]
  abel

/-- The local channel intertwines the commutator with an operator supported on `T \ K`, in
particular with every on-site unitary outside `K` [OAI265, §10.1, before eq. (10.9)]. -/
theorem localRootChannel_commutator (h : K ⊆ T) {k : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) {U : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hU : IsSupportedOn (Finset.sdiff_subset : T \ K ⊆ T) U)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * localRootChannel h k B -
        localRootChannel h k B * (U ⊗ₖ 1) =
      localRootChannel h k ((U ⊗ₖ 1) * B - B * (U ⊗ₖ 1)) := by
  apply localRootChannel_commutator_of_forall_commute h hk₀ hk₁
  intro C hC
  change (C ⊗ₖ 1) * (U ⊗ₖ 1) = (U ⊗ₖ 1) * (C ⊗ₖ 1)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    (hC.commute hU Finset.disjoint_sdiff).eq]

/-- The zeroth shell has norm at most two [OAI265, §10.1, eq. (10.7) for `l = 0`]. -/
theorem norm_localRootChannel_sub_self_le (h : K ⊆ T) {k : Matrix (Reg loc T) (Reg loc T) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannel h k B - B‖ ≤ 2 * ‖B‖ := by
  have hB := norm_localRootChannel_le h hk₀ hk₁ B
  calc
    ‖localRootChannel h k B - B‖ ≤ ‖localRootChannel h k B‖ + ‖B‖ := norm_sub_le _ _
    _ ≤ ‖B‖ + ‖B‖ := add_le_add hB le_rfl
    _ = 2 * ‖B‖ := (two_mul _).symm

/-- Two local channels of the same `k` are close by their localization errors; the regions
need not be nested [OAI265, §10.1, eq. (10.7)]. -/
theorem norm_localRootChannel_sub_localRootChannel_le (hK : K ⊆ T) (hL : L ⊆ T)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) {εK εL : ℝ}
    (hεK : ‖k - condExpect hK k‖ ≤ εK) (hεL : ‖k - condExpect hL k‖ ≤ εL)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannel hK k B - localRootChannel hL k B‖ ≤
      4 * (Real.sqrt εK + Real.sqrt εL) * ‖B‖ := by
  calc
    ‖localRootChannel hK k B - localRootChannel hL k B‖ ≤
        ‖localRootChannel hK k B - spectatorRootChannel k B‖ +
          ‖spectatorRootChannel k B - localRootChannel hL k B‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖spectatorRootChannel k B - localRootChannel hK k B‖ +
          ‖spectatorRootChannel k B - localRootChannel hL k B‖ := by rw [norm_sub_rev]
    _ ≤ 4 * Real.sqrt εK * ‖B‖ + 4 * Real.sqrt εL * ‖B‖ :=
      add_le_add (norm_spectatorRootChannel_sub_localRootChannel_le hK hk₀ hk₁ hεK B)
        (norm_spectatorRootChannel_sub_localRootChannel_le hL hk₀ hk₁ hεL B)
    _ = 4 * (Real.sqrt εK + Real.sqrt εL) * ‖B‖ := by ring

end Nonempty

/-- The channel shells `Δ₀ = ℰ₀ - id` and `Δ_{l+1} = ℰ_{l+1} - ℰ_l` of the local root channels
of a sequence of regions [OAI265, §10.1, eq. (10.7)]. -/
noncomputable def localRootChannelShell (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (k : Matrix (Reg loc T) (Reg loc T) ℂ) (l : ℕ)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ :=
  match l with
  | 0 => localRootChannel (hregions 0) k B - B
  | l + 1 => localRootChannel (hregions (l + 1)) k B - localRootChannel (hregions l) k B

theorem localRootChannelShell_sub (regions : ℕ → Finset σ) (hregions : ∀ l, regions l ⊆ T)
    (k : Matrix (Reg loc T) (Reg loc T) ℂ) (l : ℕ)
    (B C : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    localRootChannelShell regions hregions k l (B - C) =
      localRootChannelShell regions hregions k l B -
        localRootChannelShell regions hregions k l C := by
  cases l <;> simp only [localRootChannelShell, localRootChannel_sub] <;> abel

section Nonempty

variable [∀ i, Nonempty (loc i)]

/-- The zeroth shell has completely bounded norm at most two
[OAI265, §10.1, eq. (10.7) for `l = 0`]. -/
theorem norm_localRootChannelShell_zero_le (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k)
    (hk₁ : k ≤ 1) (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannelShell regions hregions k 0 B‖ ≤ 2 * ‖B‖ :=
  norm_localRootChannel_sub_self_le (hregions 0) hk₀ hk₁ B

/-- A successor shell is bounded by the two localization errors, uniformly in the spectator
[OAI265, §10.1, eq. (10.7)]. -/
theorem norm_localRootChannelShell_succ_le (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k)
    (hk₁ : k ≤ 1) (l : ℕ) {εNext εPrev : ℝ}
    (hNext : ‖k - condExpect (hregions (l + 1)) k‖ ≤ εNext)
    (hPrev : ‖k - condExpect (hregions l) k‖ ≤ εPrev)
    (B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ) :
    ‖localRootChannelShell regions hregions k (l + 1) B‖ ≤
      4 * (Real.sqrt εNext + Real.sqrt εPrev) * ‖B‖ :=
  norm_localRootChannel_sub_localRootChannel_le _ _ hk₀ hk₁ hNext hPrev B

/-- For nested regions a shell vanishes on the commutant of the operators on its region, with
arbitrary spectators [OAI265, §10.1, after eq. (10.7)]. -/
theorem localRootChannelShell_eq_zero_of_forall_commute (regions : ℕ → Finset σ)
    (hregions : ∀ l, regions l ⊆ T) (hmono : Monotone regions)
    {k : Matrix (Reg loc T) (Reg loc T) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (l : ℕ)
    {B : Matrix (Reg loc T × Aux) (Reg loc T × Aux) ℂ}
    (hB : ∀ A : Matrix (Reg loc T) (Reg loc T) ℂ, IsSupportedOn (hregions l) A →
      Commute (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) B) :
    localRootChannelShell regions hregions k l B = 0 := by
  cases l with
  | zero =>
    exact sub_eq_zero.mpr (localRootChannel_eq_self_of_forall_commute _ hk₀ hk₁ hB)
  | succ l =>
    have hPrev : ∀ A : Matrix (Reg loc T) (Reg loc T) ℂ, IsSupportedOn (hregions l) A →
        Commute (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) B := fun A hA =>
      hB A (hA.mono (hmono (Nat.le_succ l)) _)
    simp only [localRootChannelShell,
      localRootChannel_eq_self_of_forall_commute _ hk₀ hk₁ hB,
      localRootChannel_eq_self_of_forall_commute _ hk₀ hk₁ hPrev, sub_self]

end Nonempty

end OpenAI
