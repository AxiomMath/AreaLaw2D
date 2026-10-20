import AreaLawRefactored.S08_Comparators.Setup

/-!
# §8 Statements shared between the subsection files

The anchors of §8 that are consumed by another subsection file, stated as `Prop`s, so that each
file is proved against the statement of the anchors it cites (the files are written in
parallel). `Proposition.lean` discharges every one of them with the declaration of its anchor.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

/-- D8.1, Output. (iii) Within one leaf, the regions `U_{j,g}, U_{j,g}Y_{j,g}, Y_{j,g}` of any two
bands are nested or disjoint (so all their labels commute, Lemma 6.1 (2)). (ii) Band factors of
different bands commute, at any two leaves: `[A_{j,g}, A_{j',g'}] = 0` for `g ≠ g'` (the
hypothesis of Lemma 7.1 (6)). -/
def Step_8_1 : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {K : ℕ} {St : Type v} {X : Finset σ}
    (Γ : Statuses σ K St X),
    (∀ (s : St) (g g' : Fin K),
      ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g, Γ.Y s g} : Finset (Finset σ)),
      ∀ Q' ∈ ({Γ.U s g', Γ.U s g' ∪ Γ.Y s g', Γ.Y s g'} : Finset (Finset σ)),
        Q ⊆ Q' ∨ Q' ⊆ Q ∨ Disjoint Q Q') ∧
    ∀ (n : σ → ℕ) [∀ v, NeZero (n v)] (d : ℕ) [NeZero d] (t : ℝ), 0 ≤ t →
      ∀ (k : ℕ) (s s' : St) (g g' : Fin K), g ≠ g' →
        Commute (Γ.bandA n d t k s g) (Γ.bandA n d t k s' g')

/-- D8.10 (`comparator:signed-label-moments`), for an iid density `ρ^{⊗k}` on `k` copies of a
fixed finite system with `log Tr ρ^{1-u} ≤ u S + C₀ 𝓑 u²` for `|u| ≤ c₀/√𝓑` (`𝓑 ≥ 1`), `F` its
label observable: for `0 ≤ u ≤ c/√𝓑`,
`log E exp{± u (F - k S)} ≤ 2 C₀ k 𝓑 u² + O(log(k + 1))`; only the `O(log(k + 1))` term depends
on the system. -/
def Step_8_10 : Prop :=
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ → ∃ c : ℝ, 0 < c ∧
    ∀ {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef),
      ρ.trace = 1 → ∀ 𝓑 S : ℝ, 1 ≤ 𝓑 →
      (∀ u : ℝ, |u| ≤ c₀ / Real.sqrt 𝓑 → Real.log (trPowPos ρ hρ.isHermitian u) ≤
        u * S + C₀ * 𝓑 * u ^ 2) →
      ∃ Cp Np : ℝ, ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ c / Real.sqrt 𝓑 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        Real.log (trace (TensorPower.tensorPow (k := k) ρ *
            cfc (fun x => Real.exp (ε * u * (x - k * S)))
              (labelObservable (TensorPower.copyPerm Ω k) fun l => Real.log l.dim))).re ≤
          2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1)

/-- D8.11. The Schmidt decomposition `Ω̃ = ∑_i √p_i |i⟩_X |w_i⟩` across `X | X^c` (`|i⟩_X` the
eigenbasis of `ρ_X`, `p_i ≥ 0`, `∑ p_i = 1`); `w_i` ignores the `X`-part, and the `w_i` with
`p_i > 0` are orthonormal on `X^c` (sums over all physical configurations count each
`X^c`-configuration `dim 𝓗_X` times). -/
def Step_8_11 : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} (D : PhysData n) (X : Finset σ),
    (∀ x : SiteConfig n, D.Ω x = ∑ i, (Real.sqrt (D.p X i) : ℂ) *
      schmidtX (D := D) i (restrictX x) * schmidtW (D := D) i x) ∧
    (∀ (i : Reg (fun v => Fin (n v)) X) (x : SiteConfig n) (y : Reg (fun v => Fin (n v)) X),
      schmidtW (D := D) i (replaceX x y) = schmidtW (D := D) i x) ∧
    (∀ i j, 0 < D.p X i → 0 < D.p X j →
      ∑ x : SiteConfig n, star (schmidtW (D := D) i x) * schmidtW (D := D) j x =
        if i = j then (dimReg n X : ℂ) else 0) ∧
    (∀ i, 0 ≤ D.p X i) ∧ ∑ i, D.p X i = 1

/-- D8.12 (`comparator:high-label`). Every typical set has a high label sequence. -/
def Step_8_12 : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] {D : PhysData n}
    {X : Finset σ} (E : TypicalSet D X), ∃ l, HighLabel E l

/-- D8.13. For a high label sequence: `pre_k ∈ 𝒮_k` is nonzero with `‖pre_k‖ ≤ 1`, an
eigenvector of `\overline{H̃}` of eigenvalue `Ẽ₀` (`k ≥ 1`) with label `λ_k` on `C` and on `R`,
and every `A_{j,g}` (hence every root `𝓜`) commutes with the label projectors `π^{λ_k}_C`,
`π^{λ_k}_R`. -/
def Step_8_13 : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
    {X : Finset σ} (E : TypicalSet D X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))),
    HighLabel E l → ∀ k : ℕ,
      pre D E.d k (l k) ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧ pre D E.d k (l k) ≠ 0 ∧
      (star (pre D E.d k (l k)) ⬝ᵥ pre D E.d k (l k)).re ≤ 1 ∧
      (0 < k → Hbar D E.d k *ᵥ pre D E.d k (l k) = (D.E₀ : ℂ) • pre D E.d k (l k)) ∧
      piC E.d k (l k) *ᵥ pre D E.d k (l k) = pre D E.d k (l k) ∧
      piR E.d k (l k) *ᵥ pre D E.d k (l k) = pre D E.d k (l k) ∧
      ∀ {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St] (Γ : Statuses σ K St X) (t : ℝ),
        0 ≤ t → (∀ s g, Commute (Γ.bandA n E.d t k s g) (piC E.d k (l k)) ∧
          Commute (Γ.bandA n E.d t k s g) (piR E.d k (l k))) ∧
        ∀ T : Transport.MeanTree St, Commute (Γ.root n E.d T t k) (piC E.d k (l k)) ∧
          Commute (Γ.root n E.d T t k) (piR E.d k (l k))

/-- D8.15 (`comparator:pin-norm`).
`N² ≥ (z/d_*²)^k ‖𝓜^{-s} π^λ_R post_k‖²` for every tree, label and `k`. -/
def Step_8_15 : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
    {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
    (Γ : Statuses σ K St X) (T : Transport.MeanTree St) (a : ℝ), 0 ≤ a →
    ∀ (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))),
      (E.z / E.d ^ 2) ^ k *
          Matrix.Transport.filteredNormSq (Γ.root n E.d T (a / 2) k) (piR E.d k l *ᵥ post E k) ≤
        N2 D Γ E T a k l

/-- D8.16 (`comparator:pinned-metric`). On the pinned symmetric range
(`φ ∈ 𝒮_k`, `𝖯 φ = φ`) `A_{j,g}` acts as `Ã_{j,g} = (W_U^{-1} W_{UY}^{-1} W_Y)²`, which is positive
definite, preserves the pinned symmetric range, commutes with the other bands' `Ã` of the same
leaf, and has `log Ã_{j,g} = a (F_U + F_{UY} - F_Y) + O(log(k + 1))` in operator norm. -/
def Step_8_16 : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] {D : PhysData n}
    {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} (Γ : Statuses σ K St X),
    (∀ (t : ℝ), 0 ≤ t → ∀ (k : ℕ) (s : St) (g : Fin K),
      (∀ φ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k, pinProj E k *ᵥ φ = φ →
        Γ.bandA n E.d t k s g *ᵥ φ = Γ.Atil n E.d t k s g *ᵥ φ ∧
        Γ.Atil n E.d t k s g *ᵥ φ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧
        pinProj E k *ᵥ (Γ.Atil n E.d t k s g *ᵥ φ) = Γ.Atil n E.d t k s g *ᵥ φ) ∧
      (Γ.Atil n E.d t k s g).PosDef ∧
        ∀ g', Commute (Γ.Atil n E.d t k s g) (Γ.Atil n E.d t k s g')) ∧
    ∀ t : ℝ, 0 < t → t < 1 / 2 → ∃ C : ℝ, ∀ (k : ℕ) (s : St) (g : Fin K),
      ‖cfc Real.log (Γ.Atil n E.d t k s g) - ((2 * t : ℝ) : ℂ) •
          (Replicas.F (fun f => Fin (dims n E.d f)) k (physReg (Γ.U s g)) +
            Replicas.F (fun f => Fin (dims n E.d f)) k (physReg (Γ.U s g ∪ Γ.Y s g)) -
            Replicas.F (fun f => Fin (dims n E.d f)) k (physReg (Γ.Y s g)))‖ ≤
        C * Real.log ((k : ℝ) + 2)

/-- D8.20 (`comparator:rough-upper`). -/
def Step_8_20 : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
      {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
      (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))), HighLabel E l →
      ∀ (𝓡 : Finset (Finset σ)) (Bsh Bexc : ℝ), PrefixData D Γ 𝓡 Bsh Bexc →
      ∀ a : ℝ, 0 < a → a ≤ a₀ → RoughUpper D Γ E a l Bsh Bexc

/-- D8.22 (`comparator:sharp-upper`). -/
def Step_8_22 : Prop :=
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
      {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
      (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))), HighLabel E l →
      ∀ 𝓑 : ℝ, MgfData D Γ C₀ c₀ 𝓑 → ∀ a : ℝ, 0 < a → a ≤ c / Real.sqrt 𝓑 →
        SharpUpper D Γ E C a 𝓑 l

/-- D8.31 (`comparator:inverse-compression`, `comparator:lower-pin`). For `0 < τ < 1/2` and the
low-defect projection `Π` on the auxiliary sector of a high label sequence:
`A_{j,g} ≥ exp{k a L_{j,g} - o(k)} Π`, with
`L_{j,g} = 2S' - C(τ log d_* + h(τ)/a)` (rough, `C` universal) and
`L_{j,g} = 2S' + (1 - τ) g^pre_{j,g} - C(τ log d_* + h(τ)/a + a 𝓑)` (sharp, `C` depending on
`C₀, c₀`). -/
def Step_8_31 : Prop :=
  ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧
    (∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
      {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
      (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))), HighLabel E l →
      ∀ a τ : ℝ, 0 < a → a ≤ a₀ → 0 < τ → τ < 1 / 2 →
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ (k : ℕ) (s : St) (g : Fin K),
        Real.exp (k * a * (2 * E.S' - C * (τ * Real.log E.d + Real.binEntropy τ / a)) -
            k * δ k) • lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g) ∧
    ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ → ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
      {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
      (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))), HighLabel E l →
      ∀ 𝓑 : ℝ, MgfData D Γ C₀ c₀ 𝓑 → ∀ a τ : ℝ, 0 < a → a ≤ c / Real.sqrt 𝓑 → 0 < τ →
      τ < 1 / 2 →
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ (k : ℕ) (s : St) (g : Fin K),
        Real.exp (k * a * (2 * E.S' + (1 - τ) * gpre D Γ s g -
              C' * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑)) -
            k * δ k) • lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g

/-- D8.35 (`comparator:rough-lower`, `comparator:sharp-lower`). -/
def Step_8_35 : Prop :=
  ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧
    (∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
      {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
      (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))), HighLabel E l →
      ∀ a τ : ℝ, 0 < a → a ≤ a₀ → 0 < τ → τ < 1 / 2 → RoughLower D Γ E C a τ l) ∧
    ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ → ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
      {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Fintype St] [DecidableEq St]
      (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))), HighLabel E l →
      ∀ 𝓑 : ℝ, MgfData D Γ C₀ c₀ 𝓑 → ∀ a τ : ℝ, 0 < a → a ≤ c / Real.sqrt 𝓑 → 0 < τ →
      τ < 1 / 2 → SharpLower D Γ E C' a τ 𝓑 l

end AreaLaw.Comparators
