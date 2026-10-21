import AreaLawRefactored.S07_Transport

/-!
# §8 Norm comparisons from an auxiliary pair: the objects (§8.0, D8.1–D8.7, D8.11, D8.23)

Digest `digest/08-comparators.md`, paper `paper/sections/07-comparators.tex`. No geometry: the
physical system is `⨂_{v : σ} ℂ^{n_v}` over an arbitrary finite site type `σ`; the extended
system `𝒱 = 𝓗_phys ⊗ 𝓗_C ⊗ 𝓗_R` has the tensor factors `Site σ` (the physical sites and the two
auxiliary factors `C`, `R`, each of dimension `d_* = |E|`). Every §6/§7 object is used on
`Site σ` with local dimensions `dims n d`: Schur labels and metrics (`Replicas.π`, `Replicas.F`,
`Replicas.W`), band metrics `Transport.bandMetric` (written `Π_k A + (1 − Π_k)` on the whole
tensor space, D7.8) and mean trees `Transport.MeanTree`. Entropies are those of the statement
encoding (`Reg`, `pureState`, `regionEntropy`, `mutualInfo`).
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation
open OpenAI (pureState)

namespace AreaLaw.Comparators

universe u v

/-! ## D8.6 The tensor factors of `𝒱` -/

/-- D8.6. The tensor factors of `𝒱 = 𝓗_phys ⊗ 𝓗_C ⊗ 𝓗_R`. -/
inductive Site (σ : Type u) : Type u where
  /-- A physical site. -/
  | phys (v : σ) : Site σ
  /-- The auxiliary factor `C`. -/
  | C : Site σ
  /-- The auxiliary factor `R`. -/
  | R : Site σ
  deriving DecidableEq, Fintype

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- D8.6. Local dimensions of `𝒱`: `n_v` at a physical site, `d_*` at `C` and at `R`. -/
def dims (n : σ → ℕ) (d : ℕ) : Site σ → ℕ
  | .phys v => n v
  | .C => d
  | .R => d

instance (n : σ → ℕ) (d : ℕ) [∀ v, NeZero (n v)] [NeZero d] (s : Site σ) :
    NeZero (dims n d s) := by
  cases s <;> simp only [dims] <;> infer_instance

/-- A physical region as a set of tensor factors of `𝒱`. -/
def physReg (Q : Finset σ) : Finset (Site σ) :=
  Q.map ⟨Site.phys, fun _ _ h => Site.phys.inj h⟩

/-- The physical part of a basis configuration of `𝒱`. -/
def physPart {n : σ → ℕ} {d : ℕ} (x : SiteConfig (dims n d)) : SiteConfig n :=
  fun v => x (.phys v)

/-- `Tr A^{1-u}` over the positive eigenvalues of a Hermitian `A`. -/
noncomputable def trPowPos {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ)
    (hA : A.IsHermitian) (u : ℝ) : ℝ :=
  ∑ i, if 0 < hA.eigenvalues i then hA.eigenvalues i ^ (1 - u) else 0

/-! ## D8.1 Physical data, statuses, nesting -/

/-- D8.1. A normalized pure vector `Ω̃` on `𝓗_phys = ⨂_v ℂ^{n_v}`, the unique ground vector of
a positive Hamiltonian `H̃` with ground energy `Ẽ₀` and gap `g̃ > 0`
(`H̃ - Ẽ₀ ≥ g̃ (1 - |Ω̃⟩⟨Ω̃|)`). -/
structure PhysData (n : σ → ℕ) where
  /-- `Ω̃`. -/
  Ω : SiteConfig n → ℂ
  /-- `H̃`. -/
  H : Matrix (SiteConfig n) (SiteConfig n) ℂ
  /-- `Ẽ₀`. -/
  E₀ : ℝ
  /-- `g̃`. -/
  g : ℝ
  norm_Ω : star Ω ⬝ᵥ Ω = 1
  nonneg : 0 ≤ H
  ground : H *ᵥ Ω = (E₀ : ℂ) • Ω
  gap_pos : 0 < g
  gap : (g : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤ H - (E₀ : ℂ) • 1

/-- D8.1. A status collection: finitely many allowed statuses `s : St`, each a family of `K`
partitions `𝓗_phys = 𝓗_X ⊗ 𝓗_{U_g} ⊗ 𝓗_{Y_g} ⊗ 𝓗_{V_g}` with the fixed `X`, and the nesting
(`comparator:nesting`) `X U_g Y_g ⊆ X U_{g'}` for every two statuses and every `g < g'`. -/
structure Statuses (σ : Type u) [Fintype σ] [DecidableEq σ] (K : ℕ) (St : Type v)
    (X : Finset σ) where
  /-- `U_g`. -/
  U : St → Fin K → Finset σ
  /-- `Y_g`. -/
  Y : St → Fin K → Finset σ
  /-- `V_g`. -/
  V : St → Fin K → Finset σ
  disjoint_XU : ∀ s g, Disjoint X (U s g)
  disjoint_XY : ∀ s g, Disjoint X (Y s g)
  disjoint_XV : ∀ s g, Disjoint X (V s g)
  disjoint_UY : ∀ s g, Disjoint (U s g) (Y s g)
  disjoint_UV : ∀ s g, Disjoint (U s g) (V s g)
  disjoint_YV : ∀ s g, Disjoint (Y s g) (V s g)
  cover : ∀ s g, X ∪ U s g ∪ Y s g ∪ V s g = Finset.univ
  nesting : ∀ s s' g g', g < g' → X ∪ U s g ∪ Y s g ⊆ X ∪ U s' g'

namespace PhysData

variable {n : σ → ℕ} (D : PhysData n)

theorem norm_Ω_univEquiv : star (D.Ω ∘ univEquiv) ⬝ᵥ (D.Ω ∘ univEquiv) = 1 := by
  rw [← D.norm_Ω]
  exact univEquiv.sum_comp fun x => star (D.Ω x) * D.Ω x

/-- The pure state `|Ω̃⟩⟨Ω̃|` on `Reg (Fin ∘ n) univ`. -/
noncomputable def state : MState (Reg (fun v => Fin (n v)) Finset.univ) ℂ :=
  pureState (D.Ω ∘ univEquiv) D.norm_Ω_univEquiv

/-- `S(Q)`, the entropy of the marginal of `Ω̃` on `Q`. -/
noncomputable def S (Q : Finset σ) : ℝ :=
  D.state.toSubState.regionEntropy (Finset.subset_univ Q)

/-- `I(Q : Q')` in `Ω̃`, for disjoint `Q, Q'`. -/
noncomputable def I (Q Q' : Finset σ) : ℝ :=
  D.state.toSubState.mutualInfo (Finset.subset_univ Q) (Finset.subset_univ Q')

/-- `ρ_Q`, the marginal of `Ω̃` on `Q`. -/
noncomputable def ρ (Q : Finset σ) :
    Matrix (Reg (fun v => Fin (n v)) Q) (Reg (fun v => Fin (n v)) Q) ℂ :=
  marg (D.Ω ∘ univEquiv) (Finset.subset_univ Q)

theorem isHermitian_ρ (Q : Finset σ) : (D.ρ Q).IsHermitian := isHermitian_marg _ _

/-- The eigenvalues of `ρ_Q`; for `Q = X` the Schmidt coefficients `p_i` of `Ω̃` across `X|X^c`. -/
noncomputable def p (Q : Finset σ) : Reg (fun v => Fin (n v)) Q → ℝ :=
  (D.isHermitian_ρ Q).eigenvalues

/-- `Tr ρ_Q^{1-u}` over the positive eigenvalues. -/
noncomputable def trPow (Q : Finset σ) (u : ℝ) : ℝ := trPowPos (D.ρ Q) (D.isHermitian_ρ Q) u

end PhysData

/-! ## D8.2 Typical Schmidt set -/

/-- D8.2 (`comparator:typical-set`). A nonempty set `E` of Schmidt indices of `X` with
`e^{-S_X - w} ≤ p_i ≤ e^{-S_X + w}` for `i ∈ E`, `w ≥ 0` (so `p_i > 0` and `z > 0`). -/
structure TypicalSet {n : σ → ℕ} (D : PhysData n) (X : Finset σ) where
  /-- `E`. -/
  E : Finset (Reg (fun v => Fin (n v)) X)
  /-- `w`. -/
  w : ℝ
  nonempty : E.Nonempty
  w_nonneg : 0 ≤ w
  lower : ∀ i ∈ E, Real.exp (-D.S X - w) ≤ D.p X i
  upper : ∀ i ∈ E, D.p X i ≤ Real.exp (-D.S X + w)

namespace TypicalSet

variable {n : σ → ℕ} {D : PhysData n} {X : Finset σ} (E : TypicalSet D X)

/-- D8.2. `z = ∑_{i ∈ E} p_i`. -/
noncomputable def z : ℝ := ∑ i ∈ E.E, D.p X i

/-- D8.2. `d_* = |E|`. -/
def d : ℕ := E.E.card

instance : NeZero E.d := ⟨E.nonempty.card_pos.ne'⟩

/-- D8.2. `p'_i = p_i / z`. -/
noncomputable def p' (i : Reg (fun v => Fin (n v)) X) : ℝ := D.p X i / E.z

/-- D8.2. `S' = -∑_{i ∈ E} p'_i log p'_i`. -/
noncomputable def S' : ℝ := ∑ i ∈ E.E, Real.negMulLog (E.p' i)

/-- The enumeration `Fin d_* ≃ E` of the bases of `C` and `R`. -/
noncomputable def idx : Fin E.d ≃ E.E := E.E.equivFin.symm

end TypicalSet

/-! ## D8.4, D8.5 Prefix data and marginal moment data -/

/-- `dim 𝓗_Q = ∏_{v ∈ Q} n_v`. -/
def dimReg (n : σ → ℕ) (Q : Finset σ) : ℕ := ∏ v ∈ Q, n v

variable {K : ℕ} {St : Type v} {X : Finset σ}

/-- D8.4 (`comparator:prefix-data`). A finite nested family `𝓡` of physical subsystems disjoint
from `X`; each `Q ∈ {U_g, U_g Y_g}` of every status and band has a matched `B ∈ 𝓡` containing it
or contained in it with `1 + log dim 𝓗_{B △ Q} ≤ B_exc`; and `S(B) ≤ B_sh` for every `B ∈ 𝓡`. -/
structure PrefixData {n : σ → ℕ} (D : PhysData n) (Γ : Statuses σ K St X)
    (𝓡 : Finset (Finset σ)) (Bsh Bexc : ℝ) : Prop where
  nested : ∀ B ∈ 𝓡, ∀ B' ∈ 𝓡, B ⊆ B' ∨ B' ⊆ B
  disjoint : ∀ B ∈ 𝓡, Disjoint B X
  matched : ∀ s g, ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g} : Finset (Finset σ)), ∃ B ∈ 𝓡,
    (Q ⊆ B ∧ 1 + Real.log (dimReg n (B \ Q)) ≤ Bexc) ∨
      (B ⊆ Q ∧ 1 + Real.log (dimReg n (Q \ B)) ≤ Bexc)
  entropy_le : ∀ B ∈ 𝓡, D.S B ≤ Bsh

/-- D8.5 (`comparator:mgf-data`). `𝓑 ≥ 1` and, for every `Q ∈ {XU_g, V_g, Y_g, U_g, U_gY_g}` of
every status and band, `log Tr ρ_Q^{1-u} ≤ u S(Q) + C₀ 𝓑 u²` for `|u| ≤ c₀/√𝓑`. -/
structure MgfData {n : σ → ℕ} (D : PhysData n) (Γ : Statuses σ K St X) (C₀ c₀ 𝓑 : ℝ) :
    Prop where
  one_le : 1 ≤ 𝓑
  bound : ∀ s g, ∀ Q ∈ ({X ∪ Γ.U s g, Γ.V s g, Γ.Y s g, Γ.U s g, Γ.U s g ∪ Γ.Y s g} :
      Finset (Finset σ)), ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt 𝓑 →
    Real.log (D.trPow Q u) ≤ u * D.S Q + C₀ * 𝓑 * u ^ 2

/-! ## D8.6 Leaf metrics, D8.7 mean trees -/

namespace Statuses

variable (Γ : Statuses σ K St X)

/-- D8.6. `P_{j,g} = C X U_{j,g}`. -/
def P (s : St) (g : Fin K) : Finset (Site σ) := insert .C (physReg (X ∪ Γ.U s g))

/-- D8.6. `Y_{j,g}` as tensor factors of `𝒱`. -/
def Yr (s : St) (g : Fin K) : Finset (Site σ) := physReg (Γ.Y s g)

/-- D8.6. `F_{j,g} = R V_{j,g}`. -/
def F (s : St) (g : Fin K) : Finset (Site σ) := insert .R (physReg (Γ.V s g))

/-- D8.6. The partition `(P_{j,g}, Y_{j,g}, F_{j,g})` of `𝒱`. -/
def part (s : St) (g : Fin K) : Transport.PYF (Site σ) := ⟨Γ.P s g, Γ.Yr s g, Γ.F s g⟩

variable (n : σ → ℕ) (d : ℕ)

/-- D8.6. `A_{j,g} = (W_{P_{j,g}}^{-1} W_{F_{j,g}}^{-1} W_{Y_{j,g}})²` on `𝒮_k`, `t = a/2`
(`Π_k A + (1 − Π_k)` on the whole tensor space). -/
noncomputable def bandA (t : ℝ) (k : ℕ) (s : St) (g : Fin K) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  Transport.bandMetric (dims n d) t k (Γ.part s g)

/-- D8.6. `A_j = ∏_{g=1}^K A_{j,g}`. -/
noncomputable def leafA (t : ℝ) (k : ℕ) (s : St) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  (List.ofFn fun g => Γ.bandA n d t k s g).prod

/-- D8.7. `𝓜`, the root of the mean tree `T` with leaves `A_j`. -/
noncomputable def root (T : Transport.MeanTree St) (t : ℝ) (k : ℕ) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  T.eval (Γ.leafA n d t k)

/-- D8.7. `𝓜_g`, the root of the same tree with leaves `A_{j,g}`. -/
noncomputable def bandRoot (T : Transport.MeanTree St) (t : ℝ) (k : ℕ) (g : Fin K) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  T.eval fun s => Γ.bandA n d t k s g

/-- D8.16. The pinned metric `Ã_{j,g} = (W_{U_{j,g}}^{-1} W_{U_{j,g}Y_{j,g}}^{-1} W_{Y_{j,g}})²`. -/
noncomputable def Atil (t : ℝ) (k : ℕ) (s : St) (g : Fin K) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  ((Replicas.W (fun f => Fin (dims n d f)) t k (physReg (Γ.U s g)))⁻¹ *
      (Replicas.W (fun f => Fin (dims n d f)) t k (physReg (Γ.U s g ∪ Γ.Y s g)))⁻¹ *
      Replicas.W (fun f => Fin (dims n d f)) t k (physReg (Γ.Y s g))) ^ 2

end Statuses

/-- D8.7. `⟨f⟩_av = K⁻¹ ∑_g ∑_j w_j f_{j,g}`. -/
noncomputable def avg [Fintype St] [DecidableEq St] (T : Transport.MeanTree St)
    (f : St → Fin K → ℝ) : ℝ :=
  (K : ℝ)⁻¹ * ∑ g, ∑ s, T.weight s * f s g

/-! ## D8.8 The prevector, `N`, `v`, `E_def` -/

section Prevector

variable {n : σ → ℕ} (D : PhysData n) (d : ℕ)

/-- `Bell_{CR} = d_*^{-1/2} ∑_i |i⟩_C |i⟩_R`. -/
noncomputable def bell (c r : Fin d) : ℂ := if c = r then ((Real.sqrt d)⁻¹ : ℝ) else 0

/-- `Ω̃ ⊗ Bell_{CR}` on `𝒱`. -/
noncomputable def preVec : SiteConfig (dims n d) → ℂ :=
  fun x => D.Ω (physPart x) * bell d (x .C) (x .R)

/-- `Ω̃ ⊗ Bell_{CR}` and the identity on `CR`: the one-copy Hamiltonian `H̃ ⊗ 1_{CR}`. -/
noncomputable def Hx : Matrix (SiteConfig (dims n d)) (SiteConfig (dims n d)) ℂ :=
  fun x y => D.H (physPart x) (physPart y) * if x .C = y .C ∧ x .R = y .R then 1 else 0

/-- D8.8. The copy mean `\overline{H̃} = k⁻¹ ∑_i H̃^{(i)}`. -/
noncomputable def Hbar (k : ℕ) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  TensorPower.copyMean (dims n d) k (Hx D d)

/-- The label projector `π^λ_C` of the `k` copies of `C`. -/
noncomputable def piC (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  Replicas.π (fun f => Fin (dims n d f)) k {Site.C} l

/-- The label projector `π^λ_R` of the `k` copies of `R`. -/
noncomputable def piR (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  Replicas.π (fun f => Fin (dims n d f)) k {Site.R} l

/-- D8.8 (`comparator:prevector`). `pre_k = π^λ_R (Ω̃ ⊗ Bell_{CR})^{⊗k}`. -/
noncomputable def pre (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Transport.Config (dims n d) k → ℂ :=
  piR d k l *ᵥ TensorPower.tensorVec k (preVec D d)

end Prevector

section Norms

variable {n : σ → ℕ} (D : PhysData n) (Γ : Statuses σ K St X) (E : TypicalSet D X)

/-- D8.8. `N² = ‖𝓜^{-s} pre_k‖²`, `s = 1/4`, for the tree `T` and `t = a/2`. -/
noncomputable def N2 (T : Transport.MeanTree St) (a : ℝ) (k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) : ℝ :=
  Matrix.Transport.filteredNormSq (Γ.root n E.d T (a / 2) k) (pre D E.d k l)

/-- D8.8. `v = 𝓜^{-s} pre_k / N`. -/
noncomputable def vec (T : Transport.MeanTree St) (a : ℝ) (k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) : Transport.Config (dims n E.d) k → ℂ :=
  Matrix.Transport.filteredVector (Γ.root n E.d T (a / 2) k) (pre D E.d k l)

/-- D8.8. `E_def = (⟨v, \overline{H̃} v⟩ - Ẽ₀)/g̃`. -/
noncomputable def Edef (T : Transport.MeanTree St) (a : ℝ) (k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) : ℝ :=
  ((star (vec D Γ E T a k l) ⬝ᵥ (Hbar D E.d k *ᵥ vec D Γ E T a k l)).re - D.E₀) / D.g

/-- D8.8. `g^pre_{j,g} = S(XU_{j,g}) + S(V_{j,g}) - S(Y_{j,g})`. -/
noncomputable def gpre (s : St) (g : Fin K) : ℝ :=
  D.S (X ∪ Γ.U s g) + D.S (Γ.V s g) - D.S (Γ.Y s g)

/-- D8.8. `g^post_{j,g} = S(U_{j,g}) + S(U_{j,g}Y_{j,g}) - S(Y_{j,g})`. -/
noncomputable def gpost (s : St) (g : Fin K) : ℝ :=
  D.S (Γ.U s g) + D.S (Γ.U s g ∪ Γ.Y s g) - D.S (Γ.Y s g)

/-! The copy number `k` of the four comparisons is `≥ 1`
(D8.8: `\overline{H̃} = k⁻¹ ∑_{i=1}^k H̃^{(i)}`, `pre_k ∈ 𝒮_k`); `k = 0` is excluded. -/

/-- D8.8 (`comparator:rough-upper`), `s = 1/4`, `W = aK`:
`-log N²/k ≤ 2 log d_* - log z + 2sW (2B_sh/z + 2B_exc) + o_k(1)`, uniformly in the tree. -/
def RoughUpper [Fintype St] [DecidableEq St] (a : ℝ)
    (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) (Bsh Bexc : ℝ) : Prop :=
  ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k → ∀ T : Transport.MeanTree St,
    -Real.log (N2 D Γ E T a k (l k)) / k ≤
      2 * Real.log E.d - Real.log E.z + 2 * (1 / 4) * (a * K) * (2 * Bsh / E.z + 2 * Bexc) + r k

/-- D8.8 (`comparator:rough-lower`), `h` the binary entropy:
`-log N²/k ≥ 2sW [2S' - C(τ log d_* + h(τ)/a) - C (E_def/τ) S'] - o_k(1)`, uniformly in the
tree. -/
def RoughLower [Fintype St] [DecidableEq St] (C a τ : ℝ)
    (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) : Prop :=
  ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k → ∀ T : Transport.MeanTree St,
    2 * (1 / 4) * (a * K) * (2 * E.S' - C * (τ * Real.log E.d + Real.binEntropy τ / a) -
        C * (Edef D Γ E T a k (l k) / τ) * E.S') - r k ≤
      -Real.log (N2 D Γ E T a k (l k)) / k

/-- D8.8 (`comparator:sharp-upper`):
`-log N²/k ≤ 2 log d_* - log z + 2sW [⟨g^post⟩_av + C (a𝓑 + |log z|/a)] + o_k(1)`. -/
def SharpUpper [Fintype St] [DecidableEq St] (C a 𝓑 : ℝ)
    (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) : Prop :=
  ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k → ∀ T : Transport.MeanTree St,
    -Real.log (N2 D Γ E T a k (l k)) / k ≤
      2 * Real.log E.d - Real.log E.z +
        2 * (1 / 4) * (a * K) * (avg T (gpost D Γ) + C * (a * 𝓑 + |Real.log E.z| / a)) + r k

/-- D8.8 (`comparator:sharp-lower`), for every `G ≥ g_max = max_{j,g} g^pre_{j,g}` (terminal
leaves of positive weight): `-log N²/k ≥ 2sW [2S' + (1-τ)⟨g^pre⟩_av - C(τ log d_* + h(τ)/a + a𝓑)
- C (E_def/τ)(S' + g_max)] - o_k(1)`. -/
def SharpLower [Fintype St] [DecidableEq St] (C a τ 𝓑 : ℝ)
    (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) : Prop :=
  ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
    ∀ (T : Transport.MeanTree St) (G : ℝ),
    (∀ s g, T.weight s ≠ 0 → gpre D Γ s g ≤ G) →
    2 * (1 / 4) * (a * K) * (2 * E.S' + (1 - τ) * avg T (gpre D Γ) -
        C * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑) -
        C * (Edef D Γ E T a k (l k) / τ) * (E.S' + G)) - r k ≤
      -Real.log (N2 D Γ E T a k (l k)) / k

end Norms

/-! ## D8.11 Schmidt vectors, `ψ`, `B_{XC}`, `post_k`, the pin projection -/

section Schmidt

variable {n : σ → ℕ} {D : PhysData n} (E : TypicalSet D X)

/-- The Schmidt vectors `|i⟩_X`: an orthonormal eigenbasis of `ρ_X` (eigenvalues `p_i`). -/
noncomputable def schmidtX (i : Reg (fun v => Fin (n v)) X) : Reg (fun v => Fin (n v)) X → ℂ :=
  ⇑((D.isHermitian_ρ X).eigenvectorBasis i)

/-- The `X`-part of a physical configuration. -/
def restrictX (x : SiteConfig n) : Reg (fun v => Fin (n v)) X := fun v => x v

/-- The physical configuration `x` with its `X`-part replaced by `y`. -/
def replaceX (x : SiteConfig n) (y : Reg (fun v => Fin (n v)) X) : SiteConfig n :=
  fun v => if h : v ∈ X then y ⟨v, h⟩ else x v

omit [Fintype σ] in
theorem restrictX_replaceX (x : SiteConfig n) (y : Reg (fun v => Fin (n v)) X) :
    restrictX (replaceX x y) = y :=
  funext fun v => by simp [restrictX, replaceX, v.2]

/-- D8.11. The Schmidt vector `|w_i⟩ = p_i^{-1/2} ⟨i|_X Ω̃` on `X^c`, as a function of the
physical configuration that ignores its `X`-part. -/
noncomputable def schmidtW (i : Reg (fun v => Fin (n v)) X) : SiteConfig n → ℂ :=
  fun x => ((Real.sqrt (D.p X i))⁻¹ : ℝ) *
    ∑ y, star (schmidtX (D := D) i y) * D.Ω (replaceX x y)

/-- D8.11. `B_{XC} = d_*^{-1/2} ∑_{i ∈ E} |i⟩_X |i⟩_C` on `𝒱` (a function of the `XC`-part). -/
noncomputable def BXC : SiteConfig (dims n E.d) → ℂ :=
  fun x => ((Real.sqrt E.d)⁻¹ : ℝ) *
    schmidtX (D := D) (X := X) (E.idx (x .C)).1 (restrictX (physPart x))

/-- D8.11. `ψ = ∑_{i ∈ E} √p'_i |i⟩_R |w_i⟩` on `𝒱` (a function of the `R X^c`-part). -/
noncomputable def ψ : SiteConfig (dims n E.d) → ℂ :=
  fun x => (Real.sqrt (E.p' (E.idx (x .R)).1) : ℂ) *
    schmidtW (D := D) (X := X) (E.idx (x .R)).1 (physPart x)

/-- D8.11. `post_k = B_{XC}^{⊗k} ⊗ ψ^{⊗k}`. -/
noncomputable def post (k : ℕ) : Transport.Config (dims n E.d) k → ℂ :=
  TensorPower.tensorVec k fun x => BXC E x * ψ E x

/-- The tensor factors `XC`. -/
def XC (X : Finset σ) : Finset (Site σ) := insert .C (physReg X)

/-- D8.11. `𝖯`, the projection of `(XC)^{⊗k}` onto `B_{XC}^{⊗k}`, tensored with the identity on
the other factors. -/
noncomputable def pinProj (k : ℕ) :
    Matrix (Transport.Config (dims n E.d) k) (Transport.Config (dims n E.d) k) ℂ :=
  fun x y => (∏ j, BXC E (x j) * star (BXC E (y j))) *
    if ∀ j, ∀ f ∉ XC X, x j f = y j f then 1 else 0

/-- D8.12. `q_k = ‖π^λ_R ψ^{⊗k}‖² = ‖π^λ_R post_k‖²`. -/
noncomputable def q (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) : ℝ :=
  (star (piR E.d k l *ᵥ post E k) ⬝ᵥ (piR E.d k l *ᵥ post E k)).re

/-- D8.12 (`comparator:high-label`). A label sequence `λ_k` with `q_k ≥ poly(k)^{-1}` and
`log d_{λ_k} = k S' + o(k)`. -/
def HighLabel (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) : Prop :=
  ∃ c N : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ k : ℕ,
    c * ((k : ℝ) + 1) ^ (-N) ≤ q E k (l k) ∧ |Real.log (l k).dim - k * E.S'| ≤ k * ε k

end Schmidt

/-! ## D8.23 The excited-copy projections -/

section Defect

variable {n : σ → ℕ} (D : PhysData n) (d : ℕ)

/-- `|Ω̃⟩⟨Ω̃| ⊗ 1_{CR}` on one copy of `𝒱`. -/
noncomputable def groundProj : Matrix (SiteConfig (dims n d)) (SiteConfig (dims n d)) ℂ :=
  fun x y => D.Ω (physPart x) * star (D.Ω (physPart y)) *
    if x .C = y .C ∧ x .R = y .R then 1 else 0

/-- D8.23. `Q = 1 - |Ω̃⟩⟨Ω̃|` on the physical factor of one copy. -/
noncomputable def excProj : Matrix (SiteConfig (dims n d)) (SiteConfig (dims n d)) ℂ :=
  1 - groundProj D d

/-- D8.24. `Π_B = ∏_{i ∈ B} Q_i ∏_{i ∉ B} (1 - Q_i)`: exactly the copies in `B` excited. -/
noncomputable def compProj (k : ℕ) (B : Finset (Fin k)) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  fun x y => ∏ j, (if j ∈ B then excProj D d else groundProj D d) (x j) (y j)

/-- D8.23. `Π`, the projection onto `∑_i Q_i ≤ τ k`. -/
noncomputable def defectProj (τ : ℝ) (k : ℕ) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  ∑ B ∈ Finset.univ.filter fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k, compProj D d k B

/-- D8.13, D8.23. The common auxiliary sector `π^λ_C π^λ_R Π_k`. -/
noncomputable def sector (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  piC d k l * piR d k l * Transport.Pi (dims n d) k

/-- D8.23. `Π` on `𝒮_k` with the two fixed auxiliary labels. -/
noncomputable def lowProj (τ : ℝ) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  defectProj D d τ k * sector d k l

end Defect

end AreaLaw.Comparators
