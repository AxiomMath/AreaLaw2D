import Arealaw.Bell
import Arealaw.Kronecker

/-!
# The dimer chain and the area law

A chain of `n` dimers across a single cut: one Bell pair straddling the cut, which carries
the entanglement, Kronecker-multiplied with `n` pairs sitting entirely on one side, each
contributing a one-dimensional factor to the cut side.  `dimer_area_law` gives
`EE (chain n) = log 2` for every `n`, a boundary law and not a volume law: the opening
picture of Brandão–Horodecki, arXiv:1309.3789, Fig. 1a.
-/

namespace Arealaw

open scoped Kronecker
open Matrix

/-! ### A `PureState` Kronecker combinator -/

/-- The Kronecker (tensor) product of two pure states is a pure state: the squared-norm
normalization is multiplicative, `1 · 1 = 1`. -/
noncomputable def PureState.kronecker {𝕜 : Type*} [RCLike 𝕜] {A₁ B₁ A₂ B₂ : Type*} [Fintype A₁]
    [Fintype B₁] [Fintype A₂] [Fintype B₂] (ψ₁ : PureState 𝕜 A₁ B₁) (ψ₂ : PureState 𝕜 A₂ B₂) :
    PureState 𝕜 (A₁ × A₂) (B₁ × B₂) where
  M := ψ₁.M ⊗ₖ ψ₂.M
  normalized := by
    simp [Fintype.sum_prod_type, mul_pow, ← Finset.sum_mul_sum, ψ₁.normalized, ψ₂.normalized]

/-! ### A one-dimensional cut side carries no entanglement -/

/-- **A one-dimensional cut side carries no entanglement**: the reduced operator has the
single eigenvalue `1`, so `EE = negMulLog 1 = 0`. -/
theorem EE_eq_zero_of_card_eq_one {𝕜 : Type*} [RCLike 𝕜] {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (hcard : Fintype.card A = 1) (ψ : PureState 𝕜 A B) : EE ψ.M = 0 := by
  obtain ⟨u⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hcard
  have := sum_eigenvalues_pureState ψ
  simp_all [EE, H]

/-! ### The dimer chain -/

/-- The straddling Bell pair, packaged as a pure state on `Fin 2 ⊗ Fin 2` (one qubit on each
side of the cut). Pinned to `ℂ` by `bell`. -/
noncomputable def bellState : PureState ℂ (Fin 2) (Fin 2) := ⟨bell, bell_normalized⟩

/-- A Bell pair sitting entirely on the *right* of the cut: the cut side is the singleton
`Fin 1`, both qubits live in `Fin 2 × Fin 2` on the right. Its coefficient matrix is the
single row of the (normalized) Bell vector. Pinned to `ℂ` by `bell`. -/
noncomputable def rightDimer : PureState ℂ (Fin 1) (Fin 2 × Fin 2) where
  M := Matrix.of fun _ p => bell p.1 p.2
  normalized := by simpa [Fintype.sum_prod_type] using bell_normalized

/-- Cut-side index of the `n`-dimer interior. A product of `n` singletons, always
one-dimensional. -/
def InteriorA : ℕ → Type
  | 0 => Fin 1
  | n + 1 => Fin 1 × InteriorA n

/-- Right-side index of the `n`-dimer interior: the `2n` qubits of the `n` interior pairs. -/
def InteriorB : ℕ → Type
  | 0 => Fin 1
  | n + 1 => (Fin 2 × Fin 2) × InteriorB n

instance instFintypeInteriorA : (n : ℕ) → Fintype (InteriorA n)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | n + 1 => @instFintypeProd _ _ _ (instFintypeInteriorA n)

instance instDecidableEqInteriorA : (n : ℕ) → DecidableEq (InteriorA n)
  | 0 => inferInstanceAs (DecidableEq (Fin 1))
  | n + 1 => @instDecidableEqProd _ _ _ (instDecidableEqInteriorA n)

instance instFintypeInteriorB : (n : ℕ) → Fintype (InteriorB n)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | n + 1 => @instFintypeProd _ _ _ (instFintypeInteriorB n)

/-- The interior of the chain: `n` Bell pairs all on one side of the cut, Kronecker-
multiplied. Pinned to `ℂ` by `rightDimer`. -/
noncomputable def interior : (n : ℕ) → PureState ℂ (InteriorA n) (InteriorB n)
  | 0 =>
    { M := .of fun _ _ => 1
      normalized := by
        change ∑ _ : Fin 1, ∑ _ : Fin 1, ‖(1 : ℂ)‖ ^ 2 = 1
        simp }
  | n + 1 => rightDimer.kronecker (interior n)

/-- The cut side of the interior is always one-dimensional: products of singletons. -/
theorem card_interiorA : (n : ℕ) → Fintype.card (InteriorA n) = 1
  | 0 => rfl
  | n + 1 => by simp [InteriorA, card_interiorA n]

/-- The full chain of `n` dimers across the cut: the straddling Bell pair, tensored with the
`n`-dimer interior that lives entirely on one side.  Pinned to `ℂ` by `bellState`. -/
noncomputable def chain (n : ℕ) : PureState ℂ (Fin 2 × InteriorA n) (Fin 2 × InteriorB n) :=
  bellState.kronecker (interior n)

/-! ### The area law -/

/-- **The dimer area law**: `EE (chain n) = log 2` for every `n`. -/
theorem dimer_area_law (n : ℕ) : EE (chain n).M = Real.log 2 := by
  refine (EE_kronecker_add bellState (interior n)).trans ?_
  rw [EE_eq_zero_of_card_eq_one (card_interiorA n) (interior n), add_zero]
  exact EE_bell

end Arealaw
