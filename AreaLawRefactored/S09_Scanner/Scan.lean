import AreaLawRefactored.S09_Scanner.Interfaces

/-!
# §9.0 The scan (D9.1, D9.4–D9.7) and the statement of Lemma 9.1 (D9.8)

Digest `digest/09-scanner.md` D9.1, D9.4–D9.8, paper `paper/sections/08-scanner.tex` 13–221.
Graph-level (Map.md, Dimension: `any d`): a simple graph `G` on a site type `σ`, the domain `Λ`,
the cut `A ⊆ Λ`, a depth `dep : σ → ℕ` (D9.1; `dist_∞(·, T)` on `ℤ²`). The labelled terms are
the admissible supports `Y`, with anchors `a Y ∈ Y` and designated supports
`X̃_Y = GraphDomain.truncatedSupport G Λ S₀ r₀ (a Y)` (D4.11), `S₀ = A ∩ {dep ≤ L}`.

Regions of the scan are regions of the domain type `↥Λ`, the physical sites of the replica system
`Comparators.Site Λ` of §8. One band's physical state assigns each site to the near side
(`some false`, `X U`), the middle (`none`, `Y`) or the far side (`some true`, `V`).
-/

open scoped Matrix
open Finset Arealaw

namespace AreaLaw.Scanner

universe u

open Transport (MeanTree)
open Comparators (physReg Site)

/-! ## Uniform mean trees -/

/-- The vertex parameter `(N + 1)/(N + 2)`: the first child carries weight `1/(N + 2)`. -/
noncomputable def tailParam (N : ℕ) : unitInterval :=
  ⟨(N + 1 : ℝ) / (N + 2), div_nonneg (by positivity) (by positivity),
    (div_le_one (by positivity)).2 (by linarith)⟩

/-- The uniform binary mean tree on `Fin (N + 1)`. -/
noncomputable def uniformFin : (N : ℕ) → MeanTree (Fin (N + 1))
  | 0 => .leaf 0
  | N + 1 => .node (tailParam N) (.leaf 0) ((uniformFin N).map Fin.succ)

theorem labels_bind {ι κ : Type*} (T : MeanTree ι) (f : ι → MeanTree κ) :
    (T.bind f).labels = T.labels.flatMap fun j => (f j).labels := by
  induction T with
  | leaf j => simp [MeanTree.bind, MeanTree.labels]
  | node p l r ihl ihr => simp [MeanTree.bind, MeanTree.labels, ihl, ihr]

theorem labels_map {ι κ : Type*} (T : MeanTree ι) (f : ι → κ) :
    (T.map f).labels = T.labels.map f := by
  induction T with
  | leaf j => simp [MeanTree.map, MeanTree.bind, MeanTree.labels]
  | node p l r ihl ihr =>
    simp only [MeanTree.map, MeanTree.bind, MeanTree.labels] at ihl ihr ⊢
    rw [ihl, ihr, List.map_append]

theorem weight_uniformFin (N : ℕ) (i : Fin (N + 1)) :
    (uniformFin N).weight i = 1 / (N + 1 : ℝ) := by
  induction N with
  | zero => rw [Fin.eq_zero i]; simp [uniformFin, MeanTree.weight]
  | succ N ih =>
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [uniformFin, MeanTree.weight_node,
        MeanTree.weight_map_of_forall_ne _ (fun j => Fin.succ_ne_zero j)]
      simp only [MeanTree.weight, Pi.single_eq_same, tailParam]
      push_cast
      field_simp
      ring
    · rw [uniformFin, MeanTree.weight_node,
        MeanTree.weight_map_apply _ (Fin.succ_injective _), ih]
      simp only [MeanTree.weight, Pi.single_eq_of_ne (Fin.succ_ne_zero j), tailParam]
      push_cast
      field_simp
      ring

theorem nodup_uniformFin (N : ℕ) : (uniformFin N).labels.Nodup := by
  induction N with
  | zero => simp [uniformFin, MeanTree.labels]
  | succ N ih =>
    simp only [uniformFin, MeanTree.labels, labels_map, List.singleton_append, List.nodup_cons,
      List.mem_map, not_exists, not_and]
    exact ⟨fun j _ hj => Fin.succ_ne_zero j hj, ih.map (Fin.succ_injective _)⟩

/-- The uniform mean tree on a nonempty finite type (weights `1/|α|`, distinct leaves). -/
noncomputable def uniformTree (α : Type*) [Fintype α] [Nonempty α] : MeanTree α :=
  (uniformFin (Fintype.card α - 1)).map fun i =>
    (Fintype.equivFin α).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) i)

theorem uniformTree_injective (α : Type*) [Fintype α] [Nonempty α] :
    Function.Injective fun i : Fin (Fintype.card α - 1 + 1) =>
      (Fintype.equivFin α).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) i) :=
  (Fintype.equivFin α).symm.injective.comp (Fin.cast_injective _)

theorem weight_uniformTree (α : Type*) [Fintype α] [Nonempty α] [DecidableEq α] (x : α) :
    (uniformTree α).weight x = 1 / Fintype.card α := by
  have h := Nat.sub_add_cancel (Fintype.card_pos (α := α))
  have hx : (Fintype.equivFin α).symm (Fin.cast h (Fin.cast h.symm (Fintype.equivFin α x))) =
      x := by simp
  rw [uniformTree, ← hx, MeanTree.weight_map_apply _ (uniformTree_injective α), weight_uniformFin]
  congr 1
  exact_mod_cast h

theorem nodup_uniformTree (α : Type*) [Fintype α] [Nonempty α] :
    (uniformTree α).labels.Nodup := by
  rw [uniformTree, labels_map]
  exact (nodup_uniformFin _).map (uniformTree_injective α)

/-! ## The data of a scan -/

/-- D9.2–D9.6. The data of a scan: the graph `G`, the domain `Λ`, the cut `A`, the depth `dep`
(D9.1), the range `R` and the anchors `a Y ∈ Y` of the admissible supports (the labelled terms),
`n` padded slots per depth row, the collar depth `L`, the window scale and number of offsets `m`,
the number of bands `K`, the charge lookahead `D`, the graph radius `r₀` and the padded length
`M` of the charge lists. -/
structure Scan (σ : Type u) [DecidableEq σ] where
  /-- The graph. -/
  G : SimpleGraph σ
  /-- The domain `Λ`. -/
  Λ : Finset σ
  /-- The cut `A`. -/
  A : Finset σ
  /-- The depth (D9.1). -/
  dep : σ → ℕ
  /-- The interaction range. -/
  R : ℕ
  /-- The anchors of the labelled terms. -/
  a : Finset σ → σ
  /-- Padded slots per depth row. -/
  n : ℕ
  /-- The collar depth. -/
  L : ℕ
  /-- The window scale and number of offsets. -/
  m : ℕ
  /-- The number of bands. -/
  K : ℕ
  /-- The charge lookahead. -/
  D : ℕ
  /-- The graph radius of the splitting supports. -/
  r₀ : ℕ
  /-- The padded length `M_n` of the charge lists. -/
  M : ℕ
  m_pos : 0 < m
  M_pos : 0 < M

/-- D9.6. `M_n = ⌈C_l n D⌉`. -/
noncomputable def Mn (Cl : ℝ) (n D : ℕ) : ℕ := ⌈Cl * n * D⌉₊

namespace Scan

variable {σ : Type u} [DecidableEq σ] (S : Scan σ)

/-- The target `X = A ∩ T` (depth `0`) as a region of `Λ`. -/
def X : Finset S.Λ := (S.A.filter fun x => S.dep x = 0).subtype (· ∈ S.Λ)

/-- D9.3. `S₀ = A ∩ T_L`. -/
def S₀ : Finset σ := S.A.filter fun x => S.dep x ≤ S.L

/-- The labelled terms: the admissible supports. -/
abbrev Term := ↥(GraphDomain.supports S.G S.Λ S.R)

/-- D4.11. The designated support `X̃_i`, as a region of `Λ`. -/
noncomputable def Xt (i : S.Term) : Finset S.Λ :=
  (GraphDomain.truncatedSupport S.G S.Λ S.S₀ S.r₀ (S.a i)).subtype (· ∈ S.Λ)

/-- D9.6. The graph `r₀`-ball `B_Λ(a_i, r₀)` of a labelled term, as a region of `Λ`. -/
noncomputable def ball (i : S.Term) : Finset S.Λ :=
  (GraphDomain.ball S.G S.Λ (S.a i) S.r₀).subtype (· ∈ S.Λ)

/-! ## D9.4 Rows, bands, initial partitions -/

/-- D9.4. The physical state of one band: `some false` the near side `X U`, `none` the middle
`Y`, `some true` the far side `V`. -/
abbrev State := S.Λ → Option Bool

variable {S} in
/-- The sites of side `b` (`false` near, `true` far). -/
def side (st : S.State) (b : Bool) : Finset S.Λ := univ.filter fun x => st x = some b

variable {S} in
/-- The middle `Y`. -/
def middle (st : S.State) : Finset S.Λ := univ.filter fun x => st x = none

/-- D9.4. The near cutoff `b_g + m + r` of band `g` (`b_g = 8gm`) with offset `r`. -/
def lo (g r : ℕ) : ℕ := 8 * g * S.m + S.m + r

/-- D9.4. The far cutoff `b_g + 5m + r`. -/
def hi (g r : ℕ) : ℕ := 8 * g * S.m + 5 * S.m + r

/-- D9.4. The initial physical partition of band `g` with offset `r`:
`P₀ = {x ∈ A : dep ≤ b_g + m + r}`, `V = (Λ \ A) ∪ {x ∈ A : dep > b_g + 5m + r}`, `Y` the rest. -/
def init (g r : ℕ) : S.State := fun x =>
  if x.1 ∉ S.A then some true
  else if S.dep x ≤ S.lo g r then some false
  else if S.hi g r < S.dep x then some true
  else none

/-- D9.4. The fixed order of the sites of the depth row `j`; slot `k` is the `k`-th entry, the
slots `≥` its length (and the sites outside `A`) are blanks. -/
noncomputable def row (j : ℕ) : List S.Λ := (univ.filter fun x : S.Λ => S.dep x = j).toList

/-! ## D9.5 Fill rounds and fronts -/

/-- D9.5. The number of fills before round `t` (fills are the even rounds). -/
def fills (t : ℕ) : ℕ := (t + 1) / 2

/-- D9.5. The number of the first `f` fills received by side `b` (near first, alternating). -/
def sideFills (f : ℕ) (b : Bool) : ℕ := if b then f / 2 else (f + 1) / 2

/-- D9.5. Oriented depth: `dep` on the near side, `-dep` on the far side. -/
def odep (b : Bool) (x : σ) : ℤ := if b then -(S.dep x : ℤ) else S.dep x

/-- D9.5 (`scanner:fronts`). The oriented depth of the next incomplete row of side `b` of band `g`
(offset `r`) before round `t`: `j_P = b_g + m + r + 1 + ⌊t_P/n⌋`,
`j_F = -(b_g + 5m + r) + ⌊t_F/n⌋`. -/
def front (g r t : ℕ) (b : Bool) : ℤ :=
  if b then -(S.hi g r : ℤ) + (sideFills (fills t) true / S.n : ℕ)
  else (S.lo g r + 1 + sideFills (fills t) false / S.n : ℕ)

/-- D9.5. The slot consumed by the `w`-th fill of side `b`: near side in increasing depth, far
side in decreasing depth with the slot order reversed; `none` for a blank. -/
noncomputable def fillSlot (g r : ℕ) (b : Bool) (w : ℕ) : Option S.Λ :=
  (if b then (S.row (S.hi g r - w / S.n))[S.n - 1 - w % S.n]?
    else (S.row (S.lo g r + 1 + w / S.n))[w % S.n]?).filter fun x => decide (x.1 ∈ S.A)

/-- D9.5. The fill of round `t` (even) in band `g`: fill number `t/2` goes to the near side if
it is even, to the far side if it is odd; its slot is moved if it is still in the middle. -/
noncomputable def fillStep (g r t : ℕ) (st : S.State) : Option (Bool × Finset S.Λ) :=
  (S.fillSlot g r (decide (t / 2 % 2 = 1)) (sideFills (t / 2) (decide (t / 2 % 2 = 1)))).bind
    fun x => if st x = none then some (decide (t / 2 % 2 = 1), {x}) else none

/-! ## D9.6 Charge rounds -/

/-- D9.6. The list of labelled terms whose anchor has oriented depth in `[j - r₀, j + D]` on
side `b` (`j` the front), in a fixed order; padded to `M` slots by blanks. -/
noncomputable def chargeList (g r t : ℕ) (b : Bool) : List S.Term :=
  (univ : Finset S.Term).toList.filter fun i =>
    decide (S.front g r t b - S.r₀ ≤ S.odep b (S.a i) ∧ S.odep b (S.a i) ≤ S.front g r t b + S.D)

/-- D9.6. The charge of round `t` (odd) in band `g` with choice `v < 2M` (side `v / M`, slot
`v % M`): if the slot holds a term whose `r₀`-ball meets the receiving side and the middle, the
middle part of the ball moves to that side. -/
noncomputable def chargeStep (g r t v : ℕ) (st : S.State) : Option (Bool × Finset S.Λ) :=
  ((S.chargeList g r t (decide (S.M ≤ v)))[v % S.M]?).bind fun i =>
    if (S.ball i ∩ side st (decide (S.M ≤ v))).Nonempty ∧ (S.ball i ∩ middle st).Nonempty then
      some (decide (S.M ≤ v), S.ball i ∩ middle st)
    else none

/-- D9.5. The transition of round `t`: fills at even rounds, charges at odd ones. -/
noncomputable def step (g r t v : ℕ) (st : S.State) : Option (Bool × Finset S.Λ) :=
  if t % 2 = 0 then S.fillStep g r t st else S.chargeStep g r t v st

variable {S} in
/-- The state after a transition. -/
def applyStep : Option (Bool × Finset S.Λ) → S.State → S.State
  | none, st => st
  | some (b, x), st => fun y => if y ∈ x then some b else st y

/-! ## D9.7 Histories -/

/-- The number of choices of one band at round `t`: `2M` (side, slot) at a charge, `1` at a
fill. -/
def c (t : ℕ) : ℕ := if t % 2 = 1 then 2 * S.M else 1

/-- D9.7. The choices of round `t`, one for every band (independent across bands). -/
abbrev Ch (t : ℕ) := Fin S.K → Fin (S.c t)

/-- D9.7. A history before round `t`: the offsets and all choices of the rounds `< t`. -/
def Hist : ℕ → Type
  | 0 => Fin S.K → Fin S.m
  | t + 1 => Hist t × S.Ch t

instance instFintypeHist : (t : ℕ) → Fintype (S.Hist t)
  | 0 => inferInstanceAs (Fintype (Fin S.K → Fin S.m))
  | t + 1 => letI := instFintypeHist t; inferInstanceAs (Fintype (S.Hist t × S.Ch t))

instance instDecidableEqHist : (t : ℕ) → DecidableEq (S.Hist t)
  | 0 => inferInstanceAs (DecidableEq (Fin S.K → Fin S.m))
  | t + 1 => letI := instDecidableEqHist t; inferInstanceAs (DecidableEq (S.Hist t × S.Ch t))

theorem c_pos (t : ℕ) : 0 < S.c t := by
  unfold c; split_ifs <;> linarith [S.M_pos]

instance (t : ℕ) : Nonempty (S.Ch t) := ⟨fun _ => ⟨0, S.c_pos t⟩⟩

instance instNonemptyHist : (t : ℕ) → Nonempty (S.Hist t)
  | 0 => ⟨fun _ => ⟨0, S.m_pos⟩⟩
  | t + 1 => letI := instNonemptyHist t; inferInstanceAs (Nonempty (S.Hist t × S.Ch t))

/-- A history extended by the choices of round `t`. -/
def ext (t : ℕ) (h : S.Hist t) (c : S.Ch t) : S.Hist (t + 1) := (h, c)

/-- The offsets `r_g` of a history. -/
def offset : (t : ℕ) → S.Hist t → Fin S.K → Fin S.m
  | 0, h => h
  | t + 1, h => offset t h.1

/-- D9.4–D9.6. The physical state of band `g` after the history `h` of the rounds `< t`. -/
noncomputable def stateAt : (t : ℕ) → S.Hist t → Fin S.K → S.State
  | 0, h, g => S.init g (h g)
  | t + 1, h, g => applyStep (S.step g (S.offset t h.1 g) t (h.2 g) (stateAt t h.1 g))
      (stateAt t h.1 g)

/-- D9.7. The history tree: uniform offsets, then at every round the uniform choice tree attached
at every leaf (classical path probabilities). -/
noncomputable def histTree : (t : ℕ) → MeanTree (S.Hist t)
  | 0 => uniformTree _
  | t + 1 => (histTree t).bind fun h => (uniformTree (S.Ch t)).map (S.ext t h)

/-- The `2nm` rounds. -/
def T : ℕ := 2 * S.n * S.m

/-! ## D9.7 Statuses and rounds -/

/-- The region `U` of a state (the near side without `X`). -/
def U (st : S.State) : Finset S.Λ := side st false \ S.X

/-- The global status type: the terminal leaves of all `2nm` rounds. -/
abbrev St := Σ t : Fin S.T, Transport.Round.Leaf (S.Hist t) (fun _ => S.Ch t)

/-- The physical state at a terminal leaf: the old state at `(h, old)`, the new one at
`(h, c, new)`. -/
noncomputable def leafState : S.St → Fin S.K → S.State
  | ⟨t, ⟨h, none⟩⟩ => S.stateAt t h
  | ⟨t, ⟨h, some c⟩⟩ => S.stateAt (t + 1) (S.ext t h c)

theorem step_subset_middle {g r t v : ℕ} {st : S.State} {b : Bool} {x : Finset S.Λ}
    (h : S.step g r t v st = some (b, x)) : x ⊆ middle st := by
  unfold step fillStep chargeStep at h
  split_ifs at h
  · rcases hs : S.fillSlot g r _ _ with _ | y <;> rw [hs] at h
    · simp at h
    · simp only [Option.bind_some] at h
      split_ifs at h with hy
      cases h
      simpa [middle] using hy
  · rcases hs : (S.chargeList g r t (decide (S.M ≤ v)))[v % S.M]? with _ | i <;> rw [hs] at h
    · simp at h
    · simp only [Option.bind_some] at h
      split_ifs at h
      cases h
      exact inter_subset_right

theorem applyStep_step_of_ne_none {g r t v : ℕ} {st : S.State} {y : S.Λ} (hy : st y ≠ none) :
    applyStep (S.step g r t v st) st y = st y := by
  rcases h : S.step g r t v st with _ | ⟨b, x⟩
  · rfl
  · have hx := S.step_subset_middle h
    simp only [applyStep]
    rw [if_neg fun hyx => hy (by simpa [middle] using hx hyx)]

/-- D9.5. Initially assigned sites are never reassigned. -/
theorem stateAt_of_init {t : ℕ} (h : S.Hist t) (g : Fin S.K) {y : S.Λ} {b : Bool}
    (hy : S.init g (S.offset t h g) y = some b) : S.stateAt t h g y = some b := by
  induction t with
  | zero => exact hy
  | succ t ih =>
    have h1 := ih h.1 hy
    simp only [stateAt]
    rw [S.applyStep_step_of_ne_none (by rw [h1]; simp), h1]

theorem init_of_mem_X {g r : ℕ} {x : S.Λ} (hx : x ∈ S.X) : S.init g r x = some false := by
  simp only [X, mem_subtype, mem_filter] at hx
  simp [init, hx.1, hx.2]

theorem mem_A_of_init_ne {g r : ℕ} {x : S.Λ} (hx : S.init g r x ≠ some true) :
    x.1 ∈ S.A ∧ S.dep x ≤ S.hi g r := by
  have : S.lo g r ≤ S.hi g r := by simp only [lo, hi]; omega
  simp only [init] at hx
  split_ifs at hx with h1 h2 h3 <;> simp_all
  omega

theorem exists_leafState (s : S.St) :
    ∃ (t : ℕ) (h : S.Hist t), t ≤ S.T ∧ S.leafState s = S.stateAt t h := by
  obtain ⟨t, h, _ | c⟩ := s
  · exact ⟨t, h, t.2.le, rfl⟩
  · exact ⟨t + 1, S.ext t h c, t.2, rfl⟩

theorem stateAt_X {t : ℕ} (h : S.Hist t) (g : Fin S.K) {x : S.Λ} (hx : x ∈ S.X) :
    S.stateAt t h g x = some false :=
  S.stateAt_of_init h g (S.init_of_mem_X hx)

theorem hi_lt_lo {g g' : ℕ} (hg : g < g') {r : ℕ} (r' : ℕ) (hr : r < S.m) :
    S.hi g r < S.lo g' r' := by
  have : 8 * (g + 1) * S.m ≤ 8 * g' * S.m := Nat.mul_le_mul_right _ (by omega)
  simp only [hi, lo]
  nlinarith

/-- D9.8.9 (`comparator:nesting`). For `g < g'` and any two states:
`X U_g Y_g ⊆ X U_{g'}`. -/
theorem nesting_stateAt {t t' : ℕ} (h : S.Hist t) (h' : S.Hist t') {g g' : Fin S.K}
    (hg : g < g') :
    S.X ∪ S.U (S.stateAt t h g) ∪ middle (S.stateAt t h g) ⊆
      S.X ∪ S.U (S.stateAt t' h' g') := by
  intro x hx
  have hnt : S.stateAt t h g x ≠ some true := by
    simp only [mem_union, U, mem_sdiff, side, middle, mem_filter, mem_univ, true_and] at hx
    rcases hx with (hx | hx) | hx
    · rw [S.stateAt_X h g hx]; simp
    · rw [hx.1]; simp
    · rw [hx]; simp
  have hinit : S.init g (S.offset t h g) x ≠ some true := fun h1 =>
    hnt (S.stateAt_of_init h g h1)
  obtain ⟨hA, hd⟩ := S.mem_A_of_init_ne hinit
  have hlt := S.hi_lt_lo hg (S.offset t' h' g') (S.offset t h g).2
  have h2 : S.init g' (S.offset t' h' g') x = some false := by
    simp only [init, hA, not_true_eq_false, if_false]
    rw [if_pos (by omega)]
  have h3 := S.stateAt_of_init h' g' h2
  by_cases hxX : x ∈ S.X
  · exact mem_union_left _ hxX
  · exact mem_union_right _ (mem_sdiff.2 ⟨by simp [side, h3], hxX⟩)

/-- D9.7. The global status collection of all rounds: at every terminal leaf of every round and
in every band, `U` (near side without `X`), `Y` (middle), `V` (far side). -/
noncomputable def Γ : Comparators.Statuses S.Λ S.K S.St S.X where
  U s g := S.U (S.leafState s g)
  Y s g := middle (S.leafState s g)
  V s g := side (S.leafState s g) true
  disjoint_XU _ _ := disjoint_sdiff
  disjoint_XY s g := by
    obtain ⟨t, h, -, hs⟩ := S.exists_leafState s
    rw [hs, Finset.disjoint_left]
    intro x hx hy
    simp [middle, S.stateAt_X h g hx] at hy
  disjoint_XV s g := by
    obtain ⟨t, h, -, hs⟩ := S.exists_leafState s
    rw [hs, Finset.disjoint_left]
    intro x hx hy
    simp [side, S.stateAt_X h g hx] at hy
  disjoint_UY s g := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [U, side, middle, mem_sdiff, mem_filter, mem_univ, true_and] at hx hy
    rw [hx.1] at hy; simp at hy
  disjoint_UV s g := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [U, side, mem_sdiff, mem_filter, mem_univ, true_and] at hx hy
    rw [hx.1] at hy; simp at hy
  disjoint_YV s g := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [side, middle, mem_filter, mem_univ, true_and] at hx hy
    rw [hx] at hy; simp at hy
  cover s g := by
    ext x
    simp only [U, side, middle, mem_union, mem_sdiff, mem_filter, mem_univ, true_and, iff_true]
    rcases S.leafState s g x with _ | _ | _ <;> simp; tauto
  nesting s s' g g' hg := by
    obtain ⟨t, h, -, hs⟩ := S.exists_leafState s
    obtain ⟨t', h', -, hs'⟩ := S.exists_leafState s'
    rw [hs, hs']
    exact S.nesting_stateAt h h' hg

/-- A transition as a move of §7: nothing, or the moved middle part to `P` or to `F`. -/
def toMove : Option (Bool × Finset S.Λ) → Transport.Move (Site S.Λ)
  | none => .stay
  | some (false, x) => .toP (physReg x)
  | some (true, x) => .toF (physReg x)

/-- D9.7 (`transport:terminal-weights`). Round `t` of the scan as a round of §7: the history
tree, the uniform choice trees, the old partitions `(P, Y, F) = (C X U, Y, R V)` of the statuses,
and the moves of the fills and charges in every band. -/
noncomputable def round (t : Fin S.T) :
    Transport.Round (Site S.Λ) S.K (S.Hist t) (fun _ => S.Ch t) where
  histTree := S.histTree t
  choiceTree _ := uniformTree (S.Ch t)
  old h g := S.Γ.part ⟨t, ⟨h, none⟩⟩ g
  move h c g := S.toMove (S.step g (S.offset t h g) t (c g) (S.stateAt t h g))

/-- D9.8 (4). The good old histories: no side of any band has an assigned site of `A` of oriented
depth `> j + D/2`. -/
def Good (t : ℕ) (h : S.Hist t) : Prop :=
  ∀ (g : Fin S.K) (b : Bool) (x : S.Λ), S.stateAt t h g x = some b → x.1 ∈ S.A →
    S.odep b x ≤ S.front g (S.offset t h g) t b + (S.D / 2 : ℕ)

/-- D9.8.6. The deterministic prefix `(j, k)` of the fixed ordered list of positive-depth slots:
the sites of `A` of depth `0 < dep < j` and the first `k` slots of row `j`. -/
noncomputable def pre (j k : ℕ) : Finset S.Λ :=
  univ.filter (fun x : S.Λ => x.1 ∈ S.A ∧ 0 < S.dep x ∧ S.dep x < j) ∪
    ((S.row j).take k).toFinset.filter fun x => x.1 ∈ S.A

/-- D9.8.6. The family `𝓡` of prefixes `(j, k)`, `1 ≤ j ≤ L`, `k ≤ n`. -/
noncomputable def prefixes : Finset (Finset S.Λ) :=
  (Icc 1 S.L ×ˢ range (S.n + 1)).image fun p => S.pre p.1 p.2

/-- The energy terms of §7 have the designated supports `X̃_i` (on the physical factors). -/
def HasSupports {nl : Site S.Λ → ℕ} (E : Transport.EnergyTerms (Site S.Λ) nl S.Term) : Prop :=
  ∀ i, E.support i = physReg (S.Xt i)

/-! ## The items of Lemma 9.1 -/

/-- Lemma 9.1 (1) (D9.8.1–4, 9, 10, D9.28.2). Every splitting designated support is the graph
`r₀`-ball and lies in `A`; support compatibility (a support splits at most one band, and there
meets `Y` and exactly one side) for every round; every move transfers a subsystem of an `r₀`-ball;
every round is admissible; the bands commute (from `comparator:nesting`, built into `Γ`);
`Λ \ S₀ ⊆ V` in every status. -/
structure Item1 : Prop where
  ball_of_split : ∀ s g i, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i)) →
    S.Xt i = S.ball i ∧ up (S.Xt i) ⊆ S.A
  supportCompatible : ∀ (t : Fin S.T) {nl : Site S.Λ → ℕ}
    (E : Transport.EnergyTerms (Site S.Λ) nl S.Term), S.HasSupports E →
    (S.round t).SupportCompatible E
  move_ball : ∀ (t : Fin S.T) h c g, ∃ x : σ,
    ((S.round t).move h c g).subsystem ⊆
      physReg ((GraphDomain.ball S.G S.Λ x S.r₀).subtype (· ∈ S.Λ))
  admissible : ∀ t : Fin S.T, (S.round t).IsAdmissible
  crossBand : ∀ (nl : S.Λ → ℕ) [∀ v, NeZero (nl v)] (d : ℕ) [NeZero d] (τ : ℝ), 0 ≤ τ →
    ∀ (k : ℕ) (t : Fin S.T), (S.round t).CrossBandCommute (Comparators.dims nl d) τ k
  far : ∀ s g, (S.Λ \ S.S₀).subtype (· ∈ S.Λ) ⊆ S.Γ.V s g

open Classical in
/-- Lemma 9.1 (2) (D9.8.3, 5–8). Every assigned site of `A` has oriented depth `≤ j + D + r₀`;
the prefixes are nested, disjoint from `X`, between two consecutive full-row prefixes; every `U`,
`UY` is comparable with a prefix and differs from it by `≤ C n D` sites; the cuts of
`XU, XUY, Y, U, UY` have `≤ C n D` edges and these regions lie in `S₀`; at most `C K n D` terms
split in any joint status. -/
structure Item2 [DecidableRel S.G.Adj] (C : ℝ) : Prop where
  lead : ∀ (t : ℕ), t ≤ S.T → ∀ (h : S.Hist t) (g : Fin S.K) (b : Bool) (x : S.Λ),
    S.stateAt t h g x = some b → x.1 ∈ S.A →
    S.odep b x ≤ S.front g (S.offset t h g) t b + S.D + S.r₀
  nested : ∀ B ∈ S.prefixes, ∀ B' ∈ S.prefixes, B ⊆ B' ∨ B' ⊆ B
  disjoint : ∀ B ∈ S.prefixes, Disjoint B S.X
  rows : ∀ B ∈ S.prefixes, ∃ j, 1 ≤ j ∧ j ≤ S.L ∧
    (S.A.filter fun x => 0 < S.dep x ∧ S.dep x < j).subtype (· ∈ S.Λ) ⊆ B ∧
    B ⊆ (S.A.filter fun x => 0 < S.dep x ∧ S.dep x ≤ j).subtype (· ∈ S.Λ)
  matched : ∀ s g, ∀ Q ∈ ({S.Γ.U s g, S.Γ.U s g ∪ S.Γ.Y s g} : Finset (Finset S.Λ)),
    ∃ B ∈ S.prefixes, (Q ⊆ B ∧ (#(B \ Q) : ℝ) ≤ C * S.n * S.D) ∨
      (B ⊆ Q ∧ (#(Q \ B) : ℝ) ≤ C * S.n * S.D)
  cut : ∀ s g, ∀ Q ∈ ({S.X ∪ S.Γ.U s g, S.X ∪ S.Γ.U s g ∪ S.Γ.Y s g, S.Γ.Y s g, S.Γ.U s g,
      S.Γ.U s g ∪ S.Γ.Y s g} : Finset (Finset S.Λ)),
    (#(GraphDomain.edgeBoundary S.G S.Λ (up Q)) : ℝ) ≤ C * S.n * S.D ∧ up Q ⊆ S.S₀
  splitCount : ∀ s, (#(univ.filter fun i : S.Term =>
    ∃ g, ¬ (S.Γ.part s g).Contains (physReg (S.Xt i))) : ℝ) ≤ C * S.K * S.n * S.D

/-- Lemma 9.1 (3) (D9.8.11). For every labelled term, round and common `p`, the total terminal
weight of the leaves splitting the term is `≤ C D / m`. -/
def Item3 (C : ℝ) : Prop :=
  ∀ (t : Fin S.T) {nl : Site S.Λ → ℕ} (E : Transport.EnergyTerms (Site S.Λ) nl S.Term),
    S.HasSupports E → ∀ (i : S.Term) (p : unitInterval),
      (S.round t).splitWeight E i p ≤ C * S.D / S.m

open Classical in
/-- Lemma 9.1 (4), availability (D9.8.16). At a charge round, on a good old history, in every
band `g`, each term `i` split in band `g` has a slot value `v i` of band `g` (distinct terms,
distinct values) whose choices have total weight `≥ c₁/(n D)`; every such choice moves in band
`g` exactly `X̃_i ∩ Y` to the splitting side, so its entropy `η` is the split entropy of D7.11. -/
def Item4 (c₁ : ℝ) : Prop :=
  ∀ (t : Fin S.T), t.1 % 2 = 1 → ∀ (h : S.Hist t), S.Good t h → ∀ g : Fin S.K,
    ∃ v : S.Term → Fin (S.c t),
      (∀ i i', ¬ ((S.round t).old h g).Contains (physReg (S.Xt i)) →
        ¬ ((S.round t).old h g).Contains (physReg (S.Xt i')) → v i = v i' → i = i') ∧
      ∀ i, ¬ ((S.round t).old h g).Contains (physReg (S.Xt i)) →
        c₁ / (S.n * S.D) ≤
          ∑ c ∈ univ.filter (fun c : S.Ch t => c g = v i), ((S.round t).choiceTree h).weight c ∧
        ∀ c : S.Ch t, c g = v i →
          (S.round t).move h c g =
            (if ((S.round t).old h g).SplitsToP (physReg (S.Xt i)) then
              Transport.Move.toP (physReg (S.Xt i) ∩ ((S.round t).old h g).Y)
            else Transport.Move.toF (physReg (S.Xt i) ∩ ((S.round t).old h g).Y)) ∧
          ∀ (nl : Site S.Λ → ℕ) (θ : Entropy.SiteConfig nl → ℂ),
            (S.round t).eta h c g θ =
              Transport.Round.splitBandEta ((S.round t).old h g) (physReg (S.Xt i)) θ

open Classical in
/-- Lemma 9.1 (4), tail (D9.8.12–15). The history-tree weight of the old histories of round `t`
that are not good is `≤ n^{-M}`. -/
def Tail (Mt : ℝ) : Prop :=
  ∀ t : Fin S.T, ∑ h ∈ univ.filter (fun h => ¬ S.Good t h), (S.histTree t).weight h ≤
    (S.n : ℝ) ^ (-Mt)

end Scan

/-- The scan at the scales of D9.2–D9.6: `L = ⌊n^{1-ℓ}⌋`, `m = ⌊n^μ⌋`, `K = ⌊L/(8m)⌋`,
`D = ⌈n^κ⌉`, `r₀ = ⌈C₁ (log n)²⌉`, `M_n = ⌈C_l n D⌉`. -/
noncomputable abbrev scanAt {σ : Type u} [DecidableEq σ] (G : SimpleGraph σ) (Λ A : Finset σ)
    (dep : σ → ℕ) (R : ℕ) (a : Finset σ → σ) (ℓ κ μ C₁ Cl : ℝ) (n : ℕ) (hm : 0 < m μ n)
    (hM : 0 < Mn Cl n (D κ n)) : Scan σ :=
  ⟨G, Λ, A, dep, R, a, n, L ℓ n, m μ n, K ℓ μ n, D κ n, r₀ C₁ n, Mn Cl n (D κ n), hm, hM⟩

/-- D9.8 **Lemma 9.1** (geometry and probabilities of the scan). Under `scanner:scales` and
`scanner:test-geometry`, for all large `n`:
1. every splitting designated support is a graph `r₀`-ball wholly in `A`; it splits at most one
   band, and there it meets `Y` and exactly one of the two sides; the metric algebras of distinct
   bands commute;
2. every assigned site of `A` has oriented depth `≤ j + D + r₀` on its side; each `U`, `UY` is
   comparable by inclusion with a deterministic positive-depth prefix and differs from it by
   `≤ C n D` sites; the cuts of `U, UY, Y, P₀, V` have `≤ C n D` edges; at most `C K n D` terms
   split in any joint status;
3. for every labelled term, round and common `p`, the total terminal-leaf probability of the
   leaves on which the term splits is `≤ C D / m`;
4. an old history is good if no side has an assigned site of `A` of oriented depth `> j + D/2`;
   for every fixed `M > 0` the probability of not being good is `≤ n^{-M}` (`n` large); at a charge
   round on a good old history each split term is sampled on its splitting side with probability
   `≥ c/(n D)`.
All probabilities are classical path probabilities of the history tree. -/
def Lemma_9_1 : Prop :=
  ∀ {σ : Type u} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj] (V : ℕ → ℕ),
    (∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(GraphDomain.ball G Λ x r) ≤ V r) →
    ∀ (K₀ : ℝ) (m₀ : ℕ), 0 ≤ K₀ → (∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) →
    ∀ (R : ℕ) (ℓ κ μ CT C₁ : ℝ), 0 < ℓ → ℓ < 1 → 0 < κ → κ < μ → μ < 1 - ℓ → 0 < CT →
      0 < C₁ →
    ∃ (Cl C c₁ : ℝ) (n₀ : ℕ), 0 < Cl ∧ 0 < C ∧ 0 < c₁ ∧
      (∀ n : ℕ, n₀ ≤ n → 0 < m μ n ∧ 0 < Mn Cl n (D κ n)) ∧
      (∀ n : ℕ, n₀ ≤ n → ∀ (Λ A : Finset σ) (dep : σ → ℕ) (a : Finset σ → σ)
        (hm : 0 < m μ n) (hM : 0 < Mn Cl n (D κ n)), A ⊆ Λ →
        (∀ Y ∈ GraphDomain.supports G Λ R, a Y ∈ Y) →
        TestGeometry G Λ A dep CT n (L ℓ n) (r₀ C₁ n) →
        (scanAt G Λ A dep R a ℓ κ μ C₁ Cl n hm hM).Item1 ∧
        (scanAt G Λ A dep R a ℓ κ μ C₁ Cl n hm hM).Item2 C ∧
        (scanAt G Λ A dep R a ℓ κ μ C₁ Cl n hm hM).Item3 C ∧
        (scanAt G Λ A dep R a ℓ κ μ C₁ Cl n hm hM).Item4 c₁) ∧
      ∀ Mt : ℝ, 0 < Mt → ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
        ∀ (Λ A : Finset σ) (dep : σ → ℕ) (a : Finset σ → σ)
        (hm : 0 < m μ n) (hM : 0 < Mn Cl n (D κ n)), A ⊆ Λ →
        (∀ Y ∈ GraphDomain.supports G Λ R, a Y ∈ Y) →
        TestGeometry G Λ A dep CT n (L ℓ n) (r₀ C₁ n) →
        (scanAt G Λ A dep R a ℓ κ μ C₁ Cl n hm hM).Tail Mt

end AreaLaw.Scanner
