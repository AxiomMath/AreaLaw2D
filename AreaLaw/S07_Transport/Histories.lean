import AreaLaw.S07_Transport.Means
import AreaLaw.S06_Replicas
import AreaLawForMathlib.Analysis.Matrix.ProjectionCompressionCfc

/-!
# §7.3 Finite histories and entropy gains

Digest `digest/07-transport.md` D7.8–D7.13, paper `paper/sections/06-transport.tex` 245–375.
The data of one round of Proposition 7.4. Tensor factors are an arbitrary finite site type `V`
with local dimensions `n : V → ℕ`, as in the §6 anchors (Lemmas 6.3, 6.4); no geometry.

An operator `X` on `𝒮_k` that commutes with `Π_k` is written on the whole tensor space as
`Π_k X + (1 − Π_k)`: it is `X` on `𝒮_k` and the identity on `𝒮_k^⊥` (the band metric D7.8).

Ported from QICLean, file `QICLean/Representation/ReplicaTransport/States.lean`, commit
`5f76b263e3a1c418645102d90f7bef6b92f04cf3`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix PermutationRepresentation Entropy Arealaw MeasureTheory

namespace AreaLaw.Transport

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ)

/-- The replica tensor space `𝒱^{⊗k}`, `𝒱 = ⨂_v ℂ^{n_v}`. -/
abbrev Config (k : ℕ) := Replicas.Config (fun v => Fin (n v)) k

/-- The projection `Π_k` onto `𝒮_k = Sym^k 𝒱`. -/
noncomputable abbrev Pi (k : ℕ) : Matrix (Config n k) (Config n k) ℂ :=
  symProj (TensorPower.copyPerm (SiteConfig n) k)

theorem Pi_eq_projS (k : ℕ) : Pi n k = Replicas.projS (fun v => Fin (n v)) k :=
  (Replicas.projS_eq (fun v => Fin (n v)) k).symm

/-! ## D7.8 Band metric -/

/-- Three parts `(P, Y, F)` of the tensor factors. -/
structure PYF (V : Type*) where
  /-- The outer part `P`. -/
  P : Finset V
  /-- The middle part `Y`. -/
  Y : Finset V
  /-- The outer part `F`. -/
  F : Finset V

variable {n}

/-- `(P, Y, F)` partitions the tensor factors. -/
def PYF.IsPartition (π : PYF V) : Prop :=
  Disjoint π.P π.Y ∧ Disjoint π.P π.F ∧ Disjoint π.Y π.F ∧ π.P ∪ π.Y ∪ π.F = Finset.univ

variable (n)

/-- D7.8 (`transport:band-metric`). The band metric `A(P, Y, F) = (W_P^{-1} W_F^{-1} W_Y)²` on
`𝒮_k` (§6's `A_k(P, Y, F)`, D6.8), written `Π_k A + (1 − Π_k)` on the whole tensor space. -/
noncomputable def bandMetric (t : ℝ) (k : ℕ) (π : PYF V) : Matrix (Config n k) (Config n k) ℂ :=
  Pi n k * Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F + (1 - Pi n k)

variable {n}

private theorem commute_inv_right {m : Type*} [Fintype m] [DecidableEq m] {X A : Matrix m m ℂ}
    (h : Commute X A) : Commute X A⁻¹ := by
  by_cases hA : IsUnit A.det
  · calc X * A⁻¹ = A⁻¹ * (A * X) * A⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul A hA, Matrix.one_mul]
      _ = A⁻¹ * (X * A) * A⁻¹ := by rw [h.eq]
      _ = A⁻¹ * X := by rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv A hA,
          Matrix.mul_one]
  · rw [nonsing_inv_apply_not_isUnit A hA]
    exact Commute.zero_right X

/-- §6's `A_k(P, Y, F)` commutes with the permutations of entire copies. -/
theorem commute_permOp_A (t : ℝ) (k : ℕ) (P Y F : Finset V) (s : Equiv.Perm (Fin k)) :
    Commute (permOp (TensorPower.copyPerm (SiteConfig n) k) s)
      (Replicas.A (fun v => Fin (n v)) t k P Y F) := by
  have hW : ∀ Q : Finset V, Commute (permOp (TensorPower.copyPerm (SiteConfig n) k) s)
      (Replicas.W (fun v => Fin (n v)) t k Q) := fun Q =>
    TensorPower.commute_copyPerm_labelObservable k Q _ s
  exact (((commute_inv_right (hW _)).mul_right (commute_inv_right (hW _))).mul_right
    (hW _)).pow_right 2

/-- A matrix commuting with every copy permutation commutes with `Π_k`. -/
theorem commute_Pi_of_forall {k : ℕ} {M : Matrix (Config n k) (Config n k) ℂ}
    (h : ∀ s, Commute (permOp (TensorPower.copyPerm (SiteConfig n) k) s) M) :
    Commute (Pi n k) M := by
  rw [Pi, symProj]
  exact (Commute.sum_left _ _ _ fun s _ => h s).smul_left _

theorem commute_Pi_A (t : ℝ) (k : ℕ) (P Y F : Finset V) :
    Commute (Pi n k) (Replicas.A (fun v => Fin (n v)) t k P Y F) :=
  commute_Pi_of_forall fun s => commute_permOp_A t k P Y F s

theorem isHermitian_Pi (k : ℕ) : (Pi n k).IsHermitian := TensorPower.isHermitian_symProj

theorem Pi_mul_Pi (k : ℕ) : Pi n k * Pi n k = Pi n k := TensorPower.symProj_mul_symProj

theorem posDef_A [∀ v, NeZero (n v)] {π : PYF V} (hπ : π.IsPartition) {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) : (Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F).PosDef :=
  (Replicas.eq_replicas_leaf_metric (fun v => Fin (n v)) ht k hπ.1 hπ.2.1 hπ.2.2.1).2.2.2.2.1

/-- D7.8. The band metric of a partition is positive definite; on `𝒮_k` it is
`A(P, Y, F) = (W_P^{-1} W_F^{-1} W_Y)²`, whose three factors commute (D6.8). -/
theorem posDef_bandMetric [∀ v, NeZero (n v)] {π : PYF V} (hπ : π.IsPartition) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) : (bandMetric n t k π).PosDef :=
  (posDef_A hπ ht k).proj_mul_add_one_sub (isHermitian_Pi k) (Pi_mul_Pi k)
    (commute_Pi_A t k π.P π.Y π.F)

theorem commute_Pi_bandMetric (t : ℝ) (k : ℕ) (π : PYF V) :
    Commute (Pi n k) (bandMetric n t k π) :=
  commute_proj_mul_add_one_sub (Commute.refl _) (commute_Pi_A t k π.P π.Y π.F).symm |>.symm

theorem commute_permOp_bandMetric (t : ℝ) (k : ℕ) (π : PYF V) (s : Equiv.Perm (Fin k)) :
    Commute (permOp (TensorPower.copyPerm (SiteConfig n) k) s) (bandMetric n t k π) := by
  have hPs : Commute (permOp (TensorPower.copyPerm (SiteConfig n) k) s) (Pi n k) := by
    have h := congrArg conjTranspose (permOp_mul_symProj (TensorPower.copyPerm (SiteConfig n) k)
      s⁻¹)
    rw [conjTranspose_mul, TensorPower.isHermitian_symProj.eq, conjTranspose_permOp, inv_inv] at h
    change _ * _ = _ * _
    rw [permOp_mul_symProj, h]
  exact (commute_proj_mul_add_one_sub hPs.symm (commute_permOp_A t k π.P π.Y π.F s).symm).symm

/-- D7.8: two band metrics commute as operators on `𝒮_k` exactly when their
whole-space forms `Π_k A + (1 − Π_k)` commute. -/
theorem commute_bandMetric_iff (t : ℝ) (k : ℕ) (π π' : PYF V) :
    Commute (bandMetric n t k π) (bandMetric n t k π') ↔
      ∀ w ∈ Replicas.S (fun v => Fin (n v)) k,
        Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F *ᵥ
            (Replicas.A (fun v => Fin (n v)) t k π'.P π'.Y π'.F *ᵥ w) =
          Replicas.A (fun v => Fin (n v)) t k π'.P π'.Y π'.F *ᵥ
            (Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F *ᵥ w) := by
  set A := Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F
  set B := Replicas.A (fun v => Fin (n v)) t k π'.P π'.Y π'.F
  have hPA := commute_Pi_A (n := n) t k π.P π.Y π.F
  have hPB := commute_Pi_A (n := n) t k π'.P π'.Y π'.F
  have hS : ∀ w, w ∈ Replicas.S (fun v => Fin (n v)) k ↔
      w ∈ invariantSubspace (TensorPower.copyPerm (SiteConfig n) k) := fun w => by
    rw [Replicas.S_eq]
  rw [bandMetric, bandMetric, commute_proj_mul_add_one_sub_iff (Pi_mul_Pi k) hPA hPB]
  constructor
  · intro h w hw
    have hw' : Pi n k *ᵥ w = w := symProj_mulVec_of_mem _ ((hS w).1 hw)
    calc A *ᵥ (B *ᵥ w) = (A * B) *ᵥ (Pi n k *ᵥ w) := by rw [hw', Matrix.mulVec_mulVec]
      _ = (Pi n k * (A * B)) *ᵥ w := by rw [Matrix.mulVec_mulVec, (hPA.mul_right hPB).eq]
      _ = (Pi n k * (B * A)) *ᵥ w := by rw [h]
      _ = (B * A) *ᵥ (Pi n k *ᵥ w) := by rw [Matrix.mulVec_mulVec, (hPB.mul_right hPA).eq]
      _ = B *ᵥ (A *ᵥ w) := by rw [hw', Matrix.mulVec_mulVec]
  · intro h
    have hz : (A * B - B * A) * Pi n k = 0 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      have hw := h _ ((hS _).2 (symProj_mulVec_mem _ w))
      simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, Matrix.sub_mul,
        Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      rw [hw, sub_self]
    have hc : Commute (Pi n k) (A * B - B * A) :=
      (hPA.mul_right hPB).sub_right (hPB.mul_right hPA)
    rw [← sub_eq_zero, ← Matrix.mul_sub, hc.eq, hz]

/-! ## D7.9 A round -/

/-- A move in one band: do nothing, or transfer a tensor subsystem `x ⊆ Y` entirely to `P` or
entirely to `F`. -/
inductive Move (V : Type*) where
  | stay : Move V
  | toP (x : Finset V) : Move V
  | toF (x : Finset V) : Move V

/-- The transferred subsystem (empty for no move). -/
def Move.subsystem : Move V → Finset V
  | stay => ∅
  | toP x => x
  | toF x => x

/-- The new partition after a move. -/
def Move.apply : Move V → PYF V → PYF V
  | stay, π => π
  | toP x, π => ⟨π.P ∪ x, π.Y \ x, π.F⟩
  | toF x, π => ⟨π.P, π.Y \ x, π.F ∪ x⟩

/-- D7.9 (`transport:terminal-weights`, Figure `transport:tree-figure`). The data of a round:
`K` bands; a weighted history tree with leaves `h ∈ 𝓗`; for each `(h, g)` an old partition
`(P_{h,g}, Y_{h,g}, F_{h,g})`; for each `h` a conditional choice tree with leaves `c ∈ 𝓒_h`; a
choice `c` specifies in every band `g` a move (nothing, or a transfer of `x ⊆ Y` to `P` or to
`F`). -/
structure Round (V : Type*) (K : ℕ) (H : Type*) (C : H → Type*) where
  /-- The weighted history tree, leaves `h` with weights `w_h`. -/
  histTree : MeanTree H
  /-- The conditional choice tree at `h`, leaves `c` with weights `q_{c|h}`. -/
  choiceTree : ∀ h, MeanTree (C h)
  /-- The old partition `(P_{h,g}, Y_{h,g}, F_{h,g})`. -/
  old : H → Fin K → PYF V
  /-- The move of choice `c` at history `h` in band `g`. -/
  move : ∀ h, C h → Fin K → Move V

namespace Round

variable {K : ℕ} {H : Type*} {C : H → Type*} (R : Round V K H C)

/-- The new partition of choice `c` at `h` in band `g`. -/
def new (h : H) (c : C h) (g : Fin K) : PYF V := (R.move h c g).apply (R.old h g)

/-- The terminal leaves `j = (h, old)` (`⟨h, none⟩`) and `j = (h, c, new)` (`⟨h, some c⟩`). -/
abbrev Leaf (H : Type*) (C : H → Type*) := Σ h, Option (C h)

/-- The partition of band `g` at a terminal leaf. -/
def leafPart : Leaf H C → Fin K → PYF V
  | ⟨h, none⟩, g => R.old h g
  | ⟨h, some c⟩, g => R.new h c g

/-- D7.9 standing hypotheses: positive weights `w_h > 0`, `q_{c|h} > 0` (edges of weight `0`
omitted, all retained weights positive), distinct leaves, old parts partition the factors, every
move transfers a subsystem of `Y`. -/
structure IsAdmissible [DecidableEq H] [∀ h, DecidableEq (C h)] : Prop where
  histWeight_pos : ∀ h, 0 < R.histTree.weight h
  choiceWeight_pos : ∀ h c, 0 < (R.choiceTree h).weight c
  hist_nodup : R.histTree.labels.Nodup
  choice_nodup : ∀ h, (R.choiceTree h).labels.Nodup
  old_isPartition : ∀ h g, (R.old h g).IsPartition
  move_subset : ∀ h c g, (R.move h c g).subsystem ⊆ (R.old h g).Y

variable (n)

/-- D7.9 cross-band commutation: every old or new metric of band `g` commutes with every old or
new metric of band `g' ≠ g`, across all histories and choices, as operators on `𝒮_k` (no
commutation within a band). By `commute_bandMetric_iff` this is commutation of the whole-space
band metrics. -/
def CrossBandCommute (t : ℝ) (k : ℕ) : Prop :=
  ∀ j j' g g', g ≠ g' → Commute (bandMetric n t k (R.leafPart j g))
    (bandMetric n t k (R.leafPart j' g'))

/-- D7.9. `A_h = ∏_{g=1}^K A_{h,g}`. -/
noncomputable def oldMetric (t : ℝ) (k : ℕ) (h : H) : Matrix (Config n k) (Config n k) ℂ :=
  (List.ofFn fun g => bandMetric n t k (R.old h g)).prod

/-- D7.9. `A_{h,c} = ∏_{g=1}^K A_{h,c,g}`. -/
noncomputable def newMetric (t : ℝ) (k : ℕ) (h : H) (c : C h) :
    Matrix (Config n k) (Config n k) ℂ :=
  (List.ofFn fun g => bandMetric n t k (R.new h c g)).prod

/-- The metric `A_j` of a terminal leaf: `A_h` at `(h, old)`, `A_{h,c}` at `(h, c, new)`. -/
noncomputable def input (t : ℝ) (k : ℕ) : Leaf H C → Matrix (Config n k) (Config n k) ℂ
  | ⟨h, none⟩ => R.oldMetric n t k h
  | ⟨h, some c⟩ => R.newMetric n t k h c

theorem input_eq_prod (t : ℝ) (k : ℕ) (j : Leaf H C) :
    R.input n t k j = (List.ofFn fun g => bandMetric n t k (R.leafPart j g)).prod := by
  rcases j with ⟨h, _ | c⟩ <;> rfl

/-- D7.9. `B_h`, the root of the choice tree at `h` with inputs `A_{h,c}`. -/
noncomputable def choiceRoot (t : ℝ) (k : ℕ) (h : H) : Matrix (Config n k) (Config n k) ℂ :=
  (R.choiceTree h).eval (R.newMetric n t k h)

/-- D7.14. `C_h = A_h^{-1/2} B_h A_h^{-1/2}`. -/
noncomputable def relRatio (t : ℝ) (k : ℕ) (h : H) : Matrix (Config n k) (Config n k) ℂ :=
  R.oldMetric n t k h ^ (-(1 / 2) : ℝ) * R.choiceRoot n t k h *
    R.oldMetric n t k h ^ (-(1 / 2) : ℝ)

variable {n}

/-- D7.9. The terminal tree at parameter `p`: each old input `h` of the history tree is
replaced by the vertex `A_h #_p B_h`, whose second child is the choice tree at `h`. -/
def tree (p : I) : MeanTree (Leaf H C) :=
  R.histTree.bind fun h => .node p (.leaf ⟨h, none⟩) ((R.choiceTree h).map fun c => ⟨h, some c⟩)

variable (n)

/-- D7.9. The interpolated root `𝓜(p)` (for `p ∈ [0, 1]`; clamped outside). -/
noncomputable def root (t : ℝ) (k : ℕ) (p : ℝ) : Matrix (Config n k) (Config n k) ℂ :=
  (R.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).eval (R.input n t k)

variable {n}

theorem root_eq (t : ℝ) (k : ℕ) (p : I) :
    R.root n t k p = R.histTree.eval fun h =>
      geomMean p (R.oldMetric n t k h) (R.choiceRoot n t k h) := by
  have hp : Set.projIcc (0 : ℝ) 1 zero_le_one (p : ℝ) = p := Set.projIcc_val zero_le_one p
  simp only [root, hp, tree, MeanTree.eval_bind, MeanTree.eval_node, MeanTree.eval_leaf,
    MeanTree.eval_map]
  rfl

/-! ### Terminal weights -/

section Weights

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem _root_.AreaLaw.Transport.MeanTree.weight_bind_of_forall_ne (T : MeanTree ι)
    {f : ι → MeanTree κ} {h₀ : ι} {j : κ} (hf : ∀ h ≠ h₀, (f h).weight j = 0) :
    (T.bind f).weight j = T.weight h₀ * (f h₀).weight j := by
  induction T with
  | leaf h =>
    by_cases hh : h = h₀
    · subst hh; simp [MeanTree.bind, MeanTree.weight]
    · simp [MeanTree.bind, MeanTree.weight, hf h hh, Pi.single_eq_of_ne' hh]
  | node p l r ihl ihr =>
    simp only [MeanTree.bind, MeanTree.weight_node, ihl, ihr]; ring

omit [DecidableEq ι] in
theorem _root_.AreaLaw.Transport.MeanTree.weight_map_of_forall_ne (T : MeanTree ι)
    {g : ι → κ} {j : κ} (hj : ∀ c, g c ≠ j) : (T.map g).weight j = 0 := by
  induction T with
  | leaf c => simp [MeanTree.map, MeanTree.bind, MeanTree.weight, Pi.single_eq_of_ne' (hj c)]
  | node p l r ihl ihr =>
    simp only [MeanTree.map, MeanTree.bind, MeanTree.weight_node] at ihl ihr ⊢
    rw [ihl, ihr]; ring

theorem _root_.AreaLaw.Transport.MeanTree.weight_map_apply (T : MeanTree ι) {g : ι → κ}
    (hg : Function.Injective g) (c : ι) : (T.map g).weight (g c) = T.weight c := by
  rw [MeanTree.map, MeanTree.weight_bind_of_forall_ne T (h₀ := c)]
  · simp [MeanTree.weight]
  · intro h hh
    simp [MeanTree.weight, Pi.single_eq_of_ne' (hg.ne hh)]

end Weights

variable [DecidableEq H] [∀ h, DecidableEq (C h)]

omit [Fintype V] [DecidableEq V] in
/-- D7.9 (`transport:terminal-weights`). `π_{(h,old)} = (1 − p) w_h`. -/
theorem weight_tree_old (p : I) (h : H) :
    (R.tree p).weight ⟨h, none⟩ = (1 - (p : ℝ)) * R.histTree.weight h := by
  rw [tree, MeanTree.weight_bind_of_forall_ne _ (h₀ := h)]
  · rw [MeanTree.weight_node, MeanTree.weight_map_of_forall_ne _ (by simp)]
    simp [MeanTree.weight]; ring
  · intro h' hh'
    rw [MeanTree.weight_node, MeanTree.weight_map_of_forall_ne _ (by simp [hh'])]
    simp [MeanTree.weight,
      Pi.single_eq_of_ne' (by simp [hh'] : (⟨h', none⟩ : Leaf H C) ≠ ⟨h, none⟩)]

omit [Fintype V] [DecidableEq V] in
/-- D7.9 (`transport:terminal-weights`). `π_{(h,c,new)} = p w_h q_{c|h}`. -/
theorem weight_tree_new (p : I) (h : H) (c : C h) :
    (R.tree p).weight ⟨h, some c⟩ = (p : ℝ) * R.histTree.weight h * (R.choiceTree h).weight c := by
  rw [tree, MeanTree.weight_bind_of_forall_ne _ (h₀ := h)]
  · rw [MeanTree.weight_node, MeanTree.weight_map_apply (R.choiceTree h)
      (g := fun c => (⟨h, some c⟩ : Leaf H C)) (fun a b hab => by simpa using hab)]
    simp [MeanTree.weight]; ring
  · intro h' hh'
    rw [MeanTree.weight_node, MeanTree.weight_map_of_forall_ne _ (by simp [hh'])]
    simp [MeanTree.weight,
      Pi.single_eq_of_ne' (by simp [hh'] : (⟨h', none⟩ : Leaf H C) ≠ ⟨h, some c⟩)]

omit [Fintype V] [DecidableEq V] in
/-- D7.9 Output: `∑_j π_j = ∑_h w_h [(1 − p) + p ∑_c q_{c|h}] = 1`. -/
theorem sum_weight_tree [Fintype H] [∀ h, Fintype (C h)] (p : I) :
    ∑ j, (R.tree p).weight j = 1 := (R.tree p).sum_weight

/-- Every terminal weight is positive for `0 < p < 1`. -/
theorem weight_tree_pos (hR : R.IsAdmissible) {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (j : Leaf H C) : 0 < (R.tree p).weight j := by
  obtain ⟨h, _ | c⟩ := j
  · rw [weight_tree_old]; exact mul_pos (by linarith) (hR.histWeight_pos h)
  · rw [weight_tree_new]
    exact mul_pos (mul_pos hp0 (hR.histWeight_pos h)) (hR.choiceWeight_pos h c)

omit [DecidableEq H] [∀ h, DecidableEq (C h)] in
theorem mem_labels_map {ι κ : Type*} (T : MeanTree ι) {g : ι → κ} {j : κ}
    (hj : j ∈ (T.map g).labels) : ∃ c, g c = j := by
  classical
  induction T with
  | leaf c =>
    simp only [MeanTree.map, MeanTree.bind, MeanTree.labels, List.mem_singleton] at hj
    exact ⟨c, hj.symm⟩
  | node p l r ihl ihr =>
    simp only [MeanTree.map, MeanTree.bind, MeanTree.labels, List.mem_append] at hj ihl ihr
    rcases hj with hj | hj
    · exact ihl hj
    · exact ihr hj

/-! ### Partitions and inputs at the terminal leaves -/

omit [DecidableEq H] [∀ h, DecidableEq (C h)] in
theorem Move.isPartition_apply {π : PYF V} (hπ : π.IsPartition) {m : Move V}
    (hm : m.subsystem ⊆ π.Y) : (m.apply π).IsPartition := by
  obtain ⟨hPY, hPF, hYF, hU⟩ := hπ
  cases m with
  | stay => exact ⟨hPY, hPF, hYF, hU⟩
  | toP x =>
    have hx : x ⊆ π.Y := hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Finset.disjoint_union_left.mpr ⟨hPY.mono_right Finset.sdiff_subset,
        Finset.disjoint_sdiff⟩
    · exact Finset.disjoint_union_left.mpr ⟨hPF, hYF.mono_left hx⟩
    · exact hYF.mono_left Finset.sdiff_subset
    · rw [← hU]; ext a; have hxa := @hx a
      simp only [Move.apply, Finset.mem_union, Finset.mem_sdiff]; tauto
  | toF x =>
    have hx : x ⊆ π.Y := hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hPY.mono_right Finset.sdiff_subset
    · exact Finset.disjoint_union_right.mpr ⟨hPF, hPY.mono_right hx⟩
    · exact Finset.disjoint_union_right.mpr ⟨hYF.mono_left Finset.sdiff_subset,
        Finset.sdiff_disjoint⟩
    · rw [← hU]; ext a; have hxa := @hx a
      simp only [Move.apply, Finset.mem_union, Finset.mem_sdiff]; tauto

theorem isPartition_leafPart (hR : R.IsAdmissible) (j : Leaf H C) (g : Fin K) :
    (R.leafPart j g).IsPartition := by
  obtain ⟨h, _ | c⟩ := j
  · exact hR.old_isPartition h g
  · exact Move.isPartition_apply (hR.old_isPartition h g) (hR.move_subset h c g)

private theorem posDef_listProd_ofFn' {m : Type*} [Fintype m] [DecidableEq m] {K : ℕ}
    {D : Fin K → Matrix m m ℂ} (hD : ∀ g, (D g).PosDef)
    (hcomm : ∀ g g', g ≠ g' → Commute (D g) (D g')) : (List.ofFn D).prod.PosDef := by
  induction K with
  | zero => simpa using PosDef.one
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine (hD 0).mul_of_commute (ih (D := fun g ↦ D g.succ) (fun g ↦ hD _)
      (fun g g' h ↦ hcomm _ _ (fun h' ↦ h (Fin.succ_injective _ h'))))
      (Commute.list_prod_right _ _ fun y hy ↦ ?_)
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
    exact hcomm _ _ (Fin.succ_ne_zero g).symm

/-- The terminal metrics `A_j` are positive definite. -/
theorem posDef_input [∀ v, NeZero (n v)] (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) (j : Leaf H C) : (R.input n t k j).PosDef := by
  rw [input_eq_prod]
  exact posDef_listProd_ofFn' (fun g => posDef_bandMetric (R.isPartition_leafPart hR j g) ht k)
    (fun g g' hgg' => hcomm j j g g' hgg')

omit [DecidableEq H] [∀ h, DecidableEq (C h)] in
/-- The terminal metrics commute with every copy permutation, hence with `Π_k`. -/
theorem commute_permOp_input {t : ℝ} (k : ℕ) (s : Equiv.Perm (Fin k)) (j : Leaf H C) :
    Commute (permOp (TensorPower.copyPerm (SiteConfig n) k) s) (R.input n t k j) := by
  rw [input_eq_prod]
  exact Commute.list_prod_right _ _ fun y hy => by
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
    exact commute_permOp_bandMetric t k _ s

end Round

/-! ## D7.10 Entropy of a move, scale `ℓ` -/

namespace Round

variable {K : ℕ} {H : Type*} {C : H → Type*} (R : Round V K H C)

/-- D7.10 (`transport:move-eta`). For a unit `θ ∈ 𝒱` and a move of `x` to `P` with `Y = x Y₀`:
`η_{h,c,g}(θ) = S_θ(x|P) + S_θ(x|Y₀) = I_θ(x:F|P)` (here in the form `I_θ(x:F|Y₀)`, equal to
it by purity of `θ` on `P x Y₀ F`, as Lemma 6.3 states it); move to `F`: exchange `P, F`;
no move: `η = 0`. -/
noncomputable def moveEta (π : PYF V) : Move V → (SiteConfig n → ℂ) → ℝ
  | .stay => fun _ => 0
  | .toP x => Replicas.η x (π.Y \ x) π.F
  | .toF x => Replicas.η x (π.Y \ x) π.P

/-- D7.10. `η_{h,c,g}`. -/
noncomputable def eta (h : H) (c : C h) (g : Fin K) : (SiteConfig n → ℂ) → ℝ :=
  moveEta (R.old h g) (R.move h c g)

end Round

/-- D7.10. `log(e dim x)` for a tensor subsystem `x` (§5's `ℓ`). -/
noncomputable abbrev logDim (x : Finset V) : ℝ :=
  ℓ (Fintype.card (Reg (fun v => Fin (n v)) x))

/-! ## D7.11 Energy terms, designated supports, splits -/

/-- D7.11. Energy terms `0 ≤ h_i ≤ I` on physical tensor factors with designated tensor
supports `D_i ⊇ supp h_i`: `h_i` is the lift of `K_i` on `D_i`. -/
structure EnergyTerms (V : Type*) [Fintype V] [DecidableEq V] (n : V → ℕ) (ι : Type*) where
  /-- The designated support `D_i`. -/
  support : ι → Finset V
  /-- `h_i` on its designated support. -/
  op : ∀ i, Matrix (RegionConfig n (support i)) (RegionConfig n (support i)) ℂ
  /-- `0 ≤ h_i`. -/
  nonneg : ∀ i, 0 ≤ op i
  /-- `h_i ≤ I`. -/
  le_one : ∀ i, op i ≤ 1

namespace EnergyTerms

variable {ι : Type*} (E : EnergyTerms V n ι)

/-- D7.11. The term `h_i` on `𝒱`. -/
noncomputable def term (i : ι) : Matrix (SiteConfig n) (SiteConfig n) ℂ :=
  localLift (E.support i) (E.op i)

theorem isSupportedOn_term (i : ι) : IsSupportedOn (E.term i) (E.support i) :=
  isSupportedOn_localLift _ _

/-- D7.12 (`transport:replica-energy`). `h̄_i = (1/k ∑_r h_{i,r})|_{𝒮_k}`. -/
noncomputable def hbar (k : ℕ) (i : ι) : Matrix (Config n k) (Config n k) ℂ :=
  TensorPower.copyMean n k (E.term i)

/-- D7.12 (`transport:replica-energy`). `H̄ = ∑_i h̄_i`. -/
noncomputable def Hbar [Fintype ι] (k : ℕ) : Matrix (Config n k) (Config n k) ℂ :=
  ∑ i, E.hbar k i

end EnergyTerms

/-- `D` lies in one part of `π`. -/
def PYF.Contains (π : PYF V) (D : Finset V) : Prop := D ⊆ π.P ∨ D ⊆ π.Y ∨ D ⊆ π.F

/-- `D` meets `Y` and `P` but not `F` (a split with receiving side `P`). -/
def PYF.SplitsToP (π : PYF V) (D : Finset V) : Prop :=
  (D ∩ π.Y).Nonempty ∧ (D ∩ π.P).Nonempty ∧ Disjoint D π.F

/-- `D` meets `Y` and `F` but not `P` (a split with receiving side `F`). -/
def PYF.SplitsToF (π : PYF V) (D : Finset V) : Prop :=
  (D ∩ π.Y).Nonempty ∧ (D ∩ π.F).Nonempty ∧ Disjoint D π.P

namespace Round

variable {K : ℕ} {H : Type*} {C : H → Type*} (R : Round V K H C) {ι : Type*}

/-- D7.11. Support compatibility: for each terminal leaf and band, `D_i` lies in one of the
three parts `P, Y, F`, except possibly in one exceptional band, where `D_i` meets `Y` and exactly
one of `P, F`. -/
def SupportCompatible (E : EnergyTerms V n ι) : Prop :=
  ∀ j i g, (R.leafPart j g).Contains (E.support i) ∨
    (((R.leafPart j g).SplitsToP (E.support i) ∨ (R.leafPart j g).SplitsToF (E.support i)) ∧
      ∀ g' ≠ g, (R.leafPart j g').Contains (E.support i))

open Classical in
/-- D7.11. `𝒥_i`, the leaves that split `i`. -/
noncomputable def splitLeaves [Fintype H] [∀ h, Fintype (C h)] (E : EnergyTerms V n ι) (i : ι) :
    Finset (Leaf H C) :=
  Finset.univ.filter fun j => ∃ g, ¬ (R.leafPart j g).Contains (E.support i)

open Classical in
/-- D7.11. At a split of `i` in band `g`, with `x = D_i ∩ Y` and receiving side `P` (or `F`),
`η_{i,j}` is the D7.10 formula for this `x` and side: `I_θ(x:F|Y \ x)` (or `I_θ(x:P|Y \ x)`). -/
noncomputable def splitBandEta (π : PYF V) (D : Finset V) : (SiteConfig n → ℂ) → ℝ :=
  if π.SplitsToP D then Replicas.η (D ∩ π.Y) (π.Y \ D) π.F
  else Replicas.η (D ∩ π.Y) (π.Y \ D) π.P

open Classical in
/-- D7.11. `η_{i,j}`: the split entropy of the exceptional band of `i` at leaf `j`. -/
noncomputable def splitEta (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C) :
    (SiteConfig n → ℂ) → ℝ :=
  fun θ => ∑ g ∈ Finset.univ.filter fun g => ¬ (R.leafPart j g).Contains (E.support i),
    splitBandEta (R.leafPart j g) (E.support i) θ

/-- D7.12. `W_i(p) = ∑_{j ∈ 𝒥_i} π_j`. -/
noncomputable def splitWeight [Fintype H] [∀ h, Fintype (C h)] [DecidableEq H]
    [∀ h, DecidableEq (C h)] (E : EnergyTerms V n ι) (i : ι) (p : I) : ℝ :=
  ∑ j ∈ R.splitLeaves E i, (R.tree p).weight j

/-! ## D7.12 Replica energy and commutation at unsplit leaves -/

/-- `h̄_i` commutes with `Π_k`. -/
theorem commute_Pi_hbar (E : EnergyTerms V n ι) (k : ℕ) (i : ι) :
    Commute (Pi n k) (E.hbar k i) :=
  commute_Pi_of_forall fun s => TensorPower.commute_copyPerm_copyMean k (E.term i) s

/-- D7.12 (`transport:replica-energy`). If leaf `j` does not split `i`, then `[A_j, h̄_i] = 0`. -/
theorem step_7_12 [∀ v, NeZero (n v)] [DecidableEq H] [∀ h, DecidableEq (C h)]
    (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (E : EnergyTerms V n ι) (i : ι) (j : Leaf H C)
    (hj : ∀ g, (R.leafPart j g).Contains (E.support i)) :
    Commute (R.input n t k j) (E.hbar k i) := by
  rw [input_eq_prod]
  refine Commute.list_prod_left _ _ fun y hy => ?_
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
  obtain ⟨hPY, hPF, hYF, -⟩ := R.isPartition_leafPart hR j g
  -- D7.12.1: in every band `D_i` lies in one part `Q ∈ {P, Y, F}`, so `∑_r h_{i,r}` commutes
  -- with the copy permutations of each of `P, Y, F`; D7.12.2: the band metric is a function
  -- of their Schur labels (§6, D6.9.3)
  have hA := Replicas.eq_replicas_leaf_floor_3 ht k hPY hPF hYF (E.isSupportedOn_term i) (hj g)
  exact commute_proj_mul_add_one_sub (commute_Pi_hbar E k i) hA

end Round

/-! ## D7.13 Coherent vectors and measures -/

/-- D7.13 (`transport:coherent-measure`). `P_{θ,k} = |θ^{⊗k}⟩⟨θ^{⊗k}|`, `D_k = dim 𝒮_k`,
`dμ_σ(θ) = D_k Tr(σ P_{θ,k}) dθ` with `dθ` the Haar probability on the unit sphere of `𝒱` (§6's
`Replicas.P`, `Replicas.D`, `Replicas.μ`, D6.11). For a density matrix `σ` on `𝒮_k`, `μ_σ` is a
probability measure since `D_k ∫ P_{θ,k} dθ = I_{𝒮_k}`; also
`D_k = binom(k + dim 𝒱 − 1, dim 𝒱 − 1)`, polynomial in `k`. -/
theorem eq_transport_coherent_measure {Fac : Type*} [Fintype Fac] [DecidableEq Fac]
    (ι : Fac → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)]
    (k : ℕ) :
    (Replicas.D ι k : ℂ) • Matrix.of (fun x y => ∫ θ, Replicas.P ι k θ.1 x y ∂(Replicas.dθ ι)) =
      Replicas.projS ι k ∧
    (∀ ρ : Matrix (Replicas.Config ι k) (Replicas.Config ι k) ℂ, ρ.PosSemidef → ρ.trace = 1 →
      (∀ π, Replicas.U ι k Finset.univ π * ρ = ρ) →
        MeasureTheory.IsProbabilityMeasure (Replicas.μ ι k ρ)) ∧
    Replicas.D ι k = (k + Fintype.card ((f : Fac) → ι f) - 1).choose
      (Fintype.card ((f : Fac) → ι f) - 1) := by
  have hd : 0 < Fintype.card ((f : Fac) → ι f) := Fintype.card_pos
  have hD : (Replicas.D ι k : ℂ) ≠ 0 := by
    rw [Replicas.D_eq_choose ι k hd]
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  refine ⟨?_, fun ρ hρp hρt hρ => Replicas.eq_replicas_husimi ι k hρp hρt hρ,
    Replicas.D_eq_choose ι k hd⟩
  rw [Replicas.eq_replicas_resolution, smul_smul, mul_inv_cancel₀ hD, one_smul]

end AreaLaw.Transport
