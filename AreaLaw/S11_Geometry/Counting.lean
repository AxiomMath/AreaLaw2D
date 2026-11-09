import AreaLaw.S11_Geometry.Separation

/-! # §11.7 Counting exceptional sites

The total number of belt cells and marks (D11.19), the bounded exceptional set (D11.20) and the
summability of the scanner weights (D11.25.4). The constants depend on `C₀`, `k₀` and `S_*`
only: not on the cut, the domain, the shifts or the last layer `K`.

Digest `digest/11-geometry.md` D11.19, D11.20, D11.25 -/

open Set Metric Real

namespace AreaLaw.Geometry

noncomputable section

/-! ## D11.19 Repair counts -/

/-- D11.19.3. Each initial mark of scale `S` spawns at most `C (log(S+2))^C` marks, with `C`
depending on `S_*` only. -/
theorem step_11_19_3 {S_star : ℝ} (hS : 1 < S_star) : ∃ C : ℝ, 0 < C ∧
    ∀ {I M₀ : Type} (R : Repair I M₀), R.Hyp → R.stopScale = S_star → ∀ r : M₀,
      ({m : Mark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ) ≤ C * log (R.S₀ r + 2) ^ C := by
  classical
  obtain ⟨C, hC, hcount⟩ := step_11_19_2 hS
  refine ⟨C, hC, fun {I M₀} R hR hRS r => ?_⟩
  subst hRS
  obtain ⟨N, hN⟩ := hR.step_11_15_7 r
  have hP0 : R.stopScale ≤ d^[0] (R.S₀ r) := hR.stopScale_le_S₀ r
  set G := Nat.findGreatest (fun j => R.stopScale ≤ d^[j] (R.S₀ r)) N
  -- D11.19.1: the generations are bounded by the depth
  have hsub : {m : Mark M₀ | R.IsMark m ∧ m.root = r} ⊆ ↑(Repair.marksUpTo r G) := by
    rintro m ⟨hm, hr⟩
    refine Repair.mem_marksUpTo hr (Nat.le_findGreatest (hN m hm hr) ?_)
    simpa [Repair.S, hr] using hR.stopScale_le_S hm
  -- D11.19.2: at most nine children per mark
  calc ({m : Mark M₀ | R.IsMark m ∧ m.root = r}.ncard : ℝ) ≤ (Repair.marksUpTo r G).card := by
        rw [← ncard_coe_finset]; exact_mod_cast ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ _ := Repair.card_marksUpTo_le r G
    _ ≤ C * log (R.S₀ r + 2) ^ C :=
        hcount _ (by linarith [hR.two_le_stopScale, hR.stopScale_le_S₀ r]) _
          (Nat.findGreatest_spec (P := fun j => R.stopScale ≤ d^[j] (R.S₀ r)) (Nat.zero_le N) hP0)

namespace Layout

variable (L : Layout)

/-- D11.9. The shifts of `L` realize the belt-cell count of D11.9 in every layer. -/
def BeltSparse : Prop :=
  ∀ k, ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ) ≤
    8 * layerCount 2 L.C₀ * L.Z.card * (2 : ℝ) ^ (-(k * δ₀ / 2))

variable {L}

/-- D11.12. The initial marks of layer `k` number at most nine per belt cell of layer `k`. -/
lemma card_markLayer_le (k : ℕ) :
    (Finset.univ.filter fun r : L.marks => L.markLayer r = k).card ≤
      9 * (beltIndex o₂ L.Z L.C₀ k (L.a k)).card := by
  classical
  calc _ ≤ ((beltIndex o₂ L.Z L.C₀ k (L.a k)).biUnion
        fun w => Finset.univ.image (markPos k w)).card := by
        refine Finset.card_le_card_of_injOn (fun r => r.1) (fun r hr => ?_)
          (fun r _ r' _ h => Subtype.ext h)
        obtain ⟨-, -, w, hw, e, he⟩ := L.marks_markLayer r
        have hk : L.markLayer r = k := (Finset.mem_filter.1 hr).2
        rw [hk] at hw he
        exact Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_image.2 ⟨e, Finset.mem_univ _, he⟩⟩
    _ ≤ (beltIndex o₂ L.Z L.C₀ k (L.a k)).card * 9 :=
        Finset.card_biUnion_le_card_mul _ _ _ fun w _ => Finset.card_image_le.trans (by simp)
    _ = _ := mul_comm _ _

/-- `log(t_k + 2) ≤ 2(k+1)`. -/
lemma log_t_add_two_le (k : ℕ) : log ((t k : ℝ) + 2) ≤ 2 * ((k : ℝ) + 1) := by
  have ht : (t k : ℝ) ≤ 2 ^ k := (scale_facts k).2.2.2.1
  have ht0 : (0 : ℝ) < t k := (scale_facts k).2.2.1
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  calc log ((t k : ℝ) + 2) ≤ log ((2 : ℝ) ^ (k + 2)) :=
        log_le_log (by positivity) (by rw [pow_add]; nlinarith)
    _ = (k + 2) * log 2 := by rw [log_pow]; push_cast; ring
    _ ≤ (k + 2) * 1 := by gcongr; exact (log_two_lt_d9.trans (by norm_num)).le
    _ ≤ 2 * ((k : ℝ) + 1) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

end Layout

/-- D11.19 (`geometry:descendant-count`, `geometry:total-repairs`). For an initial mark of scale
`S`: depth `≤ C + C log log(e^e+S)`; at most nine children per mark; hence marks and
replacements descended from it number `≤ C(log(S+2))^C`. For a mark from layer `k`, `S ≍ t_k`,
`log S ≤ C(k+1)`. Total number of belt tiles, marks and replacements
`≤ Cb ∑_{k≥k₀} 2^{-kδ₀/2}(k+1)^C ≤ C'b`. Here: belt cells and marks number `≤ C'|Z|`
(`|Z| ≤ 2b`), `C'` depending on `C₀` and `S_*` only.
2D only: at most nine children per mark and nine marks per belt cell (planar squares). -/
theorem step_11_19 (C₀ : ℕ) {S_star : ℝ} (hS : 1 < S_star) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : Layout, L.C₀ = C₀ → L.stopScale = S_star → L.BeltSparse →
      (∑ k ∈ Finset.Ico L.k₀ L.K, ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ)) ≤
        C * L.Z.card ∧
      ({m : Mark L.marks | L.repair.IsMark m}.ncard : ℝ) ≤ C * L.Z.card := by
  classical
  obtain ⟨E, hE, hcount⟩ := step_11_19_3 hS
  set f : ℕ → ℝ := fun k => (2 : ℝ) ^ (-(k * δ₀ / 2)) * ((k : ℝ) + 1) ^ E with hf_def
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  -- D11.19.4: the series converges
  have hf : Summable f := (step_11_19_4 1 E zero_le_one).1
  set B := ∑' k, f k
  have hB : 0 ≤ B := tsum_nonneg hf0
  have hpart : ∀ F : Finset ℕ, ∑ k ∈ F, f k ≤ B := fun F => hf.sum_le_tsum F fun k _ => hf0 k
  set c : ℝ := 8 * layerCount 2 C₀
  have hc : 0 ≤ c := by positivity
  refine ⟨c * B * (1 + 9 * E * 2 ^ E), by positivity, fun L hC₀ hS' hsp => ?_⟩
  have hZ : (0 : ℝ) ≤ L.Z.card := Nat.cast_nonneg _
  -- D11.19.3: belt cells per layer, `≤ C|Z|2^{-kδ₀/2} ≤ C|Z| f k`
  have hbelt : ∀ k, ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ) ≤ c * L.Z.card * f k := by
    intro k
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ E :=
      one_le_rpow (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hE.le
    have h0 : (0 : ℝ) ≤ c * L.Z.card * (2 : ℝ) ^ (-(k * δ₀ / 2)) := by positivity
    calc ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ)
        ≤ c * L.Z.card * (2 : ℝ) ^ (-(k * δ₀ / 2)) := (hsp k).trans_eq (by rw [hC₀])
      _ ≤ c * L.Z.card * (2 : ℝ) ^ (-(k * δ₀ / 2)) * ((k : ℝ) + 1) ^ E :=
          le_mul_of_one_le_right h0 h1
      _ = c * L.Z.card * f k := by rw [hf_def]; ring
  have hsumf : ∑ k ∈ Finset.Ico L.k₀ L.K, f k ≤ B := hpart _
  refine ⟨?_, ?_⟩
  · -- D11.19.4: the belt cells
    calc (∑ k ∈ Finset.Ico L.k₀ L.K, ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ))
        ≤ ∑ k ∈ Finset.Ico L.k₀ L.K, c * L.Z.card * f k := Finset.sum_le_sum fun k _ => hbelt k
      _ = c * L.Z.card * ∑ k ∈ Finset.Ico L.k₀ L.K, f k := by rw [Finset.mul_sum]
      _ ≤ c * L.Z.card * B := by gcongr
      _ ≤ c * B * (1 + 9 * E * 2 ^ E) * L.Z.card := by
          have : 0 ≤ c * B * (9 * E * 2 ^ E) * L.Z.card := by positivity
          nlinarith
  · -- D11.19.3–4: the marks, grouped by their initial mark and its layer
    have hR := L.lemma_11_3.1
    have hfin := hR.finite_isMark
    set S := hfin.toFinset
    have h1 : ({m : Mark L.marks | L.repair.IsMark m}.ncard : ℝ) =
        ∑ r : L.marks, ((S.filter fun m => m.root = r).card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (f := Mark.root)
        (t := Finset.univ) fun _ _ => Finset.mem_univ _
    have h2 : ∀ r : L.marks, ((S.filter fun m => m.root = r).card : ℝ) ≤
        E * 2 ^ E * ((L.markLayer r : ℝ) + 1) ^ E := by
      intro r
      have e : ((S.filter fun m => m.root = r : Finset (Mark L.marks)) : Set (Mark L.marks)) =
          {m | L.repair.IsMark m ∧ m.root = r} := by
        ext m; simp [S]
      have h := hcount L.repair hR hS' r
      rw [← e, ncard_coe_finset] at h
      refine h.trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hE.le
      have hSr : L.repair.S₀ r = t (L.markLayer r) := rfl
      have hl0 : 0 ≤ log ((t (L.markLayer r) : ℝ) + 2) :=
        log_nonneg (by linarith [(scale_facts (L.markLayer r)).2.2.1])
      rw [hSr]
      calc log ((t (L.markLayer r) : ℝ) + 2) ^ E ≤ (2 * ((L.markLayer r : ℝ) + 1)) ^ E :=
            rpow_le_rpow hl0 (Layout.log_t_add_two_le _) hE.le
        _ = 2 ^ E * ((L.markLayer r : ℝ) + 1) ^ E := mul_rpow (by norm_num) (by positivity)
    have h3 : ∑ r : L.marks, E * 2 ^ E * ((L.markLayer r : ℝ) + 1) ^ E ≤
        9 * E * 2 ^ E * (c * L.Z.card * B) := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Ico L.k₀ L.K)
        (g := L.markLayer) fun r _ =>
          Finset.mem_Ico.2 ⟨(L.marks_markLayer r).1, (L.marks_markLayer r).2.1⟩]
      have hfib : ∀ k ∈ Finset.Ico L.k₀ L.K,
          ∑ r ∈ Finset.univ.filter (fun r : L.marks => L.markLayer r = k),
            E * 2 ^ E * ((L.markLayer r : ℝ) + 1) ^ E ≤
          9 * E * 2 ^ E * (c * L.Z.card * f k) := by
        intro k _
        have hcard : ((Finset.univ.filter fun r : L.marks => L.markLayer r = k).card : ℝ) ≤
            9 * ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ) := by
          exact_mod_cast Layout.card_markLayer_le k
        rw [Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.1 hr).2],
          Finset.sum_const, nsmul_eq_mul]
        have hk0 : 0 ≤ E * 2 ^ E * ((k : ℝ) + 1) ^ E := by positivity
        calc ((Finset.univ.filter fun r : L.marks => L.markLayer r = k).card : ℝ) *
              (E * 2 ^ E * ((k : ℝ) + 1) ^ E)
            ≤ 9 * ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ) *
              (E * 2 ^ E * ((k : ℝ) + 1) ^ E) := mul_le_mul_of_nonneg_right hcard hk0
          _ ≤ 9 * (c * L.Z.card * (2 : ℝ) ^ (-(k * δ₀ / 2))) *
              (E * 2 ^ E * ((k : ℝ) + 1) ^ E) := by
              gcongr
              exact (hsp k).trans_eq (by rw [hC₀])
          _ = 9 * E * 2 ^ E * (c * L.Z.card * f k) := by rw [hf_def]; ring
      calc _ ≤ ∑ k ∈ Finset.Ico L.k₀ L.K, 9 * E * 2 ^ E * (c * L.Z.card * f k) :=
            Finset.sum_le_sum hfib
        _ = 9 * E * 2 ^ E * (c * L.Z.card * ∑ k ∈ Finset.Ico L.k₀ L.K, f k) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ 9 * E * 2 ^ E * (c * L.Z.card * B) := by gcongr
    rw [h1]
    calc ∑ r : L.marks, ((S.filter fun m => m.root = r).card : ℝ)
        ≤ ∑ r : L.marks, E * 2 ^ E * ((L.markLayer r : ℝ) + 1) ^ E :=
          Finset.sum_le_sum fun r _ => h2 r
      _ ≤ 9 * E * 2 ^ E * (c * L.Z.card * B) := h3
      _ ≤ c * B * (1 + 9 * E * 2 ^ E) * L.Z.card := by
          have : 0 ≤ c * B * L.Z.card := by positivity
          nlinarith

/-! ## D11.20 Bounded exceptional set -/

/-- The lattice site `z ∈ ℤ × ℤ` of `Fin 2 → ℤ` is the point `z` of the plane `Fin 2 → ℝ`. -/
lemma latticeSite_lattice_symm (z : ℤ × ℤ) :
    latticeSite (lattice.symm z) = pt (latticePoint z) := by
  funext i; fin_cases i <;> rfl

/-- D11.20 (`geometry:bad-sites`). `D` := sites of `A` that remain in the dummy identifier or lie
in terminal squares (sites overwritten by a replacement are not dummy sites). `|D| ≤ Cb`, with
`C` depending on `C₀`, `k₀` and `S_*` only.
2D only: the terminal squares are the planar removal squares of D11.14. -/
theorem step_11_20_count (C₀ k₀ : ℕ) {S_star : ℝ} (hS : 1 < S_star) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : Layout, L.C₀ = C₀ → L.k₀ = k₀ → L.stopScale = S_star → L.BeltSparse →
    ∀ b : ℕ, L.Z.card ≤ 2 * b → ∀ D : Finset (ℤ × ℤ),
      (∀ z ∈ D, pt (latticePoint z) ∈ closure (N o₂ L.Z L.C₀ L.k₀) ∨
        ∃ m, L.repair.IsMark m ∧ ¬ L.repair.IsNonterminal m ∧
          latticePoint z ∈ ball (L.repair.v m) (d (L.repair.S m))) →
      (D.card : ℝ) ≤ C * b := by
  classical
  obtain ⟨C', hC', hcount⟩ := step_11_19 C₀ hS
  set S : ℕ := ⌈S_star⌉₊
  set C'' : ℕ := ⌈2 * C'⌉₊
  refine ⟨((C'' * (2 * S + 1) ^ 2 + 2 * (2 * C₀ + 1) ^ 2 * (2 ^ k₀ + 1) ^ 2 : ℕ) : ℝ),
    Nat.cast_nonneg _, fun L hC₀ hk₀ hS' hsp b hZ D hD => ?_⟩
  have hfin := L.lemma_11_3.1.finite_isMark
  -- D11.20.1: the centres of the terminal squares, at most the number of marks
  set J : Finset (Fin 2 → ℝ) := hfin.toFinset.image fun m => pt (L.repair.v m)
  have hJ : J.card ≤ C'' * b := by
    have h2 : (J.card : ℝ) ≤ C'' * b := by
      calc (J.card : ℝ) ≤ hfin.toFinset.card := by exact_mod_cast Finset.card_image_le
        _ ≤ C' * L.Z.card := by
            rw [← Set.ncard_eq_toFinset_card _ hfin]; exact (hcount L hC₀ hS' hsp).2
        _ ≤ C' * (2 * b) := by gcongr; exact_mod_cast hZ
        _ = 2 * C' * b := by ring
        _ ≤ C'' * b := by gcongr; exact Nat.le_ceil _
    exact_mod_cast h2
  -- D11.20.2–3
  have h := step_11_20 o₂ L.Z L.C₀ L.k₀ S J hZ hJ (D.image lattice.symm)
  rw [Finset.filter_true_of_mem, Finset.card_image_of_injective _ lattice.symm.injective,
    hC₀, hk₀] at h
  · exact_mod_cast h
  · intro z' hz'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    rw [latticeSite_lattice_symm]
    rcases hD z hz with h | ⟨m, hm, hnt, hball⟩
    · exact Or.inl h
    · refine Or.inr ⟨_, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hm), ?_⟩
      rw [dist_pt]
      have : d (L.repair.S m) < S_star := hS' ▸ not_le.1 hnt
      linarith [mem_ball.1 hball, Nat.le_ceil S_star]

/-! ## D11.25.4 Summability -/

namespace Layout

variable (L : Layout)

/-- D11.25. The identifiers that can be retained: primaries of the layers `k₀ ≤ k < K`, initial
belt tiles of the belt cells of these layers, and replacements at marks. -/
def Retainable : TileId InitId L.marks → Prop
  | .init (.primary k j) => k ∈ Finset.Ico L.k₀ L.K ∧ j ∈ primaries o₂ L.Z L.C₀ k (L.a k)
  | .init (.belt k w _) => k ∈ Finset.Ico L.k₀ L.K ∧ w ∈ beltIndex o₂ L.Z L.C₀ k (L.a k)
  | .init .dummy => False
  | .init .exterior => False
  | .repl m c => L.repair.IsMark m ∧ ∃ i, L.repair.markOct m i = c

/-- The layer of a primary. -/
def primLayer : TileId InitId L.marks → ℕ
  | .init (.primary k _) => k
  | _ => 0

/-- The pitch index of a primary. -/
def primIdx : TileId InitId L.marks → Fin 2 → ℤ
  | .init (.primary _ j) => j
  | _ => 0

/-- The identifier is a primary. -/
def IsPrim : TileId InitId L.marks → Prop
  | .init (.primary _ _) => True
  | _ => False

end Layout

/-- D11.25.4 (summability). `≤ Cb` primaries per layer with `n ≥ c 2^{(1+2δ₀)k}`:
`Cb ∑_{k≥k₀} 2^{-100(1+2δ₀)k} ≤ C'b`. Other tiles: `O(b)` many (D11.19), each `n ≥ 1`, so their
sum is `O(b)`. Here `≤ C|Z|`, `C` depending on `C₀` and `S_*` only.
2D only: the retained identifiers are those of the planar construction. -/
theorem step_11_25_4_count (C₀ : ℕ) {S_star : ℝ} (hS : 1 < S_star) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : Layout, L.C₀ = C₀ → L.stopScale = S_star → L.BeltSparse →
    ∀ (F : Finset (TileId InitId L.marks)) (n : TileId InitId L.marks → ℕ),
      (∀ a ∈ F, L.Retainable a ∧ 1 ≤ n a) →
      (∀ k j, TileId.init (.primary k j) ∈ F →
        ((2 : ℝ) ^ k) ^ (1 + 2 * δ₀) ≤ n (.init (.primary k j))) →
      ∑ a ∈ F, ((n a : ℝ) ^ 100)⁻¹ ≤ C * L.Z.card := by
  classical
  obtain ⟨C', hC', hcount⟩ := step_11_19 C₀ hS
  set g : ℕ → ℝ := fun k => (2 : ℝ) ^ (-(100 * (1 + 2 * δ₀) * k)) with hg_def
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  have hgs : Summable g := step_11_25_4.1
  set Q := ∑' k, g k
  have hQ : 0 ≤ Q := tsum_nonneg hg0
  set c : ℝ := 4 * layerCount 2 C₀
  refine ⟨c * Q + 10 * C', by positivity, fun L hC₀ hS' hsp F n hF hFp => ?_⟩
  have hZ : (0 : ℝ) ≤ L.Z.card := Nat.cast_nonneg _
  obtain ⟨hbelts, hmarks⟩ := hcount L hC₀ hS' hsp
  rw [← Finset.sum_filter_add_sum_filter_not F L.IsPrim]
  -- primaries: `n^{-100} ≤ 2^{-100(1+2δ₀)k}`, at most `c|Z|` per layer
  have hprim : ∑ a ∈ F.filter L.IsPrim, ((n a : ℝ) ^ 100)⁻¹ ≤ c * L.Z.card * Q := by
    have hmaps : ∀ a ∈ F.filter L.IsPrim, L.primLayer a ∈ Finset.Ico L.k₀ L.K := by
      intro a ha
      obtain ⟨haF, hp⟩ := Finset.mem_filter.1 ha
      rcases a with ((_ | _ | ⟨k, j⟩ | _) | _) <;> simp only [Layout.IsPrim] at hp
      exact (hF _ haF).1.1
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfib : ∀ k ∈ Finset.Ico L.k₀ L.K,
        ∑ a ∈ (F.filter L.IsPrim).filter (fun a => L.primLayer a = k), ((n a : ℝ) ^ 100)⁻¹ ≤
          c * L.Z.card * g k := by
      intro k _
      -- each term
      have hterm : ∀ a ∈ (F.filter L.IsPrim).filter (fun a => L.primLayer a = k),
          ((n a : ℝ) ^ 100)⁻¹ ≤ g k := by
        intro a ha
        obtain ⟨ha, hk⟩ := Finset.mem_filter.1 ha
        obtain ⟨haF, hp⟩ := Finset.mem_filter.1 ha
        rcases a with ((_ | _ | ⟨k', j⟩ | _) | _) <;> simp only [Layout.IsPrim] at hp
        simp only [Layout.primLayer] at hk
        subst hk
        have hn := hFp _ _ haF
        have hpos : 0 < ((2 : ℝ) ^ k') ^ (1 + 2 * δ₀) := by positivity
        calc ((n (.init (.primary k' j)) : ℝ) ^ 100)⁻¹
            ≤ ((((2 : ℝ) ^ k') ^ (1 + 2 * δ₀)) ^ 100)⁻¹ :=
              inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hn 100)
          _ = g k' := by
              change _ = (2 : ℝ) ^ (-(100 * (1 + 2 * δ₀) * k'))
              rw [rpow_neg (by norm_num), ← rpow_natCast (2 : ℝ) k',
                ← rpow_mul (by norm_num), ← rpow_natCast _ 100, ← rpow_mul (by norm_num)]
              congr 2; push_cast; ring
      -- at most `4 layerCount |Z|` primaries in layer `k` (D11.10)
      obtain ⟨⟨hfin, hcard⟩, -⟩ := step_11_10 o₂ L.Z L.C₀ k (L.a k)
      have hfc : (((F.filter L.IsPrim).filter (fun a => L.primLayer a = k)).card : ℝ) ≤
          c * L.Z.card := by
        have h1 : ((F.filter L.IsPrim).filter (fun a => L.primLayer a = k)).card ≤
            hfin.toFinset.card := by
          refine Finset.card_le_card_of_injOn L.primIdx (fun a ha => ?_) (fun a ha a' ha' h => ?_)
          · obtain ⟨ha, hk⟩ := Finset.mem_filter.1 ha
            obtain ⟨haF, hp⟩ := Finset.mem_filter.1 ha
            rcases a with ((_ | _ | ⟨k', j⟩ | _) | _) <;> simp only [Layout.IsPrim] at hp
            simp only [Layout.primLayer] at hk
            subst hk
            exact hfin.mem_toFinset.2 (hF _ haF).1.2
          · obtain ⟨ha, hk⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
            obtain ⟨-, hp⟩ := Finset.mem_filter.1 ha
            obtain ⟨ha', hk'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha')
            obtain ⟨-, hp'⟩ := Finset.mem_filter.1 ha'
            rcases a with ((_ | _ | ⟨k₁, j₁⟩ | _) | _) <;> simp only [Layout.IsPrim] at hp
            rcases a' with ((_ | _ | ⟨k₂, j₂⟩ | _) | _) <;> simp only [Layout.IsPrim] at hp'
            simp only [Layout.primLayer] at hk hk'
            simp only [Layout.primIdx] at h
            rw [hk, hk', h]
        rw [← Set.ncard_eq_toFinset_card _ hfin] at h1
        calc _ ≤ ((primaries o₂ L.Z L.C₀ k (L.a k)).ncard : ℝ) := by exact_mod_cast h1
          _ ≤ ((2 ^ 2 * (layerCount 2 L.C₀ * L.Z.card) : ℕ) : ℝ) := by exact_mod_cast hcard
          _ = c * L.Z.card := by rw [hC₀]; push_cast; ring
      calc _ ≤ ∑ a ∈ (F.filter L.IsPrim).filter (fun a => L.primLayer a = k), g k :=
            Finset.sum_le_sum hterm
        _ = (((F.filter L.IsPrim).filter (fun a => L.primLayer a = k)).card : ℝ) * g k := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ c * L.Z.card * g k := mul_le_mul_of_nonneg_right hfc (hg0 k)
    calc _ ≤ ∑ k ∈ Finset.Ico L.k₀ L.K, c * L.Z.card * g k := Finset.sum_le_sum hfib
      _ = c * L.Z.card * ∑ k ∈ Finset.Ico L.k₀ L.K, g k := by rw [Finset.mul_sum]
      _ ≤ c * L.Z.card * Q := by
          gcongr; exact hgs.sum_le_tsum _ fun k _ => hg0 k
  -- the other tiles: `n ≥ 1`, at most two per belt cell and eight per mark (D11.19)
  have hrest : ∑ a ∈ F.filter (fun a => ¬ L.IsPrim a), ((n a : ℝ) ^ 100)⁻¹ ≤
      10 * C' * L.Z.card := by
    have hfin := L.lemma_11_3.1.finite_isMark
    set Bid : Finset (TileId InitId L.marks) := (Finset.Ico L.k₀ L.K).biUnion fun k =>
      ((beltIndex o₂ L.Z L.C₀ k (L.a k)) ×ˢ (Finset.univ : Finset (Fin 2))).image
        fun p => .init (.belt k p.1 p.2)
    set Rid : Finset (TileId InitId L.marks) := hfin.toFinset.biUnion fun m =>
      Finset.univ.image fun i => .repl m (L.repair.markOct m i)
    have hsub : F.filter (fun a => ¬ L.IsPrim a) ⊆ Bid ∪ Rid := by
      intro a ha
      obtain ⟨haF, hp⟩ := Finset.mem_filter.1 ha
      have hr := (hF a haF).1
      rcases a with ((_ | _ | ⟨k, j⟩ | ⟨k, w, c⟩) | ⟨m, c⟩)
      · exact hr.elim
      · exact hr.elim
      · exact (hp trivial).elim
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨k, hr.1,
          Finset.mem_image.2 ⟨(w, c), Finset.mem_product.2 ⟨hr.2, Finset.mem_univ _⟩, rfl⟩⟩)
      · obtain ⟨hm, i, hi⟩ := hr
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, hfin.mem_toFinset.2 hm,
          Finset.mem_image.2 ⟨i, Finset.mem_univ _, by rw [hi]⟩⟩)
    have hBid : (Bid.card : ℝ) ≤ 2 * C' * L.Z.card := by
      have : Bid.card ≤ ∑ k ∈ Finset.Ico L.k₀ L.K, 2 * (beltIndex o₂ L.Z L.C₀ k (L.a k)).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => Finset.card_image_le.trans
          (by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]))
      calc (Bid.card : ℝ) ≤ ∑ k ∈ Finset.Ico L.k₀ L.K,
            2 * ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ) := by exact_mod_cast this
        _ = 2 * ∑ k ∈ Finset.Ico L.k₀ L.K, ((beltIndex o₂ L.Z L.C₀ k (L.a k)).card : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ 2 * (C' * L.Z.card) := by gcongr
        _ = 2 * C' * L.Z.card := by ring
    have hRid : (Rid.card : ℝ) ≤ 8 * C' * L.Z.card := by
      have : Rid.card ≤ hfin.toFinset.card * 8 :=
        Finset.card_biUnion_le_card_mul _ _ _ fun m _ => Finset.card_image_le.trans (by simp)
      rw [← Set.ncard_eq_toFinset_card _ hfin] at this
      calc (Rid.card : ℝ) ≤ ({m : Mark L.marks | L.repair.IsMark m}.ncard : ℝ) * 8 := by
            exact_mod_cast this
        _ ≤ C' * L.Z.card * 8 := by gcongr
        _ = 8 * C' * L.Z.card := by ring
    calc _ ≤ ∑ a ∈ F.filter (fun a => ¬ L.IsPrim a), (1 : ℝ) := by
          refine Finset.sum_le_sum fun a ha => inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
          exact_mod_cast (hF a (Finset.mem_filter.1 ha).1).2
      _ = ((F.filter fun a => ¬ L.IsPrim a).card : ℝ) := by simp
      _ ≤ ((Bid ∪ Rid).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ (Bid.card : ℝ) + Rid.card := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ 10 * C' * L.Z.card := by linarith
  calc _ ≤ c * L.Z.card * Q + 10 * C' * L.Z.card := add_le_add hprim hrest
    _ = (c * Q + 10 * C') * L.Z.card := by ring

end

end AreaLaw.Geometry
