import QStab.QClifford.Compile.SurfaceNZAssembly
import QStab.QClifford.Compile.NZBackAction

/-!
# `SurfaceHValid`, discharged: the compiled Surface/NZ bar-Z distance, unconditional

`SurfaceNZAssembly.lean` reduces the compiled Surface/NZ bar-Z distance to the single
`Prop` `SurfaceHValid d hd hd3 hodd`: every fault site of `compileProgram
(surfaceXZProgram d hd)` has a weight-`≤ 1` data residual, or its residual is a hook in
the **union** back-action set.  Because the union machine's `backActionSet` ignores the
current stabilizer, the `∀ st'` in `SurfaceHValid` is vacuous in `st'`, and the
obligation reduces to a per-fault-site classification of the compiled circuit.

This file proves that obligation bottom-up and then closes the pipeline:

* **Seeds / bridges** — `surfaceXZProgram_allNZ`, `errLocsWithContextAux_eq_prefix_nil`,
  the `nzSuffixResidual`↔`mkSurfaceHookErrors` membership keystones, and the schedule
  facts (`nzSchedule_kind_uniform`, `nzSchedule_support_nodup`, `scheduleKind_nzSchedule`).
* **Program decomposition** — `compileProgramAux_site_split` localizes any fault site to
  one measurement-leaf gadget with a data-preserving tail; `surfaceXZProgram_measLeaf`
  pins that gadget to `(.NZ, nzSchedule d hd i)`.
* **Per-gadget classification** — `nz_gadget_site_classified` (`Z`-uniform) and
  `nz_gadget_site_classified_X` (`X`-uniform, via the H-sandwich `hChain_*` lemmas):
  every surviving residual is some `nzSuffixResidual (nzSchedule d hd i) j`.
* **`surface_hvalid`** — dispatches the two CSS kinds through the classifiers and lands
  each surviving residual in `mkSurfaceHookErrors i ⊆` the union set (witness `i`).
* **Headline corollaries** (`section Corollaries`) — `surface_compiled_FHoare`
  (compiled barrier invariant) and `surface_compiled_barZ_distance` (`d ≤ sigma.lambda`
  for any clean-start run landing in the bar-Z logical class), both with the
  `SurfaceHValid` hypothesis discharged.

All three headlines (`surface_hvalid`, `surface_compiled_FHoare`,
`surface_compiled_barZ_distance`) are axiom-clean: `[propext, Classical.choice,
Quot.sound]`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric

/-! ## Generic seeds (sub-item 1) -/

/-- The Surface/NZ source program is all-NZ (every measurement uses the NZ scheme). -/
theorem surfaceXZProgram_allNZ (d : Nat) (hd : 0 < d) :
    XZProgram.allNZ (surfaceXZProgram d hd) := by
  unfold surfaceXZProgram
  induction List.finRange (numStabFormula d) with
  | nil => exact True.intro
  | cons i rest ih => exact ⟨rfl, ih⟩

/-- The CSS `XZPauli` kind of a surface stabilizer agrees with its `Pauli` kind. -/
theorem kindXZ_toPauli_eq_kindPauli (k : StabKind) :
    (kindXZ k).toPauli = kindPauli k := by
  cases k <;> rfl

/-- Whole-circuit error locations are the prefix-with-empty-tail locations: the two
definitions differ only by an `eraseFaults [] = []` appended to each site's suffix. -/
theorem errLocsWithContextAux_eq_prefix_nil {nq : Nat} (cursor : Nat) (fc : FCircuit nq) :
    QStab.QClifford.PCC.errLocsWithContextAux cursor fc =
      prefixErrLocsWithContextAux cursor fc [] := by
  induction fc generalizing cursor with
  | nil => rfl
  | cons i rest ih =>
      cases i with
      | gate g =>
          simp only [QStab.QClifford.PCC.errLocsWithContextAux, prefixErrLocsWithContextAux]
          exact ih _
      | errLoc q =>
          simp only [QStab.QClifford.PCC.errLocsWithContextAux, prefixErrLocsWithContextAux,
            eraseFaults, List.append_nil]
          rw [ih]

/-- Every slot of a uniform schedule carries the uniform kind. -/
theorem uniform_kind {nq : Nat} (k : XZPauli) (sup : List (Fin nq)) :
    ∀ s ∈ (RuleSchedule.uniform k sup).slots, s.kind = k := by
  intro s hs
  simp only [RuleSchedule.uniform, List.mem_map] at hs
  obtain ⟨q, _, rfl⟩ := hs
  rfl

/-- The NZ surface schedule is kind-uniform (the `hz`/`hk` hypothesis shape). -/
theorem nzSchedule_kind_uniform (d : Nat) (hd : 0 < d)
    (i : Fin (numStabFormula d)) :
    ∀ s ∈ (nzSchedule d hd i).slots, s.kind = kindXZ (classifyStab d i.val) :=
  uniform_kind _ _

/-- Every surface stabilizer's NZ ordering is nonempty (2 or 4 couplings). -/
theorem kindOrderRC_ne_nil (d : Nat) (k : StabKind) : kindOrderRC d k ≠ [] := by
  cases k <;> simp [kindOrderRC]

/-- The head kind of the NZ surface schedule is the stabilizer's CSS Pauli kind —
`scheduleKind`-nonemptiness resolved through `kindOrderRC_ne_nil`. -/
theorem scheduleKind_nzSchedule (d : Nat) (hd : 0 < d)
    (i : Fin (numStabFormula d)) :
    scheduleKind (nzSchedule d hd i) = kindPauli (classifyStab d i.val) := by
  rw [← kindXZ_toPauli_eq_kindPauli]
  unfold scheduleKind nzSchedule RuleSchedule.uniform
  cases hko : kindOrderRC d (classifyStab d i.val) with
  | nil => exact absurd hko (kindOrderRC_ne_nil d _)
  | cons rc rest => simp

/-! ## Nodup of the NZ schedule support (sub-item 4)

The in-range elimination erases `gridFin`'s `% (d * d)`, after which distinctness
of the scheduled qubits is linear arithmetic from the (de-privatized)
`classifyStab_*_bounds`. -/

/-! Local copies of the `private` `classifyStab_*_bounds` lemmas
(`QStab/Examples/SurfaceParametric.lean:1580-1666`, proofs verbatim).
De-privatizing at source is the right long-term fix, but flipping `private`
invalidates `SurfaceParametric.olean` and cascades a full-tree rebuild —
unify these at the next scheduled full rebuild instead. -/

private lemma classifyStab_bulkZ_bounds (d i r c : Nat)
    (h : classifyStab d i = .bulkZ r c) :
    r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  subst hr_eq; subst hc_eq
  have hdmone_pos : 0 < d - 1 := by
    rcases Nat.eq_zero_or_pos (d - 1) with hzero | hpos
    · exfalso; rw [hzero, Nat.mul_zero] at hbulk; omega
    · exact hpos
  have hr_lt : i / (d - 1) < d - 1 :=
    Nat.div_lt_iff_lt_mul hdmone_pos |>.mpr (by rw [Nat.mul_comm]; exact hbulk)
  have hc_lt : i % (d - 1) < d - 1 := Nat.mod_lt _ hdmone_pos
  exact ⟨by omega, by omega, hpar⟩

private lemma classifyStab_bulkX_bounds (d i r c : Nat)
    (h : classifyStab d i = .bulkX r c) :
    r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  subst hr_eq; subst hc_eq
  have hdmone_pos : 0 < d - 1 := by
    rcases Nat.eq_zero_or_pos (d - 1) with hzero | hpos
    · exfalso; rw [hzero, Nat.mul_zero] at hbulk; omega
    · exact hpos
  have hr_lt : i / (d - 1) < d - 1 :=
    Nat.div_lt_iff_lt_mul hdmone_pos |>.mpr (by rw [Nat.mul_comm]; exact hbulk)
  have hc_lt : i % (d - 1) < d - 1 := Nat.mod_lt _ hdmone_pos
  refine ⟨by omega, by omega, ?_⟩
  omega

private lemma classifyStab_topX_bounds (d i b : Nat)
    (h : classifyStab d i = .topX b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop
  injection h with heq
  subst heq
  exact hTop

private lemma classifyStab_rightZ_bounds (d i b : Nat)
    (h : classifyStab d i = .rightZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight
  injection h with heq
  subst heq
  omega

private lemma classifyStab_leftZ_bounds (d i b : Nat)
    (h : classifyStab d i = .leftZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight hLeft
  injection h with heq
  subst heq
  omega

private lemma classifyStab_bottomX_bounds (d i b : Nat) (hodd : d % 2 = 1)
    (hi : i < (d - 1) * (d - 1) + 2 * (d - 1))
    (h : classifyStab d i = .bottomX b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight hLeft
  injection h with heq
  subst heq
  have hmod : (d - 1) % 2 = 0 := by omega
  have := Nat.div_add_mod (d - 1) 2
  omega

/-- For in-range coordinates the `gridFin` modulus is the identity. -/
theorem gridFin_val_of_lt (d : Nat) (hd : 0 < d) {r c : Nat} (hr : r < d) (hc : c < d) :
    (gridFin d hd (r, c)).val = d * r + c := by
  show (d * r + c) % (d * d) = d * r + c
  apply Nat.mod_eq_of_lt
  calc d * r + c < d * (r + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ d * d := Nat.mul_le_mul (Nat.le_refl d) hr

/-- Row-major codes of distinct in-range coordinates are distinct — packaged so
that no call site ever hands `omega` a product of variables. -/
private lemma rowMajor_ne (d : Nat) {r₁ c₁ r₂ c₂ : Nat} (h₁c : c₁ < d) (h₂c : c₂ < d)
    (h : r₁ ≠ r₂ ∨ (r₁ = r₂ ∧ c₁ ≠ c₂)) : d * r₁ + c₁ ≠ d * r₂ + c₂ := by
  intro heq
  rcases h with hne | ⟨rfl, hne⟩
  · rcases Nat.lt_or_ge r₁ r₂ with hlt | hge
    · have hle : d * (r₁ + 1) ≤ d * r₂ := Nat.mul_le_mul (Nat.le_refl d) hlt
      rw [Nat.mul_succ] at hle; omega
    · have hlt : r₂ < r₁ := by omega
      have hle : d * (r₂ + 1) ≤ d * r₁ := Nat.mul_le_mul (Nat.le_refl d) hlt
      rw [Nat.mul_succ] at hle; omega
  · omega

/-- In-range grid coordinates with distinct row-major codes give distinct qubits. -/
theorem gridFin_ne (d : Nat) (hd : 0 < d) {r₁ c₁ r₂ c₂ : Nat}
    (h₁r : r₁ < d) (h₁c : c₁ < d) (h₂r : r₂ < d) (h₂c : c₂ < d)
    (hne : d * r₁ + c₁ ≠ d * r₂ + c₂) :
    gridFin d hd (r₁, c₁) ≠ gridFin d hd (r₂, c₂) := by
  intro h
  apply hne
  have hv := congrArg Fin.val h
  rwa [gridFin_val_of_lt d hd h₁r h₁c, gridFin_val_of_lt d hd h₂r h₂c] at hv

/-- Combined form: distinct in-range coordinates give distinct scheduled qubits,
with every hypothesis `omega`-shaped. -/
private lemma gridFin_ne' (d : Nat) (hd : 0 < d) {r₁ c₁ r₂ c₂ : Nat}
    (h₁r : r₁ < d) (h₁c : c₁ < d) (h₂r : r₂ < d) (h₂c : c₂ < d)
    (h : r₁ ≠ r₂ ∨ (r₁ = r₂ ∧ c₁ ≠ c₂)) :
    gridFin d hd (r₁, c₁) ≠ gridFin d hd (r₂, c₂) :=
  gridFin_ne d hd h₁r h₁c h₂r h₂c (rowMajor_ne d h₁c h₂c h)

/-- **The NZ schedule visits distinct qubits** (core form over `kindOrderRC`). -/
theorem kindOrderRC_map_gridFin_nodup (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) :
    ((kindOrderRC d (classifyStab d i.val)).map (gridFin d hd)).Nodup := by
  have hhalf := Nat.div_add_mod (d - 1) 2
  have hi : i.val < (d - 1) * (d - 1) + 2 * (d - 1) := by
    have hlt := i.isLt
    simp only [numStabFormula] at hlt
    have h4 : 2 * 2 ≤ (d - 1) * (d - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  cases hcl : classifyStab d i.val with
  | bulkZ r c =>
      obtain ⟨hr, hc, -⟩ := classifyStab_bulkZ_bounds d i.val r c hcl
      simp only [kindOrderRC, List.map_cons, List.map_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
        not_or, not_false_eq_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
        (apply gridFin_ne' d hd <;> omega)
  | bulkX r c =>
      obtain ⟨hr, hc, -⟩ := classifyStab_bulkX_bounds d i.val r c hcl
      simp only [kindOrderRC, List.map_cons, List.map_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
        not_or, not_false_eq_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
        (apply gridFin_ne' d hd <;> omega)
  | topX b =>
      have hb := classifyStab_topX_bounds d i.val b hcl
      simp only [kindOrderRC, List.map_cons, List.map_nil, List.nodup_cons,
        List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true,
        not_false_eq_true]
      apply gridFin_ne' d hd <;> omega
  | rightZ b =>
      have hb := classifyStab_rightZ_bounds d i.val b hcl
      simp only [kindOrderRC, List.map_cons, List.map_nil, List.nodup_cons,
        List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true,
        not_false_eq_true]
      apply gridFin_ne' d hd <;> omega
  | leftZ b =>
      have hb := classifyStab_leftZ_bounds d i.val b hcl
      simp only [kindOrderRC, List.map_cons, List.map_nil, List.nodup_cons,
        List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true,
        not_false_eq_true]
      apply gridFin_ne' d hd <;> omega
  | bottomX b =>
      have hb := classifyStab_bottomX_bounds d i.val b hodd hi hcl
      simp only [kindOrderRC, List.map_cons, List.map_nil, List.nodup_cons,
        List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true,
        not_false_eq_true]
      apply gridFin_ne' d hd <;> omega

/-- **The NZ schedule support is duplicate-free** — the `hnd` hypothesis shape
consumed by the chain characterizations. -/
theorem nzSchedule_support_nodup (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) :
    (((nzSchedule d hd i).slots).map (·.qubit)).Nodup := by
  have h := kindOrderRC_map_gridFin_nodup d hd hd3 hodd i
  simpa [nzSchedule, RuleSchedule.uniform, List.map_map, Function.comp] using h

/-! ## The reverse-decode keystone (sub-item 5 core)

`supportByKind`'s per-kind disjuncts are exactly the `kindOrderRC` pairs, so the
"reverse decode" (`coord ∈ kindOrderRC → decode = kind`) collapses to one
membership↔predicate lemma composed with the existing public keystones
(`inStabSupport_iff_supportByKind`, `decode_I_or_stabType_pub`,
`kindPauli_eq_stabType`) — no per-kind derivation needed. -/

/-- Kind-order membership coincides with the per-kind support predicate. -/
lemma mem_kindOrderRC_iff_supportByKind (d : Nat) (k : StabKind) (rc : Nat × Nat) :
    rc ∈ kindOrderRC d k ↔ supportByKind d k rc.1 rc.2 = true := by
  obtain ⟨row, col⟩ := rc
  cases k <;> simp [kindOrderRC, supportByKind, Prod.ext_iff] <;> tauto

/-- On its `kindOrderRC` support the decoder yields exactly the stabilizer's
CSS kind — the collapsed "5-kind reverse decode". -/
lemma decode_eq_kindPauli_of_mem_kindOrderRC (d i row col : Nat)
    (h : (row, col) ∈ kindOrderRC d (classifyStab d i)) :
    decodeStabPauliAt d i row col = kindPauli (classifyStab d i) := by
  have hsup : supportByKind d (classifyStab d i) row col = true :=
    (mem_kindOrderRC_iff_supportByKind d _ (row, col)).mp h
  have hne : decodeStabPauliAt d i row col ≠ Pauli.I :=
    (inStabSupport_iff_supportByKind d i row col).mpr hsup
  rcases decode_I_or_stabType_pub d i row col with hI | hty
  · exact absurd hI hne
  · rw [hty]
    exact (kindPauli_eq_stabType d i).symm

/-! ## Membership bridges (sub-item 5, Step A) -/

/-- Every coordinate scheduled by a surface stabilizer is in range (`< d` each). -/
theorem kindOrderRC_classify_in_bounds (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) :
    ∀ rc ∈ kindOrderRC d (classifyStab d i.val), rc.1 < d ∧ rc.2 < d := by
  have hhalf := Nat.div_add_mod (d - 1) 2
  have hi : i.val < (d - 1) * (d - 1) + 2 * (d - 1) := by
    have hlt := i.isLt
    simp only [numStabFormula] at hlt
    have h4 : 2 * 2 ≤ (d - 1) * (d - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  intro rc hrc
  cases hcl : classifyStab d i.val with
  | bulkZ r c =>
      obtain ⟨hr, hc, -⟩ := classifyStab_bulkZ_bounds d i.val r c hcl
      rw [hcl] at hrc
      simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at hrc
      rcases hrc with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  | bulkX r c =>
      obtain ⟨hr, hc, -⟩ := classifyStab_bulkX_bounds d i.val r c hcl
      rw [hcl] at hrc
      simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at hrc
      rcases hrc with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  | topX b =>
      have hb := classifyStab_topX_bounds d i.val b hcl
      rw [hcl] at hrc
      simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at hrc
      rcases hrc with rfl | rfl <;> exact ⟨by omega, by omega⟩
  | rightZ b =>
      have hb := classifyStab_rightZ_bounds d i.val b hcl
      rw [hcl] at hrc
      simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at hrc
      rcases hrc with rfl | rfl <;> exact ⟨by omega, by omega⟩
  | leftZ b =>
      have hb := classifyStab_leftZ_bounds d i.val b hcl
      rw [hcl] at hrc
      simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at hrc
      rcases hrc with rfl | rfl <;> exact ⟨by omega, by omega⟩
  | bottomX b =>
      have hb := classifyStab_bottomX_bounds d i.val b hodd hi hcl
      rw [hcl] at hrc
      simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at hrc
      rcases hrc with rfl | rfl <;> exact ⟨by omega, by omega⟩

/-! ## Membership bridges (sub-item 5, Step A items 2-4)

`nzSuffixResidual` over the compiled schedule coincides with the source hook
enumeration: proper suffixes with `suffixHook`, the full (`j = 0`) suffix with
the stabilizer itself.  The coordinate transfer runs through
`gridFin_val_of_lt` + `kindOrderRC_classify_in_bounds`; the value transfer
through `scheduleKind_nzSchedule` and the reverse-decode keystone. -/

/-- Scheduled-qubit membership in a schedule suffix, transferred to the
coordinate list: the compiled `any` test holds iff `q` is the grid qubit of a
dropped `kindOrderRC` coordinate. -/
lemma nzSchedule_drop_any_iff (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) (j : Nat) (q : Fin (d * d)) :
    ((nzSchedule d hd i).slots.drop j).any (fun slot => decide (slot.qubit = q)) = true ↔
      ∃ rc, rc ∈ (kindOrderRC d (classifyStab d i.val)).drop j ∧
        q.val = gridIdx d rc.1 rc.2 := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨slot, hslot, hq⟩
    rw [decide_eq_true_eq] at hq
    simp only [nzSchedule, RuleSchedule.uniform, List.map_map, ← List.map_drop,
      List.mem_map, Function.comp] at hslot
    obtain ⟨rc, hrc, rfl⟩ := hslot
    obtain ⟨h1, h2⟩ := kindOrderRC_classify_in_bounds d hd3 hodd i rc
      (List.mem_of_mem_drop hrc)
    refine ⟨rc, hrc, ?_⟩
    rw [← hq]
    show (gridFin d hd rc).val = gridIdx d rc.1 rc.2
    exact gridFin_val_of_lt d hd h1 h2
  · rintro ⟨rc, hrc, hval⟩
    obtain ⟨h1, h2⟩ := kindOrderRC_classify_in_bounds d hd3 hodd i rc
      (List.mem_of_mem_drop hrc)
    refine ⟨⟨kindXZ (classifyStab d i.val), gridFin d hd rc⟩, ?_, ?_⟩
    · simp only [nzSchedule, RuleSchedule.uniform, List.map_map, ← List.map_drop,
        List.mem_map, Function.comp]
      exact ⟨rc, hrc, rfl⟩
    · rw [decide_eq_true_eq]
      exact Fin.ext ((gridFin_val_of_lt d hd h1 h2).trans hval.symm)

/-- **Bridge (proper suffixes).**  The compiled suffix residual is the source
`suffixHook`, for every `j`. -/
theorem nzSuffixResidual_eq_suffixHook (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) (j : Nat) :
    nzSuffixResidual (nzSchedule d hd i) j = suffixHook d (classifyStab d i.val) j := by
  funext q
  by_cases hmem :
      ((nzSchedule d hd i).slots.drop j).any (fun slot => decide (slot.qubit = q)) = true
  · have hex := (nzSchedule_drop_any_iff d hd hd3 hodd i j q).mp hmem
    have hLHS : nzSuffixResidual (nzSchedule d hd i) j q =
        kindPauli (classifyStab d i.val) := by
      simp only [nzSuffixResidual]
      rw [if_pos hmem]
      exact scheduleKind_nzSchedule d hd i
    have hne := suffixHook_at_kindOrderRC_drop_ne_I d (classifyStab d i.val) j q hex
    rcases suffixHook_eq_I_or_kindPauli d (classifyStab d i.val) j q with hI | hK
    · exact absurd hI hne
    · rw [hLHS, hK]
  · have hnm : ∀ rc ∈ (kindOrderRC d (classifyStab d i.val)).drop j,
        q.val ≠ gridIdx d rc.1 rc.2 := by
      intro rc hrc hq
      exact hmem ((nzSchedule_drop_any_iff d hd hd3 hodd i j q).mpr ⟨rc, hrc, hq⟩)
    have hRHS := suffixHook_eq_I_of_idx_not_key d (classifyStab d i.val) j q hnm
    simp only [nzSuffixResidual]
    rw [if_neg (by simpa using hmem), hRHS]

/-- **Bridge (full suffix).**  The `j = 0` residual is the stabilizer itself. -/
theorem nzSuffixResidual_zero_eq_mkSurfaceStabilizers (d : Nat) (hd : 0 < d)
    (hd3 : 3 ≤ d) (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) :
    nzSuffixResidual (nzSchedule d hd i) 0 = mkSurfaceStabilizers d hd i := by
  funext q
  have hq_recon : q.val = gridIdx d (q.val / d) (q.val % d) :=
    (Nat.div_add_mod q.val d).symm
  by_cases hmem :
      ((nzSchedule d hd i).slots.drop 0).any (fun slot => decide (slot.qubit = q)) = true
  · obtain ⟨rc, hrc, hval⟩ := (nzSchedule_drop_any_iff d hd hd3 hodd i 0 q).mp hmem
    obtain ⟨h1, h2⟩ := kindOrderRC_classify_in_bounds d hd3 hodd i rc
      (List.mem_of_mem_drop hrc)
    have hdiv : q.val / d = rc.1 := by
      rw [hval]
      show (d * rc.1 + rc.2) / d = rc.1
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt h2]
      omega
    have hmod : q.val % d = rc.2 := by
      rw [hval]
      show (d * rc.1 + rc.2) % d = rc.2
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt h2
    have hdecode : decodeStabPauliAt d i.val (q.val / d) (q.val % d) =
        kindPauli (classifyStab d i.val) := by
      apply decode_eq_kindPauli_of_mem_kindOrderRC
      rw [hdiv, hmod]
      simpa using List.mem_of_mem_drop hrc
    have hLHS : nzSuffixResidual (nzSchedule d hd i) 0 q =
        kindPauli (classifyStab d i.val) := by
      simp only [nzSuffixResidual]
      rw [if_pos hmem]
      exact scheduleKind_nzSchedule d hd i
    show nzSuffixResidual (nzSchedule d hd i) 0 q =
      decodeStabPauliAt d i.val (q.val / d) (q.val % d)
    rw [hLHS, hdecode]
  · have hLHS : nzSuffixResidual (nzSchedule d hd i) 0 q = Pauli.I := by
      simp only [nzSuffixResidual]
      rw [if_neg (by simpa using hmem)]
    show nzSuffixResidual (nzSchedule d hd i) 0 q =
      decodeStabPauliAt d i.val (q.val / d) (q.val % d)
    rw [hLHS]
    by_contra hne'
    have hcoord := decode_ne_I_implies_in_kindOrderRC d i.val (q.val / d) (q.val % d)
      (fun h => hne' h.symm)
    exact hmem ((nzSchedule_drop_any_iff d hd hd3 hodd i 0 q).mpr
      ⟨(q.val / d, q.val % d), by simpa using hcoord, hq_recon⟩)

/-- **The hook-set membership wrapper.**  Every in-range suffix residual of the
compiled schedule is a registered hook of stabilizer `i`. -/
theorem nzSuffixResidual_mem_hookErrors (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) (j : Nat)
    (hj : j < (nzSchedule d hd i).slots.length) :
    nzSuffixResidual (nzSchedule d hd i) j ∈ mkSurfaceHookErrors d hd hodd i := by
  have hlen : (nzSchedule d hd i).slots.length =
      (kindOrderRC d (classifyStab d i.val)).length := by
    simp [nzSchedule, RuleSchedule.uniform]
  simp only [mkSurfaceHookErrors]
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · apply Finset.mem_union_right
    rw [nzSuffixResidual_zero_eq_mkSurfaceStabilizers d hd hd3 hodd i]
    exact Finset.mem_singleton_self _
  · apply Finset.mem_union_left
    rw [nzSuffixResidual_eq_suffixHook d hd hd3 hodd i j]
    apply Finset.mem_image_of_mem
    rw [List.mem_toFinset]
    simp only [suffixIndices, List.mem_map, List.mem_range]
    exact ⟨j - 1, by omega, by omega⟩

/-! ## Program decomposition (sub-item 2, Step B) -/

/-- `MeasLeaf program scheme sigma` witnesses that `program` contains the measurement
leaf `.meas scheme sigma` (reachable through `.seq` nesting). -/
inductive MeasLeaf {n : Nat} : XZProgram n → Scheme → RuleSchedule n → Prop
  | here (scheme : Scheme) (sigma : RuleSchedule n) :
      MeasLeaf (.meas scheme sigma) scheme sigma
  | left {first second : XZProgram n} {scheme : Scheme} {sigma : RuleSchedule n} :
      MeasLeaf first scheme sigma → MeasLeaf (.seq first second) scheme sigma
  | right {first second : XZProgram n} {scheme : Scheme} {sigma : RuleSchedule n} :
      MeasLeaf second scheme sigma → MeasLeaf (.seq first second) scheme sigma

/-- Every measurement leaf of the surface foldr program is an `NZ` gadget with a
surface schedule (generalized over the folded index list). -/
theorem foldr_measLeaf (d : Nat) (hd : 0 < d) (l : List (Fin (numStabFormula d)))
    (scheme : Scheme) (sigma : RuleSchedule (d * d)) :
    MeasLeaf (l.foldr (fun i acc => .seq (.meas .NZ (nzSchedule d hd i)) acc) .skip)
        scheme sigma →
      ∃ i, scheme = Scheme.NZ ∧ sigma = nzSchedule d hd i := by
  induction l with
  | nil => intro h; cases h
  | cons i rest ih =>
      intro h
      cases h with
      | left hleft => cases hleft; exact ⟨i, rfl, rfl⟩
      | right hright => exact ih hright

/-- Every measurement leaf of the Surface/NZ program is `(.NZ, nzSchedule d hd i)`. -/
theorem surfaceXZProgram_measLeaf (d : Nat) (hd : 0 < d) (scheme : Scheme)
    (sigma : RuleSchedule (d * d)) :
    MeasLeaf (surfaceXZProgram d hd) scheme sigma →
      ∃ i, scheme = Scheme.NZ ∧ sigma = nzSchedule d hd i := by
  unfold surfaceXZProgram
  exact foldr_measLeaf d hd _ scheme sigma

/-- **Site split.**  Every fault site of an all-NZ compiled program lies in some
measurement-leaf gadget, whose deterministic tail preserves data (so the site's data
residual is determined by the gadget alone). -/
theorem compileProgramAux_site_split {n total : Nat} (program : XZProgram n) :
    ∀ (start : Nat) (hfit : start + programHelperCount program ≤ total) (cursor : Nat)
      (tail : FCircuit (n + total)) (site : QStab.QClifford.PCC.ErrLocWithContext (n + total)),
    XZProgram.allNZ program →
    (∀ (es : ErrorState (n + total)) (d : Fin (n + total)), d.val < n →
      (propagateCircuit (eraseFaults tail) es).paulis d = es.paulis d) →
    site ∈ prefixErrLocsWithContextAux cursor (compileProgramAux start program hfit) tail →
    ∃ (scheme : Scheme) (sigma : RuleSchedule n) (gstart gcursor : Nat)
      (gtail : FCircuit (n + total)) (ghfit : gstart + helperCount scheme sigma ≤ total),
      MeasLeaf program scheme sigma ∧
      (∀ (es : ErrorState (n + total)) (d : Fin (n + total)), d.val < n →
        (propagateCircuit (eraseFaults gtail) es).paulis d = es.paulis d) ∧
      site ∈ prefixErrLocsWithContextAux gcursor
        (compileGadgetBlock scheme sigma gstart ghfit) gtail := by
  induction program with
  | skip =>
      intro start hfit cursor tail site _ _ hsite
      simp only [compileProgramAux, prefixErrLocsWithContextAux, List.not_mem_nil] at hsite
  | meas scheme sigma =>
      intro start hfit cursor tail site _ htail hsite
      exact ⟨scheme, sigma, start, cursor, tail, hfit, MeasLeaf.here _ _, htail, hsite⟩
  | seq first second ihf ihs =>
      intro start hfit cursor tail site hallNZ htail hsite
      obtain ⟨hnz1, hnz2⟩ := hallNZ
      have H1 : start + programHelperCount first ≤ total := by
        simp only [programHelperCount] at hfit; omega
      have H2 : (start + programHelperCount first) + programHelperCount second ≤ total := by
        simp only [programHelperCount] at hfit; omega
      simp only [compileProgramAux, prefixErrLocs_append, List.mem_append] at hsite
      rcases hsite with hleft | hright
      · have htail' : ∀ (es : ErrorState (n + total)) (d : Fin (n + total)), d.val < n →
            (propagateCircuit (eraseFaults
              (compileProgramAux (start + programHelperCount first) second H2 ++ tail))
                es).paulis d = es.paulis d := by
          intro es d hd_lt
          rw [eraseFaults_append, QHL.Target.propagateCircuit_append, htail _ d hd_lt]
          exact compileProgramAux_preserves_data _ second H2 hnz2 es d hd_lt
        obtain ⟨sc, sg, gs, gc, gt, gh, hml, hgt, hgm⟩ :=
          ihf start H1 cursor _ site hnz1 htail' hleft
        exact ⟨sc, sg, gs, gc, gt, gh, MeasLeaf.left hml, hgt, hgm⟩
      · obtain ⟨sc, sg, gs, gc, gt, gh, hml, hgt, hgm⟩ :=
          ihs (start + programHelperCount first) H2 _ tail site hnz2 htail hright
        exact ⟨sc, sg, gs, gc, gt, gh, MeasLeaf.right hml, hgt, hgm⟩

/-! ## Degenerate sites (sub-item 6, Step C) -/

/-- A `measZ`-site fault (on the ancilla) with a data-preserving tail: the residual on
data is identity (`measZ` fixes paulis, the tail preserves data, the injected `a` is an
ancilla `≠` every data qubit). -/
theorem residual_measZ_siteTail {P : QECParams} {total : Nat} (a : Fin (P.n + total)) (p : Pauli)
    (hancHelper : P.n ≤ a.val) (rest : Circuit (P.n + total)) (dstart : Nat) (q' : Fin P.n)
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit rest es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q'')) :
    (propagateCircuit (Gate.measZ a :: rest)
        ((PCC.cleanAtDetector dstart).inject a p)).paulis (freshDataQ P.n total q') = Pauli.I := by
  have hne : freshDataQ P.n total q' ≠ a :=
    Fin.ne_of_val_ne (by have := q'.isLt; simp only [freshDataQ_val]; omega)
  rw [propagateCircuit, htail]
  simp only [propagateGate_measZ_paulis]
  rw [injectClean_paulis, if_neg hne]

/-! ## Z-side gadget classification (Step D) -/

/-- **Z-side site classification.**  For a `Z`-uniform NZ gadget with a data-preserving
tail, every fault site's data residual has weight `≤ 1`, or equals `nzSuffixResidual
sigma j` for some in-range `j` (a registered suffix hook). -/
theorem nz_gadget_site_classified {P : QECParams} {total : Nat} (sigma : RuleSchedule P.n)
    (gstart : Nat) (ghfit : gstart + helperCount .NZ sigma ≤ total)
    (hz : ∀ s ∈ sigma.slots, s.kind = XZPauli.Z)
    (hnd : (sigma.slots.map (·.qubit)).Nodup)
    (cursor : Nat) (tail : FCircuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit (eraseFaults tail) es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q''))
    (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I)
    (hsite : site ∈ prefixErrLocsWithContextAux cursor
      (compileGadgetBlock .NZ sigma gstart ghfit) tail) :
    ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 ∨
      ∃ j, j < sigma.slots.length ∧
        targetFaultDataResidual P ⟨site, p, hp⟩ = nzSuffixResidual sigma j := by
  by_cases hw : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1
  · exact Or.inl hw
  · refine Or.inr ?_
    have hw0 : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 0 := by omega
    have hw1 : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 1 := by omega
    set a : Fin (P.n + total) := blockHelperQ P.n total gstart 1 ghfit ⟨0, by decide⟩ with ha
    have hancHelper : P.n ≤ a.val := by rw [ha]; simp [blockHelperQ]
    have hgb : compileGadgetBlock .NZ sigma gstart ghfit =
        prep0 a ++ ((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++ flagMeasZ a := rfl
    rw [hgb, show prep0 a ++ ((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++
          flagMeasZ a = prep0 a ++ (((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++
            flagMeasZ a) from by rw [List.append_assoc],
        prefixErrLocs_append, prefixErrLocs_append] at hsite
    simp only [List.mem_append] at hsite
    have htail_chain : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
        (propagateCircuit (eraseFaults (flagMeasZ a ++ tail)) es).paulis
            (freshDataQ P.n total q'') = es.paulis (freshDataQ P.n total q'') := by
      intro es q''
      rw [eraseFaults_append, QHL.Target.propagateCircuit_append, htail]
      have hef : eraseFaults (flagMeasZ a) = [Gate.measZ a] := by simp [flagMeasZ, eraseFaults]
      rw [hef]; simp only [propagateCircuit, propagateGate_measZ_paulis]
    rcases hsite with hprep | hchain | hmeas
    · rw [prefixErrLocs_prep0] at hprep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hprep
      subst hprep
      exact absurd (weight_zero_of_allI _
        (fun q' => residual_prep0_site a p _ _ q')) hw0
    · rw [zChain_eq a (liftSchedule sigma).slots
          (fun s hs => by
            simp only [liftSchedule, List.mem_map] at hs
            obtain ⟨s', hs', rfl⟩ := hs
            simp [liftSlot, hz s' hs'])] at hchain
      have hqlt : ∀ q ∈ (liftSchedule (k := total) sigma).slots.map (·.qubit), q.val < P.n := by
        intro q hq
        simp only [liftSchedule, List.map_map, List.mem_map] at hq
        obtain ⟨s, _, rfl⟩ := hq
        simp [liftSlot]
      have hqnd : ((liftSchedule (k := total) sigma).slots.map (·.qubit)).Nodup := by
        have heq : (liftSchedule (k := total) sigma).slots.map (·.qubit) =
            (sigma.slots.map (·.qubit)).map (freshDataQ P.n total) := by
          simp [liftSchedule, List.map_map, liftSlot, Function.comp]
        rw [heq]; exact hnd.map (fun _ _ => freshDataQ_inj)
      obtain ⟨k, hk⟩ := chain_residual_hook a hancHelper (flagMeasZ a ++ tail) htail_chain
        ((liftSchedule (k := total) sigma).slots.map (·.qubit)) hqlt hqnd _ site p hp hchain hw0 hw1
      have hsk : scheduleKind sigma = Pauli.Z := by
        have hne : sigma.slots ≠ [] := by
          rintro he; simp [he, liftSchedule, prefixErrLocsWithContextAux] at hchain
        obtain ⟨s0, rest0, hs0⟩ := List.exists_cons_of_ne_nil hne
        have hs0mem : s0 ∈ sigma.slots := by rw [hs0]; exact List.mem_cons_self
        simp only [scheduleKind, hs0, List.head?_cons, hz s0 hs0mem]; rfl
      have hres_nz : targetFaultDataResidual P ⟨site, p, hp⟩ = nzSuffixResidual sigma k :=
        hk.trans (nzSuffix_of_liftedChain sigma hsk k)
      have hkbound : k < sigma.slots.length := by
        by_contra hge
        push_neg at hge
        apply hw0
        apply weight_zero_of_allI
        intro q'
        rw [hres_nz]
        simp only [nzSuffixResidual, List.drop_eq_nil_of_le hge, List.any_nil]
        exact if_neg (by simp)
      exact ⟨k, hkbound, hres_nz⟩
    · rw [prefixErrLocs_flagMeasZ] at hmeas
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmeas
      subst hmeas
      exact absurd (weight_zero_of_allI _
        (fun q' => residual_measZ_siteTail a p hancHelper _ _ q' htail)) hw0

/-! ## X-side gadget classification (Step E) -/

/-- **E1.**  X-uniform schedule: the compiled parity chain is the H-sandwiched qubit
CNOT chain (X analog of `zChain_eq`; the existing Z-side lemma is untouched). -/
theorem hChain_eq {nq : Nat} (a : Fin nq) (slots : List (ScheduledPauli nq))
    (hx : ∀ s ∈ slots, s.kind = XZPauli.X) :
    (slots.map (zParitySlot a)).flatten =
      ((slots.map (·.qubit)).map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  have hks : s.kind = XZPauli.X := hx s hs
  simp only [Function.comp_apply, zParitySlot, hks]

/-- **E3.**  Kind-generic suffix-hook bridge: for any schedule kind `kp`, the lifted
`kp`-suffix hook equals `nzSuffixResidual` (the membership half is kind-blind; a NEW
generalization of the untouched Z-only `nzSuffix_of_liftedChain`). -/
theorem nzSuffix_of_liftedChain' {P : QECParams} {total : Nat} (sigma : RuleSchedule P.n)
    (kp : Pauli) (hsk : scheduleKind sigma = kp) (k : Nat) :
    (fun q' : Fin P.n =>
        if freshDataQ P.n total q' ∈ (((sigma.slots.map liftSlot).map (·.qubit)).drop k)
        then kp else Pauli.I) = nzSuffixResidual sigma k := by
  funext q'
  simp only [nzSuffixResidual, hsk]
  have hmem :
      (freshDataQ P.n total q' ∈ (((sigma.slots.map liftSlot).map (·.qubit)).drop k)) ↔
        ((sigma.slots.drop k).any (fun slot => decide (slot.qubit = q')) = true) := by
    rw [List.map_map, ← List.map_drop]
    simp only [List.mem_map, List.any_eq_true, Function.comp_apply, decide_eq_true_eq, liftSlot]
    constructor
    · rintro ⟨s, hs, hsq⟩
      exact ⟨s, hs, freshDataQ_inj hsq⟩
    · rintro ⟨s, hs, hsq⟩
      exact ⟨s, hs, by rw [hsq]⟩
  by_cases hc : freshDataQ P.n total q' ∈ (((sigma.slots.map liftSlot).map (·.qubit)).drop k)
  · rw [if_pos hc, if_pos (hmem.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hmem.mpr h))]

/-- **E2 foundation.**  The H-sandwich (X-parity) chain preserves every non-ancilla
qubit when the ancilla starts `Z`-free — X analog of `propagate_zChain_preserves_data`,
by induction with `propagate_hSandwich_preserves_control` / `_keeps_ancZfree`. -/
theorem propagate_hChain_preserves_data {nq : Nat} (anc : Fin nq) :
    ∀ qs : List (Fin nq), anc ∉ qs →
      ∀ es : ErrorState nq, zPart (es.paulis anc) = Pauli.I →
        ∀ d : Fin nq, d ≠ anc →
          (propagateCircuit (eraseFaults
              ((qs.map (fun q => hadamard q ++ cnot q anc ++ hadamard q)).flatten)) es).paulis d =
            es.paulis d := by
  intro qs
  induction qs with
  | nil => intro _ es _ d _; simp [propagateCircuit]
  | cons q qs' ih =>
      intro hnotin es hancZ d hd
      have hqa : q ≠ anc := by rintro rfl; exact hnotin (List.mem_cons.mpr (Or.inl rfl))
      have hnotin' : anc ∉ qs' := fun hh => hnotin (List.mem_cons.mpr (Or.inr hh))
      have hcirc :
          eraseFaults (((q :: qs').map (fun q => hadamard q ++ cnot q anc ++ hadamard q)).flatten) =
            eraseFaults (hadamard q ++ cnot q anc ++ hadamard q) ++
              eraseFaults ((qs'.map (fun q => hadamard q ++ cnot q anc ++ hadamard q)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      set es1 := propagateCircuit (eraseFaults (hadamard q ++ cnot q anc ++ hadamard q)) es with he1
      have he1ancZ : zPart (es1.paulis anc) = Pauli.I := by
        rw [he1]; exact propagate_hSandwich_keeps_ancZfree q anc hqa es hancZ
      have he1d : es1.paulis d = es.paulis d := by
        by_cases hdq : d = q
        · rw [hdq, he1]; exact propagate_hSandwich_preserves_control q anc hqa es hancZ
        · rw [he1]
          have hcirc2 : eraseFaults (hadamard q ++ cnot q anc ++ hadamard q) =
              [Gate.hadamard q, Gate.cnot q anc hqa, Gate.hadamard q] := by
            simp [hadamard, cnot, hqa, eraseFaults]
          rw [hcirc2]
          simp only [propagateCircuit]
          rw [propagateGate_hadamard_paulis_ne q _ d hdq,
              propagateGate_cnot_paulis_ne q anc hqa _ d hdq hd,
              propagateGate_hadamard_paulis_ne q _ d hdq]
      rw [ih hnotin' es1 he1ancZ d hd, he1d]

/-- **E2 data-site helper.**  After the partial-slot propagation `es_mid` (ancilla
`Z`-free, all data `≠ q` clean), the rest of the H-chain + tail leaves the residual
supported on `q` alone. -/
theorem residual_data_HsiteHelper {P : QECParams} {total : Nat} (a : Fin (P.n + total))
    (qs' : List (Fin (P.n + total))) (hanc' : a ∉ qs') (hancHelper : P.n ≤ a.val)
    (q : Fin (P.n + total)) (tail : Circuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit tail es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q''))
    (es_mid : ErrorState (P.n + total)) (hmid_a : zPart (es_mid.paulis a) = Pauli.I)
    (hmid_d : ∀ d : Fin (P.n + total), d ≠ q → d ≠ a → es_mid.paulis d = Pauli.I)
    (q' : Fin P.n) :
    (propagateCircuit (eraseFaults
        ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten) ++ tail)
        es_mid).paulis (freshDataQ P.n total q') =
      if freshDataQ P.n total q' = q then es_mid.paulis q else Pauli.I := by
  have hane : freshDataQ P.n total q' ≠ a :=
    Fin.ne_of_val_ne (by have := q'.isLt; simp only [freshDataQ_val]; omega)
  rw [QHL.Target.propagateCircuit_append, htail,
    propagate_hChain_preserves_data a qs' hanc' es_mid hmid_a (freshDataQ P.n total q') hane]
  by_cases hfq : freshDataQ P.n total q' = q
  · rw [if_pos hfq, hfq]
  · rw [if_neg hfq]; exact hmid_d (freshDataQ P.n total q') hfq hane

/-- Weight ≤ 1 for a residual supported on a single data qubit `q` (`q.val < P.n`). -/
private theorem weight_le_one_dataSingle {P : QECParams} {total : Nat} (q : Fin (P.n + total))
    (hqlt : q.val < P.n) (f : Fin P.n → Pauli)
    (hf : ∀ q' : Fin P.n, freshDataQ P.n total q' ≠ q → f q' = Pauli.I) :
    ErrorVec.weight f ≤ 1 := by
  apply weight_le_one_of_single _ ⟨q.val, hqlt⟩
  intro q'' hne
  apply hf
  intro h
  apply hne
  apply Fin.ext
  simpa [freshDataQ_val] using congrArg Fin.val h

private lemma pauliMul_I_left' (x : Pauli) : pauliMul Pauli.I x = x := by cases x <;> rfl
private lemma pauliMul_I_right' (x : Pauli) : pauliMul x Pauli.I = x := by cases x <;> rfl

/-- Sites of one compiled X slot (`H q ; cnot q a ; H q`): three data sites and one
ancilla site, with the exact recorded suffixes. -/
theorem prefixErrLocs_hSandwich {nq : Nat} (a q : Fin nq) (hqa : q ≠ a) (cursor : Nat)
    (tail : FCircuit nq) :
    prefixErrLocsWithContextAux cursor (hadamard q ++ cnot q a ++ hadamard q) tail =
      [⟨q, Gate.hadamard q :: Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults tail, cursor⟩,
       ⟨q, Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults tail, cursor⟩,
       ⟨a, Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults tail, cursor⟩,
       ⟨q, Gate.hadamard q :: eraseFaults tail, cursor⟩] := by
  rw [show hadamard q ++ cnot q a ++ hadamard q =
      [FInstr.errLoc q, FInstr.gate (Gate.hadamard q), FInstr.errLoc q, FInstr.errLoc a,
       FInstr.gate (Gate.cnot q a hqa), FInstr.errLoc q, FInstr.gate (Gate.hadamard q)] from by
    simp [hadamard, cnot, hqa]]
  simp [prefixErrLocsWithContextAux, eraseFaults, QStab.QClifford.PCC.gateDetectorAdvance]

/-- `eraseFaults` of an H-sandwich chain, peeling the head slot. -/
theorem eraseFaults_hChain_cons {nq : Nat} (a q : Fin nq) (hqa : q ≠ a)
    (qs' : List (Fin nq)) :
    eraseFaults (((q :: qs').map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten) =
      Gate.hadamard q :: Gate.cnot q a hqa :: Gate.hadamard q ::
        eraseFaults ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten) := by
  simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
  rw [eraseFaults_cnot q a hqa]
  simp [hadamard, eraseFaults]

/-- **E2: X-gadget chain characterization** (H-sandwich dual of `chain_residual_hook`):
every fault site of the compiled X-parity chain (with a data-preserving tail) whose
data residual survives the weight filter (`≠ 0, ≠ 1`) produces the `X` suffix hook on
some `qs.drop k`.  Data-qubit faults give weight ≤ 1 (the ancilla contamination is
`X`-only, so nothing re-deposits); ancilla faults with a `Z` component deposit
`hadamardAction Z = X` on the whole current suffix (this slot's qubit included). -/
theorem hChain_residual_hook {P : QECParams} {total : Nat} (a : Fin (P.n + total))
    (hancHelper : P.n ≤ a.val) (tail : FCircuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit (eraseFaults tail) es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q'')) :
    ∀ (qs : List (Fin (P.n + total))), (∀ q ∈ qs, q.val < P.n) → qs.Nodup →
      ∀ (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli)
        (hp : p ≠ Pauli.I),
        site ∈ prefixErrLocsWithContextAux cursor
          ((qs.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten) tail →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 0 →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 1 →
        ∃ k, targetFaultDataResidual P ⟨site, p, hp⟩ =
          fun q' => if freshDataQ P.n total q' ∈ qs.drop k then Pauli.X else Pauli.I := by
  intro qs
  induction qs with
  | nil =>
      intro _ _ cursor site p hp hsite _ _
      simp [prefixErrLocsWithContextAux] at hsite
  | cons q qs' ih =>
      intro hlt hnd cursor site p hp hsite hw0 hw1
      have hqlt : q.val < P.n := hlt q (List.mem_cons.mpr (Or.inl rfl))
      have hqa : q ≠ a := fun h => by
        have := hlt q (List.mem_cons.mpr (Or.inl rfl)); rw [h] at this; omega
      have hlt' : ∀ q'' ∈ qs', q''.val < P.n := fun q'' h => hlt q'' (List.mem_cons.mpr (Or.inr h))
      have hnd' : qs'.Nodup := (List.nodup_cons.mp hnd).2
      have hqmem : q ∉ qs' := (List.nodup_cons.mp hnd).1
      have hanc : a ∉ (q :: qs') := fun h => by have := hlt a h; omega
      have hanc' : a ∉ qs' := fun h => hanc (List.mem_cons.mpr (Or.inr h))
      rw [show ((q :: qs').map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten =
            (hadamard q ++ cnot q a ++ hadamard q) ++
              (qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten from by
            simp [List.map_cons, List.flatten_cons],
          prefixErrLocs_append] at hsite
      simp only [List.mem_append] at hsite
      rcases hsite with hhead | hrec
      · rw [prefixErrLocs_hSandwich a q hqa] at hhead
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
        have hEsplit : eraseFaults
            ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail) =
            eraseFaults ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten) ++
              eraseFaults tail := eraseFaults_append _ _
        rcases hhead with rfl | rfl | rfl | rfl
        · -- site₁ (before H₁): the suffix IS the full (q :: qs') chain
          exfalso
          have hres : targetFaultDataResidual P
              ⟨⟨q, Gate.hadamard q :: Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              (fun q' => if freshDataQ P.n total q' = q then p else Pauli.I) := by
            funext q'
            show (propagateCircuit (Gate.hadamard q :: Gate.cnot q a hqa :: Gate.hadamard q ::
                eraseFaults ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten
                  ++ tail))
                ((PCC.cleanAtDetector cursor).inject q p)).paulis (freshDataQ P.n total q') = _
            rw [hEsplit, show Gate.hadamard q :: Gate.cnot q a hqa :: Gate.hadamard q ::
                (eraseFaults ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten)
                  ++ eraseFaults tail) =
                eraseFaults (((q :: qs').map
                  (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten) ++ eraseFaults tail
              from by rw [eraseFaults_hChain_cons a q hqa]; rfl]
            rw [residual_data_HsiteHelper a (q :: qs') hanc hancHelper q (eraseFaults tail) htail
                _ (by rw [injectClean_paulis, if_neg (Ne.symm hqa)]; rfl)
                (fun d hdq hda => by rw [injectClean_paulis, if_neg hdq]) q']
            rw [injectClean_paulis, if_pos rfl]
          rw [hres] at hw0 hw1
          have hle := weight_le_one_dataSingle q hqlt
            (fun q' => if freshDataQ P.n total q' = q then p else Pauli.I)
            (fun q' hne => if_neg hne)
          omega
        · -- site₂ (before the cnot, on q)
          exfalso
          set es₂ : ErrorState (P.n + total) :=
            propagateGate (Gate.hadamard q)
              (propagateGate (Gate.cnot q a hqa)
                ((PCC.cleanAtDetector cursor).inject q p)) with hes₂
          have hinja : ((PCC.cleanAtDetector cursor).inject q p).paulis a = Pauli.I := by
            rw [injectClean_paulis, if_neg (Ne.symm hqa)]
          have hes₂a : zPart (es₂.paulis a) = Pauli.I := by
            rw [hes₂, propagateGate_hadamard_paulis_ne q _ a (Ne.symm hqa),
              propagateGate_cnot_target q a hqa, hinja]
            exact zPart_pauliMul_xPart rfl
          have hes₂d : ∀ d : Fin (P.n + total), d ≠ q → d ≠ a → es₂.paulis d = Pauli.I := by
            intro d hdq hda
            rw [hes₂, propagateGate_hadamard_paulis_ne q _ d hdq,
              propagateGate_cnot_paulis_ne q a hqa _ d hdq hda, injectClean_paulis, if_neg hdq]
          have hres : targetFaultDataResidual P
              ⟨⟨q, Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              (fun q' => if freshDataQ P.n total q' = q then es₂.paulis q else Pauli.I) := by
            funext q'
            show (propagateCircuit (Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail))
                ((PCC.cleanAtDetector cursor).inject q p)).paulis (freshDataQ P.n total q') = _
            rw [hEsplit]
            exact residual_data_HsiteHelper a qs' hanc' hancHelper q (eraseFaults tail) htail
              es₂ hes₂a (fun d hdq hda => hes₂d d hdq hda) q'
          rw [hres] at hw0 hw1
          have hle := weight_le_one_dataSingle q hqlt
            (fun q' => if freshDataQ P.n total q' = q then es₂.paulis q else Pauli.I)
            (fun q' hne => if_neg hne)
          omega
        · -- site₃ (the ancilla site): X on this slot's suffix when zPart p ≠ I
          set es₃ : ErrorState (P.n + total) :=
            propagateGate (Gate.hadamard q)
              (propagateGate (Gate.cnot q a hqa)
                ((PCC.cleanAtDetector cursor).inject a p)) with hes₃
          have hinja : ((PCC.cleanAtDetector cursor).inject a p).paulis a = p := by
            rw [injectClean_paulis, if_pos rfl]
          have hinjq : ((PCC.cleanAtDetector cursor).inject a p).paulis q = Pauli.I := by
            rw [injectClean_paulis, if_neg hqa]
          have hes₃a : es₃.paulis a = p := by
            rw [hes₃, propagateGate_hadamard_paulis_ne q _ a (Ne.symm hqa),
              propagateGate_cnot_target q a hqa, hinjq, hinja]
            simp [xPart]
          have hes₃q : es₃.paulis q = hadamardAction (zPart p) := by
            rw [hes₃, propagateGate_hadamard_self,
              propagateGate_cnot_control q a hqa, hinjq, hinja, pauliMul_I_right']
          have hes₃d : ∀ d : Fin (P.n + total), d ≠ a → d ≠ q → es₃.paulis d = Pauli.I := by
            intro d hda hdq
            rw [hes₃, propagateGate_hadamard_paulis_ne q _ d hdq,
              propagateGate_cnot_paulis_ne q a hqa _ d hdq hda, injectClean_paulis, if_neg hda]
          have hres : targetFaultDataResidual P
              ⟨⟨a, Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              (fun q' => if freshDataQ P.n total q' ∈ (q :: qs') then hadamardAction (zPart p)
                else Pauli.I) := by
            funext q'
            have hfa : freshDataQ P.n total q' ≠ a :=
              Fin.ne_of_val_ne (by have := q'.isLt; simp only [freshDataQ_val]; omega)
            show (propagateCircuit (Gate.cnot q a hqa :: Gate.hadamard q :: eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail))
                ((PCC.cleanAtDetector cursor).inject a p)).paulis (freshDataQ P.n total q') = _
            rw [hEsplit]
            show (propagateCircuit (eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten)
                  ++ eraseFaults tail) es₃).paulis (freshDataQ P.n total q') = _
            rw [QHL.Target.propagateCircuit_append, htail,
              propagate_nzHSandwichChain_anc a p qs' hanc' hnd' es₃ hes₃a
                (fun q'' hq'' => hes₃d q'' (fun h => hanc' (h ▸ hq''))
                  (fun h => hqmem (h ▸ hq'')))
                (freshDataQ P.n total q'), if_neg hfa]
            by_cases hfq : freshDataQ P.n total q' = q
            · rw [if_neg (by rw [hfq]; exact hqmem),
                if_pos (by rw [hfq]; exact List.mem_cons.mpr (Or.inl rfl)), hfq, hes₃q]
            · by_cases hfm : freshDataQ P.n total q' ∈ qs'
              · rw [if_pos hfm, if_pos (List.mem_cons.mpr (Or.inr hfm))]
              · rw [if_neg hfm, if_neg (by
                    intro h
                    rcases List.mem_cons.mp h with h1 | h2
                    · exact hfq h1
                    · exact hfm h2),
                  hes₃d _ hfa hfq]
          by_cases hzp : zPart p = Pauli.I
          · exfalso
            apply hw0
            rw [hres]
            apply weight_zero_of_allI
            intro q'
            rw [hzp]
            simp [hadamardAction]
          · have hzZ : zPart p = Pauli.Z := by cases p <;> simp_all [zPart]
            refine ⟨0, ?_⟩
            rw [hres, hzZ]
            funext q'
            simp [hadamardAction, List.drop_zero]
        · -- site₄ (before H₂, on q)
          exfalso
          set es₄ : ErrorState (P.n + total) :=
            propagateGate (Gate.hadamard q) ((PCC.cleanAtDetector cursor).inject q p) with hes₄
          have hes₄a : zPart (es₄.paulis a) = Pauli.I := by
            rw [hes₄, propagateGate_hadamard_paulis_ne q _ a (Ne.symm hqa),
              injectClean_paulis, if_neg (Ne.symm hqa)]
            rfl
          have hes₄d : ∀ d : Fin (P.n + total), d ≠ q → d ≠ a → es₄.paulis d = Pauli.I := by
            intro d hdq _
            rw [hes₄, propagateGate_hadamard_paulis_ne q _ d hdq, injectClean_paulis, if_neg hdq]
          have hres : targetFaultDataResidual P
              ⟨⟨q, Gate.hadamard q :: eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              (fun q' => if freshDataQ P.n total q' = q then es₄.paulis q else Pauli.I) := by
            funext q'
            show (propagateCircuit (Gate.hadamard q :: eraseFaults
                ((qs'.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten ++ tail))
                ((PCC.cleanAtDetector cursor).inject q p)).paulis (freshDataQ P.n total q') = _
            rw [hEsplit]
            exact residual_data_HsiteHelper a qs' hanc' hancHelper q (eraseFaults tail) htail
              es₄ hes₄a (fun d hdq hda => hes₄d d hdq hda) q'
          rw [hres] at hw0 hw1
          have hle := weight_le_one_dataSingle q hqlt
            (fun q' => if freshDataQ P.n total q' = q then es₄.paulis q else Pauli.I)
            (fun q' hne => if_neg hne)
          omega
      · obtain ⟨k, hk⟩ := ih hlt' hnd' _ site p hp hrec hw0 hw1
        exact ⟨k + 1, hk⟩

/-- **E4.  X-side site classification.**  Mirror of `nz_gadget_site_classified` for an
`X`-uniform NZ gadget: every fault site's data residual has weight `≤ 1`, or equals
`nzSuffixResidual sigma j` for some in-range `j`.  The proof copies the Z-side one with
`hChain_eq`/`hChain_residual_hook`/`nzSuffix_of_liftedChain'` in place of the Z lemmas;
the `prep0`/`measZ` degenerate cases and the `j`-bound argument are identical. -/
theorem nz_gadget_site_classified_X {P : QECParams} {total : Nat} (sigma : RuleSchedule P.n)
    (gstart : Nat) (ghfit : gstart + helperCount .NZ sigma ≤ total)
    (hx : ∀ s ∈ sigma.slots, s.kind = XZPauli.X)
    (hnd : (sigma.slots.map (·.qubit)).Nodup)
    (cursor : Nat) (tail : FCircuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit (eraseFaults tail) es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q''))
    (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I)
    (hsite : site ∈ prefixErrLocsWithContextAux cursor
      (compileGadgetBlock .NZ sigma gstart ghfit) tail) :
    ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 ∨
      ∃ j, j < sigma.slots.length ∧
        targetFaultDataResidual P ⟨site, p, hp⟩ = nzSuffixResidual sigma j := by
  by_cases hw : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1
  · exact Or.inl hw
  · refine Or.inr ?_
    have hw0 : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 0 := by omega
    have hw1 : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 1 := by omega
    set a : Fin (P.n + total) := blockHelperQ P.n total gstart 1 ghfit ⟨0, by decide⟩ with ha
    have hancHelper : P.n ≤ a.val := by rw [ha]; simp [blockHelperQ]
    have hgb : compileGadgetBlock .NZ sigma gstart ghfit =
        prep0 a ++ ((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++ flagMeasZ a := rfl
    rw [hgb, show prep0 a ++ ((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++
          flagMeasZ a = prep0 a ++ (((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++
            flagMeasZ a) from by rw [List.append_assoc],
        prefixErrLocs_append, prefixErrLocs_append] at hsite
    simp only [List.mem_append] at hsite
    have htail_chain : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
        (propagateCircuit (eraseFaults (flagMeasZ a ++ tail)) es).paulis
            (freshDataQ P.n total q'') = es.paulis (freshDataQ P.n total q'') := by
      intro es q''
      rw [eraseFaults_append, QHL.Target.propagateCircuit_append, htail]
      have hef : eraseFaults (flagMeasZ a) = [Gate.measZ a] := by simp [flagMeasZ, eraseFaults]
      rw [hef]; simp only [propagateCircuit, propagateGate_measZ_paulis]
    rcases hsite with hprep | hchain | hmeas
    · rw [prefixErrLocs_prep0] at hprep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hprep
      subst hprep
      exact absurd (weight_zero_of_allI _
        (fun q' => residual_prep0_site a p _ _ q')) hw0
    · rw [hChain_eq a (liftSchedule sigma).slots
          (fun s hs => by
            simp only [liftSchedule, List.mem_map] at hs
            obtain ⟨s', hs', rfl⟩ := hs
            simp [liftSlot, hx s' hs'])] at hchain
      have hqlt : ∀ q ∈ (liftSchedule (k := total) sigma).slots.map (·.qubit), q.val < P.n := by
        intro q hq
        simp only [liftSchedule, List.map_map, List.mem_map] at hq
        obtain ⟨s, _, rfl⟩ := hq
        simp [liftSlot]
      have hqnd : ((liftSchedule (k := total) sigma).slots.map (·.qubit)).Nodup := by
        have heq : (liftSchedule (k := total) sigma).slots.map (·.qubit) =
            (sigma.slots.map (·.qubit)).map (freshDataQ P.n total) := by
          simp [liftSchedule, List.map_map, liftSlot, Function.comp]
        rw [heq]; exact hnd.map (fun _ _ => freshDataQ_inj)
      obtain ⟨k, hk⟩ := hChain_residual_hook a hancHelper (flagMeasZ a ++ tail) htail_chain
        ((liftSchedule (k := total) sigma).slots.map (·.qubit)) hqlt hqnd _ site p hp hchain hw0 hw1
      have hsk : scheduleKind sigma = Pauli.X := by
        have hne : sigma.slots ≠ [] := by
          rintro he; simp [he, liftSchedule, prefixErrLocsWithContextAux] at hchain
        obtain ⟨s0, rest0, hs0⟩ := List.exists_cons_of_ne_nil hne
        have hs0mem : s0 ∈ sigma.slots := by rw [hs0]; exact List.mem_cons_self
        simp only [scheduleKind, hs0, List.head?_cons, hx s0 hs0mem]; rfl
      have hres_nz : targetFaultDataResidual P ⟨site, p, hp⟩ = nzSuffixResidual sigma k :=
        hk.trans (nzSuffix_of_liftedChain' sigma Pauli.X hsk k)
      have hkbound : k < sigma.slots.length := by
        by_contra hge
        push_neg at hge
        apply hw0
        apply weight_zero_of_allI
        intro q'
        rw [hres_nz]
        simp only [nzSuffixResidual, List.drop_eq_nil_of_le hge, List.any_nil]
        exact if_neg (by simp)
      exact ⟨k, hkbound, hres_nz⟩
    · rw [prefixErrLocs_flagMeasZ] at hmeas
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmeas
      subst hmeas
      exact absurd (weight_zero_of_allI _
        (fun q' => residual_measZ_siteTail a p hancHelper _ _ q' htail)) hw0

/-! ## Step F: `SurfaceHValid`, discharged, and the two headline corollaries -/

/-- **`SurfaceHValid`, proved (piece 2).**  Every fault site of the compiled Surface/NZ
circuit either has a weight-`≤ 1` data residual, or its residual is a registered hook in
the union back-action set.  The site is localized to one measurement-leaf gadget
(`compileProgramAux_site_split` + `surfaceXZProgram_measLeaf`), then classified by that
gadget's uniform CSS kind (`nz_gadget_site_classified` for `Z`, `_X` for `X`); a residual
surviving the weight filter is a `nzSuffixResidual` hook, which lands in
`mkSurfaceHookErrors i`, hence in the union set (witness `i`, constant in `st'`). -/
theorem surface_hvalid (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    SurfaceHValid d hd hd3 hodd := by
  intro f hf
  obtain ⟨site, p, hp⟩ := f
  rw [errLocsWithContextAux_eq_prefix_nil] at hf
  obtain ⟨scheme, sigma, gstart, gcursor, gtail, ghfit, hML, hgtail_split, hsite⟩ :=
    compileProgramAux_site_split (total := programHelperCount (surfaceXZProgram d hd))
      (surfaceXZProgram d hd) 0 (by simp) _ [] site
      (surfaceXZProgram_allNZ d hd)
      (fun es dd _ => by simp [eraseFaults, propagateCircuit]) hf
  obtain ⟨i, rfl, rfl⟩ := surfaceXZProgram_measLeaf d hd scheme sigma hML
  have hgtail : ∀ (es : ErrorState ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd))
      (q'' : Fin (surfaceUParams d hd3 hodd).n),
      (propagateCircuit (eraseFaults gtail) es).paulis
          (freshDataQ (surfaceUParams d hd3 hodd).n (surfaceHelpers d hd) q'') =
        es.paulis (freshDataQ (surfaceUParams d hd3 hodd).n (surfaceHelpers d hd) q'') :=
    fun es q'' => hgtail_split es
      (freshDataQ (surfaceUParams d hd3 hodd).n (surfaceHelpers d hd) q'')
      (by rw [freshDataQ_val]; exact q''.isLt)
  have hclass :
      ErrorVec.weight (targetFaultDataResidual (surfaceUParams d hd3 hodd) ⟨site, p, hp⟩) ≤ 1 ∨
        ∃ j, j < (nzSchedule d hd i).slots.length ∧
          targetFaultDataResidual (surfaceUParams d hd3 hodd) ⟨site, p, hp⟩ =
            nzSuffixResidual (nzSchedule d hd i) j := by
    cases hk : kindXZ (classifyStab d i.val) with
    | X =>
        exact nz_gadget_site_classified_X (P := surfaceUParams d hd3 hodd)
          (nzSchedule d hd i) gstart ghfit
          (fun s hs => (nzSchedule_kind_uniform d hd i s hs).trans hk)
          (nzSchedule_support_nodup d hd hd3 hodd i) gcursor gtail hgtail site p hp hsite
    | Z =>
        exact nz_gadget_site_classified (P := surfaceUParams d hd3 hodd)
          (nzSchedule d hd i) gstart ghfit
          (fun s hs => (nzSchedule_kind_uniform d hd i s hs).trans hk)
          (nzSchedule_support_nodup d hd hd3 hodd i) gcursor gtail hgtail site p hp hsite
  rcases hclass with hle | ⟨j, hj, hres⟩
  · exact Or.inl hle
  · refine Or.inr fun _ => ?_
    rw [hres]
    exact ⟨i, nzSuffixResidual_mem_hookErrors d hd hd3 hodd i j hj⟩

section Corollaries

open QHL QHL.AssertionLang QHL.Source.Examples.Surface QHL.Source.Examples.SurfaceUnionSpec

/-- **Piece 3, unconditional.**  The compiled Surface/NZ circuit satisfies the
budget-guarded compiled barrier invariant — the `SurfaceHValid` hypothesis of
`surfaceNZ_compiled_FHoare` is now discharged. -/
theorem surface_compiled_FHoare (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    FHoare
      (fun sigma : QCState ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd) =>
        sigma = QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd))
      (surfaceCircuit d hd)
      (compileFormulaWithinBudget (surfaceHelpers d hd)
        (surface_inv_formula d (unionSurfaceSpec d hd3 hodd))) :=
  surfaceNZ_compiled_FHoare d hd hd3 hodd (surface_hvalid d hd hd3 hodd)

/-- **Piece 4a, unconditional.**  Compiled bar-Z circuit-level distance: every clean-start
run of `compileProgram (surfaceXZProgram d hd)` whose data residual lies in the bar-Z
logical class fired at least `d` faults. -/
theorem surface_compiled_barZ_distance (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) :
    ∀ sigma : QCState ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd),
      qceval (surfaceCircuit d hd)
        (QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd)) sigma →
      (surfaceLogicalClass d (unionSurfaceSpec d hd3 hodd)).contains
        (dataErrorOfQCState (surfaceUParams d hd3 hodd) (surfaceHelpers d hd) sigma) →
      d ≤ sigma.lambda :=
  surfaceNZ_compiled_barZ_distance d hd hd3 hodd (surface_hvalid d hd hd3 hodd)

end Corollaries

end QStab.QClifford.Compile
