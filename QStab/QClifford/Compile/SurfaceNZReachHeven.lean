import QStab.QClifford.Compile.SurfaceNZReach
import QStab.QClifford.Compile.SurfaceHValid
import QStab.QHL.Source.Examples.SurfaceParametricUpperBound

/-!
# F2 reach (c): the geometric core — the `heven` parity lemmas

The reach master lemma `runFScript_nzBlock` needs, per gadget, the *parity-even* side
condition `scheduleParityList (lifted slots) (injectE …) false = false`.  This file proves
that geometric core, independent of the induction (so a stuck goal here is a clean
checkpoint).

## The stage residual and the reduction

At each gadget the residual is a **column-0 prefix**: `colPrefix d m` = `X` exactly on
column-0 rows `< m`, `I` elsewhere (this also bakes in "supported on column 0").  The key
reduction (`heven_of_stage`): the schedule parity of stabilizer `k` against `colPrefix d m`
is `false` whenever every column-0 qubit in `k`'s support has row `< m` — because then the
prefix agrees with the *full* column-0 string `mkSurfaceAttackerX` (`X̄`) on `k`'s support,
and parity depends only on the support, and `X̄` commutes with every stabilizer
(`mkSurfaceAttackerX_commutes_with_stabilizers`).

`heven_of_stage` covers **Z-kind** gadgets only: it needs the column-0 support rows to be
`< m`, which fails at odd-`r` column-0 X-checks.  **X-kind** gadgets are handled separately
and unconditionally by `heven_X_kind` (X-check parity against a pure-X residual is trivially
even — `scheduleParityList_X_uniform`).  Together they cover every `classifyStab` kind; the
Z-kind stage facts (which `m` at each gadget's program position, incl. the boundary
"overlap-with-full-column = 2" case) are the remaining per-kind work.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric
open QHL.Source.Examples.SurfaceParametricUpperBound

/-- **The stage residual.**  `X` on column-0 rows `< m`, `I` elsewhere (row-major:
column 0 is `q.val % d = 0`, row is `q.val / d`). -/
def colPrefix (d m : Nat) : ErrorVec (d * d) :=
  fun q => if q.val % d = 0 ∧ q.val / d < m then Pauli.X else Pauli.I

/-- On any qubit in the support of stabilizer `k` whose column-0 rows are all `< m`, the stage
prefix agrees with the full column-0 string `X̄`. -/
theorem colPrefix_eq_attackerX_on_support {d m : Nat} (hd : 0 < d)
    (k : Fin (numStabFormula d)) (q : Fin (d * d))
    (_hsupp : mkSurfaceStabilizers d hd k q ≠ Pauli.I)
    (hstage : q.val % d = 0 → q.val / d < m) :
    colPrefix d m q = mkSurfaceAttackerX d q := by
  unfold colPrefix mkSurfaceAttackerX
  by_cases hc : q.val % d = 0
  · rw [if_pos ⟨hc, hstage hc⟩, if_pos hc]
  · rw [if_neg (fun h => hc h.1), if_neg hc]

/-- **The `heven` reduction.**  The schedule parity of stabilizer `k` against the stage prefix
`colPrefix d m` is `false` whenever every column-0 qubit in `k`'s support has row `< m`. -/
theorem heven_of_stage {d m : Nat} (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (k : Fin (numStabFormula d))
    (hstage : ∀ q : Fin (d * d), mkSurfaceStabilizers d hd k q ≠ Pauli.I →
      q.val % d = 0 → q.val / d < m) :
    scheduleParity (nzSchedule d hd k) (colPrefix d m) = false := by
  rw [scheduleParity_eq_vectorParity d hd hd3 hodd k (colPrefix d m),
    vectorParity_congr_on_support (mkSurfaceStabilizers d hd k) (colPrefix d m)
      (mkSurfaceAttackerX d)
      (fun q hq => colPrefix_eq_attackerX_on_support hd k q hq (hstage q hq)),
    vectorParity_eq_parity]
  exact mkSurfaceAttackerX_commutes_with_stabilizers d hd hodd k

/-- **X-kind `heven`.**  An X-check gadget's parity against the (pure-X) stage residual is
`false` unconditionally — no stage hypothesis (X-checks commute with X-errors).  Covers the
odd-`r` column-0 X-checks where `heven_of_stage` cannot apply. -/
theorem heven_X_kind {d m : Nat} (hd : 0 < d) (k : Fin (numStabFormula d))
    (hX : kindXZ (classifyStab d k.val) = XZPauli.X) :
    scheduleParity (nzSchedule d hd k) (colPrefix d m) = false := by
  unfold scheduleParity
  refine scheduleParityList_X_uniform (colPrefix d m) ?_ (nzSchedule d hd k).slots false ?_
  · intro q; simp only [colPrefix]; split_ifs <;> simp
  · intro slot hslot
    rw [nzSchedule_kind_uniform d hd k slot hslot]; exact hX

/-! ## (b) Domino arithmetic — injection advances the column-0 prefix -/

/-- The stage prefix at a column-0 cell `(r,0)`: `X` iff `r < m`. -/
theorem colPrefix_gridFin_col0 (d : Nat) (hd : 0 < d) (m r : Nat) (hr : r < d) :
    colPrefix d m (gridFin d hd (r, 0)) = if r < m then Pauli.X else Pauli.I := by
  unfold colPrefix
  rw [gridFin_val_of_lt d hd hr hd]
  simp only [Nat.add_zero, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hd, true_and]

/-- `colPrefix` off the two domino rows `{m, m+1}` is unchanged by advancing the stage by 2
(the two rows are exactly the injected column-0 qubits). -/
theorem colPrefix_stable_off_domino (d m : Nat) (q : Fin (d * d))
    (hq : ¬ (q.val % d = 0 ∧ (q.val / d = m ∨ q.val / d = m + 1))) :
    colPrefix d m q = colPrefix d (m + 2) q := by
  unfold colPrefix
  by_cases hc : q.val % d = 0
  · simp only [hc, true_and] at hq ⊢
    by_cases hlt : q.val / d < m
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
  · simp only [hc, false_and, if_false]

/-- A column-0 qubit at row `ρ` is exactly `gridFin (ρ,0)`. -/
theorem col0_row_eq_gridFin (d : Nat) (hd : 0 < d) (q : Fin (d * d)) (ρ : Nat) (hρ : ρ < d)
    (hc : q.val % d = 0) (hrow : q.val / d = ρ) :
    q = gridFin d hd (ρ, 0) := by
  apply Fin.ext
  rw [gridFin_val_of_lt d hd hρ hd, Nat.add_zero]
  conv_lhs => rw [← Nat.div_add_mod q.val d, hrow, hc, Nat.add_zero]

/-- `colPrefix` off the single row `m` is unchanged by advancing the stage by 1. -/
theorem colPrefix_stable_off_row (d m : Nat) (q : Fin (d * d))
    (hq : ¬ (q.val % d = 0 ∧ q.val / d = m)) :
    colPrefix d m q = colPrefix d (m + 1) q := by
  unfold colPrefix
  by_cases hc : q.val % d = 0
  · simp only [hc, true_and] at hq ⊢
    by_cases hlt : q.val / d < m
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
  · simp only [hc, false_and, if_false]

/-- Distinct column-0 rows give distinct grid qubits. -/
private theorem gridFin_col0_ne (d : Nat) (hd : 0 < d) {r s : Nat} (hr : r < d) (hs : s < d)
    (hne : r ≠ s) : gridFin d hd (r, 0) ≠ gridFin d hd (s, 0) := by
  intro heq
  have hv := congrArg Fin.val heq
  rw [gridFin_val_of_lt d hd hr hd, gridFin_val_of_lt d hd hs hd] at hv
  exact hne (Nat.eq_of_mul_eq_mul_left hd (by omega))

/-- **(b) The main domino, `bulkZ(r,0)`.**  Entering at stage `m = r`, the two entry-site
injections (slots 0, 1 = rows `r`, `r+1` of column 0) advance the embedded stage prefix by
two rows.  Freshness is exact: the prefix is `I` at both injected cells, so `pauliMul X I = X`
lands clean. -/
theorem injectE_domino_bulkZ (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (r : Nat) (h : classifyStab d k.val = .bulkZ r 0)
    (hr1 : r + 1 < d) :
    injectE (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val)
        (fun q => (dataInputState (k := total) (colPrefix d r)).paulis q)
      = fun q => (dataInputState (k := total) (colPrefix d (r + 2))).paulis q := by
  have hr : r < d := by omega
  have hne01 : freshDataQ (d * d) total (gridFin d hd (r, 0))
      ≠ freshDataQ (d * d) total (gridFin d hd (r + 1, 0)) :=
    fun heq => gridFin_col0_ne d hd hr hr1 (by omega) (freshDataQ_inj heq)
  simp only [nzSchedule, h, kindOrderRC, RuleSchedule.uniform, liftSchedule, liftSlot,
    List.map_cons, List.map_nil, injs_k, injectE, List.headD_cons, List.tail_cons]
  funext q
  rw [if_neg (fun hc => nomatch hc.1), if_neg (fun hc => nomatch hc.1)]
  by_cases hq1 : q = freshDataQ (d * d) total (gridFin d hd (r + 1, 0))
  · rw [if_pos ⟨trivial, hq1⟩, if_neg (fun hc => hne01 (hq1 ▸ hc.2).symm), hq1,
      dataInputState_freshDataQ, dataInputState_freshDataQ,
      colPrefix_gridFin_col0 d hd r (r + 1) hr1, colPrefix_gridFin_col0 d hd (r + 2) (r + 1) hr1,
      if_neg (by omega), if_pos (by omega), pauliMul_I_right]
  · rw [if_neg (fun hc => hq1 hc.2)]
    by_cases hq0 : q = freshDataQ (d * d) total (gridFin d hd (r, 0))
    · rw [if_pos ⟨trivial, hq0⟩, hq0, dataInputState_freshDataQ, dataInputState_freshDataQ,
        colPrefix_gridFin_col0 d hd r r hr, colPrefix_gridFin_col0 d hd (r + 2) r hr,
        if_neg (by omega), if_pos (by omega), pauliMul_I_right]
    · rw [if_neg (fun hc => hq0 hc.2)]
      simp only [dataInputState]
      by_cases hlt : q.val < d * d
      · rw [dif_pos hlt, dif_pos hlt]
        refine colPrefix_stable_off_domino d r ⟨q.val, hlt⟩ ?_
        rintro ⟨hc0, hrow | hrow⟩
        · exact hq0 (congrArg (freshDataQ (d * d) total)
            (col0_row_eq_gridFin d hd ⟨q.val, hlt⟩ r hr hc0 hrow))
        · exact hq1 (congrArg (freshDataQ (d * d) total)
            (col0_row_eq_gridFin d hd ⟨q.val, hlt⟩ (r + 1) hr1 hc0 hrow))
      · rw [dif_neg hlt, dif_neg hlt]

/-- **(b) The last-row injector, `bulkX(d-2,0)`.**  Entering at stage `m = r + 1 = d - 1`, the
single slot-2 injection (row `r+1 = d-1` of column 0) advances the prefix by one row,
completing the column. -/
theorem injectE_domino_bulkX (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (r : Nat) (h : classifyStab d k.val = .bulkX r 0)
    (hlast : r + 2 = d) :
    injectE (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val)
        (fun q => (dataInputState (k := total) (colPrefix d (r + 1))).paulis q)
      = fun q => (dataInputState (k := total) (colPrefix d (r + 2))).paulis q := by
  have hr1 : r + 1 < d := by omega
  simp only [injs_k, h]
  rw [if_pos hlast]
  simp only [nzSchedule, h, kindOrderRC, RuleSchedule.uniform, liftSchedule, liftSlot,
    List.map_cons, List.map_nil, injectE, List.headD_cons, List.tail_cons]
  funext q
  rw [if_neg (fun hc => nomatch hc.1)]
  by_cases hq2 : q = freshDataQ (d * d) total (gridFin d hd (r + 1, 0))
  · rw [if_pos ⟨trivial, hq2⟩, if_neg (fun hc => nomatch hc.1), if_neg (fun hc => nomatch hc.1),
      hq2, dataInputState_freshDataQ, dataInputState_freshDataQ,
      colPrefix_gridFin_col0 d hd (r + 1) (r + 1) hr1,
      colPrefix_gridFin_col0 d hd (r + 2) (r + 1) hr1,
      if_neg (by omega), if_pos (by omega), pauliMul_I_right]
  · rw [if_neg (fun hc => hq2 hc.2), if_neg (fun hc => nomatch hc.1),
      if_neg (fun hc => nomatch hc.1)]
    simp only [dataInputState]
    by_cases hlt : q.val < d * d
    · rw [dif_pos hlt, dif_pos hlt]
      refine colPrefix_stable_off_row d (r + 1) ⟨q.val, hlt⟩ ?_
      rintro ⟨hc0, hrow⟩
      exact hq2 (congrArg (freshDataQ (d * d) total)
        (col0_row_eq_gridFin d hd ⟨q.val, hlt⟩ (r + 1) hr1 hc0 hrow))
    · rw [dif_neg hlt, dif_neg hlt]

/-! ## (d) Z-kind `hstage` facts — column-0 support rows are below the post-injection stage -/

/-- **`hstage` for a column-0 `Z`-injector `bulkZ(r,0)`.**  Its column-0 support is exactly rows
`r, r+1`, both `< r+2` — the post-injection stage supplied by `injectE_domino_bulkZ`. -/
theorem hstage_bulkZ (d : Nat) (hd : 0 < d) (k : Fin (numStabFormula d)) (r : Nat)
    (h : classifyStab d k.val = .bulkZ r 0) :
    ∀ q : Fin (d * d), mkSurfaceStabilizers d hd k q ≠ Pauli.I →
      q.val % d = 0 → q.val / d < r + 2 := by
  intro q hsupp hcol
  have hin : inStabSupport d k.val (q.val / d) (q.val % d) := hsupp
  rw [inStabSupport_iff_supportByKind, h] at hin
  simp only [supportByKind, hcol, decide_eq_true_eq] at hin
  omega

/-- **`hstage` for the boundary `leftZ(b)`** at the full-column stage `m = d`: its column-0
support (rows `2b+1, 2b+2 ≤ d-1`) is trivially `< d`. -/
theorem hstage_leftZ (d : Nat) (hd : 0 < d) (_hd3 : 3 ≤ d) (_hodd : d % 2 = 1)
    (k : Fin (numStabFormula d)) (b : Nat) (_h : classifyStab d k.val = .leftZ b) :
    ∀ q : Fin (d * d), mkSurfaceStabilizers d hd k q ≠ Pauli.I →
      q.val % d = 0 → q.val / d < d := by
  intro q _hsupp _hcol
  exact Nat.div_lt_of_lt_mul q.isLt

/-- **`hstage` (vacuous) for column ≥ 1 `Z`-checks** (`bulkZ(_,c+1)` / `rightZ`): no column-0
support qubit, so the antecedent is empty. -/
theorem hstage_bulkZ_col (d : Nat) (hd : 0 < d) (k : Fin (numStabFormula d)) (r c m : Nat)
    (h : classifyStab d k.val = .bulkZ r (c + 1)) :
    ∀ q : Fin (d * d), mkSurfaceStabilizers d hd k q ≠ Pauli.I →
      q.val % d = 0 → q.val / d < m := by
  intro q hsupp hcol
  have hin : inStabSupport d k.val (q.val / d) (q.val % d) := hsupp
  rw [inStabSupport_iff_supportByKind, h] at hin
  simp only [supportByKind, hcol, decide_eq_true_eq] at hin
  omega

/-- **`hstage` (vacuous) for the boundary `rightZ(b)`**: its support sits in column `d-1 ≠ 0`
(as `2 ≤ d`), so there is no column-0 support qubit. -/
theorem hstage_rightZ (d : Nat) (hd : 0 < d) (hd2 : 2 ≤ d) (k : Fin (numStabFormula d)) (b m : Nat)
    (h : classifyStab d k.val = .rightZ b) :
    ∀ q : Fin (d * d), mkSurfaceStabilizers d hd k q ≠ Pauli.I →
      q.val % d = 0 → q.val / d < m := by
  intro q hsupp hcol
  have hin : inStabSupport d k.val (q.val / d) (q.val % d) := hsupp
  rw [inStabSupport_iff_supportByKind, h] at hin
  simp only [supportByKind, hcol, decide_eq_true_eq] at hin
  omega

/-! ## (d) The stage function `stageAt` — column-0 injection count below `k`

The gadgets run in `finRange` order (`surfaceXZProgram = foldr … finRange`).  The **stage** at
program position `k` is the number of column-0 rows already injected, i.e. the prefix count of
`true` slots in `injs_k`.  Each `bulkZ(_,0)` domino injects 2 rows, the final `bulkX(d-2,0)`
injects 1, everything else 0 — so at a column-0 injector `bulkZ(r,0)` (index `r*(d-1)`) the
stage equals exactly `r`, the domino's entry precondition. -/

/-- Column-0 X-injections performed at gadget `j` = number of `true` slots in `injs_k d j`. -/
def injRows (d j : Nat) : Nat := (injs_k d j).count true

/-- **The stage before gadget `k`** = total column-0 rows injected by gadgets `0 .. k-1`. -/
def stageAt (d k : Nat) : Nat := ((List.range k).map (injRows d)).sum

@[simp] theorem stageAt_zero (d : Nat) : stageAt d 0 = 0 := rfl

/-- **Definitional advance.**  Processing gadget `k` adds its own column-0 injection count. -/
theorem stageAt_succ (d k : Nat) : stageAt d (k + 1) = stageAt d k + injRows d k := by
  unfold stageAt
  rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- **Monotonicity.**  The stage never decreases. -/
theorem stageAt_mono (d : Nat) {k k' : Nat} (h : k ≤ k') : stageAt d k ≤ stageAt d k' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => rw [stageAt_succ]; exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- **Interval decomposition.**  The stage over `[0, a+n)` splits at `a`: the tail is the sum of
per-gadget injections on `[a, a+n)`. -/
theorem stageAt_add (d a n : Nat) :
    stageAt d (a + n) = stageAt d a + ((List.range n).map (fun i => injRows d (a + i))).sum := by
  unfold stageAt
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  congr 1

/-- A column-0 `Z`-check `bulkZ(r,0)` sits at program index `r*(d-1)`. -/
theorem classifyStab_bulkZ_col0 (d j r : Nat) (h : classifyStab d j = .bulkZ r 0) :
    j = r * (d - 1) := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  have hkey : (d - 1) * (j / (d - 1)) + j % (d - 1) = j := Nat.div_add_mod j (d - 1)
  rw [hr_eq, hc_eq, Nat.add_zero] at hkey
  rw [← hkey, Nat.mul_comm (d - 1) r]

/-- A column-0 `X`-check `bulkX(r,0)` sits at program index `r*(d-1)`. -/
theorem classifyStab_bulkX_col0 (d j r : Nat) (h : classifyStab d j = .bulkX r 0) :
    j = r * (d - 1) := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  have hkey : (d - 1) * (j / (d - 1)) + j % (d - 1) = j := Nat.div_add_mod j (d - 1)
  rw [hr_eq, hc_eq, Nat.add_zero] at hkey
  rw [← hkey, Nat.mul_comm (d - 1) r]

/-- The injection count at a column-0 `Z`-check is `2`. -/
theorem injRows_bulkZ0 (d j r : Nat) (h : classifyStab d j = .bulkZ r 0) : injRows d j = 2 := by
  unfold injRows injs_k; rw [h]; rfl

/-- The injection count at the final column-0 `X`-injector is `1`. -/
theorem injRows_bulkX0_last (d j r : Nat) (h : classifyStab d j = .bulkX r 0) (hr : r + 2 = d) :
    injRows d j = 1 := by
  unfold injRows injs_k; rw [h]; simp only [if_pos hr]; rfl

/-- **Interior of an interval contributes nothing.**  Any gadget off column 0 injects no
column-0 row (its `injs_k` slots are all `false` or it is a boundary/`c≥1` check). -/
theorem injRows_eq_zero_of_mod (d j : Nat) (hc : j % (d - 1) ≠ 0) : injRows d j = 0 := by
  unfold injRows injs_k
  cases h : classifyStab d j with
  | bulkZ r c =>
    cases c with
    | zero =>
      exact absurd (by rw [classifyStab_bulkZ_col0 d j r h]; exact Nat.mul_mod_left r (d - 1)) hc
    | succ c' => rfl
  | bulkX r c =>
    cases c with
    | zero =>
      exact absurd (by rw [classifyStab_bulkX_col0 d j r h]; exact Nat.mul_mod_left r (d - 1)) hc
    | succ c' => rfl
  | topX b => rfl
  | rightZ b => rfl
  | leftZ b => rfl
  | bottomX b => rfl

/-- A `range n` sum whose only nonzero term is at index `0` equals that head term. -/
theorem sum_range_eq_head {n : Nat} (f : Nat → Nat) (hn : 0 < n)
    (h0 : ∀ i, 0 < i → i < n → f i = 0) :
    ((List.range n).map f).sum = f 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have htail : ((List.range m).map (f ∘ Nat.succ)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h0 (i + 1) (Nat.succ_pos i) (by omega)
  rw [htail, Nat.add_zero]

/-- **One interval advances the stage by its column-0 injector value.**  Over `[r*(d-1),
(r+1)*(d-1))` the only column-0 gadget is the head `r*(d-1)`; the interior is off column 0. -/
theorem stageAt_step (d r : Nat) (hd : 1 < d) :
    stageAt d ((r + 1) * (d - 1)) = stageAt d (r * (d - 1)) + injRows d (r * (d - 1)) := by
  have hpos : 0 < d - 1 := by omega
  have heq : (r + 1) * (d - 1) = r * (d - 1) + (d - 1) := by ring
  have h0 : ∀ i, 0 < i → i < d - 1 → injRows d (r * (d - 1) + i) = 0 := by
    intro i hi hilt
    apply injRows_eq_zero_of_mod
    rw [Nat.mul_comm r (d - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hilt]
    omega
  rw [heq, stageAt_add, sum_range_eq_head _ hpos h0]
  simp

/-- **Forward classification of column-0 bulk indices.**  Index `s*(d-1)` (for `s < d-1`) is the
`s`-th column-0 bulk check: a `Z`-check when `s` is even, an `X`-check when odd. -/
theorem classifyStab_col0 (d s : Nat) (_hd : 1 < d) (hs : s < d - 1) :
    classifyStab d (s * (d - 1)) = if s % 2 = 0 then .bulkZ s 0 else .bulkX s 0 := by
  have hpos : 0 < d - 1 := by omega
  have hdiv : (s * (d - 1)) / (d - 1) = s := Nat.mul_div_cancel s hpos
  have hmod : (s * (d - 1)) % (d - 1) = 0 := Nat.mul_mod_left s (d - 1)
  have hlt : s * (d - 1) < (d - 1) * (d - 1) := (Nat.mul_lt_mul_right hpos).mpr hs
  simp only [classifyStab, hlt, if_true, hdiv, hmod, Nat.add_zero]

/-- **Injection count at a column-0 bulk index.**  `2` at an even (`Z`-)row, `0` at an odd
(`X`-)row that is not the final injector. -/
theorem injRows_col0 (d s : Nat) (hd : 1 < d) (hs : s < d - 1) (hnl : s + 2 ≠ d) :
    injRows d (s * (d - 1)) = if s % 2 = 0 then 2 else 0 := by
  by_cases hpar : s % 2 = 0
  · rw [if_pos hpar]
    exact injRows_bulkZ0 d (s * (d - 1)) s (by rw [classifyStab_col0 d s hd hs, if_pos hpar])
  · rw [if_neg hpar]
    have hk : classifyStab d (s * (d - 1)) = .bulkX s 0 := by
      rw [classifyStab_col0 d s hd hs, if_neg hpar]
    unfold injRows injs_k; rw [hk]; simp only [if_neg hnl]; rfl

/-- Bounds from a `bulkZ` classification: `r+1 < d` and the checkerboard parity `(r+c) % 2 = 0`. -/
theorem classifyStab_bulkZ_bounds (d j r c : Nat) (h : classifyStab d j = .bulkZ r c) :
    r + 1 < d ∧ (r + c) % 2 = 0 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  subst hr_eq hc_eq
  have hpos : 0 < d - 1 := by
    rcases Nat.eq_zero_or_pos (d - 1) with hz | hp
    · rw [hz, Nat.mul_zero] at hbulk; omega
    · exact hp
  have hlt : j / (d - 1) < d - 1 :=
    (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [Nat.mul_comm]; exact hbulk)
  exact ⟨by omega, hpar⟩

/-- **The even-row stage recurrence.**  After the first `2t` column-0 rows (the dominoes at rows
`0, 2, …, 2t-2`, each `+2`, with the odd `X`-checks between them injecting nothing) the stage is
exactly `2t` — valid up to the last `Z`-domino row `d-3`. -/
theorem stageAt_bulkZ_aux (d : Nat) (hd : 1 < d) (hodd : d % 2 = 1) :
    ∀ t, 2 * t ≤ d - 3 → stageAt d ((2 * t) * (d - 1)) = 2 * t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro hle
    have hle' : 2 * t ≤ d - 3 := by omega
    have e1 : stageAt d ((2 * t + 1) * (d - 1))
        = stageAt d ((2 * t) * (d - 1)) + injRows d ((2 * t) * (d - 1)) := stageAt_step d (2 * t) hd
    have e2 : stageAt d ((2 * t + 1 + 1) * (d - 1))
        = stageAt d ((2 * t + 1) * (d - 1)) + injRows d ((2 * t + 1) * (d - 1)) :=
      stageAt_step d (2 * t + 1) hd
    have iv1 : injRows d ((2 * t) * (d - 1)) = 2 := by
      rw [injRows_col0 d (2 * t) hd (by omega) (by omega), if_pos (show (2 * t) % 2 = 0 by omega)]
    have iv2 : injRows d ((2 * t + 1) * (d - 1)) = 0 := by
      rw [injRows_col0 d (2 * t + 1) hd (by omega) (by omega),
        if_neg (show ¬ (2 * t + 1) % 2 = 0 by omega)]
    have hk : (2 * (t + 1)) * (d - 1) = (2 * t + 1 + 1) * (d - 1) := by ring_nf
    rw [hk, e2, e1, iv1, iv2, ih hle']
    ring

/-- **Per-kind stage value — column-0 `Z`-domino.**  Reaching a `bulkZ(r,0)` gadget, exactly `r`
column-0 rows are already injected: the domino's entry precondition `colPrefix d r`. -/
theorem stageAt_of_bulkZ (d k r : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (h : classifyStab d k = .bulkZ r 0) : stageAt d k = r := by
  have hidx : k = r * (d - 1) := classifyStab_bulkZ_col0 d k r h
  obtain ⟨hrd, hpar⟩ := classifyStab_bulkZ_bounds d k r 0 h
  have hr2 : r = 2 * (r / 2) := by omega
  have hrle : 2 * (r / 2) ≤ d - 3 := by omega
  rw [hidx, hr2]
  exact stageAt_bulkZ_aux d (by omega) hodd (r / 2) hrle

/-- **Per-kind stage value — final column-0 `X`-injector.**  Reaching `bulkX(d-2,0)` (`r+2 = d`),
the whole column below the last row is injected: the stage is `r+1 = d-1`. -/
theorem stageAt_of_bulkX_last (d k r : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (h : classifyStab d k = .bulkX r 0) (hr : r + 2 = d) : stageAt d k = r + 1 := by
  have hidx : k = r * (d - 1) := classifyStab_bulkX_col0 d k r h
  have hd1 : 1 < d := by omega
  have hr1 : r - 1 + 1 = r := by omega
  have hstep : stageAt d ((r - 1 + 1) * (d - 1))
      = stageAt d ((r - 1) * (d - 1)) + injRows d ((r - 1) * (d - 1)) := stageAt_step d (r - 1) hd1
  have hbase : stageAt d ((r - 1) * (d - 1)) = r - 1 := by
    rw [show r - 1 = 2 * ((r - 1) / 2) by omega]
    exact stageAt_bulkZ_aux d hd1 hodd ((r - 1) / 2) (by omega)
  have hinj : injRows d ((r - 1) * (d - 1)) = 2 := by
    rw [injRows_col0 d (r - 1) hd1 (by omega) (by omega), if_pos (show (r - 1) % 2 = 0 by omega)]
  have hcompute : stageAt d (r * (d - 1)) = r + 1 := by
    rw [show r * (d - 1) = (r - 1 + 1) * (d - 1) by rw [hr1], hstep, hbase, hinj]; omega
  rw [hidx]; exact hcompute

/-! ## (d) The stage total and the final residual -/

/-- **Gap #3 — the final residual is `X̄`.**  The full-column stage prefix `colPrefix d d` is
exactly `mkSurfaceAttackerX` (every qubit's row `< d`, so the row cutoff is vacuous). -/
theorem colPrefix_d_eq_attackerX (d : Nat) : colPrefix d d = mkSurfaceAttackerX d := by
  funext q
  unfold colPrefix mkSurfaceAttackerX
  have hrow : q.val / d < d := Nat.div_lt_of_lt_mul q.isLt
  by_cases hc : q.val % d = 0
  · rw [if_pos ⟨hc, hrow⟩, if_pos hc]
  · rw [if_neg (fun h => hc h.1), if_neg hc]

/-- No column-0 injector sits past the last one `bulkX(d-2,0)` at index `(d-2)*(d-1)`. -/
theorem injRows_zero_of_gt_last (d j : Nat) (hd : 1 < d) (hj : (d - 2) * (d - 1) < j) :
    injRows d j = 0 := by
  unfold injRows injs_k
  cases h : classifyStab d j with
  | bulkZ r c =>
    cases c with
    | zero =>
      exfalso
      obtain ⟨hrd, _⟩ := classifyStab_bulkZ_bounds d j r 0 h
      have hle : j ≤ (d - 2) * (d - 1) := by
        rw [classifyStab_bulkZ_col0 d j r h]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    | succ c' => rfl
  | bulkX r c =>
    cases c with
    | zero =>
      by_cases hrd : r + 2 = d
      · exfalso
        have hjeq : j = (d - 2) * (d - 1) := by
          rw [classifyStab_bulkX_col0 d j r h]; congr 1; omega
        omega
      · simp only [if_neg hrd]; rfl
    | succ c' => rfl
  | topX b => rfl
  | rightZ b => rfl
  | leftZ b => rfl
  | bottomX b => rfl

/-- **Gap #1 — the stage total is `d`.**  Every column-0 row is injected exactly once across the
whole gadget list: the `(d-1)/2` even `Z`-dominoes contribute `d-1` rows, the final `X`-injector
one more, and all boundary/`c≥1` gadgets contribute nothing. -/
theorem stageAt_total (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    stageAt d (numStabFormula d) = d := by
  have hd1 : 1 < d := by omega
  have hclass : classifyStab d ((d - 2) * (d - 1)) = .bulkX (d - 2) 0 := by
    rw [classifyStab_col0 d (d - 2) hd1 (by omega), if_neg (show ¬ (d - 2) % 2 = 0 by omega)]
  have hbase : stageAt d ((d - 2) * (d - 1)) = d - 1 := by
    have := stageAt_of_bulkX_last d ((d - 2) * (d - 1)) (d - 2) hd3 hodd hclass (by omega)
    omega
  have hM : stageAt d ((d - 2) * (d - 1) + 1) = d := by
    rw [stageAt_succ, hbase, injRows_bulkX0_last d ((d - 2) * (d - 1)) (d - 2) hclass (by omega)]
    omega
  have hnum : numStabFormula d = (d - 1) * (d - 1) + 2 * (d - 1) := by
    unfold numStabFormula; rw [Nat.max_eq_right (by omega)]
  have hprod : (d - 2) * (d - 1) + (d - 1) = (d - 1) * (d - 1) := by
    rw [← Nat.succ_mul]; congr 1; omega
  have hle : (d - 2) * (d - 1) + 1 ≤ numStabFormula d := by rw [hnum]; omega
  rw [show numStabFormula d = ((d - 2) * (d - 1) + 1)
        + (numStabFormula d - ((d - 2) * (d - 1) + 1)) by omega,
    stageAt_add, hM]
  have htail : ((List.range (numStabFormula d - ((d - 2) * (d - 1) + 1))).map
      (fun i => injRows d ((d - 2) * (d - 1) + 1 + i))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact injRows_zero_of_gt_last d ((d - 2) * (d - 1) + 1 + i) hd1 (by omega)
  rw [htail, Nat.add_zero]

end QStab.QClifford.Compile
