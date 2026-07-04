import QStab.QClifford.Compile.HGPNZReach

/-!
# HGP reach: scheme-independent shared infrastructure

The row-prefix invariant (`hgpRowB`/`hgpRowPref`), the per-gadget data advance
(`hgp_injectE_advances_amb`), and the parity-even side condition
(`hgp_heven_amb`) do **not** depend on the syndrome-extraction scheme: they are
statements about the shared `hgpSchedule` family, the `hgpInjs` row-0 injection
pattern, and `injectE`/`scheduleParityList` on the data block.  Only the
*ambient helper count* `total` (which differs per scheme — NZ has one ancilla
per gadget, Knill one per slot, etc.) appears, and it appears only as a
parameter.

This module extracts those lemmas — originally proved privately inside the NZ
reach fold (`HGPNZSafe`) with `total := programHelperCount (hgpXZProgram d)`
baked in — as a shared, `total`-parametric (`_amb`) API.  `HGPNZSafe`
re-instantiates them at the NZ helper count; `HGPKnillReach` re-instantiates
them at the Knill helper count.  Nothing here is scheme-specific and nothing is
duplicated: the NZ file's versions become one-line specializations.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric
open QHL QHL.CodeHGPSchedule
open QHL.Source.Examples.HGPUnionSpec

/-! ## The row-prefix invariant (data-only, helper-count independent) -/

/-- Boolean X-support after `m` gadgets: row-0 columns `< min m d`. -/
def hgpRowB (d m : Nat) : Fin (d * d + (d - 1) * (d - 1)) → Bool :=
  fun q => if q.val < min m d then true else false

/-- Pauli form of the row-prefix. -/
def hgpRowPref (d m : Nat) : Fin (d * d + (d - 1) * (d - 1)) → Pauli :=
  fun q => if q.val < min m d then Pauli.X else Pauli.I

theorem xOfBool_hgpRowB (d m : Nat) (q : Fin (d * d + (d - 1) * (d - 1))) :
    xOfBool (hgpRowB d m q) = hgpRowPref d m q := by
  unfold hgpRowB hgpRowPref xOfBool
  by_cases h : q.val < min m d
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- The saturated prefix is the logical `X̄`. -/
theorem hgpRowPref_total (d m : Nat) (hd : 2 ≤ d) (hm : d ≤ m) :
    hgpRowPref d m = mkHGPRepLogicalX d hd := by
  funext q
  unfold hgpRowPref
  rw [mkHGPRepLogicalX_spec]
  have hmin : min m d = d := Nat.min_eq_right hm
  rw [hmin]
  have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
  by_cases h : q.val < d
  · rw [if_pos h, if_pos ⟨by omega, Nat.div_eq_of_lt h⟩]
  · rw [if_neg h, if_neg ?_]
    intro ⟨h1, h2⟩
    have hdm := Nat.div_add_mod q.val d
    rw [h2, Nat.mul_zero, Nat.zero_add] at hdm
    have hmlt : q.val % d < d := Nat.mod_lt _ (by omega)
    omega

/-- Pointwise prefix update at the injected column. -/
theorem hgpRowPref_at_self (d k : Nat) (hk : k < d)
    (hkn : k < d * d + (d - 1) * (d - 1)) :
    pauliMul Pauli.X (hgpRowPref d k ⟨k, hkn⟩) = hgpRowPref d (k + 1) ⟨k, hkn⟩ := by
  unfold hgpRowPref
  have h1 : ¬ ((⟨k, hkn⟩ : Fin (d * d + (d - 1) * (d - 1))).val < min k d) := by
    show ¬ (k < min k d)
    omega
  have h2 : (⟨k, hkn⟩ : Fin (d * d + (d - 1) * (d - 1))).val < min (k + 1) d := by
    show k < min (k + 1) d
    omega
  rw [if_neg h1, if_pos h2]
  rfl

/-- Pointwise prefix stability away from the injected column. -/
theorem hgpRowPref_stable (d k qv : Nat) (hne : qv ≠ k)
    (hkn : qv < d * d + (d - 1) * (d - 1)) :
    hgpRowPref d k ⟨qv, hkn⟩ = hgpRowPref d (k + 1) ⟨qv, hkn⟩ := by
  unfold hgpRowPref
  by_cases h : qv < min k d
  · rw [if_pos (show (⟨qv, hkn⟩ : Fin (d * d + (d - 1) * (d - 1))).val < min k d from h),
      if_pos (show (⟨qv, hkn⟩ : Fin (d * d + (d - 1) * (d - 1))).val < min (k + 1) d
        from by show qv < min (k + 1) d; omega)]
  · rw [if_neg (show ¬ ((⟨qv, hkn⟩ : Fin (d * d + (d - 1) * (d - 1))).val < min k d) from h),
      if_neg (show ¬ ((⟨qv, hkn⟩ : Fin (d * d + (d - 1) * (d - 1))).val < min (k + 1) d)
        from by show ¬ (qv < min (k + 1) d); omega)]

/-! ## The injection pattern (count, helper-count independent) -/

theorem count_true_replicate_false :
    ∀ n : Nat, (List.replicate n false).count true = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.count_cons, ih]
    rfl

theorem hgpInjs_count (d k : Nat) :
    (hgpInjs d k).count true = if k < d then 1 else 0 := by
  unfold hgpInjs
  by_cases hk : k < d
  · rw [if_pos hk, if_pos hk, List.count_cons, count_true_replicate_false]
    rfl
  · rw [if_neg hk, if_neg hk, count_true_replicate_false]

/-! ## Ambient-parametric per-gadget lemmas

These are proved once over an abstract ambient helper count `total`; the NZ and
Knill reach folds instantiate `total` at their own program helper counts. -/

/-- The prefix state is pure-X ambiently. -/
theorem dataInputState_rowPref_pureX_amb (d m total : Nat) :
    ∀ q, (dataInputState (k := total) (hgpRowPref d m)).paulis q = Pauli.X
      ∨ (dataInputState (k := total) (hgpRowPref d m)).paulis q = Pauli.I := by
  intro q
  simp only [dataInputState]
  by_cases hq : q.val < d * d + (d - 1) * (d - 1)
  · rw [dif_pos hq]
    unfold hgpRowPref
    by_cases h : q.val < min m d
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  · rw [dif_neg hq]
    exact Or.inr rfl

/-- Kind uniformity survives the lift. -/
theorem hgp_lifted_kind_amb (d : Nat) (hd : 2 ≤ d)
    (k : Fin (2 * ((d - 1) * d))) (total : Nat) :
    ∀ slot ∈ (liftSchedule (k := total) (hgpSchedule d hd k)).slots,
      slot.kind = hgpKind d k.val := by
  intro slot hslot
  have hs : (liftSchedule (k := total) (hgpSchedule d hd k)).slots
      = (hgpSchedule d hd k).slots.map liftSlot := rfl
  rw [hs] at hslot
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hslot
  show s0.kind = hgpKind d k.val
  exact hgpSchedule_kind_uniform d hd k s0 hs0

/-- Slot-list lengths line up with the injection pattern. -/
theorem hgpInjs_length_amb (d : Nat) (hd : 2 ≤ d) (k : Fin (2 * ((d - 1) * d)))
    (total : Nat) :
    (hgpInjs d k.val).length
      = (liftSchedule (k := total) (hgpSchedule d hd k)).slots.length := by
  have hlen : (liftSchedule (k := total) (hgpSchedule d hd k)).slots.length
      = (hgpSupportList d k.val).length := by
    show ((hgpSchedule d hd k).slots.map liftSlot).length = _
    rw [List.length_map]
    show (((hgpSupportList d k.val).map (hgpFin d hd)).map _).length = _
    rw [List.length_map, List.length_map]
  rw [hlen]
  unfold hgpInjs
  by_cases hk : k.val < d
  · rw [if_pos hk, List.length_cons, List.length_replicate]
    have h3 := (hgpLenFlat_window d k.val hd k.isLt).1
    show hgpLenFlat d k.val - 1 + 1 = hgpLenFlat d k.val
    omega
  · rw [if_neg hk, List.length_replicate]
    rfl

/-- **The injector's slot-0 shape**: for `k < d`, the lifted schedule's slot list
starts with the coupling of data qubit `k` (row 0, column `k`), followed by the
mapped tail of the support list. -/
theorem hgp_slots_cons_amb (d : Nat) (hd : 2 ≤ d) (k : Fin (2 * ((d - 1) * d)))
    (total : Nat) (hk : k.val < d) :
    (liftSchedule (k := total) (hgpSchedule d hd k)).slots
      = (⟨hgpKind d k.val,
          freshDataQ (d * d + (d - 1) * (d - 1)) total
            ⟨k.val, by
              have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
              omega⟩⟩ : ScheduledPauli _)
        :: ((((d * (k.val / d + 1) + k.val % d)
            :: ((if 1 ≤ k.val % d
                  then [d * d + k.val / d * (d - 1) + (k.val % d - 1)] else [])
              ++ (if k.val % d ≤ d - 2
                  then [d * d + k.val / d * (d - 1) + k.val % d] else []))).map
              (hgpFin d hd)).map
            (fun q => (⟨hgpKind d k.val, q⟩
              : ScheduledPauli (d * d + (d - 1) * (d - 1))))).map liftSlot := by
  have hxk : k.val < (d - 1) * d := by
    have hdd : d ≤ (d - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    omega
  have hsup : hgpSupportList d k.val
      = (d * (k.val / d) + k.val % d) :: ((d * (k.val / d + 1) + k.val % d)
          :: ((if 1 ≤ k.val % d
                then [d * d + k.val / d * (d - 1) + (k.val % d - 1)] else [])
            ++ (if k.val % d ≤ d - 2
                then [d * d + k.val / d * (d - 1) + k.val % d] else []))) := by
    unfold hgpSupportList
    rw [if_pos hxk]
    rfl
  have he1 : d * (k.val / d) + k.val % d = k.val := by
    rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, Nat.mul_zero, Nat.zero_add]
  have hfin : hgpFin d hd k.val = ⟨k.val, by
      have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
      omega⟩ := by
    apply Fin.ext
    show k.val % (d * d + (d - 1) * (d - 1)) = k.val
    exact Nat.mod_eq_of_lt (by
      have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
      omega)
  show (((hgpSupportList d k.val).map (hgpFin d hd)).map
      (fun q => (⟨hgpKind d k.val, q⟩
        : ScheduledPauli (d * d + (d - 1) * (d - 1))))).map liftSlot = _
  rw [hsup]
  simp only [List.map_cons]
  rw [he1, hfin]
  rfl

/-- **Data advance.**  One gadget's entry-site injections move the row-prefix
one column forward (injector `k < d`) or leave it unchanged. -/
theorem hgp_injectE_advances_amb (d : Nat) (hd : 2 ≤ d)
    (k : Fin (2 * ((d - 1) * d))) (total : Nat) :
    injectE (liftSchedule (k := total) (hgpSchedule d hd k)).slots (hgpInjs d k.val)
      (dataInputState (k := total) (hgpRowPref d k.val)).paulis
    = (dataInputState (k := total) (hgpRowPref d (k.val + 1))).paulis := by
  by_cases hk : k.val < d
  · have hinj : hgpInjs d k.val
        = true :: List.replicate (hgpLenFlat d k.val - 1) false := by
      unfold hgpInjs
      rw [if_pos hk]
    rw [hgp_slots_cons_amb d hd k total hk, hinj, injectE]
    simp only [List.tail_cons, List.headD_cons]
    rw [injectE_all_false _ _ _ (fun b hb => List.eq_of_mem_replicate hb)]
    funext q
    by_cases hq : q = freshDataQ (d * d + (d - 1) * (d - 1)) total ⟨k.val, by
          have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
          omega⟩
    · rw [hq, if_pos ⟨trivial, rfl⟩, dataInputState_freshDataQ, dataInputState_freshDataQ]
      exact hgpRowPref_at_self d k.val hk _
    · rw [if_neg (fun h => hq h.2)]
      have hne : q.val ≠ k.val := by
        intro h
        exact hq (Fin.ext (by rw [freshDataQ_val]; exact h))
      simp only [dataInputState]
      by_cases hqd : q.val < d * d + (d - 1) * (d - 1)
      · rw [dif_pos hqd, dif_pos hqd]
        exact hgpRowPref_stable d k.val q.val hne hqd
      · rw [dif_neg hqd, dif_neg hqd]
  · have hinj : hgpInjs d k.val = List.replicate (hgpLenFlat d k.val) false := by
      unfold hgpInjs
      rw [if_neg hk]
    rw [hinj, injectE_all_false _ _ _ (fun b hb => List.eq_of_mem_replicate hb)]
    rw [show hgpRowPref d k.val = hgpRowPref d (k.val + 1) from funext fun q => by
      unfold hgpRowPref
      rw [(by omega : min k.val d = min (k.val + 1) d)]]

/-- **The side condition**: every gadget's parity check is quiet against the
advanced prefix — X-gadgets by pure-X blindness, Z-gadgets by `hgp_Xbar_comm`
on the completed `X̄`. -/
theorem hgp_heven_amb (d : Nat) (hd : 2 ≤ d) (k : Fin (2 * ((d - 1) * d)))
    (total : Nat) :
    scheduleParityList (liftSchedule (k := total) (hgpSchedule d hd k)).slots
      (injectE (liftSchedule (k := total) (hgpSchedule d hd k)).slots (hgpInjs d k.val)
        (dataInputState (k := total) (hgpRowPref d k.val)).paulis)
      false = false := by
  rw [hgp_injectE_advances_amb d hd k total]
  by_cases hx : k.val < (d - 1) * d
  · exact scheduleParityList_X_uniform _ (dataInputState_rowPref_pureX_amb d (k.val + 1) total) _ _
      (fun slot hslot => by
        rw [hgp_lifted_kind_amb d hd k total slot hslot]
        unfold hgpKind
        rw [if_pos hx])
  · have hkd : d ≤ k.val := by
      have hdd : d ≤ (d - 1) * d := Nat.le_mul_of_pos_left d (by omega)
      omega
    rw [hgpRowPref_total d (k.val + 1) hd (by omega)]
    have hlift : scheduleParityList (liftSchedule (k := total) (hgpSchedule d hd k)).slots
        (dataInputState (n := d * d + (d - 1) * (d - 1)) (k := total)
          (mkHGPRepLogicalX d hd)).paulis false
        = scheduleParity (hgpSchedule d hd k) (mkHGPRepLogicalX d hd) :=
      scheduleParityList_liftSchedule (k := total)
        (hgpSchedule d hd k) (mkHGPRepLogicalX d hd)
    rw [hlift, hgp_scheduleParity_eq_vectorParity d hd k (mkHGPRepLogicalX d hd),
      vectorParity_eq_parity]
    exact hgp_Xbar_comm d hd k

end QStab.QClifford.Compile
