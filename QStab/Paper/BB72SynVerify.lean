import QStab.Paper.BB72SynData
import QStab.Paper.BB72BV

/-!
# BB72 X-side static-DEM check via per-mech syndrome XOR (faster path)

Replaces the per-case full bv_parity over 36 + 12 stabs with
precomputed per-mech (syndrome, lz_parity) BitVec lookups. Per-case
cost drops from ~480 ops to ~10 ops.

This file is the **fast-path scaling experiment**: validate methodology
at K=2 (should be <1s vs 6.9s for original) before scaling to K=4.
-/

namespace QStab.Paper.BB72BV

/-- Per-mech-syndrome chain attack predicate at K=2. -/
def chain2_syn_check (i j : Fin 252) : Bool :=
  let s := mech_syn i ^^^ mech_syn j
  let lz := mech_lz i ^^^ mech_lz j
  decide (s = 0) && !decide (lz = 0)

/-- **No 2-mech chain has zero Z-syndrome AND non-trivial L_Z parity.**
    Fast-path: per-case ~10 ops vs ~480 in `bv_chain2_attack`. -/
theorem bb_chain_2_no_attack_syn :
    ∀ i j : Fin 252, chain2_syn_check i j = false := by
  native_decide

/-! ## Existence-form predicates with nested loops

Direct Bool functions with sorted-tuple enumeration — `C(252, K)` cases
vs `252^K` for ∀-quantifier form.

  * K=3: C(252,3) ≈ 2.6M cases, est. 1-30s native_decide.
  * K=4: C(252,4) ≈ 158M cases, est. 1-30 min.
  * K=5: C(252,5) ≈ 8.1G cases, est. hours (still borderline).
-/

/-- Does any K=3 ordered triple (i < j < k) yield a successful attack? -/
def attack_exists_k3 : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_syn i
    let li := mech_lz i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_syn j
      let lij := li ^^^ mech_lz j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let s := sij ^^^ mech_syn k
        let lz := lij ^^^ mech_lz k
        if s = 0 && lz ≠ 0 then
          found := true
  return found

/-- **No K=3 ordered triple is a successful attack** (existence-form).
    Should run in seconds (vs 19 min for the ∀-form `bb_chain_3_no_attack_bv`). -/
theorem attack_exists_k3_eq_false : attack_exists_k3 = false := by native_decide

/-- Does any K=4 ordered tuple (i < j < k < l) yield a successful attack? -/
def attack_exists_k4 : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_syn i
    let li := mech_lz i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_syn j
      let lij := li ^^^ mech_lz j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let sijk := sij ^^^ mech_syn k
        let lijk := lij ^^^ mech_lz k
        for l in List.finRange 252 do
          if found || l.val ≤ k.val then continue
          let s := sijk ^^^ mech_syn l
          let lz := lijk ^^^ mech_lz l
          if s = 0 && lz ≠ 0 then
            found := true
  return found

/-- **No K=4 ordered tuple is a successful attack** (existence-form).
    Estimated 2-3 min via native_decide. -/
theorem attack_exists_k4_eq_false : attack_exists_k4 = false := by native_decide

/-- Does any K=5 ordered tuple yield a successful attack? -/
def attack_exists_k5 : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_syn i
    let li := mech_lz i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_syn j
      let lij := li ^^^ mech_lz j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let sijk := sij ^^^ mech_syn k
        let lijk := lij ^^^ mech_lz k
        for l in List.finRange 252 do
          if found || l.val ≤ k.val then continue
          let sijkl := sijk ^^^ mech_syn l
          let lijkl := lijk ^^^ mech_lz l
          for m in List.finRange 252 do
            if found || m.val ≤ l.val then continue
            let s := sijkl ^^^ mech_syn m
            let lz := lijkl ^^^ mech_lz m
            if s = 0 && lz ≠ 0 then
              found := true
  return found

/-- **No K=5 ordered tuple is a successful attack** (existence-form).
    Built in 94 min via native_decide. -/
theorem attack_exists_k5_eq_false : attack_exists_k5 = false := by native_decide

end QStab.Paper.BB72BV
