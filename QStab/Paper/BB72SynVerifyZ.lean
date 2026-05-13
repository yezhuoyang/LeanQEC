import QStab.Paper.BB72SynDataZ

/-!
# BB72 NZ Z-side static-DEM check via per-mech (X-stab-syndrome, L_X parity)

Mirror of `BB72SynVerify` for the Z-side. Uses precomputed
`mech_xstab_syn` and `mech_lx` BitVecs. Per-case cost ~10 ops.
-/

namespace QStab.Paper.BB72BVZ

/-- Per-mech-syndrome chain attack predicate at K=2. -/
def chain2_syn_check_Z (i j : Fin 252) : Bool :=
  let s := mech_xstab_syn i ^^^ mech_xstab_syn j
  let lx := mech_lx i ^^^ mech_lx j
  decide (s = 0) && !decide (lx = 0)

theorem bb_chain_2_no_attack_syn_Z :
    ∀ i j : Fin 252, chain2_syn_check_Z i j = false := by
  native_decide

/-- Does any K=3 ordered triple (i < j < k) yield a successful Z-attack? -/
def attack_exists_k3_Z : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_xstab_syn i
    let li := mech_lx i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_xstab_syn j
      let lij := li ^^^ mech_lx j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let s := sij ^^^ mech_xstab_syn k
        let lx := lij ^^^ mech_lx k
        if s = 0 && lx ≠ 0 then
          found := true
  return found

theorem attack_exists_k3_Z_eq_false : attack_exists_k3_Z = false := by native_decide

/-- Does any K=4 ordered tuple yield a successful Z-attack? -/
def attack_exists_k4_Z : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_xstab_syn i
    let li := mech_lx i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_xstab_syn j
      let lij := li ^^^ mech_lx j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let sijk := sij ^^^ mech_xstab_syn k
        let lijk := lij ^^^ mech_lx k
        for l in List.finRange 252 do
          if found || l.val ≤ k.val then continue
          let s := sijk ^^^ mech_xstab_syn l
          let lx := lijk ^^^ mech_lx l
          if s = 0 && lx ≠ 0 then
            found := true
  return found

theorem attack_exists_k4_Z_eq_false : attack_exists_k4_Z = false := by native_decide

/-- Does any K=5 ordered tuple yield a successful Z-attack? -/
def attack_exists_k5_Z : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_xstab_syn i
    let li := mech_lx i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_xstab_syn j
      let lij := li ^^^ mech_lx j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let sijk := sij ^^^ mech_xstab_syn k
        let lijk := lij ^^^ mech_lx k
        for l in List.finRange 252 do
          if found || l.val ≤ k.val then continue
          let sijkl := sijk ^^^ mech_xstab_syn l
          let lijkl := lijk ^^^ mech_lx l
          for m in List.finRange 252 do
            if found || m.val ≤ l.val then continue
            let s := sijkl ^^^ mech_xstab_syn m
            let lx := lijkl ^^^ mech_lx m
            if s = 0 && lx ≠ 0 then
              found := true
  return found

theorem attack_exists_k5_Z_eq_false : attack_exists_k5_Z = false := by native_decide

end QStab.Paper.BB72BVZ
