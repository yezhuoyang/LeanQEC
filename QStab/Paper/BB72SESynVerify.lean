import QStab.Paper.BB72SESynData

/-!
# BB72 SE X-side static-DEM check via per-SE-mech (Z-syndrome, L_Z parity)

Mirror of `BB72SynVerify` for the SE scheduling. Same structure, same
performance characteristics: K=5 native_decide ≈ 94 min.
-/

namespace QStab.Paper.BB72BVSE

def chain2_se_syn_check (i j : Fin 252) : Bool :=
  let s := mech_se_syn i ^^^ mech_se_syn j
  let lz := mech_se_lz i ^^^ mech_se_lz j
  decide (s = 0) && !decide (lz = 0)

theorem bb_se_chain_2_no_attack_syn :
    ∀ i j : Fin 252, chain2_se_syn_check i j = false := by
  native_decide

def attack_exists_k3_SE : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_se_syn i
    let li := mech_se_lz i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_se_syn j
      let lij := li ^^^ mech_se_lz j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let s := sij ^^^ mech_se_syn k
        let lz := lij ^^^ mech_se_lz k
        if s = 0 && lz ≠ 0 then
          found := true
  return found

theorem attack_exists_k3_SE_eq_false : attack_exists_k3_SE = false := by native_decide

def attack_exists_k4_SE : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_se_syn i
    let li := mech_se_lz i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_se_syn j
      let lij := li ^^^ mech_se_lz j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let sijk := sij ^^^ mech_se_syn k
        let lijk := lij ^^^ mech_se_lz k
        for l in List.finRange 252 do
          if found || l.val ≤ k.val then continue
          let s := sijk ^^^ mech_se_syn l
          let lz := lijk ^^^ mech_se_lz l
          if s = 0 && lz ≠ 0 then
            found := true
  return found

theorem attack_exists_k4_SE_eq_false : attack_exists_k4_SE = false := by native_decide

def attack_exists_k5_SE : Bool := Id.run do
  let mut found := false
  for i in List.finRange 252 do
    if found then return true
    let si := mech_se_syn i
    let li := mech_se_lz i
    for j in List.finRange 252 do
      if found || j.val ≤ i.val then continue
      let sij := si ^^^ mech_se_syn j
      let lij := li ^^^ mech_se_lz j
      for k in List.finRange 252 do
        if found || k.val ≤ j.val then continue
        let sijk := sij ^^^ mech_se_syn k
        let lijk := lij ^^^ mech_se_lz k
        for l in List.finRange 252 do
          if found || l.val ≤ k.val then continue
          let sijkl := sijk ^^^ mech_se_syn l
          let lijkl := lijk ^^^ mech_se_lz l
          for m in List.finRange 252 do
            if found || m.val ≤ l.val then continue
            let s := sijkl ^^^ mech_se_syn m
            let lz := lijkl ^^^ mech_se_lz m
            if s = 0 && lz ≠ 0 then
              found := true
  return found

theorem attack_exists_k5_SE_eq_false : attack_exists_k5_SE = false := by native_decide

end QStab.Paper.BB72BVSE
