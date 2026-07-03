import QStab.QClifford.Compile.HGPNZProgram

/-!
# The Shor-extraction HGP object program

`hgpShorProgram d` is the `.Shor` analog of `hgpXZProgram d`: the same
code-blind generator over the same `HGP.code` anchor and reference schedules,
but each stabilizer measured by the Shor cat-verifier scheme instead of NZ.
The program-level anchor `hgpShorProgram_eq_foldr` reuses the certified
per-check equality `genSchedule_eq_hgpSchedule` (scheme-independent), so the
Shor pipeline hangs off the same object-language certificate as the NZ one.
-/

namespace QStab.QClifford.Compile

open QHL QHL.CodeHGPSchedule

/-- The Shor-extraction compiled-source program for HGP(Rep(d),Rep(d)). -/
def hgpShorProgram (d : Nat) : XZProgram (d * d + (d - 1) * (d - 1)) :=
  (List.range (2 * ((d - 1) * d))).foldr
    (fun k acc => .seq (.meas .Shor
      (genSchedule QHL.CodeLang.HGP.code hgpOrderProg hgpLenProg
        (d * d + (d - 1) * (d - 1)) d k)) acc) .skip

private theorem range_eq_finRange_map' (n : Nat) :
    List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2; simp

/-- **Program-level anchor**: `hgpShorProgram d` is the fold of the reference
schedules, one `.meas .Shor` per generator in index order. -/
theorem hgpShorProgram_eq_foldr (d : Nat) (hd : 2 ≤ d) :
    hgpShorProgram d = (List.finRange (2 * ((d - 1) * d))).foldr
      (fun i acc => .seq (.meas .Shor (hgpSchedule d hd i)) acc) .skip := by
  unfold hgpShorProgram
  rw [range_eq_finRange_map', List.foldr_map]
  congr 1
  funext i acc
  rw [genSchedule_eq_hgpSchedule d hd i]

/-- info: 'QStab.QClifford.Compile.hgpShorProgram' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hgpShorProgram

/--
info: 'QStab.QClifford.Compile.hgpShorProgram_eq_foldr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpShorProgram_eq_foldr

end QStab.QClifford.Compile
