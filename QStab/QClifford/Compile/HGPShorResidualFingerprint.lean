import QStab.QClifford.Compile.HGPShorProgram
import QStab.QClifford.Compile.HGPNZSafe
import QStab.Examples.HGPParametric

/-!
# Shor compiled-residual fingerprint: the bridge-reuse pin (executable, guarded)

**Confirmation, not construction.**  This file pins the decisive fact that lets
the Shor-extraction HGP program reuse the *unchanged* compiled-distance bridge —
the same `etildeC_hoare_preservation` / `hFold_of_valid` / `compiled_barrier_distance`
that the NZ family goes through, over the same scheme-independent union source
machine `exactUnionHGPSpec`.

`hFold_of_valid` (ETildeCSimulation.lean) consumes an **unconditional** validity
premise: *every* fault site of the compiled circuit must have a data residual of
weight `≤ 1`, or one that is pointwise dominated by a single generator (a member
of the union back-action set), with **no** post-selection restriction.  The open
question for Shor was whether its cat-verifier gadgets break this — i.e. whether
some fault produces a weight-`≥ 2` residual dominated by *no* generator, which
the unconditional bridge could not classify.

The enumeration below answers it at `d = 3`: over all `312` errLoc sites ×
`{X,Y,Z}`, the `56` residuals of weight `≥ 2` are **all** dominated by a single
generator, and **zero** weight-`≥ 2` residuals are undominated.  Every remaining fault has a
data residual of weight `≤ 1`.  (`s.suffix` is the fault-free remainder of the
*entire* circuit, so these are the *final* residuals — tail propagation through
the later gadgets is already included.)

**Consequences (the finding).**
* No bridge or slot-spec widening is needed: the unconditional
  `HGPHValid`-shaped obligation is satisfiable for the Shor circuit.
* The post-selection restriction anticipated for a "surviving-faults-only"
  back-action set is **unnecessary for the bar-Z floor**: every fault —
  including the flag-firing ones — already classifies as weight `≤ 1` or
  dominated by a single generator, so no fault needs discarding.
* Hence `HGPShorHValid` will have the *identical* unconditional shape as
  `HGPHValid`, and `hgpShor_compiled_barZ_distance` consumes the bridge verbatim.

This is a `d = 3` executable fingerprint, guarded by `#guard_msgs` (checked by
the elaborator's evaluator on every build — not a kernel-reduced proof); the
parametric `∀ d ≥ 2` discharge is the clean-cat `PreservesDataAbove` preserver +
`shor_gadget_site_classified` classification + the `hgp_hvalid`-mirroring
assembly.  It supersedes the plan's post-selection-surviving back-action set.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric

/-- Structural `Pauli` equality as a `Bool` (runtime reflection, not a tactic). -/
private def pEq : Pauli → Pauli → Bool
  | .I, .I => true | .X, .X => true | .Y, .Y => true | .Z, .Z => true
  | _, _ => false

private def nData : Nat := hgpN 3
private def nHelp : Nat := programHelperCount (hgpShorProgram 3)

/-- The compiled Shor-extraction HGP circuit at `d = 3`. -/
private def shorC : FCircuit (nData + nHelp) := compileProgram (hgpShorProgram 3)

/-- Final data residual (function form) of injecting `p` at fault site `s`:
propagate the site's fault-free suffix (rest of the whole circuit) from a
clean-at-detector state and read the data block. -/
private def residFn (s : ErrLocWithContext (nData + nHelp)) (p : Pauli) : Fin nData → Pauli :=
  fun q =>
    (propagateCircuit s.suffix ((cleanAtDetector s.detectorStart).inject s.q p)).paulis
      (freshDataQ nData nHelp q)

/-- Data weight (number of non-`I` positions) of a residual. -/
private def wt (f : Fin nData → Pauli) : Nat :=
  (List.finRange nData).countP (fun q => !pEq (f q) .I)

/-- `f` is pointwise dominated by some single HGP generator `k`. -/
private def dom (f : Fin nData → Pauli) : Bool :=
  (List.range (hgpNumStab 3)).any (fun k =>
    (List.finRange nData).all (fun q => pEq (f q) .I || pEq (f q) (stabEntry 3 k q.val)))

/-- The dominated-flags of every weight-`≥ 2` residual across all sites × `{X,Y,Z}`. -/
private def weight2Doms : List Bool :=
  (errLocsWithContext shorC).flatMap (fun s =>
    [Pauli.X, Pauli.Y, Pauli.Z].filterMap (fun p =>
      let f := residFn s p
      if 2 ≤ wt f then some (dom f) else none))

-- PIN 1: the compiled `d = 3` Shor circuit has exactly `312` fault sites.
/-- info: 312 -/
#guard_msgs in
#eval (errLocsWithContext shorC).length

-- PIN 2: `(number of weight-≥2 residuals, number of them NOT dominated)`.
-- `0` undominated is the whole point: the unconditional obligation holds.
/-- info: (56, 0) -/
#guard_msgs in
#eval (weight2Doms.length, weight2Doms.countP (fun b => !b))

-- NEGATIVE CONTROLS: `dom` discriminates — it rejects non-hooks, accepts
-- exactly generator-dominated vectors.  Guards PIN 2 against a vacuous checker.
/-- info: (false, false, true, true) -/
#guard_msgs in
#eval (dom (fun _ => Pauli.Z),
       dom (fun q => if q.val = 0 || q.val = 1 then Pauli.X else Pauli.I),
       dom (fun _ => Pauli.I),
       dom (fun q => stabEntry 3 0 q.val))

end QStab.QClifford.Compile
