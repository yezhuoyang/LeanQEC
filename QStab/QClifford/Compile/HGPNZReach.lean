import QStab.QClifford.Compile.HGPNZFtDistance
import QStab.QClifford.Compile.NZReachCalculus

/-!
# HGP G3 reach: the row-0 attack script (generator + kernel-pinned sanity)

The reach `VCSlot` asks for a fault script such that a clean-start run of
`compileProgram (hgpXZProgram d)` fires exactly `d` faults and lands in a
`failure` state (logical residual, all detectors quiet).

## The design (fixed)

Inject `X` at the **before-`H₁` entry site** of the slot coupling sector-1
qubit `(0,b)` in X-gadget `k = b`, for `b = 0..d-1` — `d` faults, all in the
X-check phase.  The residual is the row-0 `X̄ = mkHGPRepLogicalX`.  Every
detector stays quiet: X-gadgets are blind to pure-X residuals at any timing
(`scheduleParityList_X_uniform`), and every Z-gadget measures after all `d`
injections, seeing the complete `X̄` — even overlap by `hgp_Xbar_comm`.
No dominoes, no stage function, no odd/even split; uniform for all `d ≥ 2`.

Unlike the surface script, `hgpReachScript` is **defined** directly in the
generic `blockScript` form (computable), so no offset-decode lemmas are
needed — the `#eval` pins below validate the same object the proofs consume.

The slot coupling `(0,b)` is slot **0** of gadget `b`'s schedule: the support
list of X-check `k = b` starts `[d*(k/d) + k%d, …] = [b, …]`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric
open QHL QHL.CodeHGPSchedule
open QHL.Source.Examples.HGPUnionSpec

/-- Per-gadget injection pattern: gadget `k < d` (the X-check `(0, k)`)
injects at its slot 0; every other gadget is fault-free. -/
def hgpInjs (d k : Nat) : List Bool :=
  if k < d then
    true :: List.replicate (hgpLenFlat d k - 1) false
  else
    List.replicate (hgpLenFlat d k) false

/-- **The row-0 reach script** for `compileProgram (hgpXZProgram d)`: the
per-gadget `blockScript` segments in measurement (index) order. -/
def hgpReachScript (d : Nat) (hd : 2 ≤ d) : List (Option Pauli) :=
  ((List.finRange (2 * ((d - 1) * d))).map (fun k =>
    blockScript
      (liftSchedule (k := programHelperCount (hgpXZProgram d))
        (hgpSchedule d hd k)).slots
      (hgpInjs d k.val))).flatten

/-! ## Kernel-pinned sanity (design-arithmetic validation, pre-proof) -/

private def pauliBEq : Pauli → Pauli → Bool
  | Pauli.I, Pauli.I => true
  | Pauli.X, Pauli.X => true
  | Pauli.Y, Pauli.Y => true
  | Pauli.Z, Pauli.Z => true
  | _, _ => false

/-- Number of injected (non-`none`) faults in a script. -/
private def reachFaultCount (s : List (Option Pauli)) : Nat :=
  (s.filter (fun o => o.isSome)).length

private def hgpReachRun (d : Nat) (hd : 2 ≤ d) :
    ErrorState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)) × Nat :=
  runFScript (compileProgram (hgpXZProgram d)) (hgpReachScript d hd)
    (ErrorState.clean _)

/-- Data residual matches `mkHGPRepLogicalX`, all detector slots are quiet,
and the fired count is `d` — the full reach obligation, as one Bool. -/
private def hgpReachCheck (d : Nat) (hd : 2 ≤ d) : Bool :=
  ((List.finRange (hgpN d)).all fun q =>
    pauliBEq ((hgpReachRun d hd).1.paulis
        (freshDataQ (d * d + (d - 1) * (d - 1)) (programHelperCount (hgpXZProgram d)) q))
      (mkHGPRepLogicalX d hd q))
  && ((List.range (programDetectorCount (hgpXZProgram d) + 3)).all fun s =>
    !((hgpReachRun d hd).1.detectors s))
  && ((hgpReachRun d hd).2 == d)
  && (reachFaultCount (hgpReachScript d hd) == d)

-- Pins: fault count = `d`, residual = row-0 `X̄`, every detector quiet —
-- both parities, `d = 2, 3, 4, 5`.
/-- info: true -/
#guard_msgs in
#eval hgpReachCheck 2 (by omega)

/-- info: true -/
#guard_msgs in
#eval hgpReachCheck 3 (by omega)

/-- info: true -/
#guard_msgs in
#eval hgpReachCheck 4 (by omega)

/-- info: true -/
#guard_msgs in
#eval hgpReachCheck 5 (by omega)

end QStab.QClifford.Compile
