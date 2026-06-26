import QStab.Examples.SurfaceHookErrors

/-! # Functional recursive AST for the parametric Surface-code family

This is the Surface-code syntax layer we want to expose to the proof checker.
The code family is not an entry table and not a bundle of special-purpose row,
column, and logical fields.  It is a tiny functional program whose value type is

  Nat -> Nat -> Stabilizer

where `d` is the distance, `k` is the stabilizer index, and a stabilizer is a
function from qubit index to Pauli.  Logical operators and cuts are derived
stabilizer-valued programs, not primitive fields of the code object.
-/

namespace QHL.Source.Examples.SurfaceRecursiveAST

open QStab
open QStab.Examples.SurfaceParametric

/-- A stabilizer is a Pauli-valued function over natural qubit indices.

The finite `ErrorVec (d*d)` view is derived by restricting this function to
`Fin (d*d)`. -/
abbrev Stabilizer := Nat -> Pauli

def identityStabilizer : Stabilizer := fun _ => Pauli.I

/-- The value types of the functional core.  There is no primitive row, column,
logical-class, cut, or geometry type here. -/
inductive Ty where
  | nat
  | pauli
  | stab

abbrev Ty.denote : Ty -> Type
  | .nat => Nat
  | .pauli => Pauli
  | .stab => Stabilizer

/-- Named natural variables used by the small core.

`d` and `k` are the arguments of a code family. `q` is bound by a stabilizer
lambda. `i` is the local scheduling slot. `g` is used by derived cuts. -/
inductive NatVar where
  | d
  | k
  | q
  | i
  | g
  deriving DecidableEq

structure Env where
  d : Nat
  k : Nat
  q : Nat
  i : Nat
  g : Nat

def Env.code (d k : Nat) : Env :=
  { d := d, k := k, q := 0, i := 0, g := 0 }

def Env.cut (d g : Nat) : Env :=
  { d := d, k := 0, q := 0, i := 0, g := g }

def Env.schedule (d k i : Nat) : Env :=
  { d := d, k := k, q := 0, i := i, g := 0 }

/- Guards are syntax, not first-class values.  This keeps the value language to
Nat, Pauli, and Stabilizer while still giving us if/else. -/
mutual

inductive Cond : Type where
  | natEq : Term .nat -> Term .nat -> Cond
  | natLt : Term .nat -> Term .nat -> Cond
  | and : Cond -> Cond -> Cond
  | or : Cond -> Cond -> Cond
  | not : Cond -> Cond

/-- A tiny OCaml-style expression language for code-family definitions.

`recCall d k` is the generic recursive-code call for a family of type
`Nat -> Nat -> Stabilizer`; `recNatCall d k i` is the matching recursive call
for a schedule family of type `Nat -> Nat -> Nat -> Nat`. Neither constructor
is Surface-specific. -/
inductive Term : Ty -> Type where
  | natVar : NatVar -> Term .nat
  | natLit : Nat -> Term .nat
  | pauliLit : Pauli -> Term .pauli
  | add : Term .nat -> Term .nat -> Term .nat
  | sub : Term .nat -> Term .nat -> Term .nat
  | mul : Term .nat -> Term .nat -> Term .nat
  | div : Term .nat -> Term .nat -> Term .nat
  | mod : Term .nat -> Term .nat -> Term .nat
  | ite : Cond -> Term ty -> Term ty -> Term ty
  | stabLam : Term .pauli -> Term .stab
  | stabAt : Term .stab -> Term .nat -> Term .pauli
  | recCall : Term .nat -> Term .nat -> Term .stab
  | recNatCall : Term .nat -> Term .nat -> Term .nat -> Term .nat

end

mutual

def Term.eval (body : Term .stab) : Nat -> {ty : Ty} -> Term ty -> Env -> ty.denote
  | _, _, .natVar v, rho =>
      match v with
      | .d => rho.d
      | .k => rho.k
      | .q => rho.q
      | .i => rho.i
      | .g => rho.g
  | _, _, .natLit n, _ => n
  | _, _, .pauliLit p, _ => p
  | fuel, _, .add a b, rho =>
      Nat.add (Term.eval body fuel a rho) (Term.eval body fuel b rho)
  | fuel, _, .sub a b, rho =>
      Nat.sub (Term.eval body fuel a rho) (Term.eval body fuel b rho)
  | fuel, _, .mul a b, rho =>
      Nat.mul (Term.eval body fuel a rho) (Term.eval body fuel b rho)
  | fuel, _, .div a b, rho =>
      Nat.div (Term.eval body fuel a rho) (Term.eval body fuel b rho)
  | fuel, _, .mod a b, rho =>
      Nat.mod (Term.eval body fuel a rho) (Term.eval body fuel b rho)
  | fuel, _, .ite c t e, rho =>
      if Cond.eval body fuel c rho then
        Term.eval body fuel t rho
      else
        Term.eval body fuel e rho
  | fuel, _, .stabLam entry, rho =>
      fun q => Term.eval body fuel entry { rho with q := q }
  | fuel, _, .stabAt s q, rho =>
      (Term.eval body fuel s rho) (Term.eval body fuel q rho)
  | 0, _, .recCall _ _, _ =>
      identityStabilizer
  | fuel + 1, _, .recCall d k, rho =>
      Term.eval body fuel body
        { rho with
          d := Term.eval body fuel d rho
          k := Term.eval body fuel k rho }
  | _, _, .recNatCall _ _ _, _ => 0

def Cond.eval (body : Term .stab) : Nat -> Cond -> Env -> Bool
  | fuel, .natEq a b, rho =>
      let av : Nat := Term.eval body fuel a rho
      let bv : Nat := Term.eval body fuel b rho
      decide (av = bv)
  | fuel, .natLt a b, rho =>
      let av : Nat := Term.eval body fuel a rho
      let bv : Nat := Term.eval body fuel b rho
      decide (av < bv)
  | fuel, .and a b, rho =>
      Cond.eval body fuel a rho && Cond.eval body fuel b rho
  | fuel, .or a b, rho =>
      Cond.eval body fuel a rho || Cond.eval body fuel b rho
  | fuel, .not a, rho =>
      !(Cond.eval body fuel a rho)

end

mutual

def Term.evalSchedule (body : Term .nat) :
    Nat -> {ty : Ty} -> Term ty -> Env -> ty.denote
  | _, _, .natVar v, rho =>
      match v with
      | .d => rho.d
      | .k => rho.k
      | .q => rho.q
      | .i => rho.i
      | .g => rho.g
  | _, _, .natLit n, _ => n
  | _, _, .pauliLit p, _ => p
  | fuel, _, .add a b, rho =>
      Nat.add (Term.evalSchedule body fuel a rho) (Term.evalSchedule body fuel b rho)
  | fuel, _, .sub a b, rho =>
      Nat.sub (Term.evalSchedule body fuel a rho) (Term.evalSchedule body fuel b rho)
  | fuel, _, .mul a b, rho =>
      Nat.mul (Term.evalSchedule body fuel a rho) (Term.evalSchedule body fuel b rho)
  | fuel, _, .div a b, rho =>
      Nat.div (Term.evalSchedule body fuel a rho) (Term.evalSchedule body fuel b rho)
  | fuel, _, .mod a b, rho =>
      Nat.mod (Term.evalSchedule body fuel a rho) (Term.evalSchedule body fuel b rho)
  | fuel, _, .ite c t e, rho =>
      if Cond.evalSchedule body fuel c rho then
        Term.evalSchedule body fuel t rho
      else
        Term.evalSchedule body fuel e rho
  | fuel, _, .stabLam entry, rho =>
      fun q => Term.evalSchedule body fuel entry { rho with q := q }
  | fuel, _, .stabAt s q, rho =>
      (Term.evalSchedule body fuel s rho) (Term.evalSchedule body fuel q rho)
  | _, _, .recCall _ _, _ =>
      identityStabilizer
  | 0, _, .recNatCall _ _ _, _ =>
      0
  | fuel + 1, _, .recNatCall d k i, rho =>
      Term.evalSchedule body fuel body
        { rho with
          d := Term.evalSchedule body fuel d rho
          k := Term.evalSchedule body fuel k rho
          i := Term.evalSchedule body fuel i rho }

def Cond.evalSchedule (body : Term .nat) : Nat -> Cond -> Env -> Bool
  | fuel, .natEq a b, rho =>
      let av : Nat := Term.evalSchedule body fuel a rho
      let bv : Nat := Term.evalSchedule body fuel b rho
      decide (av = bv)
  | fuel, .natLt a b, rho =>
      let av : Nat := Term.evalSchedule body fuel a rho
      let bv : Nat := Term.evalSchedule body fuel b rho
      decide (av < bv)
  | fuel, .and a b, rho =>
      Cond.evalSchedule body fuel a rho && Cond.evalSchedule body fuel b rho
  | fuel, .or a b, rho =>
      Cond.evalSchedule body fuel a rho || Cond.evalSchedule body fuel b rho
  | fuel, .not a, rho =>
      !(Cond.evalSchedule body fuel a rho)

end

namespace C

abbrev N := Term .nat
abbrev P := Term .pauli
abbrev S := Term .stab

def d : N := .natVar .d
def k : N := .natVar .k
def q : N := .natVar .q
def i : N := .natVar .i
def g : N := .natVar .g

def n (x : Nat) : N := .natLit x
def p (x : Pauli) : P := .pauliLit x

def zero : N := n 0
def one : N := n 1
def two : N := n 2
def three : N := n 3
def four : N := n 4
def five : N := n 5

def add : N -> N -> N := .add
def sub : N -> N -> N := .sub
def mul : N -> N -> N := .mul
def div : N -> N -> N := .div
def mod : N -> N -> N := .mod

def eq : N -> N -> Cond := .natEq
def lt : N -> N -> Cond := .natLt
def le (a b : N) : Cond := .not (.natLt b a)
def band : Cond -> Cond -> Cond := .and
def bor : Cond -> Cond -> Cond := .or
def bnot : Cond -> Cond := .not

def ite {ty : Ty} (c : Cond) (t e : Term ty) : Term ty := .ite c t e

def and3 (a b c : Cond) : Cond := band a (band b c)
def and4 (a b c d : Cond) : Cond := band a (and3 b c d)

def orEqSucc (x base : N) : Cond :=
  bor (eq x base) (eq x (add base one))

def orEqPair (x a b : N) : Cond :=
  bor (eq x a) (eq x b)

def numStab (d : N) : N :=
  sub (mul d d) one

def gridIdx (d row col : N) : N :=
  add (mul d row) col

end C

namespace SurfaceCodeAST

/-- A generic code-family program with type `Nat -> Nat -> Stabilizer`. -/
structure CodeFn where
  body : Term .stab

abbrev SurfaceFamily := Nat -> Nat -> Stabilizer

def CodeFn.eval (F : CodeFn) (d k : Nat) : Stabilizer :=
  Term.eval F.body (d + 1) F.body (Env.code d k)

def CodeFn.denote (F : CodeFn) : SurfaceFamily :=
  F.eval

/-- A generic stabilizer-measurement schedule.

The schedule is a syntactic function `d -> k -> i -> q`, returning the data
qubit index `q` used by local gate slot `i` of stabilizer `k` at distance `d`.
The Pauli at that slot is derived by applying the code family to the scheduled
qubit. -/
structure ScheduleFn where
  body : Term .nat

abbrev ScheduleFamily := Nat -> Nat -> Nat -> Nat

def ScheduleFn.eval (S : ScheduleFn) (d k i : Nat) : Nat :=
  Term.evalSchedule S.body (d + 1) S.body (Env.schedule d k i)

def ScheduleFn.denote (S : ScheduleFn) : ScheduleFamily :=
  S.eval

structure ScheduledCode where
  code : CodeFn
  schedule : ScheduleFn

def ScheduledCode.scheduledQubit (SC : ScheduledCode) (d k i : Nat) : Nat :=
  SC.schedule.eval d k i

def ScheduledCode.scheduledPauli (SC : ScheduledCode) (d k i : Nat) : Pauli :=
  SC.code.eval d k (SC.scheduledQubit d k i)

/-- The direct local entry formula is used only as the small-distance base
case. The recursive case below calls the family at distance `d-2`. -/
def baseEntry : C.P :=
  let q := C.q
  let d := C.d
  let k := C.k
  let row := C.div q d
  let col := C.mod q d
  let dm1 := C.sub d C.one
  let bulkCount := C.mul dm1 dm1
  let r := C.div k dm1
  let c := C.mod k dm1
  let kind := C.ite (C.eq (C.mod (C.add r c) C.two) C.zero) (C.p Pauli.Z) (C.p Pauli.X)
  let bulk := C.ite (C.and3 (C.orEqSucc row r) (C.orEqSucc col c) (C.lt k bulkCount))
    kind (C.p Pauli.I)
  let b := C.sub k bulkCount
  let half := C.div dm1 C.two
  let topX :=
    C.ite (C.and3 (C.lt k (C.numStab d)) (C.eq row C.zero)
      (C.orEqSucc col (C.mul C.two b))) (C.p Pauli.X) (C.p Pauli.I)
  let bbRight := C.sub b half
  let rightZ :=
    C.ite (C.band (C.eq col dm1)
      (C.orEqSucc row (C.mul C.two bbRight))) (C.p Pauli.Z) (C.p Pauli.I)
  let bbLeft := C.sub b (C.mul C.two half)
  let leftZ :=
    C.ite (C.band (C.eq col C.zero)
      (C.orEqPair row (C.add (C.mul C.two bbLeft) C.one)
        (C.add (C.mul C.two bbLeft) C.two))) (C.p Pauli.Z) (C.p Pauli.I)
  let bbBottom := C.sub b (C.mul C.three half)
  let bottomX :=
    C.ite (C.band (C.eq row dm1)
      (C.orEqPair col (C.add (C.mul C.two bbBottom) C.one)
        (C.add (C.mul C.two bbBottom) C.two))) (C.p Pauli.X) (C.p Pauli.I)
  C.ite (C.lt k bulkCount) bulk
    (C.ite (C.lt b half) topX
      (C.ite (C.lt b (C.mul C.two half)) rightZ
        (C.ite (C.lt b (C.mul C.three half)) leftZ bottomX)))

/-- Direct NZ slot order for the small-distance base case.

This is the same N/Z convention used by `kindOrderRC`: bulk Z checks use
N-order `(NW,SW,NE,SE)`, bulk X checks use Z-order `(NW,NE,SW,SE)`, and
boundary checks use their natural two-qubit order. -/
def baseScheduleSlot : C.N :=
  let d := C.d
  let k := C.k
  let i := C.i
  let dm1 := C.sub d C.one
  let bulkCount := C.mul dm1 dm1
  let r := C.div k dm1
  let c := C.mod k dm1
  let zBulk := C.eq (C.mod (C.add r c) C.two) C.zero
  let slot0 := C.eq i C.zero
  let slot1 := C.eq i C.one
  let slot2 := C.eq i C.two
  let bulkZRow := C.ite (C.bor slot0 slot2) r (C.add r C.one)
  let bulkZCol := C.ite (C.bor slot0 slot1) c (C.add c C.one)
  let bulkXRow := C.ite (C.bor slot0 slot1) r (C.add r C.one)
  let bulkXCol := C.ite (C.bor slot0 slot2) c (C.add c C.one)
  let bulk :=
    C.ite zBulk
      (C.gridIdx d bulkZRow bulkZCol)
      (C.gridIdx d bulkXRow bulkXCol)
  let b := C.sub k bulkCount
  let half := C.div dm1 C.two
  let boundaryBit := C.ite slot0 C.zero C.one
  let topX := C.gridIdx d C.zero (C.add (C.mul C.two b) boundaryBit)
  let bbRight := C.sub b half
  let rightZ := C.gridIdx d (C.add (C.mul C.two bbRight) boundaryBit) dm1
  let bbLeft := C.sub b (C.mul C.two half)
  let leftZ := C.gridIdx d (C.add (C.add (C.mul C.two bbLeft) C.one) boundaryBit) C.zero
  let bbBottom := C.sub b (C.mul C.three half)
  let bottomX :=
    C.gridIdx d dm1 (C.add (C.add (C.mul C.two bbBottom) C.one) boundaryBit)
  C.ite (C.lt k bulkCount) bulk
    (C.ite (C.lt b half) topX
      (C.ite (C.lt b (C.mul C.two half)) rightZ
        (C.ite (C.lt b (C.mul C.three half)) leftZ bottomX)))

/-- Embed a stabilizer from distance `d-2` into the centered subgrid of the
distance-`d` code. -/
def embeddedInnerEntry : C.P :=
  let d := C.d
  let k := C.k
  let q := C.q
  let row := C.div q d
  let col := C.mod q d
  let innerD := C.sub d C.two
  let dm1 := C.sub d C.one
  let inside :=
    C.and4 (C.le C.one row) (C.lt row dm1) (C.le C.one col) (C.lt col dm1)
  let innerQ := C.add (C.mul (C.sub row C.one) innerD) (C.sub col C.one)
  C.ite inside (Term.stabAt (Term.recCall innerD k) innerQ) (C.p Pauli.I)

/-- Evaluate an old stabilizer on the centered `(d-2) × (d-2)` subgrid, and
fall back to a locally generated Pauli on the new outer half of a promoted
boundary check. -/
def promotedBoundaryEntry (oldK : C.N) (outer : Cond) (kind : Pauli) : C.P :=
  let d := C.d
  let q := C.q
  let row := C.div q d
  let col := C.mod q d
  let innerD := C.sub d C.two
  let dm1 := C.sub d C.one
  let inside :=
    C.and4 (C.le C.one row) (C.lt row dm1) (C.le C.one col) (C.lt col dm1)
  let innerQ := C.add (C.mul (C.sub row C.one) innerD) (C.sub col C.one)
  C.ite inside (Term.stabAt (Term.recCall innerD oldK) innerQ)
    (C.ite outer (C.p kind) (C.p Pauli.I))

def centeredScheduledSlot (oldK slot : C.N) : C.N :=
  let d := C.d
  let innerD := C.sub d C.two
  let innerQ := Term.recNatCall innerD oldK slot
  let innerRow := C.div innerQ innerD
  let innerCol := C.mod innerQ innerD
  C.gridIdx d (C.add innerRow C.one) (C.add innerCol C.one)

def twoSlot (slot first second : C.N) : C.N :=
  C.ite (C.eq slot C.zero) first second

def promotedBoundarySlot (oldK outer0 outer1 : C.N) (recurseFirst : Bool) : C.N :=
  let i := C.i
  if recurseFirst then
    C.ite (C.lt i C.two)
      (centeredScheduledSlot oldK i)
      (twoSlot (C.sub i C.two) outer0 outer1)
  else
    C.ite (C.lt i C.two)
      (twoSlot i outer0 outer1)
      (centeredScheduledSlot oldK (C.sub i C.two))

/-- Recursive entry in the same stabilizer-index order as `decodeStabPauliAt`.

For `d ≥ 5`, the direct bulk grid is partitioned into:

* shifted interior bulk checks, generated by a recursive call at `d-2`;
* promoted old boundary checks, generated by a recursive call plus the new
  outer half of the corresponding plaquette;
* newly exposed shell checks, generated locally by `baseEntry`.

The non-bulk boundary checks are also generated locally.  Thus the function is
recursive, but its concrete order remains the canonical direct order already
used by `mkSurfaceStabilizers`. -/
def recursiveEntry : C.P :=
  let d := C.d
  let k := C.k
  let q := C.q
  let row := C.div q d
  let col := C.mod q d
  let dm1 := C.sub d C.one
  let bulkCount := C.mul dm1 dm1
  let r := C.div k dm1
  let c := C.mod k dm1
  let innerD := C.sub d C.two
  let innerDm1 := C.sub innerD C.one
  let innerBulk := C.mul innerDm1 innerDm1
  let innerHalf := C.div innerDm1 C.two
  let lastCell := C.sub dm1 C.one
  let interiorCell :=
    C.and4 (C.le C.one r) (C.lt r lastCell) (C.le C.one c) (C.lt c lastCell)
  let interiorK := C.add (C.mul (C.sub r C.one) innerDm1) (C.sub c C.one)
  let topB := C.div (C.sub c C.one) C.two
  let topCell :=
    C.and3 (C.eq r C.zero) (C.eq c (C.add (C.mul C.two topB) C.one))
      (C.lt topB innerHalf)
  let topOuter :=
    C.band (C.eq row C.zero) (C.orEqSucc col (C.add (C.mul C.two topB) C.one))
  let topK := C.add innerBulk topB
  let rightB := C.div (C.sub r C.one) C.two
  let rightCell :=
    C.and3 (C.eq c lastCell) (C.eq r (C.add (C.mul C.two rightB) C.one))
      (C.lt rightB innerHalf)
  let rightOuter :=
    C.band (C.eq col dm1) (C.orEqSucc row (C.add (C.mul C.two rightB) C.one))
  let rightK := C.add innerBulk (C.add innerHalf rightB)
  let leftB := C.div (C.sub r C.two) C.two
  let leftCell :=
    C.and3 (C.eq c C.zero) (C.eq r (C.add (C.mul C.two leftB) C.two))
      (C.lt leftB innerHalf)
  let leftOuter :=
    C.band (C.eq col C.zero) (C.orEqSucc row (C.add (C.mul C.two leftB) C.two))
  let leftK := C.add innerBulk (C.add (C.mul C.two innerHalf) leftB)
  let bottomB := C.div (C.sub c C.two) C.two
  let bottomCell :=
    C.and3 (C.eq r lastCell) (C.eq c (C.add (C.mul C.two bottomB) C.two))
      (C.lt bottomB innerHalf)
  let bottomOuter :=
    C.band (C.eq row dm1) (C.orEqSucc col (C.add (C.mul C.two bottomB) C.two))
  let bottomK := C.add innerBulk (C.add (C.mul C.three innerHalf) bottomB)
  C.ite (C.lt k bulkCount)
    (C.ite interiorCell
      (C.ite
        (C.and4 (C.le C.one row) (C.lt row dm1) (C.le C.one col) (C.lt col dm1))
        (Term.stabAt (Term.recCall innerD interiorK)
          (C.add (C.mul (C.sub row C.one) innerD) (C.sub col C.one)))
        (C.p Pauli.I))
      (C.ite topCell (promotedBoundaryEntry topK topOuter Pauli.X)
        (C.ite rightCell (promotedBoundaryEntry rightK rightOuter Pauli.Z)
          (C.ite leftCell (promotedBoundaryEntry leftK leftOuter Pauli.Z)
            (C.ite bottomCell (promotedBoundaryEntry bottomK bottomOuter Pauli.X)
              baseEntry)))))
    baseEntry

/-- Recursive NZ schedule in the same stabilizer-index order as
`recursiveEntry`.

For promoted boundary checks, the recursive two-qubit old boundary is spliced
into the four-qubit bulk order at the positions dictated by NZ:

* top and left promotions place the two new outer slots first;
* right and bottom promotions place the recursive inner slots first.

This is exactly the recursive content of the NZ hook geometry: suffix hooks are
computed from this order. -/
def recursiveScheduleSlot : C.N :=
  let d := C.d
  let k := C.k
  let dm1 := C.sub d C.one
  let bulkCount := C.mul dm1 dm1
  let r := C.div k dm1
  let c := C.mod k dm1
  let innerD := C.sub d C.two
  let innerDm1 := C.sub innerD C.one
  let innerBulk := C.mul innerDm1 innerDm1
  let innerHalf := C.div innerDm1 C.two
  let lastCell := C.sub dm1 C.one
  let interiorCell :=
    C.and4 (C.le C.one r) (C.lt r lastCell) (C.le C.one c) (C.lt c lastCell)
  let interiorK := C.add (C.mul (C.sub r C.one) innerDm1) (C.sub c C.one)
  let topB := C.div (C.sub c C.one) C.two
  let topCell :=
    C.and3 (C.eq r C.zero) (C.eq c (C.add (C.mul C.two topB) C.one))
      (C.lt topB innerHalf)
  let topK := C.add innerBulk topB
  let topOuter0 := C.gridIdx d C.zero (C.add (C.mul C.two topB) C.one)
  let topOuter1 := C.gridIdx d C.zero (C.add (C.mul C.two topB) C.two)
  let rightB := C.div (C.sub r C.one) C.two
  let rightCell :=
    C.and3 (C.eq c lastCell) (C.eq r (C.add (C.mul C.two rightB) C.one))
      (C.lt rightB innerHalf)
  let rightK := C.add innerBulk (C.add innerHalf rightB)
  let rightOuter0 := C.gridIdx d (C.add (C.mul C.two rightB) C.one) dm1
  let rightOuter1 := C.gridIdx d (C.add (C.mul C.two rightB) C.two) dm1
  let leftB := C.div (C.sub r C.two) C.two
  let leftCell :=
    C.and3 (C.eq c C.zero) (C.eq r (C.add (C.mul C.two leftB) C.two))
      (C.lt leftB innerHalf)
  let leftK := C.add innerBulk (C.add (C.mul C.two innerHalf) leftB)
  let leftOuter0 := C.gridIdx d (C.add (C.mul C.two leftB) C.two) C.zero
  let leftOuter1 := C.gridIdx d (C.add (C.mul C.two leftB) C.three) C.zero
  let bottomB := C.div (C.sub c C.two) C.two
  let bottomCell :=
    C.and3 (C.eq r lastCell) (C.eq c (C.add (C.mul C.two bottomB) C.two))
      (C.lt bottomB innerHalf)
  let bottomK := C.add innerBulk (C.add (C.mul C.three innerHalf) bottomB)
  let bottomOuter0 := C.gridIdx d dm1 (C.add (C.mul C.two bottomB) C.two)
  let bottomOuter1 := C.gridIdx d dm1 (C.add (C.mul C.two bottomB) C.three)
  C.ite (C.lt k bulkCount)
    (C.ite interiorCell
      (centeredScheduledSlot interiorK C.i)
      (C.ite topCell (promotedBoundarySlot topK topOuter0 topOuter1 false)
        (C.ite rightCell (promotedBoundarySlot rightK rightOuter0 rightOuter1 true)
          (C.ite leftCell (promotedBoundarySlot leftK leftOuter0 leftOuter1 false)
            (C.ite bottomCell
              (promotedBoundarySlot bottomK bottomOuter0 bottomOuter1 true)
              baseScheduleSlot)))))
    baseScheduleSlot

/-- Recursive Surface-code body.

For `d < 5` we use the direct small-distance entry formula.  For larger `d`,
`recursiveEntry` calls the same family at distance `d-2` for the interior and
promoted-boundary pieces, while generating the newly exposed shell locally. -/
def surfaceBody : C.S :=
  let d := C.d
  C.ite (C.lt d C.five)
    (Term.stabLam baseEntry)
    (Term.stabLam recursiveEntry)

def nzScheduleBody : C.N :=
  let d := C.d
  C.ite (C.lt d C.five)
    baseScheduleSlot
    recursiveScheduleSlot

/-- The canonical Surface code as a functional recursive program. -/
def canonical : CodeFn where
  body := surfaceBody

def family : SurfaceFamily :=
  canonical.denote

/-- The canonical NZ stabilizer-measurement schedule as a recursive AST. -/
def nzSchedule : ScheduleFn where
  body := nzScheduleBody

def scheduled : ScheduledCode where
  code := canonical
  schedule := nzSchedule

def eval (d k : Nat) : Stabilizer :=
  canonical.eval d k

def scheduleQubit (d k i : Nat) : Nat :=
  nzSchedule.eval d k i

def scheduledPauli (d k i : Nat) : Pauli :=
  scheduled.scheduledPauli d k i

/-- Derived logical-Z stabilizer. It is not part of the code object. -/
def logicalZTerm : C.S :=
  Term.stabLam <|
    C.ite (C.eq (C.div C.q C.d) C.zero) (C.p Pauli.Z) (C.p Pauli.I)

/-- Derived row cut. It is not part of the code object. -/
def rowCutTerm : C.S :=
  Term.stabLam <|
    C.ite (C.eq (C.div C.q C.d) C.g) (C.p Pauli.Z) (C.p Pauli.I)

/-- Derived column cut. It is not part of the code object. -/
def colCutTerm : C.S :=
  Term.stabLam <|
    C.ite (C.eq (C.mod C.q C.d) C.g) (C.p Pauli.Z) (C.p Pauli.I)

def logicalZ (d : Nat) : Stabilizer :=
  Term.eval surfaceBody (d + 1) logicalZTerm (Env.code d 0)

def rowCut (d g : Nat) : Stabilizer :=
  Term.eval surfaceBody (d + 1) rowCutTerm (Env.cut d g)

def colCut (d g : Nat) : Stabilizer :=
  Term.eval surfaceBody (d + 1) colCutTerm (Env.cut d g)

theorem canonical_body : canonical.body = surfaceBody := rfl

end SurfaceCodeAST

/-- Finite view of the recursive functional code family. -/
def astSurfaceStabilizers (d : Nat) : Fin (numStabFormula d) -> ErrorVec (d * d) :=
  fun k q => SurfaceCodeAST.eval d k.val q.val

/-- Finite view of the derived logical-Z stabilizer. -/
def astSurfaceLogicalZ (d : Nat) : ErrorVec (d * d) :=
  fun q => SurfaceCodeAST.logicalZ d q.val

/-- Finite view of the derived row cut. -/
def astSurfaceRowCut (d : Nat) (g : Fin d) : ErrorVec (d * d) :=
  fun q => SurfaceCodeAST.rowCut d g.val q.val

/-- Finite view of the derived column cut. -/
def astSurfaceColCut (d : Nat) (g : Fin d) : ErrorVec (d * d) :=
  fun q => SurfaceCodeAST.colCut d g.val q.val

/-! ## Concrete d=3 AST expansion

These are not hand-written stabilizers.  `surfaceD3AstRows` is produced by
interpreting `SurfaceCodeAST.canonical` at `d = 3`, then evaluating every
stabilizer index and every data-qubit index.
-/

def surfaceD3AstRows : List (List Pauli) :=
  (List.finRange (numStabFormula 3)).map fun k =>
    (List.finRange 9).map fun q => SurfaceCodeAST.eval 3 k.val q.val

def surfaceD3MkRows : List (List Pauli) :=
  (List.finRange (numStabFormula 3)).map fun k =>
    (List.finRange 9).map fun q => mkSurfaceStabilizers 3 (by decide) k q

def pauliChar : Pauli -> String
  | Pauli.I => "I"
  | Pauli.X => "X"
  | Pauli.Y => "Y"
  | Pauli.Z => "Z"

def joinStrings (xs : List String) : String :=
  xs.foldr (fun s acc => s ++ acc) ""

def surfaceAstRowString (d k : Nat) : String :=
  joinStrings ((List.finRange (d * d)).map fun q => pauliChar (SurfaceCodeAST.eval d k q.val))

def surfaceMkRowString (d : Nat) (hd : 0 < d) (k : Fin (numStabFormula d)) : String :=
  joinStrings ((List.finRange (d * d)).map fun q => pauliChar (mkSurfaceStabilizers d hd k q))

def surfaceAstRowsString (d : Nat) : List String :=
  (List.finRange (numStabFormula d)).map fun k => surfaceAstRowString d k.val

def surfaceMkRowsString (d : Nat) (hd : 0 < d) : List String :=
  (List.finRange (numStabFormula d)).map fun k => surfaceMkRowString d hd k

def surfaceD4AstRowsString : List String :=
  surfaceAstRowsString 4

def surfaceD4MkRowsString : List String :=
  surfaceMkRowsString 4 (by decide)

def surfaceD5AstRowsString : List String :=
  surfaceAstRowsString 5

def surfaceD5MkRowsString : List String :=
  surfaceMkRowsString 5 (by decide)

def surfaceNZScheduleSlots (d : Nat) : List (List Nat) :=
  (List.finRange (numStabFormula d)).map fun k =>
    (List.range ((kindOrderRC d (classifyStab d k.val)).length)).map fun i =>
      SurfaceCodeAST.scheduleQubit d k.val i

def surfaceNZKindOrderSlots (d : Nat) : List (List Nat) :=
  (List.finRange (numStabFormula d)).map fun k =>
    (kindOrderRC d (classifyStab d k.val)).map fun rc => gridIdx d rc.1 rc.2

def surfaceD3NZScheduleSlots : List (List Nat) :=
  surfaceNZScheduleSlots 3

def surfaceD3NZScheduledPaulis : List (List Pauli) :=
  (List.finRange (numStabFormula 3)).map fun k =>
    (List.range ((kindOrderRC 3 (classifyStab 3 k.val)).length)).map fun i =>
      SurfaceCodeAST.scheduledPauli 3 k.val i

/--
info: [[Pauli.Z, Pauli.Z, Pauli.I, Pauli.Z, Pauli.Z, Pauli.I, Pauli.I, Pauli.I, Pauli.I],
 [Pauli.I, Pauli.X, Pauli.X, Pauli.I, Pauli.X, Pauli.X, Pauli.I, Pauli.I, Pauli.I],
 [Pauli.I, Pauli.I, Pauli.I, Pauli.X, Pauli.X, Pauli.I, Pauli.X, Pauli.X, Pauli.I],
 [Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.Z, Pauli.Z, Pauli.I, Pauli.Z, Pauli.Z],
 [Pauli.X, Pauli.X, Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.I],
 [Pauli.I, Pauli.I, Pauli.Z, Pauli.I, Pauli.I, Pauli.Z, Pauli.I, Pauli.I, Pauli.I],
 [Pauli.I, Pauli.I, Pauli.I, Pauli.Z, Pauli.I, Pauli.I, Pauli.Z, Pauli.I, Pauli.I],
 [Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.X, Pauli.X]]
-/
#guard_msgs in
#eval surfaceD3AstRows

/-- info: true -/
#guard_msgs in
#eval surfaceD3AstRows == surfaceD3MkRows

/--
info: ["ZZIIZZIIIIIIIIII", "IXXIIXXIIIIIIIII", "IIZZIIZZIIIIIIII", "IIIIXXIIXXIIIIII", "IIIIIZZIIZZIIIII", "IIIIIIXXIIXXIIII",
  "IIIIIIIIZZIIZZII", "IIIIIIIIIXXIIXXI", "IIIIIIIIIIZZIIZZ", "XXIIIIIIIIIIIIII", "IIIZIIIZIIIIIIII",
  "IIIIZIIIZIIIIIII", "IIIIIIIIIIIIIXXI", "IIIIIIIIIIIIIIIX", "IIIIIIIIIIIIIIII"]
-/
#guard_msgs in
#eval surfaceD4AstRowsString

/-- info: true -/
#guard_msgs in
#eval surfaceD4AstRowsString == surfaceD4MkRowsString

/--
info: ["ZZIIIZZIIIIIIIIIIIIIIIIII", "IXXIIIXXIIIIIIIIIIIIIIIII", "IIZZIIIZZIIIIIIIIIIIIIIII", "IIIXXIIIXXIIIIIIIIIIIIIII",
  "IIIIIXXIIIXXIIIIIIIIIIIII", "IIIIIIZZIIIZZIIIIIIIIIIII", "IIIIIIIXXIIIXXIIIIIIIIIII", "IIIIIIIIZZIIIZZIIIIIIIIII",
  "IIIIIIIIIIZZIIIZZIIIIIIII", "IIIIIIIIIIIXXIIIXXIIIIIII", "IIIIIIIIIIIIZZIIIZZIIIIII", "IIIIIIIIIIIIIXXIIIXXIIIII",
  "IIIIIIIIIIIIIIIXXIIIXXIII", "IIIIIIIIIIIIIIIIZZIIIZZII", "IIIIIIIIIIIIIIIIIXXIIIXXI", "IIIIIIIIIIIIIIIIIIZZIIIZZ",
  "XXIIIIIIIIIIIIIIIIIIIIIII", "IIXXIIIIIIIIIIIIIIIIIIIII", "IIIIZIIIIZIIIIIIIIIIIIIII", "IIIIIIIIIIIIIIZIIIIZIIIII",
  "IIIIIZIIIIZIIIIIIIIIIIIII", "IIIIIIIIIIIIIIIZIIIIZIIII", "IIIIIIIIIIIIIIIIIIIIIXXII", "IIIIIIIIIIIIIIIIIIIIIIIXX"]
-/
#guard_msgs in
#eval surfaceD5AstRowsString

/-- info: true -/
#guard_msgs in
#eval surfaceD5AstRowsString == surfaceD5MkRowsString

/--
info: [[0, 3, 1, 4], [1, 2, 4, 5], [3, 4, 6, 7], [4, 7, 5, 8], [0, 1], [2, 5], [3, 6], [7, 8]]
-/
#guard_msgs in
#eval surfaceD3NZScheduleSlots

/--
info: [[Pauli.Z, Pauli.Z, Pauli.Z, Pauli.Z],
 [Pauli.X, Pauli.X, Pauli.X, Pauli.X],
 [Pauli.X, Pauli.X, Pauli.X, Pauli.X],
 [Pauli.Z, Pauli.Z, Pauli.Z, Pauli.Z],
 [Pauli.X, Pauli.X],
 [Pauli.Z, Pauli.Z],
 [Pauli.Z, Pauli.Z],
 [Pauli.X, Pauli.X]]
-/
#guard_msgs in
#eval surfaceD3NZScheduledPaulis

/-- info: true -/
#guard_msgs in
#eval surfaceNZScheduleSlots 3 == surfaceNZKindOrderSlots 3

/-- info: true -/
#guard_msgs in
#eval surfaceNZScheduleSlots 5 == surfaceNZKindOrderSlots 5

/-- info: true -/
#guard_msgs in
#eval surfaceNZScheduleSlots 7 == surfaceNZKindOrderSlots 7

example : SurfaceCodeAST.canonical.body = SurfaceCodeAST.surfaceBody := rfl

#print axioms SurfaceCodeAST.canonical
#print axioms SurfaceCodeAST.canonical_body

end QHL.Source.Examples.SurfaceRecursiveAST
