import QStab.QClifford.Compile.Calculus
import QStab.QHL.CodeLang

/-!
# S3a: the two-program compiler front-end (code-blind generator)

`xzProgramOfPrograms` turns a **code function** together with two **object-language
programs** — an order program `orderProg : Term 3 .nat` and a length program
`lenProg : Term 2 .nat` — into a compiler-facing `XZProgram nQ`.  It is *code-blind*:
its definition mentions only its arguments and the object language / target-program
constructors.  Auditably so — this file imports **nothing surface-specific** (only
`Calculus` and `CodeLang`); the surface re-anchor lives in a downstream file.

The qubit count `nQ` is an explicit parameter, decoupled from the code's distance
parameter `d` (which feeds the object-language evaluation): the surface instantiates
`nQ := d*d`, while e.g. HGP(Rep(d), Rep(d)) needs `nQ := d² + (d-1)²`.

Per stabilizer `k < numStab`:
* the schedule length is the evaluated `lenProg` at `(d, k)`;
* each slot `j < len` places the code's evaluated Pauli-kind at the qubit whose index is
  the evaluated `orderProg` at `(d, k, j)`, totalized into `Fin nQ` by `% nQ`.

The kind is read per-slot from the code (`Pauli.X ↦ .X`, `Pauli.Z ↦ .Z`); the `I`/`Y`/none
default is an arbitrary `.Z` which must be *proved* never to fire in the anchor, not
assumed.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford
open QHL.CodeLang

/-- Read a target `XZPauli` kind from an optional code Pauli.  `X`/`Z` map faithfully; the
`I`/`Y`/`none` fallback (`.Z`) is arbitrary and is proved never to fire in the anchor. -/
def kindOfPauli : Option Pauli → XZPauli
  | some Pauli.X => XZPauli.X
  | some Pauli.Z => XZPauli.Z
  | _ => XZPauli.Z

/-- The generated `RuleSchedule` for stabilizer `k`: `len` slots, each reading its qubit
index from `orderProg` (totalized into `Fin nQ`) and its kind from the code's Pauli at
that qubit.  Code-blind. -/
def genSchedule (code : CodeFn) (orderProg : Term 3 .nat) (lenProg : Term 2 .nat)
    (nQ d k : Nat) : RuleSchedule nQ :=
  let len := (Term.eval code.body (CodeFn.fuelForDistance d) lenProg (Env.code d k)).getD 0
  ⟨if h : 0 < nQ then
      (List.range len).map (fun j =>
        let q := (Term.eval code.body (CodeFn.fuelForDistance d) orderProg
                    (Env.cons j (Env.code d k))).getD 0
        (⟨kindOfPauli (code.evalAt? d k q), ⟨q % nQ, Nat.mod_lt _ h⟩⟩ :
          ScheduledPauli nQ))
    else []⟩

/-- **The two-program compiler front-end.**  Measure every stabilizer `k < numStab` via
the NZ scheme with its generated schedule, in index order.  Code-blind. -/
def xzProgramOfPrograms (code : CodeFn) (orderProg : Term 3 .nat) (lenProg : Term 2 .nat)
    (numStab nQ d : Nat) : XZProgram nQ :=
  (List.range numStab).foldr
    (fun k acc => .seq (.meas .NZ (genSchedule code orderProg lenProg nQ d k)) acc) .skip

end QStab.QClifford.Compile
