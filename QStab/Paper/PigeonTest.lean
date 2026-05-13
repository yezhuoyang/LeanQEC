import Std.Tactic.BVDecide.LRAT

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000

open Std.Sat
open Std.Tactic.BVDecide.LRAT

/-- Pigeonhole 3-in-2: 9 clauses, UNSAT. -/
def pigeon_cnf : CNF Nat := ⟨#[
  [(0, true), (1, true)],
  [(2, true), (3, true)],
  [(4, true), (5, true)],
  [(0, false), (2, false)],
  [(0, false), (4, false)],
  [(2, false), (4, false)],
  [(1, false), (3, false)],
  [(1, false), (5, false)],
  [(3, false), (5, false)]
]⟩

def pigeon_lrat_bytes : ByteArray := String.toUTF8 (include_str "pigeon3in2.lrat")
def pigeon_lrat : Array IntAction :=
  match parseLRATProof pigeon_lrat_bytes with
  | .ok a => a
  | .error _ => #[]

#eval pigeon_cnf.clauses.size
#eval pigeon_lrat.size
#eval pigeon_lrat
#eval check pigeon_lrat pigeon_cnf

theorem pigeon_unsat : pigeon_cnf.Unsat := by
  apply check_sound pigeon_lrat pigeon_cnf
  native_decide
