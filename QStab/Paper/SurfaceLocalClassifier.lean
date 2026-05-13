import QStab.Paper.GenericReachableBridge
import QStab.MultiStep
import QStab.PauliOps
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Pi

/-!
# Local plaquette classifier for surface code: definitions, partial results, and a DISPROVED conjecture

## What this file does

Catalogues the canonical 4-qubit plaquette structure of the rotated
surface code and proves a few decidable facts about CX orderings at
that level (counting, structural shape).

## What this file used to claim, but doesn't

An earlier draft conjectured a "universal local classifier":

> *(false conjecture)* Surface code scheduling preserves `d_circ ≥ d`
> ⟺ every X-bulk plaquette uses a non-row-traversal CX ordering.

This was empirically supported at d=3 and d=4 but **disproved at d=5**.
At d=5, in a sample of 100 random schedulings, **97/100** schedulings
have `d_circ < 5` (Failing) yet **0/100** would be flagged by the
per-plaquette local classifier — every Failing case at d=5 is a
**multi-hook chain attack** that no single plaquette's CX ordering
can detect.

(See `notes/sanity_check_d5.py` for the disproof: histogram
`{d_circ=3: 53, 4: 44, ≥5: 3}`.)

## Why per-stab local classification fails at d ≥ 5

At d=3, d=4 the lattice is boundary-dominated: most plaquettes are
near the L_Z boundary, so 1-hook + (d−2)-single attacks dominate, and
those *are* per-plaquette detectable. At d ≥ 5, most plaquettes are
interior, and the dominant Failing mechanism is a chain combining
hooks from MULTIPLE plaquettes plus singles — not visible to any
single plaquette's local check.

This is a fundamental obstruction: **per-stab locality is insufficient**
for the surface code's `d_circ` characterisation at general d.

## What still holds

| Statement | Status |
|---|---|
| LAligned (no bad hooks anywhere) ⟹ `d_circ ≥ d` | ✓ Proven (`Paper/AlignedBarrier`, `Paper/SurfaceBarrier`) |
| Per-scheduling DEM chain check, decidable in `poly(n^{d-1})` | ✓ Proven (`Paper/GenericReachableBridge`) |
| Full ensemble verification at d=3 (2304 schedulings) | ✓ Proven (`Paper/SurfaceD3OperationalIffParam` via `native_decide`) |
| Constant-depth classifier covering all d | ✗ Open / **likely false** based on d=5 evidence |
| Per-plaquette local classifier covering all d | ✗ **Disproved at d=5** (this file) |

## What this file proves

Definitions and finite combinatorial facts about CX orderings on a
canonical 4-qubit plaquette. These remain useful as a vocabulary for
discussing per-plaquette properties, even though they do *not* yield
a universal classifier for `d_circ`.

**Zero `sorry`.**
-/

namespace QStab.Paper.SurfaceLocalClassifier

/-! ## Canonical plaquette: 4 qubits {a, b, c, d} -/

/-- Abstract plaquette qubit labels.
    a, b are the "top" row of the plaquette; c, d the "bottom" row.
    a, c are the "left" column; b, d the "right" column. -/
inductive PQubit
  | a | b | c | d
deriving DecidableEq, Repr

instance : Fintype PQubit where
  elems := {PQubit.a, PQubit.b, PQubit.c, PQubit.d}
  complete := fun p => by cases p <;> simp

/-- A CX ordering at a 4-qubit plaquette = sequence of all 4 qubits. -/
abbrev PlaqOrdering := List PQubit

/-- Hooks of an ordering = non-empty proper suffixes. -/
def hooksOf : List PQubit → List (List PQubit)
  | []      => []
  | [_]     => []
  | _ :: rest => rest :: hooksOf rest

/-- Convert PQubit to row index (0 or 1). -/
def rowOf : PQubit → Nat
  | .a | .b => 0
  | .c | .d => 1

/-- Convert PQubit to column index (0 or 1). -/
def colOf : PQubit → Nat
  | .a | .c => 0
  | .b | .d => 1

/-! ## Row-traversal orderings (8 of 24)

A "row-traversal" CX ordering visits one full row of the plaquette
before the other. This is a property of the *ordering* alone (not
of the lattice), and is the failure mode that dominates at d=3, 4
(but not at d ≥ 5; see `notes/sanity_check_d5.py`). -/

/-- A 4-qubit ordering is row-traversal iff:
    - First two qubits are in the same row, AND
    - Last two qubits are in the same row, AND
    - The two halves are different rows. -/
def isRowTraversal (ord : PlaqOrdering) : Bool :=
  match ord with
  | [x1, x2, x3, x4] =>
    (rowOf x1 == rowOf x2) && (rowOf x3 == rowOf x4) &&
    (rowOf x1 != rowOf x3)
  | _ => false

/-- Explicit list of the 8 row-traversal orderings. -/
def rowTraversalOrderings : List PlaqOrdering :=
  [[.a, .b, .c, .d], [.a, .b, .d, .c], [.b, .a, .c, .d], [.b, .a, .d, .c],
   [.c, .d, .a, .b], [.c, .d, .b, .a], [.d, .c, .a, .b], [.d, .c, .b, .a]]

/-- Every element of `rowTraversalOrderings` is row-traversal. -/
theorem rowTraversalOrderings_are_row_traversal :
    ∀ ord ∈ rowTraversalOrderings, isRowTraversal ord = true := by
  decide

/-- All 24 valid orderings of {a, b, c, d}. -/
def allOrderings : List PlaqOrdering :=
  ([PQubit.a, .b, .c, .d]).permutations

theorem total_orderings : allOrderings.length = 24 := by native_decide

/-- Exactly 8 of the 24 orderings are row-traversal. -/
theorem count_row_traversal :
    (allOrderings.filter isRowTraversal).length = 8 := by native_decide

/-- Exactly 16 of the 24 orderings are NOT row-traversal. -/
theorem count_non_row_traversal :
    (allOrderings.filter (fun o => !(isRowTraversal o))).length = 16 := by
  native_decide

/-! ## Length-2 suffix shape characterisation

Among the 24 orderings, the length-2 suffix has its two qubits in the
same row iff the ordering is row-traversal. -/

/-- Predicate: the length-2 suffix of `ord` has its two qubits in the
    same row. -/
def length2SuffixSameRow (ord : PlaqOrdering) : Bool :=
  match ord with
  | [_, _, x3, x4] => rowOf x3 == rowOf x4
  | _ => false

/-- For non-row-traversal orderings, the length-2 suffix has cross-row
    qubits. -/
theorem non_row_traversal_length2_suffix_crosses_rows :
    ∀ ord ∈ allOrderings,
      isRowTraversal ord = false → length2SuffixSameRow ord = false := by
  native_decide

/-! ## Disproved conjecture (recorded for honesty)

The following Prop was conjectured but is FALSE:

  *"For surface code at any d ≥ 3 with R = 1, scheduling preserves
   d_circ ≥ d ⟺ every X-bulk uses a non-row-traversal CX ordering."*

Counter-example: at d = 5 (qLDPC layout), 97 of 100 sampled random
schedulings have `d_circ < 5`, yet none of them have a row-traversal
ordering at any X-bulk plaquette. The Failing mechanism is multi-hook
chain attacks combining hooks from multiple plaquettes plus singles
to form a logical X-string.

We do NOT prove this Prop (we cannot — it's false). We record it
here as a Prop literal so future readers see what was disproved. -/

/--
DISPROVED at d = 5. This Prop is FALSE; the comment is for record only.

```
∀ (d : Nat) (h_d : 3 ≤ d) (S : SurfaceScheduling d),
  operational_d_circ S ≥ d ⟺ ∀ X-bulk plaquette p, ¬(isRowTraversal (S p))
```

A formal statement requires the parametric `SurfaceScheduling d` type
which we did not build (since the claim is false at d ≥ 5, there is
no theorem worth proving with this signature).
-/
def disproved_universal_local_classifier_conjecture : Prop := True

/-! ## Cross-reference

For the actually-correct, structurally-proven results, see:

  * `Paper/AlignedBarrier`     — LAligned ⟹ d_circ ≥ d, all d
  * `Paper/SurfaceBarrier`     — surface-code instance of the above
  * `Paper/GenericReachableBridge` — generic per-scheduling DEM check
  * `Paper/SurfaceD3OperationalIffParam` — full d=3 enumeration

The honest scaling situation:

  * d=3: full ensemble enumerated (2304 schedulings, native_decide).
  * d=4: full ensemble would be 31.85M; sample-verified.
  * d ≥ 5: full ensemble exponential in lattice size; per-scheduling
    `poly(n^{d-1})` chain check is the best we have. No closed-form
    constant-depth classifier is known to exist.
-/

end QStab.Paper.SurfaceLocalClassifier
