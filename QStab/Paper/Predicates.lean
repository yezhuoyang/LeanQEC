import QStab.PauliOps
import QStab.State
import QStab.Examples.SurfaceParametric
import QStab.Examples.SurfaceGeometry
import QStab.Paper.BarrierFramework

/-!
# Abstract semantic predicates (paper §3 / §6.5)

This file consolidates the abstract semantic predicates that appear
across the QStab paper and Lean formalisation. Each predicate is a
single Prop-valued definition; for every predicate we provide a
one-line `Iff.rfl` (or `rfl`) unfolding lemma so downstream proofs can
rewrite by name rather than re-`unfold`ing.

Predicate groups:

* **Row/column X/Z restriction** — single-coordinate localisation of
  the X- (resp. Z-) component of an error.
* **Stabilizer-localised** restriction predicates specialised to the
  parametric rotated surface code via `mkSurfaceStabilizers`.
* **Hook alignment** — existence of *some* row (resp. column) restricting
  the X- (resp. Z-) component (the predicate consumed by the back-action
  barrier).
* **Syndrome predicates** — same-syndrome and zero-syndrome (used by the
  `clean` premise of `record_aware_distance_preservation`).
* **Budget** — `s.C + t ≤ P.C_budget`, the safety side of the fault
  bound.
* **Barrier abbreviation** — `BarrierBeta β s := β.mu s.E_tilde`, a
  convenience wrapper of `Phi μ` minus the `(C_budget − C)` slack.
* **Touches-every-row/column** — the topological lower-bound predicate
  driving `projRowsX = d` / `projColsZ = d` arguments.

All definitions are total functions; all unfolding lemmas are
`Iff.rfl` or `rfl`. No `sorry`, no `native_decide`, no
`Classical.choose`, no `Exists.choose`, no `by_contra`.
-/

namespace QStab.Paper.Predicates

open QStab.Examples
open QStab.Paper.BarrierFramework

/-! ## Row / column restriction predicates -/

/-- `RowRestrictedX E i` : the X-component of `E` is supported only in
    row `i` of the `d × d` surface grid. Every cell outside row `i`
    has zero X-component. -/
def RowRestrictedX {d : Nat} (E : ErrorVec (d * d)) (i : Fin d) : Prop :=
  ∀ (i' : Fin d) (j : Fin d), i' ≠ i →
    Pauli.hasXComponent (E (toIdx d i' j)) = false

/-- Unfolding lemma for `RowRestrictedX`. -/
theorem RowRestrictedX_iff {d : Nat} (E : ErrorVec (d * d)) (i : Fin d) :
    RowRestrictedX E i ↔
      ∀ (i' : Fin d) (j : Fin d), i' ≠ i →
        Pauli.hasXComponent (E (toIdx d i' j)) = false :=
  Iff.rfl

/-- `ColRestrictedZ E j` : the Z-component of `E` is supported only in
    column `j` of the `d × d` surface grid. -/
def ColRestrictedZ {d : Nat} (E : ErrorVec (d * d)) (j : Fin d) : Prop :=
  ∀ (i : Fin d) (j' : Fin d), j' ≠ j →
    Pauli.hasZComponent (E (toIdx d i j')) = false

/-- Unfolding lemma for `ColRestrictedZ`. -/
theorem ColRestrictedZ_iff {d : Nat} (E : ErrorVec (d * d)) (j : Fin d) :
    ColRestrictedZ E j ↔
      ∀ (i : Fin d) (j' : Fin d), j' ≠ j →
        Pauli.hasZComponent (E (toIdx d i j')) = false :=
  Iff.rfl

/-! ## Stabilizer-localised restriction predicates

These specialise the row/column restriction predicates to the parametric
rotated-surface stabilizer family `mkSurfaceStabilizers d hd s`. -/

/-- The X-component of the parametric stabilizer indexed by `s` is
    confined to row `i`. -/
def StabRowLocalizedX (d : Nat) (hd : 0 < d)
    (s : Fin (QStab.Examples.SurfaceParametric.numStabFormula d))
    (i : Fin d) : Prop :=
  RowRestrictedX (QStab.Examples.SurfaceParametric.mkSurfaceStabilizers d hd s) i

/-- Unfolding lemma for `StabRowLocalizedX`. -/
theorem StabRowLocalizedX_iff (d : Nat) (hd : 0 < d)
    (s : Fin (QStab.Examples.SurfaceParametric.numStabFormula d))
    (i : Fin d) :
    StabRowLocalizedX d hd s i ↔
      RowRestrictedX (QStab.Examples.SurfaceParametric.mkSurfaceStabilizers d hd s) i :=
  Iff.rfl

/-- The Z-component of the parametric stabilizer indexed by `s` is
    confined to column `j`. -/
def StabColLocalizedZ (d : Nat) (hd : 0 < d)
    (s : Fin (QStab.Examples.SurfaceParametric.numStabFormula d))
    (j : Fin d) : Prop :=
  ColRestrictedZ (QStab.Examples.SurfaceParametric.mkSurfaceStabilizers d hd s) j

/-- Unfolding lemma for `StabColLocalizedZ`. -/
theorem StabColLocalizedZ_iff (d : Nat) (hd : 0 < d)
    (s : Fin (QStab.Examples.SurfaceParametric.numStabFormula d))
    (j : Fin d) :
    StabColLocalizedZ d hd s j ↔
      ColRestrictedZ (QStab.Examples.SurfaceParametric.mkSurfaceStabilizers d hd s) j :=
  Iff.rfl

/-! ## Hook alignment predicates

`HookAlignedX e_B` says *some* row contains the entire X-support of
`e_B`; symmetrically for `HookAlignedZ`. These are the existential
forms consumed by the back-action barrier argument. -/

/-- `HookAlignedX e_B` : there exists a row `i` such that every
    X-component of `e_B` lies in row `i`. -/
def HookAlignedX {d : Nat} (e_B : ErrorVec (d * d)) : Prop :=
  ∃ i : Fin d, RowRestrictedX e_B i

/-- Unfolding lemma for `HookAlignedX`. -/
theorem HookAlignedX_iff {d : Nat} (e_B : ErrorVec (d * d)) :
    HookAlignedX e_B ↔ ∃ i : Fin d, RowRestrictedX e_B i :=
  Iff.rfl

/-- `HookAlignedZ e_B` : there exists a column `j` such that every
    Z-component of `e_B` lies in column `j`. -/
def HookAlignedZ {d : Nat} (e_B : ErrorVec (d * d)) : Prop :=
  ∃ j : Fin d, ColRestrictedZ e_B j

/-- Unfolding lemma for `HookAlignedZ`. -/
theorem HookAlignedZ_iff {d : Nat} (e_B : ErrorVec (d * d)) :
    HookAlignedZ e_B ↔ ∃ j : Fin d, ColRestrictedZ e_B j :=
  Iff.rfl

/-! ## Syndrome predicates -/

/-- `SameSyndrome P E F` : every stabilizer of `P` yields the same parity
    bit on `E` and `F`. Equivalently, `E` and `F` differ by a normaliser
    element. -/
def SameSyndrome (P : QECParams) (E F : ErrorVec P.n) : Prop :=
  ∀ i : Fin P.numStab,
    ErrorVec.parity (P.stabilizers i) E = ErrorVec.parity (P.stabilizers i) F

/-- Unfolding lemma for `SameSyndrome`. -/
theorem SameSyndrome_iff (P : QECParams) (E F : ErrorVec P.n) :
    SameSyndrome P E F ↔
      ∀ i : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) E = ErrorVec.parity (P.stabilizers i) F :=
  Iff.rfl

/-- `SyndromeCorrect P s` : the classical syndrome register `s.G` is
    identically `false` (clean syndrome at the done state). -/
def SyndromeCorrect (P : QECParams) (s : QStab.State P) : Prop :=
  ∀ x y, s.G x y = false

/-- Unfolding lemma for `SyndromeCorrect`. -/
theorem SyndromeCorrect_iff (P : QECParams) (s : QStab.State P) :
    SyndromeCorrect P s ↔ ∀ x y, s.G x y = false :=
  Iff.rfl

/-! ## Budget predicate -/

/-- `FaultBudget P s t` : there is room for `t` more faults from the
    current state without exceeding `P.C_budget`. -/
def FaultBudget (P : QECParams) (s : QStab.State P) (t : Nat) : Prop :=
  s.C + t ≤ P.C_budget

/-- Unfolding lemma for `FaultBudget`. -/
theorem FaultBudget_iff (P : QECParams) (s : QStab.State P) (t : Nat) :
    FaultBudget P s t ↔ s.C + t ≤ P.C_budget :=
  Iff.rfl

/-! ## Barrier convenience abbreviation -/

/-- `BarrierBeta β s` is the barrier value of `β` at the error flow of
    state `s`. Convenience abbreviation for `β.mu s.E_tilde`; the full
    barrier potential `Φ` additionally adds the slack `(C_budget − s.C)`
    (see `Phi` in `BarrierFramework`). -/
def BarrierBeta {P : QECParams} {L : LogicalClass P}
    (β : BarrierFunction P L) (s : QStab.State P) : Nat :=
  β.mu s.E_tilde

/-- Unfolding lemma for `BarrierBeta`. -/
theorem BarrierBeta_eq {P : QECParams} {L : LogicalClass P}
    (β : BarrierFunction P L) (s : QStab.State P) :
    BarrierBeta β s = β.mu s.E_tilde :=
  rfl

/-! ## Touches-every-row / column predicates

These are the *topological* lower-bound predicates: an error that
touches every row (resp. column) of a `d × d` grid has weight at least
`d` (Pigeonhole). They are the abstract form of the
`projRowsX = d` and `projColsZ = d` premises used in the surface-code
distance argument. -/

/-- `TouchesEveryRowX E` : every row of the `d × d` grid contains at
    least one position with non-zero X-component. -/
def TouchesEveryRowX {d : Nat} (E : ErrorVec (d * d)) : Prop :=
  ∀ i : Fin d, ∃ j : Fin d, Pauli.hasXComponent (E (toIdx d i j)) = true

/-- Unfolding lemma for `TouchesEveryRowX`. -/
theorem TouchesEveryRowX_iff {d : Nat} (E : ErrorVec (d * d)) :
    TouchesEveryRowX E ↔
      ∀ i : Fin d, ∃ j : Fin d, Pauli.hasXComponent (E (toIdx d i j)) = true :=
  Iff.rfl

/-- `TouchesEveryColZ E` : every column of the `d × d` grid contains at
    least one position with non-zero Z-component. -/
def TouchesEveryColZ {d : Nat} (E : ErrorVec (d * d)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin d, Pauli.hasZComponent (E (toIdx d i j)) = true

/-- Unfolding lemma for `TouchesEveryColZ`. -/
theorem TouchesEveryColZ_iff {d : Nat} (E : ErrorVec (d * d)) :
    TouchesEveryColZ E ↔
      ∀ j : Fin d, ∃ i : Fin d, Pauli.hasZComponent (E (toIdx d i j)) = true :=
  Iff.rfl

end QStab.Paper.Predicates
