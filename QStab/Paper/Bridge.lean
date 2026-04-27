import QStab.QClifford.Standard

/-!
# Bridge between the paper's typing terminology and the Lean QType

The paper (§5.1, fig:fault-typing in invariant.tex) classifies single-qubit
Pauli faults inside a stabilizer-measurement gadget into four types:
Type-0/I/II/III. The existing Lean formalization in
`QStab/QClifford/Standard.lean` uses a slightly different vocabulary
`QType := data | hook | measOnly | trivial`, where `data` merges Type-0
and Type-I and `trivial` is an extra case the paper does not name.

This file:
1. Introduces `FaultType` matching the paper's vocabulary.
2. Defines `paperType` as a derived classifier built on top of `classify`.
3. Pins concrete bug witnesses found while auditing the paper definitions.

Bug witnesses (cross-referenced to `notes/scratch.md` of `Codedistance`):
- Bug 1: T-Hook `P ∈ {X, Y}` is X-stabilizer-specific. For Z-stabilizers
  the dangerous Pauli is Z (or Y).
- Bug 3: Type-0 vs Type-I is determined by `mflip`, not by gate position.
- Bug 4: `trivial` is a fifth case missing from the paper's enumeration.
-/

namespace QStab.Paper

open QStab.QClifford
open QStab.QClifford.Standard

/-- The paper's four fault types plus an explicit `trivial`. `trivial`
    captures faults absorbed by the gadget (e.g.\ ancilla X before
    `prepPlus`); the paper's QStab semantics handles these implicitly by
    not firing any transition. -/
inductive FaultType where
  | type0      -- data fault, no measurement flip
  | type1      -- data fault with measurement flip
  | type2      -- hook (multi-qubit data error)
  | type3      -- measurement flip only
  | trivial    -- no observable effect (e.g.\ absorbed by prep)
  deriving Repr, DecidableEq

/-- Map the existing Lean `QType` (used in `Standard.lean`) into the
    paper's `FaultType`. Note that `data wt mf` is split by `mf`:
    `mf = false` → Type-0 (no measurement flip), `mf = true` → Type-I.
    This commits to **Bug 3**'s correction: position alone does not
    determine the type, only `mflip` does. -/
def fromQType : QType → FaultType
  | .data _ false => .type0
  | .data _ true  => .type1
  | .hook _ _     => .type2
  | .measOnly     => .type3
  | .trivial      => .trivial

/-- Paper-style classifier, built on top of `classify` from `Standard.lean`. -/
def paperType (n : Nat) (es : ErrorState (n + 1)) : FaultType :=
  fromQType (classify n es)

/-- Totality: every fault has a paper-type. (Automatic since `paperType`
    is a total function.) This is the Lean analogue of the paper's
    informal claim "every fault location is well-typed under the four
    rules." -/
theorem paperType_total (n : Nat) (es : ErrorState (n + 1)) :
    ∃ τ : FaultType, paperType n es = τ :=
  ⟨_, rfl⟩

/-! ## Concrete examples reproducing the §5.1 type rules

Test setup: a weight-4 X-stabilizer XXXX measured by the standard CNOT
scheme on data qubits 0..3 with ancilla as qubit 4. -/

private def c4 : Circuit 5 := xCircuit 4
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]

-- Ancilla X between two CNOT gates: produces a hook → Type-II.
example :
    paperType 4 (computeFaultEffect c4 ⟨2, ⟨4, by omega⟩, .X, by decide⟩) = .type2 := by
  native_decide

-- Ancilla Z just before measurement: only flips the readout → Type-III.
example :
    paperType 4 (computeFaultEffect c4 ⟨5, ⟨4, by omega⟩, .Z, by decide⟩) = .type3 := by
  native_decide

-- Data X on q1 commutes with the X on q1 of XXXX → Type-0 (no mflip).
example :
    paperType 4 (computeFaultEffect c4 ⟨2, ⟨1, by omega⟩, .X, by decide⟩) = .type0 := by
  native_decide

-- Data Z on q1 anticommutes with X on q1 of XXXX → Type-I (with mflip).
example :
    paperType 4 (computeFaultEffect c4 ⟨2, ⟨1, by omega⟩, .Z, by decide⟩) = .type1 := by
  native_decide

-- Ancilla X **before** `prepPlus`: absorbed by the reset → trivial. The
-- paper's enumeration would not assign a type here; this is **Bug 4**.
example :
    paperType 4 (computeFaultEffect c4 ⟨0, ⟨4, by omega⟩, .X, by decide⟩) = .trivial := by
  native_decide

/-! ## Bug 1: T-Hook is wrong for Z-stabilizers

The paper's T-Hook rule premise is "ancilla, P ∈ {X, Y}". This is correct
for X-type stabilizers (the X fault propagates through the next CNOT(anc,
data) into a multi-qubit X error on data). For Z-type stabilizers measured
by `prepZero(a); CNOT(q_i, a); ...; measZ(a)`, the ancilla is the
**target** of the CNOT, and the dangerous Pauli is Z, not X.

We pin the bug witness here as Lean-checked facts. -/

private def cz4 : Circuit 5 := zCircuit 4
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]

-- Z-stabilizer: ancilla **Z** between coupling gates → Type-II.
example :
    paperType 4 (computeFaultEffect cz4 ⟨2, ⟨4, by omega⟩, .Z, by decide⟩) = .type2 := by
  native_decide

-- Z-stabilizer: ancilla **X** between coupling gates → Type-III, NOT
-- Type-II. (The paper's T-Hook rule mistakenly classifies this as a
-- hook.)
example :
    paperType 4 (computeFaultEffect cz4 ⟨2, ⟨4, by omega⟩, .X, by decide⟩) = .type3 := by
  native_decide

-- Z-stabilizer: ancilla **Y** between coupling gates → Type-II + mflip.
-- (Y has both X and Z components; the Z component creates the hook,
-- the X component flips the measurement.)
example :
    paperType 4 (computeFaultEffect cz4 ⟨2, ⟨4, by omega⟩, .Y, by decide⟩) = .type2 := by
  native_decide

end QStab.Paper
