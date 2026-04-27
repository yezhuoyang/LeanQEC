import QStab.QClifford.Standard
import QStab.Paper.Bridge

/-!
# Geometric typing rules for single-qubit Pauli faults

Expresses the paper's §5.1 typing rules as a function pattern-matching on
the gate suffix following a fault location, the ancilla qubit, and the
fault Pauli — in the spirit of John's suggestion: "the type-checking
should just be a geometric argument — if an X-fault on the syndrome qubit
is followed by CNOTs(syn, data_i), then it has hook type with shape XX...X."

`geomType` reads the gate suffix, classifies the fault by which gate first
touches the fault qubit and whether the qubit is the designated ancilla,
and returns the paper's `FaultType`. We pin agreement with the
`classify`-based `paperType` on representative faults via `native_decide`.
-/

namespace QStab.Paper.Geometric

open QStab.QClifford QStab.QClifford.Standard QStab.Paper

/-- Does this gate touch qubit `q`? -/
def Gate.touches : Gate n → Fin n → Bool
  | .cnot c t _, q  => decide (q = c) || decide (q = t)
  | .hadamard q', q => decide (q = q')
  | .prepZero q', q => decide (q = q')
  | .prepPlus q', q => decide (q = q')
  | .measZ q', q    => decide (q = q')

/-- Find the first gate in the suffix that touches qubit `q`. -/
def firstGateOn {n : Nat} (q : Fin n) : List (Gate n) → Option (Gate n)
  | []        => none
  | g :: rest => if Gate.touches g q then some g else firstGateOn q rest

/-- The number of CNOT gates in the suffix that have `anc` as control. -/
def countAsControl {n : Nat} (anc : Fin n) : List (Gate n) → Nat
  | []                    => 0
  | (.cnot c _ _) :: rest => (if c = anc then 1 else 0) + countAsControl anc rest
  | _ :: rest             => countAsControl anc rest

/-- The number of CNOT gates in the suffix that have `anc` as target. -/
def countAsTarget {n : Nat} (anc : Fin n) : List (Gate n) → Nat
  | []                    => 0
  | (.cnot _ t _) :: rest => (if t = anc then 1 else 0) + countAsTarget anc rest
  | _ :: rest             => countAsTarget anc rest

/-- The geometric `FaultType` of a fault `(q, P)` whose suffix is `suffix`,
    inside a single-ancilla gadget with ancilla `anc`.

    Rule order (mirrors the paper):
    - **T-Trivial**: the next gate touching `q` is a Prep on `q`.
    - **T-Hook-X**: `q = anc`, suffix has at least one CNOT with `anc` as
      control, and `P` has an `X`-component → Type-II.
    - **T-Hook-Z**: `q = anc`, suffix has at least one CNOT with `anc` as
      target, and `P` has a `Z`-component → Type-II.
    - **T-Meas**: `q = anc`, no entangling CNOTs remain on `anc`, but the
      suffix still contains the readout (H/MeasZ); whether the fault is
      Type-III depends on whether the Pauli has the component made visible
      by the readout chain.
    - **T-Data**: `q ≠ anc`, the next gate on `q` is a CNOT(`anc`, `q`)
      (X-stab) or CNOT(`q`, `anc`) (Z-stab); Type-I if the back-propagated
      component is present, Type-0 otherwise. -/
def geomType {n : Nat} (anc : Fin n) (suffix : List (Gate n))
    (q : Fin n) (P : Pauli) : FaultType :=
  match firstGateOn q suffix with
  | none                  => .trivial
  | some (.prepPlus _)    => .trivial
  | some (.prepZero _)    => .trivial
  | some (.cnot c t _)    =>
      if q = anc then
        -- Ancilla fault: hook type depends on whether anc is control or target
        if c = anc then
          -- X-stab ancilla: subsequent gates are CNOT(anc, q_i)
          -- X-component → propagates as X to subsequent data → Type-II
          -- Z-component (only) → commutes with control, becomes X via H, Type-III
          if hasXComp P then .type2 else .type3
        else if t = anc then
          -- Z-stab ancilla: subsequent gates are CNOT(q_i, anc)
          -- Z-component → propagates as Z to subsequent data (control) → Type-II
          -- X-component (only) → stays on target until MeasZ → Type-III
          if hasZComp P then .type2 else .type3
        else
          -- shouldn't occur (firstGateOn q returned a CNOT not touching q)
          .trivial
      else
        -- Data fault: q is data, next coupling gate is the CNOT
        if c = anc ∧ t = q then
          -- X-stab: CNOT(anc, q) — Z on q back-propagates to anc → mflip
          if hasZComp P then .type1 else .type0
        else if c = q ∧ t = anc then
          -- Z-stab: CNOT(q, anc) — X on q propagates to anc → mflip
          if hasXComp P then .type1 else .type0
        else
          -- mixed scheme; conservative
          .type0
  | some (.hadamard _)    =>
      -- For the standard scheme, only the ancilla has a hadamard.
      -- After H, X↔Z. The MeasZ that follows reads the X-component.
      -- A fault P before H becomes hadamardAction(P) at the time of MeasZ.
      -- Type-III iff hadamardAction(P) has X-component, iff P has Z-component.
      if hasZComp P then .type3 else .trivial
  | some (.measZ _)       =>
      -- Fault on q immediately before its measurement: only X-component flips.
      if hasXComp P then .type3 else .trivial

/-! ## Concrete agreement examples between `geomType` and `paperType`. -/

private def c4 : Circuit 5 := xCircuit 4
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]

private def cz4 : Circuit 5 := zCircuit 4
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]

/-- The ancilla qubit for both `c4` and `cz4` is qubit index `4`. -/
private def anc4 : Fin 5 := ⟨4, by omega⟩

/-- Drop the first `k` gates: gives the suffix after fault position `k`. -/
def gateSuffix {n : Nat} (gates : List (Gate n)) (k : Nat) : List (Gate n) :=
  gates.drop k

-- ==========================================================
-- X-stab (XXXX) examples
-- ==========================================================

-- Ancilla X between CNOT 1 and CNOT 2 → T-Hook-X → Type-II
example : geomType anc4 (gateSuffix c4 2) anc4 .X = .type2 := by native_decide
example :
    paperType 4 (computeFaultEffect c4 ⟨2, anc4, .X, by decide⟩) = .type2 := by
  native_decide

-- Ancilla Z between CNOTs → no X-component → Type-III
example : geomType anc4 (gateSuffix c4 2) anc4 .Z = .type3 := by native_decide
example :
    paperType 4 (computeFaultEffect c4 ⟨2, anc4, .Z, by decide⟩) = .type3 := by
  native_decide

-- Ancilla Y → has X-component → Type-II hook + mflip (FaultType collapses to .type2)
example : geomType anc4 (gateSuffix c4 2) anc4 .Y = .type2 := by native_decide

-- Data Z on q1 before its CNOT(anc, q1) → T-Data with mflip → Type-I
example : geomType anc4 (gateSuffix c4 2) ⟨1, by omega⟩ .Z = .type1 := by native_decide
example :
    paperType 4 (computeFaultEffect c4 ⟨2, ⟨1, by omega⟩, .Z, by decide⟩) = .type1 := by
  native_decide

-- Data X on q1 before its CNOT(anc, q1) → no Z-component → Type-0
example : geomType anc4 (gateSuffix c4 2) ⟨1, by omega⟩ .X = .type0 := by native_decide
example :
    paperType 4 (computeFaultEffect c4 ⟨2, ⟨1, by omega⟩, .X, by decide⟩) = .type0 := by
  native_decide

-- Ancilla X before prepPlus → T-Trivial
example : geomType anc4 (gateSuffix c4 0) anc4 .X = .trivial := by native_decide
example :
    paperType 4 (computeFaultEffect c4 ⟨0, anc4, .X, by decide⟩) = .trivial := by
  native_decide

-- ==========================================================
-- Z-stab (ZZZZ) examples — Bug-1 witness for the paper's old T-Hook
-- ==========================================================

-- Ancilla Z between CNOTs → T-Hook-Z → Type-II.
-- The OLD T-Hook rule said "P ∈ {X, Y}" which would have missed this.
example : geomType anc4 (gateSuffix cz4 2) anc4 .Z = .type2 := by native_decide
example :
    paperType 4 (computeFaultEffect cz4 ⟨2, anc4, .Z, by decide⟩) = .type2 := by
  native_decide

-- Ancilla X between CNOTs → no Z-component → Type-III, NOT Type-II.
example : geomType anc4 (gateSuffix cz4 2) anc4 .X = .type3 := by native_decide
example :
    paperType 4 (computeFaultEffect cz4 ⟨2, anc4, .X, by decide⟩) = .type3 := by
  native_decide

-- Ancilla Y → has Z-component → Type-II.
example : geomType anc4 (gateSuffix cz4 2) anc4 .Y = .type2 := by native_decide

end QStab.Paper.Geometric
