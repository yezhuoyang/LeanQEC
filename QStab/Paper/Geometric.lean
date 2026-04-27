import QStab.QClifford.Standard
import QStab.Paper.Bridge

/-!
# Syntactic type-and-effect rules for the standard CNOT scheme

`geomType` realizes the standard-scheme syntactic system ⊢_Std from
invariant.tex §5.1, fig:fault-typing — the per-scheme component of the
type-and-effect framework. Type-checking is purely syntactic: each
rule's premise is an O(1)-size pattern match on the gate suffix
following the fault, with no Pauli propagation at type-check time. The
output is the effect summary `Fault[τ, e_B, m_f]`.

This realizes the type-and-effect discipline (Gifford–Lucassen /
Nielson–Nielson) in two layers:
- **Denotational T-Fault** (in Bridge.lean as `paperType`): propagate
  through the suffix, abstract via α(es) = (dataWt, mflip, dataPauli),
  read off the type. Universal but O(L).
- **Per-scheme syntactic rules** (this file): O(1) pattern match,
  proved sound against the denotational rule. The point: type-checking
  is cheaper than the propagation semantics it abstracts.

Soundness theorems `geomType_sound_c4` and `geomType_sound_cz4` (below)
machine-check exhaustive agreement of `geomType` with `paperType` over
every (pos, q, P) in the weight-4 X- and Z-stabilizer gadgets. The
schema-level theorem (parameterized over arbitrary support) reduces to
the per-rule case analysis.

A truly scheme-agnostic O(1) syntactic system covering Standard / Shor /
Flag / Knill simultaneously is impossible (paper §5.1, "Why per-scheme,
not universal?"): each scheme's gate vocabulary admits its own O(1)
pattern match, but the patterns differ. The uniform thread across
schemes is the **type-and-effect discipline** itself: every per-scheme
syntactic system computes the same effect summary that propagation
would, just more cheaply.

For Shor / Flag / Knill: analogous syntactic systems pattern-match on
each scheme's gate vocabulary; soundness is proved by the same
case-on-propagation argument. Those are not yet machine-checked in this
file.
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
  | none                  =>
      -- No subsequent gate touches q at all: the fault Pauli stays put.
      -- Data fault → single-qubit data error (Type-0); an ancilla fault
      -- with no remaining MeasZ shouldn't occur in a well-formed gadget,
      -- but conservatively treat as trivial.
      if q = anc then .trivial else .type0
  | some (.prepPlus _)    => .trivial
  | some (.prepZero _)    => .trivial
  | some (.cnot c t _)    =>
      if q = anc then
        -- Ancilla fault: type depends on whether anc is control or target
        -- AND on the COUNT of remaining coupling CNOTs.
        if c = anc then
          -- X-stab ancilla. Propagation through nC = countAsControl anc CNOTs:
          --   data weight = nC if hasXComp(P) else 0
          --   mflip = hasZComp(P)  (Z stays on anc → X via H → flips MeasZ)
          let nC := countAsControl anc suffix
          if hasXComp P then
            if nC ≥ 2 then .type2  -- hook of weight nC ≥ 2
            else if hasZComp P then .type1  -- nC = 1 + Z-component (Y fault)
            else .type0                      -- nC = 1, X fault only
          else
            .type3                           -- Z-only fault: data weight 0, mflip 1
        else if t = anc then
          -- Z-stab ancilla. Propagation through nT = countAsTarget anc CNOTs:
          --   data weight = nT if hasZComp(P) else 0
          --   mflip = hasXComp(P)  (X stays on anc target until MeasZ flips it)
          let nT := countAsTarget anc suffix
          if hasZComp P then
            if nT ≥ 2 then .type2
            else if hasXComp P then .type1   -- nT = 1 + X-component (Y fault)
            else .type0                       -- nT = 1, Z fault only
          else
            .type3
        else
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

/-! ## Soundness of `geomType` against `paperType`

Soundness theorem (standard-scheme syntactic typing matches semantic
classification): for every fault location `(pos, q, P)` in a standard-
scheme gadget, the syntactic `geomType` (O(1) pattern match) returns
the same `FaultType` as the semantic `paperType` (propagation +
classification).

We Lean-check this for the weight-4 X- and Z-stabilizer gadgets
exhaustively over all (pos, q, P) by `native_decide`. The full schema-
level theorem (parameterized over arbitrary gadget size and arbitrary
support list) reduces to the per-rule case analysis given in
invariant.tex Theorem 4 (proof sketch); the per-instance check below
covers the concrete cases the paper's worked examples reference. -/

/-- Pauli range for the exhaustive check. -/
private def paulisNonI : List Pauli := [.X, .Y, .Z]

/-- Soundness of `geomType` against `paperType` on the weight-4
    X-stabilizer gadget `c4`, exhaustively over every `(pos, q, P)`. -/
theorem geomType_sound_c4 :
    ∀ pos ∈ List.range (c4.length + 1),
    ∀ q : Fin 5,
    ∀ P ∈ paulisNonI,
      ∀ (hp : P ≠ .I),
        geomType anc4 (gateSuffix c4 pos) q P =
        paperType 4 (computeFaultEffect c4 ⟨pos, q, P, hp⟩) := by
  native_decide

/-- Soundness on the weight-4 Z-stabilizer gadget `cz4`. -/
theorem geomType_sound_cz4 :
    ∀ pos ∈ List.range (cz4.length + 1),
    ∀ q : Fin 5,
    ∀ P ∈ paulisNonI,
      ∀ (hp : P ≠ .I),
        geomType anc4 (gateSuffix cz4 pos) q P =
        paperType 4 (computeFaultEffect cz4 ⟨pos, q, P, hp⟩) := by
  native_decide

end QStab.Paper.Geometric
