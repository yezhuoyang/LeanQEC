import QStab.QClifford.Gate

/-! # QClifford execution semantics (Floyd-Hoare model-theoretic layer style)

A QClifford circuit is a list of Pauli-propagation rules; execution is
**deterministic** (unlike QStab's nondeterministic `Step`). We give an
inductive presentation `cevalC` so that the per-rule Hoare lemmas
discharge by `cases hev` exactly as on the QStab side.

Equivalence with the functional `propagateCircuit`:
  `cevalC c es es' ↔ propagateCircuit c es = es'`

is proved in `cevalC_iff_propagateCircuit`. We use the inductive form
for stating Hoare triples (matches the standard form) and the functional form when
computing.
-/

namespace QHL.Target

open QStab.QClifford

/-- Inductive execution relation for QClifford circuits.

    Mirrors `QHL.Source.ceval` for the QStab side. Deterministic: for each
    `(c, es)` there is a unique `es'`. -/
inductive cevalC {nq : Nat} : Circuit nq → ErrorState nq → ErrorState nq → Prop where
  /-- Empty circuit: state unchanged. -/
  | E_nil (es : ErrorState nq) : cevalC [] es es
  /-- One gate then the rest. -/
  | E_cons (g : Gate nq) (gs : Circuit nq) (es es' : ErrorState nq) :
      cevalC gs (propagateGate g es) es' → cevalC (g :: gs) es es'

/-- standard notation `es =[ c ]=>c es'`. We use `=>c` (with a `c`
    suffix) to disambiguate from the QStab `=[c]=>`. -/
notation:80 es " =[ " c " ]=>c " es' => cevalC c es es'

/-- The inductive relation agrees with the functional `propagateCircuit`. -/
theorem cevalC_iff_propagateCircuit {nq : Nat} (c : Circuit nq)
    (es es' : ErrorState nq) :
    cevalC c es es' ↔ propagateCircuit c es = es' := by
  constructor
  · intro h
    induction h with
    | E_nil _ => rfl
    | E_cons g gs es es' _ ih => simp [propagateCircuit]; exact ih
  · intro h
    subst h
    induction c generalizing es with
    | nil => exact cevalC.E_nil es
    | cons g gs ih =>
      apply cevalC.E_cons g gs es _
      exact ih (propagateGate g es)

/-- The functional form of execution gives a `cevalC` witness. -/
theorem cevalC_of_propagateCircuit {nq : Nat} (c : Circuit nq) (es : ErrorState nq) :
    cevalC c es (propagateCircuit c es) :=
  (cevalC_iff_propagateCircuit c es (propagateCircuit c es)).mpr rfl

end QHL.Target
