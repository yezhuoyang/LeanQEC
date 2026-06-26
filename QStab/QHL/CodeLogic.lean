import QStab.QHL.CodeLang

/-! # Derived first-order code predicates

This module sits on top of `QHL.CodeLang`.  It does not add new semantic
callbacks.  The predicates below are just first-order formulas over evaluated
OCaml-style code functions.
-/

namespace QHL.CodeLang

namespace Term

/-- Shift one variable under a cutoff. Variables below the cutoff are bound by
    an inner binder and must not be captured. -/
def weakenVar (cutoff : Nat) {arity : Nat} (v : Fin arity) :
    Fin (arity + 1) :=
  if _ : v.val < cutoff then
    ⟨v.val, Nat.lt_trans v.isLt (Nat.lt_succ_self arity)⟩
  else
    ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩

/-- Capture-avoiding weakening under one newly bound natural variable. -/
def lift (cutoff : Nat) {arity : Nat} {ty : Ty} :
    Term arity ty -> Term (arity + 1) ty
  | .var v => .var (weakenVar cutoff v)
  | .natLit n => .natLit n
  | .boolLit b => .boolLit b
  | .pauliLit p => .pauliLit p
  | .add a b => .add (a.lift cutoff) (b.lift cutoff)
  | .sub a b => .sub (a.lift cutoff) (b.lift cutoff)
  | .mul a b => .mul (a.lift cutoff) (b.lift cutoff)
  | .div a b => .div (a.lift cutoff) (b.lift cutoff)
  | .mod a b => .mod (a.lift cutoff) (b.lift cutoff)
  | .eqNat a b => .eqNat (a.lift cutoff) (b.lift cutoff)
  | .ltNat a b => .ltNat (a.lift cutoff) (b.lift cutoff)
  | .leNat a b => .leNat (a.lift cutoff) (b.lift cutoff)
  | .not a => .not (a.lift cutoff)
  | .and a b => .and (a.lift cutoff) (b.lift cutoff)
  | .or a b => .or (a.lift cutoff) (b.lift cutoff)
  | .ite c t e => .ite (c.lift cutoff) (t.lift cutoff) (e.lift cutoff)
  | .pauliMul a b => .pauliMul (a.lift cutoff) (b.lift cutoff)
  | .anticommutes a b => .anticommutes (a.lift cutoff) (b.lift cutoff)
  | .stabLam entry => .stabLam (entry.lift (cutoff + 1))
  | .stabAt s q => .stabAt (s.lift cutoff) (q.lift cutoff)
  | .stabFold n body => .stabFold (n.lift cutoff) (body.lift (cutoff + 1))
  | .recCall d k => .recCall (d.lift cutoff) (k.lift cutoff)

/-- Weakening at the outermost scope. -/
def weaken {arity : Nat} {ty : Ty} (t : Term arity ty) : Term (arity + 1) ty :=
  t.lift 0

end Term

namespace Formula

/-- The qubit variable bound by a surrounding `stabLam`. -/
def qVar {arity : Nat} : Term (arity + 1) .nat :=
  .var ⟨0, Nat.succ_pos arity⟩

/-- A code row is the evaluated recursive code function at `(d,k)`. -/
def codeRow {arity : Nat} (d k : Term arity .nat) : Term arity .stab :=
  .recCall d k

/-- A closed stabilizer from a one-variable Pauli-entry program. -/
def closedStabilizer (entry : Term 1 .pauli) : Term 0 .stab :=
  .stabLam entry

/-- Parity-one relation, expressed as negated commutation over the finite block. -/
def anticommutesUpTo {arity : Nat}
    (n : Term arity .nat) (A B : Term arity .stab) : Formula arity :=
  .not (.commutesUpTo n A B)

/-- Every generator in `code(d, -)` commutes with candidate `L`. -/
def normalizesCodeUpTo
    (n numStab d : Term 0 .nat) (L : Term 0 .stab) : Formula 0 :=
  .allNatLt numStab <|
    .commutesUpTo n.weaken
      (codeRow d.weaken (.var ⟨0, by decide⟩))
      L.weaken

/-- All generated stabilizer rows commute pairwise. -/
def codeRowsCommuteUpTo
    (n numStab d : Term 0 .nat) : Formula 0 :=
  .allNatLt numStab <|
    .allNatLt numStab.weaken <|
      .commutesUpTo n.weaken.weaken
        (codeRow d.weaken.weaken (.var ⟨1, by decide⟩))
        (codeRow d.weaken.weaken (.var ⟨0, by decide⟩))

/-- A logical pair candidate: both operators normalize the code and anticommute
    with each other.  Non-membership in the stabilizer group is intentionally
    not hidden here; it needs a separate mask-product judgment. -/
def logicalPairCandidateUpTo
    (n numStab d : Term 0 .nat) (LX LZ : Term 0 .stab) : Formula 0 :=
  .and (normalizesCodeUpTo n numStab d LX)
    (.and (normalizesCodeUpTo n numStab d LZ)
      (anticommutesUpTo n LX LZ))

/-! ### Derived stabilizer-product notions

No new primitive is introduced here.  `rowProduct` is just an AST macro that
expands to a stabilizer lambda whose entry multiplies generated code rows.
-/

/-- Pointwise product of two stabilizer expressions, expanded into `stabLam`,
    `stabAt`, and `pauliMul`. -/
def stabMul {arity : Nat} (A B : Term arity .stab) : Term arity .stab :=
  .stabLam <|
    .pauliMul
      (.stabAt A.weaken qVar)
      (.stabAt B.weaken qVar)

/-- Entry expression for the product of selected generated rows. -/
def rowProductEntry {arity : Nat} (d : Term arity .nat) :
    List (Term arity .nat) -> Term (arity + 1) .pauli
  | [] => .pauliLit Pauli.I
  | row :: rows =>
      .pauliMul
        (.stabAt (codeRow d.weaken row.weaken) qVar)
        (rowProductEntry d rows)

/-- Product of selected generated rows, derived entirely as a stabilizer AST. -/
def rowProduct {arity : Nat} (d : Term arity .nat)
    (rows : List (Term arity .nat)) : Term arity .stab :=
  .stabLam (rowProductEntry d rows)

/-- Candidate membership in the generated stabilizer group, with the row list
    as an explicit witness.  This is `E = productRows(rows)`, not a primitive
    `InStab` predicate. -/
def generatedByRowsUpTo {arity : Nat}
    (n : Term arity .nat) (E : Term arity .stab) (d : Term arity .nat)
    (rows : List (Term arity .nat)) : Formula arity :=
  .eqStabUpTo n E (rowProduct d rows)

/-- Stabilizer equivalence with an explicit generated-row witness:
    `A = productRows(rows) * B`. -/
def equivByRowsUpTo {arity : Nat}
    (n : Term arity .nat) (A B : Term arity .stab) (d : Term arity .nat)
    (rows : List (Term arity .nat)) : Formula arity :=
  .eqStabUpTo n A (stabMul (rowProduct d rows) B)

end Formula

/-! ## Executable bug-catching checks -/

def qubit0X : Term 1 .pauli :=
  .ite (.eqNat (.var ⟨0, by decide⟩) (.natLit 0))
    (.pauliLit Pauli.X)
    (.pauliLit Pauli.I)

def qubit0Z : Term 1 .pauli :=
  .ite (.eqNat (.var ⟨0, by decide⟩) (.natLit 0))
    (.pauliLit Pauli.Z)
    (.pauliLit Pauli.I)

def closedX0 : Term 0 .stab :=
  Formula.closedStabilizer qubit0X

def closedZ0 : Term 0 .stab :=
  Formula.closedStabilizer qubit0Z

/-- A bad two-generator code: row 0 is X on q0, row 1 is Z on q0. -/
def noncommutingTwoRowCode : CodeFn where
  body := .stabLam <|
    .ite (.eqNat C.Entry.k C.zero)
      (.ite (.eqNat C.Entry.q C.zero) (.pauliLit Pauli.X) (.pauliLit Pauli.I))
      (.ite (.eqNat C.Entry.q C.zero) (.pauliLit Pauli.Z) (.pauliLit Pauli.I))

def noncommutingTwoRowCheck : Formula 0 :=
  Formula.codeRowsCommuteUpTo (.natLit 1) (.natLit 2) (.natLit 3)

/-- info: some false -/
#guard_msgs in
#eval noncommutingTwoRowCheck.eval noncommutingTwoRowCode.body 1 Env.empty

/-- A one-generator X code, used to check normalizer candidates. -/
def oneRowXCode : CodeFn where
  body := .stabLam <|
    .ite (.eqNat C.Entry.q C.zero) (.pauliLit Pauli.X) (.pauliLit Pauli.I)

def goodNormalizerCheck : Formula 0 :=
  Formula.normalizesCodeUpTo (.natLit 1) (.natLit 1) (.natLit 3) closedX0

/-- info: some true -/
#guard_msgs in
#eval goodNormalizerCheck.eval oneRowXCode.body 1 Env.empty

def badLogicalNormalizerCheck : Formula 0 :=
  Formula.normalizesCodeUpTo (.natLit 1) (.natLit 1) (.natLit 3) closedZ0

/-- info: some false -/
#guard_msgs in
#eval badLogicalNormalizerCheck.eval oneRowXCode.body 1 Env.empty

def generatedX0Check : Formula 0 :=
  Formula.generatedByRowsUpTo (.natLit 1) closedX0 (.natLit 3) [(.natLit 0)]

/-- info: some true -/
#guard_msgs in
#eval generatedX0Check.eval oneRowXCode.body 1 Env.empty

def badGeneratedZ0Check : Formula 0 :=
  Formula.generatedByRowsUpTo (.natLit 1) closedZ0 (.natLit 3) [(.natLit 0)]

/-- info: some false -/
#guard_msgs in
#eval badGeneratedZ0Check.eval oneRowXCode.body 1 Env.empty

def generatedIdentityCheck : Formula 0 :=
  Formula.generatedByRowsUpTo (.natLit 1)
    (Formula.closedStabilizer (.pauliLit Pauli.I)) (.natLit 3) []

/-- info: some true -/
#guard_msgs in
#eval generatedIdentityCheck.eval oneRowXCode.body 1 Env.empty

def logicalPairSmokeCheck : Formula 0 :=
  Formula.logicalPairCandidateUpTo (.natLit 1) (.natLit 0) (.natLit 3) closedX0 closedZ0

/-- info: some true -/
#guard_msgs in
#eval logicalPairSmokeCheck.eval identityCode.body 0 Env.empty

#print axioms Formula.codeRowsCommuteUpTo
#print axioms Formula.normalizesCodeUpTo
#print axioms Formula.logicalPairCandidateUpTo
#print axioms Formula.generatedByRowsUpTo
#print axioms Formula.equivByRowsUpTo

end QHL.CodeLang
