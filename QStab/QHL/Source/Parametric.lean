import QStab.QHL.Source.Branch

/-! # Parametric QStab programs

This is the family-level layer above concrete QStab.

Layer 1 is the recursive QEC AST layer, which generates code/schedule symbols.
Layer 2 is this parametric QStab layer, where a program is a symbolic family
`d ↦ currentStab(d, coord)` and proof rules quantify over all legal distances.
Layer 3 is concrete QStab, obtained by elaborating one distance to the ordinary
`QStabProgram` small-step semantics.

The size counted here is the size of the family-level derivation schema.  The
concrete generated program may have `d`-dependent length; that length is not
part of the parametric proof tree.
-/

namespace QHL.Source.Parametric

open QStab QHL.AssertionLang QHL.Source.Branch

/-- A concrete QStab instruction at one program label.

Canonical QStab programs have only fixed stabilizer measurements.  The four
fault kinds are nondeterministic semantic branches, not program instructions. -/
inductive QStabInstruction (P : QECParams) : Type where
  | prop (stab : Fin P.numStab) : QStabInstruction P

namespace QStabInstruction

def measuredStab {P : QECParams} : QStabInstruction P -> Fin P.numStab
  | .prop stab => stab

end QStabInstruction

/-- Stabilizer-index expressions over an instruction label.

For row-major QStab, label coordinate `(x,y)` measures stabilizer `x`.  More
measurement schedules can be added here as syntax constructors without changing
the concrete QStab small-step semantics. -/
inductive ParamStabIndexExpr : Type where
  | coordX : ParamStabIndexExpr

namespace ParamStabIndexExpr

def eval {P : QECParams} : ParamStabIndexExpr -> QECParams.Coord P -> Fin P.numStab
  | .coordX, coord => coord.x

end ParamStabIndexExpr

/-- Parametric QStab instruction syntax.

This is the syntactic function from a family label to a concrete QStab
instruction.  Its denotation depends on the generated `QECParams d`, but the
program tree itself is constant-size. -/
inductive ParamInstructionAST : Type where
  | prop (stab : ParamStabIndexExpr) : ParamInstructionAST

namespace ParamInstructionAST

def eval {P : QECParams} : ParamInstructionAST -> QECParams.Coord P -> QStabInstruction P
  | .prop stab, coord => .prop (stab.eval coord)

def measuredStab {P : QECParams} (inst : ParamInstructionAST) (coord : QECParams.Coord P) :
    Fin P.numStab :=
  (inst.eval coord).measuredStab

end ParamInstructionAST

/-- Syntactic family of fixed QStab measurement programs.

The fields `codeName` and `scheduleName` tie the program tree to the generated
code and intra-stabilizer schedule layer.  The instruction body is the actual
program syntax: given a distance-specific label, it returns the concrete
`Prop T_s` instruction at that label. -/
structure ParamQStabProgramAST where
  name : String
  codeName : String
  scheduleName : String
  Valid : Nat -> Prop
  params : (d : Nat) -> Valid d -> QECParams
  body : ParamInstructionAST

/-- Semantic family of fixed QStab measurement programs.

The executable QStab program at distance `d` is produced only by elaboration.
This is the denotation of `ParamQStabProgramAST`, plus a compatibility surface
for existing branch Hoare rules. -/
structure ParamQStabProgram where
  name : String
  Valid : Nat -> Prop
  params : (d : Nat) -> Valid d -> QECParams
  currentStab :
    (d : Nat) -> (hd : Valid d) ->
      QECParams.Coord (params d hd) -> Fin (params d hd).numStab

namespace ParamQStabProgram

/-- Elaboration from the parametric syntax layer to concrete QStab. -/
def elaborate (F : ParamQStabProgram) (d : Nat) (hd : F.Valid d) :
    QStabProgram (F.params d hd) where
  currentStab := F.currentStab d hd

@[simp] theorem elaborate_currentStab (F : ParamQStabProgram)
    (d : Nat) (hd : F.Valid d) (c : QECParams.Coord (F.params d hd)) :
    (F.elaborate d hd).currentStab c = F.currentStab d hd c :=
  rfl

end ParamQStabProgram

namespace ParamQStabProgramAST

/-- Evaluate the syntactic parametric program at one legal distance and label. -/
def instructionAt (A : ParamQStabProgramAST) (d : Nat) (hd : A.Valid d)
    (coord : QECParams.Coord (A.params d hd)) : QStabInstruction (A.params d hd) :=
  A.body.eval coord

/-- Denotation of a syntactic parametric program as the semantic family used by
    the existing concrete QStab small-step semantics. -/
def toProgram (A : ParamQStabProgramAST) : ParamQStabProgram where
  name := A.name
  Valid := A.Valid
  params := A.params
  currentStab := fun d hd coord => (A.instructionAt d hd coord).measuredStab

@[simp] theorem toProgram_currentStab (A : ParamQStabProgramAST)
    (d : Nat) (hd : A.Valid d) (coord : QECParams.Coord (A.params d hd)) :
    (A.toProgram.currentStab d hd coord) = (A.instructionAt d hd coord).measuredStab :=
  rfl

@[simp] theorem toProgram_elaborate_currentStab (A : ParamQStabProgramAST)
    (d : Nat) (hd : A.Valid d) (coord : QECParams.Coord (A.params d hd)) :
    (A.toProgram.elaborate d hd).currentStab coord =
      (A.instructionAt d hd coord).measuredStab :=
  rfl

end ParamQStabProgramAST

/-- A closed assertion formula family indexed by the same distance parameter as
    a parametric QStab program. -/
abbrev ParamFormula (F : ParamQStabProgram) :=
  (d : Nat) -> (hd : F.Valid d) -> Formula (F.params d hd) []

/-- Semantic family-level demonic Hoare statement. -/
def ParamHavocHoare (F : ParamQStabProgram)
    (A B : ParamFormula F) : Prop :=
  forall d hd,
    HavocHoare (F.elaborate d hd) (A d hd).denote (B d hd).denote

/-- Generic top-preservation certificate for Type-0. -/
noncomputable def topErr0Certificate {P : QECParams} (prog : QStabProgram P)
    (i : Fin P.n) (p : Pauli) :
    Certificate prog (Formula.top (P := P)) (.err0 i p) (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErr0 prog i p)
    (Certificate.err0 (Formula.top (P := P)) i p)
    (Entails.refl (Formula.top (P := P)))

/-- Generic top-preservation certificate for Type-I. -/
noncomputable def topErrICertificate {P : QECParams} (prog : QStabProgram P)
    (i : Fin P.n) (p : Pauli) (mf : Bool) :
    Certificate prog (Formula.top (P := P)) (.errI i p mf) (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErrI prog i p mf)
    (Certificate.errI (Formula.top (P := P)) i p mf)
    (Entails.refl (Formula.top (P := P)))

/-- Generic top-preservation certificate for Type-II. -/
noncomputable def topErrIICertificate {P : QECParams} (prog : QStabProgram P)
    (e : ErrorVec P.n) (mf : Bool) :
    Certificate prog (Formula.top (P := P)) (.errII e mf) (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErrII prog e mf)
    (Certificate.errII (Formula.top (P := P)) e mf)
    (Entails.refl (Formula.top (P := P)))

/-- Generic top-preservation certificate for Type-III. -/
noncomputable def topErrIIICertificate {P : QECParams} (prog : QStabProgram P) :
    Certificate prog (Formula.top (P := P)) .errIII (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErrIII prog)
    (Certificate.errIII (Formula.top (P := P)))
    (Entails.refl (Formula.top (P := P)))

/-- Generic top-preservation certificate for the fixed measurement branch. -/
noncomputable def topMeasCertificate {P : QECParams} (prog : QStabProgram P) :
    Certificate prog (Formula.top (P := P)) .meas (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpMeasFor prog)
    (Certificate.meas (Formula.top (P := P)))
    (Entails.refl (Formula.top (P := P)))

/-- Family-level proof tree for one demonic QStab step.

The branch fields are rule schemas: the checker instantiates them at a concrete
distance only when proving soundness for the elaborated concrete QStab program. -/
structure ParamHavocCertificate (F : ParamQStabProgram)
    (A B : ParamFormula F) where
  err0 :
    (d : Nat) -> (hd : F.Valid d) ->
      (i : Fin (F.params d hd).n) -> (p : Pauli) -> p ≠ Pauli.I ->
        Certificate (F.elaborate d hd) (A d hd) (.err0 i p) (B d hd)
  errI :
    (d : Nat) -> (hd : F.Valid d) ->
      (i : Fin (F.params d hd).n) -> (p : Pauli) -> p ≠ Pauli.I -> (mf : Bool) ->
        Certificate (F.elaborate d hd) (A d hd) (.errI i p mf) (B d hd)
  errII :
    (d : Nat) -> (hd : F.Valid d) ->
      (e : ErrorVec (F.params d hd).n) -> (mf : Bool) ->
        Certificate (F.elaborate d hd) (A d hd) (.errII e mf) (B d hd)
  errIII :
    (d : Nat) -> (hd : F.Valid d) ->
      Certificate (F.elaborate d hd) (A d hd) .errIII (B d hd)
  meas :
    (d : Nat) -> (hd : F.Valid d) ->
      Certificate (F.elaborate d hd) (A d hd) .meas (B d hd)

namespace ParamHavocCertificate

/-- Instantiate a family-level proof schema at one legal distance. -/
noncomputable def instantiate {F : ParamQStabProgram} {A B : ParamFormula F}
    (D : ParamHavocCertificate F A B) (d : Nat) (hd : F.Valid d) :
    HavocCertificate (F.elaborate d hd) (A d hd) (B d hd) :=
  HavocCertificate.havocStep
    (D.err0 d hd)
    (D.errI d hd)
    (D.errII d hd)
    (D.errIII d hd)
    (D.meas d hd)

/-- The family proof schema is a single demonic-step rule, independent of `d`. -/
def schemaSize {F : ParamQStabProgram} {A B : ParamFormula F}
    (_D : ParamHavocCertificate F A B) : Nat :=
  1

@[simp] theorem schemaSize_eq_one {F : ParamQStabProgram} {A B : ParamFormula F}
    (D : ParamHavocCertificate F A B) :
    D.schemaSize = 1 :=
  rfl

@[simp] theorem instantiate_size_eq_one {F : ParamQStabProgram} {A B : ParamFormula F}
    (D : ParamHavocCertificate F A B) (d : Nat) (hd : F.Valid d) :
    (D.instantiate d hd).size = 1 :=
  rfl

/-- Soundness of the family-level demonic rule against every elaborated program. -/
theorem sound {F : ParamQStabProgram} {A B : ParamFormula F}
    (D : ParamHavocCertificate F A B) :
    ParamHavocHoare F A B := by
  intro d hd
  exact (D.instantiate d hd).check_sound

end ParamHavocCertificate

/-- Family-level invariant derivation: one initial assertion schema plus one
    demonic preservation schema. -/
structure ParamInvariantDerivation (F : ParamQStabProgram)
    (I : ParamFormula F) where
  init : forall d hd, (I d hd).denote (State.init (F.params d hd))
  step : ParamHavocCertificate F I I

namespace ParamInvariantDerivation

/-- Instantiate a parametric invariant derivation at a legal distance. -/
noncomputable def instantiate {F : ParamQStabProgram} {I : ParamFormula F}
    (D : ParamInvariantDerivation F I) (d : Nat) (hd : F.Valid d) :
    InvariantDerivation (F.elaborate d hd) (I d hd) where
  init := D.init d hd
  step := D.step.instantiate d hd

theorem check_sound {F : ParamQStabProgram} {I : ParamFormula F}
    (D : ParamInvariantDerivation F I)
    (d : Nat) (hd : F.Valid d)
    (s : State (F.params d hd))
    (hrun : Run (F.elaborate d hd) (.done s)) :
    (I d hd).denote s :=
  (D.instantiate d hd).check_sound s hrun

theorem check_active_sound {F : ParamQStabProgram} {I : ParamFormula F}
    (D : ParamInvariantDerivation F I)
    (d : Nat) (hd : F.Valid d)
    (s : State (F.params d hd))
    (hreach : MultiStep (F.elaborate d hd)
      (.active (State.init (F.params d hd))) (.active s)) :
    (I d hd).denote s :=
  (D.instantiate d hd).check_active_sound s hreach

end ParamInvariantDerivation

/-- A family of syntactic barrier contracts for a parametric QStab program. -/
structure ParamBarrierPackage (F : ParamQStabProgram) where
  logical : (d : Nat) -> (hd : F.Valid d) -> LogicalClassSymbol (F.params d hd)
  barrier : (d : Nat) -> (hd : F.Valid d) -> BarrierSymbol (F.params d hd)
  contract :
    (d : Nat) -> (hd : F.Valid d) ->
      SyntacticBarrierContractCertificate (barrier d hd) (logical d hd)

namespace ParamBarrierPackage

def invariantF {F : ParamQStabProgram} (B : ParamBarrierPackage F) :
    ParamFormula F :=
  fun d hd => barrierInvF (B.barrier d hd) (B.logical d hd)

/-- The generic parametric QStab barrier-preservation derivation. -/
noncomputable def invariantHavocCertificate {F : ParamQStabProgram}
    (B : ParamBarrierPackage F) :
    ParamHavocCertificate F B.invariantF B.invariantF where
  err0 := fun d hd i p hp =>
    barrierInvErr0Certificate (prog := F.elaborate d hd) (B.contract d hd) i p hp
  errI := fun d hd i p hp mf =>
    barrierInvErrICertificate (prog := F.elaborate d hd) (B.contract d hd) i p hp mf
  errII := fun d hd e mf =>
    barrierInvErrIICertificate (prog := F.elaborate d hd) (B.contract d hd) e mf
  errIII := fun d hd =>
    barrierInvErrIIICertificate (prog := F.elaborate d hd) (B.contract d hd)
  meas := fun d hd =>
    barrierInvMeasCertificate (prog := F.elaborate d hd) (B.contract d hd)

@[simp] theorem invariantHavocCertificate_schemaSize {F : ParamQStabProgram}
    (B : ParamBarrierPackage F) :
    B.invariantHavocCertificate.schemaSize = 1 :=
  rfl

/-- Full parametric invariant derivation generated by the barrier contract. -/
noncomputable def invariantDerivation {F : ParamQStabProgram}
    (B : ParamBarrierPackage F) :
    ParamInvariantDerivation F B.invariantF where
  init := fun d hd =>
    barrierInvF_init_of_contract (B.barrier d hd) (B.logical d hd)
      (B.contract d hd).toChecked
  step := B.invariantHavocCertificate

theorem circuitDistance_done {F : ParamQStabProgram}
    (B : ParamBarrierPackage F)
    (d : Nat) (hd : F.Valid d)
    (s : State (F.params d hd))
    (hrun : Run (F.elaborate d hd) (.done s)) :
    (circuitDistanceF (B.logical d hd)).denote s :=
  syntacticBarrierContractCircuitDistance_done
    (prog := F.elaborate d hd) (B.contract d hd) s hrun

theorem circuitDistance_active {F : ParamQStabProgram}
    (B : ParamBarrierPackage F)
    (d : Nat) (hd : F.Valid d)
    (s : State (F.params d hd))
    (hreach : MultiStep (F.elaborate d hd)
      (.active (State.init (F.params d hd))) (.active s)) :
    (circuitDistanceF (B.logical d hd)).denote s :=
  syntacticBarrierContractCircuitDistance_active
    (prog := F.elaborate d hd) (B.contract d hd) s hreach

end ParamBarrierPackage

end QHL.Source.Parametric
