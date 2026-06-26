import QStab.QHL.Source.Branch
import QStab.QHL.Source.Parametric
import QStab.QHL.Source.Examples.SurfaceRecursiveAST
import QStab.Examples.SurfaceHookErrors

/-! # Canonical recursive-AST Surface/NZ QStab package

This module is the build-gated Surface/NZ frontend whose public objects are
generated from recursive syntax:

* `SurfaceCodeAST.canonical` is the recursive code program `d -> k -> stabilizer`.
* `SurfaceCodeAST.nzSchedule` is the separate recursive intra-stabilizer schedule.
* `surfaceASTParams` wires the generated stabilizer table and NZ suffix hooks into
  `QECParams`.
* `surfaceASTProgram` is the fixed QStab measurement program; faults remain
  nondeterministic QStab semantic branches.

The theorem-level exact-distance bridge is intentionally not imported here.
This file is the canonical syntactic target that the full barrier/distance
derivation must consume.
-/

namespace QHL.Source.Examples.SurfaceASTCanonical

open QStab QHL.AssertionLang QHL.Source.Branch
open QHL.Source.Parametric
open QStab.Examples.SurfaceParametric
open QHL.Source.Examples.SurfaceRecursiveAST

private theorem pos_of_ge_three {d : Nat} (hd3 : 3 <= d) : 0 < d :=
  Nat.lt_of_lt_of_le (by decide : 0 < 3) hd3

/-- Legal distances for the canonical parametric Surface/NZ family. -/
abbrev surfaceASTValid (d : Nat) : Prop :=
  3 <= d ∧ d % 2 = 1

/-- Generated QEC parameters for the recursive Surface/NZ family. -/
abbrev surfaceASTParams (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    QECParams :=
  mkSurfaceQECParams d (pos_of_ge_three hd3) hodd

/-- Fixed QStab program: row-major stabilizer measurements. -/
def surfaceASTProgram (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    QStabProgram (surfaceASTParams d hd3 hodd) :=
  QStabProgram.rowMajor (surfaceASTParams d hd3 hodd)

theorem surfaceASTProgram_currentStab
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1)
    (c : QECParams.Coord (surfaceASTParams d hd3 hodd)) :
    (surfaceASTProgram d hd3 hodd).currentStab c = c.x :=
  rfl

/-- Layer-2 syntax: the parametric QStab program AST.  The body is the
    constant-size program

    `fun label => Prop (label.x)`.

    The code and NZ schedule are separate syntax objects; this program only
    chooses which generated stabilizer is measured at each QStab coordinate. -/
def surfaceASTParamQStabAST : ParamQStabProgramAST where
  name := "surface.ast.nz.rowMajor"
  codeName := "surface.ast.code"
  scheduleName := "surface.ast.nz"
  Valid := surfaceASTValid
  params := fun d hd => surfaceASTParams d hd.1 hd.2
  body := .prop .coordX

/-- Denotation of the syntactic parametric QStab program. -/
def surfaceASTParamQStab : ParamQStabProgram :=
  surfaceASTParamQStabAST.toProgram

theorem surfaceASTParamQStabAST_instructionAt
    (d : Nat) (hd : surfaceASTParamQStabAST.Valid d)
    (c : QECParams.Coord (surfaceASTParamQStabAST.params d hd)) :
    surfaceASTParamQStabAST.instructionAt d hd c = QStabInstruction.prop c.x :=
  rfl

theorem surfaceASTParamQStab_elaborates_currentStab
    (d : Nat) (hd : surfaceASTParamQStab.Valid d)
    (c : QECParams.Coord (surfaceASTParamQStab.params d hd)) :
    (surfaceASTParamQStab.elaborate d hd).currentStab c = c.x :=
  rfl

theorem surfaceASTParamQStab_elaborates_rowMajor
    (d : Nat) (hd : surfaceASTParamQStab.Valid d) :
    surfaceASTParamQStab.elaborate d hd = surfaceASTProgram d hd.1 hd.2 :=
  rfl

/-- The generated stabilizer family as an assertion-language symbol. -/
def surfaceASTStabilizerFamily
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    StabilizerFamilySymbol (surfaceASTParams d hd3 hodd) where
  name := "surface.ast.code"
  distance := d
  body := .byVector (.stabilizerAt (.var .zero))
  agrees := by
    intro k
    rfl

/-- Active NZ local schedule slots, generated from the recursive schedule AST. -/
def surfaceASTScheduleActive
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1)
    (k : Fin (surfaceASTParams d hd3 hodd).numStab) (slot : Nat) : Bool :=
  decide
    (slot < (kindOrderRC d (classifyStab d k.val)).length /\
      SurfaceCodeAST.scheduleQubit d k.val slot < (surfaceASTParams d hd3 hodd).n)

/-- Totalized scheduled qubit. For inactive slots the value is irrelevant. -/
def surfaceASTScheduleQubit
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1)
    (k : Fin (surfaceASTParams d hd3 hodd).numStab) (slot : Nat) :
    Fin (surfaceASTParams d hd3 hodd).n :=
  let q := SurfaceCodeAST.scheduleQubit d k.val slot
  if hq : q < (surfaceASTParams d hd3 hodd).n then
    ⟨q, hq⟩
  else
    ⟨0, (surfaceASTParams d hd3 hodd).hn⟩

/-- Scheduled Pauli is derived from the recursive code at the scheduled qubit. -/
def surfaceASTSchedulePauli
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1)
    (k : Fin (surfaceASTParams d hd3 hodd).numStab) (slot : Nat) : Pauli :=
  SurfaceCodeAST.scheduledPauli d k.val slot

/-- The recursive NZ schedule as an assertion-language symbol. -/
def surfaceASTScheduleFamily
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    ScheduleFamilySymbol (surfaceASTParams d hd3 hodd) where
  name := "surface.ast.nz"
  distance := d
  active := surfaceASTScheduleActive d hd3 hodd
  qubit := surfaceASTScheduleQubit d hd3 hodd
  pauli := surfaceASTSchedulePauli d hd3 hodd
  maxSlots := hookWeightBound
  active_lt_max := by
    intro k slot h
    unfold surfaceASTScheduleActive at h
    simp only [decide_eq_true_eq] at h
    exact Nat.lt_of_lt_of_le h.1 (kindOrderRC_length_le_four d (classifyStab d k.val))

/-- Assertion-language formula: generated family agrees with the parameter table. -/
def surfaceASTCodeAgreementF
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    Formula (surfaceASTParams d hd3 hodd) [] :=
  stabilizerFamilyAgreementF (surfaceASTStabilizerFamily d hd3 hodd)

/-- Assertion-language formula: recursive NZ schedule agrees with the code rows. -/
def surfaceASTScheduleAgreementF
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    Formula (surfaceASTParams d hd3 hodd) [] :=
  scheduleFamilyAgreementF
    (surfaceASTStabilizerFamily d hd3 hodd)
    (surfaceASTScheduleFamily d hd3 hodd)

/-- Assertion-language formula: generated back-action branches are uniformly
    bounded by the schedule's local support bound. -/
def surfaceASTBackActionWeightF
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    Formula (surfaceASTParams d hd3 hodd) [] :=
  scheduleBackActionWeightF (surfaceASTScheduleFamily d hd3 hodd)

/-- A compact first-order assertion bundle for the generated code/schedule. -/
def surfaceASTStaticObligationsF
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    Formula (surfaceASTParams d hd3 hodd) [] :=
  .and (surfaceASTCodeAgreementF d hd3 hodd)
    (.and (surfaceASTScheduleAgreementF d hd3 hodd)
      (surfaceASTBackActionWeightF d hd3 hodd))

/-- A closed formula family over the parametric QStab layer.  The nontrivial
    barrier invariant will replace this `top` smoke invariant once the
    recursive barrier AST is connected. -/
def surfaceASTParamTopF : ParamFormula surfaceASTParamQStab :=
  fun _d _hd => Formula.top

/-- Constant-size parametric demonic proof schema over the generated program
    family.  It is checked once as a rule schema, then instantiated at any
    legal distance by elaboration. -/
noncomputable def surfaceASTParamTopHavocCertificate :
    ParamHavocCertificate surfaceASTParamQStab surfaceASTParamTopF surfaceASTParamTopF where
  err0 := fun d hd i p _hp =>
    QHL.Source.Parametric.topErr0Certificate (surfaceASTParamQStab.elaborate d hd) i p
  errI := fun d hd i p _hp mf =>
    QHL.Source.Parametric.topErrICertificate (surfaceASTParamQStab.elaborate d hd) i p mf
  errII := fun d hd e mf =>
    QHL.Source.Parametric.topErrIICertificate (surfaceASTParamQStab.elaborate d hd) e mf
  errIII := fun d hd =>
    QHL.Source.Parametric.topErrIIICertificate (surfaceASTParamQStab.elaborate d hd)
  meas := fun d hd =>
    QHL.Source.Parametric.topMeasCertificate (surfaceASTParamQStab.elaborate d hd)

theorem surfaceASTParamTopHavoc_schema_size :
    surfaceASTParamTopHavocCertificate.schemaSize = 1 :=
  rfl

theorem surfaceASTParamTopHavoc_instantiated_size
    (d : Nat) (hd : surfaceASTParamQStab.Valid d) :
    (surfaceASTParamTopHavocCertificate.instantiate d hd).size = 1 :=
  rfl

theorem surfaceASTParamTopHavoc_sound :
    ParamHavocHoare surfaceASTParamQStab surfaceASTParamTopF surfaceASTParamTopF :=
  surfaceASTParamTopHavocCertificate.sound

/-- Concrete QStab program lines generated from the recursive AST stabilizers. -/
def surfaceASTQStabProgramString (d : Nat) : List String :=
  (List.finRange (numStabFormula d)).map fun k =>
    "Prop " ++ surfaceAstRowString d k.val

/-- The d=3 fixed QStab program, rendered as stabilizer measurements. -/
def surfaceASTD3QStabProgramString : List String :=
  surfaceASTQStabProgramString 3

/- The following examples are generated by Lean reduction, not hand-written
   tables. They keep the AST frontend tied to concrete stabilizer syntax. -/

/-- info: true -/
#guard_msgs in
#eval surfaceAstRowsString 3 == surfaceMkRowsString 3 (by decide)

/-- info: true -/
#guard_msgs in
#eval surfaceAstRowsString 4 == surfaceMkRowsString 4 (by decide)

/-- info: true -/
#guard_msgs in
#eval surfaceAstRowsString 5 == surfaceMkRowsString 5 (by decide)

/-- info: true -/
#guard_msgs in
#eval surfaceNZScheduleSlots 3 == surfaceNZKindOrderSlots 3

/-- info: true -/
#guard_msgs in
#eval surfaceNZScheduleSlots 5 == surfaceNZKindOrderSlots 5

/-- info: true -/
#guard_msgs in
#eval surfaceNZScheduleSlots 7 == surfaceNZKindOrderSlots 7

/-- Syntactic Surface/NZ frontend obligations. These are not Hoare rules; they
    are the static family-generation side of the proof object. -/
inductive SurfaceASTObligation where
  | codeRecursive
  | scheduleRecursive
  | paramsGenerated
  | qstabProgramFixed
  | codeAgreementFormula
  | scheduleAgreementFormula
  | backActionGenerated
  | demonicHoare
  deriving DecidableEq

/-- Constant-size derivation skeleton for the recursive frontend obligations.
    Each constructor names a verifier-known syntactic step. -/
inductive SurfaceASTObligationDerivation
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTObligation -> Type where
  | codeRecursive :
      SurfaceCodeAST.canonical.body = SurfaceCodeAST.surfaceBody ->
      SurfaceASTObligationDerivation d hd3 hodd .codeRecursive
  | scheduleRecursive :
      SurfaceCodeAST.nzSchedule.body = SurfaceCodeAST.nzScheduleBody ->
      SurfaceASTObligationDerivation d hd3 hodd .scheduleRecursive
  | paramsGenerated :
      (surfaceASTParams d hd3 hodd).stabilizers =
        mkSurfaceStabilizers d (pos_of_ge_three hd3) ->
      SurfaceASTObligationDerivation d hd3 hodd .paramsGenerated
  | qstabProgramFixed :
      (forall c : QECParams.Coord (surfaceASTParams d hd3 hodd),
        (surfaceASTProgram d hd3 hodd).currentStab c = c.x) ->
      SurfaceASTObligationDerivation d hd3 hodd .qstabProgramFixed
  | codeAgreementFormula :
      SurfaceASTObligationDerivation d hd3 hodd .codeAgreementFormula
  | scheduleAgreementFormula :
      SurfaceASTObligationDerivation d hd3 hodd .scheduleAgreementFormula
  | backActionGenerated :
      (forall s e,
        e ∈ (surfaceASTParams d hd3 hodd).backActionSet s <->
          e ∈ mkSurfaceHookErrors d (pos_of_ge_three hd3) hodd s) ->
      SurfaceASTObligationDerivation d hd3 hodd .backActionGenerated
  | demonicHoare :
      HavocCertificate
        (surfaceASTProgram d hd3 hodd)
        (Formula.top (P := surfaceASTParams d hd3 hodd))
        (Formula.top (P := surfaceASTParams d hd3 hodd)) ->
      SurfaceASTObligationDerivation d hd3 hodd .demonicHoare

namespace SurfaceASTObligationDerivation

def size {d : Nat} {hd3 : 3 <= d} {hodd : d % 2 = 1}
    {k : SurfaceASTObligation} :
    SurfaceASTObligationDerivation d hd3 hodd k -> Nat
  | .codeRecursive _ => 1
  | .scheduleRecursive _ => 1
  | .paramsGenerated _ => 1
  | .qstabProgramFixed _ => 1
  | .codeAgreementFormula => 1
  | .scheduleAgreementFormula => 1
  | .backActionGenerated _ => 1
  | .demonicHoare h => 1 + h.size

end SurfaceASTObligationDerivation

def surfaceASTCodeRecursiveDerivation
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTObligationDerivation d hd3 hodd .codeRecursive :=
  .codeRecursive rfl

def surfaceASTScheduleRecursiveDerivation
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTObligationDerivation d hd3 hodd .scheduleRecursive :=
  .scheduleRecursive rfl

def surfaceASTParamsGeneratedDerivation
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTObligationDerivation d hd3 hodd .paramsGenerated :=
  .paramsGenerated rfl

def surfaceASTProgramFixedDerivation
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTObligationDerivation d hd3 hodd .qstabProgramFixed :=
  .qstabProgramFixed (surfaceASTProgram_currentStab d hd3 hodd)

def surfaceASTBackActionGeneratedDerivation
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTObligationDerivation d hd3 hodd .backActionGenerated :=
  .backActionGenerated (by
    intro s e
    rfl)

noncomputable def topErr0Certificate {P : QECParams} (prog : QStabProgram P)
    (i : Fin P.n) (p : Pauli) :
    Certificate prog (Formula.top (P := P)) (.err0 i p) (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErr0 prog i p)
    (Certificate.err0 (Formula.top (P := P)) i p)
    (Entails.refl (Formula.top (P := P)))

noncomputable def topErrICertificate {P : QECParams} (prog : QStabProgram P)
    (i : Fin P.n) (p : Pauli) (mf : Bool) :
    Certificate prog (Formula.top (P := P)) (.errI i p mf) (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErrI prog i p mf)
    (Certificate.errI (Formula.top (P := P)) i p mf)
    (Entails.refl (Formula.top (P := P)))

noncomputable def topErrIICertificate {P : QECParams} (prog : QStabProgram P)
    (e : ErrorVec P.n) (mf : Bool) :
    Certificate prog (Formula.top (P := P)) (.errII e mf) (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErrII prog e mf)
    (Certificate.errII (Formula.top (P := P)) e mf)
    (Entails.refl (Formula.top (P := P)))

noncomputable def topErrIIICertificate {P : QECParams} (prog : QStabProgram P) :
    Certificate prog (Formula.top (P := P)) .errIII (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpErrIII prog)
    (Certificate.errIII (Formula.top (P := P)))
    (Entails.refl (Formula.top (P := P)))

noncomputable def topMeasCertificate {P : QECParams} (prog : QStabProgram P) :
    Certificate prog (Formula.top (P := P)) .meas (Formula.top (P := P)) :=
  Certificate.consequence
    (Entails.topWpMeasFor prog)
    (Certificate.meas (Formula.top (P := P)))
    (Entails.refl (Formula.top (P := P)))

/-- A real checked demonic Hoare derivation over the fixed generated program.
    This is the nondeterministic proof-shell used by the nontrivial barrier
    invariant once all static AST obligations are discharged. -/
noncomputable def surfaceASTTopHavocCertificate
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    HavocCertificate
      (surfaceASTProgram d hd3 hodd)
      (Formula.top (P := surfaceASTParams d hd3 hodd))
      (Formula.top (P := surfaceASTParams d hd3 hodd)) :=
  HavocCertificate.havocStep
    (fun i p _hp => topErr0Certificate (surfaceASTProgram d hd3 hodd) i p)
    (fun i p _hp mf => topErrICertificate (surfaceASTProgram d hd3 hodd) i p mf)
    (fun e mf => topErrIICertificate (surfaceASTProgram d hd3 hodd) e mf)
    (topErrIIICertificate (surfaceASTProgram d hd3 hodd))
    (topMeasCertificate (surfaceASTProgram d hd3 hodd))

noncomputable def surfaceASTDemonicHoareDerivation
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTObligationDerivation d hd3 hodd .demonicHoare :=
  .demonicHoare (surfaceASTTopHavocCertificate d hd3 hodd)

theorem surfaceASTDemonicHoare_size
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    (surfaceASTDemonicHoareDerivation d hd3 hodd).size = 2 :=
  rfl

/-- Single build-gated canonical package for the recursive frontend. -/
structure SurfaceASTParametricPackage
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) where
  codeAST : SurfaceCodeAST.CodeFn
  scheduleAST : SurfaceCodeAST.ScheduleFn
  programAST : ParamQStabProgramAST
  params : QECParams
  program : QStabProgram params
  stabilizers : StabilizerFamilySymbol params
  schedule : ScheduleFamilySymbol params
  staticObligations : Formula params []
  codeRecursive : SurfaceASTObligationDerivation d hd3 hodd .codeRecursive
  scheduleRecursive : SurfaceASTObligationDerivation d hd3 hodd .scheduleRecursive
  paramsGenerated : SurfaceASTObligationDerivation d hd3 hodd .paramsGenerated
  programFixed : SurfaceASTObligationDerivation d hd3 hodd .qstabProgramFixed
  backActionGenerated : SurfaceASTObligationDerivation d hd3 hodd .backActionGenerated
  demonicHoare : SurfaceASTObligationDerivation d hd3 hodd .demonicHoare

noncomputable def surfaceASTParametricPackage
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    SurfaceASTParametricPackage d hd3 hodd where
  codeAST := SurfaceCodeAST.canonical
  scheduleAST := SurfaceCodeAST.nzSchedule
  programAST := surfaceASTParamQStabAST
  params := surfaceASTParams d hd3 hodd
  program := surfaceASTProgram d hd3 hodd
  stabilizers := surfaceASTStabilizerFamily d hd3 hodd
  schedule := surfaceASTScheduleFamily d hd3 hodd
  staticObligations := surfaceASTStaticObligationsF d hd3 hodd
  codeRecursive := surfaceASTCodeRecursiveDerivation d hd3 hodd
  scheduleRecursive := surfaceASTScheduleRecursiveDerivation d hd3 hodd
  paramsGenerated := surfaceASTParamsGeneratedDerivation d hd3 hodd
  programFixed := surfaceASTProgramFixedDerivation d hd3 hodd
  backActionGenerated := surfaceASTBackActionGeneratedDerivation d hd3 hodd
  demonicHoare := surfaceASTDemonicHoareDerivation d hd3 hodd

theorem surfaceASTPackage_demonicHoare_constant_size
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1) :
    (surfaceASTParametricPackage d hd3 hodd).demonicHoare.size = 2 :=
  rfl

theorem surfaceASTPackage_program_fixed
    (d : Nat) (hd3 : 3 <= d) (hodd : d % 2 = 1)
    (c : QECParams.Coord (surfaceASTParametricPackage d hd3 hodd).params) :
    (surfaceASTParametricPackage d hd3 hodd).program.currentStab c = c.x :=
  rfl

/--
info: ["Prop ZZIZZIIII", "Prop IXXIXXIII", "Prop IIIXXIXXI", "Prop IIIIZZIZZ", "Prop XXIIIIIII", "Prop IIZIIZIII",
  "Prop IIIZIIZII", "Prop IIIIIIIXX"]
-/
#guard_msgs in
#eval surfaceASTD3QStabProgramString

#print axioms surfaceASTParametricPackage
#print axioms surfaceASTTopHavocCertificate
#print axioms surfaceASTParamTopHavocCertificate
#print axioms surfaceASTParamTopHavoc_sound

end QHL.Source.Examples.SurfaceASTCanonical
