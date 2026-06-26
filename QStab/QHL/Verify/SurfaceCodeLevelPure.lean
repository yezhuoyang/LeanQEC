import QStab.QHL.Verify.SurfacePureAssembly

/-!
# Pure code-level assembly helpers for Surface distance

This file contains prover-side assembly only.  It introduces no new logic rules
and does not use the evaluator/checker as a distance proof.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

/-! ## Support covers for the closed logical operators -/

/-- Cover for `logicalX d`: enumerate the first column, `i -> d*i + 0`. -/
def logicalXSupportCover (dist : Nat) : STerm 1 .nat :=
  SC.closed (NatArithmetic.gridIdxLeft (.natLit dist) rowVar1 (.natLit 0))

/-- Cover for `logicalZ d`: enumerate the top row, `i -> d*0 + i`. -/
def logicalZSupportCover (dist : Nat) : STerm 1 .nat :=
  SC.closed (NatArithmetic.gridIdxLeft (.natLit dist) (.natLit 0) rowVar1)

def logicalXSupportGuard (dist : Nat) : Term 1 .bool :=
  .eqNat (NatArithmetic.colOf rowVar1 (.natLit dist)) (.natLit 0)

def logicalZSupportGuard (dist : Nat) : Term 1 .bool :=
  .eqNat (NatArithmetic.rowOf rowVar1 (.natLit dist)) (.natLit 0)

def pauliNeqOfEqLeft {arity : Nat} {Γ : List (SFormula arity)}
    (a b c : STerm arity .pauli) :
    SFormula.Deriv Γ (.eqPauli a b) ->
      SFormula.Deriv Γ (.not (.eqPauli b c)) ->
        SFormula.Deriv Γ (.not (.eqPauli a c)) :=
  fun hab hbc =>
    .notIntro <|
      let hac : SFormula.Deriv (.eqPauli a c :: Γ) (.eqPauli a c) := .assumption
      let hba : SFormula.Deriv (.eqPauli a c :: Γ) (.eqPauli b a) :=
        .eqPauliSymm a b hab.weakenContext
      let hbc' : SFormula.Deriv (.eqPauli a c :: Γ) (.eqPauli b c) :=
        .eqPauliTrans b a c hba hac
      .notElim hbc' hbc.weakenContext

def nonIOfEqPauliLit {arity : Nat} {Γ : List (SFormula arity)}
    (E : STerm arity .stab) (q : STerm arity .nat) (p : Pauli)
    (hp : decide (p = Pauli.I) = false) :
    SFormula.Deriv Γ (.eqPauli (.stabAt E q) (SC.p p)) ->
      SFormula.Deriv Γ (SFormula.nonIAt E q) :=
  fun hEntry =>
    pauliNeqOfEqLeft
      (.stabAt E q)
      (SC.p p)
      (SC.p Pauli.I)
      hEntry
      (.pauliNeqLit p Pauli.I hp)

def logicalXSlotWitness (dist : Nat) : Term 1 .nat :=
  NatArithmetic.gridIdxLeft (.natLit dist) rowVar1 (.natLit 0)

def logicalZSlotWitness (dist : Nat) : Term 1 .nat :=
  NatArithmetic.gridIdxLeft (.natLit dist) (.natLit 0) rowVar1

def logicalXSlotGuard (dist : Nat) : Term 1 .bool :=
  .eqNat (NatArithmetic.colOf (logicalXSlotWitness dist) (.natLit dist)) (.natLit 0)

def logicalZSlotGuard (dist : Nat) : Term 1 .bool :=
  .eqNat (NatArithmetic.rowOf (logicalZSlotWitness dist) (.natLit dist)) (.natLit 0)

theorem oddDistance_pos_decision (D : OddSurfaceDistance) :
    decide (0 < D.distance) = true := by
  cases D with
  | mk index =>
      simp [OddSurfaceDistance.distance, oddDistance]

theorem oddDistance_pred_lt_decision (D : OddSurfaceDistance) :
    decide (D.distance - 1 < D.distance) = true := by
  cases D with
  | mk index =>
      simp [OddSurfaceDistance.distance, oddDistance]

def logicalXSlotWitnessPure (dist : Nat) :
    SFormula.PureNatTerm (logicalXSlotWitness dist) :=
  SFormula.PureNatTerm.gridIdxLeft
    (SFormula.PureNatTerm.nat (arity := 1) dist)
    (SFormula.PureNatTerm.var (arity := 1) ⟨0, by decide⟩)
    (SFormula.PureNatTerm.nat (arity := 1) 0)

def logicalZSlotWitnessPure (dist : Nat) :
    SFormula.PureNatTerm (logicalZSlotWitness dist) :=
  SFormula.PureNatTerm.gridIdxLeft
    (SFormula.PureNatTerm.nat (arity := 1) dist)
    (SFormula.PureNatTerm.nat (arity := 1) 0)
    (SFormula.PureNatTerm.var (arity := 1) ⟨0, by decide⟩)

def logicalXSlotInRangeDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
      (SFormula.witnessLt
        (SC.closed (logicalXSlotWitness D.distance))
        (SC.n (arity := 1) (nQubits D.distance))) :=
  let rowLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.closed rowVar1) (SC.n D.distance)) :=
    .hyp (by simp [SFormula.boundNatLt, SFormula.boundNat, rowVar1, STerm.weaken,
      STerm.lift, SC.n, SC.closed, Term.lift])
  let colLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.n (arity := 1) 0) (SC.n D.distance)) :=
    .closedNatLt 0 D.distance (oddDistance_pos_decision D)
  .gridIdxLeftLtSquare D.distance rowVar1 (.natLit 0) rowLt colLt

def logicalXSlotRowEqDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
      (.eqNat
        (SC.closed (NatArithmetic.rowOf (logicalXSlotWitness D.distance) (.natLit D.distance)))
        (SC.closed rowVar1)) :=
  let rowLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.closed rowVar1) (SC.n D.distance)) :=
    .hyp (by simp [SFormula.boundNatLt, SFormula.boundNat, rowVar1, STerm.weaken,
      STerm.lift, SC.n, SC.closed, Term.lift])
  let colLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.n (arity := 1) 0) (SC.n D.distance)) :=
    .closedNatLt 0 D.distance (oddDistance_pos_decision D)
  .gridIdxLeftDivEq D.distance rowVar1 (.natLit 0) rowLt colLt

def logicalXSlotColEqDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
      (.eqNat
        (SC.closed (NatArithmetic.colOf (logicalXSlotWitness D.distance) (.natLit D.distance)))
        (SC.n (arity := 1) 0)) :=
  let rowLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.closed rowVar1) (SC.n D.distance)) :=
    .hyp (by simp [SFormula.boundNatLt, SFormula.boundNat, rowVar1, STerm.weaken,
      STerm.lift, SC.n, SC.closed, Term.lift])
  let colLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.n (arity := 1) 0) (SC.n D.distance)) :=
    .closedNatLt 0 D.distance (oddDistance_pos_decision D)
  .gridIdxLeftModEq D.distance rowVar1 (.natLit 0) rowLt colLt

def logicalZSlotInRangeDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
      (SFormula.witnessLt
        (SC.closed (logicalZSlotWitness D.distance))
        (SC.n (arity := 1) (nQubits D.distance))) :=
  let rowLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.n (arity := 1) 0) (SC.n D.distance)) :=
    .closedNatLt 0 D.distance (oddDistance_pos_decision D)
  let colLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.closed rowVar1) (SC.n D.distance)) :=
    .hyp (by simp [SFormula.boundNatLt, SFormula.boundNat, rowVar1, STerm.weaken,
      STerm.lift, SC.n, SC.closed, Term.lift])
  .gridIdxLeftLtSquare D.distance (.natLit 0) rowVar1 rowLt colLt

def logicalZSlotRowEqDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
      (.eqNat
        (SC.closed (NatArithmetic.rowOf (logicalZSlotWitness D.distance) (.natLit D.distance)))
        (SC.n (arity := 1) 0)) :=
  let rowLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.n (arity := 1) 0) (SC.n D.distance)) :=
    .closedNatLt 0 D.distance (oddDistance_pos_decision D)
  let colLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.closed rowVar1) (SC.n D.distance)) :=
    .hyp (by simp [SFormula.boundNatLt, SFormula.boundNat, rowVar1, STerm.weaken,
      STerm.lift, SC.n, SC.closed, Term.lift])
  .gridIdxLeftDivEq D.distance (.natLit 0) rowVar1 rowLt colLt

def logicalZSlotColEqDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
      (.eqNat
        (SC.closed (NatArithmetic.colOf (logicalZSlotWitness D.distance) (.natLit D.distance)))
        (SC.closed rowVar1)) :=
  let rowLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.n (arity := 1) 0) (SC.n D.distance)) :=
    .closedNatLt 0 D.distance (oddDistance_pos_decision D)
  let colLt :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
        (SFormula.witnessLt (SC.closed rowVar1) (SC.n D.distance)) :=
    .hyp (by simp [SFormula.boundNatLt, SFormula.boundNat, rowVar1, STerm.weaken,
      STerm.lift, SC.n, SC.closed, Term.lift])
  .gridIdxLeftModEq D.distance (.natLit 0) rowVar1 rowLt colLt

/-- The first-column support of `logicalX d` hits every row label. -/
def logicalXSupportSurjectiveDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] <|
      SFormula.supportSurjectiveF
        (SC.n D.distance)
        (SC.n (nQubits D.distance))
        (SC.closed (logicalX D.distance))
        (gridRowOf D.distance) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let E := SC.closed (logicalX D.distance)
  let rowOf := gridRowOf D.distance
  refine SFormula.Deriv.allNatLtIntroBounded (SC.n D.distance)
    (SFormula.supportSurjectiveBody n E rowOf) ?_
  let q : STerm 1 .nat := SC.closed (logicalXSlotWitness D.distance)
  let A : SFormula 2 :=
    .and
      (SFormula.nonIAt E.weaken.weaken (SFormula.boundNat (arity := 1)))
      (.eqNat (rowOf.lift 1) ((SFormula.boundNat (arity := 0)).weaken))
  refine SFormula.Deriv.existsNatLtIntroTerm n.weaken A q ?_ ?_
  · exact logicalXSlotInRangeDeriv D
  · refine SFormula.Deriv.applyNatSubstitutionBeta (logicalXSlotWitness D.distance) A
      (logicalXSlotWitnessPure D.distance) ?_
    have hNonI :
        SFormula.Deriv
          [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
          (SFormula.nonIAt E.weaken q) := by
      have hNat := logicalXSlotColEqDeriv D
      have hGuard0 := SFormula.Deriv.eqNatBoolTrue
        (NatArithmetic.colOf (logicalXSlotWitness D.distance) (.natLit D.distance))
        (.natLit 0) hNat
      have hGuard :
          SFormula.Deriv [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
            (.eqBool
              (SC.closed (Term.instantiateTopNat (logicalXSlotWitness D.distance)
                (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))))
              (SC.b true)) := by
        simpa [logicalXSlotGuard, logicalXSlotWitness, Formula.qVar, NatArithmetic.colOf,
          Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
          Term.weakenVar, SC.closed, SC.b] using hGuard0
      have hEntry := SFormula.Deriv.stabAtClosedIteLamEqThen
        (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))
        (.pauliLit Pauli.X)
        (.pauliLit Pauli.I)
        (logicalXSlotWitness D.distance)
        (logicalXSlotWitnessPure D.distance)
        hGuard
      have hEntry' :
          SFormula.Deriv [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
            (.eqPauli (.stabAt E.weaken q) (SC.p Pauli.X)) := by
        simpa [E, q, logicalX, Formula.qVar, SC.closed, SC.p,
          STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
          Term.weaken, Term.lift, Term.weakenVar] using hEntry
      exact nonIOfEqPauliLit E.weaken q Pauli.X (by decide) hEntry'
    have hRowEq := logicalXSlotRowEqDeriv D
    simpa [A, SFormula.instantiateTopNat, SFormula.instantiateNatAt,
      SFormula.nonIAt, SFormula.boundNat, STerm.instantiateTopNat, STerm.instantiateNatAt,
      STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.p, rowOf, E, q,
      gridRowOf, logicalXSlotWitness, rowVar1, NatArithmetic.rowOf,
      NatArithmetic.gridIdxLeft, logicalX, Formula.qVar] using
        SFormula.Deriv.andIntro hNonI hRowEq

/-- Pure lower-bound half for `logicalX`: at least `d` non-identity entries. -/
def logicalXWeightLowerDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] <|
      .not (.weightLe
        (SC.n (nQubits D.distance))
        (SC.closed (logicalX D.distance))
        (SC.n (D.distance - 1))) :=
  .finiteSurjectiveWeightLower
    (SC.n (nQubits D.distance))
    (SC.closed (logicalX D.distance))
    (SC.n (D.distance - 1))
    (SC.n D.distance)
    (gridRowOf D.distance)
    (logicalXSupportSurjectiveDeriv D)
    (.closedNatLt (D.distance - 1) D.distance (oddDistance_pred_lt_decision D))

/-- The top-row support of `logicalZ d` hits every column label. -/
def logicalZSupportSurjectiveDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] <|
      SFormula.supportSurjectiveF
        (SC.n D.distance)
        (SC.n (nQubits D.distance))
        (SC.closed (logicalZ D.distance))
        (gridColOf D.distance) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let E := SC.closed (logicalZ D.distance)
  let rowOf := gridColOf D.distance
  refine SFormula.Deriv.allNatLtIntroBounded (SC.n D.distance)
    (SFormula.supportSurjectiveBody n E rowOf) ?_
  let q : STerm 1 .nat := SC.closed (logicalZSlotWitness D.distance)
  let A : SFormula 2 :=
    .and
      (SFormula.nonIAt E.weaken.weaken (SFormula.boundNat (arity := 1)))
      (.eqNat (rowOf.lift 1) ((SFormula.boundNat (arity := 0)).weaken))
  refine SFormula.Deriv.existsNatLtIntroTerm n.weaken A q ?_ ?_
  · exact logicalZSlotInRangeDeriv D
  · refine SFormula.Deriv.applyNatSubstitutionBeta (logicalZSlotWitness D.distance) A
      (logicalZSlotWitnessPure D.distance) ?_
    have hNonI :
        SFormula.Deriv
          [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
          (SFormula.nonIAt E.weaken q) := by
      have hNat := logicalZSlotRowEqDeriv D
      have hGuard0 := SFormula.Deriv.eqNatBoolTrue
        (NatArithmetic.rowOf (logicalZSlotWitness D.distance) (.natLit D.distance))
        (.natLit 0) hNat
      have hGuard :
          SFormula.Deriv [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
            (.eqBool
              (SC.closed (Term.instantiateTopNat (logicalZSlotWitness D.distance)
                (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0))))
              (SC.b true)) := by
        simpa [logicalZSlotGuard, logicalZSlotWitness, Formula.qVar, NatArithmetic.rowOf,
          Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
          Term.weakenVar, SC.closed, SC.b] using hGuard0
      have hEntry := SFormula.Deriv.stabAtClosedIteLamEqThen
        (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0))
        (.pauliLit Pauli.Z)
        (.pauliLit Pauli.I)
        (logicalZSlotWitness D.distance)
        (logicalZSlotWitnessPure D.distance)
        hGuard
      have hEntry' :
          SFormula.Deriv [SFormula.boundNatLt (SC.n (arity := 0) D.distance)]
            (.eqPauli (.stabAt E.weaken q) (SC.p Pauli.Z)) := by
        simpa [E, q, logicalZ, Formula.qVar, SC.closed, SC.p,
          STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
          Term.weaken, Term.lift, Term.weakenVar] using hEntry
      exact nonIOfEqPauliLit E.weaken q Pauli.Z (by decide) hEntry'
    have hColEq := logicalZSlotColEqDeriv D
    simpa [A, SFormula.instantiateTopNat, SFormula.instantiateNatAt,
      SFormula.nonIAt, SFormula.boundNat, STerm.instantiateTopNat, STerm.instantiateNatAt,
      STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.p, rowOf, E, q,
      gridColOf, logicalZSlotWitness, rowVar1, NatArithmetic.colOf,
      NatArithmetic.gridIdxLeft, logicalZ, Formula.qVar] using
        SFormula.Deriv.andIntro hNonI hColEq

/-- Pure lower-bound half for `logicalZ`: at least `d` non-identity entries. -/
def logicalZWeightLowerDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] <|
      .not (.weightLe
        (SC.n (nQubits D.distance))
        (SC.closed (logicalZ D.distance))
        (SC.n (D.distance - 1))) :=
  .finiteSurjectiveWeightLower
    (SC.n (nQubits D.distance))
    (SC.closed (logicalZ D.distance))
    (SC.n (D.distance - 1))
    (SC.n D.distance)
    (gridColOf D.distance)
    (logicalZSupportSurjectiveDeriv D)
    (.closedNatLt (D.distance - 1) D.distance (oddDistance_pred_lt_decision D))

/-- Pure derivation that the first-column cover hits every non-identity entry of
`logicalX d`. -/
def logicalXSupportCoveredDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] <|
      supportCoveredF
        (SC.n (nQubits D.distance))
        (SC.closed (logicalX D.distance))
        (SC.n D.distance)
        (logicalXSupportCover D.distance) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let E := SC.closed (logicalX D.distance)
  let w := SC.n (arity := 0) D.distance
  let cover := logicalXSupportCover D.distance
  refine SFormula.Deriv.allNatLtIntroBounded n (supportCoveredBody E w cover) ?_
  refine SFormula.Deriv.impIntro ?_
  let qTerm : Term 1 .nat := rowVar1
  let lamCond : Term 2 .bool :=
    .eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0)
  let condAtQ : STerm 1 .bool := SC.closed (Term.instantiateTopNat qTerm lamCond)
  let target : SFormula 1 :=
    .existsNatLt w.weaken
      (.eqNat (cover.lift 1) ((SFormula.boundNat (arity := 0)).weaken))
  have trueBranch :
      SFormula.Deriv
        (.eqBool condAtQ (SC.b true) ::
          SFormula.nonIAt E.weaken SFormula.boundNat ::
          SFormula.boundNatLt n :: [])
        target := by
    let ctx :=
      [.eqBool condAtQ (SC.b true),
        SFormula.nonIAt E.weaken SFormula.boundNat,
        SFormula.boundNatLt n]
    let qLt : SFormula.Deriv ctx
        (SFormula.witnessLt (SC.closed qTerm) (SC.n (nQubits D.distance))) :=
      .hyp (by right; right; left)
    let condTrue : SFormula.Deriv ctx (.eqBool condAtQ (SC.b true)) :=
      .assumption
    let colZero : SFormula.Deriv ctx
        (.eqBool (SC.closed (logicalXSupportGuard D.distance)) (SC.b true)) := by
      simpa [condAtQ, lamCond, qTerm, logicalXSupportGuard, Term.instantiateTopNat,
        Term.instantiateNatAt, Term.weaken, Term.weakenVar, Formula.qVar,
        rowVar1, NatArithmetic.colOf, SC.closed]
        using condTrue
    let rowLt : SFormula.Deriv ctx
        (SFormula.witnessLt
          (SC.closed (NatArithmetic.rowOf qTerm (.natLit D.distance)))
          (SC.n D.distance)) :=
      .divLtOfLtSquare D.distance qTerm qLt
    refine .existsNatLtIntroTerm _ _ (SC.closed (NatArithmetic.rowOf qTerm (.natLit D.distance)))
      rowLt ?_
    refine .applyNatSubstitutionBeta (NatArithmetic.rowOf qTerm (.natLit D.distance)) _
      (SFormula.PureNatTerm.div (SFormula.PureNatTerm.var ⟨0, by decide⟩)
        (SFormula.PureNatTerm.nat D.distance)) ?_
    have eqGrid : SFormula.Deriv ctx
        (.eqNat
          (SC.closed (NatArithmetic.gridIdxLeft (.natLit D.distance)
            (NatArithmetic.rowOf qTerm (.natLit D.distance)) (.natLit 0)))
          (SC.closed qTerm)) :=
      .gridIdxLeftDivModEqOfCol D.distance (.natLit 0) qTerm qLt colZero
    simpa [target, supportCoveredBody, logicalXSupportCover, cover, w, qTerm,
      logicalXSupportGuard, SFormula.instantiateTopNat, SFormula.instantiateNatAt,
      SFormula.weaken, SFormula.lift, STerm.instantiateNatAt, STerm.weaken,
      STerm.instantiateTopNat, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.b, rowVar1,
      SFormula.boundNat,
      NatArithmetic.rowOf, NatArithmetic.colOf, NatArithmetic.gridIdxLeft]
      using eqGrid
  have falseBranch :
      SFormula.Deriv
        (.eqBool condAtQ (SC.b false) ::
          SFormula.nonIAt E.weaken SFormula.boundNat ::
          SFormula.boundNatLt n :: [])
        target := by
    let ctx :=
      [.eqBool condAtQ (SC.b false),
        SFormula.nonIAt E.weaken SFormula.boundNat,
        SFormula.boundNatLt n]
    let condFalse : SFormula.Deriv ctx (.eqBool condAtQ (SC.b false)) :=
      .assumption
    let nonI : SFormula.Deriv ctx (SFormula.nonIAt E.weaken SFormula.boundNat) :=
      .hyp (by right; left)
    let entryI : SFormula.Deriv ctx
        (.eqPauli (.stabAt E.weaken SFormula.boundNat) (SC.p Pauli.I)) := by
      have h :=
        SFormula.Deriv.stabAtClosedIteLamEqElse lamCond
          (Term.pauliLit (arity := 2) Pauli.X)
          (Term.pauliLit (arity := 2) Pauli.I)
          qTerm
          (SFormula.PureNatTerm.var ⟨0, by decide⟩)
          condFalse
      simpa [E, logicalX, qTerm, lamCond, condAtQ, logicalXSupportGuard, SFormula.nonIAt,
        SFormula.boundNat, SC.closed, SC.p, SC.b, STerm.weaken, STerm.lift,
        Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
        Term.weakenVar, rowVar1, NatArithmetic.colOf]
        using h
    exact SFormula.Deriv.botElim (SFormula.Deriv.notElim entryI nonI)
  simpa [target, supportCoveredBody, n, E, w, cover, qTerm, condAtQ] using
    SFormula.Deriv.boolCases condAtQ target trueBranch falseBranch

/-- Pure upper-bound half for `logicalX`: its support is covered by `d` entries. -/
def logicalXWeightUpperPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.weightLe
        (SC.n (nQubits D.distance))
        (SC.closed (logicalX D.distance))
        (SC.n D.distance)) :=
  .weightLeBySupport
    (SC.n (nQubits D.distance))
    (SC.closed (logicalX D.distance))
    (SC.n D.distance)
    (logicalXSupportCover D.distance)
    (.core (logicalXSupportCoveredDeriv D))

/-- Pure derivation that the top-row cover hits every non-identity entry of
`logicalZ d`. -/
def logicalZSupportCoveredDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] <|
      supportCoveredF
        (SC.n (nQubits D.distance))
        (SC.closed (logicalZ D.distance))
        (SC.n D.distance)
        (logicalZSupportCover D.distance) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let E := SC.closed (logicalZ D.distance)
  let w := SC.n (arity := 0) D.distance
  let cover := logicalZSupportCover D.distance
  refine SFormula.Deriv.allNatLtIntroBounded n (supportCoveredBody E w cover) ?_
  refine SFormula.Deriv.impIntro ?_
  let qTerm : Term 1 .nat := rowVar1
  let lamCond : Term 2 .bool :=
    .eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0)
  let condAtQ : STerm 1 .bool := SC.closed (Term.instantiateTopNat qTerm lamCond)
  let target : SFormula 1 :=
    .existsNatLt w.weaken
      (.eqNat (cover.lift 1) ((SFormula.boundNat (arity := 0)).weaken))
  have trueBranch :
      SFormula.Deriv
        (.eqBool condAtQ (SC.b true) ::
          SFormula.nonIAt E.weaken SFormula.boundNat ::
          SFormula.boundNatLt n :: [])
        target := by
    let ctx :=
      [.eqBool condAtQ (SC.b true),
        SFormula.nonIAt E.weaken SFormula.boundNat,
        SFormula.boundNatLt n]
    let qLt : SFormula.Deriv ctx
        (SFormula.witnessLt (SC.closed qTerm) (SC.n (nQubits D.distance))) :=
      .hyp (by right; right; left)
    let condTrue : SFormula.Deriv ctx (.eqBool condAtQ (SC.b true)) :=
      .assumption
    let rowZero : SFormula.Deriv ctx
        (.eqBool (SC.closed (logicalZSupportGuard D.distance)) (SC.b true)) := by
      simpa [condAtQ, lamCond, qTerm, logicalZSupportGuard, Term.instantiateTopNat,
        Term.instantiateNatAt, Term.weaken, Term.weakenVar, Formula.qVar,
        rowVar1, NatArithmetic.rowOf, SC.closed]
        using condTrue
    let colLt : SFormula.Deriv ctx
        (SFormula.witnessLt
          (SC.closed (NatArithmetic.colOf qTerm (.natLit D.distance)))
          (SC.n D.distance)) :=
      .modLtOfLtSquare D.distance qTerm qLt
    refine .existsNatLtIntroTerm _ _ (SC.closed (NatArithmetic.colOf qTerm (.natLit D.distance)))
      colLt ?_
    refine .applyNatSubstitutionBeta (NatArithmetic.colOf qTerm (.natLit D.distance)) _
      (SFormula.PureNatTerm.mod (SFormula.PureNatTerm.var ⟨0, by decide⟩)
        (SFormula.PureNatTerm.nat D.distance)) ?_
    have eqGrid : SFormula.Deriv ctx
        (.eqNat
          (SC.closed (NatArithmetic.gridIdxLeft (.natLit D.distance)
            (.natLit 0) (NatArithmetic.colOf qTerm (.natLit D.distance))))
          (SC.closed qTerm)) :=
      .gridIdxLeftDivModEqOfRow D.distance (.natLit 0) qTerm qLt rowZero
    simpa [target, supportCoveredBody, logicalZSupportCover, cover, w, qTerm,
      logicalZSupportGuard, SFormula.instantiateTopNat, SFormula.instantiateNatAt,
      SFormula.weaken, SFormula.lift, STerm.instantiateNatAt, STerm.weaken,
      STerm.instantiateTopNat, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.b, rowVar1,
      SFormula.boundNat,
      NatArithmetic.rowOf, NatArithmetic.colOf, NatArithmetic.gridIdxLeft]
      using eqGrid
  have falseBranch :
      SFormula.Deriv
        (.eqBool condAtQ (SC.b false) ::
          SFormula.nonIAt E.weaken SFormula.boundNat ::
          SFormula.boundNatLt n :: [])
        target := by
    let ctx :=
      [.eqBool condAtQ (SC.b false),
        SFormula.nonIAt E.weaken SFormula.boundNat,
        SFormula.boundNatLt n]
    let condFalse : SFormula.Deriv ctx (.eqBool condAtQ (SC.b false)) :=
      .assumption
    let nonI : SFormula.Deriv ctx (SFormula.nonIAt E.weaken SFormula.boundNat) :=
      .hyp (by right; left)
    let entryI : SFormula.Deriv ctx
        (.eqPauli (.stabAt E.weaken SFormula.boundNat) (SC.p Pauli.I)) := by
      have h :=
        SFormula.Deriv.stabAtClosedIteLamEqElse lamCond
          (Term.pauliLit (arity := 2) Pauli.Z)
          (Term.pauliLit (arity := 2) Pauli.I)
          qTerm
          (SFormula.PureNatTerm.var ⟨0, by decide⟩)
          condFalse
      simpa [E, logicalZ, qTerm, lamCond, condAtQ, logicalZSupportGuard, SFormula.nonIAt,
        SFormula.boundNat, SC.closed, SC.p, SC.b, STerm.weaken, STerm.lift,
        Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
        Term.weakenVar, rowVar1, NatArithmetic.rowOf]
        using h
    exact SFormula.Deriv.botElim (SFormula.Deriv.notElim entryI nonI)
  simpa [target, supportCoveredBody, n, E, w, cover, qTerm, condAtQ] using
    SFormula.Deriv.boolCases condAtQ target trueBranch falseBranch

/-- Pure upper-bound half for `logicalZ`: its support is covered by `d` entries. -/
def logicalZWeightUpperPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.weightLe
        (SC.n (nQubits D.distance))
        (SC.closed (logicalZ D.distance))
        (SC.n D.distance)) :=
  .weightLeBySupport
    (SC.n (nQubits D.distance))
    (SC.closed (logicalZ D.distance))
    (SC.n D.distance)
    (logicalZSupportCover D.distance)
    (.core (logicalZSupportCoveredDeriv D))

/-- Pure exact-weight derivation for `logicalX d`: upper and lower support bounds. -/
def logicalXWeightExactPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (weightExactF D.distance (logicalX D.distance))) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let E := SC.closed (logicalX D.distance)
  let upper : SFormula 0 := .weightLe n E (SC.n D.distance)
  let lower : SFormula 0 := .not (.weightLe n E (SC.n (D.distance - 1)))
  let hAnd : SFormula.Deriv [upper, lower] (.and upper lower) :=
    .andIntro (.hyp (by simp)) (.hyp (by simp))
  simpa [closedSF, weightExactF, n, E, upper, lower] using
    PureFamilyDerivA.cut2 hAnd
      (logicalXWeightUpperPure D)
      (PureFamilyDerivA.core (logicalXWeightLowerDeriv D))

/-- Pure exact-weight derivation for `logicalZ d`: upper and lower support bounds. -/
def logicalZWeightExactPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (weightExactF D.distance (logicalZ D.distance))) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let E := SC.closed (logicalZ D.distance)
  let upper : SFormula 0 := .weightLe n E (SC.n D.distance)
  let lower : SFormula 0 := .not (.weightLe n E (SC.n (D.distance - 1)))
  let hAnd : SFormula.Deriv [upper, lower] (.and upper lower) :=
    .andIntro (.hyp (by simp)) (.hyp (by simp))
  simpa [closedSF, weightExactF, n, E, upper, lower] using
    PureFamilyDerivA.cut2 hAnd
      (logicalZWeightUpperPure D)
      (PureFamilyDerivA.core (logicalZWeightLowerDeriv D))

/-- Pure derivation of the code-level exact-weight conjunct for the two closed
logical operators. -/
def logicalWeightsPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalWeightsF D.distance)) := by
  let XW : SFormula 0 := closedSF (weightExactF D.distance (logicalX D.distance))
  let ZW : SFormula 0 := closedSF (weightExactF D.distance (logicalZ D.distance))
  let hAnd : SFormula.Deriv [XW, ZW] (.and XW ZW) :=
    .andIntro (.hyp (by simp)) (.hyp (by simp))
  simpa [closedSF, logicalWeightsF, XW, ZW] using
    PureFamilyDerivA.cut2 hAnd
      (logicalXWeightExactPure D)
      (logicalZWeightExactPure D)

/-! ## Logical-pair anticommutation at the grid origin -/

/-- The origin qubit, written in the grid-index syntax so the object-logic grid
rules can prove both row and column guards. -/
def logicalOriginQ (dist : Nat) : Term 0 .nat :=
  NatArithmetic.gridIdxLeft (.natLit dist) (.natLit 0) (.natLit 0)

def logicalOriginQPure (dist : Nat) :
    SFormula.PureNatTerm (logicalOriginQ dist) :=
  SFormula.PureNatTerm.gridIdxLeft
    (SFormula.PureNatTerm.nat (arity := 0) dist)
    (SFormula.PureNatTerm.nat (arity := 0) 0)
    (SFormula.PureNatTerm.nat (arity := 0) 0)

def logicalOriginInRangeDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv []
      (SFormula.witnessLt
        (SC.closed (logicalOriginQ D.distance))
        (SC.n (arity := 0) (nQubits D.distance))) :=
  .gridIdxLeftLtSquare D.distance (.natLit 0) (.natLit 0)
    (.closedNatLt 0 D.distance (oddDistance_pos_decision D))
    (.closedNatLt 0 D.distance (oddDistance_pos_decision D))

def logicalOriginRowEqDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv []
      (.eqNat
        (SC.closed (NatArithmetic.rowOf (logicalOriginQ D.distance)
          (.natLit D.distance)))
        (SC.n (arity := 0) 0)) :=
  .gridIdxLeftDivEq D.distance (.natLit 0) (.natLit 0)
    (.closedNatLt 0 D.distance (oddDistance_pos_decision D))
    (.closedNatLt 0 D.distance (oddDistance_pos_decision D))

def logicalOriginColEqDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv []
      (.eqNat
        (SC.closed (NatArithmetic.colOf (logicalOriginQ D.distance)
          (.natLit D.distance)))
        (SC.n (arity := 0) 0)) :=
  .gridIdxLeftModEq D.distance (.natLit 0) (.natLit 0)
    (.closedNatLt 0 D.distance (oddDistance_pos_decision D))
    (.closedNatLt 0 D.distance (oddDistance_pos_decision D))

def logicalXOriginEntryDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv []
      (.eqPauli
        (.stabAt (SC.closed (logicalX D.distance)) (SC.closed (logicalOriginQ D.distance)))
        (SC.p (arity := 0) Pauli.X)) := by
  have hNat := logicalOriginColEqDeriv D
  have hGuard0 := SFormula.Deriv.eqNatBoolTrue
    (NatArithmetic.colOf (logicalOriginQ D.distance) (.natLit D.distance))
    (.natLit 0) hNat
  have hGuard :
      SFormula.Deriv []
        (.eqBool
          (SC.closed (Term.instantiateTopNat (logicalOriginQ D.distance)
            (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))))
          (SC.b (arity := 0) true)) := by
    simpa [logicalOriginQ, Formula.qVar, NatArithmetic.colOf, Term.instantiateTopNat,
      Term.instantiateNatAt, Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.b]
      using hGuard0
  have hEntry := SFormula.Deriv.stabAtClosedIteLamEqThen
    (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.X)
    (.pauliLit Pauli.I)
    (logicalOriginQ D.distance)
    (logicalOriginQPure D.distance)
    hGuard
  simpa [logicalX, logicalOriginQ, Formula.qVar, SC.closed, SC.p,
    Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
    Term.weakenVar] using hEntry

def logicalZOriginEntryDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv []
      (.eqPauli
        (.stabAt (SC.closed (logicalZ D.distance)) (SC.closed (logicalOriginQ D.distance)))
        (SC.p (arity := 0) Pauli.Z)) := by
  have hNat := logicalOriginRowEqDeriv D
  have hGuard0 := SFormula.Deriv.eqNatBoolTrue
    (NatArithmetic.rowOf (logicalOriginQ D.distance) (.natLit D.distance))
    (.natLit 0) hNat
  have hGuard :
      SFormula.Deriv []
        (.eqBool
          (SC.closed (Term.instantiateTopNat (logicalOriginQ D.distance)
            (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0))))
          (SC.b (arity := 0) true)) := by
    simpa [logicalOriginQ, Formula.qVar, NatArithmetic.rowOf, Term.instantiateTopNat,
      Term.instantiateNatAt, Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.b]
      using hGuard0
  have hEntry := SFormula.Deriv.stabAtClosedIteLamEqThen
    (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.Z)
    (.pauliLit Pauli.I)
    (logicalOriginQ D.distance)
    (logicalOriginQPure D.distance)
    hGuard
  simpa [logicalZ, logicalOriginQ, Formula.qVar, SC.closed, SC.p,
    Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
    Term.weakenVar] using hEntry

def logicalXZOriginAnticommDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv []
      (.eqBool
        (.anticommutes
          (.stabAt (SC.closed (logicalX D.distance)) (SC.closed (logicalOriginQ D.distance)))
          (.stabAt (SC.closed (logicalZ D.distance)) (SC.closed (logicalOriginQ D.distance))))
        (SC.b (arity := 0) true)) := by
  let x0 : STerm 0 .pauli :=
    .stabAt (SC.closed (logicalX D.distance)) (SC.closed (logicalOriginQ D.distance))
  let z0 : STerm 0 .pauli :=
    .stabAt (SC.closed (logicalZ D.distance)) (SC.closed (logicalOriginQ D.distance))
  have hAntiLit :
      SFormula.Deriv []
        (.eqBool
          (.anticommutes (SC.p (arity := 0) Pauli.X) (SC.p (arity := 0) Pauli.Z))
          (SC.b (arity := 0) true)) := by
    simpa using SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z
  simpa [x0, z0] using
    SFormula.Deriv.anticommutesTransport
      x0 (SC.p (arity := 0) Pauli.X)
      z0 (SC.p (arity := 0) Pauli.Z)
      (SC.b (arity := 0) true)
      (logicalXOriginEntryDeriv D)
      (logicalZOriginEntryDeriv D)
      hAntiLit

def logicalXGuardAtBound (dist : Nat) : STerm 1 .bool :=
  SC.closed (.eqNat (NatArithmetic.colOf rowVar1 (.natLit dist)) (.natLit 0))

def logicalZGuardAtBound (dist : Nat) : STerm 1 .bool :=
  SC.closed (.eqNat (NatArithmetic.rowOf rowVar1 (.natLit dist)) (.natLit 0))

/-- Purely arithmetic/boolean fact: the only qubit whose column and row guards
are both zero is the grid origin.  This is a prover-side premise discharged by
the scoped `arithBool` rule; it contains no stabilizer or Pauli atom. -/
def logicalOriginOverlapBody (D : OddSurfaceDistance) : SFormula 1 :=
    .imp
      (.and
        (.eqBool (logicalXGuardAtBound D.distance) (SC.b true))
        (.eqBool (logicalZGuardAtBound D.distance) (SC.b true)))
      (.eqNat SFormula.boundNat (SC.closed (logicalOriginQ D.distance)).weaken)

def logicalOriginOverlapF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (nQubits D.distance)) (logicalOriginOverlapBody D)

theorem logicalOriginOverlap_fragment (D : OddSurfaceDistance) :
    arithBoolFragment (logicalOriginOverlapF D) = true := by
  rfl

theorem logicalOriginOverlap_valid (D : OddSurfaceDistance) :
    forall (rho : Env 0) (E : PartialStabilizer),
      (logicalOriginOverlapF D).eval Surface.code.body (D.distance + 2) rho E =
        some true := by
  intro rho E
  simp only [logicalOriginOverlapF, SFormula.eval, SC.n, STerm.eval, Term.eval,
    bind, Option.bind]
  apply allNatLt_complete
  intro q hq
  have hpos : 0 < D.distance := by
    cases D with
    | mk index =>
        simp [OddSurfaceDistance.distance, oddDistance]
  have horigin : D.distance * 0 + 0 = 0 := by simp
  simp [logicalOriginOverlapBody, logicalXGuardAtBound, logicalZGuardAtBound,
    SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, rowVar1,
    NatArithmetic.rowOf, NatArithmetic.colOf, logicalOriginQ, NatArithmetic.gridIdxLeft,
    bind, Option.bind, Env.cons]
  by_cases hcol : q % D.distance = 0
  · by_cases hrow : q / D.distance = 0
    · have hq0 : q = 0 := by
        have hdivmod := Nat.div_add_mod q D.distance
        rw [hrow, hcol] at hdivmod
        omega
      subst q
      simp [SFormula.boundNat, logicalOriginQ, NatArithmetic.gridIdxLeft, SC.closed,
        STerm.eval, STerm.weaken, STerm.lift, Term.eval, Term.weaken, Term.lift,
        Term.weakenVar, Env.cons]
    · by_cases hAnte : D.distance = 0 ∨ q < D.distance
      · exfalso
        cases hAnte with
        | inl hd0 => omega
        | inr hqLt =>
            exact hrow (Nat.div_eq_of_lt hqLt)
      · simp [hcol, hAnte]
  · simp [hcol]

def logicalOriginOverlapPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (logicalOriginOverlapF D) :=
  .arithBool (logicalOriginOverlapF D)
    (logicalOriginOverlap_fragment D)
    (logicalOriginOverlap_valid D)

def logicalXBoundEntryIDeriv {Γ : List (SFormula 1)} (D : OddSurfaceDistance) :
    SFormula.Deriv Γ (.eqBool (logicalXGuardAtBound D.distance) (SC.b false)) ->
      SFormula.Deriv Γ
        (.eqPauli
          (.stabAt (SC.closed (logicalX D.distance)).weaken SFormula.boundNat)
          (SC.p (arity := 1) Pauli.I)) := by
  intro hFalse
  let cond : Term 2 .bool := .eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0)
  have hEntry := SFormula.Deriv.stabAtClosedIteLamEqElse cond
    (Term.pauliLit (arity := 2) Pauli.X)
    (Term.pauliLit (arity := 2) Pauli.I)
    rowVar1
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by
      simpa [logicalXGuardAtBound, cond, rowVar1, Formula.qVar, NatArithmetic.colOf,
        Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.weakenVar,
        SC.closed] using hFalse)
  simpa [logicalX, cond, rowVar1, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
    Term.weaken, Term.lift, Term.weakenVar, NatArithmetic.colOf] using hEntry

def logicalZBoundEntryIDeriv {Γ : List (SFormula 1)} (D : OddSurfaceDistance) :
    SFormula.Deriv Γ (.eqBool (logicalZGuardAtBound D.distance) (SC.b false)) ->
      SFormula.Deriv Γ
        (.eqPauli
          (.stabAt (SC.closed (logicalZ D.distance)).weaken SFormula.boundNat)
          (SC.p (arity := 1) Pauli.I)) := by
  intro hFalse
  let cond : Term 2 .bool := .eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0)
  have hEntry := SFormula.Deriv.stabAtClosedIteLamEqElse cond
    (Term.pauliLit (arity := 2) Pauli.Z)
    (Term.pauliLit (arity := 2) Pauli.I)
    rowVar1
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by
      simpa [logicalZGuardAtBound, cond, rowVar1, Formula.qVar, NatArithmetic.rowOf,
        Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.weakenVar,
        SC.closed] using hFalse)
  simpa [logicalZ, cond, rowVar1, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
    Term.weaken, Term.lift, Term.weakenVar, NatArithmetic.rowOf] using hEntry

def logicalXZCommutesExceptOriginDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [logicalOriginOverlapF D]
      (.allNatLt (SC.n (nQubits D.distance))
        (.imp (.not (.eqNat SFormula.boundNat
              (SC.closed (logicalOriginQ D.distance)).weaken))
          (SFormula.localCommutesAt
            (SC.closed (logicalX D.distance)).weaken
            (SC.closed (logicalZ D.distance)).weaken
            SFormula.boundNat))) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let LX := SC.closed (logicalX D.distance)
  let LZ := SC.closed (logicalZ D.distance)
  let q0 := SC.closed (logicalOriginQ D.distance)
  let body : SFormula 1 :=
    .imp (.not (.eqNat SFormula.boundNat q0.weaken))
      (SFormula.localCommutesAt LX.weaken LZ.weaken SFormula.boundNat)
  refine SFormula.Deriv.allNatLtIntroBounded n body ?_
  refine SFormula.Deriv.impIntro ?_
  let ctx : List (SFormula 1) :=
    [.not (.eqNat SFormula.boundNat q0.weaken),
      SFormula.boundNatLt n,
      (logicalOriginOverlapF D).weaken]
  let target : SFormula 1 :=
    SFormula.localCommutesAt LX.weaken LZ.weaken SFormula.boundNat
  let xGuard := logicalXGuardAtBound D.distance
  let zGuard := logicalZGuardAtBound D.distance
  have falseX :
      SFormula.Deriv (.eqBool xGuard (SC.b false) :: ctx) target := by
    let ctxF := .eqBool xGuard (SC.b false) :: ctx
    have hFalse : SFormula.Deriv ctxF (.eqBool xGuard (SC.b false)) := .assumption
    have hEntryI :
        SFormula.Deriv ctxF
          (.eqPauli (.stabAt LX.weaken SFormula.boundNat) (SC.p Pauli.I)) :=
      logicalXBoundEntryIDeriv D hFalse
    simpa [target, LX, LZ] using
      SFormula.Deriv.localCommutesOfLeftI LX.weaken LZ.weaken SFormula.boundNat hEntryI
  have trueX :
      SFormula.Deriv (.eqBool xGuard (SC.b true) :: ctx) target := by
    let ctxT := .eqBool xGuard (SC.b true) :: ctx
    have falseZ :
        SFormula.Deriv (.eqBool zGuard (SC.b false) :: ctxT) target := by
      let ctxZF := .eqBool zGuard (SC.b false) :: ctxT
      have hFalse : SFormula.Deriv ctxZF (.eqBool zGuard (SC.b false)) := .assumption
      have hEntryI :
          SFormula.Deriv ctxZF
            (.eqPauli (.stabAt LZ.weaken SFormula.boundNat) (SC.p Pauli.I)) :=
        logicalZBoundEntryIDeriv D hFalse
      simpa [target, LX, LZ] using
        SFormula.Deriv.localCommutesOfRightI LX.weaken LZ.weaken SFormula.boundNat hEntryI
    have trueZ :
        SFormula.Deriv (.eqBool zGuard (SC.b true) :: ctxT) target := by
      let ctxZT := .eqBool zGuard (SC.b true) :: ctxT
      have hNotEq : SFormula.Deriv ctxZT (.not (.eqNat SFormula.boundNat q0.weaken)) :=
        .hyp (by simp [ctxZT, ctxT, ctx])
      have hOverlap :
          SFormula.Deriv ctxZT ((logicalOriginOverlapF D).weaken) :=
        .hyp (by simp [ctxZT, ctxT, ctx])
      have hBoundLt : SFormula.Deriv ctxZT (SFormula.boundNatLt n) :=
        .hyp (by simp [ctxZT, ctxT, ctx])
      have hAll :
          SFormula.Deriv ctxZT
            (.allNatLt n.weaken ((logicalOriginOverlapBody D).lift 1)) := by
        simpa [logicalOriginOverlapF, SFormula.weaken, STerm.weaken] using hOverlap
      have hApply := SFormula.Deriv.allNatLtElim
        n.weaken
        ((logicalOriginOverlapBody D).lift 1)
        SFormula.boundNat
        hAll
        hBoundLt
      have hBody :
          SFormula.Deriv ctxZT (logicalOriginOverlapBody D) :=
        SFormula.Deriv.applyNatBoundNatBeta (logicalOriginOverlapBody D) hApply
      have hX : SFormula.Deriv ctxZT (.eqBool xGuard (SC.b true)) :=
        .hyp (by simp [ctxZT, ctxT, ctx])
      have hZ : SFormula.Deriv ctxZT (.eqBool zGuard (SC.b true)) :=
        .assumption
      have hEq : SFormula.Deriv ctxZT (.eqNat SFormula.boundNat q0.weaken) :=
        SFormula.Deriv.mp hBody (SFormula.Deriv.andIntro hX hZ)
      exact SFormula.Deriv.botElim (SFormula.Deriv.notElim hEq hNotEq)
    exact SFormula.Deriv.boolCases zGuard target trueZ falseZ
  simpa [n, body, target, xGuard, zGuard, LX, LZ, q0] using
    SFormula.Deriv.boolCases xGuard target trueX falseX

def logicalXZNoncommDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [logicalOriginOverlapF D]
      (.not (.commutesUpTo
        (SC.n (nQubits D.distance))
        (SC.closed (logicalX D.distance))
        (SC.closed (logicalZ D.distance)))) := by
  let n := SC.n (arity := 0) (nQubits D.distance)
  let LX := SC.closed (logicalX D.distance)
  let LZ := SC.closed (logicalZ D.distance)
  let q0 := SC.closed (logicalOriginQ D.distance)
  exact SFormula.Deriv.noncommutesOfSingleAnti n LX LZ q0
    (logicalOriginInRangeDeriv D).weakenContext
    (logicalXZOriginAnticommDeriv D).weakenContext
    (logicalXZCommutesExceptOriginDeriv D)

def logicalXZNoncommPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.not (.commutesUpTo
        (SC.n (nQubits D.distance))
        (SC.closed (logicalX D.distance))
        (SC.closed (logicalZ D.distance)))) :=
  .cut1 (logicalXZNoncommDeriv D) (logicalOriginOverlapPure D)

/-! ## Code-level assembly from generated-row facts

The exact-weight and logical `X/Z` anticommutation pieces above are closed pure
derivations.  The remaining code-level content is precisely the generated-row
geometry: pairwise commutation of recursive rows, and normalization of the two
logical operators by every recursive row.  The following assembly lemmas expose
that frontier as explicit pure-derivation inputs rather than hiding it in an
evaluator or checker. -/

def logicalPairPureFromNormalizers (D : OddSurfaceDistance)
    (xNorm :
      PureFamilyDerivA Surface.code.body (D.distance + 2)
        (closedSF (logicalXNormalizesOddF D)))
    (zNorm :
      PureFamilyDerivA Surface.code.body (D.distance + 2)
        (closedSF (logicalZNormalizesOddF D))) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalPairF D.distance)) := by
  let XN : SFormula 0 := closedSF (logicalXNormalizesOddF D)
  let ZN : SFormula 0 := closedSF (logicalZNormalizesOddF D)
  let Anti : SFormula 0 := closedSF (logicalAnticommutesOddF D)
  let ZNAnti : SFormula 0 := .and ZN Anti
  let hAnd : SFormula.Deriv [XN, ZNAnti] (.and XN ZNAnti) :=
    .andIntro (.hyp (by simp)) (.hyp (by simp))
  have hAnti :
      PureFamilyDerivA Surface.code.body (D.distance + 2) Anti := by
    simpa [Anti, closedSF, logicalAnticommutesOddF, Formula.anticommutesUpTo] using
      logicalXZNoncommPure D
  simpa [XN, ZN, Anti, ZNAnti, closedSF, logicalPairF, logicalXNormalizesOddF,
    logicalZNormalizesOddF, logicalAnticommutesOddF, Formula.logicalPairCandidateUpTo,
    Formula.anticommutesUpTo] using
      PureFamilyDerivA.cut2 hAnd xNorm
        (PureFamilyDerivA.cut2
          (by
            let ZN : SFormula 0 := closedSF (logicalZNormalizesOddF D)
            let Anti : SFormula 0 := closedSF (logicalAnticommutesOddF D)
            exact (SFormula.Deriv.andIntro (.hyp (by simp)) (.hyp (by simp)) :
              SFormula.Deriv [ZN, Anti] (.and ZN Anti)))
          zNorm hAnti)

def codeLevelPureFromGeneratedRows (D : OddSurfaceDistance)
    (rows :
      PureFamilyDerivA Surface.code.body (D.distance + 2)
        (closedSF (rowsCommuteOddF D)))
    (xNorm :
      PureFamilyDerivA Surface.code.body (D.distance + 2)
        (closedSF (logicalXNormalizesOddF D)))
    (zNorm :
      PureFamilyDerivA Surface.code.body (D.distance + 2)
        (closedSF (logicalZNormalizesOddF D))) :
    PureFamilyDeriv Surface.code.body (D.distance + 2) (codeLevelSF D) := by
  let Rows : SFormula 0 := closedSF (rowsCommuteOddF D)
  let Pair : SFormula 0 := closedSF (logicalPairF D.distance)
  let Weights : SFormula 0 := closedSF (logicalWeightsF D.distance)
  let PairWeights : SFormula 0 := .and Pair Weights
  let hAnd : SFormula.Deriv [Rows, PairWeights] (.and Rows PairWeights) :=
    .andIntro (.hyp (by simp)) (.hyp (by simp))
  refine .arity0 ?_
  simpa [codeLevelSF, surfaceCodeLevelOddF, surfaceCodeLevelF, rowsCommuteOddF,
    Rows, Pair, Weights, PairWeights, closedSF] using
    PureFamilyDerivA.cut2 hAnd rows
      (PureFamilyDerivA.cut2
        (by
          let Pair : SFormula 0 := closedSF (logicalPairF D.distance)
          let Weights : SFormula 0 := closedSF (logicalWeightsF D.distance)
          exact (SFormula.Deriv.andIntro (.hyp (by simp)) (.hyp (by simp)) :
            SFormula.Deriv [Pair, Weights] (.and Pair Weights)))
        (logicalPairPureFromNormalizers D xNorm zNorm)
        (logicalWeightsPure D))

end QHL.CodeLang.Surface.Verify
