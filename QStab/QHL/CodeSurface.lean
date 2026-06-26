import QStab.QHL.CodeNatArithmetic
import QStab.QHL.CodeStabBinder

/-! # Surface code in the code-level assertion language

This file ports the recursive Surface-code AST into `QHL.CodeLang`, the same
small functional language used by the five-qubit and repetition examples.

The proof objects below are derivations in `Formula.Deriv`; the checker only
sees:

* the recursive `CodeFn` AST,
* first-order formulas over bounded natural indices,
* Hoare-style logical rules for formulas (`and`, `imp`, bounded `forall`),
* atomic Pauli/stabilizer evaluations.

There is no import of the older Surface-specific semantic proof records.
-/

namespace QHL.CodeLang.Surface

open QHL.CodeLang

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-! ## Small AST combinators -/

private def q : Term 3 .nat := C.Entry.q
private def k : Term 3 .nat := C.Entry.k
private def d : Term 3 .nat := C.Entry.d

def n3 {arity : Nat} : Term arity .nat := .natLit 3
def n4 {arity : Nat} : Term arity .nat := .natLit 4
def n5 {arity : Nat} : Term arity .nat := .natLit 5

def bor3 {arity : Nat} (a b c : Term arity .bool) : Term arity .bool :=
  .or a (.or b c)

def band3 {arity : Nat} (a b c : Term arity .bool) : Term arity .bool :=
  .and a (.and b c)

def band4 {arity : Nat} (a b c d : Term arity .bool) : Term arity .bool :=
  .and a (band3 b c d)

def bnot {arity : Nat} (a : Term arity .bool) : Term arity .bool :=
  .not a

def le {arity : Nat} (a b : Term arity .nat) : Term arity .bool :=
  .leNat a b

def orEqSucc {arity : Nat} (x base : Term arity .nat) : Term arity .bool :=
  .or (.eqNat x base) (.eqNat x (.add base (.natLit 1)))

def orEqPair {arity : Nat} (x a b : Term arity .nat) : Term arity .bool :=
  .or (.eqNat x a) (.eqNat x b)

def gridIdx {arity : Nat}
    (dist row col : Term arity .nat) : Term arity .nat :=
  .add (.mul dist row) col

def numStab (dist : Nat) : Nat :=
  QHL.CodeLang.StabBinder.SFormula.gridNumStab dist

def nQubits (dist : Nat) : Nat :=
  dist * dist

def andList {arity : Nat} : List (Formula arity) -> Formula arity
  | [] => .top
  | A :: rest => rest.foldl (fun acc B => .and acc B) A

/-! ## Recursive Surface-code AST

The index order matches the existing rotated-surface layout:

* `(d-1)^2` bulk plaquettes in row-major order;
* top-X, right-Z, left-Z, bottom-X boundary checks.

The raw AST is executable at any natural numeral, because the evaluator is a
generic OCaml-style evaluator for `CodeFn`.  The canonical Surface API below
does not expose raw natural distances: a supported Surface distance is an
`OddSurfaceDistance`, i.e. `d = 2*m + 3`.  For `d < 5`, the AST uses the direct
local formula.  For larger odd `d`, the interior and promoted boundary checks
use `recCall (d-2) oldK`; only the new outer shell is generated locally.
-/

def baseEntry : Term 3 .pauli :=
  let row := .div q d
  let col := .mod q d
  let dm1 := .sub d (.natLit 1)
  let bulkCount := .mul dm1 dm1
  let r := .div k dm1
  let c := .mod k dm1
  let kind :=
    .ite (.eqNat (.mod (.add r c) (.natLit 2)) (.natLit 0))
      (.pauliLit Pauli.Z)
      (.pauliLit Pauli.X)
  let bulk :=
    .ite (band3 (orEqSucc row r) (orEqSucc col c) (.ltNat k bulkCount))
      kind
      (.pauliLit Pauli.I)
  let b := .sub k bulkCount
  let half := .div dm1 (.natLit 2)
  let topX :=
    .ite (band3 (.ltNat k (.sub (.mul d d) (.natLit 1))) (.eqNat row (.natLit 0))
        (orEqSucc col (.mul (.natLit 2) b)))
      (.pauliLit Pauli.X)
      (.pauliLit Pauli.I)
  let bbRight := .sub b half
  let rightZ :=
    .ite (.and (.eqNat col dm1) (orEqSucc row (.mul (.natLit 2) bbRight)))
      (.pauliLit Pauli.Z)
      (.pauliLit Pauli.I)
  let bbLeft := .sub b (.mul (.natLit 2) half)
  let leftZ :=
    .ite (.and (.eqNat col (.natLit 0))
        (orEqPair row (.add (.mul (.natLit 2) bbLeft) (.natLit 1))
          (.add (.mul (.natLit 2) bbLeft) (.natLit 2))))
      (.pauliLit Pauli.Z)
      (.pauliLit Pauli.I)
  let bbBottom := .sub b (.mul (.natLit 3) half)
  let bottomX :=
    .ite (.and (.eqNat row dm1)
        (orEqPair col (.add (.mul (.natLit 2) bbBottom) (.natLit 1))
          (.add (.mul (.natLit 2) bbBottom) (.natLit 2))))
      (.pauliLit Pauli.X)
      (.pauliLit Pauli.I)
  .ite (.ltNat k bulkCount) bulk
    (.ite (.ltNat b half) topX
      (.ite (.ltNat b (.mul (.natLit 2) half)) rightZ
        (.ite (.ltNat b (.mul (.natLit 3) half)) leftZ bottomX)))

def promotedBoundaryEntry
    (oldK : Term 3 .nat) (outer : Term 3 .bool) (kind : Pauli) :
    Term 3 .pauli :=
  let row := .div q d
  let col := .mod q d
  let innerD := .sub d (.natLit 2)
  let dm1 := .sub d (.natLit 1)
  let inside :=
    band4 (le (.natLit 1) row) (.ltNat row dm1) (le (.natLit 1) col) (.ltNat col dm1)
  let innerQ := .add (.mul (.sub row (.natLit 1)) innerD) (.sub col (.natLit 1))
  .ite inside
    (.stabAt (.recCall innerD oldK) innerQ)
    (.ite outer (.pauliLit kind) (.pauliLit Pauli.I))

def recursiveEntry : Term 3 .pauli :=
  let row := .div q d
  let col := .mod q d
  let dm1 := .sub d (.natLit 1)
  let bulkCount := .mul dm1 dm1
  let r := .div k dm1
  let c := .mod k dm1
  let innerD := .sub d (.natLit 2)
  let innerDm1 := .sub innerD (.natLit 1)
  let innerBulk := .mul innerDm1 innerDm1
  let innerHalf := .div innerDm1 (.natLit 2)
  let lastCell := .sub dm1 (.natLit 1)
  let interiorCell :=
    band4 (le (.natLit 1) r) (.ltNat r lastCell) (le (.natLit 1) c) (.ltNat c lastCell)
  let interiorK := .add (.mul (.sub r (.natLit 1)) innerDm1) (.sub c (.natLit 1))
  let inside :=
    band4 (le (.natLit 1) row) (.ltNat row dm1) (le (.natLit 1) col) (.ltNat col dm1)
  let innerQ := .add (.mul (.sub row (.natLit 1)) innerD) (.sub col (.natLit 1))
  let topB := .div (.sub c (.natLit 1)) (.natLit 2)
  let topCell :=
    band3 (.eqNat r (.natLit 0)) (.eqNat c (.add (.mul (.natLit 2) topB) (.natLit 1)))
      (.ltNat topB innerHalf)
  let topOuter :=
    .and (.eqNat row (.natLit 0)) (orEqSucc col (.add (.mul (.natLit 2) topB) (.natLit 1)))
  let topK := .add innerBulk topB
  let rightB := .div (.sub r (.natLit 1)) (.natLit 2)
  let rightCell :=
    band3 (.eqNat c lastCell) (.eqNat r (.add (.mul (.natLit 2) rightB) (.natLit 1)))
      (.ltNat rightB innerHalf)
  let rightOuter :=
    .and (.eqNat col dm1) (orEqSucc row (.add (.mul (.natLit 2) rightB) (.natLit 1)))
  let rightK := .add innerBulk (.add innerHalf rightB)
  let leftB := .div (.sub r (.natLit 2)) (.natLit 2)
  let leftCell :=
    band3 (.eqNat c (.natLit 0)) (.eqNat r (.add (.mul (.natLit 2) leftB) (.natLit 2)))
      (.ltNat leftB innerHalf)
  let leftOuter :=
    .and (.eqNat col (.natLit 0)) (orEqSucc row (.add (.mul (.natLit 2) leftB) (.natLit 2)))
  let leftK := .add innerBulk (.add (.mul (.natLit 2) innerHalf) leftB)
  let bottomB := .div (.sub c (.natLit 2)) (.natLit 2)
  let bottomCell :=
    band3 (.eqNat r lastCell) (.eqNat c (.add (.mul (.natLit 2) bottomB) (.natLit 2)))
      (.ltNat bottomB innerHalf)
  let bottomOuter :=
    .and (.eqNat row dm1) (orEqSucc col (.add (.mul (.natLit 2) bottomB) (.natLit 2)))
  let bottomK := .add innerBulk (.add (.mul (.natLit 3) innerHalf) bottomB)
  .ite (.ltNat k bulkCount)
    (.ite interiorCell
      (.ite inside (.stabAt (.recCall innerD interiorK) innerQ) (.pauliLit Pauli.I))
      (.ite topCell (promotedBoundaryEntry topK topOuter Pauli.X)
        (.ite rightCell (promotedBoundaryEntry rightK rightOuter Pauli.Z)
          (.ite leftCell (promotedBoundaryEntry leftK leftOuter Pauli.Z)
            (.ite bottomCell (promotedBoundaryEntry bottomK bottomOuter Pauli.X) baseEntry)))))
    baseEntry

/-- The canonical recursive Surface-code AST of type `Nat -> Nat -> Stabilizer`. -/
def body : Term 2 .stab :=
  .ite (.ltNat C.Code.d (n5 : Term 2 .nat))
    (.stabLam baseEntry)
    (.stabLam recursiveEntry)

def code : CodeFn where
  body := body

/-! ## Derived logical operators -/

def logicalZ (dist : Nat) : Term 0 .stab :=
  .stabLam <|
    .ite (.eqNat (.div Formula.qVar (.natLit dist)) (.natLit 0))
      (.pauliLit Pauli.Z)
      (.pauliLit Pauli.I)

def logicalX (dist : Nat) : Term 0 .stab :=
  .stabLam <|
    .ite (.eqNat (.mod Formula.qVar (.natLit dist)) (.natLit 0))
      (.pauliLit Pauli.X)
      (.pauliLit Pauli.I)

def weightExactF (dist : Nat) (L : Term 0 .stab) : Formula 0 :=
  .and
    (.weightLe (.natLit (nQubits dist)) L (.natLit dist))
    (.not (.weightLe (.natLit (nQubits dist)) L (.natLit (dist - 1))))

def logicalWeightsF (dist : Nat) : Formula 0 :=
  .and (weightExactF dist (logicalX dist)) (weightExactF dist (logicalZ dist))

def rowsCommuteF (dist : Nat) : Formula 0 :=
  Formula.codeRowsCommuteUpTo
    (.natLit (nQubits dist)) (.natLit (numStab dist)) (.natLit dist)

def logicalPairF (dist : Nat) : Formula 0 :=
  Formula.logicalPairCandidateUpTo
    (.natLit (nQubits dist)) (.natLit (numStab dist)) (.natLit dist)
    (logicalX dist) (logicalZ dist)

def oddDistance (m : Nat) : Nat :=
  2 * m + 3

/-- Canonical Surface distances.  There is intentionally no even-distance constructor. -/
structure OddSurfaceDistance where
  index : Nat
deriving Repr, DecidableEq

namespace OddSurfaceDistance

def distance (D : OddSurfaceDistance) : Nat :=
  oddDistance D.index

def d3 : OddSurfaceDistance := { index := 0 }
def d5 : OddSurfaceDistance := { index := 1 }
def d7 : OddSurfaceDistance := { index := 2 }

end OddSurfaceDistance

def surfaceCodeLevelF (dist : Nat) : Formula 0 :=
  .and (rowsCommuteF dist) (.and (logicalPairF dist) (logicalWeightsF dist))

def logicalZOdd (D : OddSurfaceDistance) : Term 0 .stab :=
  logicalZ D.distance

def logicalXOdd (D : OddSurfaceDistance) : Term 0 .stab :=
  logicalX D.distance

def rowsCommuteOddF (D : OddSurfaceDistance) : Formula 0 :=
  rowsCommuteF D.distance

def logicalPairOddF (D : OddSurfaceDistance) : Formula 0 :=
  logicalPairF D.distance

def logicalWeightsOddF (D : OddSurfaceDistance) : Formula 0 :=
  logicalWeightsF D.distance

def surfaceCodeLevelOddF (D : OddSurfaceDistance) : Formula 0 :=
  surfaceCodeLevelF D.distance

def logicalXNormalizesOddF (D : OddSurfaceDistance) : Formula 0 :=
  Formula.normalizesCodeUpTo
    (.natLit (nQubits D.distance)) (.natLit (numStab D.distance)) (.natLit D.distance)
    (logicalXOdd D)

def logicalZNormalizesOddF (D : OddSurfaceDistance) : Formula 0 :=
  Formula.normalizesCodeUpTo
    (.natLit (nQubits D.distance)) (.natLit (numStab D.distance)) (.natLit D.distance)
    (logicalZOdd D)

def logicalAnticommutesOddF (D : OddSurfaceDistance) : Formula 0 :=
  Formula.anticommutesUpTo (.natLit (nQubits D.distance)) (logicalXOdd D) (logicalZOdd D)

def logicalXWeightExactOddF (D : OddSurfaceDistance) : Formula 0 :=
  weightExactF D.distance (logicalXOdd D)

def logicalZWeightExactOddF (D : OddSurfaceDistance) : Formula 0 :=
  weightExactF D.distance (logicalZOdd D)

def boolHoldsF {arity : Nat} (b : Term arity .bool) : Formula arity :=
  .eqBool b (.boolLit true)

def rowVar1 : Term 1 .nat := .var ⟨0, by decide⟩
def leftRowVar2 : Term 2 .nat := .var ⟨1, by decide⟩
def rightRowVar2 : Term 2 .nat := .var ⟨0, by decide⟩

/-! ## Geometric lower-bound predicates

The distance lower bound should not enumerate all Pauli strings.  The geometric
argument is:

* an X-component normalizer that anticommutes with the top-row `Z` logical must
  have X-support in every grid row;
* an error with support in every row has weight at least `d`;
* the Z-component argument is the transpose: every column is occupied.

These predicates are still plain assertion-language formulas.  There is no new
primitive membership or path predicate here.
-/

def hasXComponent {arity : Nat} (p : Term arity .pauli) : Term arity .bool :=
  .anticommutes p (.pauliLit Pauli.Z)

def hasZComponent {arity : Nat} (p : Term arity .pauli) : Term arity .bool :=
  .anticommutes p (.pauliLit Pauli.X)

def xSupportAtF {arity : Nat} (E : Term arity .stab) (q : Term arity .nat) :
    Formula arity :=
  boolHoldsF (hasXComponent (.stabAt E q))

def zSupportAtF {arity : Nat} (E : Term arity .stab) (q : Term arity .nat) :
    Formula arity :=
  boolHoldsF (hasZComponent (.stabAt E q))

def colVar {arity : Nat} : Term (arity + 1) .nat :=
  .var ⟨0, Nat.succ_pos arity⟩

def xRowOccupiedAtF {arity : Nat} (dist : Nat)
    (E : Term arity .stab) (row : Term arity .nat) : Formula arity :=
  .not <| .allNatLt (.natLit dist) <|
    .not <| xSupportAtF E.weaken
      (gridIdx (.natLit dist) row.weaken colVar)

def xRowsOccupiedF (D : OddSurfaceDistance) (E : Term 0 .stab) : Formula 0 :=
  .allNatLt (.natLit D.distance) <|
    xRowOccupiedAtF D.distance E.weaken rowVar1

def zColOccupiedAtF {arity : Nat} (dist : Nat)
    (E : Term arity .stab) (col : Term arity .nat) : Formula arity :=
  .not <| .allNatLt (.natLit dist) <|
    .not <| zSupportAtF E.weaken
      (gridIdx (.natLit dist) colVar col.weaken)

def zColsOccupiedF (D : OddSurfaceDistance) (E : Term 0 .stab) : Formula 0 :=
  .allNatLt (.natLit D.distance) <|
    zColOccupiedAtF D.distance E.weaken rowVar1

def normalizesOddF (D : OddSurfaceDistance) (E : Term 0 .stab) : Formula 0 :=
  Formula.normalizesCodeUpTo
    (.natLit (nQubits D.distance)) (.natLit (numStab D.distance)) (.natLit D.distance) E

def xNontrivialNormalizerF (D : OddSurfaceDistance) (E : Term 0 .stab) : Formula 0 :=
  .and (normalizesOddF D E)
    (Formula.anticommutesUpTo (.natLit (nQubits D.distance)) E (logicalZOdd D))

def zNontrivialNormalizerF (D : OddSurfaceDistance) (E : Term 0 .stab) : Formula 0 :=
  .and (normalizesOddF D E)
    (Formula.anticommutesUpTo (.natLit (nQubits D.distance)) E (logicalXOdd D))

def xParityPropagationRowsF (D : OddSurfaceDistance) (E : Term 0 .stab) :
    Formula 0 :=
  .imp (xNontrivialNormalizerF D E) (xRowsOccupiedF D E)

def zParityPropagationColsF (D : OddSurfaceDistance) (E : Term 0 .stab) :
    Formula 0 :=
  .imp (zNontrivialNormalizerF D E) (zColsOccupiedF D E)

def xRowsOccupiedWeightLowerF (D : OddSurfaceDistance) (E : Term 0 .stab) :
    Formula 0 :=
  .imp (xRowsOccupiedF D E)
    (.not (.weightLe (.natLit (nQubits D.distance)) E (.natLit (D.distance - 1))))

def zColsOccupiedWeightLowerF (D : OddSurfaceDistance) (E : Term 0 .stab) :
    Formula 0 :=
  .imp (zColsOccupiedF D E)
    (.not (.weightLe (.natLit (nQubits D.distance)) E (.natLit (D.distance - 1))))

def xLowerBoundByGeometryF (D : OddSurfaceDistance) (E : Term 0 .stab) :
    Formula 0 :=
  .imp (xNontrivialNormalizerF D E)
    (.not (.weightLe (.natLit (nQubits D.distance)) E (.natLit (D.distance - 1))))

def zLowerBoundByGeometryF (D : OddSurfaceDistance) (E : Term 0 .stab) :
    Formula 0 :=
  .imp (zNontrivialNormalizerF D E)
    (.not (.weightLe (.natLit (nQubits D.distance)) E (.natLit (D.distance - 1))))

/-! ## Stabilizer-binder form of the lower-bound statement

The formulas above are closed-instance statements: the error `E` is a closed
stabilizer term.  The finite stabilizer binder lets us write the actual
distance-lower-bound shape:

`forall E : Stab[d*d], nontrivialNormalizer(E) -> weight(E) >= d`.

This section uses only the generic binder from `CodeStabBinder`; Surface
contributes formulas, not new syntax.
-/

namespace OpenStab

open QHL.CodeLang.StabBinder

def boolHoldsF {arity : Nat} (b : STerm arity .bool) : SFormula arity :=
  .eqBool b (SC.b true)

def hasXComponent {arity : Nat} (p : STerm arity .pauli) : STerm arity .bool :=
  .anticommutes p (SC.p Pauli.Z)

def hasZComponent {arity : Nat} (p : STerm arity .pauli) : STerm arity .bool :=
  .anticommutes p (SC.p Pauli.X)

def xSupportAtF {arity : Nat} (E : STerm arity .stab) (q : Term arity .nat) :
    SFormula arity :=
  boolHoldsF (hasXComponent (.stabAt E (.closed q)))

def zSupportAtF {arity : Nat} (E : STerm arity .stab) (q : Term arity .nat) :
    SFormula arity :=
  boolHoldsF (hasZComponent (.stabAt E (.closed q)))

def xRowOccupiedAtF {arity : Nat} (dist : Nat)
    (E : STerm arity .stab) (row : Term arity .nat) : SFormula arity :=
  .not <| .allNatLt (SC.n dist) <|
    .not <| xSupportAtF E.weaken
      (gridIdx (.natLit dist) row.weaken colVar)

def zColOccupiedAtF {arity : Nat} (dist : Nat)
    (E : STerm arity .stab) (col : Term arity .nat) : SFormula arity :=
  .not <| .allNatLt (SC.n dist) <|
    .not <| zSupportAtF E.weaken
      (gridIdx (.natLit dist) colVar col.weaken)

def xRowsOccupiedF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) <|
    xRowOccupiedAtF D.distance SC.bound.weaken rowVar1

def zColsOccupiedF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) <|
    zColOccupiedAtF D.distance SC.bound.weaken rowVar1

def normalizesOddF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (numStab D.distance)) <|
    .commutesUpTo (SC.n (nQubits D.distance))
      (.closed (Formula.codeRow (Term.natLit D.distance).weaken rowVar1))
      SC.bound.weaken

def anticommutesLogicalZF (D : OddSurfaceDistance) : SFormula 0 :=
  .not <|
    .commutesUpTo (SC.n (nQubits D.distance))
      SC.bound
      (.closed (logicalZOdd D))

def anticommutesLogicalXF (D : OddSurfaceDistance) : SFormula 0 :=
  .not <|
    .commutesUpTo (SC.n (nQubits D.distance))
      SC.bound
      (.closed (logicalXOdd D))

def xNontrivialNormalizerF (D : OddSurfaceDistance) : SFormula 0 :=
  .and (normalizesOddF D) (anticommutesLogicalZF D)

def zNontrivialNormalizerF (D : OddSurfaceDistance) : SFormula 0 :=
  .and (normalizesOddF D) (anticommutesLogicalXF D)

def xParityPropagationRowsF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (xNontrivialNormalizerF D) (xRowsOccupiedF D)

def zParityPropagationColsF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (zNontrivialNormalizerF D) (zColsOccupiedF D)

def rowCutNoXImpliesCommutesBody (D : OddSurfaceDistance) : SFormula 1 :=
  .imp
    (SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1)
    (.commutesUpTo (SC.n (nQubits D.distance))
      (SC.rowZCut D.distance rowVar1) SC.bound.weaken)

def colCutNoZImpliesCommutesBody (D : OddSurfaceDistance) : SFormula 1 :=
  .imp
    (SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1)
    (.commutesUpTo (SC.n (nQubits D.distance))
      (SC.colXCut D.distance rowVar1) SC.bound.weaken)

def rowCutNoXImpliesCommutesF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (rowCutNoXImpliesCommutesBody D)

def colCutNoZImpliesCommutesF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (colCutNoZImpliesCommutesBody D)

def xRowsOccupiedWeightLowerF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (xRowsOccupiedF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

def zColsOccupiedWeightLowerF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (zColsOccupiedF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

/-- Row projection used by the generic support-surjectivity counting rule.
    The input variable is a qubit index `q`; the output is `q / d`. -/
def gridRowOf (dist : Nat) : STerm 1 .nat :=
  SC.closed (NatArithmetic.rowOf rowVar1 (.natLit dist))

/-- Column projection used by the generic support-surjectivity counting rule.
    The input variable is a qubit index `q`; the output is `q % d`. -/
def gridColOf (dist : Nat) : STerm 1 .nat :=
  SC.closed (NatArithmetic.colOf rowVar1 (.natLit dist))

def xRowsSupportSurjectiveF (D : OddSurfaceDistance) : SFormula 0 :=
  SFormula.supportSurjectiveF
    (SC.n D.distance)
    (SC.n (nQubits D.distance))
    SC.bound
    (gridRowOf D.distance)

def zColsSupportSurjectiveF (D : OddSurfaceDistance) : SFormula 0 :=
  SFormula.supportSurjectiveF
    (SC.n D.distance)
    (SC.n (nQubits D.distance))
    SC.bound
    (gridColOf D.distance)

def xRowsOccupiedSupportSurjectiveF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (xRowsOccupiedF D) (xRowsSupportSurjectiveF D)

def zColsOccupiedSupportSurjectiveF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (zColsOccupiedF D) (zColsSupportSurjectiveF D)

theorem distancePredLtDecision (D : OddSurfaceDistance) :
    decide (D.distance - 1 < D.distance) = true := by
  cases D with
  | mk index =>
      simp [OddSurfaceDistance.distance, oddDistance]

def xRowsWeightLowerAssumingSupportSurjectiveDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [xRowsSupportSurjectiveF D] (xRowsOccupiedWeightLowerF D) :=
  .impIntro <|
    .finiteSurjectiveWeightLower
      (SC.n (nQubits D.distance))
      SC.bound
      (SC.n (D.distance - 1))
      (SC.n D.distance)
      (gridRowOf D.distance)
      (.hyp (by simp [xRowsSupportSurjectiveF]))
      (.closedNatLt (D.distance - 1) D.distance (distancePredLtDecision D))

def zColsWeightLowerAssumingSupportSurjectiveDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [zColsSupportSurjectiveF D] (zColsOccupiedWeightLowerF D) :=
  .impIntro <|
    .finiteSurjectiveWeightLower
      (SC.n (nQubits D.distance))
      SC.bound
      (SC.n (D.distance - 1))
      (SC.n D.distance)
      (gridColOf D.distance)
      (.hyp (by simp [zColsSupportSurjectiveF]))
      (.closedNatLt (D.distance - 1) D.distance (distancePredLtDecision D))

def xRowsWeightLowerFromSupportSurjectiveDeriv {D : OddSurfaceDistance}
    (cover : SFormula.Deriv [xRowsOccupiedF D] (xRowsSupportSurjectiveF D)) :
    SFormula.Deriv [] (xRowsOccupiedWeightLowerF D) :=
  .impIntro <|
    .finiteSurjectiveWeightLower
      (SC.n (nQubits D.distance))
      SC.bound
      (SC.n (D.distance - 1))
      (SC.n D.distance)
      (gridRowOf D.distance)
      cover
      (.closedNatLt (D.distance - 1) D.distance (distancePredLtDecision D))

def zColsWeightLowerFromSupportSurjectiveDeriv {D : OddSurfaceDistance}
    (cover : SFormula.Deriv [zColsOccupiedF D] (zColsSupportSurjectiveF D)) :
    SFormula.Deriv [] (zColsOccupiedWeightLowerF D) :=
  .impIntro <|
    .finiteSurjectiveWeightLower
      (SC.n (nQubits D.distance))
      SC.bound
      (SC.n (D.distance - 1))
      (SC.n D.distance)
      (gridColOf D.distance)
      cover
      (.closedNatLt (D.distance - 1) D.distance (distancePredLtDecision D))

def xRowsWeightLowerFromSupportImpDeriv {D : OddSurfaceDistance}
    (coverImp : SFormula.Deriv [] (xRowsOccupiedSupportSurjectiveF D)) :
    SFormula.Deriv [] (xRowsOccupiedWeightLowerF D) :=
  xRowsWeightLowerFromSupportSurjectiveDeriv <|
    .mp coverImp.weakenContext .assumption

def zColsWeightLowerFromSupportImpDeriv {D : OddSurfaceDistance}
    (coverImp : SFormula.Deriv [] (zColsOccupiedSupportSurjectiveF D)) :
    SFormula.Deriv [] (zColsOccupiedWeightLowerF D) :=
  zColsWeightLowerFromSupportSurjectiveDeriv <|
    .mp coverImp.weakenContext .assumption

def xLowerBoundByGeometryF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (xNontrivialNormalizerF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

def zLowerBoundByGeometryF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (zNontrivialNormalizerF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

/-! ### Syntactic row/column cuts and finite products

The topological step is represented as ordinary syntax.  A row cut is the
Pauli string with `Z` on one grid row; a column cut is the transpose with `X`
on one grid column.  Adjacent bridge factors and their finite products are
`stabMul`/`stabFold` terms, not meta-level lists.
-/

def rowCut {arity : Nat} (dist : Nat) (row : Term arity .nat) : STerm arity .stab :=
  .closed <|
    .stabLam <|
      .ite (.eqNat (.div Formula.qVar (.natLit dist)) row.weaken)
        (.pauliLit Pauli.Z)
        (.pauliLit Pauli.I)

def colCut {arity : Nat} (dist : Nat) (col : Term arity .nat) : STerm arity .stab :=
  .closed <|
    .stabLam <|
      .ite (.eqNat (.mod Formula.qVar (.natLit dist)) col.weaken)
        (.pauliLit Pauli.X)
        (.pauliLit Pauli.I)

def rowBridge {arity : Nat} (dist : Nat) (row : Term arity .nat) :
    STerm arity .stab :=
  SC.stabMul (rowCut dist row) (rowCut dist (.add row (.natLit 1)))

def colBridge {arity : Nat} (dist : Nat) (col : Term arity .nat) :
    STerm arity .stab :=
  SC.stabMul (colCut dist col) (colCut dist (.add col (.natLit 1)))

def stripWidth (dist : Nat) : Nat :=
  QHL.CodeLang.StabBinder.SFormula.gridStripWidth dist

def rowZStripIndex {arity : Nat} (dist : Nat)
    (row slot : Term arity .nat) : Term arity .nat :=
  QHL.CodeLang.StabBinder.SFormula.gridRowZStripIndex dist row slot

def colXStripIndex {arity : Nat} (dist : Nat)
    (col slot : Term arity .nat) : Term arity .nat :=
  QHL.CodeLang.StabBinder.SFormula.gridColXStripIndex dist col slot

def rowZStripProduct {arity : Nat} (dist : Nat) (row : Term arity .nat) :
    STerm arity .stab :=
  SC.stabFold (SC.n (stripWidth dist))
    (.closed (Formula.codeRow (.natLit dist)
      (rowZStripIndex dist row.weaken colVar)))

def colXStripProduct {arity : Nat} (dist : Nat) (col : Term arity .nat) :
    STerm arity .stab :=
  SC.stabFold (SC.n (stripWidth dist))
    (.closed (Formula.codeRow (.natLit dist)
      (colXStripIndex dist col.weaken colVar)))

def rowZStripIndexPure {arity : Nat} (dist : Nat)
    {row slot : Term arity .nat}
    (hrow : SFormula.PureNatTerm row) (hslot : SFormula.PureNatTerm slot) :
    SFormula.PureNatTerm (rowZStripIndex dist row slot) := by
  unfold rowZStripIndex
  let dm1 : SFormula.PureNatTerm (Term.natLit (arity := arity) (dist - 1)) :=
    SFormula.PureNatTerm.nat (dist - 1)
  let bulkCount :
      SFormula.PureNatTerm (Term.natLit (arity := arity) ((dist - 1) * (dist - 1))) :=
    SFormula.PureNatTerm.nat ((dist - 1) * (dist - 1))
  let half : SFormula.PureNatTerm (Term.natLit (arity := arity) ((dist - 1) / 2)) :=
    SFormula.PureNatTerm.nat ((dist - 1) / 2)
  let two : SFormula.PureNatTerm (Term.natLit (arity := arity) 2) :=
    SFormula.PureNatTerm.nat 2
  let zero : SFormula.PureNatTerm (Term.natLit (arity := arity) 0) :=
    SFormula.PureNatTerm.nat 0
  let one : SFormula.PureNatTerm (Term.natLit (arity := arity) 1) :=
    SFormula.PureNatTerm.nat 1
  let rowEven : SFormula.PureBoolTerm (.eqNat (.mod row (.natLit 2)) (.natLit 0)) :=
    SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hrow two) zero
  exact
    SFormula.PureNatTerm.ite
      (SFormula.PureBoolTerm.ltNat hslot half)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul hrow dm1)
        (SFormula.PureNatTerm.ite rowEven
          (SFormula.PureNatTerm.mul two hslot)
          (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul two hslot) one)))
      (SFormula.PureNatTerm.ite rowEven
        (SFormula.PureNatTerm.add bulkCount
          (SFormula.PureNatTerm.add half (SFormula.PureNatTerm.div hrow two)))
        (SFormula.PureNatTerm.add bulkCount
          (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul two half)
            (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub hrow one) two))))

def colXStripIndexPure {arity : Nat} (dist : Nat)
    {col slot : Term arity .nat}
    (hcol : SFormula.PureNatTerm col) (hslot : SFormula.PureNatTerm slot) :
    SFormula.PureNatTerm (colXStripIndex dist col slot) := by
  unfold colXStripIndex
  let dm1 : SFormula.PureNatTerm (Term.natLit (arity := arity) (dist - 1)) :=
    SFormula.PureNatTerm.nat (dist - 1)
  let bulkCount :
      SFormula.PureNatTerm (Term.natLit (arity := arity) ((dist - 1) * (dist - 1))) :=
    SFormula.PureNatTerm.nat ((dist - 1) * (dist - 1))
  let half : SFormula.PureNatTerm (Term.natLit (arity := arity) ((dist - 1) / 2)) :=
    SFormula.PureNatTerm.nat ((dist - 1) / 2)
  let two : SFormula.PureNatTerm (Term.natLit (arity := arity) 2) :=
    SFormula.PureNatTerm.nat 2
  let three : SFormula.PureNatTerm (Term.natLit (arity := arity) 3) :=
    SFormula.PureNatTerm.nat 3
  let zero : SFormula.PureNatTerm (Term.natLit (arity := arity) 0) :=
    SFormula.PureNatTerm.nat 0
  let one : SFormula.PureNatTerm (Term.natLit (arity := arity) 1) :=
    SFormula.PureNatTerm.nat 1
  let colEven : SFormula.PureBoolTerm (.eqNat (.mod col (.natLit 2)) (.natLit 0)) :=
    SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hcol two) zero
  exact
    SFormula.PureNatTerm.ite
      (SFormula.PureBoolTerm.ltNat hslot half)
      (SFormula.PureNatTerm.add
        (SFormula.PureNatTerm.mul
          (SFormula.PureNatTerm.ite colEven
            (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul two hslot) one)
            (SFormula.PureNatTerm.mul two hslot))
          dm1)
        hcol)
      (SFormula.PureNatTerm.ite colEven
        (SFormula.PureNatTerm.add bulkCount (SFormula.PureNatTerm.div hcol two))
        (SFormula.PureNatTerm.add bulkCount
          (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul three half)
            (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub hcol one) two))))

def rowBridgePrefixProduct (D : OddSurfaceDistance) (bound : STerm 0 .nat) :
    STerm 0 .stab :=
  SC.stabFold bound (rowBridge D.distance rowVar1)

def colBridgePrefixProduct (D : OddSurfaceDistance) (bound : STerm 0 .nat) :
    STerm 0 .stab :=
  SC.stabFold bound (colBridge D.distance rowVar1)

def rowBridgeProduct (D : OddSurfaceDistance) : STerm 0 .stab :=
  rowBridgePrefixProduct D (SC.n (D.distance - 1))

def colBridgeProduct (D : OddSurfaceDistance) : STerm 0 .stab :=
  colBridgePrefixProduct D (SC.n (D.distance - 1))

def rowBridgeFactorsCommuteF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .commutesUpTo (SC.n (nQubits D.distance)).weaken
      (rowBridge D.distance rowVar1)
      SC.bound.weaken

def colBridgeFactorsCommuteF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .commutesUpTo (SC.n (nQubits D.distance)).weaken
      (colBridge D.distance rowVar1)
      SC.bound.weaken

def rowZStripIndexInRangeF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .allNatLt (SC.n (arity := 1) (stripWidth D.distance)) <|
      SFormula.witnessLt
        (SC.closed (rowZStripIndex D.distance leftRowVar2 rightRowVar2))
        (SC.n (arity := 2) (numStab D.distance))

def colXStripIndexInRangeF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .allNatLt (SC.n (arity := 1) (stripWidth D.distance)) <|
      SFormula.witnessLt
        (SC.closed (colXStripIndex D.distance leftRowVar2 rightRowVar2))
        (SC.n (arity := 2) (numStab D.distance))

def rowZStripProductCommutesF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .commutesUpTo (SC.n (nQubits D.distance)).weaken
      (rowZStripProduct D.distance rowVar1)
      SC.bound.weaken

def colXStripProductCommutesF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .commutesUpTo (SC.n (nQubits D.distance)).weaken
      (colXStripProduct D.distance rowVar1)
      SC.bound.weaken

def rowBridgeGeneratedEqF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .eqStabUpTo (SC.n (nQubits D.distance)).weaken
      (rowBridge D.distance rowVar1)
      (rowZStripProduct D.distance rowVar1)

def colBridgeGeneratedEqF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n (D.distance - 1)) <|
    .eqStabUpTo (SC.n (nQubits D.distance)).weaken
      (colBridge D.distance rowVar1)
      (colXStripProduct D.distance rowVar1)

def rowBridgeProductCommutesF (D : OddSurfaceDistance) : SFormula 0 :=
  .commutesUpTo (SC.n (nQubits D.distance)) (rowBridgeProduct D) SC.bound

def colBridgeProductCommutesF (D : OddSurfaceDistance) : SFormula 0 :=
  .commutesUpTo (SC.n (nQubits D.distance)) (colBridgeProduct D) SC.bound

def rowBridgeProductCommutesDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [rowBridgeFactorsCommuteF D] (rowBridgeProductCommutesF D) :=
  .commutesStabFoldLeft
    (SC.n (nQubits D.distance))
    (SC.n (D.distance - 1))
    (rowBridge D.distance rowVar1)
    SC.bound
    (.hyp (by simp [rowBridgeFactorsCommuteF]))

def colBridgeProductCommutesDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [colBridgeFactorsCommuteF D] (colBridgeProductCommutesF D) :=
  .commutesStabFoldLeft
    (SC.n (nQubits D.distance))
    (SC.n (D.distance - 1))
    (colBridge D.distance rowVar1)
    SC.bound
    (.hyp (by simp [colBridgeFactorsCommuteF]))

/-! ### Cut commutation from generic local Pauli rules

The following two derivations are intentionally not trusted kernel rules.  They
use only generic `SFormula.Deriv` constructors: finite bounded introduction,
Boolean case analysis, lambda/if beta for closed cuts, quotient/remainder
arithmetic, index substitution, and local Pauli commutation.
-/

def rowCutQubitCond (D : OddSurfaceDistance) : Term 3 .bool :=
  .eqNat
    (NatArithmetic.rowOf (.var ⟨0, by decide⟩) (.natLit D.distance))
    (rowVar1.weaken.weaken)

def colCutQubitCond (D : OddSurfaceDistance) : Term 3 .bool :=
  .eqNat
    (NatArithmetic.colOf (.var ⟨0, by decide⟩) (.natLit D.distance))
    (rowVar1.weaken.weaken)

def qVarPure2 : SFormula.PureNatTerm (colVar (arity := 1)) :=
  SFormula.PureNatTerm.var ⟨0, by decide⟩

def rowVarPure2 : SFormula.PureNatTerm (rowVar1.weaken) :=
  SFormula.PureNatTerm.var ⟨1, by decide⟩

def rowOfQPure2 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm
      (NatArithmetic.rowOf (colVar (arity := 1)) (.natLit D.distance)) :=
  SFormula.PureNatTerm.rowOf qVarPure2 (SFormula.PureNatTerm.nat D.distance)

def colOfQPure2 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm
      (NatArithmetic.colOf (colVar (arity := 1)) (.natLit D.distance)) :=
  SFormula.PureNatTerm.colOf qVarPure2 (SFormula.PureNatTerm.nat D.distance)

def gridIdxRowColOfQPure2 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm
      (NatArithmetic.gridIdxLeft (.natLit D.distance) rowVar1.weaken
        (NatArithmetic.colOf (colVar (arity := 1)) (.natLit D.distance))) :=
  SFormula.PureNatTerm.gridIdxLeft
    (SFormula.PureNatTerm.nat D.distance)
    rowVarPure2
    (colOfQPure2 D)

def gridIdxRowOfQColPure2 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm
      (NatArithmetic.gridIdxLeft (.natLit D.distance)
        (NatArithmetic.rowOf (colVar (arity := 1)) (.natLit D.distance))
        rowVar1.weaken) :=
  SFormula.PureNatTerm.gridIdxLeft
    (SFormula.PureNatTerm.nat D.distance)
    (rowOfQPure2 D)
    rowVarPure2

def rowCutLocalCommutesFromNoXDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
        (SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1).weaken,
        (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
      (SFormula.localCommutesAt
        (SC.rowZCut D.distance rowVar1).weaken
        SC.bound.weaken.weaken
        SFormula.boundNat) := by
  let qTerm : Term 2 .nat := colVar
  let rowTerm : Term 2 .nat := rowVar1.weaken
  let gridTerm : Term 2 .nat :=
    NatArithmetic.gridIdxLeft (.natLit D.distance) rowTerm
      (NatArithmetic.colOf qTerm (.natLit D.distance))
  let cond : Term 3 .bool := rowCutQubitCond D
  let cut : STerm 2 .stab := (SC.rowZCut D.distance rowVar1).weaken
  let Eterm : STerm 2 .stab := SC.bound.weaken.weaken
  let ctx :=
    [SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
      (SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1).weaken,
      (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
  let target := SFormula.localCommutesAt cut Eterm SFormula.boundNat
  let qLt : SFormula.Deriv ctx
      (SFormula.witnessLt (SC.closed qTerm) (SC.n (nQubits D.distance))) :=
    .assumption
  let noXGlobal : SFormula.Deriv ctx
      ((SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1).weaken) :=
    .hyp (by right; left)
  have trueBranch :
      SFormula.Deriv
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b true) :: ctx)
        target := by
    let ctxT :=
      [.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b true),
        SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
        (SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1).weaken,
        (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
    let qLtT : SFormula.Deriv ctxT
        (SFormula.witnessLt (SC.closed qTerm) (SC.n (nQubits D.distance))) :=
      .hyp (by right; left)
    let condTrue : SFormula.Deriv ctxT
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b true)) :=
      .assumption
    let noXT : SFormula.Deriv ctxT
        ((SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1).weaken) :=
      .hyp (by right; right; left)
    let colLt : SFormula.Deriv ctxT
        (SFormula.witnessLt
          (SC.closed (NatArithmetic.colOf qTerm (.natLit D.distance)))
          (SC.n D.distance)) :=
      .modLtOfLtSquare D.distance qTerm qLtT
    let noXApply :=
      SFormula.Deriv.allNatLtElim
        (SC.n (arity := 2) D.distance)
        (.not <| SFormula.xSupportAt SC.bound.weaken.weaken
          (SC.gridIdx (.natLit D.distance) rowVar1.weaken.weaken colVar))
        (SC.closed (NatArithmetic.colOf qTerm (.natLit D.distance)))
        noXT
        colLt
    let noXAtGrid : SFormula.Deriv ctxT
        (.not (.eqBool
          (.anticommutes (.stabAt Eterm (SC.closed gridTerm)) (SC.p Pauli.Z))
          (SC.b true))) := by
      let noXBody : SFormula 3 :=
        .not <| SFormula.xSupportAt SC.bound.weaken.weaken
          (SC.gridIdx (.natLit D.distance) rowVar1.weaken.weaken colVar)
      have h :=
        SFormula.Deriv.applyNatSubstitutionBetaElim
          (NatArithmetic.colOf qTerm (.natLit D.distance))
          noXBody
          (colOfQPure2 D)
          noXApply
      simpa [gridTerm, Eterm, SFormula.xSupportAt, SC.gridIdx,
        SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        STerm.instantiateNatAt, Term.instantiateNatAt, SFormula.weaken,
        SFormula.lift, STerm.weaken, STerm.lift, Term.weaken, Term.lift,
        Term.weakenVar, SC.closed, SC.p, SC.b, SC.bound, rowTerm, rowVar1, colVar,
        noXBody,
        NatArithmetic.gridIdxLeft, NatArithmetic.colOf]
        using h
    let condTrueGrid : SFormula.Deriv ctxT
        (.eqBool
          (SC.closed (.eqNat (NatArithmetic.rowOf qTerm (.natLit D.distance)) rowTerm))
          (SC.b true)) := by
      simpa [cond, qTerm, rowTerm, rowCutQubitCond, SFormula.instantiateTopNat,
        SFormula.instantiateNatAt, STerm.instantiateNatAt, Term.instantiateTopNat,
        Term.instantiateNatAt, Term.weaken, Term.lift, Term.weakenVar,
        SC.closed, SC.b, rowVar1, colVar, NatArithmetic.rowOf]
        using condTrue
    let idxEq : SFormula.Deriv ctxT
        (.eqNat (SC.closed gridTerm) (SC.closed qTerm)) :=
      .gridIdxLeftDivModEqOfRow D.distance rowTerm qTerm qLtT condTrueGrid
    let noAntiAtQ : SFormula.Deriv ctxT
        (.not (.eqBool
          (.anticommutes (.stabAt Eterm (SC.closed qTerm)) (SC.p Pauli.Z))
          (SC.b true))) :=
      .noAntiAtSubst Eterm (SC.p Pauli.Z) gridTerm qTerm
        (gridIdxRowColOfQPure2 D) qVarPure2 idxEq noXAtGrid
    let entryEq : SFormula.Deriv ctxT
        (.eqPauli (.stabAt cut SFormula.boundNat) (SC.p Pauli.Z)) := by
      have h :=
        SFormula.Deriv.stabAtClosedIteLamEqThen cond
          (Term.pauliLit (arity := 3) Pauli.Z)
          (Term.pauliLit (arity := 3) Pauli.I)
          qTerm
          qVarPure2
          condTrue
      simpa [cut, cond, qTerm, rowCutQubitCond, SC.rowZCut, SC.closed,
        SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        STerm.instantiateNatAt, Term.instantiateTopNat, Term.instantiateNatAt,
        SFormula.boundNat, STerm.weaken, STerm.lift, Term.weaken, Term.lift,
        Term.weakenVar, rowVar1, colVar, NatArithmetic.rowOf]
        using h
    simpa [target, cut, Eterm, qTerm] using
      SFormula.Deriv.localCommutesOfLeftEqNoAntiRight
        cut Eterm SFormula.boundNat (SC.p Pauli.Z) entryEq noAntiAtQ
  have falseBranch :
      SFormula.Deriv
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b false) :: ctx)
        target := by
    let ctxF :=
      [.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b false),
        SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
        (SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1).weaken,
        (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
    let condFalse : SFormula.Deriv ctxF
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b false)) :=
      .assumption
    let entryEq : SFormula.Deriv ctxF
        (.eqPauli (.stabAt cut SFormula.boundNat) (SC.p Pauli.I)) := by
      have h :=
        SFormula.Deriv.stabAtClosedIteLamEqElse cond
          (Term.pauliLit (arity := 3) Pauli.Z)
          (Term.pauliLit (arity := 3) Pauli.I)
          qTerm
          qVarPure2
          condFalse
      simpa [cut, cond, qTerm, rowCutQubitCond, SC.rowZCut, SC.closed,
        SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        STerm.instantiateNatAt, Term.instantiateTopNat, Term.instantiateNatAt,
        SFormula.boundNat, STerm.weaken, STerm.lift, Term.weaken, Term.lift,
        Term.weakenVar, rowVar1, colVar, NatArithmetic.rowOf]
        using h
    simpa [target, cut, Eterm, qTerm] using
      SFormula.Deriv.localCommutesOfLeftI cut Eterm SFormula.boundNat entryEq
  exact
    SFormula.Deriv.boolCases (SC.closed (Term.instantiateTopNat qTerm cond)) target
      trueBranch falseBranch

def colCutLocalCommutesFromNoZDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
        (SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1).weaken,
        (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
      (SFormula.localCommutesAt
        (SC.colXCut D.distance rowVar1).weaken
        SC.bound.weaken.weaken
        SFormula.boundNat) := by
  let qTerm : Term 2 .nat := colVar
  let colTerm : Term 2 .nat := rowVar1.weaken
  let gridTerm : Term 2 .nat :=
    NatArithmetic.gridIdxLeft (.natLit D.distance)
      (NatArithmetic.rowOf qTerm (.natLit D.distance)) colTerm
  let cond : Term 3 .bool := colCutQubitCond D
  let cut : STerm 2 .stab := (SC.colXCut D.distance rowVar1).weaken
  let Eterm : STerm 2 .stab := SC.bound.weaken.weaken
  let ctx :=
    [SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
      (SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1).weaken,
      (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
  let target := SFormula.localCommutesAt cut Eterm SFormula.boundNat
  let qLt : SFormula.Deriv ctx
      (SFormula.witnessLt (SC.closed qTerm) (SC.n (nQubits D.distance))) :=
    .assumption
  let noZGlobal : SFormula.Deriv ctx
      ((SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1).weaken) :=
    .hyp (by right; left)
  have trueBranch :
      SFormula.Deriv
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b true) :: ctx)
        target := by
    let ctxT :=
      [.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b true),
        SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
        (SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1).weaken,
        (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
    let qLtT : SFormula.Deriv ctxT
        (SFormula.witnessLt (SC.closed qTerm) (SC.n (nQubits D.distance))) :=
      .hyp (by right; left)
    let condTrue : SFormula.Deriv ctxT
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b true)) :=
      .assumption
    let noZT : SFormula.Deriv ctxT
        ((SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1).weaken) :=
      .hyp (by right; right; left)
    let rowLt : SFormula.Deriv ctxT
        (SFormula.witnessLt
          (SC.closed (NatArithmetic.rowOf qTerm (.natLit D.distance)))
          (SC.n D.distance)) :=
      .divLtOfLtSquare D.distance qTerm qLtT
    let noZApply :=
      SFormula.Deriv.allNatLtElim
        (SC.n (arity := 2) D.distance)
        (.not <| SFormula.zSupportAt SC.bound.weaken.weaken
          (SC.gridIdx (.natLit D.distance) colVar rowVar1.weaken.weaken))
        (SC.closed (NatArithmetic.rowOf qTerm (.natLit D.distance)))
        noZT
        rowLt
    let noZAtGrid : SFormula.Deriv ctxT
        (.not (.eqBool
          (.anticommutes (.stabAt Eterm (SC.closed gridTerm)) (SC.p Pauli.X))
          (SC.b true))) := by
      let noZBody : SFormula 3 :=
        .not <| SFormula.zSupportAt SC.bound.weaken.weaken
          (SC.gridIdx (.natLit D.distance) colVar rowVar1.weaken.weaken)
      have h :=
        SFormula.Deriv.applyNatSubstitutionBetaElim
          (NatArithmetic.rowOf qTerm (.natLit D.distance))
          noZBody
          (rowOfQPure2 D)
          noZApply
      simpa [gridTerm, Eterm, SFormula.zSupportAt, SC.gridIdx,
        SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        STerm.instantiateNatAt, Term.instantiateNatAt, SFormula.weaken,
        SFormula.lift, STerm.weaken, STerm.lift, Term.weaken, Term.lift,
        Term.weakenVar, SC.closed, SC.p, SC.b, SC.bound, colTerm, rowVar1, colVar,
        noZBody,
        NatArithmetic.gridIdxLeft, NatArithmetic.rowOf]
        using h
    let condTrueGrid : SFormula.Deriv ctxT
        (.eqBool
          (SC.closed (.eqNat (NatArithmetic.colOf qTerm (.natLit D.distance)) colTerm))
          (SC.b true)) := by
      simpa [cond, qTerm, colTerm, colCutQubitCond, SFormula.instantiateTopNat,
        SFormula.instantiateNatAt, STerm.instantiateNatAt, Term.instantiateTopNat,
        Term.instantiateNatAt, Term.weaken, Term.lift, Term.weakenVar,
        SC.closed, SC.b, rowVar1, colVar, NatArithmetic.colOf]
        using condTrue
    let idxEq : SFormula.Deriv ctxT
        (.eqNat (SC.closed gridTerm) (SC.closed qTerm)) :=
      .gridIdxLeftDivModEqOfCol D.distance colTerm qTerm qLtT condTrueGrid
    let noAntiAtQ : SFormula.Deriv ctxT
        (.not (.eqBool
          (.anticommutes (.stabAt Eterm (SC.closed qTerm)) (SC.p Pauli.X))
          (SC.b true))) :=
      .noAntiAtSubst Eterm (SC.p Pauli.X) gridTerm qTerm
        (gridIdxRowOfQColPure2 D) qVarPure2 idxEq noZAtGrid
    let entryEq : SFormula.Deriv ctxT
        (.eqPauli (.stabAt cut SFormula.boundNat) (SC.p Pauli.X)) := by
      have h :=
        SFormula.Deriv.stabAtClosedIteLamEqThen cond
          (Term.pauliLit (arity := 3) Pauli.X)
          (Term.pauliLit (arity := 3) Pauli.I)
          qTerm
          qVarPure2
          condTrue
      simpa [cut, cond, qTerm, colCutQubitCond, SC.colXCut, SC.closed,
        SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        STerm.instantiateNatAt, Term.instantiateTopNat, Term.instantiateNatAt,
        SFormula.boundNat, STerm.weaken, STerm.lift, Term.weaken, Term.lift,
        Term.weakenVar, rowVar1, colVar, NatArithmetic.colOf]
        using h
    simpa [target, cut, Eterm, qTerm] using
      SFormula.Deriv.localCommutesOfLeftEqNoAntiRight
        cut Eterm SFormula.boundNat (SC.p Pauli.X) entryEq noAntiAtQ
  have falseBranch :
      SFormula.Deriv
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b false) :: ctx)
        target := by
    let ctxF :=
      [.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b false),
        SFormula.boundNatLt (SC.n (arity := 1) (nQubits D.distance)),
        (SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1).weaken,
        (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken]
    let condFalse : SFormula.Deriv ctxF
        (.eqBool (SC.closed (Term.instantiateTopNat qTerm cond)) (SC.b false)) :=
      .assumption
    let entryEq : SFormula.Deriv ctxF
        (.eqPauli (.stabAt cut SFormula.boundNat) (SC.p Pauli.I)) := by
      have h :=
        SFormula.Deriv.stabAtClosedIteLamEqElse cond
          (Term.pauliLit (arity := 3) Pauli.X)
          (Term.pauliLit (arity := 3) Pauli.I)
          qTerm
          qVarPure2
          condFalse
      simpa [cut, cond, qTerm, colCutQubitCond, SC.colXCut, SC.closed,
        SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        STerm.instantiateNatAt, Term.instantiateTopNat, Term.instantiateNatAt,
        SFormula.boundNat, STerm.weaken, STerm.lift, Term.weaken, Term.lift,
        Term.weakenVar, rowVar1, colVar, NatArithmetic.colOf]
        using h
    simpa [target, cut, Eterm, qTerm] using
      SFormula.Deriv.localCommutesOfLeftI cut Eterm SFormula.boundNat entryEq
  exact
    SFormula.Deriv.boolCases (SC.closed (Term.instantiateTopNat qTerm cond)) target
      trueBranch falseBranch

def rowCutNoXImpliesCommutesDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (rowCutNoXImpliesCommutesF D) := by
  refine .allNatLtIntroBounded (SC.n D.distance) (rowCutNoXImpliesCommutesBody D) ?_
  refine .impIntro ?_
  refine .commutesOfPointwise
    (SC.n (arity := 1) (nQubits D.distance))
    (SC.rowZCut D.distance rowVar1)
    SC.bound.weaken ?_
  exact .allNatLtIntroBounded
    (SC.n (arity := 1) (nQubits D.distance))
    (SFormula.localCommutesAt
      (SC.rowZCut D.distance rowVar1).weaken
      SC.bound.weaken.weaken
      SFormula.boundNat)
    (rowCutLocalCommutesFromNoXDeriv D)

def colCutNoZImpliesCommutesDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (colCutNoZImpliesCommutesF D) := by
  refine .allNatLtIntroBounded (SC.n D.distance) (colCutNoZImpliesCommutesBody D) ?_
  refine .impIntro ?_
  refine .commutesOfPointwise
    (SC.n (arity := 1) (nQubits D.distance))
    (SC.colXCut D.distance rowVar1)
    SC.bound.weaken ?_
  exact .allNatLtIntroBounded
    (SC.n (arity := 1) (nQubits D.distance))
    (SFormula.localCommutesAt
      (SC.colXCut D.distance rowVar1).weaken
      SC.bound.weaken.weaken
      SFormula.boundNat)
    (colCutLocalCommutesFromNoZDeriv D)

def rowBridgeFactorsFromGeneratedDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [rowBridgeGeneratedEqF D, rowZStripProductCommutesF D]
      (rowBridgeFactorsCommuteF D) := by
  refine .allNatLtIntroBounded (SC.n (D.distance - 1))
    (.commutesUpTo (SC.n (nQubits D.distance)).weaken
      (rowBridge D.distance rowVar1)
      SC.bound.weaken) ?_
  let ctx := [SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1)),
    (rowBridgeGeneratedEqF D).weaken, (rowZStripProductCommutesF D).weaken]
  let rowLt : SFormula.Deriv ctx
      (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))) := .assumption
  let hEqGlobal : SFormula.Deriv ctx ((rowBridgeGeneratedEqF D).weaken) :=
    .hyp (by right; left)
  let hProdGlobal : SFormula.Deriv ctx ((rowZStripProductCommutesF D).weaken) :=
    .hyp (by right; right; left)
  let hEqApply := SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hEqGlobal rowLt
  let hProdApply := SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hProdGlobal rowLt
  let hEq := SFormula.Deriv.applyNatBoundNatBeta _ hEqApply
  let hProd := SFormula.Deriv.applyNatBoundNatBeta _ hProdApply
  let n := SC.n (arity := 1) (nQubits D.distance)
  exact
    SFormula.Deriv.commutesOfEqLeft n
      (rowZStripProduct D.distance rowVar1)
      (rowBridge D.distance rowVar1)
      SC.bound.weaken
      (SFormula.Deriv.eqStabSymm n
        (rowBridge D.distance rowVar1)
        (rowZStripProduct D.distance rowVar1)
        hEq)
      hProd

def colBridgeFactorsFromGeneratedDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [colBridgeGeneratedEqF D, colXStripProductCommutesF D]
      (colBridgeFactorsCommuteF D) := by
  refine .allNatLtIntroBounded (SC.n (D.distance - 1))
    (.commutesUpTo (SC.n (nQubits D.distance)).weaken
      (colBridge D.distance rowVar1)
      SC.bound.weaken) ?_
  let ctx := [SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1)),
    (colBridgeGeneratedEqF D).weaken, (colXStripProductCommutesF D).weaken]
  let colLt : SFormula.Deriv ctx
      (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))) := .assumption
  let hEqGlobal : SFormula.Deriv ctx ((colBridgeGeneratedEqF D).weaken) :=
    .hyp (by right; left)
  let hProdGlobal : SFormula.Deriv ctx ((colXStripProductCommutesF D).weaken) :=
    .hyp (by right; right; left)
  let hEqApply := SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hEqGlobal colLt
  let hProdApply := SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hProdGlobal colLt
  let hEq := SFormula.Deriv.applyNatBoundNatBeta _ hEqApply
  let hProd := SFormula.Deriv.applyNatBoundNatBeta _ hProdApply
  let n := SC.n (arity := 1) (nQubits D.distance)
  exact
    SFormula.Deriv.commutesOfEqLeft n
      (colXStripProduct D.distance rowVar1)
      (colBridge D.distance rowVar1)
      SC.bound.weaken
      (SFormula.Deriv.eqStabSymm n
        (colBridge D.distance rowVar1)
        (colXStripProduct D.distance rowVar1)
        hEq)
      hProd

def rowZStripProductCommutesFromNormalizerDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [normalizesOddF D, rowZStripIndexInRangeF D]
      (rowZStripProductCommutesF D) := by
  refine .allNatLtIntroBounded (SC.n (D.distance - 1))
    (.commutesUpTo (SC.n (nQubits D.distance)).weaken
      (rowZStripProduct D.distance rowVar1)
      SC.bound.weaken) ?_
  let ctxRow := [SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1)),
    (normalizesOddF D).weaken, (rowZStripIndexInRangeF D).weaken]
  let n1 := SC.n (arity := 1) (nQubits D.distance)
  let stripBody : STerm 2 .stab :=
    .closed (Formula.codeRow (.natLit D.distance)
      (rowZStripIndex D.distance rowVar1.weaken colVar))
  let rowLt : SFormula.Deriv ctxRow
      (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))) :=
    SFormula.Deriv.assumption
  let hRangeGlobal : SFormula.Deriv ctxRow ((rowZStripIndexInRangeF D).weaken) :=
    SFormula.Deriv.hyp (by right; right; left)
  let hRangeRowApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hRangeGlobal rowLt
  let hRangeRow :=
    SFormula.Deriv.applyNatBoundNatBeta _ hRangeRowApply
  let hNormGlobal : SFormula.Deriv ctxRow ((normalizesOddF D).weaken) :=
    SFormula.Deriv.hyp (by right; left)
  refine SFormula.Deriv.commutesStabFoldLeft n1
    (SC.n (arity := 1) (stripWidth D.distance))
    stripBody
    SC.bound.weaken ?_
  refine .allNatLtIntroBounded (SC.n (stripWidth D.distance))
    (.commutesUpTo n1.weaken stripBody SC.bound.weaken.weaken) ?_
  let ctxSlot := [SFormula.boundNatLt (SC.n (arity := 1) (stripWidth D.distance)),
    (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))).weaken,
    (normalizesOddF D).weaken.weaken, (rowZStripIndexInRangeF D).weaken.weaken]
  let rowLt : SFormula.Deriv ctxSlot
      (SFormula.witnessLt (SC.closed leftRowVar2) (SC.n (arity := 2) (D.distance - 1))) := by
    simpa [SFormula.boundNatLt, SFormula.witnessLt, SFormula.weaken, SFormula.lift,
      STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar, SC.closed,
      SC.n, leftRowVar2] using
      (SFormula.Deriv.hyp (Γ := ctxSlot)
        (A := (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))).weaken)
        (by right; left))
  let slotLt : SFormula.Deriv ctxSlot
      (SFormula.witnessLt (SC.closed rightRowVar2)
        (SC.n (arity := 2) (stripWidth D.distance))) := by
    simpa [SFormula.boundNatLt, SFormula.witnessLt, SFormula.weaken, SFormula.lift,
      STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar, SC.closed,
      SC.n, rightRowVar2] using
      (SFormula.Deriv.hyp (Γ := ctxSlot)
        (A := SFormula.boundNatLt (SC.n (arity := 1) (stripWidth D.distance)))
        (by left))
  let hRangeSlotApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat
      ((SFormula.Deriv.weakenFresh hRangeRow).weakenContext)
      slotLt
  let hIdxLt :=
    SFormula.Deriv.applyNatBoundNatBeta _ hRangeSlotApply
  let hNormSlot : SFormula.Deriv ctxSlot ((normalizesOddF D).weaken.weaken) :=
    (SFormula.Deriv.weakenFresh hNormGlobal).weakenContext
  let hNormApply :=
    SFormula.Deriv.allNatLtElim _ _ (SC.closed
      (rowZStripIndex D.distance leftRowVar2 rightRowVar2)) hNormSlot hIdxLt
  let hNorm :=
    SFormula.Deriv.applyNatSubstitutionBetaElim
      (rowZStripIndex D.distance leftRowVar2 rightRowVar2) _
      (rowZStripIndexPure D.distance
        (SFormula.PureNatTerm.var ⟨1, by decide⟩)
        (SFormula.PureNatTerm.var ⟨0, by decide⟩))
      hNormApply
  simpa [ctxSlot, n1, stripBody, normalizesOddF, rowZStripIndexInRangeF,
    rowZStripProductCommutesF, rowZStripProduct, rowZStripIndex, Formula.codeRow,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.bound, SC.closed, rowVar1, leftRowVar2,
    rightRowVar2, colVar] using hNorm

def colXStripProductCommutesFromNormalizerDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [normalizesOddF D, colXStripIndexInRangeF D]
      (colXStripProductCommutesF D) := by
  refine .allNatLtIntroBounded (SC.n (D.distance - 1))
    (.commutesUpTo (SC.n (nQubits D.distance)).weaken
      (colXStripProduct D.distance rowVar1)
      SC.bound.weaken) ?_
  let n1 := SC.n (arity := 1) (nQubits D.distance)
  let stripBody : STerm 2 .stab :=
    .closed (Formula.codeRow (.natLit D.distance)
      (colXStripIndex D.distance rowVar1.weaken colVar))
  let ctxRow := [SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1)),
    (normalizesOddF D).weaken, (colXStripIndexInRangeF D).weaken]
  let colLt : SFormula.Deriv ctxRow
      (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))) :=
    SFormula.Deriv.assumption
  let hRangeGlobal : SFormula.Deriv ctxRow ((colXStripIndexInRangeF D).weaken) :=
    SFormula.Deriv.hyp (by right; right; left)
  let hRangeColApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hRangeGlobal colLt
  let hRangeCol :=
    SFormula.Deriv.applyNatBoundNatBeta _ hRangeColApply
  let hNormGlobal : SFormula.Deriv ctxRow ((normalizesOddF D).weaken) :=
    SFormula.Deriv.hyp (by right; left)
  refine SFormula.Deriv.commutesStabFoldLeft n1
    (SC.n (arity := 1) (stripWidth D.distance))
    stripBody
    SC.bound.weaken ?_
  refine .allNatLtIntroBounded (SC.n (stripWidth D.distance))
    (.commutesUpTo n1.weaken stripBody SC.bound.weaken.weaken) ?_
  let ctxSlot := [SFormula.boundNatLt (SC.n (arity := 1) (stripWidth D.distance)),
    (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))).weaken,
    (normalizesOddF D).weaken.weaken, (colXStripIndexInRangeF D).weaken.weaken]
  let colLt : SFormula.Deriv ctxSlot
      (SFormula.witnessLt (SC.closed leftRowVar2) (SC.n (arity := 2) (D.distance - 1))) := by
    simpa [SFormula.boundNatLt, SFormula.witnessLt, SFormula.weaken, SFormula.lift,
      STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar, SC.closed,
      SC.n, leftRowVar2] using
      (SFormula.Deriv.hyp (Γ := ctxSlot)
        (A := (SFormula.boundNatLt (SC.n (arity := 0) (D.distance - 1))).weaken)
        (by right; left))
  let slotLt : SFormula.Deriv ctxSlot
      (SFormula.witnessLt (SC.closed rightRowVar2)
        (SC.n (arity := 2) (stripWidth D.distance))) := by
    simpa [SFormula.boundNatLt, SFormula.witnessLt, SFormula.weaken, SFormula.lift,
      STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar, SC.closed,
      SC.n, rightRowVar2] using
      (SFormula.Deriv.hyp (Γ := ctxSlot)
        (A := SFormula.boundNatLt (SC.n (arity := 1) (stripWidth D.distance)))
        (by left))
  let hRangeSlotApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat
      ((SFormula.Deriv.weakenFresh hRangeCol).weakenContext)
      slotLt
  let hIdxLt :=
    SFormula.Deriv.applyNatBoundNatBeta _ hRangeSlotApply
  let hNormSlot : SFormula.Deriv ctxSlot ((normalizesOddF D).weaken.weaken) :=
    (SFormula.Deriv.weakenFresh hNormGlobal).weakenContext
  let hNormApply :=
    SFormula.Deriv.allNatLtElim _ _ (SC.closed
      (colXStripIndex D.distance leftRowVar2 rightRowVar2)) hNormSlot hIdxLt
  let hNorm :=
    SFormula.Deriv.applyNatSubstitutionBetaElim
      (colXStripIndex D.distance leftRowVar2 rightRowVar2) _
      (colXStripIndexPure D.distance
        (SFormula.PureNatTerm.var ⟨1, by decide⟩)
        (SFormula.PureNatTerm.var ⟨0, by decide⟩))
      hNormApply
  simpa [ctxSlot, n1, stripBody, normalizesOddF, colXStripIndexInRangeF,
    colXStripProductCommutesF, colXStripProduct, colXStripIndex, Formula.codeRow,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.bound, SC.closed, rowVar1, leftRowVar2,
    rightRowVar2, colVar] using hNorm

def rowBridgeFactorsFromGeneratedNormalizerDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [rowBridgeGeneratedEqF D, rowZStripIndexInRangeF D]
      (.imp (normalizesOddF D) (rowBridgeFactorsCommuteF D)) := by
  refine .impIntro ?_
  let ctx := [normalizesOddF D, rowBridgeGeneratedEqF D, rowZStripIndexInRangeF D]
  let hProd : SFormula.Deriv ctx (rowZStripProductCommutesF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [normalizesOddF D, rowZStripIndexInRangeF D])
      (Δ := ctx)
      (fun C h => by
        simp [ctx] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h))
      (rowZStripProductCommutesFromNormalizerDeriv D)
  let ctxProd :=
    [rowZStripProductCommutesF D, normalizesOddF D,
      rowBridgeGeneratedEqF D, rowZStripIndexInRangeF D]
  let hBridge : SFormula.Deriv ctxProd (rowBridgeFactorsCommuteF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [rowBridgeGeneratedEqF D, rowZStripProductCommutesF D])
      (Δ := ctxProd)
      (fun C h => by
        simp [ctxProd] at h ⊢
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h)
      (rowBridgeFactorsFromGeneratedDeriv D)
  let hRule : SFormula.Deriv ctx
      (.imp (rowZStripProductCommutesF D) (rowBridgeFactorsCommuteF D)) :=
    .impIntro hBridge
  exact .mp hRule hProd

def colBridgeFactorsFromGeneratedNormalizerDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [colBridgeGeneratedEqF D, colXStripIndexInRangeF D]
      (.imp (normalizesOddF D) (colBridgeFactorsCommuteF D)) := by
  refine .impIntro ?_
  let ctx := [normalizesOddF D, colBridgeGeneratedEqF D, colXStripIndexInRangeF D]
  let hProd : SFormula.Deriv ctx (colXStripProductCommutesF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [normalizesOddF D, colXStripIndexInRangeF D])
      (Δ := ctx)
      (fun C h => by
        simp [ctx] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h))
      (colXStripProductCommutesFromNormalizerDeriv D)
  let ctxProd :=
    [colXStripProductCommutesF D, normalizesOddF D,
      colBridgeGeneratedEqF D, colXStripIndexInRangeF D]
  let hBridge : SFormula.Deriv ctxProd (colBridgeFactorsCommuteF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [colBridgeGeneratedEqF D, colXStripProductCommutesF D])
      (Δ := ctxProd)
      (fun C h => by
        simp [ctxProd] at h ⊢
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h)
      (colBridgeFactorsFromGeneratedDeriv D)
  let hRule : SFormula.Deriv ctx
      (.imp (colXStripProductCommutesF D) (colBridgeFactorsCommuteF D)) :=
    .impIntro hBridge
  exact .mp hRule hProd

def rowBridgePrefixFactorsCommuteF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt SFormula.boundNat <|
    .commutesUpTo (SC.n (arity := 1) (nQubits D.distance)).weaken
      (rowBridge D.distance rightRowVar2)
      SC.bound.weaken.weaken

def colBridgePrefixFactorsCommuteF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt SFormula.boundNat <|
    .commutesUpTo (SC.n (arity := 1) (nQubits D.distance)).weaken
      (colBridge D.distance rightRowVar2)
      SC.bound.weaken.weaken

def rowBridgePrefixFactorsCommuteDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
       (rowBridgeFactorsCommuteF D).weaken]
      (rowBridgePrefixFactorsCommuteF D) := by
  refine .allNatLtIntroBounded SFormula.boundNat _ ?_
  let ctx := [SFormula.boundNatLt SFormula.boundNat,
    (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
    (rowBridgeFactorsCommuteF D).weaken.weaken]
  let idxLtRow :
      SFormula.Deriv ctx
        (SFormula.witnessLt SFormula.boundNat SFormula.boundNat.weaken) :=
    .assumption
  let rowLtD :
      SFormula.Deriv ctx
        (SFormula.witnessLt SFormula.boundNat.weaken (SC.n D.distance)) :=
    .hyp (by right; left)
  let idxLtPred :
      SFormula.Deriv ctx
        (SFormula.witnessLt SFormula.boundNat (SC.n (D.distance - 1))) :=
    .ltOfLtLtClosedPred D.distance SFormula.boundNat SFormula.boundNat.weaken
      idxLtRow rowLtD
  let global :
      SFormula.Deriv ctx ((rowBridgeFactorsCommuteF D).weaken.weaken) :=
    .hyp (by right; right; left)
  let hApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat global idxLtPred
  let hBeta := SFormula.Deriv.applyNatBoundNatBeta _ hApply
  simpa [rowBridgePrefixFactorsCommuteF, rowBridgeFactorsCommuteF, SFormula.lift,
    SFormula.weaken, STerm.lift, STerm.weaken, Term.lift, Term.weaken,
    Term.weakenVar, SC.n, SC.bound, rowBridge, rowCut, colCut, rightRowVar2,
    rowVar1] using hBeta

def colBridgePrefixFactorsCommuteDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
       (colBridgeFactorsCommuteF D).weaken]
      (colBridgePrefixFactorsCommuteF D) := by
  refine .allNatLtIntroBounded SFormula.boundNat _ ?_
  let ctx := [SFormula.boundNatLt SFormula.boundNat,
    (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
    (colBridgeFactorsCommuteF D).weaken.weaken]
  let idxLtCol :
      SFormula.Deriv ctx
        (SFormula.witnessLt SFormula.boundNat SFormula.boundNat.weaken) :=
    .assumption
  let colLtD :
      SFormula.Deriv ctx
        (SFormula.witnessLt SFormula.boundNat.weaken (SC.n D.distance)) :=
    .hyp (by right; left)
  let idxLtPred :
      SFormula.Deriv ctx
        (SFormula.witnessLt SFormula.boundNat (SC.n (D.distance - 1))) :=
    .ltOfLtLtClosedPred D.distance SFormula.boundNat SFormula.boundNat.weaken
      idxLtCol colLtD
  let global :
      SFormula.Deriv ctx ((colBridgeFactorsCommuteF D).weaken.weaken) :=
    .hyp (by right; right; left)
  let hApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat global idxLtPred
  let hBeta := SFormula.Deriv.applyNatBoundNatBeta _ hApply
  simpa [colBridgePrefixFactorsCommuteF, colBridgeFactorsCommuteF, SFormula.lift,
    SFormula.weaken, STerm.lift, STerm.weaken, Term.lift, Term.weaken,
    Term.weakenVar, SC.n, SC.bound, colBridge, rowCut, colCut, rightRowVar2,
    rowVar1] using hBeta

def rowBridgePrefixProductCommutesF (D : OddSurfaceDistance) : SFormula 1 :=
  .commutesUpTo (SC.n (arity := 1) (nQubits D.distance))
    (SC.stabFold SFormula.boundNat (rowBridge D.distance rightRowVar2))
    SC.bound.weaken

def colBridgePrefixProductCommutesF (D : OddSurfaceDistance) : SFormula 1 :=
  .commutesUpTo (SC.n (arity := 1) (nQubits D.distance))
    (SC.stabFold SFormula.boundNat (colBridge D.distance rightRowVar2))
    SC.bound.weaken

def rowBridgePrefixProductCommutesDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
       (rowBridgeFactorsCommuteF D).weaken]
      (rowBridgePrefixProductCommutesF D) :=
  .commutesStabFoldLeft
    (SC.n (arity := 1) (nQubits D.distance))
    SFormula.boundNat
    (rowBridge D.distance rightRowVar2)
    SC.bound.weaken
    (rowBridgePrefixFactorsCommuteDeriv D)

def colBridgePrefixProductCommutesDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
       (colBridgeFactorsCommuteF D).weaken]
      (colBridgePrefixProductCommutesF D) :=
  .commutesStabFoldLeft
    (SC.n (arity := 1) (nQubits D.distance))
    SFormula.boundNat
    (colBridge D.distance rightRowVar2)
    SC.bound.weaken
    (colBridgePrefixFactorsCommuteDeriv D)

def rowCutTelescopedPrefix {arity : Nat} (dist : Nat) (row : Term arity .nat) :
    STerm arity .stab :=
  SC.stabMul (rowCut dist (.natLit 0)) (rowCut dist row)

def colCutTelescopedPrefix {arity : Nat} (dist : Nat) (col : Term arity .nat) :
    STerm arity .stab :=
  SC.stabMul (colCut dist (.natLit 0)) (colCut dist col)

def rowCutTelescopingBody (D : OddSurfaceDistance) : SFormula 1 :=
  .eqStabUpTo (SC.n (nQubits D.distance))
    (SC.stabFold SFormula.boundNat (rowBridge D.distance rightRowVar2))
    (rowCutTelescopedPrefix D.distance rowVar1)

def colCutTelescopingBody (D : OddSurfaceDistance) : SFormula 1 :=
  .eqStabUpTo (SC.n (nQubits D.distance))
    (SC.stabFold SFormula.boundNat (colBridge D.distance rightRowVar2))
    (colCutTelescopedPrefix D.distance rowVar1)

def rowCutTelescopingF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (rowCutTelescopingBody D)

def colCutTelescopingF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (colCutTelescopingBody D)

def rowBridgeFactorsFromNormalizerF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (normalizesOddF D) (rowBridgeFactorsCommuteF D)

def colBridgeFactorsFromNormalizerF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (normalizesOddF D) (colBridgeFactorsCommuteF D)

def bridgeProofFuel (D : OddSurfaceDistance) : Nat :=
  D.distance + 2

def dummyClosedStabilizer : Term 0 .stab :=
  Formula.closedStabilizer (.pauliLit Pauli.I)

def rowBridgeGeneratedClosedF (D : OddSurfaceDistance) : Formula 0 :=
  (rowBridgeGeneratedEqF D).instantiate dummyClosedStabilizer

def colBridgeGeneratedClosedF (D : OddSurfaceDistance) : Formula 0 :=
  (colBridgeGeneratedEqF D).instantiate dummyClosedStabilizer

def rowBridgeGeneratedClosedCheckedAt (D : OddSurfaceDistance) : Bool :=
  Formula.check code.body (bridgeProofFuel D) (rowBridgeGeneratedClosedF D) Env.empty

def colBridgeGeneratedClosedCheckedAt (D : OddSurfaceDistance) : Bool :=
  Formula.check code.body (bridgeProofFuel D) (colBridgeGeneratedClosedF D) Env.empty

theorem rowBridgeGeneratedClosedCheckedAt_sound {D : OddSurfaceDistance} :
    rowBridgeGeneratedClosedCheckedAt D = true ->
      Formula.eval code.body (bridgeProofFuel D) (rowBridgeGeneratedClosedF D) Env.empty =
        some true := by
  intro h
  exact Formula.check_sound h

theorem colBridgeGeneratedClosedCheckedAt_sound {D : OddSurfaceDistance} :
    colBridgeGeneratedClosedCheckedAt D = true ->
      Formula.eval code.body (bridgeProofFuel D) (colBridgeGeneratedClosedF D) Env.empty =
        some true := by
  intro h
  exact Formula.check_sound h

def xRowsOccupiedFromGeometryContextDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [rowCutNoXImpliesCommutesF D, rowCutTelescopingF D,
        rowBridgeFactorsCommuteF D, xNontrivialNormalizerF D]
      (xRowsOccupiedF D) := by
  refine .allNatLtIntroBounded (SC.n D.distance)
    (xRowOccupiedAtF D.distance SC.bound.weaken rowVar1) ?_
  let rowBody := xRowOccupiedAtF D.distance SC.bound.weaken rowVar1
  let noX := SFormula.gridRowNoX D.distance SC.bound.weaken rowVar1
  let n := SC.n (arity := 1) (nQubits D.distance)
  let pref := SC.stabFold SFormula.boundNat (rowBridge D.distance rightRowVar2)
  let cut0 := SC.closed (logicalZOdd D).weaken
  let cutRow := SC.rowZCut D.distance rowVar1
  let ctx := [noX, SFormula.boundNatLt (SC.n (arity := 0) D.distance),
    (rowCutNoXImpliesCommutesF D).weaken, (rowCutTelescopingF D).weaken,
    (rowBridgeFactorsCommuteF D).weaken, (xNontrivialNormalizerF D).weaken]
  have rowLt : SFormula.Deriv ctx
      (SFormula.boundNatLt (SC.n (arity := 0) D.distance)) :=
    .hyp (by right; left)
  have noXDeriv : SFormula.Deriv ctx noX :=
    .assumption
  have nontriv : SFormula.Deriv ctx ((xNontrivialNormalizerF D).weaken) :=
    .hyp (by right; right; right; right; right; left)
  have antiZE : SFormula.Deriv ctx
      (.not (.commutesUpTo n SC.bound.weaken cut0)) := by
    simpa [xNontrivialNormalizerF, anticommutesLogicalZF, n, cut0, SFormula.lift,
      SFormula.weaken, STerm.lift, STerm.weaken, SC.n, SC.bound, logicalZOdd] using
      (SFormula.Deriv.andElimRight nontriv)
  have antiZLeft : SFormula.Deriv ctx
      (.not (.commutesUpTo n cut0 SC.bound.weaken)) :=
    .noncommutesSymm n SC.bound.weaken cut0 antiZE
  have cutComm : SFormula.Deriv ctx
      (.commutesUpTo n cutRow SC.bound.weaken) := by
    have cutRuleGlobal :
        SFormula.Deriv ctx ((rowCutNoXImpliesCommutesF D).weaken) :=
      .hyp (by right; right; left)
    have cutRuleApply :=
      SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat cutRuleGlobal rowLt
    have cutRuleRow :=
      SFormula.Deriv.applyNatBoundNatBeta _ cutRuleApply
    exact .mp
      (by
        simpa [rowCutNoXImpliesCommutesBody, noX, n, cutRow, SFormula.gridRowNoX,
          xSupportAtF, SFormula.xSupportAt, gridIdx, SC.gridIdx] using cutRuleRow)
      noXDeriv
  have noncommProduct : SFormula.Deriv ctx
      (.not (.commutesUpTo n (SC.stabMul cut0 cutRow) SC.bound.weaken)) :=
    .noncommutesStabMulRight n cut0 cutRow SC.bound.weaken antiZLeft cutComm
  have prefixCommBase :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
         (rowBridgeFactorsCommuteF D).weaken]
        (rowBridgePrefixProductCommutesF D) :=
    rowBridgePrefixProductCommutesDeriv D
  have prefixComm : SFormula.Deriv ctx (.commutesUpTo n pref SC.bound.weaken) := by
    simpa [rowBridgePrefixProductCommutesF, n, pref] using
      (SFormula.Deriv.weakenBy
        (Γ := [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
          (rowBridgeFactorsCommuteF D).weaken])
        (Δ := ctx)
        (fun C h => by
          simp [ctx] at h ⊢
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        prefixCommBase)
  have telGlobal : SFormula.Deriv ctx ((rowCutTelescopingF D).weaken) :=
    .hyp (by right; right; right; left)
  have telApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat telGlobal rowLt
  have telRow := SFormula.Deriv.applyNatBoundNatBeta _ telApply
  have telEq : SFormula.Deriv ctx
      (.eqStabUpTo n pref (SC.stabMul cut0 cutRow)) := by
    simpa [rowCutTelescopingF, rowCutTelescopingBody, rowCutTelescopedPrefix,
      rowBridgePrefixProductCommutesF, pref, n, cut0, cutRow, rowCut, SC.rowZCut,
      logicalZOdd, logicalZ, SFormula.lift, SFormula.weaken, STerm.lift, STerm.weaken,
      Term.lift, Term.weaken, Term.weakenVar, SC.n, SC.bound, rightRowVar2, rowVar1]
      using telRow
  have noncommPrefix : SFormula.Deriv ctx
      (.not (.commutesUpTo n pref SC.bound.weaken)) :=
    .noncommutesOfEqLeft n (SC.stabMul cut0 cutRow) pref SC.bound.weaken
      (.eqStabSymm n pref (SC.stabMul cut0 cutRow) telEq)
      noncommProduct
  have contradiction : SFormula.Deriv ctx .bot :=
    .notElim prefixComm noncommPrefix
  have notNoX : SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
       (rowCutNoXImpliesCommutesF D).weaken, (rowCutTelescopingF D).weaken,
       (rowBridgeFactorsCommuteF D).weaken, (xNontrivialNormalizerF D).weaken]
      (.not noX) :=
    .notIntro contradiction
  simpa [rowBody, xRowOccupiedAtF, noX, SFormula.gridRowNoX, xSupportAtF,
    SFormula.xSupportAt, gridIdx, SC.gridIdx] using notNoX

def zColsOccupiedFromGeometryContextDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [colCutNoZImpliesCommutesF D, colCutTelescopingF D,
        colBridgeFactorsCommuteF D, zNontrivialNormalizerF D]
      (zColsOccupiedF D) := by
  refine .allNatLtIntroBounded (SC.n D.distance)
    (zColOccupiedAtF D.distance SC.bound.weaken rowVar1) ?_
  let colBody := zColOccupiedAtF D.distance SC.bound.weaken rowVar1
  let noZ := SFormula.gridColNoZ D.distance SC.bound.weaken rowVar1
  let n := SC.n (arity := 1) (nQubits D.distance)
  let pref := SC.stabFold SFormula.boundNat (colBridge D.distance rightRowVar2)
  let cut0 := SC.closed (logicalXOdd D).weaken
  let cutCol := SC.colXCut D.distance rowVar1
  let ctx := [noZ, SFormula.boundNatLt (SC.n (arity := 0) D.distance),
    (colCutNoZImpliesCommutesF D).weaken, (colCutTelescopingF D).weaken,
    (colBridgeFactorsCommuteF D).weaken, (zNontrivialNormalizerF D).weaken]
  have colLt : SFormula.Deriv ctx
      (SFormula.boundNatLt (SC.n (arity := 0) D.distance)) :=
    .hyp (by right; left)
  have noZDeriv : SFormula.Deriv ctx noZ :=
    .assumption
  have nontriv : SFormula.Deriv ctx ((zNontrivialNormalizerF D).weaken) :=
    .hyp (by right; right; right; right; right; left)
  have antiXE : SFormula.Deriv ctx
      (.not (.commutesUpTo n SC.bound.weaken cut0)) := by
    simpa [zNontrivialNormalizerF, anticommutesLogicalXF, n, cut0, SFormula.lift,
      SFormula.weaken, STerm.lift, STerm.weaken, SC.n, SC.bound, logicalXOdd] using
      (SFormula.Deriv.andElimRight nontriv)
  have antiXLeft : SFormula.Deriv ctx
      (.not (.commutesUpTo n cut0 SC.bound.weaken)) :=
    .noncommutesSymm n SC.bound.weaken cut0 antiXE
  have cutComm : SFormula.Deriv ctx
      (.commutesUpTo n cutCol SC.bound.weaken) := by
    have cutRuleGlobal :
        SFormula.Deriv ctx ((colCutNoZImpliesCommutesF D).weaken) :=
      .hyp (by right; right; left)
    have cutRuleApply :=
      SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat cutRuleGlobal colLt
    have cutRuleCol :=
      SFormula.Deriv.applyNatBoundNatBeta _ cutRuleApply
    exact .mp
      (by
        simpa [colCutNoZImpliesCommutesBody, noZ, n, cutCol, SFormula.gridColNoZ,
          zSupportAtF, SFormula.zSupportAt, gridIdx, SC.gridIdx] using cutRuleCol)
      noZDeriv
  have noncommProduct : SFormula.Deriv ctx
      (.not (.commutesUpTo n (SC.stabMul cut0 cutCol) SC.bound.weaken)) :=
    .noncommutesStabMulRight n cut0 cutCol SC.bound.weaken antiXLeft cutComm
  have prefixCommBase :
      SFormula.Deriv
        [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
         (colBridgeFactorsCommuteF D).weaken]
        (colBridgePrefixProductCommutesF D) :=
    colBridgePrefixProductCommutesDeriv D
  have prefixComm : SFormula.Deriv ctx (.commutesUpTo n pref SC.bound.weaken) := by
    simpa [colBridgePrefixProductCommutesF, n, pref] using
      (SFormula.Deriv.weakenBy
        (Γ := [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
          (colBridgeFactorsCommuteF D).weaken])
        (Δ := ctx)
        (fun C h => by
          simp [ctx] at h ⊢
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        prefixCommBase)
  have telGlobal : SFormula.Deriv ctx ((colCutTelescopingF D).weaken) :=
    .hyp (by right; right; right; left)
  have telApply :=
    SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat telGlobal colLt
  have telCol := SFormula.Deriv.applyNatBoundNatBeta _ telApply
  have telEq : SFormula.Deriv ctx
      (.eqStabUpTo n pref (SC.stabMul cut0 cutCol)) := by
    simpa [colCutTelescopingF, colCutTelescopingBody, colCutTelescopedPrefix,
      colBridgePrefixProductCommutesF, pref, n, cut0, cutCol, colCut, SC.colXCut,
      logicalXOdd, logicalX, SFormula.lift, SFormula.weaken, STerm.lift, STerm.weaken,
      Term.lift, Term.weaken, Term.weakenVar, SC.n, SC.bound, rightRowVar2, rowVar1]
      using telCol
  have noncommPrefix : SFormula.Deriv ctx
      (.not (.commutesUpTo n pref SC.bound.weaken)) :=
    .noncommutesOfEqLeft n (SC.stabMul cut0 cutCol) pref SC.bound.weaken
      (.eqStabSymm n pref (SC.stabMul cut0 cutCol) telEq)
      noncommProduct
  have contradiction : SFormula.Deriv ctx .bot :=
    .notElim prefixComm noncommPrefix
  have notNoZ : SFormula.Deriv
      [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
       (colCutNoZImpliesCommutesF D).weaken, (colCutTelescopingF D).weaken,
       (colBridgeFactorsCommuteF D).weaken, (zNontrivialNormalizerF D).weaken]
      (.not noZ) :=
    .notIntro contradiction
  simpa [colBody, zColOccupiedAtF, noZ, SFormula.gridColNoZ, zSupportAtF,
    SFormula.zSupportAt, gridIdx, SC.gridIdx] using notNoZ

/-- The object-language Surface lower-bound statement with a stabilizer binder. -/
def distanceLowerBoundForallStabF (D : OddSurfaceDistance) :
    ForallStabFormula 0 where
  width := SC.n (nQubits D.distance)
  body := .and (xLowerBoundByGeometryF D) (zLowerBoundByGeometryF D)

def distanceLowerBoundClosedInstanceF
    (D : OddSurfaceDistance) (E : Term 0 .stab) : Formula 0 :=
  (distanceLowerBoundForallStabF D).instantiate E

def distanceLowerBoundClosedInstanceChecked
    (D : OddSurfaceDistance) (E : Term 0 .stab) : Bool :=
  match Formula.deriveTrue? code.body (D.distance + 2) Env.empty
      (distanceLowerBoundClosedInstanceF D E) with
  | some H =>
      (distanceLowerBoundForallStabF D).checkClosedInstance code.body (D.distance + 2) E H
  | none => false

/-- Symbolic geometric lemmas needed for the open lower-bound theorem.

These are proof obligations in the stabilizer-binder logic, not Lean semantic
payloads.  The constructor cannot be filled unless each field is itself a
`SFormula.Deriv` tree.
-/
structure DistanceLowerBoundLemmaDeriv (D : OddSurfaceDistance) where
  xParityPropagation : SFormula.Deriv [] (xParityPropagationRowsF D)
  xRowsWeightLower : SFormula.Deriv [] (xRowsOccupiedWeightLowerF D)
  zParityPropagation : SFormula.Deriv [] (zParityPropagationColsF D)
  zColsWeightLower : SFormula.Deriv [] (zColsOccupiedWeightLowerF D)

/-- A sharper intermediate package: once row/column occupancy has been turned
    into generic support-surjectivity, the counting part of the distance lower
    bound is completely handled by `finiteSurjectiveWeightLower`. -/
structure DistanceLowerBoundSupportDeriv (D : OddSurfaceDistance) where
  xParityPropagation : SFormula.Deriv [] (xParityPropagationRowsF D)
  xRowsSupportSurjective : SFormula.Deriv [] (xRowsOccupiedSupportSurjectiveF D)
  zParityPropagation : SFormula.Deriv [] (zParityPropagationColsF D)
  zColsSupportSurjective : SFormula.Deriv [] (zColsOccupiedSupportSurjectiveF D)

namespace DistanceLowerBoundSupportDeriv

def toLemmaDeriv {D : OddSurfaceDistance} (G : DistanceLowerBoundSupportDeriv D) :
    DistanceLowerBoundLemmaDeriv D where
  xParityPropagation := G.xParityPropagation
  xRowsWeightLower := xRowsWeightLowerFromSupportImpDeriv G.xRowsSupportSurjective
  zParityPropagation := G.zParityPropagation
  zColsWeightLower := zColsWeightLowerFromSupportImpDeriv G.zColsSupportSurjective

def check {D : OddSurfaceDistance} (G : DistanceLowerBoundSupportDeriv D) : Bool :=
  G.xParityPropagation.check && G.xRowsSupportSurjective.check &&
    G.zParityPropagation.check && G.zColsSupportSurjective.check

def assembledCheck {D : OddSurfaceDistance} (G : DistanceLowerBoundSupportDeriv D) : Bool :=
  G.toLemmaDeriv.xParityPropagation.check && G.toLemmaDeriv.xRowsWeightLower.check &&
    G.toLemmaDeriv.zParityPropagation.check && G.toLemmaDeriv.zColsWeightLower.check

def size {D : OddSurfaceDistance} (G : DistanceLowerBoundSupportDeriv D) : Nat :=
  G.xParityPropagation.size + G.xRowsSupportSurjective.size +
    G.zParityPropagation.size + G.zColsSupportSurjective.size

def assembledSize {D : OddSurfaceDistance} (G : DistanceLowerBoundSupportDeriv D) : Nat :=
  G.toLemmaDeriv.xParityPropagation.size + G.toLemmaDeriv.xRowsWeightLower.size +
    G.toLemmaDeriv.zParityPropagation.size + G.toLemmaDeriv.zColsWeightLower.size

end DistanceLowerBoundSupportDeriv

namespace DistanceLowerBoundLemmaDeriv

def xLowerBoundDeriv {D : OddSurfaceDistance} (G : DistanceLowerBoundLemmaDeriv D) :
    SFormula.Deriv [] (xLowerBoundByGeometryF D) :=
  let hNontriv : SFormula.Deriv [xNontrivialNormalizerF D] (xNontrivialNormalizerF D) :=
    .assumption
  let hRows : SFormula.Deriv [xNontrivialNormalizerF D] (xRowsOccupiedF D) :=
    .mp G.xParityPropagation.weakenContext hNontriv
  let hWeight :
      SFormula.Deriv [xNontrivialNormalizerF D]
        (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1)))) :=
    .mp G.xRowsWeightLower.weakenContext hRows
  .impIntro hWeight

def zLowerBoundDeriv {D : OddSurfaceDistance} (G : DistanceLowerBoundLemmaDeriv D) :
    SFormula.Deriv [] (zLowerBoundByGeometryF D) :=
  let hNontriv : SFormula.Deriv [zNontrivialNormalizerF D] (zNontrivialNormalizerF D) :=
    .assumption
  let hCols : SFormula.Deriv [zNontrivialNormalizerF D] (zColsOccupiedF D) :=
    .mp G.zParityPropagation.weakenContext hNontriv
  let hWeight :
      SFormula.Deriv [zNontrivialNormalizerF D]
        (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1)))) :=
    .mp G.zColsWeightLower.weakenContext hCols
  .impIntro hWeight

def toForallStabDeriv {D : OddSurfaceDistance} (G : DistanceLowerBoundLemmaDeriv D) :
    ForallStabDeriv (distanceLowerBoundForallStabF D) :=
  .intro <| .andIntro G.xLowerBoundDeriv G.zLowerBoundDeriv

def size {D : OddSurfaceDistance} (G : DistanceLowerBoundLemmaDeriv D) : Nat :=
  G.xParityPropagation.size + G.xRowsWeightLower.size +
    G.zParityPropagation.size + G.zColsWeightLower.size

def assembledSize {D : OddSurfaceDistance} (G : DistanceLowerBoundLemmaDeriv D) : Nat :=
  G.toForallStabDeriv.size

def check {D : OddSurfaceDistance} (G : DistanceLowerBoundLemmaDeriv D) : Bool :=
  G.xParityPropagation.check && G.xRowsWeightLower.check &&
    G.zParityPropagation.check && G.zColsWeightLower.check

end DistanceLowerBoundLemmaDeriv

/-! ### Bounded-forall views for the geometric proof

These are small, reusable derivation fragments in the stabilizer-binder logic.
They do not prove the geometric lemmas by themselves; they expose the row or
column instance that a later counting/propagation derivation must use.
-/

def xRowsOccupiedApplyDeriv (D : OddSurfaceDistance) (row : STerm 0 .nat) :
    SFormula.Deriv
      [xRowsOccupiedF D, SFormula.witnessLt row (SC.n D.distance)]
      (.applyNat row (xRowOccupiedAtF D.distance SC.bound.weaken rowVar1)) :=
  .allNatLtElim (SC.n D.distance)
    (xRowOccupiedAtF D.distance SC.bound.weaken rowVar1)
    row
    (.hyp (by simp [xRowsOccupiedF]))
    (.hyp (by simp))

def zColsOccupiedApplyDeriv (D : OddSurfaceDistance) (col : STerm 0 .nat) :
    SFormula.Deriv
      [zColsOccupiedF D, SFormula.witnessLt col (SC.n D.distance)]
      (.applyNat col (zColOccupiedAtF D.distance SC.bound.weaken rowVar1)) :=
  .allNatLtElim (SC.n D.distance)
    (zColOccupiedAtF D.distance SC.bound.weaken rowVar1)
    col
    (.hyp (by simp [zColsOccupiedF]))
    (.hyp (by simp))

def xRowsOccupiedApplyChecked (D : OddSurfaceDistance) (row : STerm 0 .nat) : Bool :=
  (xRowsOccupiedApplyDeriv D row).check

def zColsOccupiedApplyChecked (D : OddSurfaceDistance) (col : STerm 0 .nat) : Bool :=
  (zColsOccupiedApplyDeriv D col).check

def xRowHasSupportF (D : OddSurfaceDistance) : SFormula 1 :=
  .existsNatLt (SC.n D.distance) <|
    xSupportAtF SC.bound.weaken.weaken
      (gridIdx (.natLit D.distance) rowVar1.weaken colVar)

def zColHasSupportF (D : OddSurfaceDistance) : SFormula 1 :=
  .existsNatLt (SC.n D.distance) <|
    zSupportAtF SC.bound.weaken.weaken
      (gridIdx (.natLit D.distance) colVar rowVar1.weaken)

def xRowOccupiedDeMorganDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [xRowOccupiedAtF D.distance SC.bound.weaken rowVar1]
      (xRowHasSupportF D) :=
  .finiteDeMorgan (SC.n D.distance)
    (xSupportAtF SC.bound.weaken.weaken
      (gridIdx (.natLit D.distance) rowVar1.weaken colVar)) <|
      .hyp (by simp [xRowOccupiedAtF])

def zColOccupiedDeMorganDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [zColOccupiedAtF D.distance SC.bound.weaken rowVar1]
      (zColHasSupportF D) :=
  .finiteDeMorgan (SC.n D.distance)
    (zSupportAtF SC.bound.weaken.weaken
      (gridIdx (.natLit D.distance) colVar rowVar1.weaken)) <|
      .hyp (by simp [zColOccupiedAtF])

def xRowOccupiedDeMorganChecked (D : OddSurfaceDistance) : Bool :=
  (xRowOccupiedDeMorganDeriv D).check

def zColOccupiedDeMorganChecked (D : OddSurfaceDistance) : Bool :=
  (zColOccupiedDeMorganDeriv D).check

def xRowsOccupiedAllRowsSupportF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (xRowHasSupportF D)

def zColsOccupiedAllColsSupportF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (zColHasSupportF D)

def xRowsOccupiedAllRowsSupportDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (.imp (xRowsOccupiedF D) (xRowsOccupiedAllRowsSupportF D)) :=
  .impIntro <|
    .allNatLtIntroBounded (SC.n D.distance) (xRowHasSupportF D) <|
      let hApply :
          SFormula.Deriv
            [SFormula.boundNatLt (SC.n (arity := 0) D.distance), (xRowsOccupiedF D).weaken]
            (.applyNat SFormula.boundNat
              ((xRowOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)) :=
        .allNatLtElim (SC.n (arity := 1) D.distance)
          ((xRowOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)
          SFormula.boundNat
          (.hyp (by
            simp [SFormula.boundNatLt, SFormula.weaken, SFormula.lift, STerm.lift,
              Term.lift, SC.n, xRowsOccupiedF]))
          .assumption
      let hOcc :
          SFormula.Deriv
            [SFormula.boundNatLt (SC.n (arity := 0) D.distance), (xRowsOccupiedF D).weaken]
            (xRowOccupiedAtF D.distance SC.bound.weaken rowVar1) :=
        .applyNatBoundNatBeta
          (xRowOccupiedAtF D.distance SC.bound.weaken rowVar1)
          hApply
      let hDemorgan :
          SFormula.Deriv
            [SFormula.boundNatLt (SC.n (arity := 0) D.distance), (xRowsOccupiedF D).weaken]
            (.imp (xRowOccupiedAtF D.distance SC.bound.weaken rowVar1) (xRowHasSupportF D)) :=
        SFormula.Deriv.weakenBy (fun _ h => by cases h) <|
          .impIntro (xRowOccupiedDeMorganDeriv D)
      .mp hDemorgan hOcc

def zColsOccupiedAllColsSupportDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (.imp (zColsOccupiedF D) (zColsOccupiedAllColsSupportF D)) :=
  .impIntro <|
    .allNatLtIntroBounded (SC.n D.distance) (zColHasSupportF D) <|
      let hApply :
          SFormula.Deriv
            [SFormula.boundNatLt (SC.n (arity := 0) D.distance), (zColsOccupiedF D).weaken]
            (.applyNat SFormula.boundNat
              ((zColOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)) :=
        .allNatLtElim (SC.n (arity := 1) D.distance)
          ((zColOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)
          SFormula.boundNat
          (.hyp (by
            simp [SFormula.boundNatLt, SFormula.weaken, SFormula.lift, STerm.lift,
              Term.lift, SC.n, zColsOccupiedF]))
          .assumption
      let hOcc :
          SFormula.Deriv
            [SFormula.boundNatLt (SC.n (arity := 0) D.distance), (zColsOccupiedF D).weaken]
            (zColOccupiedAtF D.distance SC.bound.weaken rowVar1) :=
        .applyNatBoundNatBeta
          (zColOccupiedAtF D.distance SC.bound.weaken rowVar1)
          hApply
      let hDemorgan :
          SFormula.Deriv
            [SFormula.boundNatLt (SC.n (arity := 0) D.distance), (zColsOccupiedF D).weaken]
            (.imp (zColOccupiedAtF D.distance SC.bound.weaken rowVar1) (zColHasSupportF D)) :=
        SFormula.Deriv.weakenBy (fun _ h => by cases h) <|
          .impIntro (zColOccupiedDeMorganDeriv D)
      .mp hDemorgan hOcc

def xRowsOccupiedAllRowsSupportChecked (D : OddSurfaceDistance) : Bool :=
  (xRowsOccupiedAllRowsSupportDeriv D).check

def zColsOccupiedAllColsSupportChecked (D : OddSurfaceDistance) : Bool :=
  (zColsOccupiedAllColsSupportDeriv D).check

def xSupportNonIDeriv {arity : Nat} (E : STerm arity .stab) (q : Term arity .nat) :
    SFormula.Deriv [xSupportAtF E q] (SFormula.nonIAt E (SC.closed q)) :=
  .pauliAnticommutesNonI
    (.stabAt E (SC.closed q))
    (SC.p Pauli.Z)
    .assumption

def zSupportNonIDeriv {arity : Nat} (E : STerm arity .stab) (q : Term arity .nat) :
    SFormula.Deriv [zSupportAtF E q] (SFormula.nonIAt E (SC.closed q)) :=
  .pauliAnticommutesNonI
    (.stabAt E (SC.closed q))
    (SC.p Pauli.X)
    .assumption

def gridIdxPureNat2 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm
      (gridIdx (.natLit D.distance) rowVar1.weaken colVar) :=
  SFormula.PureNatTerm.gridIdxLeft
    (SFormula.PureNatTerm.nat (arity := 2) D.distance)
    (SFormula.PureNatTerm.var (arity := 2) ⟨1, by decide⟩)
    (SFormula.PureNatTerm.var (arity := 2) ⟨0, by decide⟩)

def gridIdxTransposePureNat2 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm
      (gridIdx (.natLit D.distance) colVar rowVar1.weaken) :=
  SFormula.PureNatTerm.gridIdxLeft
    (SFormula.PureNatTerm.nat (arity := 2) D.distance)
    (SFormula.PureNatTerm.var (arity := 2) ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var (arity := 2) ⟨1, by decide⟩)

def xSupportWitnessToSurjectiveBodyDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [xSupportAtF SC.bound.weaken.weaken
          (gridIdx (.natLit D.distance) rowVar1.weaken colVar),
       SFormula.boundNatLt (SC.n (arity := 1) D.distance),
       (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
       (xRowsOccupiedAllRowsSupportF D).weaken.weaken]
      ((SFormula.supportSurjectiveBody
        (SC.n (arity := 0) (nQubits D.distance))
        SC.bound
        (gridRowOf D.distance)).weaken) := by
  let qTerm : Term 2 .nat := gridIdx (.natLit D.distance) rowVar1.weaken colVar
  let rowLt :
      SFormula.Deriv
        [xSupportAtF SC.bound.weaken.weaken
            (gridIdx (.natLit D.distance) rowVar1.weaken colVar),
         SFormula.boundNatLt (SC.n (arity := 1) D.distance),
         (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
         (xRowsOccupiedAllRowsSupportF D).weaken.weaken]
        (SFormula.witnessLt (SC.closed rowVar1.weaken) (SC.n D.distance)) :=
    .hyp (by right; right; left)
  let colLt :
      SFormula.Deriv
        [xSupportAtF SC.bound.weaken.weaken
            (gridIdx (.natLit D.distance) rowVar1.weaken colVar),
         SFormula.boundNatLt (SC.n (arity := 1) D.distance),
         (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
         (xRowsOccupiedAllRowsSupportF D).weaken.weaken]
        (SFormula.witnessLt (SC.closed colVar) (SC.n D.distance)) :=
    .hyp (by right; left)
  refine .existsNatLtIntroTerm _ _ (SC.closed qTerm) ?lt ?body
  · exact .gridIdxLeftLtSquare D.distance rowVar1.weaken colVar rowLt colLt
  · refine .applyNatSubstitutionBeta qTerm _ (gridIdxPureNat2 D) ?_
    let nonI :
        SFormula.Deriv
          [xSupportAtF SC.bound.weaken.weaken
              (gridIdx (.natLit D.distance) rowVar1.weaken colVar),
           SFormula.boundNatLt (SC.n (arity := 1) D.distance),
           (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
           (xRowsOccupiedAllRowsSupportF D).weaken.weaken]
          (SFormula.nonIAt SC.bound.weaken.weaken (SC.closed qTerm)) :=
      .pauliAnticommutesNonI
        (.stabAt SC.bound.weaken.weaken (SC.closed qTerm))
        (SC.p Pauli.Z)
        (.hyp (by left))
    let rowEq :
        SFormula.Deriv
          [xSupportAtF SC.bound.weaken.weaken
              (gridIdx (.natLit D.distance) rowVar1.weaken colVar),
           SFormula.boundNatLt (SC.n (arity := 1) D.distance),
           (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
           (xRowsOccupiedAllRowsSupportF D).weaken.weaken]
          (.eqNat (SC.closed (NatArithmetic.rowOf qTerm (.natLit D.distance)))
            (SC.closed rowVar1.weaken)) :=
      .gridIdxLeftDivEq D.distance rowVar1.weaken colVar rowLt colLt
    simpa [qTerm, gridRowOf, SFormula.instantiateTopNat, SFormula.instantiateNatAt,
      SFormula.lift, SFormula.weaken, SFormula.nonIAt, SFormula.boundNat,
      STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt,
      Term.lift, Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.p, SC.bound,
      rowVar1, colVar, gridIdx, NatArithmetic.rowOf]
      using (SFormula.Deriv.andIntro nonI rowEq)

def zSupportWitnessToSurjectiveBodyDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [zSupportAtF SC.bound.weaken.weaken
          (gridIdx (.natLit D.distance) colVar rowVar1.weaken),
       SFormula.boundNatLt (SC.n (arity := 1) D.distance),
       (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
       (zColsOccupiedAllColsSupportF D).weaken.weaken]
      ((SFormula.supportSurjectiveBody
        (SC.n (arity := 0) (nQubits D.distance))
        SC.bound
        (gridColOf D.distance)).weaken) := by
  let qTerm : Term 2 .nat := gridIdx (.natLit D.distance) colVar rowVar1.weaken
  let rowLt :
      SFormula.Deriv
        [zSupportAtF SC.bound.weaken.weaken
            (gridIdx (.natLit D.distance) colVar rowVar1.weaken),
         SFormula.boundNatLt (SC.n (arity := 1) D.distance),
         (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
         (zColsOccupiedAllColsSupportF D).weaken.weaken]
        (SFormula.witnessLt (SC.closed colVar) (SC.n D.distance)) :=
    .hyp (by right; left)
  let colLt :
      SFormula.Deriv
        [zSupportAtF SC.bound.weaken.weaken
            (gridIdx (.natLit D.distance) colVar rowVar1.weaken),
         SFormula.boundNatLt (SC.n (arity := 1) D.distance),
         (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
         (zColsOccupiedAllColsSupportF D).weaken.weaken]
        (SFormula.witnessLt (SC.closed rowVar1.weaken) (SC.n D.distance)) :=
    .hyp (by right; right; left)
  refine .existsNatLtIntroTerm _ _ (SC.closed qTerm) ?lt ?body
  · exact .gridIdxLeftLtSquare D.distance colVar rowVar1.weaken rowLt colLt
  · refine .applyNatSubstitutionBeta qTerm _ (gridIdxTransposePureNat2 D) ?_
    let nonI :
        SFormula.Deriv
          [zSupportAtF SC.bound.weaken.weaken
              (gridIdx (.natLit D.distance) colVar rowVar1.weaken),
           SFormula.boundNatLt (SC.n (arity := 1) D.distance),
           (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
           (zColsOccupiedAllColsSupportF D).weaken.weaken]
          (SFormula.nonIAt SC.bound.weaken.weaken (SC.closed qTerm)) :=
      .pauliAnticommutesNonI
        (.stabAt SC.bound.weaken.weaken (SC.closed qTerm))
        (SC.p Pauli.X)
        (.hyp (by left))
    let colEq :
        SFormula.Deriv
          [zSupportAtF SC.bound.weaken.weaken
              (gridIdx (.natLit D.distance) colVar rowVar1.weaken),
           SFormula.boundNatLt (SC.n (arity := 1) D.distance),
           (SFormula.boundNatLt (SC.n (arity := 0) D.distance)).weaken,
           (zColsOccupiedAllColsSupportF D).weaken.weaken]
          (.eqNat (SC.closed (NatArithmetic.colOf qTerm (.natLit D.distance)))
            (SC.closed rowVar1.weaken)) :=
      .gridIdxLeftModEq D.distance colVar rowVar1.weaken rowLt colLt
    simpa [qTerm, gridColOf, SFormula.instantiateTopNat, SFormula.instantiateNatAt,
      SFormula.lift, SFormula.weaken, SFormula.nonIAt, SFormula.boundNat,
      STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt,
      Term.lift, Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.p, SC.bound,
      rowVar1, colVar, gridIdx, NatArithmetic.colOf]
      using (SFormula.Deriv.andIntro nonI colEq)

def xRowsSupportSurjectiveFromAllRowsSupportDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [xRowsOccupiedAllRowsSupportF D] (xRowsSupportSurjectiveF D) :=
  .allNatLtIntroBounded (SC.n D.distance)
    (SFormula.supportSurjectiveBody
      (SC.n (nQubits D.distance)) SC.bound (gridRowOf D.distance)) <|
    let hApply :
        SFormula.Deriv
          [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
           (xRowsOccupiedAllRowsSupportF D).weaken]
          (.applyNat SFormula.boundNat ((xRowHasSupportF D).lift 1)) :=
      .allNatLtElim (SC.n (arity := 1) D.distance)
        ((xRowHasSupportF D).lift 1)
        SFormula.boundNat
        (.hyp (by
          simp [xRowsOccupiedAllRowsSupportF, SFormula.boundNatLt,
            SFormula.weaken, SFormula.lift, STerm.lift, Term.lift, SC.n]))
        .assumption
    let hExists :
        SFormula.Deriv
          [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
           (xRowsOccupiedAllRowsSupportF D).weaken]
          (xRowHasSupportF D) :=
      .applyNatBoundNatBeta (xRowHasSupportF D) hApply
    .existsNatLtElim (SC.n D.distance)
      (xSupportAtF SC.bound.weaken.weaken
        (gridIdx (.natLit D.distance) rowVar1.weaken colVar))
      (SFormula.supportSurjectiveBody
        (SC.n (nQubits D.distance)) SC.bound (gridRowOf D.distance))
      hExists
      (xSupportWitnessToSurjectiveBodyDeriv D)

def zColsSupportSurjectiveFromAllColsSupportDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [zColsOccupiedAllColsSupportF D] (zColsSupportSurjectiveF D) :=
  .allNatLtIntroBounded (SC.n D.distance)
    (SFormula.supportSurjectiveBody
      (SC.n (nQubits D.distance)) SC.bound (gridColOf D.distance)) <|
    let hApply :
        SFormula.Deriv
          [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
           (zColsOccupiedAllColsSupportF D).weaken]
          (.applyNat SFormula.boundNat ((zColHasSupportF D).lift 1)) :=
      .allNatLtElim (SC.n (arity := 1) D.distance)
        ((zColHasSupportF D).lift 1)
        SFormula.boundNat
        (.hyp (by
          simp [zColsOccupiedAllColsSupportF, SFormula.boundNatLt,
            SFormula.weaken, SFormula.lift, STerm.lift, Term.lift, SC.n]))
        .assumption
    let hExists :
        SFormula.Deriv
          [SFormula.boundNatLt (SC.n (arity := 0) D.distance),
           (zColsOccupiedAllColsSupportF D).weaken]
          (zColHasSupportF D) :=
      .applyNatBoundNatBeta (zColHasSupportF D) hApply
    .existsNatLtElim (SC.n D.distance)
      (zSupportAtF SC.bound.weaken.weaken
        (gridIdx (.natLit D.distance) colVar rowVar1.weaken))
      (SFormula.supportSurjectiveBody
        (SC.n (nQubits D.distance)) SC.bound (gridColOf D.distance))
      hExists
      (zSupportWitnessToSurjectiveBodyDeriv D)

def xRowsOccupiedSupportSurjectiveDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (xRowsOccupiedSupportSurjectiveF D) :=
  .impIntro <|
    let hAll :
        SFormula.Deriv [xRowsOccupiedF D] (xRowsOccupiedAllRowsSupportF D) :=
      .mp (xRowsOccupiedAllRowsSupportDeriv D).weakenContext .assumption
    let hAllImp :
        SFormula.Deriv [] (.imp (xRowsOccupiedAllRowsSupportF D) (xRowsSupportSurjectiveF D)) :=
      .impIntro (xRowsSupportSurjectiveFromAllRowsSupportDeriv D)
    .mp hAllImp.weakenContext hAll

def zColsOccupiedSupportSurjectiveDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (zColsOccupiedSupportSurjectiveF D) :=
  .impIntro <|
    let hAll :
        SFormula.Deriv [zColsOccupiedF D] (zColsOccupiedAllColsSupportF D) :=
      .mp (zColsOccupiedAllColsSupportDeriv D).weakenContext .assumption
    let hAllImp :
        SFormula.Deriv [] (.imp (zColsOccupiedAllColsSupportF D) (zColsSupportSurjectiveF D)) :=
      .impIntro (zColsSupportSurjectiveFromAllColsSupportDeriv D)
    .mp hAllImp.weakenContext hAll

def xRowsOccupiedSupportSurjectiveChecked (D : OddSurfaceDistance) : Bool :=
  (xRowsOccupiedSupportSurjectiveDeriv D).check

def zColsOccupiedSupportSurjectiveChecked (D : OddSurfaceDistance) : Bool :=
  (zColsOccupiedSupportSurjectiveDeriv D).check

def xRowsWeightLowerByCountingDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (xRowsOccupiedWeightLowerF D) :=
  xRowsWeightLowerFromSupportImpDeriv (xRowsOccupiedSupportSurjectiveDeriv D)

def zColsWeightLowerByCountingDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (zColsOccupiedWeightLowerF D) :=
  zColsWeightLowerFromSupportImpDeriv (zColsOccupiedSupportSurjectiveDeriv D)

def distanceLowerBoundFromParityDeriv (D : OddSurfaceDistance)
    (xParity : SFormula.Deriv [] (xParityPropagationRowsF D))
    (zParity : SFormula.Deriv [] (zParityPropagationColsF D)) :
    DistanceLowerBoundLemmaDeriv D where
  xParityPropagation := xParity
  xRowsWeightLower := xRowsWeightLowerByCountingDeriv D
  zParityPropagation := zParity
  zColsWeightLower := zColsWeightLowerByCountingDeriv D

/-! ### Family-indexed lower-bound assembly

The generated strip-bridge equalities, strip-index range facts, and closed
cut-product telescoping facts are all closed with respect to the bound
stabilizer, but true only for the recursive Surface code AST.  They are routed
through `FamilyDeriv.checkedBoundFree`; the remaining open propagation and
counting steps stay as ordinary symbolic stabilizer-binder derivations.
-/

def rowBridgeGeneratedFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (rowBridgeGeneratedEqF D) :=
  .checkedBoundFree _

def colBridgeGeneratedFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (colBridgeGeneratedEqF D) :=
  .checkedBoundFree _

def rowZStripIndexInRangeFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (rowZStripIndexInRangeF D) :=
  .checkedBoundFree _

def colXStripIndexInRangeFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (colXStripIndexInRangeF D) :=
  .checkedBoundFree _

def rowCutTelescopingFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (rowCutTelescopingF D) :=
  .checkedBoundFree _

def colCutTelescopingFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (colCutTelescopingF D) :=
  .checkedBoundFree _

def rowBridgeFactorsFromFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (rowBridgeFactorsFromNormalizerF D) := by
  simpa [rowBridgeFactorsFromNormalizerF] using
    (FamilyDeriv.cut2 (rowBridgeFactorsFromGeneratedNormalizerDeriv D)
      (rowBridgeGeneratedFamilyDeriv D)
      (rowZStripIndexInRangeFamilyDeriv D))

def colBridgeFactorsFromFamilyDeriv (D : OddSurfaceDistance) :
    FamilyDeriv code.body (bridgeProofFuel D) (colBridgeFactorsFromNormalizerF D) := by
  simpa [colBridgeFactorsFromNormalizerF] using
    (FamilyDeriv.cut2 (colBridgeFactorsFromGeneratedNormalizerDeriv D)
      (colBridgeGeneratedFamilyDeriv D)
      (colXStripIndexInRangeFamilyDeriv D))

/-- Surface-local open cut obligations.

These formulas still mention the arbitrary stabilizer bound by
`ForallStabFormula`, so they cannot be discharged by the bound-free executable
family checker.  Keeping them in this explicit package prevents the generic
`SFormula.Deriv` trusted core from containing Surface/grid/cut-specific rules.
-/
structure SurfaceCutCommuteFamilyDeriv (D : OddSurfaceDistance) where
  rowNoXCommutes :
    FamilyDeriv code.body (bridgeProofFuel D) (rowCutNoXImpliesCommutesF D)
  colNoZCommutes :
    FamilyDeriv code.body (bridgeProofFuel D) (colCutNoZImpliesCommutesF D)

namespace SurfaceCutCommuteFamilyDeriv

def check {D : OddSurfaceDistance} (O : SurfaceCutCommuteFamilyDeriv D) : Bool :=
  FamilyDeriv.check O.rowNoXCommutes && FamilyDeriv.check O.colNoZCommutes

def size {D : OddSurfaceDistance} (O : SurfaceCutCommuteFamilyDeriv D) : Nat :=
  FamilyDeriv.size O.rowNoXCommutes + FamilyDeriv.size O.colNoZCommutes

end SurfaceCutCommuteFamilyDeriv

def surfaceCutCommuteFamilyDeriv (D : OddSurfaceDistance) :
    SurfaceCutCommuteFamilyDeriv D where
  rowNoXCommutes := .core (rowCutNoXImpliesCommutesDeriv D)
  colNoZCommutes := .core (colCutNoZImpliesCommutesDeriv D)

def xParityPropagationRowsFromBridgeFactorsDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [rowCutNoXImpliesCommutesF D, rowCutTelescopingF D,
        rowBridgeFactorsFromNormalizerF D]
      (xParityPropagationRowsF D) := by
  refine .impIntro ?_
  let ctx := [xNontrivialNormalizerF D, rowCutNoXImpliesCommutesF D, rowCutTelescopingF D,
    rowBridgeFactorsFromNormalizerF D]
  let hNontriv : SFormula.Deriv ctx (xNontrivialNormalizerF D) := .assumption
  let hNorm : SFormula.Deriv ctx (normalizesOddF D) := .andElimLeft hNontriv
  let hBridgeRule : SFormula.Deriv ctx (rowBridgeFactorsFromNormalizerF D) :=
    .hyp (by right; right; right; left)
  let hBridge : SFormula.Deriv ctx (rowBridgeFactorsCommuteF D) :=
    .mp hBridgeRule hNorm
  let hRowsRuleBase :
      SFormula.Deriv
        [rowBridgeFactorsCommuteF D, xNontrivialNormalizerF D,
          rowCutNoXImpliesCommutesF D, rowCutTelescopingF D]
        (xRowsOccupiedF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [rowCutNoXImpliesCommutesF D, rowCutTelescopingF D,
        rowBridgeFactorsCommuteF D, xNontrivialNormalizerF D])
      (Δ := [rowBridgeFactorsCommuteF D, xNontrivialNormalizerF D,
        rowCutNoXImpliesCommutesF D, rowCutTelescopingF D])
      (fun C h => by
        simp at h ⊢
        rcases h with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
      (xRowsOccupiedFromGeometryContextDeriv D)
  let hRows :
      SFormula.Deriv
        [rowBridgeFactorsCommuteF D, xNontrivialNormalizerF D,
          rowCutNoXImpliesCommutesF D, rowCutTelescopingF D,
          rowBridgeFactorsFromNormalizerF D]
        (xRowsOccupiedF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [rowBridgeFactorsCommuteF D, xNontrivialNormalizerF D,
        rowCutNoXImpliesCommutesF D, rowCutTelescopingF D])
      (Δ := [rowBridgeFactorsCommuteF D, xNontrivialNormalizerF D,
        rowCutNoXImpliesCommutesF D, rowCutTelescopingF D,
        rowBridgeFactorsFromNormalizerF D])
      (fun C h => by
        simp at h ⊢
        rcases h with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
      hRowsRuleBase
  exact .mp (.impIntro hRows) hBridge

def zParityPropagationColsFromBridgeFactorsDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [colCutNoZImpliesCommutesF D, colCutTelescopingF D,
        colBridgeFactorsFromNormalizerF D]
      (zParityPropagationColsF D) := by
  refine .impIntro ?_
  let ctx := [zNontrivialNormalizerF D, colCutNoZImpliesCommutesF D, colCutTelescopingF D,
    colBridgeFactorsFromNormalizerF D]
  let hNontriv : SFormula.Deriv ctx (zNontrivialNormalizerF D) := .assumption
  let hNorm : SFormula.Deriv ctx (normalizesOddF D) := .andElimLeft hNontriv
  let hBridgeRule : SFormula.Deriv ctx (colBridgeFactorsFromNormalizerF D) :=
    .hyp (by right; right; right; left)
  let hBridge : SFormula.Deriv ctx (colBridgeFactorsCommuteF D) :=
    .mp hBridgeRule hNorm
  let hColsRuleBase :
      SFormula.Deriv
        [colBridgeFactorsCommuteF D, zNontrivialNormalizerF D,
          colCutNoZImpliesCommutesF D, colCutTelescopingF D]
        (zColsOccupiedF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [colCutNoZImpliesCommutesF D, colCutTelescopingF D,
        colBridgeFactorsCommuteF D, zNontrivialNormalizerF D])
      (Δ := [colBridgeFactorsCommuteF D, zNontrivialNormalizerF D,
        colCutNoZImpliesCommutesF D, colCutTelescopingF D])
      (fun C h => by
        simp at h ⊢
        rcases h with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
      (zColsOccupiedFromGeometryContextDeriv D)
  let hCols :
      SFormula.Deriv
        [colBridgeFactorsCommuteF D, zNontrivialNormalizerF D,
          colCutNoZImpliesCommutesF D, colCutTelescopingF D,
          colBridgeFactorsFromNormalizerF D]
        (zColsOccupiedF D) :=
    SFormula.Deriv.weakenBy
      (Γ := [colBridgeFactorsCommuteF D, zNontrivialNormalizerF D,
        colCutNoZImpliesCommutesF D, colCutTelescopingF D])
      (Δ := [colBridgeFactorsCommuteF D, zNontrivialNormalizerF D,
        colCutNoZImpliesCommutesF D, colCutTelescopingF D,
        colBridgeFactorsFromNormalizerF D])
      (fun C h => by
        simp at h ⊢
        rcases h with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
      hColsRuleBase
  exact .mp (.impIntro hCols) hBridge

def xParityPropagationRowsFamilyDeriv
    (D : OddSurfaceDistance) (O : SurfaceCutCommuteFamilyDeriv D) :
    FamilyDeriv code.body (bridgeProofFuel D) (xParityPropagationRowsF D) :=
  FamilyDeriv.cut3 (xParityPropagationRowsFromBridgeFactorsDeriv D)
    O.rowNoXCommutes
    (rowCutTelescopingFamilyDeriv D)
    (rowBridgeFactorsFromFamilyDeriv D)

def zParityPropagationColsFamilyDeriv
    (D : OddSurfaceDistance) (O : SurfaceCutCommuteFamilyDeriv D) :
    FamilyDeriv code.body (bridgeProofFuel D) (zParityPropagationColsF D) :=
  FamilyDeriv.cut3 (zParityPropagationColsFromBridgeFactorsDeriv D)
    O.colNoZCommutes
    (colCutTelescopingFamilyDeriv D)
    (colBridgeFactorsFromFamilyDeriv D)

def distanceLowerBoundBodyFromFamilyLemmasDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv
      [xParityPropagationRowsF D, xRowsOccupiedWeightLowerF D,
        zParityPropagationColsF D, zColsOccupiedWeightLowerF D]
      (distanceLowerBoundForallStabF D).body := by
  let ctx :=
    [xParityPropagationRowsF D, xRowsOccupiedWeightLowerF D,
      zParityPropagationColsF D, zColsOccupiedWeightLowerF D]
  let xParity : SFormula.Deriv ctx (xParityPropagationRowsF D) := .assumption
  let xWeight : SFormula.Deriv ctx (xRowsOccupiedWeightLowerF D) := .hyp (by right; left)
  let zParity : SFormula.Deriv ctx (zParityPropagationColsF D) :=
    .hyp (by right; right; left)
  let zWeight : SFormula.Deriv ctx (zColsOccupiedWeightLowerF D) :=
    .hyp (by right; right; right; left)
  let xNontriv :
      SFormula.Deriv (xNontrivialNormalizerF D :: ctx) (xNontrivialNormalizerF D) :=
    .assumption
  let xRows : SFormula.Deriv (xNontrivialNormalizerF D :: ctx) (xRowsOccupiedF D) :=
    .mp xParity.weakenContext xNontriv
  let xNotWeight :
      SFormula.Deriv (xNontrivialNormalizerF D :: ctx)
        (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1)))) :=
    .mp xWeight.weakenContext xRows
  let xLower : SFormula.Deriv ctx (xLowerBoundByGeometryF D) :=
    .impIntro xNotWeight
  let zNontriv :
      SFormula.Deriv (zNontrivialNormalizerF D :: ctx) (zNontrivialNormalizerF D) :=
    .assumption
  let zCols : SFormula.Deriv (zNontrivialNormalizerF D :: ctx) (zColsOccupiedF D) :=
    .mp zParity.weakenContext zNontriv
  let zNotWeight :
      SFormula.Deriv (zNontrivialNormalizerF D :: ctx)
        (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1)))) :=
    .mp zWeight.weakenContext zCols
  let zLower : SFormula.Deriv ctx (zLowerBoundByGeometryF D) :=
    .impIntro zNotWeight
  simpa [distanceLowerBoundForallStabF, xLowerBoundByGeometryF,
    zLowerBoundByGeometryF, ctx] using SFormula.Deriv.andIntro xLower zLower

def distanceLowerBoundFamilyDeriv
    (D : OddSurfaceDistance) (O : SurfaceCutCommuteFamilyDeriv D) :
    ForallStabFamilyDeriv code.body (bridgeProofFuel D) (distanceLowerBoundForallStabF D) :=
  .intro <|
    FamilyDeriv.cut4 (distanceLowerBoundBodyFromFamilyLemmasDeriv D)
      (xParityPropagationRowsFamilyDeriv D O)
      (FamilyDeriv.core (xRowsWeightLowerByCountingDeriv D))
      (zParityPropagationColsFamilyDeriv D O)
      (FamilyDeriv.core (zColsWeightLowerByCountingDeriv D))

def xRowsWeightLowerByCountingChecked (D : OddSurfaceDistance) : Bool :=
  (xRowsWeightLowerByCountingDeriv D).check

def zColsWeightLowerByCountingChecked (D : OddSurfaceDistance) : Bool :=
  (zColsWeightLowerByCountingDeriv D).check

def xRowsOccupiedApplyBody (D : OddSurfaceDistance) : SFormula 1 :=
  .applyNat SFormula.boundNat
    ((xRowOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)

def zColsOccupiedApplyBody (D : OddSurfaceDistance) : SFormula 1 :=
  .applyNat SFormula.boundNat
    ((zColOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)

def xRowsOccupiedAllRowsApplyF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (xRowsOccupiedApplyBody D)

def zColsOccupiedAllColsApplyF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.n D.distance) (zColsOccupiedApplyBody D)

def xRowsOccupiedAllRowsApplyDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (.imp (xRowsOccupiedF D) (xRowsOccupiedAllRowsApplyF D)) :=
  .impIntro <|
    .allNatLtIntroBounded (SC.n D.distance) (xRowsOccupiedApplyBody D) <|
      .allNatLtElim (SC.n (arity := 1) D.distance)
        ((xRowOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)
        SFormula.boundNat
        (.hyp (by
          simp [SFormula.boundNatLt, SFormula.weaken, SFormula.lift, STerm.lift, Term.lift,
            SC.n, xRowsOccupiedF]))
        .assumption

def zColsOccupiedAllColsApplyDeriv (D : OddSurfaceDistance) :
    SFormula.Deriv [] (.imp (zColsOccupiedF D) (zColsOccupiedAllColsApplyF D)) :=
  .impIntro <|
    .allNatLtIntroBounded (SC.n D.distance) (zColsOccupiedApplyBody D) <|
      .allNatLtElim (SC.n (arity := 1) D.distance)
        ((zColOccupiedAtF D.distance SC.bound.weaken rowVar1).lift 1)
        SFormula.boundNat
        (.hyp (by
          simp [SFormula.boundNatLt, SFormula.weaken, SFormula.lift, STerm.lift, Term.lift,
            SC.n, zColsOccupiedF]))
        .assumption

def xRowsOccupiedAllRowsApplyChecked (D : OddSurfaceDistance) : Bool :=
  (xRowsOccupiedAllRowsApplyDeriv D).check

def zColsOccupiedAllColsApplyChecked (D : OddSurfaceDistance) : Bool :=
  (zColsOccupiedAllColsApplyDeriv D).check

end OpenStab

/-! ## Geometric shell predicates for the `d -> d+2` step -/

/-- Rows whose local definition in `recursiveEntry` uses an old `recCall`.
These are the carried interior plaquettes and promoted old boundary checks.
-/
def carriedRowB {arity : Nat} (dist rowIdx : Term arity .nat) : Term arity .bool :=
  let dm1 := .sub dist (.natLit 1)
  let bulkCount := .mul dm1 dm1
  let r := .div rowIdx dm1
  let c := .mod rowIdx dm1
  let innerD := .sub dist (.natLit 2)
  let innerDm1 := .sub innerD (.natLit 1)
  let innerHalf := .div innerDm1 (.natLit 2)
  let lastCell := .sub dm1 (.natLit 1)
  let interiorCell :=
    band4 (le (.natLit 1) r) (.ltNat r lastCell) (le (.natLit 1) c) (.ltNat c lastCell)
  let topB := .div (.sub c (.natLit 1)) (.natLit 2)
  let topCell :=
    band3 (.eqNat r (.natLit 0)) (.eqNat c (.add (.mul (.natLit 2) topB) (.natLit 1)))
      (.ltNat topB innerHalf)
  let rightB := .div (.sub r (.natLit 1)) (.natLit 2)
  let rightCell :=
    band3 (.eqNat c lastCell) (.eqNat r (.add (.mul (.natLit 2) rightB) (.natLit 1)))
      (.ltNat rightB innerHalf)
  let leftB := .div (.sub r (.natLit 2)) (.natLit 2)
  let leftCell :=
    band3 (.eqNat c (.natLit 0)) (.eqNat r (.add (.mul (.natLit 2) leftB) (.natLit 2)))
      (.ltNat leftB innerHalf)
  let bottomB := .div (.sub c (.natLit 2)) (.natLit 2)
  let bottomCell :=
    band3 (.eqNat r lastCell) (.eqNat c (.add (.mul (.natLit 2) bottomB) (.natLit 2)))
      (.ltNat bottomB innerHalf)
  .and (.ltNat rowIdx bulkCount)
    (bor3 interiorCell topCell (.or rightCell (.or leftCell bottomCell)))

/-- Rows generated locally by the newly exposed shell. -/
def shellRowB {arity : Nat} (dist rowIdx : Term arity .nat) : Term arity .bool :=
  .not (carriedRowB dist rowIdx)

def rowCommutesAtF (dist : Nat) (i j : Term 2 .nat) : Formula 2 :=
  let nT : Term 2 .nat := .natLit (nQubits dist)
  let dT : Term 2 .nat := .natLit dist
  .commutesUpTo nT (Formula.codeRow dT i) (Formula.codeRow dT j)

def pairCommutesWhenF (dist : Nat) (antecedent : Formula 2) : Formula 0 :=
  .allNatLt (.natLit (numStab dist)) <|
    .allNatLt (Term.natLit (numStab dist)).weaken <|
      .imp antecedent (rowCommutesAtF dist leftRowVar2 rightRowVar2)

def carriedPairCommuteF (dist : Nat) : Formula 0 :=
  let dT : Term 2 .nat := .natLit dist
  pairCommutesWhenF dist <|
    .and
      (boolHoldsF (carriedRowB dT leftRowVar2))
      (boolHoldsF (carriedRowB dT rightRowVar2))

def carriedShellPairCommuteF (dist : Nat) : Formula 0 :=
  let dT : Term 2 .nat := .natLit dist
  pairCommutesWhenF dist <|
    .or
      (.and
        (boolHoldsF (carriedRowB dT leftRowVar2))
        (boolHoldsF (shellRowB dT rightRowVar2)))
      (.and
        (boolHoldsF (shellRowB dT leftRowVar2))
        (boolHoldsF (carriedRowB dT rightRowVar2)))

def shellShellPairCommuteF (dist : Nat) : Formula 0 :=
  let dT : Term 2 .nat := .natLit dist
  pairCommutesWhenF dist <|
    .and
      (boolHoldsF (shellRowB dT leftRowVar2))
      (boolHoldsF (shellRowB dT rightRowVar2))

def carriedPairCommuteStepF (m : Nat) : Formula 0 :=
  .imp (rowsCommuteF (oddDistance m)) (carriedPairCommuteF (oddDistance (m + 1)))

def commuteFromCarriedShellF (m : Nat) : Formula 0 :=
  let next := oddDistance (m + 1)
  .imp
    (.and (carriedPairCommuteF next)
      (.and (carriedShellPairCommuteF next) (shellShellPairCommuteF next)))
    (rowsCommuteF next)

def rowNormalizesWhenF (dist : Nat) (L : Term 0 .stab)
    (cond : Term 1 .nat -> Term 1 .bool) : Formula 0 :=
  .allNatLt (.natLit (numStab dist)) <|
    let nT : Term 1 .nat := .natLit (nQubits dist)
    let dT : Term 1 .nat := .natLit dist
    .imp (boolHoldsF (cond rowVar1))
      (.commutesUpTo nT (Formula.codeRow dT rowVar1) L.weaken)

def logicalRowsWhenF (dist : Nat) (cond : Term 1 .nat -> Term 1 .bool) :
    Formula 0 :=
  .and
    (rowNormalizesWhenF dist (logicalX dist) cond)
    (rowNormalizesWhenF dist (logicalZ dist) cond)

def logicalAnticommF (dist : Nat) : Formula 0 :=
  Formula.anticommutesUpTo (.natLit (nQubits dist)) (logicalX dist) (logicalZ dist)

def carriedLogicalRowsStepF (m : Nat) : Formula 0 :=
  let next := oddDistance (m + 1)
  .imp (logicalPairF (oddDistance m))
    (logicalRowsWhenF next (fun row => carriedRowB (.natLit next) row))

def shellLogicalRowsF (m : Nat) : Formula 0 :=
  let next := oddDistance (m + 1)
  logicalRowsWhenF next (fun row => shellRowB (.natLit next) row)

def logicalPairFromCarriedShellF (m : Nat) : Formula 0 :=
  let next := oddDistance (m + 1)
  .imp
    (.and
      (logicalRowsWhenF next (fun row => carriedRowB (.natLit next) row))
      (.and (shellLogicalRowsF m) (logicalAnticommF next)))
    (logicalPairF next)

def logicalXWeightStepF (m : Nat) : Formula 0 :=
  .imp (weightExactF (oddDistance m) (logicalX (oddDistance m)))
    (weightExactF (oddDistance (m + 1)) (logicalX (oddDistance (m + 1))))

def logicalZWeightStepF (m : Nat) : Formula 0 :=
  .imp (weightExactF (oddDistance m) (logicalZ (oddDistance m)))
    (weightExactF (oddDistance (m + 1)) (logicalZ (oddDistance (m + 1))))

def logicalWeightsFromPartsF (m : Nat) : Formula 0 :=
  .imp
    (.and
      (weightExactF (oddDistance (m + 1)) (logicalX (oddDistance (m + 1))))
      (weightExactF (oddDistance (m + 1)) (logicalZ (oddDistance (m + 1)))))
    (logicalWeightsF (oddDistance (m + 1)))

/-! ## Checked derivations -/

private def derivationOf? (dist : Nat) (A : Formula 0) : Option (Formula.Deriv A true) :=
  Formula.deriveTrue? code.body (dist + 2) Env.empty A

private def derivationChecked (dist : Nat) (A : Formula 0) : Bool :=
  match derivationOf? dist A with
  | some D => D.check code.body (dist + 2) Env.empty
  | none => false

private def rowsCommuteRawChecked (dist : Nat) : Bool :=
  derivationChecked dist (rowsCommuteF dist)

private def logicalPairRawChecked (dist : Nat) : Bool :=
  derivationChecked dist (logicalPairF dist)

private def logicalWeightsRawChecked (dist : Nat) : Bool :=
  derivationChecked dist (logicalWeightsF dist)

private def surfaceCodeLevelRawChecked (dist : Nat) : Bool :=
  derivationChecked dist (surfaceCodeLevelF dist)

def rowsCommuteChecked (D : OddSurfaceDistance) : Bool :=
  derivationChecked D.distance (rowsCommuteOddF D)

def logicalPairChecked (D : OddSurfaceDistance) : Bool :=
  derivationChecked D.distance (logicalPairOddF D)

def logicalWeightsChecked (D : OddSurfaceDistance) : Bool :=
  derivationChecked D.distance (logicalWeightsOddF D)

def surfaceCodeLevelChecked (D : OddSurfaceDistance) : Bool :=
  derivationChecked D.distance (surfaceCodeLevelOddF D)

/-! ## Odd-distance induction package

The motive is indexed by `m`, with physical distance `2*m + 3`.  The step is
split into carried-row, shell-row, logical-row, and logical-weight obligations
under the `d -> d+2` Surface growth.
-/

def oddMotiveF (m : Nat) : Formula 0 :=
  surfaceCodeLevelOddF { index := m }

def commuteStepF (m : Nat) : Formula 0 :=
  .imp (rowsCommuteF (oddDistance m)) (rowsCommuteF (oddDistance (m + 1)))

def logicalPairStepF (m : Nat) : Formula 0 :=
  .imp (logicalPairF (oddDistance m)) (logicalPairF (oddDistance (m + 1)))

def logicalWeightsStepF (m : Nat) : Formula 0 :=
  .imp (logicalWeightsF (oddDistance m)) (logicalWeightsF (oddDistance (m + 1)))

structure SurfaceOddStepDerivation (m : Nat) where
  carriedCommute : Formula.Deriv (carriedPairCommuteStepF m) true
  carriedShellCommute : Formula.Deriv (carriedShellPairCommuteF (oddDistance (m + 1))) true
  shellShellCommute : Formula.Deriv (shellShellPairCommuteF (oddDistance (m + 1))) true
  commuteAssemble : Formula.Deriv (commuteFromCarriedShellF m) true
  carriedLogical : Formula.Deriv (carriedLogicalRowsStepF m) true
  shellLogical : Formula.Deriv (shellLogicalRowsF m) true
  logicalAnticomm : Formula.Deriv (logicalAnticommF (oddDistance (m + 1))) true
  logicalAssemble : Formula.Deriv (logicalPairFromCarriedShellF m) true
  xWeight : Formula.Deriv (logicalXWeightStepF m) true
  zWeight : Formula.Deriv (logicalZWeightStepF m) true
  weightsAssemble : Formula.Deriv (logicalWeightsFromPartsF m) true

namespace SurfaceOddStepDerivation

def toMotiveDeriv {m : Nat} (S : SurfaceOddStepDerivation m)
    (prev : Formula.Deriv (oddMotiveF m) true) :
    Formula.Deriv (oddMotiveF (m + 1)) true :=
  let prevCommute : Formula.Deriv (rowsCommuteF (oddDistance m)) true :=
    .andElimLeft prev
  let prevRest :
      Formula.Deriv (.and (logicalPairF (oddDistance m)) (logicalWeightsF (oddDistance m)))
        true :=
    .andElimRight prev
  let prevLogical : Formula.Deriv (logicalPairF (oddDistance m)) true :=
    .andElimLeft prevRest
  let prevWeights : Formula.Deriv (logicalWeightsF (oddDistance m)) true :=
    .andElimRight prevRest
  let carriedCommute := Formula.Deriv.mp S.carriedCommute prevCommute
  let nextCommuteAntecedent :
      Formula.Deriv
        (.and (carriedPairCommuteF (oddDistance (m + 1)))
          (.and (carriedShellPairCommuteF (oddDistance (m + 1)))
            (shellShellPairCommuteF (oddDistance (m + 1))))) true :=
    .andTrue carriedCommute (.andTrue S.carriedShellCommute S.shellShellCommute)
  let nextCommute := Formula.Deriv.mp S.commuteAssemble nextCommuteAntecedent
  let carriedLogical := Formula.Deriv.mp S.carriedLogical prevLogical
  let nextLogicalAntecedent :
      Formula.Deriv
        (.and
          (logicalRowsWhenF (oddDistance (m + 1))
            (fun row => carriedRowB (.natLit (oddDistance (m + 1))) row))
          (.and (shellLogicalRowsF m) (logicalAnticommF (oddDistance (m + 1)))))
        true :=
    .andTrue carriedLogical (.andTrue S.shellLogical S.logicalAnticomm)
  let nextLogical := Formula.Deriv.mp S.logicalAssemble nextLogicalAntecedent
  let prevXWeight :
      Formula.Deriv (weightExactF (oddDistance m) (logicalX (oddDistance m))) true :=
    .andElimLeft prevWeights
  let prevZWeight :
      Formula.Deriv (weightExactF (oddDistance m) (logicalZ (oddDistance m))) true :=
    .andElimRight prevWeights
  let nextXWeight := Formula.Deriv.mp S.xWeight prevXWeight
  let nextZWeight := Formula.Deriv.mp S.zWeight prevZWeight
  let nextWeightsAntecedent :
      Formula.Deriv
        (.and
          (weightExactF (oddDistance (m + 1)) (logicalX (oddDistance (m + 1))))
          (weightExactF (oddDistance (m + 1)) (logicalZ (oddDistance (m + 1)))))
        true :=
    .andTrue nextXWeight nextZWeight
  let nextWeights := Formula.Deriv.mp S.weightsAssemble nextWeightsAntecedent
  .andTrue nextCommute (.andTrue nextLogical nextWeights)

def check {m : Nat} (S : SurfaceOddStepDerivation m) : Bool :=
  let dist := oddDistance (m + 1)
  S.carriedCommute.check code.body (dist + 2) Env.empty &&
    S.carriedShellCommute.check code.body (dist + 2) Env.empty &&
    S.shellShellCommute.check code.body (dist + 2) Env.empty &&
    S.commuteAssemble.check code.body (dist + 2) Env.empty &&
    S.carriedLogical.check code.body (dist + 2) Env.empty &&
    S.shellLogical.check code.body (dist + 2) Env.empty &&
    S.logicalAnticomm.check code.body (dist + 2) Env.empty &&
    S.logicalAssemble.check code.body (dist + 2) Env.empty &&
    S.xWeight.check code.body (dist + 2) Env.empty &&
    S.zWeight.check code.body (dist + 2) Env.empty &&
    S.weightsAssemble.check code.body (dist + 2) Env.empty

def size {m : Nat} (S : SurfaceOddStepDerivation m) : Nat :=
  S.carriedCommute.size + S.carriedShellCommute.size + S.shellShellCommute.size +
    S.commuteAssemble.size + S.carriedLogical.size + S.shellLogical.size +
    S.logicalAnticomm.size + S.logicalAssemble.size + S.xWeight.size + S.zWeight.size +
    S.weightsAssemble.size

end SurfaceOddStepDerivation

def oddStepDerivation? (m : Nat) : Option (SurfaceOddStepDerivation m) := do
  let dist := oddDistance (m + 1)
  let carriedCommute <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (carriedPairCommuteStepF m)
  let carriedShellCommute <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (carriedShellPairCommuteF dist)
  let shellShellCommute <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (shellShellPairCommuteF dist)
  let commuteAssemble <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (commuteFromCarriedShellF m)
  let carriedLogical <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (carriedLogicalRowsStepF m)
  let shellLogical <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (shellLogicalRowsF m)
  let logicalAnticomm <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (logicalAnticommF dist)
  let logicalAssemble <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (logicalPairFromCarriedShellF m)
  let xWeight <- Formula.deriveTrue? code.body (dist + 2) Env.empty (logicalXWeightStepF m)
  let zWeight <- Formula.deriveTrue? code.body (dist + 2) Env.empty (logicalZWeightStepF m)
  let weightsAssemble <-
    Formula.deriveTrue? code.body (dist + 2) Env.empty (logicalWeightsFromPartsF m)
  some {
    carriedCommute := carriedCommute
    carriedShellCommute := carriedShellCommute
    shellShellCommute := shellShellCommute
    commuteAssemble := commuteAssemble
    carriedLogical := carriedLogical
    shellLogical := shellLogical
    logicalAnticomm := logicalAnticomm
    logicalAssemble := logicalAssemble
    xWeight := xWeight
    zWeight := zWeight
    weightsAssemble := weightsAssemble
  }

def oddStepChecked (m : Nat) : Bool :=
  match oddStepDerivation? m with
  | some S => S.check
  | none => false

/-! ## Constant-size odd-distance proof schema -/

inductive SurfaceOddStepSchema where
  | shellGrowth

namespace SurfaceOddStepSchema

def size : SurfaceOddStepSchema -> Nat
  | .shellGrowth => 1

def instantiate? (S : SurfaceOddStepSchema) (m : Nat) :
    Option (SurfaceOddStepDerivation m) :=
  match S with
  | .shellGrowth => oddStepDerivation? m

def checkAt (S : SurfaceOddStepSchema) (m : Nat) : Bool :=
  match S.instantiate? m with
  | some D => D.check
  | none => false

end SurfaceOddStepSchema

structure SurfaceAllOddDerivation where
  base : Formula.Deriv (oddMotiveF 0) true
  stepSchema : SurfaceOddStepSchema

namespace SurfaceAllOddDerivation

def size (D : SurfaceAllOddDerivation) : Nat :=
  D.base.size + D.stepSchema.size

def induction (D : SurfaceAllOddDerivation) :
    Formula.NatZeroInductionDerivation oddMotiveF where
  base := D.base
  step := fun n prev => do
    let S <- D.stepSchema.instantiate? n
    some (S.toMotiveDeriv prev)

def instantiate? (D : SurfaceAllOddDerivation) (m : Nat) :
    Option (Formula.Deriv (oddMotiveF m) true) :=
  D.induction.instantiate? m

def checkAt (D : SurfaceAllOddDerivation) (m : Nat) : Bool :=
  D.induction.checkAt code.body (oddDistance m + 2) m

def instantiatedSize? (D : SurfaceAllOddDerivation) (m : Nat) : Option Nat :=
  D.induction.instantiatedSize? m

end SurfaceAllOddDerivation

def surfaceAllOddDerivation? : Option SurfaceAllOddDerivation := do
  let base <- derivationOf? 3 (oddMotiveF 0)
  some { base := base, stepSchema := .shellGrowth }

def surfaceAllOddCheckedAtIndex (m : Nat) : Bool :=
  match surfaceAllOddDerivation? with
  | some D => D.checkAt m
  | none => false

def surfaceAllOddSchemaSize? : Option Nat :=
  match surfaceAllOddDerivation? with
  | some D => some D.size
  | none => none

structure SurfaceOddCodeTheorem (D : OddSurfaceDistance) where
  stabilizersCommute : Formula.Deriv (rowsCommuteOddF D) true
  logicalXNormalizes : Formula.Deriv (logicalXNormalizesOddF D) true
  logicalZNormalizes : Formula.Deriv (logicalZNormalizesOddF D) true
  logicalXAnticommutesZ : Formula.Deriv (logicalAnticommutesOddF D) true
  logicalXWeightExact : Formula.Deriv (logicalXWeightExactOddF D) true
  logicalZWeightExact : Formula.Deriv (logicalZWeightExactOddF D) true

namespace SurfaceOddCodeTheorem

def check {D : OddSurfaceDistance} (T : SurfaceOddCodeTheorem D) : Bool :=
  let fuel := D.distance + 2
  T.stabilizersCommute.check code.body fuel Env.empty &&
    T.logicalXNormalizes.check code.body fuel Env.empty &&
    T.logicalZNormalizes.check code.body fuel Env.empty &&
    T.logicalXAnticommutesZ.check code.body fuel Env.empty &&
    T.logicalXWeightExact.check code.body fuel Env.empty &&
    T.logicalZWeightExact.check code.body fuel Env.empty

def size {D : OddSurfaceDistance} (T : SurfaceOddCodeTheorem D) : Nat :=
  T.stabilizersCommute.size + T.logicalXNormalizes.size + T.logicalZNormalizes.size +
    T.logicalXAnticommutesZ.size + T.logicalXWeightExact.size + T.logicalZWeightExact.size

end SurfaceOddCodeTheorem

def surfaceCodeLevelDerivationAt? (D : OddSurfaceDistance) :
    Option (Formula.Deriv (surfaceCodeLevelOddF D) true) := do
  let allOdd <- surfaceAllOddDerivation?
  allOdd.instantiate? D.index

def surfaceOddCodeTheoremAt? (D : OddSurfaceDistance) :
    Option (SurfaceOddCodeTheorem D) := do
  let H <- surfaceCodeLevelDerivationAt? D
  let commute : Formula.Deriv (rowsCommuteOddF D) true := .andElimLeft H
  let rest :
      Formula.Deriv (.and (logicalPairOddF D) (logicalWeightsOddF D)) true :=
    .andElimRight H
  let logicalPair : Formula.Deriv (logicalPairOddF D) true :=
    .andElimLeft rest
  let logicalWeights : Formula.Deriv (logicalWeightsOddF D) true :=
    .andElimRight rest
  let xNorm : Formula.Deriv (logicalXNormalizesOddF D) true :=
    .andElimLeft logicalPair
  let pairRest :
      Formula.Deriv (.and (logicalZNormalizesOddF D) (logicalAnticommutesOddF D)) true :=
    .andElimRight logicalPair
  let zNorm : Formula.Deriv (logicalZNormalizesOddF D) true :=
    .andElimLeft pairRest
  let anticomm : Formula.Deriv (logicalAnticommutesOddF D) true :=
    .andElimRight pairRest
  let xWeight : Formula.Deriv (logicalXWeightExactOddF D) true :=
    .andElimLeft logicalWeights
  let zWeight : Formula.Deriv (logicalZWeightExactOddF D) true :=
    .andElimRight logicalWeights
  some {
    stabilizersCommute := commute
    logicalXNormalizes := xNorm
    logicalZNormalizes := zNorm
    logicalXAnticommutesZ := anticomm
    logicalXWeightExact := xWeight
    logicalZWeightExact := zWeight
  }

def surfaceOddCodeTheoremCheckedAt (D : OddSurfaceDistance) : Bool :=
  match surfaceOddCodeTheoremAt? D with
  | some T => T.check
  | none => false

def surfaceOddCodeTheoremSizeAt? (D : OddSurfaceDistance) : Option Nat :=
  match surfaceOddCodeTheoremAt? D with
  | some T => some T.size
  | none => none

/-! ## Surface code-distance theorem object

This is the first all-odd theorem boundary for code distance.  The code-level
fields are already generated by the recursive Surface AST and odd-distance
induction.  The lower-bound field is the open stabilizer-binder derivation:
it ranges over every Pauli string/stabilizer value of width `d*d`.
-/

structure SurfaceCodeDistanceTheorem (D : OddSurfaceDistance) where
  codeLevel : SurfaceOddCodeTheorem D
  lowerBound : StabBinder.ForallStabDeriv (OpenStab.distanceLowerBoundForallStabF D)

namespace SurfaceCodeDistanceTheorem

def check {D : OddSurfaceDistance} (T : SurfaceCodeDistanceTheorem D) : Bool :=
  T.codeLevel.check && T.lowerBound.check

def size {D : OddSurfaceDistance} (T : SurfaceCodeDistanceTheorem D) : Nat :=
  T.codeLevel.size + T.lowerBound.size

end SurfaceCodeDistanceTheorem

def surfaceCodeDistanceFromLowerLemmas?
    (D : OddSurfaceDistance) (G : OpenStab.DistanceLowerBoundLemmaDeriv D) :
    Option (SurfaceCodeDistanceTheorem D) := do
  let C <- surfaceOddCodeTheoremAt? D
  some { codeLevel := C, lowerBound := G.toForallStabDeriv }

/-- Canonical code-distance theorem wrapper using the code-family-indexed
    stabilizer-binder derivation.  The executable family leaves are bound-free
    Surface-generated equalities/range/telescoping facts checked against
    `code.body`; the open propagation, counting, and final lower-bound steps
    are symbolic `SFormula` derivations. -/
structure SurfaceCodeDistanceFamilyTheorem (D : OddSurfaceDistance) where
  codeLevel : SurfaceOddCodeTheorem D
  lowerBound :
    StabBinder.ForallStabFamilyDeriv code.body (OpenStab.bridgeProofFuel D)
      (OpenStab.distanceLowerBoundForallStabF D)

namespace SurfaceCodeDistanceFamilyTheorem

def check {D : OddSurfaceDistance} (T : SurfaceCodeDistanceFamilyTheorem D) : Bool :=
  T.codeLevel.check && StabBinder.ForallStabFamilyDeriv.check T.lowerBound

def size {D : OddSurfaceDistance} (T : SurfaceCodeDistanceFamilyTheorem D) : Nat :=
  T.codeLevel.size + StabBinder.ForallStabFamilyDeriv.size T.lowerBound

end SurfaceCodeDistanceFamilyTheorem

def surfaceCodeDistanceFamilyTheorem?
    (D : OddSurfaceDistance) (O : OpenStab.SurfaceCutCommuteFamilyDeriv D) :
    Option (SurfaceCodeDistanceFamilyTheorem D) := do
  let C <- surfaceOddCodeTheoremAt? D
  some { codeLevel := C, lowerBound := OpenStab.distanceLowerBoundFamilyDeriv D O }

def surfaceCodeDistanceFamilyTheoremFromGenericCuts?
    (D : OddSurfaceDistance) : Option (SurfaceCodeDistanceFamilyTheorem D) :=
  surfaceCodeDistanceFamilyTheorem? D (OpenStab.surfaceCutCommuteFamilyDeriv D)

def surfaceCodeDistanceFamilyCheckedAt
    (D : OddSurfaceDistance) (O : OpenStab.SurfaceCutCommuteFamilyDeriv D) : Bool :=
  match surfaceCodeDistanceFamilyTheorem? D O with
  | some T => T.check
  | none => false

def surfaceCodeDistanceFamilyCheckedAtGenericCuts
    (D : OddSurfaceDistance) : Bool :=
  match surfaceCodeDistanceFamilyTheoremFromGenericCuts? D with
  | some T => T.check
  | none => false

structure SurfaceGeometricLowerBoundDerivation (D : OddSurfaceDistance)
    (E : Term 0 .stab) where
  xParityPropagation : Formula.Deriv (xParityPropagationRowsF D E) true
  xRowsWeightLower : Formula.Deriv (xRowsOccupiedWeightLowerF D E) true
  xLowerBound : Formula.Deriv (xLowerBoundByGeometryF D E) true
  zParityPropagation : Formula.Deriv (zParityPropagationColsF D E) true
  zColsWeightLower : Formula.Deriv (zColsOccupiedWeightLowerF D E) true
  zLowerBound : Formula.Deriv (zLowerBoundByGeometryF D E) true

namespace SurfaceGeometricLowerBoundDerivation

def check {D : OddSurfaceDistance} {E : Term 0 .stab}
    (G : SurfaceGeometricLowerBoundDerivation D E) : Bool :=
  let fuel := D.distance + 2
  G.xParityPropagation.check code.body fuel Env.empty &&
    G.xRowsWeightLower.check code.body fuel Env.empty &&
    G.xLowerBound.check code.body fuel Env.empty &&
    G.zParityPropagation.check code.body fuel Env.empty &&
    G.zColsWeightLower.check code.body fuel Env.empty &&
    G.zLowerBound.check code.body fuel Env.empty

def size {D : OddSurfaceDistance} {E : Term 0 .stab}
    (G : SurfaceGeometricLowerBoundDerivation D E) : Nat :=
  G.xParityPropagation.size + G.xRowsWeightLower.size + G.xLowerBound.size +
    G.zParityPropagation.size + G.zColsWeightLower.size + G.zLowerBound.size

end SurfaceGeometricLowerBoundDerivation

def surfaceGeometricLowerBoundAt? (D : OddSurfaceDistance) (E : Term 0 .stab) :
    Option (SurfaceGeometricLowerBoundDerivation D E) := do
  let fuel := D.distance + 2
  let xParityPropagation <-
    Formula.deriveTrue? code.body fuel Env.empty (xParityPropagationRowsF D E)
  let xRowsWeightLower <-
    Formula.deriveTrue? code.body fuel Env.empty (xRowsOccupiedWeightLowerF D E)
  let xLowerBound <-
    Formula.deriveTrue? code.body fuel Env.empty (xLowerBoundByGeometryF D E)
  let zParityPropagation <-
    Formula.deriveTrue? code.body fuel Env.empty (zParityPropagationColsF D E)
  let zColsWeightLower <-
    Formula.deriveTrue? code.body fuel Env.empty (zColsOccupiedWeightLowerF D E)
  let zLowerBound <-
    Formula.deriveTrue? code.body fuel Env.empty (zLowerBoundByGeometryF D E)
  some {
    xParityPropagation := xParityPropagation
    xRowsWeightLower := xRowsWeightLower
    xLowerBound := xLowerBound
    zParityPropagation := zParityPropagation
    zColsWeightLower := zColsWeightLower
    zLowerBound := zLowerBound
  }

def surfaceGeometricLowerBoundCheckedAt
    (D : OddSurfaceDistance) (E : Term 0 .stab) : Bool :=
  match surfaceGeometricLowerBoundAt? D E with
  | some G => G.check
  | none => false

def surfaceGeometricLowerBoundSizeAt?
    (D : OddSurfaceDistance) (E : Term 0 .stab) : Option Nat :=
  match surfaceGeometricLowerBoundAt? D E with
  | some G => some G.size
  | none => none

def oddInductionDerivation? :
    Option (Formula.NatZeroInductionDerivation oddMotiveF) := do
  let base <- derivationOf? 3 (oddMotiveF 0)
  some {
    base := base
    step := fun n prev => do
      let S <- oddStepDerivation? n
      some (S.toMotiveDeriv prev)
  }

def oddInductiveAtIndex? (m : Nat) :
    Option (Formula.Deriv (oddMotiveF m) true) := do
  let D <- oddInductionDerivation?
  D.instantiate? m

def oddInductionCheckedAtIndex (m : Nat) : Bool :=
  match oddInductiveAtIndex? m with
  | some D => D.check code.body (oddDistance m + 2) Env.empty
  | none => false

/-! ## Generated views and guards -/

def pauliChar : Pauli -> String
  | .I => "I"
  | .X => "X"
  | .Y => "Y"
  | .Z => "Z"

private def rowStringRaw (dist row : Nat) : String :=
  let entries := (List.range (nQubits dist)).map fun slot =>
    code.evalEntry? (dist + 2) dist row slot
  entries.foldr
    (fun p acc =>
      (match p with
      | some pauli => pauliChar pauli
      | none => "?") ++ acc)
    ""

private def generatedRowsRaw (dist : Nat) : List String :=
  (List.range (numStab dist)).map fun row => rowStringRaw dist row

def generatedRows (D : OddSurfaceDistance) : List String :=
  generatedRowsRaw D.distance

private def logicalStringRaw (dist : Nat) (L : Term 0 .stab) : String :=
  let stab? := Term.eval code.body (dist + 2) L Env.empty
  let entries := (List.range (nQubits dist)).map fun slot => do
    let stab <- stab?
    stab slot
  entries.foldr
    (fun p acc =>
      (match p with
      | some pauli => pauliChar pauli
      | none => "?") ++ acc)
    ""

def logicalString (D : OddSurfaceDistance) (L : Term 0 .stab) : String :=
  logicalStringRaw D.distance L

/-- info: ["ZZIZZIIII", "IXXIXXIII", "IIIXXIXXI", "IIIIZZIZZ", "XXIIIIIII", "IIZIIZIII", "IIIZIIZII", "IIIIIIIXX"] -/
#guard_msgs in
#eval generatedRows .d3

/-- info: "XIIXIIXII" -/
#guard_msgs in
#eval logicalString .d3 (logicalXOdd .d3)

/-- info: "ZZZIIIIII" -/
#guard_msgs in
#eval logicalString .d3 (logicalZOdd .d3)

/-- info: true -/
#guard_msgs in
#eval rowsCommuteChecked .d3

/-- info: true -/
#guard_msgs in
#eval logicalPairChecked .d3

/-- info: true -/
#guard_msgs in
#eval logicalWeightsChecked .d3

/-- info: true -/
#guard_msgs in
#eval surfaceCodeLevelChecked .d3

/-- info: true -/
#guard_msgs in
#eval rowsCommuteChecked .d5

/-- info: true -/
#guard_msgs in
#eval logicalPairChecked .d5

/-- info: true -/
#guard_msgs in
#eval logicalWeightsChecked .d5

/-- info: true -/
#guard_msgs in
#eval surfaceCodeLevelChecked .d5

/-- info: true -/
#guard_msgs in
#eval oddStepChecked 0

/-- info: true -/
#guard_msgs in
#eval oddInductionCheckedAtIndex 0

/-- info: true -/
#guard_msgs in
#eval oddInductionCheckedAtIndex 1

/-- info: true -/
#guard_msgs in
#eval surfaceOddCodeTheoremCheckedAt .d3

/-- info: true -/
#guard_msgs in
#eval surfaceOddCodeTheoremCheckedAt .d5

/-- info: some 654 -/
#guard_msgs in
#eval surfaceOddCodeTheoremSizeAt? .d3

/-- info: true -/
#guard_msgs in
#eval surfaceGeometricLowerBoundCheckedAt .d3 (logicalXOdd .d3)

/-- info: true -/
#guard_msgs in
#eval surfaceGeometricLowerBoundCheckedAt .d3 (logicalZOdd .d3)

/-- info: true -/
#guard_msgs in
#eval surfaceGeometricLowerBoundCheckedAt .d5 (logicalXOdd .d5)

/-- info: true -/
#guard_msgs in
#eval surfaceGeometricLowerBoundCheckedAt .d5 (logicalZOdd .d5)

/-- info: some 93 -/
#guard_msgs in
#eval surfaceGeometricLowerBoundSizeAt? .d3 (logicalXOdd .d3)

/-- info: true -/
#guard_msgs in
#eval OpenStab.distanceLowerBoundClosedInstanceChecked .d3 (logicalXOdd .d3)

/-- info: true -/
#guard_msgs in
#eval OpenStab.distanceLowerBoundClosedInstanceChecked .d3 (logicalZOdd .d3)

/-- info: true -/
#guard_msgs in
#eval OpenStab.distanceLowerBoundClosedInstanceChecked .d5 (logicalXOdd .d5)

/-- info: true -/
#guard_msgs in
#eval OpenStab.distanceLowerBoundClosedInstanceChecked .d5 (logicalZOdd .d5)

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsOccupiedApplyChecked .d3 (StabBinder.SC.n 0)

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsOccupiedApplyChecked .d3 (StabBinder.SC.n 0)

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsOccupiedApplyChecked .d5 (StabBinder.SC.n 2)

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsOccupiedApplyChecked .d5 (StabBinder.SC.n 2)

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowOccupiedDeMorganChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColOccupiedDeMorganChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowOccupiedDeMorganChecked .d5

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColOccupiedDeMorganChecked .d5

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsOccupiedAllRowsApplyChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsOccupiedAllColsApplyChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsOccupiedAllRowsApplyChecked .d5

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsOccupiedAllColsApplyChecked .d5

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsOccupiedSupportSurjectiveChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsOccupiedSupportSurjectiveChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsOccupiedSupportSurjectiveChecked .d5

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsOccupiedSupportSurjectiveChecked .d5

/-- info: true -/
#guard_msgs in
#eval (OpenStab.xRowsWeightLowerAssumingSupportSurjectiveDeriv .d3).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.zColsWeightLowerAssumingSupportSurjectiveDeriv .d3).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.xRowsWeightLowerAssumingSupportSurjectiveDeriv .d5).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.zColsWeightLowerAssumingSupportSurjectiveDeriv .d5).check

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsWeightLowerByCountingChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsWeightLowerByCountingChecked .d3

/-- info: true -/
#guard_msgs in
#eval OpenStab.xRowsWeightLowerByCountingChecked .d5

/-- info: true -/
#guard_msgs in
#eval OpenStab.zColsWeightLowerByCountingChecked .d5

/-- info: true -/
#guard_msgs in
#eval (OpenStab.rowBridgeProductCommutesDeriv .d3).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.colBridgeProductCommutesDeriv .d3).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.rowBridgeProductCommutesDeriv .d5).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.colBridgeProductCommutesDeriv .d5).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.rowBridgePrefixFactorsCommuteDeriv .d3).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.colBridgePrefixFactorsCommuteDeriv .d3).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.rowBridgePrefixProductCommutesDeriv .d5).check

/-- info: true -/
#guard_msgs in
#eval (OpenStab.colBridgePrefixProductCommutesDeriv .d5).check

/-- info: true -/
#guard_msgs in
#eval OpenStab.rowBridgeGeneratedClosedCheckedAt .d7

/-- info: true -/
#guard_msgs in
#eval OpenStab.colBridgeGeneratedClosedCheckedAt .d7

/-- info: true -/
#guard_msgs in
#eval surfaceCodeDistanceFamilyCheckedAtGenericCuts .d3

/-- info: true -/
#guard_msgs in
#eval surfaceCodeDistanceFamilyCheckedAtGenericCuts .d5

/-- info: some 107 -/
#guard_msgs in
#eval surfaceAllOddSchemaSize?

/-- info: true -/
#guard_msgs in
#eval surfaceAllOddCheckedAtIndex 0

/-- info: true -/
#guard_msgs in
#eval surfaceAllOddCheckedAtIndex 1

#print axioms code
#print axioms rowsCommuteChecked
#print axioms logicalPairChecked
#print axioms logicalWeightsChecked
#print axioms surfaceCodeLevelChecked
#print axioms oddStepChecked
#print axioms surfaceAllOddDerivation?
#print axioms surfaceCodeLevelDerivationAt?
#print axioms surfaceOddCodeTheoremAt?
#print axioms surfaceOddCodeTheoremCheckedAt
#print axioms surfaceGeometricLowerBoundAt?
#print axioms surfaceGeometricLowerBoundCheckedAt
#print axioms OpenStab.distanceLowerBoundForallStabF
#print axioms OpenStab.distanceLowerBoundClosedInstanceChecked
#print axioms OpenStab.DistanceLowerBoundLemmaDeriv.toForallStabDeriv
#print axioms OpenStab.DistanceLowerBoundLemmaDeriv.check
#print axioms OpenStab.xRowsOccupiedApplyDeriv
#print axioms OpenStab.zColsOccupiedApplyDeriv
#print axioms OpenStab.xRowOccupiedDeMorganDeriv
#print axioms OpenStab.zColOccupiedDeMorganDeriv
#print axioms OpenStab.xRowsOccupiedAllRowsApplyDeriv
#print axioms OpenStab.zColsOccupiedAllColsApplyDeriv
#print axioms OpenStab.xRowsOccupiedSupportSurjectiveDeriv
#print axioms OpenStab.zColsOccupiedSupportSurjectiveDeriv
#print axioms OpenStab.rowBridgeProductCommutesDeriv
#print axioms OpenStab.colBridgeProductCommutesDeriv
#print axioms OpenStab.rowBridgePrefixFactorsCommuteDeriv
#print axioms OpenStab.colBridgePrefixFactorsCommuteDeriv
#print axioms OpenStab.rowBridgePrefixProductCommutesDeriv
#print axioms OpenStab.colBridgePrefixProductCommutesDeriv
#print axioms OpenStab.rowBridgeGeneratedClosedCheckedAt_sound
#print axioms OpenStab.colBridgeGeneratedClosedCheckedAt_sound
#print axioms OpenStab.xRowsWeightLowerAssumingSupportSurjectiveDeriv
#print axioms OpenStab.zColsWeightLowerAssumingSupportSurjectiveDeriv
#print axioms OpenStab.xRowsWeightLowerByCountingDeriv
#print axioms OpenStab.zColsWeightLowerByCountingDeriv
#print axioms OpenStab.distanceLowerBoundFromParityDeriv
#print axioms OpenStab.DistanceLowerBoundSupportDeriv.toLemmaDeriv
#print axioms OpenStab.distanceLowerBoundFamilyDeriv
#print axioms SurfaceCodeDistanceTheorem.check
#print axioms surfaceCodeDistanceFromLowerLemmas?
#print axioms SurfaceCodeDistanceFamilyTheorem.check
#print axioms surfaceCodeDistanceFamilyTheorem?
#print axioms surfaceCodeDistanceFamilyTheoremFromGenericCuts?
#print axioms surfaceCodeDistanceFamilyCheckedAt
#print axioms surfaceCodeDistanceFamilyCheckedAtGenericCuts
#print axioms surfaceAllOddCheckedAtIndex
#print axioms surfaceAllOddSchemaSize?
#print axioms oddInductionDerivation?
#print axioms oddInductionCheckedAtIndex

end QHL.CodeLang.Surface
