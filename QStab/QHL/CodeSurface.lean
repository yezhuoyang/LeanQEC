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
  max 1 ((dist - 1) * (dist - 1) + 2 * (dist - 1))

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

def xRowsOccupiedWeightLowerF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (xRowsOccupiedF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

def zColsOccupiedWeightLowerF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (zColsOccupiedF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

def xLowerBoundByGeometryF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (xNontrivialNormalizerF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

def zLowerBoundByGeometryF (D : OddSurfaceDistance) : SFormula 0 :=
  .imp (zNontrivialNormalizerF D)
    (.not (.weightLe (SC.n (nQubits D.distance)) SC.bound (SC.n (D.distance - 1))))

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
#print axioms surfaceAllOddCheckedAtIndex
#print axioms surfaceAllOddSchemaSize?
#print axioms oddInductionDerivation?
#print axioms oddInductionCheckedAtIndex

end QHL.CodeLang.Surface
