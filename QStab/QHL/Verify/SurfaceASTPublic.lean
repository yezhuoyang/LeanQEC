import QStab.QHL.CodeSurface

/-!
# Public verifier view of the recursive Surface AST

`CodeSurface.lean` defines the canonical Surface AST using private shorthands for
the entry variables `q`, `d`, and `k`.  That is fine for the trusted definition,
but verifier-side proofs need a public reducible view so `simp` can execute the
OCaml-style evaluator without referring to private names.

The definitions here are a mirror of the frozen AST using the public
`C.Entry.q`, `C.Entry.d`, and `C.Entry.k` variables.  The `*_eq_public` lemmas
are all `rfl`, so this file cannot silently diverge from `CodeSurface`.
-/

namespace QHL.CodeLang.Surface.Verify.SurfaceASTPublic

open QHL.CodeLang
open QHL.CodeLang.Surface

def q : Term 3 .nat := C.Entry.q
def k : Term 3 .nat := C.Entry.k
def d : Term 3 .nat := C.Entry.d

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

def body : Term 2 .stab :=
  .ite (.ltNat C.Code.d (n5 : Term 2 .nat))
    (.stabLam baseEntry)
    (.stabLam recursiveEntry)

theorem baseEntry_eq_public : Surface.baseEntry = baseEntry := by
  rfl

theorem promotedBoundaryEntry_eq_public
    (oldK : Term 3 .nat) (outer : Term 3 .bool) (kind : Pauli) :
    Surface.promotedBoundaryEntry oldK outer kind = promotedBoundaryEntry oldK outer kind := by
  rfl

theorem recursiveEntry_eq_public : Surface.recursiveEntry = recursiveEntry := by
  rfl

theorem body_eq_public : Surface.body = body := by
  rfl

theorem code_body_eq_public : Surface.code.body = body := by
  rfl

end QHL.CodeLang.Surface.Verify.SurfaceASTPublic
