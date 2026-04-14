import QStab.Simulate

/-! # Rotated surface code instantiation (Phase 1 of NZ distance proof)

Defines the [[d², 1, d]] rotated surface code as a `QECParams` for d=3 and d=4,
matching invariant.tex §3.2 (lines 1229–1431).

## Qubit indexing

The paper numbers data qubits as q_{d(i-1)+j} (1-based), where (i,j) is
(row, column) with rows top-to-bottom. In Lean we use Fin n (0-based), so
paper's q_k corresponds to Fin index k-1, and qubit at row i, column j
(1-based) has Fin index d*(i-1) + (j-1).

## Stabilizer ordering

Stabilizers are listed in the paper's order ŝ₁, ŝ₂, ..., interpreted as
QStab's T_0, T_1, ... (0-indexed). This determines the measurement schedule:
the QStab program measures T_x in coordinate (x, y).
-/

namespace QStab.Examples

open Pauli

/-- Build an ErrorVec of length n from a list of (qubitIndex, Pauli) pairs.
    Unlisted positions default to Pauli.I. -/
def ofList {n : Nat} (ops : List (Nat × Pauli)) : ErrorVec n :=
  fun i => (ops.lookup i.val).getD Pauli.I

/-! ## Distance-3 rotated surface code ([[9, 1, 3]])

3×3 grid, 9 data qubits, 8 stabilizer generators (matches invariant.tex:1288–1291):

```
    q₁  q₂  q₃
    q₄  q₅  q₆
    q₇  q₈  q₉
```

Stabilizers:
  T_0 = ŝ₁ = Z₁Z₂Z₄Z₅     (bulk Z, NW plaquette)
  T_1 = ŝ₂ = X₂X₃X₅X₆     (bulk X, NE plaquette)
  T_2 = ŝ₃ = X₄X₅X₇X₈     (bulk X, SW plaquette)
  T_3 = ŝ₄ = Z₅Z₆Z₈Z₉     (bulk Z, SE plaquette)
  T_4 = ŝ₅ = X₁X₂         (boundary X, top-left)
  T_5 = ŝ₆ = Z₃Z₆         (boundary Z, right-top)
  T_6 = ŝ₇ = Z₄Z₇         (boundary Z, left-bottom)
  T_7 = ŝ₈ = X₈X₉         (boundary X, bottom-right)

Logical operators (invariant.tex:1291):
  X̄ = X₁X₄X₇   (left column)
  Z̄ = Z₁Z₂Z₃   (top row)
-/

namespace SurfaceD3

def s1 : ErrorVec 9 := ofList [(0, .Z), (1, .Z), (3, .Z), (4, .Z)]
def s2 : ErrorVec 9 := ofList [(1, .X), (2, .X), (4, .X), (5, .X)]
def s3 : ErrorVec 9 := ofList [(3, .X), (4, .X), (6, .X), (7, .X)]
def s4 : ErrorVec 9 := ofList [(4, .Z), (5, .Z), (7, .Z), (8, .Z)]
def s5 : ErrorVec 9 := ofList [(0, .X), (1, .X)]
def s6 : ErrorVec 9 := ofList [(2, .Z), (5, .Z)]
def s7 : ErrorVec 9 := ofList [(3, .Z), (6, .Z)]
def s8 : ErrorVec 9 := ofList [(7, .X), (8, .X)]

/-- Stabilizer generators indexed by Fin 8 in paper's order. -/
def stabilizers : Fin 8 → ErrorVec 9
  | ⟨0, _⟩ => s1 | ⟨1, _⟩ => s2 | ⟨2, _⟩ => s3 | ⟨3, _⟩ => s4
  | ⟨4, _⟩ => s5 | ⟨5, _⟩ => s6 | ⟨6, _⟩ => s7 | ⟨7, _⟩ => s8

/-- The [[9, 1, 3]] rotated surface code with R rounds. -/
def params (R : Nat) (hR : 0 < R) : QECParams where
  n := 9
  k := 1
  d := 3
  R := R
  numStab := 8
  stabilizers := stabilizers
  r := 3            -- max hook weight under NZ scheduling (weight-3 of weight-4 stab)
  C_budget := 1     -- ⌊(d-1)/2⌋ for standard distance
  hn := by omega
  hns := by omega
  hR := hR

/-- Default instance for R = 5 (satisfies R ≥ 2d − 1 = 5 for NZ distance theorem). -/
def code : QECParams := params 5 (by omega)

/-- Logical X̄ = X₁X₄X₇ (left column, qubits 0, 3, 6). -/
def logicalX : ErrorVec 9 := ofList [(0, .X), (3, .X), (6, .X)]

/-- Logical Z̄ = Z₁Z₂Z₃ (top row, qubits 0, 1, 2). -/
def logicalZ : ErrorVec 9 := ofList [(0, .Z), (1, .Z), (2, .Z)]

/-- Row i cut operator Ẑ_i = ∏_j Z_(i,j). Used in the topological lower-bound
    argument (invariant.tex:1719). `i` is 1-based. -/
def rowCut (i : Nat) : ErrorVec 9 :=
  ofList [((i-1)*3, .Z), ((i-1)*3 + 1, .Z), ((i-1)*3 + 2, .Z)]

/-- Column j cut operator X̂_j = ∏_i X_(i,j). `j` is 1-based. -/
def colCut (j : Nat) : ErrorVec 9 :=
  ofList [(j-1, .X), (j-1 + 3, .X), (j-1 + 6, .X)]

/-! ### Sanity checks

All `#eval!` outputs are validated against the paper by eye. Run in Lean
infoview to confirm; these are not automated assertions. -/

-- Identity commutes with every stabilizer: all parities are false.
#eval! (List.finRange 8).map fun i =>
  ErrorVec.parity (stabilizers i) (ErrorVec.identity 9)

/-- Single X on qubit 0 (paper's q₁):
    - anticommutes with T_0 = Z₁Z₂Z₄Z₅ (Z on q₀)  → true
    - commutes with T_4 = X₁X₂ (X on q₀)          → false
    - commutes with all others (no overlap)        → false -/
def e_X1 : ErrorVec 9 := ErrorVec.update (ErrorVec.identity 9) ⟨0, by decide⟩ .X

-- Expected: [true, false, false, false, false, false, false, false]
#eval! (List.finRange 8).map fun i => ErrorVec.parity (stabilizers i) e_X1

-- Logical X̄ must commute with every stabilizer (it is in the normalizer).
-- Expected: all false
#eval! (List.finRange 8).map fun i => ErrorVec.parity (stabilizers i) logicalX

-- Logical Z̄ must commute with every stabilizer.
-- Expected: all false
#eval! (List.finRange 8).map fun i => ErrorVec.parity (stabilizers i) logicalZ

/-! ### Row-cut telescoping (preparation for topological lemma, §3.4)

Paper claim (invariant.tex:1721): Ẑ_i ≡ Z̄ (mod S) for every row i.
Verified below for d=3 via:
  row₁ · row₂ = s1 · s6   (both equal Z₁Z₂Z₃Z₄Z₅Z₆)
  row₂ · row₃ = s4 · s7   (both equal Z₄Z₅Z₆Z₇Z₈Z₉)
Hence row₂ = row₁ · (s1 · s6) ∈ row₁ · S, so Ẑ_2 ≡ Ẑ_1 = Z̄ (mod S). -/

/-- Helper: compare two ErrorVecs entrywise. -/
def eqVec (e₁ e₂ : ErrorVec 9) : List Bool :=
  (List.finRange 9).map fun i => decide (e₁ i = e₂ i)

-- Expected: all true
#eval! eqVec (ErrorVec.mul (rowCut 1) (rowCut 2)) (ErrorVec.mul s1 s6)

-- Expected: all true
#eval! eqVec (ErrorVec.mul (rowCut 2) (rowCut 3)) (ErrorVec.mul s4 s7)

-- rowCut 1 = logicalZ by definition (both are Z on qubits 0,1,2).
-- Expected: all true
#eval! eqVec (rowCut 1) logicalZ

end SurfaceD3

/-! ## Distance-4 rotated surface code ([[16, 1, 4]])

4×4 grid, 16 data qubits, 15 stabilizer generators (matches invariant.tex:1407–1431):

```
    q₁   q₂   q₃   q₄
    q₅   q₆   q₇   q₈
    q₉   q₁₀  q₁₁  q₁₂
    q₁₃  q₁₄  q₁₅  q₁₆
```

Stabilizers (paper's order ŝ₁, ..., ŝ₁₅ → T_0, ..., T_14):
  T_0..T_4  = ŝ₁..ŝ₅   (Z-type, weight-4 bulk)
  T_5..T_8  = ŝ₆..ŝ₉   (X-type, weight-4 bulk)
  T_9, T_10 = ŝ₁₀, ŝ₁₁ (Z-type, boundary weight-2, left/right)
  T_11..T_14 = ŝ₁₂..ŝ₁₅ (X-type, boundary weight-2, top/bottom)

Logical operators (invariant.tex:1429):
  X̄ = X₁X₅X₉X₁₃      (left column)
  Z̄ = Z₁Z₂Z₃Z₄       (top row)
-/

namespace SurfaceD4

-- Z-type weight-4 bulk (invariant.tex:1409–1414)
def s1 : ErrorVec 16 := ofList [(0, .Z), (1, .Z), (4, .Z), (5, .Z)]       -- Z₁Z₂Z₅Z₆
def s2 : ErrorVec 16 := ofList [(2, .Z), (3, .Z), (6, .Z), (7, .Z)]       -- Z₃Z₄Z₇Z₈
def s3 : ErrorVec 16 := ofList [(5, .Z), (6, .Z), (9, .Z), (10, .Z)]      -- Z₆Z₇Z₁₀Z₁₁
def s4 : ErrorVec 16 := ofList [(8, .Z), (9, .Z), (12, .Z), (13, .Z)]     -- Z₉Z₁₀Z₁₃Z₁₄
def s5 : ErrorVec 16 := ofList [(10, .Z), (11, .Z), (14, .Z), (15, .Z)]   -- Z₁₁Z₁₂Z₁₅Z₁₆

-- X-type weight-4 bulk (invariant.tex:1415–1419)
def s6 : ErrorVec 16 := ofList [(1, .X), (2, .X), (5, .X), (6, .X)]       -- X₂X₃X₆X₇
def s7 : ErrorVec 16 := ofList [(4, .X), (5, .X), (8, .X), (9, .X)]       -- X₅X₆X₉X₁₀
def s8 : ErrorVec 16 := ofList [(6, .X), (7, .X), (10, .X), (11, .X)]     -- X₇X₈X₁₁X₁₂
def s9 : ErrorVec 16 := ofList [(9, .X), (10, .X), (13, .X), (14, .X)]    -- X₁₀X₁₁X₁₄X₁₅

-- Z-type boundary weight-2 (invariant.tex:1420–1422)
def s10 : ErrorVec 16 := ofList [(4, .Z), (8, .Z)]                         -- Z₅Z₉   (left)
def s11 : ErrorVec 16 := ofList [(7, .Z), (11, .Z)]                        -- Z₈Z₁₂  (right)

-- X-type boundary weight-2 (invariant.tex:1423–1427)
def s12 : ErrorVec 16 := ofList [(0, .X), (1, .X)]                         -- X₁X₂   (top)
def s13 : ErrorVec 16 := ofList [(2, .X), (3, .X)]                         -- X₃X₄   (top)
def s14 : ErrorVec 16 := ofList [(12, .X), (13, .X)]                       -- X₁₃X₁₄ (bottom)
def s15 : ErrorVec 16 := ofList [(14, .X), (15, .X)]                       -- X₁₅X₁₆ (bottom)

/-- Stabilizer generators for d=4 indexed by Fin 15 in paper's order. -/
def stabilizers : Fin 15 → ErrorVec 16
  | ⟨0, _⟩ => s1  | ⟨1, _⟩ => s2  | ⟨2, _⟩ => s3  | ⟨3, _⟩ => s4
  | ⟨4, _⟩ => s5  | ⟨5, _⟩ => s6  | ⟨6, _⟩ => s7  | ⟨7, _⟩ => s8
  | ⟨8, _⟩ => s9  | ⟨9, _⟩ => s10 | ⟨10, _⟩ => s11 | ⟨11, _⟩ => s12
  | ⟨12, _⟩ => s13 | ⟨13, _⟩ => s14 | ⟨14, _⟩ => s15

/-- The [[16, 1, 4]] rotated surface code with R rounds. -/
def params (R : Nat) (hR : 0 < R) : QECParams where
  n := 16
  k := 1
  d := 4
  R := R
  numStab := 15
  stabilizers := stabilizers
  r := 3
  C_budget := 1     -- ⌊(d-1)/2⌋ = 1
  hn := by omega
  hns := by omega
  hR := hR

/-- Default instance for R = 7 (satisfies R ≥ 2d − 1 = 7). -/
def code : QECParams := params 7 (by omega)

/-- Logical X̄ = X₁X₅X₉X₁₃ (left column). -/
def logicalX : ErrorVec 16 := ofList [(0, .X), (4, .X), (8, .X), (12, .X)]

/-- Logical Z̄ = Z₁Z₂Z₃Z₄ (top row). -/
def logicalZ : ErrorVec 16 := ofList [(0, .Z), (1, .Z), (2, .Z), (3, .Z)]

/-- Row i cut operator (1-based row index). -/
def rowCut (i : Nat) : ErrorVec 16 :=
  ofList [((i-1)*4, .Z), ((i-1)*4 + 1, .Z), ((i-1)*4 + 2, .Z), ((i-1)*4 + 3, .Z)]

/-! ### Sanity checks -/

-- Identity commutes with every stabilizer.
#eval! (List.finRange 15).map fun i =>
  ErrorVec.parity (stabilizers i) (ErrorVec.identity 16)

-- Logical X̄ commutes with every stabilizer.
-- Expected: all false
#eval! (List.finRange 15).map fun i =>
  ErrorVec.parity (stabilizers i) logicalX

-- Logical Z̄ commutes with every stabilizer.
-- Expected: all false
#eval! (List.finRange 15).map fun i =>
  ErrorVec.parity (stabilizers i) logicalZ

/-! ### Row-cut telescoping (d=4)

NOTE: [invariant.tex:1436–1440] claims
    row₁·row₂ = s1·s2·s12·s13
    row₃·row₄ = s4·s5·s14·s15
but s12, s13, s14, s15 are *X-type* stabilizers (X₁X₂, X₃X₄, X₁₃X₁₄, X₁₅X₁₆).
Multiplying X-type into a Z-only target produces Y's (ZX = −iY), not Z's.
`#eval!` confirms this is a paper bug.

The correct identities (using Z-type stabilizers only):
  row₁·row₂ = s1·s2               -- fully covered by bulk Z-plaquettes
  row₂·row₃ = s3·s10·s11          -- 1 bulk + 2 boundary Z (paper-correct)
  row₃·row₄ = s4·s5               -- fully covered by bulk Z-plaquettes

Telescoping still works: Ẑ_i ≡ Ẑ_1 = Z̄ (mod S) for every i ∈ [d]. -/

def eqVec (e₁ e₂ : ErrorVec 16) : List Bool :=
  (List.finRange 16).map fun i => decide (e₁ i = e₂ i)

-- Expected: all true
#eval! eqVec
  (ErrorVec.mul (rowCut 1) (rowCut 2))
  (ErrorVec.mul s1 s2)

-- Expected: all true
#eval! eqVec
  (ErrorVec.mul (rowCut 2) (rowCut 3))
  (ErrorVec.mul s3 (ErrorVec.mul s10 s11))

-- Expected: all true
#eval! eqVec
  (ErrorVec.mul (rowCut 3) (rowCut 4))
  (ErrorVec.mul s4 s5)

end SurfaceD4

end QStab.Examples
