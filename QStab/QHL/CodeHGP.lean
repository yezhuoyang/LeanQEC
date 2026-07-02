import QStab.QHL.CodeLang
import QStab.Examples.HGPCode

/-!
# The hypergraph-product family HGP(Rep(d), Rep(d)) as an object-language program

`HGP(H, H)` with `H` the repetition-code parity check (`(d-1) × d`, `H[i,a] = 1` iff
`a ∈ {i, i+1}`), giving the `[[d² + (d-1)², 1, d]]` family — `[[13,1,3]]` at `d = 3`.

Layout (matching `QStab/Examples/HGPCode.lean` at `d = 3`):
* Sector 1 (bit-type): `d × d` qubits, `q < d²`, coordinates `(a, b) = (q/d, q%d)`.
* Sector 2 (check-type): `(d-1) × (d-1)` qubits, `p = q - d²`, `(i', j') = (p/(d-1), p%(d-1))`.

Stabilizers (`numStab = 2·d·(d-1)`), from `H_X = (H⊗I | I⊗Hᵀ)`, `H_Z = (I⊗H | Hᵀ⊗I)`:
* X-check `k < (d-1)·d`, `(i, j) = (k/d, k%d)`:
  sector-1 `X` at `(a, j)` for `a ∈ {i, i+1}` (all in **column `j`** — the hook-alignment
  source); sector-2 `X` at `(i, j')` for `j' ∈ {j-1, j}` (expressed as `j' = j ∨ j'+1 = j`
  to stay subtraction-free).
* Z-check `t = k - (d-1)·d < d·(d-1)`, `(a, j) = (t/(d-1), t%(d-1))`:
  sector-1 `Z` at `(a, b)` for `b ∈ {j, j+1}` (all in **row `a`**); sector-2 `Z` at
  `(i', j)` for `i' ∈ {a-1, a}` (as `i' = a ∨ i'+1 = a`).

No `recCall`: pure branch arithmetic, so evaluation is fuel- and codeBody-irrelevant.
-/

namespace QHL.CodeLang.HGP

open QHL.CodeLang

def qv : Term 3 .nat := .var 0
def kv : Term 3 .nat := .var 1
def dv : Term 3 .nat := .var 2

def dm1 : Term 3 .nat := .sub dv (.natLit 1)
/-- `d²` — the sector boundary. -/
def s2start : Term 3 .nat := .mul dv dv
/-- `(d-1)·d` — the X-check count. -/
def xCount : Term 3 .nat := .mul dm1 dv
/-- Sector-2 offset `p = q - d²`. -/
def pOff : Term 3 .nat := .sub qv s2start
/-- Total qubits `d² + (d-1)²`. -/
def nQ : Term 3 .nat := .add s2start (.mul dm1 dm1)

/-- Sector-1 row/col of `q`. -/
def s1row : Term 3 .nat := .div qv dv
def s1col : Term 3 .nat := .mod qv dv
/-- Sector-2 row/col of `q`. -/
def s2row : Term 3 .nat := .div pOff dm1
def s2col : Term 3 .nat := .mod pOff dm1

/-- X-check coordinates `(i, j) = (k/d, k%d)`. -/
def xI : Term 3 .nat := .div kv dv
def xJ : Term 3 .nat := .mod kv dv
/-- Z-check coordinates `(a, j) = (t/(d-1), t%(d-1))`, `t = k - (d-1)·d`. -/
def zT : Term 3 .nat := .sub kv xCount
def zA : Term 3 .nat := .div zT dm1
def zJ : Term 3 .nat := .mod zT dm1

/-- HGP(Rep(d), Rep(d)) entry: `(d, k, q) ↦ Pauli`. -/
def hgpEntryAST : Term 3 .pauli :=
  .ite (.and (.ltNat kv (.mul (.natLit 2) xCount)) (.ltNat qv nQ))
    (.ite (.ltNat kv xCount)
      -- X-check (i, j)
      (.ite (.ltNat qv s2start)
        (.ite (.and (.eqNat s1col xJ)
                (.or (.eqNat s1row xI) (.eqNat s1row (.add xI (.natLit 1)))))
          (.pauliLit Pauli.X) (.pauliLit Pauli.I))
        (.ite (.and (.eqNat s2row xI)
                (.or (.eqNat s2col xJ) (.eqNat (.add s2col (.natLit 1)) xJ)))
          (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
      -- Z-check (a, j)
      (.ite (.ltNat qv s2start)
        (.ite (.and (.eqNat s1row zA)
                (.or (.eqNat s1col zJ) (.eqNat s1col (.add zJ (.natLit 1)))))
          (.pauliLit Pauli.Z) (.pauliLit Pauli.I))
        (.ite (.and (.eqNat s2col zJ)
                (.or (.eqNat s2row zA) (.eqNat (.add s2row (.natLit 1)) zA)))
          (.pauliLit Pauli.Z) (.pauliLit Pauli.I))))
    (.pauliLit Pauli.I)

/-- **The HGP(Rep(d), Rep(d)) family as a `CodeFn`** — one parametric object AST. -/
def code : CodeFn where
  body := .stabLam hgpEntryAST

/-! ## Cross-validation against the concrete `[[13,1,3]]` assets (`HGPCode.lean`)

Expected supports at `d = 3` (X-checks `k = 0..5`, Z-checks `k = 6..11`):
`s0 = X{0,3,9}`, `s6 = Z{0,1,9}` etc. — printed rows below must match the
`HGPCode.lean:40-52` stabilizer table entry-for-entry. -/

private def showRow (k : Nat) : List (Option Pauli) :=
  (List.range 13).map fun q => HGP.code.evalAt? 3 k q

#eval showRow 0   -- expect X at {0, 3, 9}
#eval showRow 1   -- expect X at {1, 4, 9, 10}
#eval showRow 5   -- expect X at {5, 8, 12}
#eval showRow 6   -- expect Z at {0, 1, 9}
#eval showRow 7   -- expect Z at {1, 2, 10}
#eval showRow 11  -- expect Z at {7, 8, 12}

/- **Full-table cross-check**: the parametric program at `d = 3` reproduces the
concrete `[[13,1,3]]` stabilizer table entry-for-entry. -/
#eval (List.finRange 12).all fun k => (List.finRange 13).all fun q =>
  HGP.code.evalAt? 3 k.val q.val = some (QStab.Examples.HGP13.stabilizers k q)
-- expect true

-- Parametric sanity at d = 5 ([[41,1,5]]): X-check (0,0) sector-1 col-0 rows {0,1};
-- sector-2 (0, j') with j' = 0 → qubit 25.
#eval (List.range 41).filterMap fun q =>
  match HGP.code.evalAt? 5 0 q with
  | some Pauli.I => none
  | some p => some (q, p)
  | none => none
-- expect [(0, X), (5, X), (25, X)]

end QHL.CodeLang.HGP
