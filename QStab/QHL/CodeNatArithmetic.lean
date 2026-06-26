import QStab.QHL.CodeLang

/-! # Symbolic natural-number arithmetic for code-family terms

This module is deliberately below the assertion and Hoare kernels.  It does not
add proof rules to `Formula.Deriv`, `SFormula.Deriv`, or QStab Hoare logic.

The purpose is to isolate the arithmetic facts needed by recursive Surface-code
syntax: row-major indices, row/column projections, the inner `(d - 2)` grid, and
the simple `/ 2` shell coordinates used on odd-distance boundaries.
-/

namespace QHL.CodeLang
namespace NatArithmetic

abbrev N (arity : Nat) := Term arity .nat
abbrev B (arity : Nat) := Term arity .bool

def evalNat? {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (t : N arity) (rho : Env arity) : Option Nat :=
  Term.eval codeBody fuel t rho

def evalBool? {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (t : B arity) (rho : Env arity) : Option Bool :=
  Term.eval codeBody fuel t rho

/-- The row-major index shape used by `Surface.gridIdx`: `dist * row + col`. -/
def gridIdxLeft {arity : Nat} (dist row col : N arity) : N arity :=
  .add (.mul dist row) col

/-- The row-major index shape used by the recursive inner-grid call:
    `row * dist + col`. -/
def gridIdxRight {arity : Nat} (dist row col : N arity) : N arity :=
  .add (.mul row dist) col

def square {arity : Nat} (dist : N arity) : N arity :=
  .mul dist dist

def rowOf {arity : Nat} (idx dist : N arity) : N arity :=
  .div idx dist

def colOf {arity : Nat} (idx dist : N arity) : N arity :=
  .mod idx dist

def innerDist {arity : Nat} (dist : N arity) : N arity :=
  .sub dist (.natLit 2)

def innerCoord {arity : Nat} (x : N arity) : N arity :=
  .sub x (.natLit 1)

def innerGridIdxRight {arity : Nat} (dist row col : N arity) : N arity :=
  gridIdxRight (innerDist dist) (innerCoord row) (innerCoord col)

theorem pos_of_lt {c d : Nat} (hc : c < d) : 0 < d := by
  exact Nat.lt_of_le_of_lt (Nat.zero_le c) hc

theorem gridIdxLeft_lt_square {d row col : Nat}
    (hrow : row < d) (hcol : col < d) : d * row + col < d * d := by
  have h1 : d * row + col < d * row + d := Nat.add_lt_add_left hcol (d * row)
  have h2 : d * row + d <= d * d := by
    simpa [Nat.mul_succ] using Nat.mul_le_mul_left d (Nat.succ_le_of_lt hrow)
  exact lt_of_lt_of_le h1 h2

theorem gridIdxRight_lt_square {d row col : Nat}
    (hrow : row < d) (hcol : col < d) : row * d + col < d * d := by
  simpa [Nat.mul_comm row d] using gridIdxLeft_lt_square (d := d) hrow hcol

theorem gridIdxLeft_div {d row col : Nat} (hcol : col < d) :
    (d * row + col) / d = row := by
  have hd : 0 < d := pos_of_lt hcol
  rw [Nat.add_comm (d * row) col]
  rw [Nat.add_mul_div_left col row hd]
  rw [Nat.div_eq_of_lt hcol]
  simp

theorem gridIdxRight_div {d row col : Nat} (hcol : col < d) :
    (row * d + col) / d = row := by
  simpa [Nat.mul_comm row d] using gridIdxLeft_div (d := d) (row := row) hcol

theorem gridIdxLeft_mod {d row col : Nat} (hcol : col < d) :
    (d * row + col) % d = col := by
  rw [Nat.add_comm (d * row) col]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hcol

theorem gridIdxRight_mod {d row col : Nat} (hcol : col < d) :
    (row * d + col) % d = col := by
  simpa [Nat.mul_comm row d] using gridIdxLeft_mod (d := d) (row := row) hcol

theorem pred_lt_sub_two {x d : Nat} (hlo : 1 <= x) (hhi : x < d - 1) :
    x - 1 < d - 2 := by
  omega

theorem sub_two_pos {d : Nat} (h : 3 <= d) : 0 < d - 2 := by
  omega

theorem innerGridIdxRight_lt_square {d row col : Nat}
    (hrowLo : 1 <= row) (hrowHi : row < d - 1)
    (hcolLo : 1 <= col) (hcolHi : col < d - 1) :
    (row - 1) * (d - 2) + (col - 1) < (d - 2) * (d - 2) :=
  gridIdxRight_lt_square (d := d - 2)
    (pred_lt_sub_two hrowLo hrowHi)
    (pred_lt_sub_two hcolLo hcolHi)

theorem innerGridIdxRight_div {d row col : Nat}
    (hcolLo : 1 <= col) (hcolHi : col < d - 1) :
    ((row - 1) * (d - 2) + (col - 1)) / (d - 2) = row - 1 :=
  gridIdxRight_div (d := d - 2) (row := row - 1)
    (pred_lt_sub_two hcolLo hcolHi)

theorem innerGridIdxRight_mod {d row col : Nat}
    (hcolLo : 1 <= col) (hcolHi : col < d - 1) :
    ((row - 1) * (d - 2) + (col - 1)) % (d - 2) = col - 1 :=
  gridIdxRight_mod (d := d - 2) (row := row - 1)
    (pred_lt_sub_two hcolLo hcolHi)

theorem two_mul_lt_sub_one_of_lt_half {b d : Nat}
    (hb : b < (d - 1) / 2) : 2 * b < d - 1 := by
  omega

theorem two_mul_succ_lt_of_lt_half {b d : Nat}
    (hb : b < (d - 1) / 2) : 2 * b + 1 < d := by
  omega

theorem two_mul_succ_succ_le_of_lt_half {b d : Nat}
    (hb : b < (d - 1) / 2) : 2 * b + 2 <= d := by
  omega

theorem even_half_lt_half_sub_one_of_lt {i d : Nat}
    (hi : i < d - 1) (hdOdd : d % 2 = 1) (hiEven : i % 2 = 0) :
    i / 2 < (d - 1) / 2 := by
  omega

theorem odd_pred_half_lt_half_sub_one_of_lt {i d : Nat}
    (hi : i < d - 1) (hiOdd : i % 2 = 1) :
    (i - 1) / 2 < (d - 1) / 2 := by
  omega

theorem even_twice_half {i : Nat} (hiEven : i % 2 = 0) :
    2 * (i / 2) = i := by
  omega

theorem odd_twice_pred_half {i : Nat} (hiOdd : i % 2 = 1) :
    2 * ((i - 1) / 2) + 1 = i := by
  omega

section Eval

variable {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat} {rho : Env arity}
variable {dist row col : N arity} {dv rv cv : Nat}

theorem eval_gridIdxLeft
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv) :
    evalNat? codeBody fuel (gridIdxLeft dist row col) rho = some (dv * rv + cv) := by
  dsimp [evalNat?] at *
  simp [gridIdxLeft, Term.eval, hd, hr, hc]

theorem eval_gridIdxRight
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv) :
    evalNat? codeBody fuel (gridIdxRight dist row col) rho = some (rv * dv + cv) := by
  dsimp [evalNat?] at *
  simp [gridIdxRight, Term.eval, hd, hr, hc]

theorem eval_square
    (hd : evalNat? codeBody fuel dist rho = some dv) :
    evalNat? codeBody fuel (square dist) rho = some (dv * dv) := by
  dsimp [evalNat?] at *
  simp [square, Term.eval, hd]

theorem eval_gridIdxLeft_lt_square
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hrow : rv < dv) (hcol : cv < dv) :
    evalBool? codeBody fuel (.ltNat (gridIdxLeft dist row col) (square dist)) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [gridIdxLeft, square, Term.eval, hd, hr, hc,
    gridIdxLeft_lt_square hrow hcol]

theorem eval_gridIdxRight_lt_square
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hrow : rv < dv) (hcol : cv < dv) :
    evalBool? codeBody fuel (.ltNat (gridIdxRight dist row col) (square dist)) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [gridIdxRight, square, Term.eval, hd, hr, hc,
    gridIdxRight_lt_square hrow hcol]

theorem eval_gridIdxLeft_rowOf
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hcol : cv < dv) :
    evalBool? codeBody fuel (.eqNat (rowOf (gridIdxLeft dist row col) dist) row) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [rowOf, gridIdxLeft, Term.eval, hd, hr, hc,
    gridIdxLeft_div hcol]

theorem eval_gridIdxRight_rowOf
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hcol : cv < dv) :
    evalBool? codeBody fuel (.eqNat (rowOf (gridIdxRight dist row col) dist) row) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [rowOf, gridIdxRight, Term.eval, hd, hr, hc,
    gridIdxRight_div hcol]

theorem eval_gridIdxLeft_colOf
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hcol : cv < dv) :
    evalBool? codeBody fuel (.eqNat (colOf (gridIdxLeft dist row col) dist) col) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [colOf, gridIdxLeft, Term.eval, hd, hr, hc,
    gridIdxLeft_mod hcol]

theorem eval_gridIdxRight_colOf
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hcol : cv < dv) :
    evalBool? codeBody fuel (.eqNat (colOf (gridIdxRight dist row col) dist) col) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [colOf, gridIdxRight, Term.eval, hd, hr, hc,
    gridIdxRight_mod hcol]

theorem eval_innerDist
    (hd : evalNat? codeBody fuel dist rho = some dv) :
    evalNat? codeBody fuel (innerDist dist) rho = some (dv - 2) := by
  dsimp [evalNat?] at *
  simp [innerDist, Term.eval, hd]

theorem eval_innerCoord
    (hx : evalNat? codeBody fuel row rho = some rv) :
    evalNat? codeBody fuel (innerCoord row) rho = some (rv - 1) := by
  dsimp [evalNat?] at *
  simp [innerCoord, Term.eval, hx]

theorem eval_innerGridIdxRight_lt_square
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hrowLo : 1 <= rv) (hrowHi : rv < dv - 1)
    (hcolLo : 1 <= cv) (hcolHi : cv < dv - 1) :
    evalBool? codeBody fuel
        (.ltNat (innerGridIdxRight dist row col) (square (innerDist dist))) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [innerGridIdxRight, gridIdxRight, square, innerDist,
    innerCoord, Term.eval, hd, hr, hc,
    innerGridIdxRight_lt_square hrowLo hrowHi hcolLo hcolHi]

theorem eval_innerGridIdxRight_rowOf
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hcolLo : 1 <= cv) (hcolHi : cv < dv - 1) :
    evalBool? codeBody fuel
        (.eqNat (rowOf (innerGridIdxRight dist row col) (innerDist dist))
          (innerCoord row)) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [rowOf, innerGridIdxRight, gridIdxRight, innerDist,
    innerCoord, Term.eval, hd, hr, hc, innerGridIdxRight_div (d := dv)
      (row := rv) (col := cv) hcolLo hcolHi]

theorem eval_innerGridIdxRight_colOf
    (hd : evalNat? codeBody fuel dist rho = some dv)
    (hr : evalNat? codeBody fuel row rho = some rv)
    (hc : evalNat? codeBody fuel col rho = some cv)
    (hcolLo : 1 <= cv) (hcolHi : cv < dv - 1) :
    evalBool? codeBody fuel
        (.eqNat (colOf (innerGridIdxRight dist row col) (innerDist dist))
          (innerCoord col)) rho =
      some true := by
  dsimp [evalNat?, evalBool?] at *
  simp [colOf, innerGridIdxRight, gridIdxRight, innerDist,
    innerCoord, Term.eval, hd, hr, hc, innerGridIdxRight_mod (d := dv)
      (row := rv) (col := cv) hcolLo hcolHi]

end Eval

/-! ## Build-gated smoke checks

These are closed executable examples.  They exercise the same syntax that the
Surface code uses, but they do not become assertion or Hoare proof rules.
-/

def smokeDist : N 0 := .natLit 5
def smokeRow : N 0 := .natLit 3
def smokeCol : N 0 := .natLit 4

example :
    evalNat? (.stabLam (.pauliLit Pauli.I)) 0
      (gridIdxLeft smokeDist smokeRow smokeCol) Env.empty = some 19 := by
  simp [evalNat?, gridIdxLeft, smokeDist, smokeRow, smokeCol, Term.eval]

example :
    evalBool? (.stabLam (.pauliLit Pauli.I)) 0
      (.eqNat (rowOf (gridIdxLeft smokeDist smokeRow smokeCol) smokeDist) smokeRow)
      Env.empty = some true := by
  simp [evalBool?, rowOf, gridIdxLeft, smokeDist, smokeRow, smokeCol, Term.eval]

example :
    evalBool? (.stabLam (.pauliLit Pauli.I)) 0
      (.eqNat (colOf (gridIdxLeft smokeDist smokeRow smokeCol) smokeDist) smokeCol)
      Env.empty = some true := by
  simp [evalBool?, colOf, gridIdxLeft, smokeDist, smokeRow, smokeCol, Term.eval]

example :
    evalBool? (.stabLam (.pauliLit Pauli.I)) 0
      (.ltNat (innerGridIdxRight (.natLit 7) (.natLit 3) (.natLit 4))
        (square (innerDist (.natLit 7))))
      Env.empty = some true := by
  simp [evalBool?, innerGridIdxRight, gridIdxRight, square, innerDist, innerCoord,
    Term.eval]

end NatArithmetic
end QHL.CodeLang
