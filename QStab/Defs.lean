import QStab.PauliOps

/-! # QEC parameters and measurement coordinate system

Defines the `QECParams` structure bundling all code parameters,
and the `Coord` type for the stabilizer measurement schedule with `next`/`prev`.
-/

/-- Parameters for an [[n,k,d]] stabilizer code with R rounds of measurement. -/
structure QECParams where
  /-- Number of physical qubits -/
  n : Nat
  /-- Number of logical qubits -/
  k : Nat
  /-- Code distance -/
  d : Nat
  /-- Number of measurement rounds -/
  R : Nat
  /-- Number of stabilizer generators (= n - k) -/
  numStab : Nat
  /-- The stabilizer generators, each an n-qubit Pauli vector -/
  stabilizers : Fin numStab → ErrorVec n
  /-- Back-action weight upper bound per syndrome qubit -/
  r : Nat
  /-- Total error budget -/
  C_budget : Nat
  /-- n > 0 -/
  hn : 0 < n
  /-- numStab > 0 -/
  hns : 0 < numStab
  /-- R > 0 -/
  hR : 0 < R

namespace QECParams

/-- Measurement coordinate: (stabilizer index x, round index y).
    x ranges over 0..numStab-1, y ranges over 0..R-1.
    Paper convention: x corresponds to stabilizer T_x, y to round number.
    Total order: (x,y) < (x',y') iff x + numStab*y < x' + numStab*y'. -/
structure Coord (P : QECParams) where
  x : Fin P.numStab
  y : Fin P.R
  deriving DecidableEq

namespace Coord

/-- Linearize a coordinate to a single index: l = x + numStab * y. -/
def toLinear {P : QECParams} (c : Coord P) : Nat :=
  c.x.val + P.numStab * c.y.val

/-- Total order on coordinates via linearization. -/
instance {P : QECParams} : LT (Coord P) where
  lt c₁ c₂ := c₁.toLinear < c₂.toLinear

instance {P : QECParams} : LE (Coord P) where
  le c₁ c₂ := c₁.toLinear ≤ c₂.toLinear

instance {P : QECParams} (c₁ c₂ : Coord P) : Decidable (c₁ < c₂) :=
  inferInstanceAs (Decidable (c₁.toLinear < c₂.toLinear))

instance {P : QECParams} (c₁ c₂ : Coord P) : Decidable (c₁ ≤ c₂) :=
  inferInstanceAs (Decidable (c₁.toLinear ≤ c₂.toLinear))

/-- The first coordinate (0, 0). -/
def first (P : QECParams) : Coord P :=
  ⟨⟨0, P.hns⟩, ⟨0, P.hR⟩⟩

/-- The last coordinate (numStab-1, R-1). -/
def last (P : QECParams) : Coord P :=
  ⟨⟨P.numStab - 1, Nat.sub_lt P.hns (by omega)⟩,
   ⟨P.R - 1, Nat.sub_lt P.hR (by omega)⟩⟩

/-- Next(x,y): advance the measurement coordinate.
    Row-major order: x increments first, then y.
    Returns none at the last coordinate. -/
def next {P : QECParams} (c : Coord P) : Option (Coord P) :=
  if hx : c.x.val + 1 < P.numStab then
    some ⟨⟨c.x.val + 1, hx⟩, c.y⟩
  else if hy : c.y.val + 1 < P.R then
    some ⟨⟨0, P.hns⟩, ⟨c.y.val + 1, hy⟩⟩
  else
    none

/-- Prev(x,y): go back one step in the measurement schedule.
    Returns none at the first coordinate. -/
def prev {P : QECParams} (c : Coord P) : Option (Coord P) :=
  if hx : 0 < c.x.val then
    some ⟨⟨c.x.val - 1, by omega⟩, c.y⟩
  else if hy : 0 < c.y.val then
    some ⟨⟨P.numStab - 1, Nat.sub_lt P.hns (by omega)⟩,
          ⟨c.y.val - 1, by omega⟩⟩
  else
    none

/-- Whether coordinate c has been visited (is strictly before current). -/
def visited {P : QECParams} (current c : Coord P) : Prop :=
  c.toLinear < current.toLinear

instance {P : QECParams} (current c : Coord P) : Decidable (visited current c) :=
  inferInstanceAs (Decidable (c.toLinear < current.toLinear))

/-- Whether the current coordinate is at the end of a round (x = numStab - 1). -/
def isRoundEnd {P : QECParams} (c : Coord P) : Prop :=
  c.x.val = P.numStab - 1

instance {P : QECParams} (c : Coord P) : Decidable c.isRoundEnd :=
  inferInstanceAs (Decidable (c.x.val = P.numStab - 1))

end Coord

end QECParams
