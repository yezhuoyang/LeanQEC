import QStab.State

/-! # Fixed QStab measurement programs

The canonical QStab program is a fixed stabilizer-measurement schedule.
Faults are not program statements; they are nondeterministic semantic
transitions around the current measurement coordinate.
-/

namespace QStab

open QECParams

/-- A fixed QStab measurement program.  The dynamic state carries the current
    coordinate; the program maps that coordinate to the stabilizer actually
    measured at that point. -/
structure QStabProgram (P : QECParams) where
  currentStab : Coord P -> Fin P.numStab

namespace QStabProgram

/-- The historical row-major schedule: coordinate `x` measures stabilizer `x`. -/
def rowMajor (P : QECParams) : QStabProgram P where
  currentStab := fun c => c.x

/-- Default coercion used only as a migration aid: old statements written as
    `Step P` elaborate to the row-major fixed measurement program. -/
instance (P : QECParams) : CoeDep QECParams P (QStabProgram P) where
  coe := rowMajor P

@[simp] theorem rowMajor_currentStab (P : QECParams) (c : Coord P) :
    (rowMajor P).currentStab c = c.x := rfl

end QStabProgram

end QStab
