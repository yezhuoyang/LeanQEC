import QStab.Invariant

/-! # Register initialization invariant (Lemma 4)

For any fixed budget level t:
  p(σ) = (C < t) ∨ { (C = t) ∧ ∀ (a,b) with (x,y) ≤ (a,b), G[a,b] = 0 }

Unvisited classical registers remain zero.
-/

namespace QStab.Invariants

open QECParams

/-- Register initialization invariant (parameterized by budget level t):
    when C = t, all registers at or after the current coordinate are false. -/
def registerInitInvariant (P : QECParams) (t : Nat) : Invariant P where
  holds := fun s =>
    s.C < t ∨
    (s.C = t ∧ ∀ (x : Fin P.numStab) (y : Fin P.R),
      s.coord ≤ Coord.mk x y → s.G x y = false)
  holds_init := sorry
  preservation := sorry

/-- Simplified form when t = 0: all registers at or after current coord are false. -/
def registerInitZero (P : QECParams) : Invariant P where
  holds := fun s =>
    s.C = 0 → ∀ (x : Fin P.numStab) (y : Fin P.R),
      s.coord ≤ Coord.mk x y → s.G x y = false
  holds_init := sorry
  preservation := sorry

end QStab.Invariants
