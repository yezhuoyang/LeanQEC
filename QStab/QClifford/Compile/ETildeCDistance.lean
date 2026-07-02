import QStab.QClifford.Compile.ETildeCSimulation

/-!
# From the compiled barrier invariant to circuit-level distance

`etildeC_hoare_preservation` transports a QStab barrier-invariant certificate to
a compiled `FHoare` triple whose postcondition is the budget-guarded compiled
`barrierInvF`.  This file extracts the *distance content* of that triple: every
clean-start run of the compiled circuit whose data residual lies in the logical
class has spent at least `L.distance` faults.

Together with `hFold_of_valid` this reduces the compiled distance statement for
a scheme to exactly two scheme-specific inputs: the per-fault validity `hvalid`
and the vanishing of the barrier on the logical class (`hmu`, the semantic
content of `barrierLogicalF`, available for aligned codes via `mu_at_logical`).
The remaining step to the VCGen `ftDistance` slot is the per-instance
translation between the target `CodeSpec` failure predicate and
`L.contains (dataErrorOfQCState _ _ _)`.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QHL
open QHL.AssertionLang

/-- **Distance content of the compiled barrier invariant.**  If the compiled
circuit satisfies the budget-guarded compiled `barrierInvF` from the clean
state, the barrier vanishes on the logical class, and the source budget covers
the distance, then every clean-start run whose data residual is in the logical
class fired at least `L.distance` faults.  Runs beyond the source budget are
covered by `hbudget` outright. -/
theorem compiled_barrier_distance {P : QECParams} {k : Nat} {fc : FCircuit (P.n + k)}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (hoare : FHoare (fun sigma : QCState (P.n + k) => sigma = QCState.clean (P.n + k)) fc
      (compileFormulaWithinBudget k (barrierInvF beta L)))
    (hmu : ∀ E : ErrorVec P.n, L.contains E → beta.eval E = 0)
    (hbudget : L.distance ≤ P.C_budget) :
    ∀ sigma : QCState (P.n + k), qceval fc (QCState.clean (P.n + k)) sigma →
      L.contains (dataErrorOfQCState P k sigma) → L.distance ≤ sigma.lambda := by
  intro sigma hrun hmem
  by_cases hl : sigma.lambda ≤ P.C_budget
  · have hpost := hoare (QCState.clean (P.n + k)) sigma hrun rfl hl
    simp only [compileFormula, Formula.denoteWith, barrierInvF, barrierPotentialF, spentF,
      Formula.evalWith, Term.evalWith, qcliffordDataBackend] at hpost
    have h0 : beta.eval (dataErrorOfQCState P k sigma) = 0 := hmu _ hmem
    rw [h0] at hpost
    have h1 : L.distance ≤ 0 + (P.C_budget - (P.C_budget - sigma.lambda)) := hpost.1
    omega
  · exact Nat.le_trans hbudget (Nat.le_of_lt (Nat.lt_of_not_le hl))

end QStab.QClifford.Compile
