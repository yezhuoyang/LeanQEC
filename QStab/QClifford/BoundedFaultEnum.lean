import QStab.QClifford.FaultEnum
import QStab.QClifford.FaultHoare

/-! # Bounded concrete QClifford fault enumeration

`FaultEnum.allFaultRuns` enumerates every branch of a concrete faulty circuit,
which is exponential in the number of `errLoc`s.  For a distance-3 lower bound
we only need branches with at most two injected faults.  This file provides a
budgeted enumerator and proves the same membership equivalence for executions
whose fault count is within the budget.
-/

namespace QStab.QClifford

/-- The non-identity single-qubit Pauli choices at an `errLoc`. -/
def nonidentityPaulis : List Pauli := [Pauli.X, Pauli.Y, Pauli.Z]

theorem mem_nonidentityPaulis_of_ne_I {p : Pauli} (hp : p ≠ Pauli.I) :
    p ∈ nonidentityPaulis := by
  cases p <;> simp [nonidentityPaulis] at hp ⊢

theorem ne_I_of_mem_nonidentityPaulis {p : Pauli} (hp : p ∈ nonidentityPaulis) :
    p ≠ Pauli.I := by
  cases p <;> simp [nonidentityPaulis] at hp ⊢

/-- All `(fault-count, final-state)` outcomes using at most `budget` injected
faults.  At an error location, the idle branch keeps the same budget and each
injection branch consumes one unit. -/
def allFaultRunsUpTo {nq : Nat} : Nat -> FCircuit nq -> ErrorState nq ->
    List (Nat × ErrorState nq)
  | _, [], es => [(0, es)]
  | budget, .gate g :: rest, es => allFaultRunsUpTo budget rest (propagateGate g es)
  | 0, .errLoc _ :: rest, es => allFaultRunsUpTo 0 rest es
  | budget + 1, .errLoc q :: rest, es =>
      allFaultRunsUpTo (budget + 1) rest es ++
      (nonidentityPaulis.flatMap fun p =>
        (allFaultRunsUpTo budget rest (es.inject q p)).map fun we => (we.1 + 1, we.2))

/-- Every execution whose fault count is within the budget appears in the
budgeted enumeration. -/
theorem mem_of_fcevalW_le {nq : Nat} {w budget : Nat} {fc : FCircuit nq}
    {es es' : ErrorState nq} (h : fcevalW w fc es es') (hle : w ≤ budget) :
    (w, es') ∈ allFaultRunsUpTo budget fc es := by
  induction h generalizing budget with
  | nil es =>
      simp [allFaultRunsUpTo]
  | gate g is es esf w _ ih =>
      simpa [allFaultRunsUpTo] using ih hle
  | idle q is es esf w _ ih =>
      cases budget with
      | zero =>
          simpa [allFaultRunsUpTo] using ih hle
      | succ budget =>
          simp only [allFaultRunsUpTo, List.mem_append]
          exact Or.inl (ih hle)
  | inject q is es esf p hp w _ ih =>
      cases budget with
      | zero =>
          omega
      | succ budget =>
          have hle' : w ≤ budget := by omega
          simp only [allFaultRunsUpTo, List.mem_append, List.mem_flatMap, List.mem_map]
          right
          refine ⟨p, mem_nonidentityPaulis_of_ne_I hp, (w, esf), ih hle', rfl⟩

/-- Every member of the budgeted enumeration is a real execution and its fault
count is within the budget. -/
theorem fcevalW_of_mem_upTo {nq : Nat} {budget : Nat} {fc : FCircuit nq}
    {es : ErrorState nq} {we : Nat × ErrorState nq}
    (h : we ∈ allFaultRunsUpTo budget fc es) :
    fcevalW we.1 fc es we.2 ∧ we.1 ≤ budget := by
  induction fc generalizing budget es we with
  | nil =>
      obtain ⟨w0, es0⟩ := we
      simp only [allFaultRunsUpTo, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fcevalW.nil es0, Nat.zero_le budget⟩
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          simp only [allFaultRunsUpTo] at h
          obtain ⟨hrun, hbudget⟩ := ih h
          exact ⟨fcevalW.gate g rest es we.2 we.1 hrun, hbudget⟩
      | errLoc q =>
          cases budget with
          | zero =>
              simp only [allFaultRunsUpTo] at h
              obtain ⟨hrun, hbudget⟩ := ih h
              exact ⟨fcevalW.idle q rest es we.2 we.1 hrun, hbudget⟩
          | succ budget =>
              simp only [allFaultRunsUpTo, List.mem_append, List.mem_flatMap, List.mem_map] at h
              rcases h with hidle | hinj
              · obtain ⟨hrun, hbudget⟩ := ih hidle
                exact ⟨fcevalW.idle q rest es we.2 we.1 hrun, hbudget⟩
              · rcases hinj with ⟨p, hpMem, we0, hmem, hmap⟩
                obtain ⟨w0, es0⟩ := we0
                cases hmap
                obtain ⟨hrun, hbudget⟩ := ih hmem
                have hp : p ≠ Pauli.I := ne_I_of_mem_nonidentityPaulis hpMem
                exact ⟨fcevalW.inject q rest es es0 p hp w0 hrun, by omega⟩

/-- Fault tolerance up to `t` faults reduces to a finite budgeted check. -/
theorem tolerates_iff_upTo {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq -> Prop) (t : Nat) :
    ToleratesFaults fc failure t ↔
      forall we, we ∈ allFaultRunsUpTo t fc (ErrorState.clean nq) -> ¬ failure we.2 := by
  constructor
  · intro hTol we hmem
    obtain ⟨hrun, hle⟩ := fcevalW_of_mem_upTo hmem
    exact hTol we.1 we.2 hle hrun
  · intro hCheck w es' hle hrun
    exact hCheck (w, es') (mem_of_fcevalW_le hrun hle)

/-- State-resident form of the finite budgeted check. -/
theorem toleratesLambda_iff_upTo {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq -> Prop) (t : Nat) :
    ToleratesFaultsΛ fc failure t ↔
      forall we, we ∈ allFaultRunsUpTo t fc (ErrorState.clean nq) -> ¬ failure we.2 := by
  rw [← tolerates_iff_lambda]
  exact tolerates_iff_upTo fc failure t

end QStab.QClifford
