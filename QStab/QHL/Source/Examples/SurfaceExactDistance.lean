import QStab.QHL.Source.Examples.Surface
import QStab.QHL.Source.Examples.SurfaceParametricUpperBound

/-! # Parametric operational circuit distance of the NZ Surface code

This file combines two genuinely operational statements over one canonical
odd-distance Surface family:

* lower bound: the verifier-checked logical barrier invariant;
* upper bound: a concrete QStab execution of `d` type-0 faults producing the
  column-zero logical-X string.

The execution budget is explicitly retargeted to `d`. The original canonical
constructor uses `(d - 1) / 2`, which is appropriate for a below-distance FT
theorem but cannot execute a distance-`d` attack.
-/

namespace QHL.Source.Examples.SurfaceExactDistance

open QStab QStab.Examples QStab.Examples.SurfaceGeneral
     QStab.Examples.SurfaceParametric
     QStab.Paper.SurfaceBarrier
     QHL.AssertionLang QHL.Source.Examples.Surface
     QHL.Source.Examples.SurfaceParametricUpperBound

/-- Change only the adversarial execution budget of a QStab program. -/
abbrev retargetParams (P : QECParams) (budget : Nat) : QECParams where
  n := P.n
  k := P.k
  d := P.d
  R := P.R
  numStab := P.numStab
  stabilizers := P.stabilizers
  backActionSet := P.backActionSet
  r := P.r
  backAction_weight_bound := P.backAction_weight_bound
  C_budget := budget
  hn := P.hn
  hns := P.hns
  hR := P.hR

/-- Stabilizer-subgroup membership is independent of the execution budget. -/
def inStabRetarget {P : QECParams} {budget : Nat} {E : ErrorVec P.n} :
    InStab P E → InStab (retargetParams P budget) E
  | .identity => .identity
  | .gen i => by
      simpa [retargetParams] using
        (InStab.gen (P := retargetParams P budget) i)
  | .mul h₁ h₂ => .mul (inStabRetarget h₁) (inStabRetarget h₂)

/-- Reverse transport for stabilizer-subgroup membership. -/
def inStabRestore {P : QECParams} {budget : Nat} {E : ErrorVec P.n} :
    InStab (retargetParams P budget) E → InStab P E
  | .identity => .identity
  | .gen i => by
      simpa [retargetParams] using (InStab.gen (P := P) i)
  | .mul h₁ h₂ => .mul (inStabRestore h₁) (inStabRestore h₂)

/-- Retarget an NZ Surface specification to another execution budget without
    changing its code, logical operator, geometry, hooks, or schedule. -/
abbrev retargetSurfaceSpec {d : Nat} (spec : NZSurfaceSpec d) (budget : Nat) :
    NZSurfaceSpec d where
  params := retargetParams spec.params budget
  hn := spec.hn
  hd_pos := spec.hd_pos
  logicalZ := spec.logicalZ
  rowCut := spec.rowCut
  rowCut_zero := spec.rowCut_zero
  rowCut_succ := fun i hi => by
    obtain ⟨S, hS, hZ, hrow⟩ := spec.rowCut_succ i hi
    exact ⟨S, inStabRetarget hS, hZ, hrow⟩
  logicalZ_normalizer := spec.logicalZ_normalizer
  rowCut_spec := spec.rowCut_spec
  stab_commute := spec.stab_commute
  hook_spread_bound := fun s_idx e_B he E S_wit hS => by
    obtain ⟨S_wit', hS', hcard⟩ :=
      spec.hook_spread_bound s_idx e_B he E S_wit (inStabRestore hS)
    exact ⟨S_wit', inStabRetarget hS', hcard⟩

/-- Canonical odd-distance NZ Surface code run with budget exactly `d`. -/
abbrev exactSurfaceSpec (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : NZSurfaceSpec d :=
  retargetSurfaceSpec (mkSurfaceNZSurfaceSpec d hd3 hodd) d

@[simp] theorem exactSurfaceSpec_budget
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    (exactSurfaceSpec d hd3 hodd).params.C_budget = d :=
  rfl

/-- The exact state update performed by one type-0 X fault. -/
def t0XState {P : QECParams} (s : State P) (i : Fin P.n) : State P :=
  { s with
    C := s.C - 1
    cnt0 := s.cnt0 + 1
    lam_E := s.lam_E + 1
    E_tilde := ErrorVec.update s.E_tilde i .X }

/-- Inject one X fault at every qubit in a list, in reverse list order. -/
def injectXList {P : QECParams} (s : State P) : List (Fin P.n) → State P
  | [] => s
  | i :: is => t0XState (injectXList s is) i

@[simp] theorem injectXList_C {P : QECParams} (s : State P) (is : List (Fin P.n)) :
    (injectXList s is).C = s.C - is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [injectXList, t0XState, List.length_cons]
      rw [ih]
      omega

/-- The recursive injector is a genuine sequence of QStab type-0 steps. -/
theorem injectXList_run {P : QECParams} (prog : QStabProgram P)
    (s : State P) (is : List (Fin P.n))
    (hbudget : is.length ≤ s.C) :
    MultiStep prog (.active s) (.active (injectXList s is)) := by
  induction is with
  | nil => exact Relation.ReflTransGen.refl
  | cons i is ih =>
      simp only [List.length_cons] at hbudget
      have htail : is.length ≤ s.C := by omega
      have hrun := ih htail
      have hC : 0 < (injectXList s is).C := by
        rw [injectXList_C]
        omega
      exact Relation.ReflTransGen.tail hrun
        (Step.type0 (prog := prog) (injectXList s is) i .X (by decide) hC)

/-- Starting from identity and updating distinct qubits by X produces exactly
    the X-indicator function of list membership. -/
theorem injectXList_error {P : QECParams} (is : List (Fin P.n))
    (hnodup : is.Nodup) (q : Fin P.n) :
    (injectXList (State.init P) is).E_tilde q =
      if q ∈ is then Pauli.X else Pauli.I := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have hnot : i ∉ is := (List.nodup_cons.mp hnodup).1
      have htail : is.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hqi : q = i
      · subst q
        simp [injectXList, t0XState, ErrorVec.update, ih htail, hnot]
        rfl
      · simp [injectXList, t0XState, ErrorVec.update, ih htail, hqi]

/-- Finite list of all data qubits in column zero. -/
noncomputable def columnQubits (d : Nat) : List (Fin (d * d)) :=
  ((Finset.univ : Finset (Fin (d * d))).filter fun q => q.val % d = 0).toList

theorem columnQubits_length (d : Nat) (hd : 0 < d) :
    (columnQubits d).length = d := by
  have hweight := mkSurfaceAttackerX_weight d hd
  simpa [columnQubits, ErrorVec.weight, mkSurfaceAttackerX] using hweight

theorem columnQubits_nodup (d : Nat) : (columnQubits d).Nodup := by
  exact Finset.nodup_toList _

theorem mem_columnQubits (d : Nat) (q : Fin (d * d)) :
    q ∈ columnQubits d ↔ q.val % d = 0 := by
  simp [columnQubits]

/-- The concrete QStab injection sequence ends in the canonical Surface
    column-zero attacker. -/
theorem inject_column_error
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    (injectXList (State.init (exactSurfaceSpec d hd3 hodd).params)
      (columnQubits d)).E_tilde = mkSurfaceAttackerX d := by
  funext q
  rw [injectXList_error (columnQubits d) (columnQubits_nodup d) q]
  have hqval : q.val < d * d := q.isLt
  let q' : Fin (d * d) := ⟨q.val, hqval⟩
  change (if q' ∈ columnQubits d then Pauli.X else Pauli.I) =
    mkSurfaceAttackerX d q'
  simp [mem_columnQubits, mkSurfaceAttackerX]

/-- Checked operational lower bound for the canonical Surface family at the
    budget used by the matching attack. -/
theorem surface_operational_lower
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    OperationalLowerBound
      (surfaceProgram d (exactSurfaceSpec d hd3 hodd))
      (surface_logical_formula d (exactSurfaceSpec d hd3 hodd)) d :=
  surface_operational_lower_bound d (exactSurfaceSpec d hd3 hodd)

/-- Genuine operational upper bound: `d` QStab type-0 faults inject the
    column-zero logical-X attack. -/
theorem surface_operational_upper
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    OperationalUpperBound
      (surfaceProgram d (exactSurfaceSpec d hd3 hodd))
      (surface_logical_formula d (exactSurfaceSpec d hd3 hodd)) d := by
  let spec := exactSurfaceSpec d hd3 hodd
  let final := injectXList (State.init spec.params) (columnQubits d)
  refine ⟨final, ?_, ?_, ?_⟩
  · apply injectXList_run
      (surfaceProgram d spec)
    change (columnQubits d).length ≤ d
    rw [columnQubits_length d (by omega)]
  · apply (surface_logical_iff d spec final).mpr
    rw [show final.E_tilde = mkSurfaceAttackerX d by
      simpa [final, spec] using inject_column_error d hd3 hodd]
    exact mkSurfaceAttackerX_in_barZClass d hd3 hodd
  · change spec.params.C_budget - final.C = d
    rw [show final.C = spec.params.C_budget - (columnQubits d).length by
      exact injectXList_C (State.init spec.params) (columnQubits d)]
    rw [columnQubits_length d (by omega)]
    simp [spec]

/-- Parametric exact operational circuit distance for every odd `d ≥ 3`. -/
theorem surface_operational_exact_distance
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    OperationalExactDistance
      (surfaceProgram d (exactSurfaceSpec d hd3 hodd))
      (surface_logical_formula d (exactSurfaceSpec d hd3 hodd)) d where
  lower := surface_operational_lower d hd3 hodd
  upper := surface_operational_upper d hd3 hodd

#print axioms surface_operational_lower
#print axioms surface_operational_upper
#print axioms surface_operational_exact_distance

end QHL.Source.Examples.SurfaceExactDistance
