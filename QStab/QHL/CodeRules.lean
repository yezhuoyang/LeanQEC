import QStab.QHL.CodeLogic

/-! # Basic derived rules for the code-level assertion language

This file does not add assertion-language primitives.  It proves the first
small rules about the existing executable semantics in `CodeLang`: finite
quantifiers, finite stabilizer equality, and self-commutation.  These are the
boring pieces we need before building larger Surface-code derivations.
-/

namespace QHL.CodeLang

namespace Formula

/-- Closed executable formula checking.  This is only a wrapper around
    `Formula.eval`; it is not a new formula constructor. -/
def check {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (A : Formula arity) (rho : Env arity) : Bool :=
  match A.eval codeBody fuel rho with
  | some true => true
  | _ => false

theorem check_sound {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {A : Formula arity} {rho : Env arity} :
    A.check codeBody fuel rho = true ->
      A.eval codeBody fuel rho = some true := by
  unfold check
  cases h : A.eval codeBody fuel rho <;> simp
  rename_i b
  cases b <;> simp

theorem check_complete {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {A : Formula arity} {rho : Env arity} :
    A.eval codeBody fuel rho = some true ->
      A.check codeBody fuel rho = true := by
  intro h
  simp [check, h]

end Formula

/-! ## Finite quantifier rules -/

theorem allNatLt_sound {n : Nat} {pred : Nat -> Option Bool} :
    allNatLt n pred = some true ->
      forall i, i < n -> pred i = some true := by
  induction n with
  | zero =>
      intro _ i hi
      omega
  | succ m ih =>
      intro h i hi
      unfold allNatLt at h
      cases hprev : allNatLt m pred with
      | none =>
          simp [hprev] at h
      | some ok =>
          cases ok
          · simp [hprev] at h
          · simp [hprev] at h
            by_cases hlast : i = m
            · subst hlast
              exact h
            · exact ih hprev i (by omega)

theorem allNatLt_complete {n : Nat} {pred : Nat -> Option Bool} :
    (forall i, i < n -> pred i = some true) ->
      allNatLt n pred = some true := by
  induction n with
  | zero =>
      intro _
      rfl
  | succ m ih =>
      intro h
      unfold allNatLt
      have hprev : allNatLt m pred = some true :=
        ih (fun i hi => h i (by omega))
      have hlast : pred m = some true :=
        h m (Nat.lt_succ_self m)
      simp [hprev, hlast]

theorem existsNatLt_sound {n : Nat} {pred : Nat -> Option Bool} :
    existsNatLt n pred = some true ->
      exists i, i < n /\ pred i = some true := by
  induction n with
  | zero =>
      intro h
      simp [existsNatLt] at h
  | succ m ih =>
      intro h
      unfold existsNatLt at h
      cases hprev : existsNatLt m pred with
      | none =>
          simp [hprev] at h
      | some ok =>
          cases ok
          · simp [hprev] at h
            exact ⟨m, Nat.lt_succ_self m, h⟩
          · obtain ⟨i, hi, hpred⟩ := ih hprev
            exact ⟨i, by omega, hpred⟩

theorem existsNatLt_defined {n : Nat} {pred : Nat -> Option Bool} :
    (forall i, i < n -> exists b, pred i = some b) ->
      exists b, existsNatLt n pred = some b := by
  induction n with
  | zero =>
      intro _
      exact ⟨false, rfl⟩
  | succ m ih =>
      intro htotal
      obtain ⟨prev, hprev⟩ :=
        ih (fun i hi => htotal i (by omega))
      cases prev
      · obtain ⟨last, hlast⟩ := htotal m (Nat.lt_succ_self m)
        cases last
        · exact ⟨false, by simp [existsNatLt, hprev, hlast]⟩
        · exact ⟨true, by simp [existsNatLt, hprev, hlast]⟩
      · exact ⟨true, by simp [existsNatLt, hprev]⟩

theorem existsNatLt_complete {n : Nat} {pred : Nat -> Option Bool} :
    (forall i, i < n -> exists b, pred i = some b) ->
    (exists i, i < n /\ pred i = some true) ->
      existsNatLt n pred = some true := by
  induction n with
  | zero =>
      intro _ h
      obtain ⟨_, hi, _⟩ := h
      omega
  | succ m ih =>
      intro htotal h
      rcases h with ⟨i, hi, hpred⟩
      by_cases hlast : i = m
      · have hm : pred m = some true := by
          simpa [hlast] using hpred
        obtain ⟨prev, hprev⟩ :=
          existsNatLt_defined (n := m) (pred := pred)
            (fun q hq => htotal q (by omega))
        cases prev <;> simp [existsNatLt, hprev, hm]
      · have hi' : i < m := by omega
        have hprev : existsNatLt m pred = some true :=
          ih (fun q hq => htotal q (by omega)) ⟨i, hi', hpred⟩
        simp [existsNatLt, hprev]

/-! ## Stabilizer equality rules -/

theorem stabEqUpTo_sound {n : Nat} {A B : PartialStabilizer} :
    stabEqUpTo n A B = some true ->
      forall q, q < n -> exists p, A q = some p /\ B q = some p := by
  induction n with
  | zero =>
      intro _ q hq
      omega
  | succ m ih =>
      intro h q hq
      unfold stabEqUpTo at h
      cases hprev : stabEqUpTo m A B with
      | none =>
          simp [hprev] at h
      | some ok =>
          cases ok
          · simp [hprev] at h
          · cases hA : A m with
            | none =>
                simp [hprev, hA] at h
            | some pA =>
                cases hB : B m with
                | none =>
                    simp [hprev, hA, hB] at h
                | some pB =>
                    simp [hprev, hA, hB] at h
                    by_cases hlast : q = m
                    · subst hlast
                      exact ⟨pA, hA, by simpa [← h] using hB⟩
                    · exact ih hprev q (by omega)

theorem stabEqUpTo_complete {n : Nat} {A B : PartialStabilizer} :
    (forall q, q < n -> exists p, A q = some p /\ B q = some p) ->
      stabEqUpTo n A B = some true := by
  induction n with
  | zero =>
      intro _
      rfl
  | succ m ih =>
      intro h
      unfold stabEqUpTo
      have hprev : stabEqUpTo m A B = some true :=
        ih (fun q hq => h q (by omega))
      obtain ⟨p, hA, hB⟩ := h m (Nat.lt_succ_self m)
      simp [hprev, hA, hB]

theorem stabEqUpTo_refl_of_total {n : Nat} {A : PartialStabilizer} :
    (forall q, q < n -> exists p, A q = some p) ->
      stabEqUpTo n A A = some true := by
  intro htotal
  exact stabEqUpTo_complete
    (fun q hq =>
      let ⟨p, hp⟩ := htotal q hq
      ⟨p, hp, hp⟩)

/-! ## Parity/self-commutation rules -/

private theorem pauli_anticommutes_self (p : Pauli) :
    ErrorVec.Pauli.anticommutes p p = false := by
  cases p <;> rfl

theorem parityUpTo_self_false {n : Nat} {A : PartialStabilizer} :
    (forall q, q < n -> exists p, A q = some p) ->
      parityUpTo n A A = some false := by
  induction n with
  | zero =>
      intro _
      rfl
  | succ m ih =>
      intro htotal
      unfold parityUpTo
      have hprev : parityUpTo m A A = some false :=
        ih (fun q hq => htotal q (by omega))
      obtain ⟨p, hp⟩ := htotal m (Nat.lt_succ_self m)
      simp [hprev, hp, pauli_anticommutes_self]

theorem commutesUpTo_self_eval {codeBody : Term 2 .stab} {fuel n : Nat}
    {A : Term 0 .stab} {S : PartialStabilizer}
    (hA : Term.eval codeBody fuel A Env.empty = some S)
    (htotal : forall q, q < n -> exists p, S q = some p) :
    Formula.eval codeBody fuel
        (.commutesUpTo (.natLit n) A A) Env.empty = some true := by
  simp [Formula.eval, Term.eval, hA, parityUpTo_self_false htotal]

/-! ## Projection rules for derived code predicates -/

theorem codeRowsCommuteUpTo_nat_open_sound {codeBody : Term 2 .stab}
    {fuel n numStab d : Nat} :
    Formula.eval codeBody fuel
        (Formula.codeRowsCommuteUpTo (.natLit n) (.natLit numStab) (.natLit d))
        Env.empty = some true ->
      forall i j, i < numStab -> j < numStab ->
        Formula.eval codeBody fuel
          (.commutesUpTo (Term.natLit n).weaken.weaken
            (Formula.codeRow (Term.natLit d).weaken.weaken (.var ⟨1, by decide⟩))
            (Formula.codeRow (Term.natLit d).weaken.weaken (.var ⟨0, by decide⟩)))
          (Env.cons j (Env.cons i Env.empty)) = some true := by
  intro h i j hi hj
  unfold Formula.codeRowsCommuteUpTo at h
  simp [Formula.eval, Term.eval, Term.weaken, Term.lift, Formula.codeRow] at h
  have hiRow := allNatLt_sound h i hi
  have hjRow := allNatLt_sound hiRow j hj
  simpa [Formula.eval, Term.eval, Term.weaken, Term.lift, Formula.codeRow] using hjRow

theorem normalizesCodeUpTo_nat_open_sound {codeBody : Term 2 .stab}
    {fuel n numStab d : Nat} {L : Term 0 .stab} :
    Formula.eval codeBody fuel
        (Formula.normalizesCodeUpTo (.natLit n) (.natLit numStab) (.natLit d) L)
        Env.empty = some true ->
      forall i, i < numStab ->
        Formula.eval codeBody fuel
          (.commutesUpTo (Term.natLit n).weaken
            (Formula.codeRow (Term.natLit d).weaken (.var ⟨0, by decide⟩))
            L.weaken)
          (Env.cons i Env.empty) = some true := by
  intro h i hi
  unfold Formula.normalizesCodeUpTo at h
  simp [Formula.eval, Term.eval, Term.weaken, Term.lift, Formula.codeRow] at h
  have hiRow := allNatLt_sound h i hi
  simpa [Formula.eval, Term.eval, Term.weaken, Term.lift, Formula.codeRow] using hiRow

theorem generatedByRowsUpTo_nat_sound {codeBody : Term 2 .stab}
    {fuel n d : Nat} {E : Term 0 .stab} {rows : List (Term 0 .nat)} :
    Formula.eval codeBody fuel
        (Formula.generatedByRowsUpTo (.natLit n) E (.natLit d) rows)
        Env.empty = some true ->
      Formula.eval codeBody fuel
        (.eqStabUpTo (.natLit n) E (Formula.rowProduct (.natLit d) rows))
        Env.empty = some true := by
  intro h
  simpa [Formula.generatedByRowsUpTo] using h

/-! ## Small closed checks using the derived rules -/

/-- info: false -/
#guard_msgs in
#eval Formula.check noncommutingTwoRowCode.body 1
  noncommutingTwoRowCheck Env.empty

/-- info: true -/
#guard_msgs in
#eval Formula.check oneRowXCode.body 1
  generatedX0Check Env.empty

/-- info: false -/
#guard_msgs in
#eval Formula.check oneRowXCode.body 1
  badGeneratedZ0Check Env.empty

#print axioms Formula.check_sound
#print axioms allNatLt_sound
#print axioms allNatLt_complete
#print axioms existsNatLt_sound
#print axioms stabEqUpTo_sound
#print axioms parityUpTo_self_false

end QHL.CodeLang
