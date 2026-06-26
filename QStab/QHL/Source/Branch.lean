import QStab.QHL.Assertion
import QStab.QHL.Assertion.Barrier
import QStab.Invariant

/-! # Canonical QStab branch Hoare logic

The canonical QStab proof language is not a command language with
`skip`, `seq`, or fixed injected-error statements.  A QStab program is a fixed
measurement schedule (`QStabProgram P`); faults are nondeterministic semantic
branches.  This file gives the one-step Hoare calculus over those branch labels
and the invariant-certificate rule that quantifies over every branch.
-/

namespace QHL.Source.Branch

open QStab QHL QHL.AssertionLang

/-- Labels for the enabled one-step nondeterministic transitions. -/
inductive TransitionLabel (P : QECParams) : Type where
  | err0 (i : Fin P.n) (p : Pauli) : TransitionLabel P
  | errI (i : Fin P.n) (p : Pauli) (mf : Bool) : TransitionLabel P
  | errII (e : ErrorVec P.n) (mf : Bool) : TransitionLabel P
  | errIII : TransitionLabel P
  | meas : TransitionLabel P

/-- Active-to-active transition semantics for one branch label. -/
inductive TransitionStep {P : QECParams} (prog : QStabProgram P) :
    TransitionLabel P -> State P -> State P -> Prop where
  | err0 (st : State P) (i : Fin P.n) (p : Pauli)
      (hp : p ≠ Pauli.I) (hC : 0 < st.C) :
      TransitionStep prog (.err0 i p) st { st with
        C := st.C - 1
        cnt0 := st.cnt0 + 1
        lam_E := st.lam_E + 1
        E_tilde := ErrorVec.update st.E_tilde i p
      }
  | errI (st : State P) (i : Fin P.n) (p : Pauli)
      (hp : p ≠ Pauli.I) (mf : Bool) (hC : 0 < st.C) :
      TransitionStep prog (.errI i p mf) st { st with
        C := st.C - 1
        cnt1 := st.cnt1 + 1
        lam_E := st.lam_E + 1
        E_tilde := ErrorVec.update st.E_tilde i p
        G := fun x y => if mf && x = currentStab prog st && y = st.coord.y
                         then !st.G x y
                         else st.G x y
      }
  | errII (st : State P) (e : ErrorVec P.n)
      (he : e ∈ P.backActionSet (currentStab prog st))
      (mf : Bool) (hC : 0 < st.C) :
      TransitionStep prog (.errII e mf) st { st with
        C := st.C - 1
        cnt2 := st.cnt2 + 1
        lam_E := st.lam_E + ErrorVec.weight e
        E_tilde := ErrorVec.mul e st.E_tilde
        G := fun x y => if mf && x = currentStab prog st && y = st.coord.y
                         then !st.G x y
                         else st.G x y
        F := fun j => if j = currentStab prog st
                       then xor (xor (st.F j)
                         (ErrorVec.parity (P.stabilizers (currentStab prog st)) e))
                         (if mf then true else false)
                       else st.F j
      }
  | errIII (st : State P) (hC : 0 < st.C) :
      TransitionStep prog .errIII st { st with
        C := st.C - 1
        cnt3 := st.cnt3 + 1
        G := fun x y => if x = currentStab prog st ∧ y = st.coord.y
                         then !st.G x y
                         else st.G x y
      }
  | meas (st : State P) (nc : QECParams.Coord P) (hN : st.coord.next = some nc) :
      TransitionStep prog .meas st (measureStep prog st nc)

namespace TransitionStep

/-- Every labelled branch is an active-to-active `Step prog`. -/
theorem toStep {P : QECParams} {prog : QStabProgram P}
    {tau : TransitionLabel P} {st st' : State P}
    (h : TransitionStep prog tau st st') :
    Step prog (.active st) (.active st') := by
  cases h with
  | err0 st i p hp hC => exact Step.type0 (prog := prog) st i p hp hC
  | errI st i p hp mf hC => exact Step.type1 (prog := prog) st i p hp mf hC
  | errII st e he mf hC => exact Step.type2 (prog := prog) st e he mf hC
  | errIII st hC => exact Step.type3 (prog := prog) st hC
  | meas st nc hN => exact Step.measure (prog := prog) st nc hN

end TransitionStep

/-- Semantic one-branch Hoare triple. -/
def Hoare {P : QECParams} (prog : QStabProgram P)
    (Pre : Assertion P) (tau : TransitionLabel P) (Post : Assertion P) : Prop :=
  ∀ st st' : State P, TransitionStep prog tau st st' -> Pre st -> Post st'

notation:90 "{{" Pre "}}[" prog "] " tau " {{" Post "}}" => Hoare prog Pre tau Post

/-- Semantic demonic one-step Hoare triple.  This is the QStab analogue of a
    `havoc` rule: every enabled nondeterministic active-to-active transition
    must preserve the postcondition. -/
def HavocHoare {P : QECParams} (prog : QStabProgram P)
    (Pre Post : Assertion P) : Prop :=
  ∀ st st' : State P, Step prog (.active st) (.active st') -> Pre st -> Post st'

/-- Semantic WP for Type-0. -/
def wpErr0 {P : QECParams} (i : Fin P.n) (p : Pauli) (Q : Assertion P) :
    Assertion P :=
  fun st => 0 < st.C -> Q ((StateSubst.err0 i p).apply st)

/-- Semantic WP for program-indexed Type-I. -/
def wpErrI {P : QECParams} (prog : QStabProgram P)
    (i : Fin P.n) (p : Pauli) (mf : Bool) (Q : Assertion P) : Assertion P :=
  fun st => 0 < st.C -> Q ((StateSubst.errI prog i p mf).apply st)

/-- Semantic WP for program-indexed Type-II. -/
def wpErrII {P : QECParams} (prog : QStabProgram P)
    (e : ErrorVec P.n) (mf : Bool) (Q : Assertion P) : Assertion P :=
  fun st => e ∈ P.backActionSet (currentStab prog st) -> 0 < st.C ->
    Q ((StateSubst.errII prog e mf).apply st)

/-- Semantic WP for program-indexed Type-III. -/
def wpErrIII {P : QECParams} (prog : QStabProgram P) (Q : Assertion P) :
    Assertion P :=
  fun st => 0 < st.C -> Q ((StateSubst.errIII prog).apply st)

/-- Semantic WP for the fixed scheduled measurement action. -/
def wpMeasFor {P : QECParams} (prog : QStabProgram P) (Q : Assertion P) :
    Assertion P :=
  fun st => ∀ nc : QECParams.Coord P, st.coord.next = some nc ->
    Q (measureStep prog st nc)

theorem hoare_err0 {P : QECParams} (prog : QStabProgram P)
    (Q : Assertion P) (i : Fin P.n) (p : Pauli) :
    {{wpErr0 i p Q}}[prog] .err0 i p {{Q}} := by
  intro st st' h hPre
  cases h with
  | err0 _ _ _ _ hC => exact hPre hC

theorem hoare_errI {P : QECParams} (prog : QStabProgram P)
    (Q : Assertion P) (i : Fin P.n) (p : Pauli) (mf : Bool) :
    {{wpErrI prog i p mf Q}}[prog] .errI i p mf {{Q}} := by
  intro st st' h hPre
  cases h with
  | errI _ _ _ _ _ hC => exact hPre hC

theorem hoare_errII {P : QECParams} (prog : QStabProgram P)
    (Q : Assertion P) (e : ErrorVec P.n) (mf : Bool) :
    {{wpErrII prog e mf Q}}[prog] .errII e mf {{Q}} := by
  intro st st' h hPre
  cases h with
  | errII _ _ he _ hC => exact hPre he hC

theorem hoare_errIII {P : QECParams} (prog : QStabProgram P) (Q : Assertion P) :
    {{wpErrIII prog Q}}[prog] .errIII {{Q}} := by
  intro st st' h hPre
  cases h with
  | errIII _ hC => exact hPre hC

theorem hoare_meas {P : QECParams} (prog : QStabProgram P) (Q : Assertion P) :
    {{wpMeasFor prog Q}}[prog] .meas {{Q}} := by
  intro st st' h hPre
  cases h with
  | meas _ nc hN => exact hPre nc hN

theorem hoare_consequence {P : QECParams} {prog : QStabProgram P}
    {Pre Pre' Post Post' : Assertion P} {tau : TransitionLabel P}
    (h : {{Pre'}}[prog] tau {{Post'}})
    (hPre : ∀ st : State P, Pre st -> Pre' st)
    (hPost : ∀ st : State P, Post' st -> Post st) :
    {{Pre}}[prog] tau {{Post}} := by
  intro st st' hstep hpre
  exact hPost st' (h st st' hstep (hPre st hpre))

theorem hoare_conj {P : QECParams} {prog : QStabProgram P}
    {Pre1 Pre2 Post1 Post2 : Assertion P} {tau : TransitionLabel P}
    (h1 : {{Pre1}}[prog] tau {{Post1}})
    (h2 : {{Pre2}}[prog] tau {{Post2}}) :
    {{fun st => Pre1 st ∧ Pre2 st}}[prog] tau {{fun st => Post1 st ∧ Post2 st}} := by
  intro st st' hstep hpre
  exact ⟨h1 st st' hstep hpre.1, h2 st st' hstep hpre.2⟩

theorem hoare_havocStep {P : QECParams} {prog : QStabProgram P}
    {Pre Post : Assertion P}
    (hErr0 : ∀ i p, p ≠ Pauli.I -> {{Pre}}[prog] .err0 i p {{Post}})
    (hErrI : ∀ i p, p ≠ Pauli.I -> ∀ mf, {{Pre}}[prog] .errI i p mf {{Post}})
    (hErrII : ∀ e mf, {{Pre}}[prog] .errII e mf {{Post}})
    (hErrIII : {{Pre}}[prog] .errIII {{Post}})
    (hMeas : {{Pre}}[prog] .meas {{Post}}) :
    HavocHoare prog Pre Post := by
  intro st st' hstep hPre
  cases hstep with
  | type0 s i p hp hC =>
      exact hErr0 i p hp st _
        (TransitionStep.err0 (prog := prog) st i p hp hC) hPre
  | type1 s i p hp mf hC =>
      exact hErrI i p hp mf st _
        (TransitionStep.errI (prog := prog) st i p hp mf hC) hPre
  | type2 s e he mf hC =>
      exact hErrII e mf st _
        (TransitionStep.errII (prog := prog) st e he mf hC) hPre
  | type3 s hC =>
      exact hErrIII st _ (TransitionStep.errIII (prog := prog) st hC) hPre
  | measure s nc hN =>
      exact hMeas st _ (TransitionStep.meas (prog := prog) st nc hN) hPre

theorem denote_wpErr0 {P : QECParams} (Q : Formula P []) (i : Fin P.n) (p : Pauli)
    (st : State P) :
    (Q.wpErr0 i p).denote st <-> wpErr0 i p Q.denote st := by
  unfold Formula.wpErr0 Formula.denote wpErr0
  simp only [Formula.eval, Term.eval]
  constructor
  · intro h hC
    exact (Formula.eval_substState (StateSubst.err0 i p) Q Env.empty st).mp (h hC)
  · intro h hC
    exact (Formula.eval_substState (StateSubst.err0 i p) Q Env.empty st).mpr (h hC)

theorem denote_wpErrI {P : QECParams} (prog : QStabProgram P) (Q : Formula P [])
    (i : Fin P.n) (p : Pauli) (mf : Bool) (st : State P) :
    (Q.wpErrI prog i p mf).denote st <-> wpErrI prog i p mf Q.denote st := by
  unfold Formula.wpErrI Formula.denote wpErrI
  simp only [Formula.eval, Term.eval]
  constructor
  · intro h hC
    exact (Formula.eval_substState (StateSubst.errI prog i p mf) Q Env.empty st).mp (h hC)
  · intro h hC
    exact (Formula.eval_substState (StateSubst.errI prog i p mf) Q Env.empty st).mpr (h hC)

theorem denote_wpErrII {P : QECParams} (prog : QStabProgram P) (Q : Formula P [])
    (e : ErrorVec P.n) (mf : Bool) (st : State P) :
    (Q.wpErrII prog e mf).denote st <-> wpErrII prog e mf Q.denote st := by
  unfold Formula.wpErrII Formula.denote wpErrII
  simp only [Formula.eval, Term.eval]
  constructor
  · intro h he hC
    exact (Formula.eval_substState (StateSubst.errII prog e mf) Q Env.empty st).mp
      (h he hC)
  · intro h he hC
    exact (Formula.eval_substState (StateSubst.errII prog e mf) Q Env.empty st).mpr
      (h he hC)

theorem denote_wpErrIII {P : QECParams} (prog : QStabProgram P) (Q : Formula P [])
    (st : State P) :
    (Q.wpErrIII prog).denote st <-> wpErrIII prog Q.denote st := by
  unfold Formula.wpErrIII Formula.denote wpErrIII
  simp only [Formula.eval, Term.eval]
  constructor
  · intro h hC
    exact (Formula.eval_substState (StateSubst.errIII prog) Q Env.empty st).mp (h hC)
  · intro h hC
    exact (Formula.eval_substState (StateSubst.errIII prog) Q Env.empty st).mpr (h hC)

theorem denote_wpMeasFor {P : QECParams} (prog : QStabProgram P) (Q : Formula P [])
    (st : State P) (nc : QECParams.Coord P) (hN : st.coord.next = some nc) :
    (Q.wpMeasFor prog).denote st ↔ Q.denote (measureStep prog st nc) := by
  rw [Formula.wpMeasFor, Formula.denote, Formula.denote,
    Formula.eval_substState (StateSubst.measFor prog)]
  have h_getD : st.coord.next.getD st.coord = nc := by simp [hN]
  simp only [StateSubst.measFor]
  rw [h_getD]

private theorem Pauli_I_mul_contract (p : Pauli) : Pauli.mul Pauli.I p = p := by
  cases p <;> rfl

private theorem Pauli_mul_I_contract (p : Pauli) : Pauli.mul p Pauli.I = p := by
  cases p <;> rfl

private theorem update_eq_mul_update_identity_contract (n : Nat) (E : ErrorVec n)
    (i : Fin n) (p : Pauli) :
    ErrorVec.update E i p =
      ErrorVec.mul (ErrorVec.update (ErrorVec.identity n) i p) E := by
  funext j
  unfold ErrorVec.update ErrorVec.mul ErrorVec.identity
  by_cases hij : j = i
  · subst hij
    simp only [Function.update_self]
    rw [Pauli_mul_I_contract]
  · simp only [Function.update_of_ne hij]
    rw [Pauli_I_mul_contract]

private theorem weight_update_identity_le_one_contract (n : Nat) (i : Fin n) (p : Pauli) :
    ErrorVec.weight (ErrorVec.update (ErrorVec.identity n) i p) <= 1 := by
  unfold ErrorVec.weight ErrorVec.update ErrorVec.identity
  have h_subset : (Finset.univ.filter
      fun j : Fin n => Function.update (fun _ => Pauli.I) i (Pauli.mul p Pauli.I) j ≠ Pauli.I) ⊆
        ({i} : Finset (Fin n)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_singleton]
    by_contra hji
    apply hj
    simp [Function.update, hji]
  calc (Finset.univ.filter
        fun j : Fin n => Function.update (fun _ => Pauli.I) i (Pauli.mul p Pauli.I) j ≠ Pauli.I).card
      <= ({i} : Finset (Fin n)).card := Finset.card_le_card h_subset
    _ = 1 := Finset.card_singleton i

/-- Initial-state validity of a barrier invariant follows from the contract. -/
theorem barrierInvF_init_of_contract {P : QECParams}
    (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
    (contract : BarrierContractCertificate beta L) :
    (barrierInvF beta L).denote (State.init P) := by
  refine ⟨?_, ?_⟩
  · have h_id := contract.identity_sound
    change L.distance <= beta.eval (ErrorVec.identity P.n) + (P.C_budget - P.C_budget)
    rw [h_id]
    simp
  · change P.C_budget <= P.C_budget
    exact Nat.le_refl P.C_budget

/-- The barrier invariant is preserved by every active branch of `Step prog`. -/
theorem barrierInvF_step_preservation_of_contract {P : QECParams}
    (prog : QStabProgram P) (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
    (contract : BarrierContractCertificate beta L)
    (a b : State P) :
    (barrierInvF beta L).denote a ->
    Step prog (.active a) (.active b) ->
    (barrierInvF beta L).denote b := by
  intro hPre step
  cases step with
  | type0 s i p hp hC =>
      obtain ⟨h_phi, h_budget⟩ := hPre
      refine ⟨?_, ?_⟩
      · change L.distance <=
          beta.eval (ErrorVec.update a.E_tilde i p) + (P.C_budget - (a.C - 1))
        change L.distance <= beta.eval a.E_tilde + (P.C_budget - a.C) at h_phi
        rw [update_eq_mul_update_identity_contract]
        have h_wt := weight_update_identity_le_one_contract P.n i p
        have h_tri := contract.triangle_sound a.E_tilde
          (ErrorVec.update (ErrorVec.identity P.n) i p)
        change a.C <= P.C_budget at h_budget
        omega
      · change a.C - 1 <= P.C_budget
        change a.C <= P.C_budget at h_budget
        omega
  | type1 s i p hp mf hC =>
      obtain ⟨h_phi, h_budget⟩ := hPre
      refine ⟨?_, ?_⟩
      · change L.distance <=
          beta.eval (ErrorVec.update a.E_tilde i p) + (P.C_budget - (a.C - 1))
        change L.distance <= beta.eval a.E_tilde + (P.C_budget - a.C) at h_phi
        rw [update_eq_mul_update_identity_contract]
        have h_wt := weight_update_identity_le_one_contract P.n i p
        have h_tri := contract.triangle_sound a.E_tilde
          (ErrorVec.update (ErrorVec.identity P.n) i p)
        change a.C <= P.C_budget at h_budget
        omega
      · change a.C - 1 <= P.C_budget
        change a.C <= P.C_budget at h_budget
        omega
  | type2 s e he mf hC =>
      obtain ⟨h_phi, h_budget⟩ := hPre
      refine ⟨?_, ?_⟩
      · change L.distance <=
          beta.eval (ErrorVec.mul e a.E_tilde) + (P.C_budget - (a.C - 1))
        change L.distance <= beta.eval a.E_tilde + (P.C_budget - a.C) at h_phi
        have h_align := contract.aligned_sound (currentStab prog a) e he a.E_tilde
        change a.C <= P.C_budget at h_budget
        omega
      · change a.C - 1 <= P.C_budget
        change a.C <= P.C_budget at h_budget
        omega
  | type3 s hC =>
      obtain ⟨h_phi, h_budget⟩ := hPre
      refine ⟨?_, ?_⟩
      · change L.distance <= beta.eval a.E_tilde + (P.C_budget - (a.C - 1))
        change L.distance <= beta.eval a.E_tilde + (P.C_budget - a.C) at h_phi
        change a.C <= P.C_budget at h_budget
        omega
      · change a.C - 1 <= P.C_budget
        change a.C <= P.C_budget at h_budget
        omega
  | measure s nc hN =>
      simpa [barrierInvF, barrierPotentialF, spentF, Formula.denote, Formula.eval,
        Term.eval, measureStep_E_tilde, measureStep_C] using hPre

/-- The barrier invariant is preserved by each labelled branch. -/
theorem barrierInvF_transition_preservation_of_contract {P : QECParams}
    (prog : QStabProgram P) (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
    (contract : BarrierContractCertificate beta L)
    {tau : TransitionLabel P} {a b : State P}
    (step : TransitionStep prog tau a b) :
    (barrierInvF beta L).denote a -> (barrierInvF beta L).denote b :=
  fun hPre =>
    barrierInvF_step_preservation_of_contract prog beta L contract a b hPre step.toStep

/-- Derivation trees for one-branch QStab Hoare logic. -/
inductive Deriv {P : QECParams} (prog : QStabProgram P) :
    Assertion P -> TransitionLabel P -> Assertion P -> Type where
  | H_Err0 (Q : Assertion P) (i : Fin P.n) (p : Pauli) :
      Deriv prog (wpErr0 i p Q) (.err0 i p) Q
  | H_ErrI (Q : Assertion P) (i : Fin P.n) (p : Pauli) (mf : Bool) :
      Deriv prog (wpErrI prog i p mf Q) (.errI i p mf) Q
  | H_ErrII (Q : Assertion P) (e : ErrorVec P.n) (mf : Bool) :
      Deriv prog (wpErrII prog e mf Q) (.errII e mf) Q
  | H_ErrIII (Q : Assertion P) :
      Deriv prog (wpErrIII prog Q) .errIII Q
  | H_Meas (Q : Assertion P) :
      Deriv prog (wpMeasFor prog Q) .meas Q
  | H_Consequence {Pre Pre' Post Post' : Assertion P} {tau : TransitionLabel P} :
      Deriv prog Pre' tau Post' ->
      (∀ st : State P, Pre st -> Pre' st) ->
      (∀ st : State P, Post' st -> Post st) ->
      Deriv prog Pre tau Post
  | H_Conj {Pre1 Pre2 Post1 Post2 : Assertion P} {tau : TransitionLabel P} :
      Deriv prog Pre1 tau Post1 -> Deriv prog Pre2 tau Post2 ->
      Deriv prog (fun st => Pre1 st ∧ Pre2 st) tau (fun st => Post1 st ∧ Post2 st)

namespace Deriv

/-- Soundness of branch derivations against labelled nondeterministic semantics. -/
theorem sound {P : QECParams} {prog : QStabProgram P}
    {Pre Post : Assertion P} {tau : TransitionLabel P} :
    Deriv prog Pre tau Post -> {{Pre}}[prog] tau {{Post}}
  | .H_Err0 Q i p => hoare_err0 prog Q i p
  | .H_ErrI Q i p mf => hoare_errI prog Q i p mf
  | .H_ErrII Q e mf => hoare_errII prog Q e mf
  | .H_ErrIII Q => hoare_errIII prog Q
  | .H_Meas Q => hoare_meas prog Q
  | .H_Consequence d hPre hPost => hoare_consequence d.sound hPre hPost
  | .H_Conj d1 d2 => hoare_conj d1.sound d2.sound

noncomputable def H_Err0F {P : QECParams} {prog : QStabProgram P}
    (Q : Formula P []) (i : Fin P.n) (p : Pauli) :
    Deriv prog (Q.wpErr0 i p).denote (.err0 i p) Q.denote :=
  H_Consequence (H_Err0 Q.denote i p)
    (fun st => (denote_wpErr0 Q i p st).mp) (fun _ => id)

noncomputable def H_ErrIF {P : QECParams} {prog : QStabProgram P}
    (Q : Formula P []) (i : Fin P.n) (p : Pauli) (mf : Bool) :
    Deriv prog (Q.wpErrI prog i p mf).denote (.errI i p mf) Q.denote :=
  H_Consequence (H_ErrI Q.denote i p mf)
    (fun st => (denote_wpErrI prog Q i p mf st).mp) (fun _ => id)

noncomputable def H_ErrIIF {P : QECParams} {prog : QStabProgram P}
    (Q : Formula P []) (e : ErrorVec P.n) (mf : Bool) :
    Deriv prog (Q.wpErrII prog e mf).denote (.errII e mf) Q.denote :=
  H_Consequence (H_ErrII Q.denote e mf)
    (fun st => (denote_wpErrII prog Q e mf st).mp) (fun _ => id)

noncomputable def H_ErrIIIF {P : QECParams} {prog : QStabProgram P}
    (Q : Formula P []) :
    Deriv prog (Q.wpErrIII prog).denote .errIII Q.denote :=
  H_Consequence (H_ErrIII Q.denote)
    (fun st => (denote_wpErrIII prog Q st).mp) (fun _ => id)

noncomputable def H_MeasF {P : QECParams} {prog : QStabProgram P}
    (Q : Formula P []) :
    Deriv prog (Q.wpMeasFor prog).denote .meas Q.denote :=
  H_Consequence (H_Meas Q.denote)
    (fun st h nc hN => (denote_wpMeasFor prog Q st nc hN).mp h) (fun _ => id)

end Deriv

/-- Derivation trees for demonic one-step nondeterminism.  The `H_HavocStep`
    rule is a finite rule schema: a verifier checks one derivation family for
    each transition kind, and the semantics quantifies over every enabled
    branch. -/
inductive HavocDeriv {P : QECParams} (prog : QStabProgram P) :
    Assertion P -> Assertion P -> Type where
  | H_HavocStep {Pre Post : Assertion P} :
      (err0 : ∀ i p, p ≠ Pauli.I -> Deriv prog Pre (.err0 i p) Post) ->
      (errI : ∀ i p, p ≠ Pauli.I -> ∀ mf, Deriv prog Pre (.errI i p mf) Post) ->
      (errII : ∀ e mf, Deriv prog Pre (.errII e mf) Post) ->
      Deriv prog Pre .errIII Post ->
      Deriv prog Pre .meas Post ->
      HavocDeriv prog Pre Post
  | H_Consequence {Pre Pre' Post' Post : Assertion P} :
      HavocDeriv prog Pre' Post' ->
      (∀ st : State P, Pre st -> Pre' st) ->
      (∀ st : State P, Post' st -> Post st) ->
      HavocDeriv prog Pre Post
  | H_Conj {Pre1 Pre2 Post1 Post2 : Assertion P} :
      HavocDeriv prog Pre1 Post1 -> HavocDeriv prog Pre2 Post2 ->
      HavocDeriv prog (fun st => Pre1 st ∧ Pre2 st) (fun st => Post1 st ∧ Post2 st)

namespace HavocDeriv

/-- Soundness of the demonic one-step derivation rule. -/
theorem sound {P : QECParams} {prog : QStabProgram P}
    {Pre Post : Assertion P} :
    HavocDeriv prog Pre Post -> HavocHoare prog Pre Post
  | .H_HavocStep err0 errI errII errIII meas =>
      hoare_havocStep
        (fun i p hp => (err0 i p hp).sound)
        (fun i p hp mf => (errI i p hp mf).sound)
        (fun e mf => (errII e mf).sound)
        errIII.sound
        meas.sound
  | .H_Consequence d hPre hPost =>
      fun st st' hstep hpre => hPost st' (d.sound st st' hstep (hPre st hpre))
  | .H_Conj d1 d2 =>
      fun st st' hstep hpre =>
        ⟨d1.sound st st' hstep hpre.1, d2.sound st st' hstep hpre.2⟩

end HavocDeriv

/-- Small local entailment calculus for formula-level consequence steps. -/
inductive Entails (P : QECParams) : Formula P [] -> Formula P [] -> Type where
  | refl (A : Formula P []) : Entails P A A
  | trans {A B C : Formula P []} : Entails P A B -> Entails P B C -> Entails P A C
  | top (A : Formula P []) : Entails P A .top
  | bot (A : Formula P []) : Entails P .bot A
  | andIntro {A B C : Formula P []} :
      Entails P A B -> Entails P A C -> Entails P A (.and B C)
  | andLeft (A B : Formula P []) : Entails P (.and A B) A
  | andRight (A B : Formula P []) : Entails P (.and A B) B
  | topWpErr0 (prog : QStabProgram P) (i : Fin P.n) (p : Pauli) :
      Entails P .top (Formula.wpErr0 i p (Formula.top (P := P)))
  | topWpErrI (prog : QStabProgram P) (i : Fin P.n) (p : Pauli) (mf : Bool) :
      Entails P .top (Formula.wpErrI prog i p mf (Formula.top (P := P)))
  | topWpErrII (prog : QStabProgram P) (e : ErrorVec P.n) (mf : Bool) :
      Entails P .top (Formula.wpErrII prog e mf (Formula.top (P := P)))
  | topWpErrIII (prog : QStabProgram P) :
      Entails P .top (Formula.wpErrIII prog (Formula.top (P := P)))
  | topWpMeasFor (prog : QStabProgram P) :
      Entails P .top (Formula.wpMeasFor prog (Formula.top (P := P)))
  | barrierInvWpErr0 (prog : QStabProgram P)
      (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
      (contract : SyntacticBarrierContractCertificate beta L)
      (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) :
      Entails P (barrierInvF beta L) ((barrierInvF beta L).wpErr0 i p)
  | barrierInvWpErrI (prog : QStabProgram P)
      (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
      (contract : SyntacticBarrierContractCertificate beta L)
      (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
      Entails P (barrierInvF beta L) ((barrierInvF beta L).wpErrI prog i p mf)
  | barrierInvWpErrII (prog : QStabProgram P)
      (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
      (contract : SyntacticBarrierContractCertificate beta L)
      (e : ErrorVec P.n) (mf : Bool) :
      Entails P (barrierInvF beta L) ((barrierInvF beta L).wpErrII prog e mf)
  | barrierInvWpErrIII (prog : QStabProgram P)
      (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
      (contract : SyntacticBarrierContractCertificate beta L) :
      Entails P (barrierInvF beta L) ((barrierInvF beta L).wpErrIII prog)
  | barrierInvWpMeasFor (prog : QStabProgram P)
      (beta : BarrierSymbol P) (L : LogicalClassSymbol P)
      (_contract : SyntacticBarrierContractCertificate beta L) :
      Entails P (barrierInvF beta L) ((barrierInvF beta L).wpMeasFor prog)

namespace Entails

def sound {P : QECParams} {A B : Formula P []} : Entails P A B -> A.Entails B
  | .refl _ => fun _ h => h
  | .trans h₁ h₂ => fun st h => h₂.sound st (h₁.sound st h)
  | .top _ => fun _ _ => trivial
  | .bot _ => fun _ h => False.elim h
  | .andIntro h₁ h₂ => fun st h => ⟨h₁.sound st h, h₂.sound st h⟩
  | .andLeft _ _ => fun _ h => h.1
  | .andRight _ _ => fun _ h => h.2
  | .topWpErr0 _ _ _ => by
      intro st _
      simp [Formula.wpErr0, Formula.denote, Formula.eval, Formula.substState, Term.eval]
  | .topWpErrI _ _ _ _ => by
      intro st _
      simp [Formula.wpErrI, Formula.denote, Formula.eval, Formula.substState, Term.eval]
  | .topWpErrII _ _ _ => by
      intro st _
      simp [Formula.wpErrII, Formula.denote, Formula.eval, Formula.substState, Term.eval]
  | .topWpErrIII _ => by
      intro st _
      simp [Formula.wpErrIII, Formula.denote, Formula.eval, Formula.substState, Term.eval]
  | .topWpMeasFor _ => by
      intro st _
      trivial
  | .barrierInvWpErr0 prog beta L contract i p hp => by
      intro st hInv
      exact (denote_wpErr0 (barrierInvF beta L) i p st).mpr (fun hC =>
        barrierInvF_transition_preservation_of_contract prog beta L contract.toChecked
          (TransitionStep.err0 (prog := prog) st i p hp hC) hInv)
  | .barrierInvWpErrI prog beta L contract i p hp mf => by
      intro st hInv
      exact (denote_wpErrI prog (barrierInvF beta L) i p mf st).mpr (fun hC =>
        barrierInvF_transition_preservation_of_contract prog beta L contract.toChecked
          (TransitionStep.errI (prog := prog) st i p hp mf hC) hInv)
  | .barrierInvWpErrII prog beta L contract e mf => by
      intro st hInv
      exact (denote_wpErrII prog (barrierInvF beta L) e mf st).mpr (fun he hC =>
        barrierInvF_transition_preservation_of_contract prog beta L contract.toChecked
          (TransitionStep.errII (prog := prog) st e he mf hC) hInv)
  | .barrierInvWpErrIII prog beta L contract => by
      intro st hInv
      exact (denote_wpErrIII prog (barrierInvF beta L) st).mpr (fun hC =>
        barrierInvF_transition_preservation_of_contract prog beta L contract.toChecked
          (TransitionStep.errIII (prog := prog) st hC) hInv)
  | .barrierInvWpMeasFor prog beta L _contract => by
      intro st hInv
      change ((barrierInvF beta L).substState (StateSubst.measFor prog)).eval Env.empty st
      exact (Formula.eval_substState (StateSubst.measFor prog)
        (barrierInvF beta L) Env.empty st).mpr (by
          simpa [barrierInvF, barrierPotentialF, spentF, Formula.eval, Term.eval,
            StateSubst.measFor, measureStep_E_tilde, measureStep_C] using hInv)

end Entails

/-- Verifier-facing transition-label proof trees over closed formulas. -/
inductive Certificate {P : QECParams} (prog : QStabProgram P) :
    Formula P [] -> TransitionLabel P -> Formula P [] -> Type where
  | err0 (Q : Formula P []) (i : Fin P.n) (p : Pauli) :
      Certificate prog (Q.wpErr0 i p) (.err0 i p) Q
  | errI (Q : Formula P []) (i : Fin P.n) (p : Pauli) (mf : Bool) :
      Certificate prog (Q.wpErrI prog i p mf) (.errI i p mf) Q
  | errII (Q : Formula P []) (e : ErrorVec P.n) (mf : Bool) :
      Certificate prog (Q.wpErrII prog e mf) (.errII e mf) Q
  | errIII (Q : Formula P []) :
      Certificate prog (Q.wpErrIII prog) .errIII Q
  | meas (Q : Formula P []) :
      Certificate prog (Q.wpMeasFor prog) .meas Q
  | consequence {A A' B' B : Formula P []} {tau : TransitionLabel P} :
      Entails P A A' -> Certificate prog A' tau B' ->
      Entails P B' B -> Certificate prog A tau B
  | conj {A₁ A₂ B₁ B₂ : Formula P []} {tau : TransitionLabel P} :
      Certificate prog A₁ tau B₁ -> Certificate prog A₂ tau B₂ ->
      Certificate prog (.and A₁ A₂) tau (.and B₁ B₂)

namespace Certificate

def size {P : QECParams} {prog : QStabProgram P}
    {A B : Formula P []} {tau : TransitionLabel P} :
    Certificate prog A tau B -> Nat
  | .err0 _ _ _ => 1
  | .errI _ _ _ _ => 1
  | .errII _ _ _ => 1
  | .errIII _ => 1
  | .meas _ => 1
  | .consequence _ d _ => 1 + d.size
  | .conj d₁ d₂ => 1 + d₁.size + d₂.size

/-- Checker: folds certificate data into the branch-Hoare derivation kernel. -/
noncomputable def check {P : QECParams} {prog : QStabProgram P}
    {A B : Formula P []} {tau : TransitionLabel P} :
    Certificate prog A tau B -> Deriv prog A.denote tau B.denote
  | .err0 Q i p => Deriv.H_Err0F Q i p
  | .errI Q i p mf => Deriv.H_ErrIF Q i p mf
  | .errII Q e mf => Deriv.H_ErrIIF Q e mf
  | .errIII Q => Deriv.H_ErrIIIF Q
  | .meas Q => Deriv.H_MeasF Q
  | .consequence hpre d hpost =>
      Deriv.H_Consequence d.check hpre.sound hpost.sound
  | .conj d₁ d₂ => Deriv.H_Conj d₁.check d₂.check

theorem check_sound {P : QECParams} {prog : QStabProgram P}
    {A B : Formula P []} {tau : TransitionLabel P}
    (cert : Certificate prog A tau B) : {{A.denote}}[prog] tau {{B.denote}} :=
  cert.check.sound

end Certificate

/-! ## Syntactic branch certificates for the barrier invariant

The next five builders are the canonical invariant-preservation proof shape:
prove the invariant entails the branch-specific weakest precondition, then
apply the ordinary branch Hoare rule.  They are deliberately not primitive
Hoare rules.
-/

noncomputable def barrierInvErr0Certificate {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) :
    Certificate prog (barrierInvF beta L) (.err0 i p) (barrierInvF beta L) :=
  Certificate.consequence
    (Entails.barrierInvWpErr0 prog beta L contract i p hp)
    (Certificate.err0 (barrierInvF beta L) i p)
    (Entails.refl (barrierInvF beta L))

noncomputable def barrierInvErrICertificate {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
    Certificate prog (barrierInvF beta L) (.errI i p mf) (barrierInvF beta L) :=
  Certificate.consequence
    (Entails.barrierInvWpErrI prog beta L contract i p hp mf)
    (Certificate.errI (barrierInvF beta L) i p mf)
    (Entails.refl (barrierInvF beta L))

noncomputable def barrierInvErrIICertificate {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (e : ErrorVec P.n) (mf : Bool) :
    Certificate prog (barrierInvF beta L) (.errII e mf) (barrierInvF beta L) :=
  Certificate.consequence
    (Entails.barrierInvWpErrII prog beta L contract e mf)
    (Certificate.errII (barrierInvF beta L) e mf)
    (Entails.refl (barrierInvF beta L))

noncomputable def barrierInvErrIIICertificate {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    Certificate prog (barrierInvF beta L) .errIII (barrierInvF beta L) :=
  Certificate.consequence
    (Entails.barrierInvWpErrIII prog beta L contract)
    (Certificate.errIII (barrierInvF beta L))
    (Entails.refl (barrierInvF beta L))

noncomputable def barrierInvMeasCertificate {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    Certificate prog (barrierInvF beta L) .meas (barrierInvF beta L) :=
  Certificate.consequence
    (Entails.barrierInvWpMeasFor prog beta L contract)
    (Certificate.meas (barrierInvF beta L))
    (Entails.refl (barrierInvF beta L))

@[simp] theorem barrierInvErr0Certificate_size {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) :
    (barrierInvErr0Certificate (prog := prog) contract i p hp).size = 2 := rfl

@[simp] theorem barrierInvErrICertificate_size {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
    (barrierInvErrICertificate (prog := prog) contract i p hp mf).size = 2 := rfl

@[simp] theorem barrierInvErrIICertificate_size {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (e : ErrorVec P.n) (mf : Bool) :
    (barrierInvErrIICertificate (prog := prog) contract e mf).size = 2 := rfl

@[simp] theorem barrierInvErrIIICertificate_size {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    (barrierInvErrIIICertificate (prog := prog) contract).size = 2 := rfl

@[simp] theorem barrierInvMeasCertificate_size {P : QECParams} {prog : QStabProgram P}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    (barrierInvMeasCertificate (prog := prog) contract).size = 2 := rfl

/-- Verifier-facing proof tree for one demonic nondeterministic QStab step. -/
inductive HavocCertificate {P : QECParams} (prog : QStabProgram P) :
    Formula P [] -> Formula P [] -> Type where
  | havocStep {A B : Formula P []} :
      (err0 : ∀ i p, p ≠ Pauli.I -> Certificate prog A (.err0 i p) B) ->
      (errI : ∀ i p, p ≠ Pauli.I -> ∀ mf, Certificate prog A (.errI i p mf) B) ->
      (errII : ∀ e mf, Certificate prog A (.errII e mf) B) ->
      Certificate prog A .errIII B ->
      Certificate prog A .meas B ->
      HavocCertificate prog A B
  | consequence {A A' B' B : Formula P []} :
      Entails P A A' -> HavocCertificate prog A' B' ->
      Entails P B' B -> HavocCertificate prog A B
  | conj {A₁ A₂ B₁ B₂ : Formula P []} :
      HavocCertificate prog A₁ B₁ -> HavocCertificate prog A₂ B₂ ->
      HavocCertificate prog (.and A₁ A₂) (.and B₁ B₂)

namespace HavocCertificate

def size {P : QECParams} {prog : QStabProgram P}
    {A B : Formula P []} :
    HavocCertificate prog A B -> Nat
  | .havocStep _ _ _ _ _ => 1
  | .consequence _ d _ => 1 + d.size
  | .conj d₁ d₂ => 1 + d₁.size + d₂.size

/-- Checker: folds a demonic branch-family certificate into the Hoare kernel. -/
noncomputable def check {P : QECParams} {prog : QStabProgram P}
    {A B : Formula P []} :
    HavocCertificate prog A B -> HavocDeriv prog A.denote B.denote
  | .havocStep err0 errI errII errIII meas =>
      HavocDeriv.H_HavocStep
        (fun i p hp => (err0 i p hp).check)
        (fun i p hp mf => (errI i p hp mf).check)
        (fun e mf => (errII e mf).check)
        errIII.check
        meas.check
  | .consequence hpre d hpost =>
      HavocDeriv.H_Consequence d.check hpre.sound hpost.sound
  | .conj d₁ d₂ => HavocDeriv.H_Conj d₁.check d₂.check

theorem check_sound {P : QECParams} {prog : QStabProgram P}
    {A B : Formula P []}
    (cert : HavocCertificate prog A B) : HavocHoare prog A.denote B.denote :=
  cert.check.sound

end HavocCertificate

abbrev ProofDerivation {P : QECParams} (prog : QStabProgram P)
    (A : Formula P []) (tau : TransitionLabel P) (B : Formula P []) : Type :=
  Certificate prog A tau B

abbrev HavocProofDerivation {P : QECParams} (prog : QStabProgram P)
    (A B : Formula P []) : Type :=
  HavocCertificate prog A B

/-- A syntactic invariant derivation: an initial-state proof plus one demonic
    one-step proof over all enabled branches. -/
structure InvariantDerivation {P : QECParams} (prog : QStabProgram P)
    (I : Formula P []) where
  init : I.denote (State.init P)
  step : HavocCertificate prog I I

namespace InvariantDerivation

/-- Reconstruct a semantic program invariant after checking the demonic Hoare
    derivation. -/
noncomputable def check {P : QECParams} {prog : QStabProgram P} {I : Formula P []}
    (D : InvariantDerivation prog I) : ProgramInvariant prog where
  holds := I.denote
  holds_init := D.init
  preservation := by
    intro a b hI hstep
    exact D.step.check.sound a b hstep hI

theorem check_sound {P : QECParams} {prog : QStabProgram P} {I : Formula P []}
    (D : InvariantDerivation prog I) (s : State P) (hrun : Run prog (.done s)) :
    I.denote s :=
  D.check.holds_at_done s hrun

theorem check_active_sound {P : QECParams} {prog : QStabProgram P} {I : Formula P []}
    (D : InvariantDerivation prog I) (s : State P)
    (hreach : MultiStep prog (.active (State.init P)) (.active s)) :
    I.denote s :=
  D.check.holds_of_reachable s hreach

end InvariantDerivation

/-- A checked branch family sufficient to establish a program invariant. -/
structure InvariantCertificate {P : QECParams} (prog : QStabProgram P)
    (I : Formula P []) where
  init : I.denote (State.init P)
  err0 : (i : Fin P.n) -> (p : Pauli) -> p ≠ Pauli.I ->
    Certificate prog I (.err0 i p) I
  errI : (i : Fin P.n) -> (p : Pauli) -> p ≠ Pauli.I -> (mf : Bool) ->
    Certificate prog I (.errI i p mf) I
  errII : (e : ErrorVec P.n) -> (mf : Bool) ->
    Certificate prog I (.errII e mf) I
  errIII : Certificate prog I .errIII I
  meas : Certificate prog I .meas I

namespace InvariantCertificate

/-- View the compatibility branch-family certificate as one demonic step proof. -/
noncomputable def toHavocCertificate {P : QECParams} {prog : QStabProgram P}
    {I : Formula P []} (cert : InvariantCertificate prog I) :
    HavocCertificate prog I I :=
  HavocCertificate.havocStep cert.err0 cert.errI cert.errII cert.errIII cert.meas

noncomputable def toInvariantDerivation {P : QECParams} {prog : QStabProgram P}
    {I : Formula P []} (cert : InvariantCertificate prog I) :
    InvariantDerivation prog I where
  init := cert.init
  step := cert.toHavocCertificate

/-- Reconstruct a semantic program invariant after checking the demonic rule. -/
noncomputable def check {P : QECParams} {prog : QStabProgram P} {I : Formula P []}
    (cert : InvariantCertificate prog I) : ProgramInvariant prog :=
  cert.toInvariantDerivation.check

theorem check_sound {P : QECParams} {prog : QStabProgram P} {I : Formula P []}
    (cert : InvariantCertificate prog I) (s : State P) (hrun : Run prog (.done s)) :
    I.denote s :=
  cert.check.holds_at_done s hrun

theorem check_active_sound {P : QECParams} {prog : QStabProgram P} {I : Formula P []}
    (cert : InvariantCertificate prog I) (s : State P)
    (hreach : MultiStep prog (.active (State.init P)) (.active s)) :
    I.denote s :=
  cert.check.holds_of_reachable s hreach

end InvariantCertificate

/-- A syntactic barrier contract generates one demonic branch-family proof. -/
noncomputable def syntacticBarrierContractToHavocCertificate {P : QECParams}
    {prog : QStabProgram P} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    HavocCertificate prog (barrierInvF beta L) (barrierInvF beta L) :=
  HavocCertificate.havocStep
    (fun i p hp => barrierInvErr0Certificate (prog := prog) contract i p hp)
    (fun i p hp mf => barrierInvErrICertificate (prog := prog) contract i p hp mf)
    (fun e mf => barrierInvErrIICertificate (prog := prog) contract e mf)
    (barrierInvErrIIICertificate (prog := prog) contract)
    (barrierInvMeasCertificate (prog := prog) contract)

/-- A syntactic barrier contract generates a full invariant derivation. -/
noncomputable def syntacticBarrierContractToInvariantDerivation {P : QECParams}
    {prog : QStabProgram P} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    InvariantDerivation prog (barrierInvF beta L) where
  init := barrierInvF_init_of_contract beta L contract.toChecked
  step := syntacticBarrierContractToHavocCertificate (prog := prog) contract

theorem syntacticBarrierContractCircuitDistance_done {P : QECParams}
    {prog : QStabProgram P} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (s : State P) (hrun : Run prog (.done s)) :
    (circuitDistanceF L).denote s := by
  intro hLogical
  have hInv := (syntacticBarrierContractToInvariantDerivation
    (prog := prog) contract).check_sound s hrun
  obtain ⟨hBound, _hBudget⟩ := hInv
  have hLogical' : L.contains s.E_tilde := by
    simpa [Formula.eval, Term.eval] using hLogical
  have hZero : beta.eval s.E_tilde = 0 := contract.logical_sound s.E_tilde hLogical'
  change L.distance <= beta.eval s.E_tilde + (P.C_budget - s.C) at hBound
  change L.distance <= P.C_budget - s.C
  rw [hZero] at hBound
  simpa using hBound

theorem syntacticBarrierContractCircuitDistance_active {P : QECParams}
    {prog : QStabProgram P} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L)
    (s : State P)
    (hreach : MultiStep prog (.active (State.init P)) (.active s)) :
    (circuitDistanceF L).denote s := by
  intro hLogical
  have hInv := (syntacticBarrierContractToInvariantDerivation
    (prog := prog) contract).check_active_sound s hreach
  obtain ⟨hBound, _hBudget⟩ := hInv
  have hLogical' : L.contains s.E_tilde := by
    simpa [Formula.eval, Term.eval] using hLogical
  have hZero : beta.eval s.E_tilde = 0 := contract.logical_sound s.E_tilde hLogical'
  change L.distance <= beta.eval s.E_tilde + (P.C_budget - s.C) at hBound
  change L.distance <= P.C_budget - s.C
  rw [hZero] at hBound
  simpa using hBound

end QHL.Source.Branch
