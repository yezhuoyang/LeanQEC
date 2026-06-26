import QStab.QHL.CodeSurface
import QStab.QHL.Verify.PureDeriv

/-!
# Convergence (totality) of the recursive Surface code's `recCall`

This file proves a reusable lemma — `recCall_total` — that the recursively
defined Surface code body, given enough fuel, evaluates `recCall (natLit d)
(natLit k)` to a *total* partial stabilizer (every qubit `q < nQubits d` resolves
to `some p`).  This is the foundational definedness fact behind the `recUnfold`
obligations of `codeLevelDefined` / `lowerDefined` in the prover.

The proof is a direct strong induction on the (odd) Surface distance:

* **base** `d < 5` (i.e. `d = 3`): `Surface.code.body` selects `baseEntry`, a
  *closed* nested-`ite` Pauli term (no `recCall`/`stabAt`).  Every such term is a
  `StabBinder.PureTerm`, hence evaluates to `some` at any fuel and environment —
  so the resulting stabilizer is total.
* **step** `d ≥ 5`: the body selects `recursiveEntry`.  Its guards and base leaves
  are all pure; the only non-pure leaves are `stabAt (recCall (d-2) K) innerQ`,
  reached only inside the geometric guard `inside` (`1 ≤ row < d-1`, `1 ≤ col <
  d-1`).  There `innerQ = (row-1)(d-2)+(col-1) < (d-2)^2 = nQubits (d-2)`, so the
  inductive hypothesis (inner `recCall` is total up to `nQubits (d-2)`) resolves
  the entry.

No `sorry`/`admit`/`native_decide`/new `axiom`/`Lean.ofReduceBool`/
`@[implemented_by]`/`unsafe`/`Formula.check`/`Formula.eval`-as-proof is used.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Surface

set_option maxRecDepth 4096

/-! ## Pure Pauli trees and their totality

`StabBinder.PureTerm` covers only `.nat`/`.bool` terms (it has no `pauliLit`
constructor).  `baseEntry` is a Pauli term: a nested `ite` whose guards are pure
`.bool` terms and whose leaves are `pauliLit`.  We capture exactly this shape
with `PurePauli` and prove it always evaluates to `some` (at any fuel/env). -/

/-- A Pauli term built only from `pauliLit` and `ite (pure-bool guard) · ·` over
pure subterms.  Such a term has no `recCall`/`stabAt`/`stabFold`, so it converges
to `some` at any fuel. -/
inductive PurePauli : {arity : Nat} → Term arity .pauli → Prop where
  | lit {arity : Nat} (p : Pauli) : PurePauli (Term.pauliLit (arity := arity) p)
  | ite {arity : Nat} {c : Term arity .bool} {a b : Term arity .pauli} :
      SFormula.PureBoolTerm c → PurePauli a → PurePauli b → PurePauli (.ite c a b)

/-- A `PurePauli` term evaluates to `some` at any fuel and environment. -/
theorem PurePauli.eval_total {arity : Nat} {x : Term arity .pauli}
    (hx : PurePauli x) (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ p, Term.eval cb fuel x rho = some p := by
  induction hx with
  | lit p => exact ⟨p, by simp [Term.eval]⟩
  | ite hc _ _ iha ihb =>
      obtain ⟨cv, hcv⟩ := SFormula.PureBoolTerm.eval_total hc cb fuel rho
      cases cv with
      | false =>
          obtain ⟨bv, hbv⟩ := ihb
          exact ⟨bv, by simp [Term.eval, hcv, hbv]⟩
      | true =>
          obtain ⟨av, hav⟩ := iha
          exact ⟨av, by simp [Term.eval, hcv, hav]⟩

/-! ## `PureTerm`/`PurePauli` closure under one-variable substitution

The keystone leaf obligations are `eqPauli`s whose *right* side is
`Term.instantiateTopNat q thenP` — the substituted lam body of a `pauliLit`-`ite`
tree.  To discharge them via `PurePauli.eval_total` we must know the *substituted*
tree is still `PurePauli`.  Since `PureTerm`/`PurePauli` never enter
`stabLam`/`stabFold`/`stabAt`/`recCall` (they have no such constructors), the
`x.weaken` in those `instantiateNatAt` clauses is never reached, so closure is
clean: substituting a pure `x` into a pure tree keeps it pure. -/

/-- A `PureTerm` (nat/bool/pauli) substituted at any cutoff with a pure nat `x`
still evaluates to `some`.  Proved directly as a `Prop` (∃) — `PureTerm` is
`Type`-valued, so a *data* closure `def` would hit the recursor codegen wall; we
only ever need eval-totality, so we prove that.  The binder cases that `weaken` `x`
never occur (`PureTerm` has no `stabLam`/`stabFold` constructor). -/
theorem pureTerm_instantiateNatAt_eval_total {arity : Nat} {ty : Ty} {cutoff : Nat}
    (hcut : cutoff ≤ arity) {x : Term arity .nat} (hx : SFormula.PureNatTerm x)
    {t : Term (arity + 1) ty} (ht : SFormula.PureTerm t)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ v, Term.eval cb fuel (Term.instantiateNatAt cutoff x hcut t) rho = some v := by
  induction ht with
  | var v =>
      rw [Term.instantiateNatAt]
      by_cases h1 : v.val < cutoff
      · rw [dif_pos h1]; simp [Term.eval]
      · rw [dif_neg h1]
        by_cases h2 : v.val = cutoff
        · rw [dif_pos h2]; exact hx.eval_total cb fuel rho
        · rw [dif_neg h2]; simp [Term.eval]
  | natLit n => rw [Term.instantiateNatAt]; simp [Term.eval]
  | boolLit b => rw [Term.instantiateNatAt]; simp [Term.eval]
  | add _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | sub _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | mul _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | div _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | mod _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | eqNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | ltNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | leNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; simp [Term.eval, ha, hb]
  | not _ iha =>
      obtain ⟨_, ha⟩ := iha
      rw [Term.instantiateNatAt]; simp [Term.eval, ha]
  | and _ _ iha ihb =>
      obtain ⟨av, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; cases av <;> simp [Term.eval, ha, hb]
  | or _ _ iha ihb =>
      obtain ⟨av, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; cases av <;> simp [Term.eval, ha, hb]
  | ite _ _ _ ihc iha ihb =>
      obtain ⟨cv, hc⟩ := ihc; obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; cases cv <;> simp [Term.eval, hc, ha, hb]

/-- `PurePauli` substituted at any cutoff with a pure nat `x` still evaluates to
`some`.  (The `pauliLit`-`ite` tree's guards are `PureTerm`, dispatched to the
above; the `pauliLit` leaves are trivially total.) -/
theorem purePauli_instantiateNatAt_eval_total {arity : Nat} {cutoff : Nat}
    (hcut : cutoff ≤ arity) {x : Term arity .nat} (hx : SFormula.PureNatTerm x)
    {t : Term (arity + 1) .pauli} (ht : PurePauli t)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ v, Term.eval cb fuel (Term.instantiateNatAt cutoff x hcut t) rho = some v := by
  induction ht with
  | lit p => rw [Term.instantiateNatAt]; simp [Term.eval]
  | ite hc _ _ iha ihb =>
      obtain ⟨cv, hcv⟩ := pureTerm_instantiateNatAt_eval_total hcut hx hc cb fuel rho
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [Term.instantiateNatAt]; cases cv <;> simp [Term.eval, hcv, ha, hb]

/-- `PurePauli` substituted at the *top* variable still evaluates to `some` — the
RHS shape of every keystone leaf obligation (`Term.instantiateTopNat q thenP`). -/
theorem purePauli_instantiateTopNat_eval_total {arity : Nat} {x : Term arity .nat}
    (hx : SFormula.PureNatTerm x) {t : Term (arity + 1) .pauli} (ht : PurePauli t)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ v, Term.eval cb fuel (Term.instantiateTopNat x t) rho = some v :=
  purePauli_instantiateNatAt_eval_total (Nat.zero_le arity) hx ht cb fuel rho

/-! ## `stabAt (stabLam (PurePauli-ite)) q` totality — the uniform leaf helper

The keystone leaf obligations' *left* side is
`stabAt (closed (stabLam (ite cond thenP elseP))) (closed q)`.  Its `Term.eval`
unfolds to `(fun qv => Term.eval (ite cond thenP elseP) (cons qv rho)) qv`, which
is `some` exactly when the lam body is `PurePauli` and `q` evaluates.  This is the
ONE call that collapses the whole `logicalX*_WF`-style `stabAt (stabLam …) q`
everywhere-`some` pattern. -/

/-- `stabAt (stabLam body) q` evaluates to `some` when the lam body is `PurePauli`
and the index `q` is pure. -/
theorem stabLam_purePauli_eval_total {arity : Nat} {body : Term (arity + 1) .pauli}
    (hbody : PurePauli body) {q : Term arity .nat} (hq : SFormula.PureNatTerm q)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ p, Term.eval cb fuel (.stabAt (.stabLam body) q) rho = some p := by
  obtain ⟨qv, hqv⟩ := hq.eval_total cb fuel rho
  obtain ⟨p, hp⟩ := hbody.eval_total cb fuel (Env.cons qv rho)
  exact ⟨p, by simp [Term.eval, hqv, hp, bind, Option.bind]⟩

/-- Generalized `stabAt (stabLam body) q` totality: the body need only evaluate to
`some` at *every* extended environment (`cons qv rho`).  This lets the keystone
`stabAtClosedIteLam` leaf feed eval-totality of a *substituted* (`codeSubstAt`) lam
body, where a literal `PurePauli` data certificate is unavailable. -/
theorem stabLam_eval_total {arity : Nat} {body : Term (arity + 1) .pauli}
    {q : Term arity .nat} (hq : SFormula.PureNatTerm q)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity)
    (hbody : ∀ qv, ∃ p, Term.eval cb fuel body (Env.cons qv rho) = some p) :
    ∃ p, Term.eval cb fuel (.stabAt (.stabLam body) q) rho = some p := by
  obtain ⟨qv, hqv⟩ := hq.eval_total cb fuel rho
  obtain ⟨p, hp⟩ := hbody qv
  exact ⟨p, by simp [Term.eval, hqv, hp, bind, Option.bind]⟩

/-! ## `lift` / `liftTopN` / `codeSubstAt` eval-totality closure

The keystone leaf obligations' lam bodies are `codeSubstAt dT kT 1 baseEntry`
(and `recursiveEntry`) — the abstract base entry with the symbolic distance/index
substituted in.  To feed `stabLam_eval_total` we need eval-totality of that
substituted body.  Since `baseEntry` is recursion-free (`PurePauli`) and `dT`/`kT`
are pure, the substituted body is still recursion-free, hence eval-total.  We prove
this directly (eval-totality, a `Prop`) by structural recursion on the purity
certificate, threading the `liftTopN` of the pure substituents. -/

/-- `lift` of a pure term is eval-total (its eval at the lifted env reduces to a
pure-term eval).  Proved by induction on the purity certificate; the `stabLam`/
`stabFold` clauses never occur. -/
theorem pureTerm_lift_eval_total {arity : Nat} {ty : Ty} (cutoff : Nat)
    {t : Term arity ty} (ht : SFormula.PureTerm t)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env (arity + 1)) :
    ∃ v, Term.eval cb fuel (Term.lift cutoff t) rho = some v := by
  induction ht generalizing cutoff with
  | var v => simp [Term.lift, Term.eval]
  | natLit n => simp [Term.lift, Term.eval]
  | boolLit b => simp [Term.lift, Term.eval]
  | add _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | sub _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | mul _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | div _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | mod _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | eqNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | ltNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | leNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      simp [Term.lift, Term.eval, ha, hb]
  | not _ iha =>
      obtain ⟨_, ha⟩ := iha cutoff
      simp [Term.lift, Term.eval, ha]
  | and _ _ iha ihb =>
      obtain ⟨av, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      cases av <;> simp [Term.lift, Term.eval, ha, hb]
  | or _ _ iha ihb =>
      obtain ⟨av, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      cases av <;> simp [Term.lift, Term.eval, ha, hb]
  | ite _ _ _ ihc iha ihb =>
      obtain ⟨cv, hc⟩ := ihc cutoff; obtain ⟨_, ha⟩ := iha cutoff; obtain ⟨_, hb⟩ := ihb cutoff
      cases cv <;> simp [Term.lift, Term.eval, hc, ha, hb]

/-- `liftTopN 1` of a pure term (= `weaken` = `lift 0`) is eval-total.  This is the
only `liftTopN` depth the keystone needs (the lam binds exactly one qubit, so
`codeSubstAt … 1 …` lifts the substituents by 1). -/
theorem pureTerm_liftTopN_one_eval_total {arity : Nat} {ty : Ty}
    {t : Term arity ty} (ht : SFormula.PureTerm t)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env (arity + 1)) :
    ∃ v, Term.eval cb fuel (QHL.CodeLang.Verify.liftTopN 1 t) rho = some v := by
  have heq : QHL.CodeLang.Verify.liftTopN 1 t = Term.lift 0 t := by
    simp [QHL.CodeLang.Verify.liftTopN, Term.weaken]
  rw [heq]; exact pureTerm_lift_eval_total 0 ht cb fuel rho

/-- `codeSubstAt dT kT 1 t` is eval-total when the abstract entry `t` is a pure
nat/bool/pauli tree and the substituents `dT`/`kT` are pure.  This is the lam-body
totality the keystone `stabAtClosedIteLam` leaf needs: the substituted base entry's
guards/leaves all evaluate.  Depth stays `1` (`PureTerm` has no binder constructor),
so the only non-trivial leaf is `liftTopN 1 dT/kT` (eval-total by the lemma above). -/
theorem pureTerm_codeSubstAt_one_eval_total {arity : Nat} {ty : Ty}
    {dT kT : Term arity .nat} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    {t : Term (1 + 2) ty} (ht : SFormula.PureTerm t)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env (arity + 1)) :
    ∃ v, Term.eval cb fuel (QHL.CodeLang.Verify.codeSubstAt dT kT 1 t) rho = some v := by
  induction ht with
  | var v =>
      rw [QHL.CodeLang.Verify.codeSubstAt]
      by_cases h1 : v.val < 1
      · rw [dif_pos h1]; simp [Term.eval]
      · rw [dif_neg h1]
        by_cases h2 : v.val = 1
        · rw [dif_pos h2]; exact pureTerm_liftTopN_one_eval_total hk cb fuel rho
        · rw [dif_neg h2]; exact pureTerm_liftTopN_one_eval_total hd cb fuel rho
  | natLit n => rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval]
  | boolLit b => rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval]
  | add _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | sub _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | mul _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | div _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | mod _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | eqNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | ltNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | leNat _ _ iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha, hb]
  | not _ iha =>
      obtain ⟨_, ha⟩ := iha
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ha]
  | and _ _ iha ihb =>
      obtain ⟨av, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; cases av <;> simp [Term.eval, ha, hb]
  | or _ _ iha ihb =>
      obtain ⟨av, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; cases av <;> simp [Term.eval, ha, hb]
  | ite _ _ _ ihc iha ihb =>
      obtain ⟨cv, hc⟩ := ihc; obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; cases cv <;> simp [Term.eval, hc, ha, hb]

/-- `codeSubstAt dT kT 1 t` of a `PurePauli` entry `t` (e.g. `baseEntry`) is
eval-total — the `pauliLit`-`ite` tree's guards are `PureTerm` (dispatched to
`pureTerm_codeSubstAt_one_eval_total`), the leaves are `pauliLit`. -/
theorem purePauli_codeSubstAt_one_eval_total {arity : Nat}
    {dT kT : Term arity .nat} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    {t : Term (1 + 2) .pauli} (ht : PurePauli t)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env (arity + 1)) :
    ∃ v, Term.eval cb fuel (QHL.CodeLang.Verify.codeSubstAt dT kT 1 t) rho = some v := by
  induction ht with
  | lit p => rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval]
  | ite hc _ _ iha ihb =>
      obtain ⟨cv, hcv⟩ := pureTerm_codeSubstAt_one_eval_total hd hk hc cb fuel rho
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb
      rw [QHL.CodeLang.Verify.codeSubstAt]; cases cv <;> simp [Term.eval, hcv, ha, hb]

/-! ## Base entry is a pure Pauli tree

`baseEntry` is built only from `ite`/`pauliLit` over pure-bool guards (the
guards use `div`, `mod`, `sub`, `mul`, `add`, `eqNat`, `ltNat`, `leNat`, `and`,
`or`) — no `recCall`/`stabAt`/`stabFold`.  So it is a `PurePauli`. -/

/-- Tactic: discharge a `SFormula.PureNatTerm`/`PureBoolTerm`/`PurePauli` goal for
a concrete `recCall`/`stabAt`-free term by repeatedly applying the structural
constructors.  Used only on the syntactically explicit base/recursive entries. -/
macro "pure_tree" : tactic =>
  `(tactic|
    (try simp only [Surface.band3, Surface.band4, Surface.le, Surface.orEqSucc,
      Surface.orEqPair, Surface.bor3, Surface.bnot, Surface.gridIdx]
     repeat'
      first
        | exact SFormula.PureNatTerm.var _
        | exact SFormula.PureNatTerm.natLit _
        | exact SFormula.PureBoolTerm.boolLit _
        | exact PurePauli.lit _
        | apply PurePauli.ite
        | apply SFormula.PureBoolTerm.eqNat
        | apply SFormula.PureBoolTerm.ltNat
        | apply SFormula.PureBoolTerm.leNat
        | apply SFormula.PureBoolTerm.not
        | apply SFormula.PureBoolTerm.and
        | apply SFormula.PureBoolTerm.or
        | apply SFormula.PureNatTerm.add
        | apply SFormula.PureNatTerm.sub
        | apply SFormula.PureNatTerm.mul
        | apply SFormula.PureNatTerm.div
        | apply SFormula.PureNatTerm.mod
        | apply SFormula.PureNatTerm.ite))

/-- `baseEntry` is a pure Pauli tree. -/
def baseEntry_purePauli : PurePauli Surface.baseEntry := by
  simp only [Surface.baseEntry, Surface.band3, Surface.orEqSucc, Surface.orEqPair]
  pure_tree

/-! ## Unfolding the code body under `Env.code d k` -/

/-- `Surface.code.body` evaluated at `Env.code d k` selects `baseEntry` when
`d < 5` and `recursiveEntry` otherwise, returning the per-qubit closure. -/
theorem body_eval_code (f d k : Nat) :
    Term.eval Surface.code.body f Surface.code.body (Env.code d k) =
      some (fun q =>
        if d < 5 then
          Term.eval Surface.code.body f Surface.baseEntry (Env.cons q (Env.code d k))
        else
          Term.eval Surface.code.body f Surface.recursiveEntry (Env.cons q (Env.code d k))) := by
  simp only [Surface.code, Surface.body, Term.eval, C.Code.d, n5, Env.code, Env.cons,
    bind, Option.bind]
  by_cases h : d < 5 <;> simp [h]

/-! ## Geometric range lemma

When the recursive entry delegates to the inner code (the `inside` guard
`1 ≤ row < d-1`, `1 ≤ col < d-1` holds, with `row = q/d`, `col = q%d`), the inner
qubit index `innerQ = (row-1)*(d-2)+(col-1)` is `< (d-2)^2 = nQubits (d-2)`. -/
theorem innerQ_lt {d row col : Nat} (hd : 2 ≤ d)
    (hrow0 : 1 ≤ row) (hrow1 : row < d - 1) (hcol0 : 1 ≤ col) (hcol1 : col < d - 1) :
    (row - 1) * (d - 2) + (col - 1) < (d - 2) * (d - 2) := by
  have hrow' : row - 1 < d - 2 := by omega
  have hcol' : col - 1 < d - 2 := by omega
  have key2 : (row - 1) * (d - 2) + (d - 2) ≤ (d - 2) * (d - 2) := by
    have hmul : (row - 1 + 1) * (d - 2) ≤ (d - 2) * (d - 2) :=
      Nat.mul_le_mul_right _ (by omega)
    calc (row - 1) * (d - 2) + (d - 2) = (row - 1 + 1) * (d - 2) := by rw [Nat.add_one_mul]
      _ ≤ (d - 2) * (d - 2) := hmul
  omega

/-! ## Totality of the recursive entry (one level), given the inner totality -/

/-- The inner-code totality hypothesis: at fuel `f'`, the inner code at distance
`d-2` and *every* index `Kv` is a stabilizer total up to `nQubits (d-2)`. -/
def InnerTotal (f' d : Nat) : Prop :=
  ∀ (Kv qv : Nat), qv < (d - 2) * (d - 2) →
    ∃ p, Surface.code.evalEntry? f' (d - 2) Kv qv = some p

/-- The exact guarded-recursive-leaf term shape (`inside`-guarded `stabAt
(recCall (d-2) K) innerQ`, with else-branch `E`), as a function of the index term
`K` and the else `E`. -/
def guardedLeaf (K : Term 3 .nat) (E : Term 3 .pauli) : Term 3 .pauli :=
  .ite
    (band4 (le (.natLit 1) (.div C.Entry.q C.Entry.d))
      (.ltNat (.div C.Entry.q C.Entry.d) (.sub C.Entry.d (.natLit 1)))
      (le (.natLit 1) (.mod C.Entry.q C.Entry.d))
      (.ltNat (.mod C.Entry.q C.Entry.d) (.sub C.Entry.d (.natLit 1))))
    (.stabAt (.recCall (.sub C.Entry.d (.natLit 2)) K)
      (.add (.mul (.sub (.div C.Entry.q C.Entry.d) (.natLit 1))
        (.sub C.Entry.d (.natLit 2)))
        (.sub (.mod C.Entry.q C.Entry.d) (.natLit 1))))
    E

/-- Structural certificate that a Pauli term is total at `cons q (code d k)`
(fuel `f'+1`) given `InnerTotal f' d`: built from pure-Pauli leaves, pure-guarded
`ite`, and the inside-guarded recursive leaf `guardedLeaf K E` (any pure `K`,
any certified else-branch `E`). -/
inductive RecOk : Term 3 .pauli → Prop where
  | pure {x : Term 3 .pauli} : PurePauli x → RecOk x
  | guarded {K : Term 3 .nat} {E : Term 3 .pauli} :
      SFormula.PureNatTerm K → RecOk E → RecOk (guardedLeaf K E)
  | ite {c : Term 3 .bool} {a b : Term 3 .pauli} :
      SFormula.PureBoolTerm c → RecOk a → RecOk b → RecOk (.ite c a b)

/-- A single guarded recursive leaf `ite inside (stabAt (recCall (d-2) K) innerQ) E`
(the shape shared by `recursiveEntry`'s interior leaf and all four
`promotedBoundaryEntry` leaves) evaluates to `some`, provided the inner code is
total up to `nQubits (d-2)` and the else-branch `E` is total. -/
theorem guardedStab_total {f' d k q : Nat} (hd : 2 ≤ d)
    {K : Term 3 .nat} (hK : SFormula.PureNatTerm K)
    {E : Term 3 .pauli}
    (hE : ∃ p, Term.eval Surface.code.body (f' + 1) E (Env.cons q (Env.code d k)) = some p)
    (hinner : InnerTotal f' d) :
    ∃ p, Term.eval Surface.code.body (f' + 1) (guardedLeaf K E)
        (Env.cons q (Env.code d k)) = some p := by
  -- Evaluate the guard, the index `K`, and bottom out the variable lookups.
  obtain ⟨Kv, hKv⟩ := SFormula.PureNatTerm.eval_total hK Surface.code.body f'
    (Env.cons q (Env.code d k))
  simp only [guardedLeaf, C.Entry.q, C.Entry.d, Surface.band4, Surface.band3, Surface.le,
    Term.eval, Env.cons, Env.code, bind, Option.bind]
  -- `C.Entry.q`/`k`/`d` are de Bruijn 0/1/2, resolving to `q`/`k`/`d`.
  by_cases hinside : (1 ≤ q / d ∧ q / d < d - 1) ∧ (1 ≤ q % d ∧ q % d < d - 1)
  · -- `inside` holds: delegate to the inner code, which is total at `innerQ`.
    obtain ⟨⟨hr0, hr1⟩, hc0, hc1⟩ := hinside
    have hrange : (q / d - 1) * (d - 2) + (q % d - 1) < (d - 2) * (d - 2) :=
      innerQ_lt hd hr0 hr1 hc0 hc1
    obtain ⟨p, hp⟩ := hinner Kv ((q / d - 1) * (d - 2) + (q % d - 1)) hrange
    refine ⟨p, ?_⟩
    -- Reduce `evalEntry?` to the matched form appearing in the goal.
    simp only [CodeFn.evalEntry?, CodeFn.evalStabilizer?, Env.code,
      bind, Option.bind] at hp
    have hKeval : Surface.code.body.eval f' K (Env.cons q (Env.cons k (Env.cons d Env.empty)))
        = some Kv := by
      simpa [C.Entry.q, C.Entry.k, C.Entry.d, Env.cons, Env.code] using hKv
    simp only [decide_eq_true_eq, hr0, hr1, hc0, hc1, if_true, hKeval]
    simpa using hp
  · -- `inside` fails: the guard evaluates to `some false`, selecting `E`.
    obtain ⟨p, hp⟩ := hE
    refine ⟨p, ?_⟩
    have hElse : Surface.code.body.eval (f' + 1) E
        (Env.cons q (Env.cons k (Env.cons d Env.empty))) = some p := by
      simpa [Env.code, Env.cons] using hp
    have hguard :
        (if decide (1 ≤ q / d) = true then
            if decide (q / d < d - 1) = true then
              if decide (1 ≤ q % d) = true then some (decide (q % d < d - 1)) else some false
            else some false
          else some false) = some false := by
      by_cases hr0 : 1 ≤ q / d <;> by_cases hr1 : q / d < d - 1 <;>
        by_cases hc0 : 1 ≤ q % d <;> by_cases hc1 : q % d < d - 1 <;>
        simp_all [decide_eq_true_eq]
    rw [hguard]
    simpa using hElse

/-- A `RecOk`-certified Pauli term is total at `cons q (code d k)` (fuel `f'+1`),
given `2 ≤ d` and `InnerTotal f' d`. -/
theorem RecOk.eval_total {x : Term 3 .pauli} (hx : RecOk x) {f' d k q : Nat}
    (hd : 2 ≤ d) (hinner : InnerTotal f' d) :
    ∃ p, Term.eval Surface.code.body (f' + 1) x (Env.cons q (Env.code d k)) = some p := by
  induction hx with
  | pure hp => exact hp.eval_total Surface.code.body (f' + 1) (Env.cons q (Env.code d k))
  | guarded hK _ ihE => exact guardedStab_total hd hK ihE hinner
  | ite hc _ _ iha ihb =>
      obtain ⟨cv, hcv⟩ := SFormula.PureBoolTerm.eval_total hc Surface.code.body (f' + 1)
        (Env.cons q (Env.code d k))
      cases cv with
      | false =>
          obtain ⟨bv, hbv⟩ := ihb
          exact ⟨bv, by simp [Term.eval, hcv, hbv]⟩
      | true =>
          obtain ⟨av, hav⟩ := iha
          exact ⟨av, by simp [Term.eval, hcv, hav]⟩

/-! ## The keystone bridge: `RecOk`-certified entry, substituted, at the keystone env

The keystone normalizer leaves bottom out at a `stabAtClosedIteLam` `FormulaDefined`
obligation whose lam body is `codeSubstAt dT kT 1 recursiveEntry` — the recursive
entry with the symbolic distance/index `dT`/`kT` substituted, opened under the
qubit binder.  Its totality (`∀ qv, ∃ p, eval … (Env.cons qv rho) = some p`) is NOT
covered by the `PurePauli` helpers (the entry contains `recCall`).  We bridge it to
`RecOk.eval_total`: substituting `dT`/`kT` (each evaluating to a concrete `dv`/`kv`
at `rho`) and opening at `qv` is the same eval as `recursiveEntry` evaluated at
`Env.cons qv (Env.code dv kv)`, so `RecOk.eval_total` (with `2 ≤ dv` and the inner
`InnerTotal`) supplies totality.  We prove the substituted analogues of
`guardedStab_total` / `RecOk.eval_total` directly (no private `eval_codeSubstAt`). -/

/-- The two substituents `liftTopN 1 dT`/`liftTopN 1 kT` evaluate, under the qubit
binder `Env.cons qv rho`, to the base values `dT.eval rho`/`kT.eval rho`.  This is
`Term.eval_weaken_top` modulo `liftTopN 1 = lift 0`. -/
theorem liftTopN_one_eval_eq {arity : Nat} {ty : Ty} (t : Term arity ty)
    (cb : Term 2 .stab) (fuel qv : Nat) (rho : Env arity) :
    Term.eval cb fuel (QHL.CodeLang.Verify.liftTopN 1 t) (Env.cons qv rho) =
      Term.eval cb fuel t rho := by
  have heq : QHL.CodeLang.Verify.liftTopN 1 t = Term.lift 0 t := by
    simp [QHL.CodeLang.Verify.liftTopN, Term.weaken]
  rw [heq]; exact QHL.CodeLang.Verify.Term.eval_weaken_top t cb fuel qv rho

/-- **Pure-term substitution eval-equality (depth 1).**  For a `PureTerm` `t : Term 3 ty`,
substituting `dT`/`kT` and opening at `qv` agrees with evaluating `t` at the keystone
env `Env.cons qv (Env.code dv kv)`.  The eval-equality analogue of
`pureTerm_codeSubstAt_one_eval_total`; the var case identifies the three de Bruijn
slots with `qv`/`kv`/`dv` via `liftTopN_one_eval_eq`. -/
theorem pureTerm_codeSubstAt_one_eval_eq {arity : Nat} {ty : Ty}
    {dT kT : Term arity .nat} {dv kv qv : Nat}
    {t : Term (1 + 2) ty} (ht : SFormula.PureTerm t)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    (hdAll : ∀ fuel', Term.eval cb fuel' dT rho = some dv)
    (hkAll : ∀ fuel', Term.eval cb fuel' kT rho = some kv) :
    Term.eval cb fuel (QHL.CodeLang.Verify.codeSubstAt dT kT 1 t) (Env.cons qv rho) =
      Term.eval cb fuel t (Env.cons qv (Env.code dv kv)) := by
  induction ht generalizing fuel with
  | @var v =>
      rcases v with ⟨vv, hvv⟩
      rw [QHL.CodeLang.Verify.codeSubstAt]
      by_cases h1 : vv < 1
      · rw [dif_pos h1]
        -- vv = 0 (the qubit slot)
        have hv0 : vv = 0 := by omega
        subst hv0
        simp only [Term.eval, Env.cons, Env.code]
      · rw [dif_neg h1]
        by_cases h2 : vv = 1
        · rw [dif_pos h2]
          subst h2
          rw [liftTopN_one_eval_eq kT cb fuel qv rho, hkAll fuel]
          simp [Term.eval, Env.cons, Env.code]
        · rw [dif_neg h2]
          have hv2 : vv = 2 := by omega
          subst hv2
          rw [liftTopN_one_eval_eq dT cb fuel qv rho, hdAll fuel]
          simp [Term.eval, Env.cons, Env.code]
  | natLit n => rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval]
  | boolLit b => rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval]
  | add _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | sub _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | mul _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | div _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | mod _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | eqNat _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | ltNat _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | leNat _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | not _ iha =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel]
  | and _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | or _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, iha fuel, ihb fuel]
  | ite _ _ _ ihc iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval, ihc fuel, iha fuel, ihb fuel]

/-- **Recursive-stab leaf substitution eval-equality.**  For pure index/distance
terms `a b c : Term 3 .nat`, the substituted `stabAt (recCall a b) c` opened at `qv`
agrees with its keystone-env evaluation.  The `recCall` reduces (at any fuel) to the
same closed inner-code evaluation on both sides, since `a`/`b`/`c` substitute to the
same values.  Proved by the pure-term eval-equality on the three arguments plus a
fuel split on the `recCall`. -/
theorem stabAtRecCall_codeSubstAt_one_eval_eq {arity : Nat} {dT kT : Term arity .nat}
    {dv kv qv : Nat} {a b c : Term (1 + 2) .nat}
    (ha : SFormula.PureTerm a) (hb : SFormula.PureTerm b) (hc : SFormula.PureTerm c)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    (hdAll : ∀ fuel', Term.eval cb fuel' dT rho = some dv)
    (hkAll : ∀ fuel', Term.eval cb fuel' kT rho = some kv) :
    Term.eval cb fuel
        (QHL.CodeLang.Verify.codeSubstAt dT kT 1 (.stabAt (.recCall a b) c)) (Env.cons qv rho) =
      Term.eval cb fuel (.stabAt (.recCall a b) c) (Env.cons qv (Env.code dv kv)) := by
  simp only [QHL.CodeLang.Verify.codeSubstAt]
  -- evaluate the inner `recCall` and the projection index `c`
  have hcEq := pureTerm_codeSubstAt_one_eval_eq hc cb fuel hdAll hkAll (qv := qv)
  cases fuel with
  | zero => simp [Term.eval, hcEq]
  | succ f =>
      have haEq := pureTerm_codeSubstAt_one_eval_eq ha cb f hdAll hkAll (qv := qv)
      have hbEq := pureTerm_codeSubstAt_one_eval_eq hb cb f hdAll hkAll (qv := qv)
      simp only [Term.eval, hcEq, haEq, hbEq]

/-! ## `recursiveEntry` is a `RecOk` tree -/

/-- A `promotedBoundaryEntry` is a `guardedLeaf` with a pure (PurePauli)
else-branch `ite outer (lit kind) (lit I)`. -/
theorem promotedBoundaryEntry_recOk {oldK : Term 3 .nat} (hK : SFormula.PureNatTerm oldK)
    {outer : Term 3 .bool} (houter : SFormula.PureBoolTerm outer) (kind : Pauli) :
    RecOk (Surface.promotedBoundaryEntry oldK outer kind) := by
  have hleaf : Surface.promotedBoundaryEntry oldK outer kind
      = guardedLeaf oldK (.ite outer (.pauliLit kind) (.pauliLit Pauli.I)) := by
    rfl
  rw [hleaf]
  exact RecOk.guarded hK (RecOk.pure (PurePauli.ite houter (PurePauli.lit _) (PurePauli.lit _)))

/-- The interior recursive leaf `ite inside (stabAt (recCall innerD interiorK)
innerQ) (lit I)` is `guardedLeaf interiorK (lit I)`. -/
theorem interiorLeaf_recOk {interiorK : Term 3 .nat} (hK : SFormula.PureNatTerm interiorK) :
    RecOk
      (.ite
        (band4 (le (.natLit 1) (.div C.Entry.q C.Entry.d))
          (.ltNat (.div C.Entry.q C.Entry.d) (.sub C.Entry.d (.natLit 1)))
          (le (.natLit 1) (.mod C.Entry.q C.Entry.d))
          (.ltNat (.mod C.Entry.q C.Entry.d) (.sub C.Entry.d (.natLit 1))))
        (.stabAt (.recCall (.sub C.Entry.d (.natLit 2)) interiorK)
          (.add (.mul (.sub (.div C.Entry.q C.Entry.d) (.natLit 1))
            (.sub C.Entry.d (.natLit 2)))
            (.sub (.mod C.Entry.q C.Entry.d) (.natLit 1))))
        (.pauliLit Pauli.I)) :=
  RecOk.guarded hK (RecOk.pure (PurePauli.lit _))

/-- `recursiveEntry` is a `RecOk` tree: its outer guards and indices are pure, its
five recursive leaves are `guardedLeaf`s, and its base leaves are pure Pauli. -/
theorem recursiveEntry_recOk : RecOk Surface.recursiveEntry := by
  unfold Surface.recursiveEntry
  refine RecOk.ite (by pure_tree) ?_ (RecOk.pure baseEntry_purePauli)
  refine RecOk.ite (by pure_tree) (interiorLeaf_recOk (by pure_tree)) ?_
  refine RecOk.ite (by pure_tree)
    (promotedBoundaryEntry_recOk (by pure_tree) (by pure_tree) _) ?_
  refine RecOk.ite (by pure_tree)
    (promotedBoundaryEntry_recOk (by pure_tree) (by pure_tree) _) ?_
  refine RecOk.ite (by pure_tree)
    (promotedBoundaryEntry_recOk (by pure_tree) (by pure_tree) _) ?_
  refine RecOk.ite (by pure_tree)
    (promotedBoundaryEntry_recOk (by pure_tree) (by pure_tree) _)
    (RecOk.pure baseEntry_purePauli)

/-- `PurePauli` substitution eval-equality (depth 1): the pauli analogue of
`pureTerm_codeSubstAt_one_eval_eq` (its guards are `PureTerm`, leaves `pauliLit`). -/
theorem purePauli_codeSubstAt_one_eval_eq {arity : Nat}
    {dT kT : Term arity .nat} {dv kv qv : Nat}
    {t : Term (1 + 2) .pauli} (ht : PurePauli t)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    (hdAll : ∀ fuel', Term.eval cb fuel' dT rho = some dv)
    (hkAll : ∀ fuel', Term.eval cb fuel' kT rho = some kv) :
    Term.eval cb fuel (QHL.CodeLang.Verify.codeSubstAt dT kT 1 t) (Env.cons qv rho) =
      Term.eval cb fuel t (Env.cons qv (Env.code dv kv)) := by
  induction ht generalizing fuel with
  | lit p => rw [QHL.CodeLang.Verify.codeSubstAt]; simp [Term.eval]
  | @ite c a b hc _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]
      have hcEq := pureTerm_codeSubstAt_one_eval_eq hc cb fuel hdAll hkAll (qv := qv)
      simp only [Term.eval, hcEq, iha fuel, ihb fuel]

/-- **The keystone bridge — eval-equality form.**  For every `RecOk`-certified entry
`x : Term 3 .pauli`, substituting the symbolic distance/index `dT`/`kT` (which evaluate
to `dv`/`kv` at the base env `rho`, at every fuel) and opening under the qubit binder at
`qv` is *the same evaluation* as evaluating the original entry at the keystone env
`Env.cons qv (Env.code dv kv)`.  Proved by induction on the `RecOk` certificate: pure
subtrees via `pureTerm_codeSubstAt_one_eval_eq`, the inside-guarded recursive leaf via
`stabAtRecCall_codeSubstAt_one_eval_eq` (its three `recCall`/projection arguments are
all pure).  This is the missing depth-1 `codeSubstAt` eval-equality for the non-pure
recursive entry, derived without the private `eval_codeSubstAt`. -/
theorem RecOk.codeSubstAt_one_eval_eq {x : Term 3 .pauli} (hx : RecOk x)
    {arity : Nat} {dT kT : Term arity .nat} {dv kv qv : Nat}
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    (hdAll : ∀ fuel', Term.eval cb fuel' dT rho = some dv)
    (hkAll : ∀ fuel', Term.eval cb fuel' kT rho = some kv) :
    Term.eval cb fuel (QHL.CodeLang.Verify.codeSubstAt dT kT 1 x) (Env.cons qv rho) =
      Term.eval cb fuel x (Env.cons qv (Env.code dv kv)) := by
  induction hx generalizing fuel with
  | pure hp => exact purePauli_codeSubstAt_one_eval_eq hp cb fuel hdAll hkAll
  | @guarded K E hK hE ihE =>
      -- `guardedLeaf K E = ite (pure band4) (stabAt (recCall (sub d 2) K) innerQ) E`.
      simp only [guardedLeaf]
      rw [QHL.CodeLang.Verify.codeSubstAt]
      -- the guard (pure), the recursive stab leaf, and the else `E`.
      have hgEq := pureTerm_codeSubstAt_one_eval_eq
        (t := band4 (le (.natLit 1) (.div C.Entry.q C.Entry.d))
          (.ltNat (.div C.Entry.q C.Entry.d) (.sub C.Entry.d (.natLit 1)))
          (le (.natLit 1) (.mod C.Entry.q C.Entry.d))
          (.ltNat (.mod C.Entry.q C.Entry.d) (.sub C.Entry.d (.natLit 1))))
        (by unfold band4 band3 le C.Entry.q C.Entry.d; pure_tree) cb fuel hdAll hkAll (qv := qv)
      have hstabEq := stabAtRecCall_codeSubstAt_one_eval_eq
        (a := .sub C.Entry.d (.natLit 2)) (b := K)
        (c := .add (.mul (.sub (.div C.Entry.q C.Entry.d) (.natLit 1))
          (.sub C.Entry.d (.natLit 2))) (.sub (.mod C.Entry.q C.Entry.d) (.natLit 1)))
        (by unfold C.Entry.d; pure_tree) hK (by unfold C.Entry.q C.Entry.d; pure_tree)
        cb fuel hdAll hkAll (qv := qv)
      simp only [Term.eval, hgEq, hstabEq, ihE fuel]
  | @ite c a b hc _ _ iha ihb =>
      rw [QHL.CodeLang.Verify.codeSubstAt]
      have hcEq := pureTerm_codeSubstAt_one_eval_eq hc cb fuel hdAll hkAll (qv := qv)
      simp only [Term.eval, hcEq, iha fuel, ihb fuel]

/-- **The keystone lam-body totality.**  The recursive-entry lam body
`codeSubstAt dT kT 1 recursiveEntry`, opened under the qubit binder, is eval-total at
the keystone env `Env.cons qv rho`, provided `dT`/`kT` evaluate to `dv`/`kv` (at every
fuel), `2 ≤ dv`, and the inner code converges (`InnerTotal (fuel-1) dv`).  This is the
`hbody` premise of `formulaDefined_stabAtClosedIteLam` for the *recursive* peels (the
non-`PurePauli` lam body): the eval-equality bridge identifies it with
`recursiveEntry` at `Env.cons qv (Env.code dv kv)`, where `recursiveEntry_recOk.eval_total`
finishes. -/
theorem recPeelLamBody_eval_total {arity : Nat} {dT kT : Term arity .nat} {dv kv : Nat}
    {rho : Env arity} (hd : 2 ≤ dv) {f' : Nat}
    (hdAll : ∀ fuel', Term.eval Surface.code.body fuel' dT rho = some dv)
    (hkAll : ∀ fuel', Term.eval Surface.code.body fuel' kT rho = some kv)
    (hinner : InnerTotal f' dv) (qv : Nat) :
    ∃ p, Term.eval Surface.code.body (f' + 1)
        (QHL.CodeLang.Verify.codeSubstAt dT kT 1 Surface.recursiveEntry)
        (Env.cons qv rho) = some p := by
  rw [recursiveEntry_recOk.codeSubstAt_one_eval_eq Surface.code.body (f' + 1) hdAll hkAll
    (qv := qv)]
  exact recursiveEntry_recOk.eval_total (k := kv) (q := qv) hd hinner

/-! ## Main convergence induction -/

/-- **Core convergence (by recursion depth).**  For every odd Surface distance
`d = 2m+3` and index `k`, with fuel `f ≥ m+1`, the code stabilizer entry
`evalEntry? f d k q` is defined for every qubit `q < nQubits d = d*d`. -/
theorem codeEntry_total :
    ∀ (m k f : Nat), m + 1 ≤ f →
      ∀ q, q < (2 * m + 3) * (2 * m + 3) →
        ∃ p, Surface.code.evalEntry? f (2 * m + 3) k q = some p := by
  intro m
  induction m with
  | zero =>
      -- d = 3 < 5: base entry, always total (pure Pauli tree).
      intro k f hf q hq
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp only [CodeFn.evalEntry?, CodeFn.evalStabilizer?]
      rw [body_eval_code]
      simp only [bind, Option.bind]
      have h3 : (2 * 0 + 3) < 5 := by omega
      simp only [h3, if_true]
      exact baseEntry_purePauli.eval_total Surface.code.body (f' + 1)
        (Env.cons q (Env.code (2 * 0 + 3) k))
  | succ n ih =>
      -- d = 2(n+1)+3 = 2n+5 ≥ 5: recursive entry; inner code at index n is the IH.
      intro k f hf q hq
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hf' : n + 1 ≤ f' := by omega
      simp only [CodeFn.evalEntry?, CodeFn.evalStabilizer?]
      rw [body_eval_code]
      simp only [bind, Option.bind]
      have hge5 : ¬ (2 * (n + 1) + 3) < 5 := by omega
      simp only [hge5, if_false]
      -- Inner totality at distance `(2n+5)-2 = 2n+3`, fuel `f'`.
      have hinner : InnerTotal f' (2 * (n + 1) + 3) := by
        intro Kv qv hqv
        have hd2 : (2 * (n + 1) + 3) - 2 = 2 * n + 3 := by omega
        rw [hd2] at hqv ⊢
        exact ih Kv f' hf' qv hqv
      have hd : 2 ≤ 2 * (n + 1) + 3 := by omega
      exact recursiveEntry_recOk.eval_total hd hinner

/-! ## The reusable `recCall` convergence lemma

This is the definedness fact behind the `recUnfold` obligations: at an odd Surface
distance `d = 2m+3`, with sufficient fuel, `recCall (natLit d) (natLit k)`
converges to a stabilizer total up to `nQubits d = d*d`. -/

/-- **`recCall` convergence at odd Surface distances (literal arguments).**

For `d = 2m+3` and any index `k`, with fuel `≥ m+2` (so the body evaluation at
fuel `fuel-1 ≥ m+1` covers the recursion depth), `recCall (natLit d) (natLit k)`
evaluates to a partial stabilizer `sa` total up to `nQubits d = d*d`. -/
theorem recCall_total (m k fuel : Nat) (hfuel : m + 2 ≤ fuel) {arity : Nat}
    (rho : Env arity) :
    ∃ sa, Term.eval Surface.code.body fuel
        (.recCall (.natLit (2 * m + 3)) (.natLit k)) rho = some sa ∧
      ∀ q, q < (2 * m + 3) * (2 * m + 3) → ∃ p, sa q = some p := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  have hf' : m + 1 ≤ f' := by omega
  -- `recCall@(f'+1)` reduces to the inner-code stabilizer at fuel `f'`.
  rw [QHL.CodeLang.Verify.CodeEvalHelpers.eval_recCall_natLit Surface.code f' (2 * m + 3) k rho]
  -- The stabilizer is `eval cb f' cb (code d k) = some clo` (`body_eval_code`).
  have hstab : Surface.code.evalStabilizer? f' (2 * m + 3) k
      = Term.eval Surface.code.body f' Surface.code.body (Env.code (2 * m + 3) k) := rfl
  rw [hstab, body_eval_code]
  refine ⟨_, rfl, ?_⟩
  intro q hq
  -- Entry-wise totality is exactly `codeEntry_total` (unfolded through the closure).
  obtain ⟨p, hp⟩ := codeEntry_total m k f' hf' q hq
  refine ⟨p, ?_⟩
  simpa [CodeFn.evalEntry?, CodeFn.evalStabilizer?, body_eval_code, bind, Option.bind] using hp

/-- **`recCall` convergence with a literal distance and a SYMBOLIC pure index.**

This is the form the `recUnfold` obligations actually need: the recursion-call
arguments are `dT = .natLit (2m+3)` (the literal Surface distance) and an
arbitrary *pure* index term `kT` (e.g. a bound row/column variable) evaluated in
an arbitrary environment `rho`.  Convergence is independent of `kT`'s value
because `codeEntry_total` holds for *every* index. -/
theorem recCall_total_symbolicK (m fuel : Nat) (hfuel : m + 2 ≤ fuel) {arity : Nat}
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity) :
    ∃ sa, Term.eval Surface.code.body fuel
        (.recCall (.natLit (2 * m + 3)) kT) rho = some sa ∧
      ∀ q, q < (2 * m + 3) * (2 * m + 3) → ∃ p, sa q = some p := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  have hf' : m + 1 ≤ f' := by omega
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body f' rho
  have hd : Term.eval Surface.code.body f' (.natLit (2 * m + 3)) rho = some (2 * m + 3) := by
    simp [Term.eval]
  rw [QHL.CodeLang.Verify.CodeEvalHelpers.eval_recCall_succ hd hkv, body_eval_code]
  refine ⟨_, rfl, ?_⟩
  intro q hq
  obtain ⟨p, hp⟩ := codeEntry_total m kv f' hf' q hq
  refine ⟨p, ?_⟩
  simpa [CodeFn.evalEntry?, CodeFn.evalStabilizer?, body_eval_code, bind, Option.bind] using hp

/-- **`recCall` convergence with a SYMBOLIC pure distance and a SYMBOLIC pure index.**

The fully-symbolic form the `recUnfold` obligations of the *symbolic-distance* row
selects need: both the distance term `dT` and the index term `kT` are arbitrary
pure terms (e.g. `DistAtA.dT` and a bound row variable), with `dT` evaluating to the
odd Surface distance `2m+3` at every fuel (the `DistAtA.evalsTo` fact).  Convergence
is exactly `recCall_total_symbolicK` transported across `dT.eval = some (2m+3)`. -/
theorem recCall_total_symbolicDK (m fuel : Nat) (hfuel : m + 2 ≤ fuel) {arity : Nat}
    {dT kT : Term arity .nat} (rho : Env arity)
    (hdAll : ∀ fuel', Term.eval Surface.code.body fuel' dT rho = some (2 * m + 3))
    (hk : SFormula.PureNatTerm kT) :
    ∃ sa, Term.eval Surface.code.body fuel
        (.recCall dT kT) rho = some sa ∧
      ∀ q, q < (2 * m + 3) * (2 * m + 3) → ∃ p, sa q = some p := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  have hf' : m + 1 ≤ f' := by omega
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body f' rho
  rw [QHL.CodeLang.Verify.CodeEvalHelpers.eval_recCall_succ (hdAll f') hkv, body_eval_code]
  refine ⟨_, rfl, ?_⟩
  intro q hq
  obtain ⟨p, hp⟩ := codeEntry_total m kv f' hf' q hq
  refine ⟨p, ?_⟩
  simpa [CodeFn.evalEntry?, CodeFn.evalStabilizer?, body_eval_code, bind, Option.bind] using hp

/-- The fuel bound `m + 2` is met by `bridgeProofFuel D = D.distance + 2 = 2m+5`
and by the code-level fuel `D.distance + 2 = 2m+5`, with room to spare. -/
theorem recCall_total_at_bridgeFuel (D : OddSurfaceDistance) (k : Nat) {arity : Nat}
    (rho : Env arity) :
    ∃ sa, Term.eval Surface.code.body (D.distance + 2)
        (.recCall (.natLit D.distance) (.natLit k)) rho = some sa ∧
      ∀ q, q < Surface.nQubits D.distance → ∃ p, sa q = some p := by
  have hdist : D.distance = 2 * D.index + 3 := rfl
  rw [hdist, show Surface.nQubits (2 * D.index + 3) = (2 * D.index + 3) * (2 * D.index + 3)
      from rfl]
  exact recCall_total D.index k (2 * D.index + 3 + 2) (by omega) rho

/-! ## Axiom audit of the uniform `PurePauli` eval-totality optimization

All the new uniform helpers (the `PurePauli`/`PureTerm` eval-totality closures
under `instantiateNatAt`/`lift`/`liftTopN`/`codeSubstAt`, plus the
`stabLam`-totality helpers) carry no `sorryAx`/new axioms — they are the
sorry-free, reusable leaf-eval interface that collapses the keystone leaf-eval
cost. -/
#print axioms PurePauli.eval_total
#print axioms purePauli_instantiateTopNat_eval_total
#print axioms stabLam_purePauli_eval_total
#print axioms stabLam_eval_total
#print axioms pureTerm_lift_eval_total
#print axioms pureTerm_codeSubstAt_one_eval_total
#print axioms purePauli_codeSubstAt_one_eval_total

end QHL.CodeLang.Surface.Verify
