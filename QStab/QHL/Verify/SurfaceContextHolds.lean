import QStab.QHL.CodeStabBinder
import QStab.QHL.Verify.PureDeriv

/-!
# External eval-under-weakening lemmas + `ContextHolds` discharger

This file re-proves, **publicly and from public ingredients only**, the
eval-under-weakening collapse that the frozen `CodeStabBinder.lean` keeps
`private` (`STerm.eval_lift_of_env`, `SFormula.eval_lift_of_env`,
`eval_lift_of_envLifted`).  Those private lemmas are exactly what is needed to
discharge the `ContextHolds` obligation that appears at the
`SFormula.Deriv.allNatLtIntro` / `allNatLtIntroBounded` nodes of
`SFormula.Deriv.DefinedObligations`, but `private` means they cannot be reached
from another file.

We therefore re-derive the whole chain over a **public** insert-one-binder
relation `LiftedEnv` (a structural copy of the kernel's `EnvLifted`), bottoming
out at the public `Term.eval` clauses:

* `Term.eval_lift_of_lifted`   (full structural, arbitrary cutoff)
* `STerm.eval_lift_of_lifted`  (uses the `Term` lemma at the `.closed` leaf)
* `SFormula.eval_lift_of_lifted` (uses the `STerm` lemma)

and then specialise to the **top-weaken** (`cutoff = 0`, `Env.cons x rho`)
corollaries that `ContextHolds` actually consumes:

* `sterm_eval_weaken_top`
* `sformula_eval_weaken_top`

Finally we assemble the `ContextHolds` dischargers for the universal-intro nodes:

* `contextHolds_weaken_cons`         (plain `allNatLtIntro`)
* `contextHolds_boundNatLt_cons`     (bounded `allNatLtIntroBounded`)

No new axioms, no `native_decide`, no `sorry`.
-/

namespace QHL.CodeLang.StabBinder

open QHL.CodeLang

/-! ## A public insert-one-binder relation -/

/-- `rho'` is `rho` with one fresh natural variable inserted at de Bruijn
    position `cutoff`.  Public structural copy of the kernel's `private`
    `EnvLifted` (CodeStabBinder.lean / PureDeriv.lean). -/
def LiftedEnv {arity : Nat} (cutoff : Nat)
    (rho : Env arity) (rho' : Env (arity + 1)) : Prop :=
  (forall v : Fin arity, v.val < cutoff ->
      rho' ⟨v.val, Nat.lt_trans v.isLt (Nat.lt_succ_self arity)⟩ = rho v) /\
  (forall v : Fin arity, cutoff <= v.val ->
      rho' ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ = rho v)

/-- Pushing one more binder over a `LiftedEnv` keeps the relation, with the
    cutoff and both environments extended by the same fresh value. -/
theorem LiftedEnv.underBinder {arity cutoff : Nat}
    {rho : Env arity} {rho' : Env (arity + 1)}
    (h : LiftedEnv cutoff rho rho') (x : Nat) :
    LiftedEnv (cutoff + 1) (Env.cons x rho) (Env.cons x rho') := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · cases v using Fin.cases with
    | zero => rfl
    | succ v =>
        have hv' : v.val < cutoff := Nat.lt_of_succ_lt_succ hv
        simp [Env.cons]
        exact h.1 v hv'
  · cases v using Fin.cases with
    | zero => simp at hv
    | succ v =>
        have hv' : cutoff <= v.val := Nat.le_of_succ_le_succ hv
        simp [Env.cons]
        exact h.2 v hv'

/-- The base case: a fresh top binder gives `LiftedEnv 0 rho (Env.cons x rho)`. -/
theorem LiftedEnv.top {arity : Nat} (rho : Env arity) (x : Nat) :
    LiftedEnv 0 rho (Env.cons x rho) := by
  refine ⟨fun v hv => ?_, fun v _ => ?_⟩
  · omega
  · simp [Env.cons]

/-! ## Term-level eval-under-weakening (arbitrary cutoff)

This is the kernel's `private eval_lift_of_envLifted` (PureDeriv.lean) re-derived
over our public `LiftedEnv`, using only the public `Term.eval`/`Term.lift`
clauses. -/

theorem Term.eval_lift_of_lifted {arity cutoff : Nat} {ty : Ty}
    (t : Term arity ty) (cb : Term 2 .stab) (fuel : Nat)
    {rho : Env arity} {rho' : Env (arity + 1)} (h : LiftedEnv cutoff rho rho') :
    Term.eval cb fuel (t.lift cutoff) rho' = Term.eval cb fuel t rho := by
  induction t generalizing cutoff fuel with
  | var v =>
      unfold Term.lift Term.weakenVar
      by_cases hlt : v.val < cutoff
      · simp [Term.eval, hlt, h.1 v hlt]
      · have hge : cutoff <= v.val := by omega
        simp [Term.eval, hlt, h.2 v hge]
  | natLit _ => simp [Term.lift, Term.eval]
  | boolLit _ => simp [Term.lift, Term.eval]
  | pauliLit _ => simp [Term.lift, Term.eval]
  | add a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | sub a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | mul a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | div a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | mod a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | eqNat a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | ltNat a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | leNat a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | not a iha => simp [Term.lift, Term.eval, iha fuel h]
  | and a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | or a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | ite c t e ihc iht ihe => simp [Term.lift, Term.eval, ihc fuel h, iht fuel h, ihe fuel h]
  | pauliMul a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | anticommutes a b iha ihb => simp [Term.lift, Term.eval, iha fuel h, ihb fuel h]
  | stabLam entry ih =>
      simp only [Term.lift, Term.eval]
      congr 1
      funext q
      exact ih fuel (h.underBinder q)
  | stabAt s q ihs ihq => simp [Term.lift, Term.eval, ihs fuel h, ihq fuel h]
  | stabFold n body ihn ihbody =>
      simp only [Term.lift, Term.eval, ihn fuel h]
      cases hn : Term.eval cb fuel n rho with
      | none => simp
      | some nv =>
          simp only [bind, Option.bind]
          have hbodyEq :
              (fun i =>
                match Term.eval cb fuel (Term.lift (cutoff + 1) body) (Env.cons i rho') with
                | some row => row
                | none => fun _ => none) =
              (fun i =>
                match Term.eval cb fuel body (Env.cons i rho) with
                | some row => row
                | none => fun _ => none) := by
            funext i
            rw [ihbody fuel (h.underBinder i)]
          exact congrArg (fun f => some (partialStabilizerFold nv f)) hbodyEq
  | recCall d k ihd ihk =>
      cases fuel with
      | zero => simp [Term.lift, Term.eval]
      | succ f => simp [Term.lift, Term.eval, ihd f h, ihk f h]

/-! ## Term-level eval-under-substitution (`instantiateNatAt`, arbitrary cutoff)

The recursive normalizer peels bottom out at a `stabAtClosedIteLam` node whose RHS
is `Term.instantiateTopNat qT thenP` — the substituted lam body opened at the qubit
term `qT`.  Discharging the `FormulaDefined` obligation needs the eval-under-
substitution bridge: evaluating `instantiateNatAt cutoff x t` agrees with evaluating
`t` in the environment `rho'` obtained by inserting `x`'s value at `cutoff`.

This re-derives, **publicly and from public ingredients only**, the frozen
`private Term.eval_instantiateNatAt` (CodeStabBinder.lean ~1003).  It is a full
structural recursion (NOT restricted to literal `x`): the binder cases
(`stabLam`/`stabFold`/`recCall`) recurse under the binder via `SubstedEnv.underBinder`,
weakening the substituent `x` over the fresh binder via `Term.eval_lift_of_lifted`. -/

/-- `rho'` is `rho` with the value `xv` inserted at de Bruijn position `cutoff`.
Public structural copy of the kernel's `private` `EnvInserted`. -/
def SubstedEnv {arity : Nat} (cutoff xv : Nat)
    (rho : Env arity) (rho' : Env (arity + 1)) (hcut : cutoff <= arity) : Prop :=
  LiftedEnv cutoff rho rho' ∧ rho' ⟨cutoff, Nat.lt_succ_of_le hcut⟩ = xv

/-- A fresh top binder carrying value `xv` gives `SubstedEnv 0 xv rho (cons xv rho)`. -/
theorem SubstedEnv.top {arity : Nat} (rho : Env arity) (xv : Nat) :
    SubstedEnv 0 xv rho (Env.cons xv rho) (Nat.zero_le arity) :=
  ⟨LiftedEnv.top rho xv, rfl⟩

/-- Pushing one more binder over a `SubstedEnv` keeps the relation. -/
theorem SubstedEnv.underBinder {arity cutoff xv : Nat}
    {rho : Env arity} {rho' : Env (arity + 1)} {hcut : cutoff <= arity}
    (h : SubstedEnv cutoff xv rho rho' hcut) (q : Nat) :
    SubstedEnv (cutoff + 1) xv (Env.cons q rho) (Env.cons q rho') (by omega) :=
  ⟨LiftedEnv.underBinder h.1 q, by simpa [Env.cons] using h.2⟩

/-- **Eval-under-substitution bridge.**  Substituting `x` (a term whose value is `xv`
at *every* fuel) at de Bruijn `cutoff`, then evaluating, agrees with evaluating in the
inserted environment `rho'`.  Public re-derivation of the frozen private lemma. -/
theorem Term.eval_instantiateNatAt {arity cutoff : Nat} {ty : Ty}
    (t : Term (arity + 1) ty) {x : Term arity .nat} (hcut : cutoff <= arity)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    {rho' : Env (arity + 1)} {xv : Nat}
    (hxAll : ∀ fuel', Term.eval cb fuel' x rho = some xv)
    (hins : SubstedEnv cutoff xv rho rho' hcut) :
    Term.eval cb fuel (Term.instantiateNatAt cutoff x hcut t) rho =
      Term.eval cb fuel t rho' :=
  match t with
  | .var v => by
      unfold Term.instantiateNatAt
      by_cases hlt : v.val < cutoff
      · simp [hlt, Term.eval]
        exact (hins.1.1 ⟨v.val, by omega⟩ hlt).symm
      · by_cases heq : v.val = cutoff
        · simp [hlt, heq, Term.eval, hxAll fuel]
          have hv : v = ⟨cutoff, Nat.lt_succ_of_le hcut⟩ := Fin.ext heq
          simpa [hv] using hins.2.symm
        · have hgt : cutoff < v.val := by omega
          simp [hlt, heq, Term.eval]
          let pred : Fin arity := ⟨v.val - 1, by omega⟩
          have hshift := hins.1.2 pred (by dsimp [pred]; omega)
          have hidx : (⟨pred.val + 1, Nat.succ_lt_succ pred.isLt⟩ : Fin (arity + 1)) = v := by
            apply Fin.ext; dsimp [pred]; omega
          simpa [pred, hidx] using hshift.symm
  | .natLit _ => by simp [Term.instantiateNatAt, Term.eval]
  | .boolLit _ => by simp [Term.instantiateNatAt, Term.eval]
  | .pauliLit _ => by simp [Term.instantiateNatAt, Term.eval]
  | .add a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .sub a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .mul a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .div a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .mod a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .eqNat a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .ltNat a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .leNat a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .not a => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins]
  | .and a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .or a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .ite c t e => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt c hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt t hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt e hcut cb fuel hxAll hins]
  | .pauliMul a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .anticommutes a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt b hcut cb fuel hxAll hins]
  | .stabLam entry => by
      simp only [Term.instantiateNatAt, Term.eval]
      congr 1
      funext q
      have hxweak : ∀ fuel', Term.eval cb fuel' x.weaken (Env.cons q rho) = some xv := by
        intro fuel'
        simpa [Term.weaken] using
          (Term.eval_lift_of_lifted x cb fuel' (LiftedEnv.top rho q)).trans (hxAll fuel')
      exact Term.eval_instantiateNatAt entry (by omega) cb fuel hxweak
        (SubstedEnv.underBinder hins q)
  | .stabAt s q => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt s hcut cb fuel hxAll hins,
        Term.eval_instantiateNatAt q hcut cb fuel hxAll hins]
  | .stabFold n body => by
      simp only [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt n hcut cb fuel hxAll hins]
      cases hn : Term.eval cb fuel n rho' with
      | none => simp
      | some nv =>
          simp only [bind, Option.bind]
          have hbodyEq :
              (fun i =>
                match Term.eval cb fuel
                  (Term.instantiateNatAt (cutoff + 1) x.weaken (by omega) body) (Env.cons i rho) with
                | some row => row
                | none => fun _ => none) =
              (fun i =>
                match Term.eval cb fuel body (Env.cons i rho') with
                | some row => row
                | none => fun _ => none) := by
            funext i
            have hxweak : ∀ fuel', Term.eval cb fuel' x.weaken (Env.cons i rho) = some xv := by
              intro fuel'
              simpa [Term.weaken] using
                (Term.eval_lift_of_lifted x cb fuel' (LiftedEnv.top rho i)).trans (hxAll fuel')
            rw [Term.eval_instantiateNatAt body (by omega) cb fuel hxweak
              (SubstedEnv.underBinder hins i)]
          exact congrArg (fun f => some (partialStabilizerFold nv f)) hbodyEq
  | .recCall d k => by
      cases fuel with
      | zero => simp [Term.instantiateNatAt, Term.eval]
      | succ f =>
          simp [Term.instantiateNatAt, Term.eval,
            Term.eval_instantiateNatAt d hcut cb f hxAll hins,
            Term.eval_instantiateNatAt k hcut cb f hxAll hins]
  termination_by Term.sizeOfTerm t
  decreasing_by
    all_goals
      simp_wf
      simp [Term.sizeOfTerm]
      try omega

/-- **Top-substitution eval bridge.**  Evaluating `instantiateTopNat x t` at `rho`
agrees with evaluating `t` at `Env.cons xv rho`, given `x` evaluates to `xv` at every
fuel.  The shape the recursive peels' `stabAtClosedIteLam` RHS obligation needs. -/
theorem Term.eval_instantiateTopNat {arity : Nat} {ty : Ty}
    (t : Term (arity + 1) ty) {x : Term arity .nat}
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity} {xv : Nat}
    (hxAll : ∀ fuel', Term.eval cb fuel' x rho = some xv) :
    Term.eval cb fuel (Term.instantiateTopNat x t) rho =
      Term.eval cb fuel t (Env.cons xv rho) :=
  Term.eval_instantiateNatAt t (Nat.zero_le arity) cb fuel hxAll (SubstedEnv.top rho xv)

/-! ## STerm-level eval-under-weakening (arbitrary cutoff)

Re-derivation of the frozen `private STerm.eval_lift_of_env`
(CodeStabBinder.lean ~1411) over our public `LiftedEnv`.  The `.closed` leaf
appeals to `Term.eval_lift_of_lifted`; the binder cases (`stabLam`, `stabFold`,
`applyNat`) recurse under the binder via `LiftedEnv.underBinder`. -/

theorem STerm.eval_lift_of_lifted {arity cutoff : Nat} {ty : Ty}
    (t : STerm arity ty) {rho : Env arity} {rho' : Env (arity + 1)}
    (h : LiftedEnv cutoff rho rho') (codeBody : Term 2 .stab) (fuel : Nat)
    (E : PartialStabilizer) :
    STerm.eval codeBody fuel (t.lift cutoff) rho' E =
      STerm.eval codeBody fuel t rho E := by
  induction t generalizing cutoff fuel with
  | closed t =>
      simp [STerm.lift, STerm.eval, Term.eval_lift_of_lifted t codeBody fuel h]
  | boundStab =>
      simp [STerm.lift, STerm.eval]
  | ite c t e ihc iht ihe =>
      simp [STerm.lift, STerm.eval, ihc h fuel, iht h fuel, ihe h fuel]
  | pauliMul a b iha ihb =>
      simp [STerm.lift, STerm.eval, iha h fuel, ihb h fuel]
  | anticommutes a b iha ihb =>
      simp [STerm.lift, STerm.eval, iha h fuel, ihb h fuel]
  | ltNat a b iha ihb =>
      simp [STerm.lift, STerm.eval, iha h fuel, ihb h fuel]
  | stabLam entry ih =>
      simp [STerm.lift, STerm.eval]
      funext q
      exact ih (h.underBinder q) fuel
  | stabAt s q ihs ihq =>
      simp [STerm.lift, STerm.eval, ihs h fuel, ihq h fuel]
  | stabFold n body ihn ihbody =>
      simp [STerm.lift, STerm.eval, ihn h fuel]
      cases hn : STerm.eval codeBody fuel n rho E with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i q
          have hbody := ihbody (h.underBinder i) fuel
          rw [hbody]
  | applyNat witness body ihw ihbody =>
      simp [STerm.lift, STerm.eval, ihw h fuel]
      cases hw : STerm.eval codeBody fuel witness rho E with
      | none =>
          simp
      | some wv =>
          simp
          exact ihbody (h.underBinder wv) fuel

/-! ## SFormula-level eval-under-weakening (arbitrary cutoff)

Re-derivation of the frozen `private SFormula.eval_lift_of_env`
(CodeStabBinder.lean ~1547) over our public `LiftedEnv`.  Leaves appeal to
`STerm.eval_lift_of_lifted`; the quantifier/binder cases (`applyNat`,
`allNatLt`, `existsNatLt`) recurse under the binder via `LiftedEnv.underBinder`. -/

theorem SFormula.eval_lift_of_lifted {arity cutoff : Nat}
    (A : SFormula arity) {rho : Env arity} {rho' : Env (arity + 1)}
    (h : LiftedEnv cutoff rho rho') (codeBody : Term 2 .stab) (fuel : Nat)
    (E : PartialStabilizer) :
    SFormula.eval codeBody fuel (A.lift cutoff) rho' E =
      SFormula.eval codeBody fuel A rho E := by
  induction A generalizing cutoff fuel with
  | top =>
      simp [SFormula.lift, SFormula.eval]
  | bot =>
      simp [SFormula.lift, SFormula.eval]
  | eqNat a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted a h codeBody fuel E,
        STerm.eval_lift_of_lifted b h codeBody fuel E]
  | eqBool a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted a h codeBody fuel E,
        STerm.eval_lift_of_lifted b h codeBody fuel E]
  | eqPauli a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted a h codeBody fuel E,
        STerm.eval_lift_of_lifted b h codeBody fuel E]
  | eqStabUpTo n a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted n h codeBody fuel E,
        STerm.eval_lift_of_lifted a h codeBody fuel E,
        STerm.eval_lift_of_lifted b h codeBody fuel E]
  | commutesUpTo n a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted n h codeBody fuel E,
        STerm.eval_lift_of_lifted a h codeBody fuel E,
        STerm.eval_lift_of_lifted b h codeBody fuel E]
  | weightLe n a w =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted n h codeBody fuel E,
        STerm.eval_lift_of_lifted a h codeBody fuel E,
        STerm.eval_lift_of_lifted w h codeBody fuel E]
  | and A B ihA ihB =>
      simp [SFormula.lift, SFormula.eval, ihA h fuel, ihB h fuel]
  | or A B ihA ihB =>
      simp [SFormula.lift, SFormula.eval, ihA h fuel, ihB h fuel]
  | not A ih =>
      simp [SFormula.lift, SFormula.eval, ih h fuel]
  | imp A B ihA ihB =>
      simp [SFormula.lift, SFormula.eval, ihA h fuel, ihB h fuel]
  | applyNat witness A ih =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted witness h codeBody fuel E]
      cases hw : STerm.eval codeBody fuel witness rho E with
      | none => simp
      | some wv =>
          simp
          exact ih (h.underBinder wv) fuel
  | allNatLt n A ih =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted n h codeBody fuel E]
      cases hn : STerm.eval codeBody fuel n rho E with
      | none => simp
      | some nv =>
          simp
          congr
          funext x
          exact ih (h.underBinder x) fuel
  | existsNatLt n A ih =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_lifted n h codeBody fuel E]
      cases hn : STerm.eval codeBody fuel n rho E with
      | none => simp
      | some nv =>
          simp
          congr
          funext x
          exact ih (h.underBinder x) fuel

/-! ## Top-weaken corollaries (cutoff = 0, `Env.cons x rho`)

These are the shapes `ContextHolds` consumes: `A.weaken = A.lift 0`, evaluated
at `Env.cons x rho`, agrees with `A` evaluated at `rho`. -/

theorem sterm_eval_weaken_top {arity : Nat} {ty : Ty}
    (codeBody : Term 2 .stab) (fuel : Nat) (t : STerm arity ty)
    (rho : Env arity) (E : PartialStabilizer) (x : Nat) :
    STerm.eval codeBody fuel t.weaken (Env.cons x rho) E =
      STerm.eval codeBody fuel t rho E := by
  simpa [STerm.weaken] using
    STerm.eval_lift_of_lifted t (LiftedEnv.top rho x) codeBody fuel E

theorem sformula_eval_weaken_top {arity : Nat}
    (codeBody : Term 2 .stab) (fuel : Nat) (A : SFormula arity)
    (rho : Env arity) (E : PartialStabilizer) (x : Nat) :
    SFormula.eval codeBody fuel A.weaken (Env.cons x rho) E =
      SFormula.eval codeBody fuel A rho E := by
  simpa [SFormula.weaken] using
    SFormula.eval_lift_of_lifted A (LiftedEnv.top rho x) codeBody fuel E

/-! ## `boundNatLt` head evaluates `true` inside the bounded binder

`SFormula.boundNatLt n` is `witnessLt boundNat n.weaken`, i.e.
`eqBool (ltNat boundNat n.weaken) (SC.b true)`.  At `Env.cons x rho`,
`boundNat` evaluates to the freshly bound `x` and `n.weaken` evaluates to the
old value of `n` at `rho` (by `sterm_eval_weaken_top`); so the head is
`decide (x < bound) = true` exactly when `x < bound`. -/

theorem boundNatLt_eval_true {arity : Nat}
    (codeBody : Term 2 .stab) (fuel : Nat) (n : STerm arity .nat)
    (rho : Env arity) (E : PartialStabilizer) (x bound : Nat)
    (hN : n.eval codeBody fuel rho E = some bound) (hx : x < bound) :
    SFormula.eval codeBody fuel (SFormula.boundNatLt n) (Env.cons x rho) E =
      some true := by
  have hboundNat :
      STerm.eval codeBody fuel (SFormula.boundNat (arity := arity))
        (Env.cons x rho) E = some x := by
    unfold SFormula.boundNat SC.closed STerm.eval Term.eval
    change some ((Env.cons x rho) ⟨0, Nat.succ_pos arity⟩) = some x
    rfl
  have hNweak :
      STerm.eval codeBody fuel n.weaken (Env.cons x rho) E = some bound := by
    rw [sterm_eval_weaken_top]; exact hN
  simp [SFormula.boundNatLt, SFormula.witnessLt, SFormula.eval, STerm.eval,
    hboundNat, hNweak, SC.b, Term.eval, hx]

/-! ## `ContextHolds` dischargers for the universal-intro nodes

Given a context `Γ` all of whose formulas hold at `(rho, E)`, after stepping
under one bounded binder (consing `x < bound`):

* every weakened `G ∈ Γ.map (·.weaken)` still holds, by
  `sformula_eval_weaken_top`;
* (bounded form) the extra `boundNatLt n` head holds, by `boundNatLt_eval_true`.
-/

/-- Plain `allNatLtIntro` discharger: weakening the whole context preserves
    `ContextHolds`. -/
theorem contextHolds_weaken_cons {arity : Nat}
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity)
    (E : PartialStabilizer) (Γ : List (SFormula arity)) (x : Nat)
    (hΓ : SFormula.ContextHolds codeBody fuel rho E Γ) :
    SFormula.ContextHolds codeBody fuel (Env.cons x rho) E
      (Γ.map (fun G => G.weaken)) := by
  intro A hA
  rcases List.mem_map.1 hA with ⟨G, hGmem, rfl⟩
  rw [sformula_eval_weaken_top]
  exact hΓ G hGmem

/-- Bounded `allNatLtIntroBounded` discharger: the weakened context plus the
    `boundNatLt n` head all hold, given the binder value is in range. -/
theorem contextHolds_boundNatLt_cons {arity : Nat}
    (codeBody : Term 2 .stab) (fuel : Nat) (n : STerm arity .nat)
    (rho : Env arity) (E : PartialStabilizer) (Γ : List (SFormula arity))
    (x bound : Nat)
    (hN : n.eval codeBody fuel rho E = some bound) (hx : x < bound)
    (hΓ : SFormula.ContextHolds codeBody fuel rho E Γ) :
    SFormula.ContextHolds codeBody fuel (Env.cons x rho) E
      (SFormula.boundNatLt n :: Γ.map (fun G => G.weaken)) := by
  intro A hA
  rcases List.mem_cons.1 hA with hHead | hTail
  · subst hHead
    exact boundNatLt_eval_true codeBody fuel n rho E x bound hN hx
  · exact contextHolds_weaken_cons codeBody fuel rho E Γ x hΓ A hTail

/-! ## Axiom audit of the public eval-under-substitution bridge (sorry-free) -/
#print axioms Term.eval_instantiateNatAt
#print axioms Term.eval_instantiateTopNat

end QHL.CodeLang.StabBinder
