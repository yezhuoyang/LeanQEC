import QStab.QHL.CodeStabBinder
import QStab.QHL.Verify.CodeEvalHelpers

/-! # Fuel monotonicity and recursion-unfold soundness for the code evaluator

This file builds the semantic foundation for treating "recursion" as a sound
*logic rule*: a fuel-driven recursive evaluator can be unfolded by appealing to
a lemma instead of by running the evaluator at proof time.

## What "fuel monotonicity" can and cannot mean here

The naive statement

  `Term.eval cb f t rho = some v -> Term.eval cb (f+1) t rho = some v`

is **false** for stabilizer-typed terms (`ty = .stab`).  A stabilizer value has
type `PartialStabilizer = Nat -> Option Pauli`, and the `.stabLam` case of the
evaluator returns a *closure that captures the current fuel*:

  `eval cb f (stabLam entry) rho = some (fun q => eval cb f entry (cons q rho))`.

At fuel `f+1` the same term returns `some (fun q => eval cb (f+1) entry ...)`.
These two `some`-values are *different functions* whenever some entry is `none`
at fuel `f` but `some _` at fuel `f+1` (e.g. when `entry` reads a `recCall` that
is fuel-starved at `f`).  Concretely, with
`cb := stabLam (ite (q = 0) X I)` and
`t := stabLam (stabAt (recCall 7 11) q)` one has
`(eval cb 0 t .empty).map (· 0) = some none` but
`(eval cb 1 t .empty).map (· 0) = some (some X)`, so the two stabilizer values
disagree at `q = 0` and exact `Option`-equality fails.  (This was checked with
`#eval`; see the smoke test at the end of the file.)

The honest, *true* monotonicity statement is therefore a **refinement**: as fuel
grows the result only ever becomes "more defined".  For ground types
(`.nat`, `.bool`, `.pauli`) refinement is exactly the spec's equality
`a = some v -> b = some v`; for `.stab` it is entry-wise preservation of `some`.
This refinement is exactly what the recursion-unfold rule needs, because the two
sides of the unfold differ by precisely one fuel unit on the same code body, and
the assertion `stabEqUpTo` only compares the *defined* prefix.
-/

namespace QHL.CodeLang.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder

/-! ## A fuel-refinement relation on evaluator outputs -/

/-- Fuel refinement on evaluator outputs.

For ground types it is the spec's `a = some v -> b = some v`.  For stabilizer
type it is entry-wise preservation of definedness: every entry that is `some` in
`a` is `some` (with the same Pauli) in `b`. -/
def Refines : (ty : Ty) -> Option ty.partialDenote -> Option ty.partialDenote -> Prop
  | .stab, a, b =>
      forall sa, a = some sa ->
        exists sb, b = some sb /\ forall q p, sa q = some p -> sb q = some p
  | .nat, a, b => forall v, a = some v -> b = some v
  | .bool, a, b => forall v, a = some v -> b = some v
  | .pauli, a, b => forall v, a = some v -> b = some v

namespace Refines

/-- Refinement is reflexive. -/
theorem rfl' {ty : Ty} (a : Option ty.partialDenote) : Refines ty a a := by
  cases ty
  · exact fun v h => h
  · exact fun v h => h
  · exact fun v h => h
  · exact fun sa h => ⟨sa, h, fun _ _ hp => by
      cases h; exact hp⟩

end Refines

/-! ## Generic monadic refinement helpers (axiom-clean: `[propext]`) -/

/-- Refinement through a one-argument bind ending in a pure result. -/
private theorem bind1_refine {α γ : Type}
    {x1 x2 : Option α} {g : α -> γ}
    (hx : forall v, x1 = some v -> x2 = some v)
    {w : γ}
    (hw : (do let av <- x1; some (g av)) = some w) :
    (do let av <- x2; some (g av)) = some w := by
  cases hx1 : x1 with
  | none => rw [hx1] at hw; simp at hw
  | some av => rw [hx1] at hw; simp at hw; rw [hx av hx1]; simpa using hw

/-- Refinement through a two-argument bind ending in a pure result. -/
private theorem bind2_refine {α β γ : Type}
    {x1 x2 : Option α} {y1 y2 : Option β} {g : α -> β -> γ}
    (hx : forall v, x1 = some v -> x2 = some v)
    (hy : forall v, y1 = some v -> y2 = some v)
    {w : γ}
    (hw : (do let av <- x1; let bv <- y1; some (g av bv)) = some w) :
    (do let av <- x2; let bv <- y2; some (g av bv)) = some w := by
  cases hx1 : x1 with
  | none => rw [hx1] at hw; simp at hw
  | some av =>
    cases hy1 : y1 with
    | none => rw [hx1, hy1] at hw; simp at hw
    | some bv =>
      rw [hx1, hy1] at hw; simp at hw
      rw [hx av hx1, hy bv hy1]; simpa using hw

/-- Refinement through a single first-value bind, where the continuation
    refines branch-wise.  Covers `.and`, `.or`, and `.ite`. -/
private theorem branch_refine {α γ : Type}
    {x1 x2 : Option α} {k1 k2 : α -> Option γ}
    (hx : forall v, x1 = some v -> x2 = some v)
    (hk : forall a w, k1 a = some w -> k2 a = some w)
    {w : γ} (hw : (x1 >>= k1) = some w) : (x2 >>= k2) = some w := by
  cases hx1 : x1 with
  | none => rw [hx1] at hw; simp at hw
  | some av => rw [hx1] at hw; simp at hw; rw [hx av hx1]; simp; exact hk av w hw

/-- Refinement through a guarded if-then-else over an arbitrary result type.
    Covers the generic-`ty` `.ite` case where `Refines` does not reduce. -/
private theorem refines_ite {ty : Ty}
    {c1 c2 : Option Bool} {x1 x2 y1 y2 : Option ty.partialDenote}
    (hc : forall v, c1 = some v -> c2 = some v)
    (hx : Refines ty x1 x2) (hy : Refines ty y1 y2) :
    Refines ty (c1 >>= fun cv => if cv then x1 else y1)
      (c2 >>= fun cv => if cv then x2 else y2) := by
  cases ty <;>
    · intro v hv
      cases hc1 : c1 with
      | none => rw [hc1] at hv; simp at hv
      | some cv =>
          rw [hc1] at hv; simp at hv; rw [hc cv hc1]; simp
          cases cv with
          | true => simp at hv ⊢; exact hx v hv
          | false => simp at hv ⊢; exact hy v hv

/-! ## Entry-wise monotonicity for the stabilizer combinators -/

/-- Entry-wise monotonicity for partial stabilizer multiplication. -/
private theorem partialStabilizerMul_refine
    {A1 A2 B1 B2 : PartialStabilizer}
    (hA : forall q p, A1 q = some p -> A2 q = some p)
    (hB : forall q p, B1 q = some p -> B2 q = some p)
    (q : Nat) (p : Pauli)
    (h : partialStabilizerMul A1 B1 q = some p) :
    partialStabilizerMul A2 B2 q = some p := by
  simp only [partialStabilizerMul] at h ⊢
  exact bind2_refine (fun v hv => hA q v hv) (fun v hv => hB q v hv) h

/-- Entry-wise monotonicity for the partial stabilizer fold, given that each
    body row is entry-wise monotone. -/
private theorem partialStabilizerFold_refine
    {n : Nat} {body1 body2 : Nat -> PartialStabilizer}
    (h : forall i q p, body1 i q = some p -> body2 i q = some p) :
    forall (q : Nat) (p : Pauli),
      partialStabilizerFold n body1 q = some p -> partialStabilizerFold n body2 q = some p := by
  induction n with
  | zero =>
      intro q p hq
      simpa [partialStabilizerFold] using hq
  | succ m ih =>
      intro q p hq
      simp only [partialStabilizerFold] at hq ⊢
      exact partialStabilizerMul_refine
        (fun q' p' hp' => ih q' p' hp')
        (fun q' p' hp' => h m q' p' hp') q p hq

/-! ## The generic fuel-monotonicity theorem -/

/-- **Generic evaluator fuel monotonicity (refinement form).**

`Term.eval` is monotone in fuel up to refinement: increasing the fuel by one
only ever makes the result more defined.  For ground types this is exactly the
spec's `= some v -> = some v`; for `.stab` it is entry-wise `some`-preservation
(see the module docstring for why exact equality is *false* at `.stab`).

The proof uses the *same* well-founded measure `(fuel, sizeOfTerm term)` that the
evaluator itself terminates by.  The only nontrivial case is `.recCall`: at fuel
`0` the hypothesis `= some _` is impossible (the evaluator returns `none`), and
at fuel `f+1` the inner recursive call drops to fuel `f`, so the induction
hypothesis applies at the strictly smaller measure `(f, sizeOfTerm cb)`. -/
theorem eval_fuel_mono_refines (cb : Term 2 .stab) :
    forall (f : Nat) {arity : Nat} {ty : Ty} (t : Term arity ty) (rho : Env arity),
      Refines ty (Term.eval cb f t rho) (Term.eval cb (f + 1) t rho)
  | _, _, _, .var v, rho => by intro w hw; simpa [Term.eval] using hw
  | _, _, _, .natLit n, _ => by intro w hw; simpa [Term.eval] using hw
  | _, _, _, .boolLit b, _ => by intro w hw; simpa [Term.eval] using hw
  | _, _, _, .pauliLit p, _ => by intro w hw; simpa [Term.eval] using hw
  | f, _, _, .add a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .sub a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .mul a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .div a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .mod a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .eqNat a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .ltNat a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .leNat a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .not a, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind1_refine (eval_fuel_mono_refines cb f a rho) hw
  | f, _, _, .and a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      refine branch_refine (eval_fuel_mono_refines cb f a rho) ?_ hw
      intro av wv hk1
      cases av with
      | true => exact eval_fuel_mono_refines cb f b rho wv hk1
      | false => exact hk1
  | f, _, _, .or a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      refine branch_refine (eval_fuel_mono_refines cb f a rho) ?_ hw
      intro av wv hk1
      cases av with
      | true => exact hk1
      | false => exact eval_fuel_mono_refines cb f b rho wv hk1
  | f, _, _, .ite c t e, rho => by
      have h := refines_ite (ty := _)
        (eval_fuel_mono_refines cb f c rho)
        (eval_fuel_mono_refines cb f t rho)
        (eval_fuel_mono_refines cb f e rho)
      simpa [Term.eval] using h
  | f, _, _, .pauliMul a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .anticommutes a b, rho => by
      intro w hw
      rw [Term.eval] at hw ⊢
      exact bind2_refine (eval_fuel_mono_refines cb f a rho)
        (eval_fuel_mono_refines cb f b rho) hw
  | f, _, _, .stabLam entry, rho => by
      intro sa hsa
      refine ⟨fun q => Term.eval cb (f + 1) entry (Env.cons q rho), by simp [Term.eval], ?_⟩
      intro q p hp
      have hsa' : (fun q => Term.eval cb f entry (Env.cons q rho)) = sa := by
        simpa [Term.eval] using hsa
      rw [<- hsa'] at hp
      exact eval_fuel_mono_refines cb f entry (Env.cons q rho) p hp
  | f, _, _, .stabAt s q, rho => by
      intro w hw
      rw [Term.eval] at hw
      cases hsv : Term.eval cb f s rho with
      | none => rw [hsv] at hw; simp at hw
      | some sv =>
        cases hqv : Term.eval cb f q rho with
        | none => rw [hsv, hqv] at hw; simp at hw
        | some qv =>
          rw [hsv, hqv] at hw; simp at hw
          obtain ⟨sb, hsb, hsbmono⟩ := eval_fuel_mono_refines cb f s rho sv hsv
          rw [Term.eval, hsb, eval_fuel_mono_refines cb f q rho qv hqv]
          simpa using hsbmono qv w hw
  | f, _, _, .stabFold n body, rho => by
      intro sa hsa
      rw [Term.eval] at hsa
      cases hnv : Term.eval cb f n rho with
      | none => rw [hnv] at hsa; simp at hsa
      | some nv =>
        rw [hnv] at hsa; simp at hsa
        -- The `f+1`-fuel value of the fold, with each row evaluated at fuel `f+1`.
        refine ⟨partialStabilizerFold nv (fun i =>
            match Term.eval cb (f + 1) body (Env.cons i rho) with
            | some row => row
            | none => fun _ => none), ?_, ?_⟩
        · rw [Term.eval, eval_fuel_mono_refines cb f n rho nv hnv]; rfl
        · intro q p hp
          rw [<- hsa] at hp
          refine partialStabilizerFold_refine ?_ q p hp
          intro i q' p' hp'
          cases hbi : Term.eval cb f body (Env.cons i rho) with
          | none => simp [hbi] at hp'
          | some row =>
              obtain ⟨sb, hsb, hsbmono⟩ :=
                eval_fuel_mono_refines cb f body (Env.cons i rho) row hbi
              simp only [hbi] at hp'
              simp only [hsb]
              exact hsbmono q' p' hp'
  | 0, _, _, .recCall d k, rho => by
      intro sa hsa
      rw [Term.eval] at hsa
      exact absurd hsa (by simp)
  | f + 1, _, _, .recCall d k, rho => by
      intro sa hsa
      rw [Term.eval] at hsa
      cases hdv : Term.eval cb f d rho with
      | none => rw [hdv] at hsa; simp at hsa
      | some dv =>
        cases hkv : Term.eval cb f k rho with
        | none => rw [hdv, hkv] at hsa; simp at hsa
        | some kv =>
          rw [hdv, hkv] at hsa; simp at hsa
          obtain ⟨sb, hsb, hsbmono⟩ :=
            eval_fuel_mono_refines cb f cb (Env.code dv kv) sa hsa
          refine ⟨sb, ?_, hsbmono⟩
          rw [Term.eval, eval_fuel_mono_refines cb f d rho dv hdv,
            eval_fuel_mono_refines cb f k rho kv hkv]
          exact hsb
termination_by f _ _ t _ => (f, Term.sizeOfTerm t)
decreasing_by
  all_goals
    simp_wf
    simp [Term.sizeOfTerm]
    omega

/-! ## Ground-type corollary: exact-equality fuel monotonicity

For non-stabilizer terms refinement *is* the spec's literal statement. -/

/-- Exact-equality fuel monotonicity for natural-number terms. -/
theorem eval_fuel_mono_nat {arity : Nat} {cb : Term 2 .stab} {t : Term arity .nat}
    {rho : Env arity} {f : Nat} {v : Nat}
    (h : Term.eval cb f t rho = some v) : Term.eval cb (f + 1) t rho = some v :=
  eval_fuel_mono_refines cb f t rho v h

/-- Exact-equality fuel monotonicity for boolean terms. -/
theorem eval_fuel_mono_bool {arity : Nat} {cb : Term 2 .stab} {t : Term arity .bool}
    {rho : Env arity} {f : Nat} {v : Bool}
    (h : Term.eval cb f t rho = some v) : Term.eval cb (f + 1) t rho = some v :=
  eval_fuel_mono_refines cb f t rho v h

/-- Exact-equality fuel monotonicity for Pauli terms. -/
theorem eval_fuel_mono_pauli {arity : Nat} {cb : Term 2 .stab} {t : Term arity .pauli}
    {rho : Env arity} {f : Nat} {v : Pauli}
    (h : Term.eval cb f t rho = some v) : Term.eval cb (f + 1) t rho = some v :=
  eval_fuel_mono_refines cb f t rho v h

/-- Entry-wise fuel monotonicity for stabilizer terms: every defined entry at
    fuel `f` is preserved (with the same Pauli) at fuel `f+1`. -/
theorem eval_fuel_mono_stab {arity : Nat} {cb : Term 2 .stab} {t : Term arity .stab}
    {rho : Env arity} {f : Nat} {sa : PartialStabilizer}
    (h : Term.eval cb f t rho = some sa) :
    exists sb, Term.eval cb (f + 1) t rho = some sb /\
      forall q p, sa q = some p -> sb q = some p :=
  eval_fuel_mono_refines cb f t rho sa h

/-- `≤`-corollary of entry-wise fuel monotonicity for stabilizer terms. -/
theorem eval_fuel_le_stab {arity : Nat} {cb : Term 2 .stab} {t : Term arity .stab}
    {rho : Env arity} {f g : Nat} (hfg : f <= g) {sa : PartialStabilizer}
    (h : Term.eval cb f t rho = some sa) :
    exists sb, Term.eval cb g t rho = some sb /\
      forall q p, sa q = some p -> sb q = some p := by
  obtain ⟨m, rfl⟩ := Nat.le.dest hfg
  clear hfg
  induction m with
  | zero => exact ⟨sa, by simpa using h, fun q p hp => hp⟩
  | succ j ih =>
      obtain ⟨sb, hsb, hsbmono⟩ := ih
      obtain ⟨sc, hsc, hscmono⟩ := eval_fuel_mono_stab hsb
      refine ⟨sc, ?_, fun q p hp => hscmono q p (hsbmono q p hp)⟩
      rw [Nat.add_succ]
      exact hsc

/-! ## A self-contained substitution lemma for literal natural arguments

The project's `StabBinder.Term.eval_instantiateNatAt` is `private`, so it cannot
be reused across files.  We re-derive the part we need, specialised to the case
where the substituted term is a closed literal `Term.natLit xv` (the only case
`codeSubst` ever uses).  Restricting to literals removes all the
weakening-under-binders bookkeeping, because `(Term.natLit xv).weaken` is
definitionally `Term.natLit xv`. -/

/-- `rho'` is `rho` with a fresh natural variable inserted at de Bruijn `cutoff`,
    captured by the lifted/non-lifted variable images. -/
private def EnvLifted {arity : Nat} (cutoff : Nat)
    (rho : Env arity) (rho' : Env (arity + 1)) : Prop :=
  (forall v : Fin arity, v.val < cutoff ->
      rho' ⟨v.val, Nat.lt_trans v.isLt (Nat.lt_succ_self arity)⟩ = rho v) /\
  (forall v : Fin arity, cutoff <= v.val ->
      rho' ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ = rho v)

/-- `EnvLifted` extended with the value taken by the freshly inserted variable. -/
private def EnvInserted {arity : Nat} (cutoff xv : Nat)
    (rho : Env arity) (rho' : Env (arity + 1)) (hcut : cutoff <= arity) : Prop :=
  EnvLifted cutoff rho rho' /\ rho' ⟨cutoff, Nat.lt_succ_of_le hcut⟩ = xv

private theorem EnvLifted.underBinder {arity cutoff : Nat}
    {rho : Env arity} {rho' : Env (arity + 1)}
    (h : EnvLifted cutoff rho rho') (x : Nat) :
    EnvLifted (cutoff + 1) (Env.cons x rho) (Env.cons x rho') := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · cases v using Fin.cases with
    | zero => rfl
    | succ v => simp [Env.cons]; exact h.1 v (Nat.lt_of_succ_lt_succ hv)
  · cases v using Fin.cases with
    | zero => simp at hv
    | succ v => simp [Env.cons]; exact h.2 v (Nat.le_of_succ_le_succ hv)

private theorem EnvLifted.top {arity : Nat} (rho : Env arity) (x : Nat) :
    EnvLifted 0 rho (Env.cons x rho) := by
  refine ⟨fun v hv => ?_, fun v _ => ?_⟩
  · omega
  · simp [Env.cons]

private theorem EnvInserted.underBinder {arity cutoff xv : Nat}
    {rho : Env arity} {rho' : Env (arity + 1)} {hcut : cutoff <= arity}
    (h : EnvInserted cutoff xv rho rho' hcut) (q : Nat) :
    EnvInserted (cutoff + 1) xv (Env.cons q rho) (Env.cons q rho') (by omega) :=
  ⟨EnvLifted.underBinder h.1 q, by simpa [Env.cons] using h.2⟩

private theorem EnvInserted.top {arity : Nat} (rho : Env arity) (xv : Nat) :
    EnvInserted 0 xv rho (Env.cons xv rho) (Nat.zero_le arity) :=
  ⟨EnvLifted.top rho xv, rfl⟩

/-- **Generic weakening-evaluation lemma.**  Lifting a term over a fresh binder
    and evaluating in the inserted environment agrees with the original
    evaluation.  This is the kernel's `Term.eval_lift_of_env` re-derived locally
    (that one is `private`), over PureDeriv's own `EnvLifted`.  It is a fully
    general structural fact, *not* literal-restricted, and it is the one weakening
    collapse the telescoping rule needs (for the closed cut under the
    `stabMul`-lambda).  The `.stabLam`/`.stabFold` cases recurse under the binder
    via `EnvLifted.underBinder`; `.recCall` drops fuel uniformly. -/
private theorem eval_lift_of_envLifted {arity cutoff : Nat} {ty : Ty}
    (t : Term arity ty) (cb : Term 2 .stab) (fuel : Nat)
    {rho : Env arity} {rho' : Env (arity + 1)} (h : EnvLifted cutoff rho rho') :
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

/-- **Top weakening collapse (public corollary).**  Weakening a term by a fresh
    top binder and evaluating in the consed environment agrees with the original
    evaluation: `⟦t.lift 0⟧_(q::ρ) = ⟦t⟧_ρ`.  This is the cutoff-`0` instance of
    `eval_lift_of_envLifted` and the reusable face of the weakening machinery —
    e.g. the Surface cut-family totality proofs need exactly this (they cannot
    reach the `private` `EnvLifted` plumbing). -/
theorem Term.eval_weaken_top {arity : Nat} {ty : Ty}
    (t : Term arity ty) (cb : Term 2 .stab) (fuel q : Nat) (rho : Env arity) :
    Term.eval cb fuel (t.lift 0) (Env.cons q rho) = Term.eval cb fuel t rho :=
  eval_lift_of_envLifted t cb fuel (EnvLifted.top rho q)

private theorem STerm.eval_lift_of_envLifted {arity cutoff : Nat} {ty : Ty}
    (t : STerm arity ty) {rho : Env arity} {rho' : Env (arity + 1)}
    (h : EnvLifted cutoff rho rho') (cb : Term 2 .stab) (fuel : Nat)
    (E : PartialStabilizer) :
    STerm.eval cb fuel (t.lift cutoff) rho' E =
      STerm.eval cb fuel t rho E := by
  induction t generalizing cutoff fuel with
  | closed t =>
      simp [STerm.lift, STerm.eval,
        QHL.CodeLang.Verify.eval_lift_of_envLifted t cb fuel h]
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
      exact ih (EnvLifted.underBinder h q) fuel
  | stabAt s q ihs ihq =>
      simp [STerm.lift, STerm.eval, ihs h fuel, ihq h fuel]
  | stabFold n body ihn ihbody =>
      simp [STerm.lift, STerm.eval, ihn h fuel]
      cases hn : STerm.eval cb fuel n rho E with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i q
          have hbody := ihbody (EnvLifted.underBinder h i) fuel
          rw [hbody]
  | applyNat witness body ihw ihbody =>
      simp [STerm.lift, STerm.eval, ihw h fuel]
      cases hw : STerm.eval cb fuel witness rho E with
      | none =>
          simp
      | some wv =>
          simp
          exact ihbody (EnvLifted.underBinder h wv) fuel

private theorem STerm.eval_weaken_top {arity : Nat} {ty : Ty}
    (t : STerm arity ty) (cb : Term 2 .stab) (fuel q : Nat)
    (rho : Env arity) (E : PartialStabilizer) :
    STerm.eval cb fuel t.weaken (Env.cons q rho) E =
      STerm.eval cb fuel t rho E := by
  exact STerm.eval_lift_of_envLifted t (EnvLifted.top rho q) cb fuel E

/-- Substitution-evaluation lemma for an arbitrary natural argument.

This is the arity-general version of the literal-only lemma below.  It is
re-derived here because the corresponding kernel helper is private.  The
hypothesis `hxAll` asks that the substituting Nat term is fuel-stable in the
current environment; this holds for the pure arithmetic Nat terms used as
recursion arguments in the proof layer. -/
private theorem eval_instantiateNatAt {arity cutoff : Nat} {ty : Ty}
    (t : Term (arity + 1) ty) (x : Term arity .nat) (hcut : cutoff <= arity)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    {rho' : Env (arity + 1)} {xv : Nat}
    (hxAll : forall fuel', Term.eval cb fuel' x rho = some xv)
    (hins : EnvInserted cutoff xv rho rho' hcut) :
    Term.eval cb fuel (StabBinder.Term.instantiateNatAt cutoff x hcut t) rho =
      Term.eval cb fuel t rho' :=
  match t with
  | .var v => by
      unfold StabBinder.Term.instantiateNatAt
      by_cases hlt : v.val < cutoff
      · simp [hlt, Term.eval]
        exact (hins.1.1 ⟨v.val, by omega⟩ hlt).symm
      · by_cases heq : v.val = cutoff
        · simp [hlt, heq, Term.eval, hxAll fuel]
          have hv : v = ⟨cutoff, Nat.lt_succ_of_le hcut⟩ := Fin.ext heq
          simpa [hv] using hins.2.symm
        · have hgt : cutoff < v.val := by omega
          have hpred : v.val - 1 < arity := by omega
          have hge : cutoff <= v.val - 1 := by omega
          simp [hlt, heq, Term.eval]
          have hshift := hins.1.2 ⟨v.val - 1, hpred⟩ hge
          have hidx :
              (⟨(v.val - 1) + 1, Nat.succ_lt_succ hpred⟩ : Fin (arity + 1)) = v := by
            apply Fin.ext
            exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hgt))
          simpa [hidx] using hshift.symm
  | .natLit _ => by simp [StabBinder.Term.instantiateNatAt, Term.eval]
  | .boolLit _ => by simp [StabBinder.Term.instantiateNatAt, Term.eval]
  | .pauliLit _ => by simp [StabBinder.Term.instantiateNatAt, Term.eval]
  | .add a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .sub a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .mul a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .div a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .mod a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .eqNat a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .ltNat a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .leNat a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .not a => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins]
  | .and a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .or a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .ite c t e => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt c x hcut cb fuel hxAll hins,
        eval_instantiateNatAt t x hcut cb fuel hxAll hins,
        eval_instantiateNatAt e x hcut cb fuel hxAll hins]
  | .pauliMul a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .anticommutes a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt a x hcut cb fuel hxAll hins,
        eval_instantiateNatAt b x hcut cb fuel hxAll hins]
  | .stabLam entry => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval]
      funext q
      have hxweak :
          forall fuel',
            Term.eval cb fuel' x.weaken (Env.cons q rho) = some xv := by
        intro fuel'
        simpa [Term.weaken] using
          (eval_lift_of_envLifted x cb fuel' (EnvLifted.top rho q)).trans (hxAll fuel')
      exact eval_instantiateNatAt entry x.weaken (by omega) cb fuel hxweak
        (EnvInserted.underBinder hins q)
  | .stabAt s q => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt s x hcut cb fuel hxAll hins,
        eval_instantiateNatAt q x hcut cb fuel hxAll hins]
  | .stabFold n body => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt n x hcut cb fuel hxAll hins]
      cases hn : Term.eval cb fuel n rho' with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i q
          have hxweak :
              forall fuel',
                Term.eval cb fuel' x.weaken (Env.cons i rho) = some xv := by
            intro fuel'
            simpa [Term.weaken] using
              (eval_lift_of_envLifted x cb fuel' (EnvLifted.top rho i)).trans
                (hxAll fuel')
          have hbody :=
            eval_instantiateNatAt body x.weaken (by omega) cb fuel hxweak
              (EnvInserted.underBinder hins i)
          rw [hbody]
  | .recCall d k => by
      cases fuel with
      | zero =>
          simp [StabBinder.Term.instantiateNatAt, Term.eval]
      | succ fuel =>
          simp [StabBinder.Term.instantiateNatAt, Term.eval,
            eval_instantiateNatAt d x hcut cb fuel hxAll hins,
            eval_instantiateNatAt k x hcut cb fuel hxAll hins]
termination_by Term.sizeOfTerm t
decreasing_by all_goals (simp_wf; simp [Term.sizeOfTerm]; try omega)

/-! ### Arity-general code-body substitution

The literal `codeSubst` below is enough for closed recursion-unfold leaves, but
under a family binder the recursive call has symbolic arguments such as
`gridRowZStripIndex dist row slot`.  The following small substitution engine is
generic: under `depth` ordinary binders, it replaces the code body's variables
`k` and `d` by arbitrary ambient Nat terms `kT` and `dT`, weakened under those
binders.  The accompanying theorem is the semantic foundation for the
arity-general rec-unfold rule; it is not Surface-specific. -/

def liftTopN : (depth : Nat) -> {arity : Nat} -> {ty : Ty} ->
    Term arity ty -> Term (arity + depth) ty
  | 0, _, _, t => by simpa using t
  | depth + 1, _, _, t => by
      simpa [Nat.add_assoc] using (Term.weaken (liftTopN depth t))

def codeSubstAt {arity : Nat} (dT kT : Term arity .nat) :
    (depth : Nat) -> {ty : Ty} -> Term (depth + 2) ty -> Term (arity + depth) ty
  | depth, _, .var v =>
      if hlt : v.val < depth then
        .var ⟨v.val, by omega⟩
      else if heq : v.val = depth then
        liftTopN depth kT
      else
        liftTopN depth dT
  | _, _, .natLit n => .natLit n
  | _, _, .boolLit b => .boolLit b
  | _, _, .pauliLit p => .pauliLit p
  | depth, _, .add a b => .add (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .sub a b => .sub (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .mul a b => .mul (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .div a b => .div (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .mod a b => .mod (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .eqNat a b =>
      .eqNat (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .ltNat a b =>
      .ltNat (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .leNat a b =>
      .leNat (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .not a => .not (codeSubstAt dT kT depth a)
  | depth, _, .and a b => .and (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .or a b => .or (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .ite c t e =>
      .ite (codeSubstAt dT kT depth c)
        (codeSubstAt dT kT depth t)
        (codeSubstAt dT kT depth e)
  | depth, _, .pauliMul a b =>
      .pauliMul (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .anticommutes a b =>
      .anticommutes (codeSubstAt dT kT depth a) (codeSubstAt dT kT depth b)
  | depth, _, .stabLam entry => .stabLam (codeSubstAt dT kT (depth + 1) entry)
  | depth, _, .stabAt s q =>
      .stabAt (codeSubstAt dT kT depth s) (codeSubstAt dT kT depth q)
  | depth, _, .stabFold n body =>
      .stabFold (codeSubstAt dT kT depth n) (codeSubstAt dT kT (depth + 1) body)
  | depth, _, .recCall d k =>
      .recCall (codeSubstAt dT kT depth d) (codeSubstAt dT kT depth k)
termination_by depth ty t => Term.sizeOfTerm t
decreasing_by all_goals (simp_wf; simp [Term.sizeOfTerm]; try omega)

private def envTailPure {arity : Nat} (rho : Env (arity + 1)) : Env arity :=
  fun i => rho ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

private theorem EnvLifted.tailPure {arity : Nat} (rho : Env (arity + 1)) :
    EnvLifted 0 (envTailPure rho) rho := by
  refine ⟨fun v hv => by omega, fun v _ => ?_⟩
  rfl

private def EnvAmbientAt {arity depth : Nat} (rho : Env arity)
    (dst : Env (arity + depth)) : Prop :=
  forall j : Fin arity, dst ⟨depth + j.val, by omega⟩ = rho j

private theorem EnvAmbientAt.zero {arity : Nat} {rho dst : Env arity}
    (h : EnvAmbientAt (depth := 0) rho dst) : dst = rho := by
  funext j
  simpa [EnvAmbientAt] using h j

private theorem EnvAmbientAt.tail {arity depth : Nat} {rho : Env arity}
    {dst : Env (arity + (depth + 1))}
    (h : EnvAmbientAt (depth := depth + 1) rho dst) :
    EnvAmbientAt (depth := depth) rho (envTailPure dst) := by
  intro j
  unfold envTailPure
  have hidx :
      (⟨depth + j.val + 1, by omega⟩ : Fin (arity + (depth + 1))) =
        ⟨depth + 1 + j.val, by omega⟩ := by
    apply Fin.ext
    simp
    omega
  simpa [hidx] using h j

private theorem EnvAmbientAt.underBinder {arity depth : Nat} {rho : Env arity}
    {dst : Env (arity + depth)} (h : EnvAmbientAt (depth := depth) rho dst)
    (q : Nat) :
    EnvAmbientAt (depth := depth + 1) rho (Env.cons q dst) := by
  intro j
  change (Env.cons q dst) ⟨depth + 1 + j.val, by omega⟩ = rho j
  have hidx :
      (⟨depth + 1 + j.val, by omega⟩ : Fin (arity + (depth + 1))) =
        ⟨(depth + j.val) + 1, by omega⟩ := by
    apply Fin.ext
    simp
    omega
  rw [hidx]
  simp [Env.cons]
  simpa using h j

private theorem eval_liftTopN {arity depth : Nat} {ty : Ty} (t : Term arity ty)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    {dst : Env (arity + depth)}
    (h : EnvAmbientAt (depth := depth) rho dst) :
    Term.eval cb fuel (liftTopN depth t) dst = Term.eval cb fuel t rho := by
  induction depth with
  | zero =>
      have henv : dst = rho := EnvAmbientAt.zero h
      subst henv
      simp [liftTopN]
  | succ depth ih =>
      simp [liftTopN, Nat.add_assoc]
      rw [Term.weaken, eval_lift_of_envLifted _ cb fuel (EnvLifted.tailPure dst)]
      exact ih (EnvAmbientAt.tail h)

private def EnvCodeSubstAt {arity depth : Nat} (dv kv : Nat) (rho : Env arity)
    (src : Env (depth + 2)) (dst : Env (arity + depth)) : Prop :=
  (forall i : Fin depth, dst ⟨i.val, by omega⟩ = src ⟨i.val, by omega⟩) /\
  src ⟨depth, by omega⟩ = kv /\
  src ⟨depth + 1, by omega⟩ = dv /\
  EnvAmbientAt (depth := depth) rho dst

private theorem EnvCodeSubstAt.underBinder {arity depth dv kv : Nat}
    {rho : Env arity} {src : Env (depth + 2)} {dst : Env (arity + depth)}
    (h : EnvCodeSubstAt dv kv rho src dst) (q : Nat) :
    EnvCodeSubstAt (depth := depth + 1) dv kv rho (Env.cons q src) (Env.cons q dst) := by
  refine ⟨?_, ?_, ?_, EnvAmbientAt.underBinder h.2.2.2 q⟩
  · intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        change (Env.cons q dst) ⟨i.val + 1, by omega⟩ =
          (Env.cons q src) ⟨i.val + 1, by omega⟩
        simp [Env.cons]
        exact h.1 i
  · change (Env.cons q src) ⟨depth + 1, by omega⟩ = kv
    have hidx :
        (⟨depth + 1, by omega⟩ : Fin ((depth + 1) + 2)) =
          ⟨depth + 1, by omega⟩ := rfl
    simp [Env.cons, hidx]
    simpa using h.2.1
  · change (Env.cons q src) ⟨depth + 1 + 1, by omega⟩ = dv
    have hidx :
        (⟨depth + 1 + 1, by omega⟩ : Fin ((depth + 1) + 2)) =
          ⟨(depth + 1) + 1, by omega⟩ := by
      apply Fin.ext
      omega
    rw [hidx]
    simp [Env.cons]
    simpa using h.2.2.1

private theorem eval_codeSubstAt {arity depth : Nat} {ty : Ty}
    (t : Term (depth + 2) ty) (dT kT : Term arity .nat)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    {src : Env (depth + 2)} {dst : Env (arity + depth)} {dv kv : Nat}
    (hdAll : forall fuel', Term.eval cb fuel' dT rho = some dv)
    (hkAll : forall fuel', Term.eval cb fuel' kT rho = some kv)
    (henv : EnvCodeSubstAt dv kv rho src dst) :
    Term.eval cb fuel (codeSubstAt dT kT depth t) dst =
      Term.eval cb fuel t src :=
  match t with
  | .var v => by
      unfold codeSubstAt
      by_cases hlt : v.val < depth
      · simp [hlt, Term.eval]
        exact henv.1 ⟨v.val, by omega⟩
      · by_cases heq : v.val = depth
        · simp [hlt, heq, Term.eval]
          rw [eval_liftTopN kT cb fuel henv.2.2.2, hkAll fuel]
          have hv : v = ⟨depth, by omega⟩ := Fin.ext heq
          simpa [hv] using henv.2.1.symm
        · have hvval : v.val = depth + 1 := by omega
          simp [hlt, heq, Term.eval]
          rw [eval_liftTopN dT cb fuel henv.2.2.2, hdAll fuel]
          have hv : v = ⟨depth + 1, by omega⟩ := Fin.ext hvval
          simpa [hv] using henv.2.2.1.symm
  | .natLit _ => by simp [codeSubstAt, Term.eval]
  | .boolLit _ => by simp [codeSubstAt, Term.eval]
  | .pauliLit _ => by simp [codeSubstAt, Term.eval]
  | .add a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .sub a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .mul a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .div a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .mod a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .eqNat a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .ltNat a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .leNat a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .not a => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv]
  | .and a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .or a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .ite c t e => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt c dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt t dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt e dT kT cb fuel hdAll hkAll henv]
  | .pauliMul a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .anticommutes a b => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt a dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt b dT kT cb fuel hdAll hkAll henv]
  | .stabLam entry => by
      simp [codeSubstAt, Term.eval]
      funext q
      exact eval_codeSubstAt entry dT kT cb fuel hdAll hkAll
        (EnvCodeSubstAt.underBinder henv q)
  | .stabAt s q => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt s dT kT cb fuel hdAll hkAll henv,
        eval_codeSubstAt q dT kT cb fuel hdAll hkAll henv]
  | .stabFold n body => by
      simp [codeSubstAt, Term.eval,
        eval_codeSubstAt n dT kT cb fuel hdAll hkAll henv]
      cases hn : Term.eval cb fuel n src with
      | none => simp
      | some nv =>
          simp
          congr
          funext i
          rw [eval_codeSubstAt body dT kT cb fuel hdAll hkAll
            (EnvCodeSubstAt.underBinder henv i)]
  | .recCall d k => by
      cases fuel with
      | zero =>
          simp [codeSubstAt, Term.eval]
      | succ fuel =>
          simp [codeSubstAt, Term.eval,
            eval_codeSubstAt d dT kT cb fuel hdAll hkAll henv,
            eval_codeSubstAt k dT kT cb fuel hdAll hkAll henv]
termination_by Term.sizeOfTerm t
decreasing_by all_goals (simp_wf; simp [Term.sizeOfTerm]; try omega)

/-- Substitute symbolic Nat arguments for the code body's `(d,k)` parameters. -/
def codeSubstTerm {arity : Nat} (cb : Term 2 .stab)
    (dT kT : Term arity .nat) : Term arity .stab :=
  codeSubstAt dT kT 0 cb

theorem eval_codeSubstTerm {arity : Nat} (cb : Term 2 .stab) (fuel : Nat)
    (dT kT : Term arity .nat) (rho : Env arity) {dv kv : Nat}
    (hdAll : forall fuel', Term.eval cb fuel' dT rho = some dv)
    (hkAll : forall fuel', Term.eval cb fuel' kT rho = some kv) :
    Term.eval cb fuel (codeSubstTerm cb dT kT) rho =
      Term.eval cb fuel cb (Env.code dv kv) := by
  unfold codeSubstTerm
  refine eval_codeSubstAt cb dT kT cb fuel hdAll hkAll ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact False.elim (Nat.not_lt_zero _ i.isLt)
  · simp [Env.code, Env.cons]
  · simp [Env.code, Env.cons]
  · intro j
    apply congrArg rho
    apply Fin.ext
    simp

/-- Substitution-evaluation lemma for a literal natural argument: substituting
    `Term.natLit xv` at `cutoff` is the same as evaluating in the inserted
    environment.  Holds at *any* fuel (the literal is fuel-independent). -/
private theorem eval_instantiateNatAt_lit {arity cutoff : Nat} {ty : Ty}
    (t : Term (arity + 1) ty) (xv : Nat) (hcut : cutoff <= arity)
    (cb : Term 2 .stab) (fuel : Nat) {rho : Env arity} {rho' : Env (arity + 1)}
    (hins : EnvInserted cutoff xv rho rho' hcut) :
    Term.eval cb fuel
        (StabBinder.Term.instantiateNatAt cutoff (.natLit xv) hcut t) rho =
      Term.eval cb fuel t rho' :=
  match t with
  | .var v => by
      unfold StabBinder.Term.instantiateNatAt
      by_cases hlt : v.val < cutoff
      · simp [hlt, Term.eval]; exact (hins.1.1 ⟨v.val, by omega⟩ hlt).symm
      · by_cases heq : v.val = cutoff
        · simp [heq, Term.eval]
          have hv : v = ⟨cutoff, Nat.lt_succ_of_le hcut⟩ := Fin.ext heq
          simpa [hv] using hins.2.symm
        · have hgt : cutoff < v.val := by omega
          have hpred : v.val - 1 < arity := by omega
          have hge : cutoff <= v.val - 1 := by omega
          simp [hlt, heq, Term.eval]
          have hshift := hins.1.2 ⟨v.val - 1, hpred⟩ hge
          have hidx :
              (⟨(v.val - 1) + 1, Nat.succ_lt_succ hpred⟩ : Fin (arity + 1)) = v := by
            apply Fin.ext; show (v.val - 1) + 1 = v.val; omega
          simpa [hidx] using hshift.symm
  | .natLit _ => by simp [StabBinder.Term.instantiateNatAt, Term.eval]
  | .boolLit _ => by simp [StabBinder.Term.instantiateNatAt, Term.eval]
  | .pauliLit _ => by simp [StabBinder.Term.instantiateNatAt, Term.eval]
  | .add a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .sub a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .mul a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .div a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .mod a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .eqNat a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .ltNat a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .leNat a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .not a => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins]
  | .and a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .or a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .ite c t e => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit c xv hcut cb fuel hins,
        eval_instantiateNatAt_lit t xv hcut cb fuel hins,
        eval_instantiateNatAt_lit e xv hcut cb fuel hins]
  | .pauliMul a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .anticommutes a b => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit a xv hcut cb fuel hins,
        eval_instantiateNatAt_lit b xv hcut cb fuel hins]
  | .stabLam entry => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval]
      funext q
      have := eval_instantiateNatAt_lit entry xv (by omega) cb fuel
        (EnvInserted.underBinder hins q)
      simpa [Term.weaken, Term.lift] using this
  | .stabAt s q => by
      simp [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit s xv hcut cb fuel hins,
        eval_instantiateNatAt_lit q xv hcut cb fuel hins]
  | .stabFold n body => by
      have IHbody : forall i,
          Term.eval cb fuel
              (StabBinder.Term.instantiateNatAt (cutoff + 1)
                ((Term.natLit (arity := arity) xv).weaken) (by omega) body)
              (Env.cons i rho) =
            Term.eval cb fuel body (Env.cons i rho') := fun i =>
        eval_instantiateNatAt_lit body xv (by omega) cb fuel
          (EnvInserted.underBinder hins i)
      simp only [StabBinder.Term.instantiateNatAt, Term.eval,
        eval_instantiateNatAt_lit n xv hcut cb fuel hins]
      cases hn : Term.eval cb fuel n rho' with
      | none => simp
      | some nv => simp only [IHbody]
  | .recCall d k => by
      cases fuel with
      | zero => simp [StabBinder.Term.instantiateNatAt, Term.eval]
      | succ fuel =>
          simp [StabBinder.Term.instantiateNatAt, Term.eval,
            eval_instantiateNatAt_lit d xv hcut cb fuel hins,
            eval_instantiateNatAt_lit k xv hcut cb fuel hins]
termination_by Term.sizeOfTerm t
decreasing_by all_goals (simp_wf; simp [Term.sizeOfTerm]; try omega)

/-- `instantiateTopNat` of a literal collapses to evaluation in the consed env. -/
private theorem eval_instantiateTopNat_lit {arity : Nat} {ty : Ty}
    (t : Term (arity + 1) ty) (xv : Nat) (cb : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) :
    Term.eval cb fuel (StabBinder.Term.instantiateTopNat (.natLit xv) t) rho =
      Term.eval cb fuel t (Env.cons xv rho) :=
  eval_instantiateNatAt_lit t xv (Nat.zero_le arity) cb fuel (EnvInserted.top rho xv)

/-! ## Recursion-unfold soundness -/

/-- The closed substitution that turns the open code body `cb : Term 2 .stab`
    into the closed stabilizer term denoting `cb (Env.code d k)`.

`Env.code d k = cons k (cons d empty)` binds variable `0 = k` and `1 = d`, so we
substitute `k` first (collapsing arity `2 -> 1`), then `d` (collapsing
`1 -> 0`). -/
def codeSubst (cb : Term 2 .stab) (d k : Nat) : Term 0 .stab :=
  StabBinder.Term.instantiateTopNat (.natLit d)
    (StabBinder.Term.instantiateTopNat (.natLit k) cb)

/-- Evaluating the closed substitution agrees, at *any* fuel, with evaluating the
    open code body under `Env.code d k`.  Two applications of
    `eval_instantiateTopNat_lit`. -/
theorem eval_codeSubst (cb : Term 2 .stab) (f d k : Nat) :
    Term.eval cb f (codeSubst cb d k) Env.empty =
      Term.eval cb f cb (Env.code d k) := by
  rw [codeSubst,
    eval_instantiateTopNat_lit _ d cb f Env.empty,
    eval_instantiateTopNat_lit _ k cb f (Env.cons d Env.empty),
    Env.code]

/-- **Recursion-unfold soundness.**

`recCall (lit d) (lit k)` at fuel `f+1` and the closed substitution
`codeSubst cb d k` at fuel `f+1` denote the *same partial stabilizer up to `n`*:
`stabEqUpTo n` of the two evaluations is `some true`.

This is the semantic justification for a recursion rule that replaces a
`recCall` atom by the unfolded code body without running the evaluator.  The
single hypothesis `hdef` is the natural well-definedness side condition: the
`recCall` must actually evaluate up to the queried prefix.  Concretely we require
that every queried entry `q < n` is defined; this is what makes `stabEqUpTo`
return `some true` rather than `none`.

The proof chains three facts:
* `eval_recCall_succ`     : `recCall@(f+1) = eval cb f cb (Env.code d k)`;
* `eval_codeSubst`        : `codeSubst@(f+1) = eval cb (f+1) cb (Env.code d k)`;
* `eval_fuel_mono_refines`: the `f`-result entry-refines into the `f+1`-result.
The fuel-monotonicity step is the crux: it is exactly the entry-wise refinement
proven above, and it is the reason the `.stab` case could not be stated as exact
equality. -/
theorem recUnfold_sound {cb : Term 2 .stab} {f n d k : Nat}
    {sa : PartialStabilizer}
    (hrec : Term.eval cb (f + 1) (.recCall (.natLit d) (.natLit k)) Env.empty = some sa)
    (hdef : forall q, q < n -> exists p, sa q = some p) :
    (do
      let a <- Term.eval cb (f + 1) (.recCall (.natLit d) (.natLit k)) Env.empty
      let b <- Term.eval cb (f + 1) (codeSubst cb d k) Env.empty
      stabEqUpTo n a b) = some true := by
  -- recCall@(f+1) reduces to eval cb f cb (code d k).
  have hrecEq :
      Term.eval cb (f + 1) (.recCall (.natLit d) (.natLit k)) Env.empty =
        Term.eval cb f cb (Env.code d k) :=
    CodeEvalHelpers.eval_recCall_succ (by simp [Term.eval]) (by simp [Term.eval])
  -- codeSubst@(f+1) reduces to eval cb (f+1) cb (code d k).
  have hsubEq :
      Term.eval cb (f + 1) (codeSubst cb d k) Env.empty =
        Term.eval cb (f + 1) cb (Env.code d k) :=
    eval_codeSubst cb (f + 1) d k
  -- The recCall value `sa` is the `f`-fuel evaluation of the body.
  have hsaBody : Term.eval cb f cb (Env.code d k) = some sa := by
    rw [<- hrecEq]; exact hrec
  -- Fuel monotonicity: `sa` entry-refines into the `f+1`-fuel body value `sb`.
  obtain ⟨sb, hsb, hsbmono⟩ :=
    eval_fuel_mono_refines cb f cb (Env.code d k) sa hsaBody
  -- Rewrite both monadic operands to `some`; the binds then reduce, leaving
  -- the goal `stabEqUpTo n sa sb = some true`.
  rw [hrec, hsubEq, hsb]
  show stabEqUpTo n sa sb = some true
  -- Prove `stabEqUpTo n sa sb = some true` by induction on `n`.
  clear hrec hrecEq hsubEq hsaBody hsb
  induction n with
  | zero => rfl
  | succ m ih =>
      have hdefm : forall q, q < m -> exists p, sa q = some p :=
        fun q hq => hdef q (Nat.lt_succ_of_lt hq)
      have ihm := ih hdefm
      obtain ⟨p, hp⟩ := hdef m (Nat.lt_succ_self m)
      simp only [stabEqUpTo, ihm]
      rw [hp, hsbmono m p hp]
      simp

/-! ## Symbolic-argument recursion-unfold

`recUnfold_sound` above unfolds a `recCall` whose *arguments are literals*
(`natLit d`, `natLit k`).  The lower-bound proof must also unfold a `recCall`
whose arguments are **terms** — e.g. binder variables, or `gridRowZStripIndex
dist row slot` — i.e. `recCall dT kT` for arbitrary closed `dT kT : Term 0 .nat`.

`recUnfoldT_sound` is the term-argument generalisation: at fuel `f+1`,
`recCall dT kT` and the unfolded body `codeSubst cb dv kv` (where `dv = ⟦dT⟧`,
`kv = ⟦kT⟧`) agree on their first `n` qubits.  The extra side condition over the
literal case is exactly the *definedness of the arguments*: `dT`/`kT` must
evaluate to some `dv`/`kv` (the literal case had this for free).  Soundness
factors through the already-general `CodeEvalHelpers.eval_recCall_succ` (which is
stated over arbitrary term arguments) followed by the *same* fuel-monotonicity
step as the literal case. -/

/-- The closed `eqStabUpTo` atom produced by the **symbolic-argument** recUnfold
    rule: `recCall dT kT` and the unfolded body `codeSubst cb dv kv` agree up to
    `n` qubits.  The unfolded operand uses the *evaluated* argument values
    `dv`/`kv` (the literals the symbolic arguments compute to). -/
def recUnfoldAtomT (cb : Term 2 .stab) (n : Nat) (dT kT : Term 0 .nat)
    (dv kv : Nat) : SFormula 0 :=
  .eqStabUpTo (SC.closed (.natLit n))
    (SC.closed (.recCall dT kT))
    (SC.closed (codeSubst cb dv kv))

/-- The symbolic-argument recUnfold atom's evaluation is the `stabEqUpTo` shape
    `recUnfoldT_sound` concludes is `some true`. -/
private theorem recUnfoldAtomT_eval (cb : Term 2 .stab) (fuel n : Nat)
    (dT kT : Term 0 .nat) (dv kv : Nat) (E : PartialStabilizer) :
    (recUnfoldAtomT cb n dT kT dv kv).eval cb fuel Env.empty E =
      (do
        let a <- Term.eval cb fuel (.recCall dT kT) Env.empty
        let b <- Term.eval cb fuel (codeSubst cb dv kv) Env.empty
        stabEqUpTo n a b) := by
  simp only [recUnfoldAtomT, SFormula.eval, STerm.eval, SC.closed, Term.eval]
  rfl

/-- **Symbolic-argument recursion-unfold soundness.**

Like `recUnfold_sound`, but the `recCall` arguments are arbitrary closed terms
`dT kT : Term 0 .nat`, supplied with their evaluated values `dv = ⟦dT⟧`,
`kv = ⟦kT⟧` (the *definedness of the arguments* side conditions `hd`/`hk`).  At
fuel `f+1`, `recCall dT kT` and the unfolded `codeSubst cb dv kv` agree on their
first `n` qubits.

The proof reuses the general `eval_recCall_succ` (term-argument form) to reduce
`recCall@(f+1)` to `eval cb f cb (Env.code dv kv)`, `eval_codeSubst` to reduce
the unfolded body to `eval cb (f+1) cb (Env.code dv kv)`, then closes with the
*same* `eval_fuel_mono_refines` fuel step as the literal case. -/
theorem recUnfoldT_sound {cb : Term 2 .stab} {f n : Nat}
    {dT kT : Term 0 .nat} {dv kv : Nat} {sa : PartialStabilizer}
    (hd : Term.eval cb f dT Env.empty = some dv)
    (hk : Term.eval cb f kT Env.empty = some kv)
    (hrec : Term.eval cb (f + 1) (.recCall dT kT) Env.empty = some sa)
    (hdef : forall q, q < n -> exists p, sa q = some p) :
    (do
      let a <- Term.eval cb (f + 1) (.recCall dT kT) Env.empty
      let b <- Term.eval cb (f + 1) (codeSubst cb dv kv) Env.empty
      stabEqUpTo n a b) = some true := by
  -- recCall@(f+1) reduces to eval cb f cb (code dv kv) via the *term-arg* helper.
  have hrecEq :
      Term.eval cb (f + 1) (.recCall dT kT) Env.empty =
        Term.eval cb f cb (Env.code dv kv) :=
    CodeEvalHelpers.eval_recCall_succ hd hk
  -- codeSubst@(f+1) reduces to eval cb (f+1) cb (code dv kv).
  have hsubEq :
      Term.eval cb (f + 1) (codeSubst cb dv kv) Env.empty =
        Term.eval cb (f + 1) cb (Env.code dv kv) :=
    eval_codeSubst cb (f + 1) dv kv
  -- The recCall value `sa` is the `f`-fuel evaluation of the body.
  have hsaBody : Term.eval cb f cb (Env.code dv kv) = some sa := by
    rw [<- hrecEq]; exact hrec
  -- Fuel monotonicity: `sa` entry-refines into the `f+1`-fuel body value `sb`.
  obtain ⟨sb, hsb, hsbmono⟩ :=
    eval_fuel_mono_refines cb f cb (Env.code dv kv) sa hsaBody
  rw [hrec, hsubEq, hsb]
  show stabEqUpTo n sa sb = some true
  clear hrec hrecEq hsubEq hsaBody hsb hd hk
  induction n with
  | zero => rfl
  | succ m ih =>
      have hdefm : forall q, q < m -> exists p, sa q = some p :=
        fun q hq => hdef q (Nat.lt_succ_of_lt hq)
      have ihm := ih hdefm
      obtain ⟨p, hp⟩ := hdef m (Nat.lt_succ_self m)
      simp only [stabEqUpTo, ihm]
      rw [hp, hsbmono m p hp]
      simp

/-! ## Smoke tests -/

/-- A recursive code body that recurses `d` times then returns `X` at qubit `0`,
    `I` elsewhere.  Used to exercise both monotonicity directions. -/
def demoBody : Term 2 .stab :=
  .ite (.eqNat (.var ⟨1, by decide⟩) (.natLit 0))
    (.stabLam
      (.ite (.eqNat (.var ⟨0, by decide⟩) (.natLit 0)) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
    (.recCall (.sub (.var ⟨1, by decide⟩) (.natLit 1)) (.var ⟨0, by decide⟩))

/-- `stabLam` is *not* exact-equality fuel-monotone: at fuel `0` qubit `0` is
    underdefined, at fuel `1` it is `X`.  Witnesses the docstring claim. -/
def underdefinedBody : Term 2 .stab :=
  .stabLam
    (.ite (.eqNat (.var ⟨0, by decide⟩) (.natLit 0)) (.pauliLit Pauli.X) (.pauliLit Pauli.I))

def underdefinedTerm : Term 0 .stab :=
  .stabLam (.stabAt (.recCall (.natLit 7) (.natLit 11)) (.var ⟨0, by decide⟩))

-- fuel 0: entry 0 is `none`; fuel 1: entry 0 is `some X`.  Exact equality fails.
#guard (Term.eval underdefinedBody 0 underdefinedTerm Env.empty).map (fun s => s 0) = some none
#guard (Term.eval underdefinedBody 1 underdefinedTerm Env.empty).map (fun s => s 0)
        = some (some Pauli.X)

-- Entry-wise monotonicity does hold across a fuel step on the demo body.
#guard (do
  let a <- Term.eval demoBody 3 demoBody (Env.code 2 5)
  let b <- Term.eval demoBody 4 demoBody (Env.code 2 5)
  stabEqUpTo 3 a b) = some true

-- codeSubst agrees with evaluating the body under `Env.code`.
#guard (Term.eval demoBody 4 (codeSubst demoBody 2 5) Env.empty).bind (fun s => s 0)
        = (Term.eval demoBody 4 demoBody (Env.code 2 5)).bind (fun s => s 0)

-- Symbolic-argument recUnfold smoke test: `recCall` with *term* arguments
-- (`(2+0)`, `(4+1)`) unfolds to `codeSubst demoBody 2 5` and agrees up to qubit 3.
#guard (do
  let a <- Term.eval demoBody 4
    (.recCall (.add (.natLit 2) (.natLit 0)) (.add (.natLit 4) (.natLit 1))) Env.empty
  let b <- Term.eval demoBody 4 (codeSubst demoBody 2 5) Env.empty
  stabEqUpTo 3 a b) = some true

#print axioms eval_fuel_mono_refines
#print axioms recUnfold_sound
#print axioms recUnfoldT_sound

/-! ## A pure (evaluator-free) family-derivation system

`FamilyDeriv` (CodeStabBinder ~5017) mixes the symbolic logic core
(`SFormula.Deriv`) with an *evaluation*-based leaf (`checkedBoundFree`), whose
soundness is discharged by running the evaluator at proof time and threading a
`check = true` hypothesis.

`PureFamilyDeriv` is the **pure** variant: it has the same shape (a `core`
embedding of `SFormula.Deriv`, plus the structural `cut1..cut4` rules), but it
replaces `checkedBoundFree` by a *logic rule* `recUnfold` whose soundness is the
already-proven semantic lemma `recUnfold_sound`.  Its soundness theorem is
**structural** (induction on the derivation tree) and takes **no** `check = true`
hypothesis: every closed leaf fact is justified by a soundness lemma, never by
executing the evaluator at proof time.

The `recUnfold` constructor produces exactly the `eqStabUpTo` atom whose
`SFormula.eval cb fuel Env.empty E` is the
`do a <- …recCall…; b <- …codeSubst…; stabEqUpTo n a b` shape that
`recUnfold_sound` concludes is `some true`.  The atom is built with the same
`SC.closed` closed-term wrapping used by the `stabAtClosedIteLamEq*` rules. -/

/-- The closed `eqStabUpTo` atom produced by the `recUnfold` rule: it asserts
    that `recCall (lit d) (lit k)` and the unfolded code body `codeSubst cb d k`
    agree on their first `n` qubits.  Wrapping each operand with `SC.closed`
    makes `SFormula.eval`'s `STerm.eval` collapse to `Term.eval`, so the atom's
    evaluation is *definitionally* `recUnfold_sound`'s conclusion. -/
def recUnfoldAtom (cb : Term 2 .stab) (n d k : Nat) : SFormula 0 :=
  .eqStabUpTo (SC.closed (.natLit n))
    (SC.closed (.recCall (.natLit d) (.natLit k)))
    (SC.closed (codeSubst cb d k))

/-- Arity-general symbolic-argument rec-unfold atom.  This is the same rule as
`recUnfoldAtom`, but the recursive-call arguments are arbitrary pure Nat terms in
the current binder environment, and the right-hand side is the code body with
those terms syntactically substituted for `(d,k)`. -/
def recUnfoldAtomA (cb : Term 2 .stab) {arity : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat) : SFormula arity :=
  .eqStabUpTo n
    (SC.closed (.recCall dT kT))
    (SC.closed (codeSubstTerm cb dT kT))

private theorem recUnfoldAtomA_sound {cb : Term 2 .stab} {fuel arity : Nat}
    {n : STerm arity .nat} {dT kT : Term arity .nat}
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT)
    {rho : Env arity} {E : PartialStabilizer} {nv dv kv : Nat}
    (hn : n.eval cb fuel rho E = some nv)
    (hd : Term.eval cb fuel dT rho = some dv)
    (hk : Term.eval cb fuel kT rho = some kv)
    {sa : PartialStabilizer}
    (hrec : Term.eval cb fuel (.recCall dT kT) rho = some sa)
    (hdefEntries : forall q, q < nv -> exists p, sa q = some p) :
    (recUnfoldAtomA cb n dT kT).eval cb fuel rho E = some true := by
  cases fuel with
  | zero =>
      rw [Term.eval] at hrec
      exact absurd hrec (by simp)
  | succ f =>
      have hdAll : forall fuel', Term.eval cb fuel' dT rho = some dv :=
        SFormula.PureNatTerm.eval_all_fuels hdPure hd
      have hkAll : forall fuel', Term.eval cb fuel' kT rho = some kv :=
        SFormula.PureNatTerm.eval_all_fuels hkPure hk
      have hrecStep :
          Term.eval cb (f + 1) (.recCall dT kT) rho =
            Term.eval cb f cb (Env.code dv kv) :=
        CodeEvalHelpers.eval_recCall_succ (hdAll f) (hkAll f)
      have hcbLow : Term.eval cb f cb (Env.code dv kv) = some sa := by
        rw [← hrecStep]
        exact hrec
      obtain ⟨sb, hcbHigh, hrefine⟩ := eval_fuel_mono_stab hcbLow
      have hsubst :
          Term.eval cb (f + 1) (codeSubstTerm cb dT kT) rho = some sb := by
        rw [eval_codeSubstTerm cb (f + 1) dT kT rho hdAll hkAll]
        exact hcbHigh
      simp only [recUnfoldAtomA, SFormula.eval, STerm.eval, SC.closed, Term.eval, hn,
        hrec, hsubst, bind, Option.bind]
      apply stabEqUpTo_complete
      intro q hq
      obtain ⟨p, hp⟩ := hdefEntries q hq
      exact ⟨p, hp, hrefine q p hp⟩

/-! ## A targeted, generic grid index-range rule

The object logic's arithmetic rules (`closedNatLt`, `gridIdxLeftLtSquare`,
`divLtOfLtSquare`, `ltOfLtLtClosedPred`, …) cannot derive the *closed* fact

  `gridRowZStripIndex dist row slot < gridNumStab dist`   (for `row < dist - 1`)

for a symbolic meta-`dist`: `closedNatLt` is literal-only and the grid div/mod
rules do not compose into the strip-index range bound.  This fact is, however,
*unconditionally true* (no oddness, no `dist ≥ 3` side condition) and provable by
pure `Nat` arithmetic over the **kernel** grid functions
(`gridRowZStripIndex`/`gridColXStripIndex`/`gridNumStab`/`gridStripWidth`).

We therefore add a single targeted, *generic* leaf rule (and its column dual),
phrased entirely over the kernel grid functions and parameterised by the meta
`dist` — exactly the granularity of `gridIdxLeftLtSquare`.  It is **not**
Surface-named and **not** an "any-`Nat`-via-`omega`" rule: it asserts only the
specific strip-index range bound, justified by `allNatLt_complete` together with
the omega range lemmas below.
-/

/-- Generic, kernel-level row-strip index-range formula at meta `dist`:
    for every `row < dist - 1` and `slot < gridStripWidth dist`, the
    `gridRowZStripIndex dist row slot` is `< gridNumStab dist`.

    The two bound binders supply `row` (de Bruijn `1`) and `slot` (de Bruijn
    `0`); the witness/body are wrapped exactly as in the corresponding Surface
    leaf, so this formula is definitionally equal to that leaf's body. -/
def gridRowStripRangeF (dist : Nat) : SFormula 0 :=
  .allNatLt (SC.n (dist - 1)) <|
    .allNatLt (SC.n (arity := 1) (SFormula.gridStripWidth dist)) <|
      SFormula.witnessLt
        (SC.closed (SFormula.gridRowZStripIndex dist
          (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩)))
        (SC.n (arity := 2) (SFormula.gridNumStab dist))

/-- Column dual of `gridRowStripRangeF` over `gridColXStripIndex`. -/
def gridColStripRangeF (dist : Nat) : SFormula 0 :=
  .allNatLt (SC.n (dist - 1)) <|
    .allNatLt (SC.n (arity := 1) (SFormula.gridStripWidth dist)) <|
      SFormula.witnessLt
        (SC.closed (SFormula.gridColXStripIndex dist
          (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩)))
        (SC.n (arity := 2) (SFormula.gridNumStab dist))

/-- **Generic row-strip index-range arithmetic.**

The closed-form value of `gridRowZStripIndex dist row slot` (the `ite` tree it
reduces to under `Term.eval`) is `< gridNumStab dist` for every `row < dist - 1`
and any `slot`.  No oddness or lower-bound side condition on `dist` is required.

Bulk slots use the kernel square bound `gridIdxLeft_lt_square`; boundary slots
are linear after bounding the div terms, dispatched by `omega`. -/
theorem gridRowZStripIndex_lt_gridNumStab (dist row slot : Nat)
    (hrow : row < dist - 1) :
    (if slot < (dist - 1) / 2 then
       (if row % 2 = 0 then row * (dist - 1) + 2 * slot
        else row * (dist - 1) + (2 * slot + 1))
     else
       (if row % 2 = 0 then (dist - 1) * (dist - 1) + ((dist - 1) / 2 + row / 2)
        else (dist - 1) * (dist - 1) + (2 * ((dist - 1) / 2) + (row - 1) / 2))) <
      SFormula.gridNumStab dist := by
  have hnum : (dist - 1) * (dist - 1) + 2 * (dist - 1) <= SFormula.gridNumStab dist := by
    simp [SFormula.gridNumStab]
  have hbulkle : (dist - 1) * (dist - 1) <= SFormula.gridNumStab dist :=
    Nat.le_trans (Nat.le_add_right _ _) hnum
  by_cases hs : slot < (dist - 1) / 2
  · have h2 : 2 * slot < dist - 1 := by omega
    have h3 : 2 * slot + 1 < dist - 1 := by omega
    by_cases he : row % 2 = 0
    · simp only [hs, he, if_true]
      exact Nat.lt_of_lt_of_le (by simpa [Nat.mul_comm] using
        NatArithmetic.gridIdxLeft_lt_square hrow h2) hbulkle
    · simp only [hs, he, if_false, if_true]
      exact Nat.lt_of_lt_of_le (by simpa [Nat.mul_comm] using
        NatArithmetic.gridIdxLeft_lt_square hrow h3) hbulkle
  · by_cases he : row % 2 = 0
    · simp only [hs, he, if_false, if_true]
      have hrd : row / 2 < dist - 1 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrow
      omega
    · simp only [hs, he, if_false]
      have hrd : (row - 1) / 2 < dist - 1 :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hrow)
      have hhalf : (dist - 1) / 2 ≤ dist - 1 := Nat.div_le_self _ _
      omega

/-- Column dual of `gridRowZStripIndex_lt_gridNumStab`. -/
theorem gridColXStripIndex_lt_gridNumStab (dist col slot : Nat)
    (hcol : col < dist - 1) :
    (if slot < (dist - 1) / 2 then
       (if col % 2 = 0 then (2 * slot + 1) * (dist - 1) + col
        else (2 * slot) * (dist - 1) + col)
     else
       (if col % 2 = 0 then (dist - 1) * (dist - 1) + col / 2
        else (dist - 1) * (dist - 1) + (3 * ((dist - 1) / 2) + (col - 1) / 2))) <
      SFormula.gridNumStab dist := by
  have hnum : (dist - 1) * (dist - 1) + 2 * (dist - 1) <= SFormula.gridNumStab dist := by
    simp [SFormula.gridNumStab]
  have hbulkle : (dist - 1) * (dist - 1) <= SFormula.gridNumStab dist :=
    Nat.le_trans (Nat.le_add_right _ _) hnum
  by_cases hs : slot < (dist - 1) / 2
  · have h2 : 2 * slot < dist - 1 := by omega
    have h3 : 2 * slot + 1 < dist - 1 := by omega
    by_cases he : col % 2 = 0
    · simp only [hs, he, if_true]
      exact Nat.lt_of_lt_of_le (by simpa [Nat.mul_comm] using
        NatArithmetic.gridIdxLeft_lt_square h3 hcol) hbulkle
    · simp only [hs, he, if_false, if_true]
      exact Nat.lt_of_lt_of_le (by simpa [Nat.mul_comm] using
        NatArithmetic.gridIdxLeft_lt_square h2 hcol) hbulkle
  · by_cases he : col % 2 = 0
    · simp only [hs, he, if_false, if_true]
      have hcd : col / 2 < dist - 1 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hcol
      omega
    · simp only [hs, he, if_false]
      have hcd : (col - 1) / 2 < dist - 1 :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hcol)
      have hhalf : (dist - 1) / 2 ≤ dist - 1 := Nat.div_le_self _ _
      omega

/-- **Soundness of the generic row index-range leaf.**

`gridRowStripRangeF dist` evaluates to `some true` under `SFormula.eval` at any
code body, fuel, and stabilizer placeholder.  The formula is closed and the
witness is `SC.closed`, so the placeholder `E` is irrelevant; the proof reduces
the two bounded binders with `allNatLt_complete` and discharges the per-`(row,
slot)` range bound with `gridRowZStripIndex_lt_gridNumStab`. -/
theorem gridRowStripRangeF_eval (cb : Term 2 .stab) (fuel dist : Nat)
    (E : PartialStabilizer) :
    (gridRowStripRangeF dist).eval cb fuel Env.empty E = some true := by
  simp only [gridRowStripRangeF, SFormula.eval, SFormula.witnessLt, STerm.eval, SC.n,
    SC.b, SC.closed, Term.eval]
  apply allNatLt_complete
  intro row hrow
  apply allNatLt_complete
  intro slot _hslot
  simp only [SFormula.gridRowZStripIndex, Term.eval, Env.cons, bind, Option.bind]
  have hr := gridRowZStripIndex_lt_gridNumStab dist row slot hrow
  by_cases hs : slot < (dist - 1) / 2 <;> by_cases he : row % 2 = 0 <;>
    simp only [hs, he, if_true, if_false, decide_true, decide_false] at hr ⊢ <;>
    simpa using hr

/-- Column dual of `gridRowStripRangeF_eval`. -/
theorem gridColStripRangeF_eval (cb : Term 2 .stab) (fuel dist : Nat)
    (E : PartialStabilizer) :
    (gridColStripRangeF dist).eval cb fuel Env.empty E = some true := by
  simp only [gridColStripRangeF, SFormula.eval, SFormula.witnessLt, STerm.eval, SC.n,
    SC.b, SC.closed, Term.eval]
  apply allNatLt_complete
  intro col hcol
  apply allNatLt_complete
  intro slot _hslot
  simp only [SFormula.gridColXStripIndex, Term.eval, Env.cons, bind, Option.bind]
  have hr := gridColXStripIndex_lt_gridNumStab dist col slot hcol
  by_cases hs : slot < (dist - 1) / 2 <;> by_cases he : col % 2 = 0 <;>
    simp only [hs, he, if_true, if_false, decide_true, decide_false] at hr ⊢ <;>
    simpa using hr

/-! ## A targeted, generic fold-telescoping rule

The lower-bound proof needs the *telescoping* identity for a finite product of
adjacent bridge factors:

  `∏_{i < row} (cut i · cut (i+1))  =  cut 0 · cut row`   (up to the queried prefix)

where `cut : {a} → Term a .nat → STerm a .stab` is a closed kernel stabilizer
*cut family* — a `stabLam` returning a Pauli at each qubit — and the bridge of an
index `i` is `SC.stabMul (cut i) (cut (i+1))`.  This is the same shape the Surface
row/column-cut telescoping leaves have, but phrased here over the **kernel** stab
combinators `SC.stabMul`/`SC.stabFold`/`SC.n` only, with **no** Surface name.

The genuinely generic content is the fold algebra
`partialStabilizerFold m (fun i q => some (cut i q · cut (i+1) q)) = cut 0 · cut m`,
re-derived here from scratch (`local_pauliMulCancelMiddle` +
`partialStabilizerFold_adjacentTelescopes`) so PureDeriv stays self-contained.
The only side condition is that the cut family is *total*: at every index and
qubit it evaluates to `some` of a Pauli.  That totality is what collapses the
inner `Option` binds of the bridge `stabMul` to a pointwise `Pauli.mul`, and it
is what `eqStabUpTo`'s defined-prefix comparison consumes. -/

/-- Pauli cancellation in the middle: `(a·b)·(b·c) = a·c`.  The cancellation that
    makes the adjacent-product fold telescope. -/
private theorem local_pauliMulCancelMiddle (a b c : Pauli) :
    Pauli.mul (Pauli.mul a b) (Pauli.mul b c) = Pauli.mul a c := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **Generic adjacent-product telescoping (semantic core).**

For any *total* Pauli cut family `cut : Nat → Nat → Pauli`, the fold of adjacent
products telescopes to the product of the endpoints:

  `∏_{i < m} (cut i · cut (i+1)) (q) = cut 0 q · cut m q`.

This is the mathematical heart of the telescoping leaf, re-derived generically
inside PureDeriv (independent of any Surface definition) so the rule below is
kernel-only.  Proof: induction on `m`; the successor step is
`local_pauliMulCancelMiddle`. -/
theorem partialStabilizerFold_adjacentTelescopes
    (cut : Nat -> Nat -> Pauli) (m q : Nat) :
    partialStabilizerFold m (fun i q => some (Pauli.mul (cut i q) (cut (i + 1) q))) q =
      some (Pauli.mul (cut 0 q) (cut m q)) := by
  induction m with
  | zero =>
      simp [partialStabilizerFold, partialIdentityStabilizer, Pauli.mul_self]
  | succ j ih =>
      simp [partialStabilizerFold, partialStabilizerMul, ih,
        local_pauliMulCancelMiddle]

/-- The fold-index variable bound by the surrounding `SC.stabFold` (de Bruijn
    `0` at arity `2`: above the `row` binder). -/
def telFoldVar : Term 2 .nat := .var ⟨0, by decide⟩

/-- The outer `row` variable bound by the surrounding `allNatLt` (de Bruijn `0`
    at arity `1`). -/
def telRowVar : Term 1 .nat := .var ⟨0, by decide⟩

/-- A *closed cut family*: a closed kernel stabilizer-term family taking a natural
    index term to a (closed) stabilizer term, at any arity.  Wrapping each cut in
    `SC.closed` (as the bridge/prefix below do) matches the shape of the Surface
    `rowCut`/`colCut`, both of which are `SC.closed (stabLam …)`.  Keeping the cut
    closed makes weakening under the `stabMul`-lambda collapse to `Term`-level
    weakening, so the soundness proof stays kernel-only. -/
abbrev CutFamily := {a : Nat} -> Term a .nat -> Term a .stab

/-- The generic adjacent **bridge** of a closed cut family at index `row`:
    `cut row · cut (row + 1)`, built with the kernel `SC.stabMul` over
    `SC.closed`-wrapped cuts. -/
def telBridge (cut : CutFamily) {a : Nat} (row : Term a .nat) : STerm a .stab :=
  SC.stabMul (SC.closed (cut row)) (SC.closed (cut (.add row (.natLit 1))))

/-- The telescoped **prefix** of a closed cut family: `cut 0 · cut row`. -/
def telPrefix (cut : CutFamily) (row : Term 1 .nat) : STerm 1 .stab :=
  SC.stabMul (SC.closed (cut (.natLit 0))) (SC.closed (cut row))

/-- **Generic fold-telescoping formula**, phrased over kernel stab combinators
    and a closed cut family only:

      `∀ row < outerBound,
         ∏_{i < row} (cut i · cut (i+1))  =_{up to N}  cut 0 · cut row`.

    The left side is `SC.stabFold boundNat (telBridge cut foldVar)`; the right is
    `telPrefix cut row`.  When `cut := rowCutInner D.distance` and
    `outerBound := D.distance`, `N := nQubits D.distance`, this is *definitionally*
    `rowCutTelescopingF D` (and dually for columns). -/
def foldTelescopeF (cut : CutFamily) (outerBound N : Nat) : SFormula 0 :=
  .allNatLt (SC.n outerBound) <|
    .eqStabUpTo (SC.n (arity := 1) N)
      (SC.stabFold SFormula.boundNat (telBridge cut telFoldVar))
      (telPrefix cut telRowVar)

/-- A closed cut term, weakened by one binder and evaluated under any consed
    environment, evaluates exactly as the unweakened cut at the lifted index — the
    `Term`-level weakening collapse for `STerm.closed`.  This is the one weakening
    fact the telescoping soundness needs; it follows from the local generic
    weakening lemma `eval_lift_of_envLifted`. -/
private theorem stermEvalClosedWeaken_cons {a : Nat} {ty : Ty}
    (cb : Term 2 .stab) (fuel : Nat) (E : PartialStabilizer)
    (t : Term a ty) (q : Nat) (rho : Env a) {v : ty.partialDenote}
    (hv : Term.eval cb fuel t rho = some v) :
    STerm.eval cb fuel (STerm.weaken (STerm.closed t)) (Env.cons q rho) E = some v := by
  simp only [STerm.weaken, STerm.lift, STerm.eval]
  rw [eval_lift_of_envLifted t cb fuel (EnvLifted.top rho q)]
  exact hv

/-- **Generic fold-telescoping soundness.**

`foldTelescopeF cut outerBound N` evaluates to `some true` for any code body,
fuel, and stabilizer slot, **provided** the closed cut family is *total*: there
is a total Pauli interpretation `g : Nat → Nat → Pauli` such that, at every index
value `iv`, the cut term evaluates to the everywhere-defined stabilizer
`fun q => some (g iv q)`.

This is the kernel-only generalisation of the Surface telescoping leaf.  The
proof reduces the two binders with `allNatLt_complete`/`stabEqUpTo_complete`,
collapses the bridge `stabMul`'s inner `Option` binds to a pointwise `Pauli.mul`
using totality (the closed cut's weakening collapsing via
`stermEvalClosedWeaken_cons`), then closes with
`partialStabilizerFold_adjacentTelescopes`. -/
theorem foldTelescopeF_eval (cb : Term 2 .stab) (fuel : Nat) (E : PartialStabilizer)
    (cut : CutFamily) (outerBound N : Nat) (g : Nat -> Nat -> Pauli)
    -- the cut at a literal index, inside the fold body (arity-2 env), is total `g`:
    (hcutFold : forall (row iv : Nat),
      Term.eval cb fuel (cut telFoldVar) (Env.cons iv (Env.cons row Env.empty)) =
        some (fun q => some (g iv q)))
    (hcutFoldSucc : forall (row iv : Nat),
      Term.eval cb fuel (cut (.add telFoldVar (.natLit 1)))
          (Env.cons iv (Env.cons row Env.empty)) =
        some (fun q => some (g (iv + 1) q)))
    -- the cut at literal `0` and at the row variable, in the prefix (arity-1 env):
    (hcutZero : forall (row : Nat),
      Term.eval cb fuel (cut (.natLit 0)) (Env.cons row Env.empty) =
        some (fun q => some (g 0 q)))
    (hcutRow : forall (row : Nat),
      Term.eval cb fuel (cut telRowVar) (Env.cons row Env.empty) =
        some (fun q => some (g row q))) :
    (foldTelescopeF cut outerBound N).eval cb fuel Env.empty E = some true := by
  simp only [foldTelescopeF, SFormula.eval, SC.n, STerm.eval, Term.eval]
  apply allNatLt_complete
  intro row _hrow
  -- The `eqStabUpTo` body at this fixed `row`: reduce the leading `some N` bind,
  -- then evaluate the two stabilizer operands `av` (the bridge fold) and `bv`
  -- (the telescoped prefix) to `some` of explicit *total* functions.
  simp only [SFormula.eval, SC.n, STerm.eval, Term.eval, bind, Option.bind]
  -- LHS fold value: `∏_{i<row} (g i · g (i+1))`.
  -- The fold-body function: each index `i` maps to the bridge `g i · g (i+1)`.
  -- Totality of the closed cut (via `stermEvalClosedWeaken_cons`) collapses the
  -- inner `Option` binds of the bridge `stabMul` to this pointwise product.  The
  -- two collapse facts below are stated `∀ i q` so they rewrite *under* the fold
  -- binder; this sidesteps any `match`-motive mismatch.
  have hfoldFst : forall (i q : Nat),
      STerm.eval cb fuel (STerm.weaken (STerm.closed (cut telFoldVar)))
          (Env.cons q (Env.cons i (Env.cons row Env.empty))) E =
        some (fun q => some (g i q)) := fun i q =>
    stermEvalClosedWeaken_cons cb fuel E (cut telFoldVar) q
      (Env.cons i (Env.cons row Env.empty)) (hcutFold row i)
  have hfoldSnd : forall (i q : Nat),
      STerm.eval cb fuel (STerm.weaken (STerm.closed (cut (.add telFoldVar (.natLit 1)))))
          (Env.cons q (Env.cons i (Env.cons row Env.empty))) E =
        some (fun q => some (g (i + 1) q)) := fun i q =>
    stermEvalClosedWeaken_cons cb fuel E (cut (.add telFoldVar (.natLit 1))) q
      (Env.cons i (Env.cons row Env.empty)) (hcutFoldSucc row i)
  have hav :
      STerm.eval cb fuel (SC.stabFold SFormula.boundNat (telBridge cut telFoldVar))
          (Env.cons row Env.empty) E =
        some (fun q => some (Pauli.mul (g 0 q) (g row q))) := by
    simp only [SC.stabFold, telBridge, SC.stabMul, STerm.eval, SFormula.boundNat,
      SC.qVar, SC.closed, Term.eval, Env.cons, bind, Option.bind, hfoldFst, hfoldSnd]
    congr 1
    funext q
    exact partialStabilizerFold_adjacentTelescopes g row q
  -- RHS prefix value: `g 0 · g row`.
  have hbv :
      STerm.eval cb fuel (telPrefix cut telRowVar) (Env.cons row Env.empty) E =
        some (fun q => some (Pauli.mul (g 0 q) (g row q))) := by
    simp only [telPrefix, SC.stabMul, STerm.eval, SC.qVar, SC.closed, Term.eval, Env.cons,
      bind, Option.bind]
    congr 1
    funext q
    rw [stermEvalClosedWeaken_cons cb fuel E (cut (.natLit 0)) q
          (Env.cons row Env.empty) (hcutZero row),
      stermEvalClosedWeaken_cons cb fuel E (cut telRowVar) q
          (Env.cons row Env.empty) (hcutRow row)]
  rw [hav, hbv]
  -- Both operands are now `some` of the same total function; reflexive equality.
  apply stabEqUpTo_complete
  intro q _hq
  exact ⟨Pauli.mul (g 0 q) (g row q), rfl, rfl⟩

#print axioms foldTelescopeF_eval

private theorem partialStabilizerFold_congrUpTo {bound n : Nat}
    {body1 body2 : Nat -> PartialStabilizer}
    (h : forall i, i < bound -> forall q, q < n ->
      exists p, body1 i q = some p /\ body2 i q = some p) :
    forall q, q < n ->
      exists p, partialStabilizerFold bound body1 q = some p /\
        partialStabilizerFold bound body2 q = some p := by
  induction bound with
  | zero =>
      intro q _hq
      exact ⟨Pauli.I, by simp [partialStabilizerFold, partialIdentityStabilizer],
        by simp [partialStabilizerFold, partialIdentityStabilizer]⟩
  | succ m ih =>
      intro q hq
      obtain ⟨pp, hprev1, hprev2⟩ :=
        ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self m))) q hq
      obtain ⟨pr, hrow1, hrow2⟩ := h m (Nat.lt_succ_self m) q hq
      refine ⟨Pauli.mul pp pr, ?_, ?_⟩ <;>
        simp [partialStabilizerFold, partialStabilizerMul, hprev1, hprev2, hrow1, hrow2]

/-! ## Generic disjoint-fold rule

The `foldDisjoint` rule below closes a *bridge = strip-product* leaf of the shape

  `∀ row < outerBound,  lhs(row)  =_{up to N}  ∏_{i < width} body(row, i)`.

This is the generic, Surface-decoupled core behind the Surface
`rowBridgeGenerated`/`colBridgeGenerated` leaves: the LHS `lhs` (a per-row closed
stabilizer term — the two-row `Z`/`X` bridge) equals the finite product over the
`width` strip slots of `body` (the recursive surface-stabilizer entries of the
strip).  The mathematical content is the *disjoint tiling*: the strip's bulk
plaquettes and one boundary stabilizer cover the two-row band with no overlaps, so
the product collapses to the bridge.

As with `foldTelescope`, PureDeriv lives *below* CodeSurface and so cannot mention
`rowBridge`/`surfaceCellPauli`; the geometry is passed entirely through the
soundness side-condition (the totality interpretations `g`/`t` and the
disjoint-union fact relating the *semantic* `partialStabilizerFold` to `t`).  No
`Formula.check`/`Formula.eval`-as-decision is used. -/

/-- **Generic disjoint-fold formula.** `∀ row < outerBound, lhs =_N stabFold width
    body`.  When `lhs := rowBridge D.distance rowVar1`,
    `body := codeRow (rowZStripIndex …)`, `outerBound := D.distance - 1`,
    `width := stripWidth D.distance`, `N := nQubits D.distance`, this is
    *definitionally* `rowBridgeGeneratedEqF D` (dually for columns). -/
def foldDisjointF (lhs : STerm 1 .stab) (body : STerm 2 .stab)
    (outerBound width N : Nat) : SFormula 0 :=
  .allNatLt (SC.n outerBound) <|
    .eqStabUpTo (SC.n (arity := 1) N) lhs (SC.stabFold (SC.n width) body)

/-- Pointwise congruence for the semantic `partialStabilizerFold` (local copy of the
    private `CodeStabBinder` helper). -/
private theorem partialStabilizerFold_pointwiseCongr {n : Nat}
    {body1 body2 : Nat -> PartialStabilizer}
    (h : forall i, body1 i = body2 i) :
    partialStabilizerFold n body1 = partialStabilizerFold n body2 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [partialStabilizerFold, ih, h]

/-- The fold of a totally-defined body collapses to `some` of the semantic
    `partialStabilizerFold` of the pointwise interpretation `g`. -/
private theorem stabFoldEval_total (cb : Term 2 .stab) (fuel : Nat)
    (E : PartialStabilizer) (body : STerm 2 .stab) (width row : Nat)
    (g : Nat -> Nat -> Pauli)
    (hbody : forall (iv : Nat),
      STerm.eval cb fuel body (Env.cons iv (Env.cons row Env.empty)) E =
        some (fun q => some (g iv q))) :
    STerm.eval cb fuel (SC.stabFold (SC.n width) body) (Env.cons row Env.empty) E =
      some (partialStabilizerFold width (fun i => fun q => some (g i q))) := by
  simp only [SC.stabFold, SC.n, STerm.eval, Term.eval, bind, Option.bind]
  congr 1
  apply partialStabilizerFold_pointwiseCongr
  intro i
  rw [hbody i]

/-- **Generic disjoint-fold soundness.**

`foldDisjointF lhs body outerBound width N` evaluates to `some true` for any code
body, fuel, and stabilizer slot, **provided**:

* `lhs` is *total*: at every `row`, it evaluates to the everywhere-defined
  stabilizer `fun q => some (t row q)` (`hlhs`);
* `body` is *total*: at every `(row, iv)`, it evaluates to `fun q => some (g row iv
  q)` (`hbody`);
* the *disjoint-union fact*: at every `(row, q)` the semantic product of the
  `width` strip rows equals the target value `t row q` (`hunion`).  This is the
  `partialStabilizerFold` form — a genuine statement about the semantic fold and
  the interpretations, NOT `Formula.eval`-as-decision.  (The disjoint *tiling* —
  that the strip covers the two-row band with no overlaps — is what the Surface
  instance discharges to produce this fact.)

Proof: reduce the binder with `allNatLt_complete`/`stabEqUpTo_complete`, evaluate
the LHS via `hlhs` and the fold via `stabFoldEval_total` (totality), then equate to
`t` via `hunion`.  This parallels `foldTelescopeF_eval` and `arithBool`'s eval
side-condition. -/
theorem foldDisjointF_eval (cb : Term 2 .stab) (fuel : Nat) (E : PartialStabilizer)
    (lhs : STerm 1 .stab) (body : STerm 2 .stab) (outerBound width N : Nat)
    (g : Nat -> Nat -> Nat -> Pauli) (t : Nat -> Nat -> Pauli)
    (hbody : forall (row iv : Nat),
      STerm.eval cb fuel body (Env.cons iv (Env.cons row Env.empty)) E =
        some (fun q => some (g row iv q)))
    (hlhs : forall (row : Nat),
      STerm.eval cb fuel lhs (Env.cons row Env.empty) E =
        some (fun q => some (t row q)))
    (hunion : forall (row q : Nat),
      partialStabilizerFold width (fun i => fun q => some (g row i q)) q =
        some (t row q)) :
    (foldDisjointF lhs body outerBound width N).eval cb fuel Env.empty E = some true := by
  simp only [foldDisjointF, SFormula.eval, SC.n, STerm.eval, Term.eval]
  apply allNatLt_complete
  intro row _hrow
  -- The `eqStabUpTo` body at this fixed `row`: reduce the leading `some N` bind,
  -- the LHS operand via totality, and the fold operand via `stabFoldEval_total`.
  have hfold := stabFoldEval_total cb fuel E body width row (g row) (hbody row)
  simp only [SC.n] at hfold
  simp only [bind, Option.bind, hlhs row, hfold]
  apply stabEqUpTo_complete
  intro q _hq
  exact ⟨t row q, rfl, hunion row q⟩

#print axioms foldDisjointF_eval

/-! ## Scoped Nat/Bool arithmetic fragment

The `arithBool` pure-family rule below is intentionally narrow.  It can only
close formulas built from Nat/Bool atoms and finite Nat binders.  Every
stabilizer/Pauli atom is rejected at the outer formula level, and every term
constructor that observes or constructs stabilizers/Paulis is rejected
recursively.  Thus the rule can discharge branch guards and index arithmetic,
but it cannot establish commutation, weight, stabilizer equality, or local
Pauli facts.
-/

namespace ArithBoolFragment

def term {arity : Nat} : {ty : Ty} -> Term arity ty -> Bool
  | _, .var _ => true
  | _, .natLit _ => true
  | _, .boolLit _ => true
  | _, .pauliLit _ => false
  | _, .add a b => term a && term b
  | _, .sub a b => term a && term b
  | _, .mul a b => term a && term b
  | _, .div a b => term a && term b
  | _, .mod a b => term a && term b
  | _, .eqNat a b => term a && term b
  | _, .ltNat a b => term a && term b
  | _, .leNat a b => term a && term b
  | _, .not a => term a
  | _, .and a b => term a && term b
  | _, .or a b => term a && term b
  | _, .ite c t e => term c && term t && term e
  | _, .pauliMul _ _ => false
  | _, .anticommutes _ _ => false
  | _, .stabLam _ => false
  | _, .stabAt _ _ => false
  | _, .stabFold _ _ => false
  | _, .recCall _ _ => false

def sterm {arity : Nat} : {ty : Ty} -> STerm arity ty -> Bool
  | _, .closed t => term t
  | _, .boundStab => false
  | _, .ite c t e => sterm c && sterm t && sterm e
  | _, .pauliMul _ _ => false
  | _, .anticommutes _ _ => false
  | _, .ltNat a b => sterm a && sterm b
  | _, .stabLam _ => false
  | _, .stabAt _ _ => false
  | _, .stabFold _ _ => false
  | _, .applyNat witness body => sterm witness && sterm body

def formula {arity : Nat} : SFormula arity -> Bool
  | .top => true
  | .bot => true
  | .eqNat a b => sterm a && sterm b
  | .eqBool a b => sterm a && sterm b
  | .eqPauli _ _ => false
  | .eqStabUpTo _ _ _ => false
  | .commutesUpTo _ _ _ => false
  | .weightLe _ _ _ => false
  | .and A B => formula A && formula B
  | .or A B => formula A && formula B
  | .not A => formula A
  | .imp A B => formula A && formula B
  | .applyNat witness A => sterm witness && formula A
  | .allNatLt n A => sterm n && formula A
  | .existsNatLt n A => sterm n && formula A

end ArithBoolFragment

/-- Structural gate for the scoped Nat/Bool arithmetic decision rule. -/
def arithBoolFragment {arity : Nat} (A : SFormula arity) : Bool :=
  ArithBoolFragment.formula A

/-! ## Support-cover upper bound on Hamming weight

Dual to the lower-bound cardinality lemmas in `CodeStabBinder`
(`weight_not_le_of_surjective_support`): an *upper* bound on the weight is
witnessed by exhibiting a cover of the support by `w` index positions.  If every
support coordinate `q < n` (i.e. `nonIBool E q = true`) is hit by some
`cover i` with `i < w`, then the support has at most `w` elements, hence
`weightUpTo n E = some v` forces `v ≤ w`. -/
theorem weight_le_of_support_cover {n w v : Nat} {E : PartialStabilizer}
    {cover : Nat -> Nat}
    (hcover : forall q, q < n -> SFormula.nonIBool E q = true ->
      exists i, i < w /\ cover i = q)
    (hweight : weightUpTo n E = some v) : v <= w := by
  have hv : v = (SFormula.supportSet n E).card :=
    SFormula.weightUpTo_eq_supportSet_card hweight
  have hsub :
      SFormula.supportSet n E ⊆
        Finset.image (fun i => cover i) (Finset.range w) := by
    intro q hq
    have hqmem : q ∈ Finset.range n ∧ SFormula.nonIBool E q = true := by
      simpa [SFormula.supportSet, Finset.mem_filter] using hq
    obtain ⟨i, hiLt, hicover⟩ :=
      hcover q (Finset.mem_range.mp hqmem.1) hqmem.2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hiLt, hicover⟩
  calc v = (SFormula.supportSet n E).card := hv
    _ ≤ (Finset.image (fun i => cover i) (Finset.range w)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range w).card := Finset.card_image_le
    _ = w := Finset.card_range w

/-! ## Arity-general pure family derivations

This layer is a generic sibling of the closed `PureFamilyDeriv` below.  It lets
non-logical pure leaves, such as symbolic recursion-unfolding, appear underneath
ordinary natural binders.  The soundness theorem is structural and quantified by
an arbitrary environment `rho`; no evaluator/checker Boolean is used as a leaf. -/

/-- Body of the support-cover premise.  Under the current bounded support index
    `q` (top variable), every support position must be hit by `cover`:
    `nonI(E,q) -> exists i < w, cover(i) = q`.  In the inner existential body the
    de Bruijn layout matches `supportSurjectiveBody`: `boundNat (arity+1)` is the
    inner index `i`, `cover.lift 1` reads that `i` (with `q` inserted below it),
    and `(boundNat arity).weaken` is the outer support index `q`. -/
def supportCoveredBody {arity : Nat}
    (E : STerm arity .stab) (w : STerm arity .nat)
    (cover : STerm (arity + 1) .nat) : SFormula (arity + 1) :=
  .imp (SFormula.nonIAt E.weaken SFormula.boundNat)
    (.existsNatLt w.weaken
      (.eqNat (cover.lift 1) ((SFormula.boundNat (arity := arity)).weaken)))

/-- The support-cover premise: for every support position `q < n`, there exists
    an index `i < w` with `cover(i) = q`.  Witnessing this forces the Hamming
    weight to be at most `w` (cf. `weight_le_of_support_cover`). -/
def supportCoveredF {arity : Nat}
    (n : STerm arity .nat) (E : STerm arity .stab) (w : STerm arity .nat)
    (cover : STerm (arity + 1) .nat) : SFormula arity :=
  .allNatLt n (supportCoveredBody E w cover)

/-- The cover antecedent `nonIAt E.weaken boundNat`, evaluated at the bound
    support index `q`, is `some true` exactly when `nonIBool Ev q = true`. -/
private theorem nonIAt_weaken_boundNat_eval_true {arity : Nat}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {Eterm : STerm arity .stab} {q : Nat} {Ev : PartialStabilizer}
    (hE : Eterm.eval cb fuel rho E = some Ev)
    (hNonI : SFormula.nonIBool Ev q = true) :
    SFormula.eval cb fuel (SFormula.nonIAt Eterm.weaken SFormula.boundNat)
        (Env.cons q rho) E = some true := by
  have hEw : Eterm.weaken.eval cb fuel (Env.cons q rho) E = some Ev := by
    rw [STerm.eval_weaken_top Eterm cb fuel q rho E, hE]
  have hEvq : exists p, Ev q = some p ∧ p ≠ Pauli.I := by
    unfold SFormula.nonIBool at hNonI
    cases hq : Ev q with
    | none => rw [hq] at hNonI; simp at hNonI
    | some p =>
        rw [hq] at hNonI
        exact ⟨p, rfl, by simpa using hNonI⟩
  obtain ⟨p, hp, hpNe⟩ := hEvq
  have hQindex :
      (SFormula.boundNat (arity := arity)).eval cb fuel (Env.cons q rho) E = some q := by
    simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval]
    rfl
  simp [SFormula.nonIAt, SFormula.eval, SC.p, STerm.eval, Term.eval,
    hEw, hQindex, hp, hpNe]

/-- Extraction lemma for the support-cover body.  If the body holds at the
    support index `q < nv` and `q` is actually a support position
    (`nonIBool Ev q = true`), then there is an index `i < wv` whose `cover`
    value equals `q`. -/
private theorem supportCoveredBody_eval_true {arity : Nat}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {Eterm : STerm arity .stab} {w : STerm arity .nat}
    {cover : STerm (arity + 1) .nat} {q wv : Nat} {Ev : PartialStabilizer}
    (h : SFormula.eval cb fuel (supportCoveredBody Eterm w cover)
        (Env.cons q rho) E = some true)
    (hw : w.eval cb fuel rho E = some wv)
    (hE : Eterm.eval cb fuel rho E = some Ev)
    (hNonI : SFormula.nonIBool Ev q = true) :
    exists i, i < wv /\
      cover.eval cb fuel (Env.cons i rho) E = some q := by
  have hAnte :=
    nonIAt_weaken_boundNat_eval_true (cb := cb) (fuel := fuel) (rho := rho)
      (E := E) (Eterm := Eterm) (q := q) (Ev := Ev) hE hNonI
  -- Peel the implication: antecedent true => consequent (the inner existential).
  have hwW : w.weaken.eval cb fuel (Env.cons q rho) E = some wv := by
    rw [STerm.eval_weaken_top w cb fuel q rho E, hw]
  simp only [supportCoveredBody, SFormula.eval, hAnte] at h
  simp only [hwW] at h
  -- Now `h` is the inner `existsNatLt wv (eqNat cover q)` evaluating to true.
  rcases existsNatLt_sound h with ⟨i, hiLt, hBody⟩
  refine ⟨i, hiLt, ?_⟩
  -- Decode the `.eqNat (cover.lift 1) (boundNat.weaken)` body at `Env.cons i (Env.cons q rho)`.
  have hCoverLift :
      (cover.lift 1).eval cb fuel (Env.cons i (Env.cons q rho)) E =
        cover.eval cb fuel (Env.cons i rho) E := by
    have hbase : EnvLifted 1 (Env.cons i rho) (Env.cons i (Env.cons q rho)) :=
      EnvLifted.underBinder (EnvLifted.top rho q) i
    exact STerm.eval_lift_of_envLifted cover hbase cb fuel E
  have hQindex :
      ((SFormula.boundNat (arity := arity)).weaken).eval cb fuel
        (Env.cons i (Env.cons q rho)) E = some q := by
    have hbase :
        (SFormula.boundNat (arity := arity)).eval cb fuel (Env.cons q rho) E =
          some q := by
      simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval]
      rfl
    rw [STerm.eval_weaken_top (SFormula.boundNat (arity := arity)) cb fuel i
      (Env.cons q rho) E, hbase]
  simp only [hCoverLift, hQindex] at hBody
  cases hCov : cover.eval cb fuel (Env.cons i rho) E with
  | none => rw [hCov] at hBody; simp at hBody
  | some cv =>
      rw [hCov] at hBody
      simp only [bind, Option.bind, Option.some.injEq, decide_eq_true_eq] at hBody
      rw [hBody]

inductive PureFamilyDerivA (cb : Term 2 .stab) (fuel : Nat) :
    {arity : Nat} -> SFormula arity -> Type where
  | core {arity : Nat} {A : SFormula arity} :
      SFormula.Deriv [] A -> PureFamilyDerivA cb fuel A
  | recUnfold {arity : Nat}
      (n : STerm arity .nat) (dT kT : Term arity .nat)
      (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT) :
      PureFamilyDerivA cb fuel (recUnfoldAtomA cb n dT kT)
  | allNatLtIntro {arity : Nat} (n : STerm arity .nat) {A : SFormula (arity + 1)} :
      PureFamilyDerivA cb fuel A -> PureFamilyDerivA cb fuel (.allNatLt n A)
  | foldCongr {arity : Nat}
      (n bound : STerm arity .nat) (body1 body2 : STerm (arity + 1) .stab) :
      PureFamilyDerivA cb fuel (.allNatLt bound (.eqStabUpTo n.weaken body1 body2)) ->
        PureFamilyDerivA cb fuel
          (.eqStabUpTo n (SC.stabFold bound body1) (SC.stabFold bound body2))
  | eqStabOfPointwiseEq {arity : Nat}
      (n : STerm arity .nat) (A B : STerm arity .stab) :
      PureFamilyDerivA cb fuel
        (.allNatLt n
          (.eqPauli
            (.stabAt A.weaken SFormula.boundNat)
            (.stabAt B.weaken SFormula.boundNat))) ->
        PureFamilyDerivA cb fuel (.eqStabUpTo n A B)
  | arithBool {arity : Nat} (A : SFormula arity) :
      arithBoolFragment A = true ->
        (forall (rho : Env arity) (E : PartialStabilizer),
          A.eval cb fuel rho E = some true) ->
          PureFamilyDerivA cb fuel A
  | iteSelectThen {arity : Nat}
      (n : STerm arity .nat) (cond : Term arity .bool) (S1 S2 : Term arity .stab) :
      PureFamilyDerivA cb fuel (.eqBool (SC.closed cond) (SC.b true)) ->
        PureFamilyDerivA cb fuel
          (.eqStabUpTo n (SC.closed (.ite cond S1 S2)) (SC.closed S1))
  | iteSelectElse {arity : Nat}
      (n : STerm arity .nat) (cond : Term arity .bool) (S1 S2 : Term arity .stab) :
      PureFamilyDerivA cb fuel (.eqBool (SC.closed cond) (SC.b false)) ->
        PureFamilyDerivA cb fuel
          (.eqStabUpTo n (SC.closed (.ite cond S1 S2)) (SC.closed S2))
  | eqPauliProj {arity : Nat}
      (n : STerm arity .nat) (A B : STerm arity .stab) (q : STerm arity .nat) :
      PureFamilyDerivA cb fuel (.eqStabUpTo n A B) ->
        PureFamilyDerivA cb fuel (.eqPauli (.stabAt A q) (.stabAt B q))
  | eqPauliRefl {arity : Nat} (a : STerm arity .pauli) :
      PureFamilyDerivA cb fuel (.eqPauli a a)
  | eqPauliSymm {arity : Nat} (a b : STerm arity .pauli) :
      PureFamilyDerivA cb fuel (.eqPauli a b) ->
        PureFamilyDerivA cb fuel (.eqPauli b a)
  | eqPauliTrans {arity : Nat} (a b c : STerm arity .pauli) :
      PureFamilyDerivA cb fuel (.eqPauli a b) ->
        PureFamilyDerivA cb fuel (.eqPauli b c) ->
          PureFamilyDerivA cb fuel (.eqPauli a c)
  | pauliIteSelectThen {arity : Nat}
      (cond : Term arity .bool) (p1 p2 : Term arity .pauli) :
      PureFamilyDerivA cb fuel (.eqBool (SC.closed cond) (SC.b true)) ->
        PureFamilyDerivA cb fuel
          (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p1))
  | pauliIteSelectElse {arity : Nat}
      (cond : Term arity .bool) (p1 p2 : Term arity .pauli) :
      PureFamilyDerivA cb fuel (.eqBool (SC.closed cond) (SC.b false)) ->
        PureFamilyDerivA cb fuel
          (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p2))
  | closedStabAtSplit {arity : Nat} (s : Term arity .stab) (q : Term arity .nat) :
      PureFamilyDerivA cb fuel
        (.eqPauli (SC.closed (.stabAt s q)) (.stabAt (SC.closed s) (SC.closed q)))
  | weightLeBySupport {arity : Nat}
      (n : STerm arity .nat) (E : STerm arity .stab) (w : STerm arity .nat)
      (cover : STerm (arity + 1) .nat) :
      PureFamilyDerivA cb fuel (supportCoveredF n E w cover) ->
        PureFamilyDerivA cb fuel (.weightLe n E w)
  | cut1 {arity : Nat} {A B : SFormula arity} :
      SFormula.Deriv [A] B ->
        PureFamilyDerivA cb fuel A ->
          PureFamilyDerivA cb fuel B
  | cut2 {arity : Nat} {A B C : SFormula arity} :
      SFormula.Deriv [A, B] C ->
        PureFamilyDerivA cb fuel A ->
          PureFamilyDerivA cb fuel B ->
            PureFamilyDerivA cb fuel C

namespace PureFamilyDerivA

def size {cb : Term 2 .stab} {fuel arity : Nat} {A : SFormula arity} :
    PureFamilyDerivA cb fuel A -> Nat
  | .core D => 1 + D.size
  | .recUnfold _ _ _ _ _ => 1
  | .allNatLtIntro _ child => 1 + size child
  | .foldCongr _ _ _ _ child => 1 + size child
  | .eqStabOfPointwiseEq _ _ _ child => 1 + size child
  | .arithBool _ _ _ => 1
  | .iteSelectThen _ _ _ _ child => 1 + size child
  | .iteSelectElse _ _ _ _ child => 1 + size child
  | .eqPauliProj _ _ _ _ child => 1 + size child
  | .eqPauliRefl _ => 1
  | .eqPauliSymm _ _ child => 1 + size child
  | .eqPauliTrans _ _ _ child1 child2 => 1 + size child1 + size child2
  | .pauliIteSelectThen _ _ _ child => 1 + size child
  | .pauliIteSelectElse _ _ _ child => 1 + size child
  | .closedStabAtSplit _ _ => 1
  | .weightLeBySupport _ _ _ _ child => 1 + size child
  | .cut1 D hA => 1 + D.size + size hA
  | .cut2 D hA hB => 1 + D.size + size hA + size hB

def DefinedObligations {cb : Term 2 .stab} {fuel arity : Nat} {A : SFormula arity}
    (D : PureFamilyDerivA cb fuel A) (rho : Env arity) (E : PartialStabilizer) :
    Prop :=
  match D with
  | .core Dcore => Dcore.DefinedObligations cb fuel rho E
  | .recUnfold n dT kT _ _ =>
      exists nv dv kv sa,
        n.eval cb fuel rho E = some nv /\
          Term.eval cb fuel dT rho = some dv /\
            Term.eval cb fuel kT rho = some kv /\
              Term.eval cb fuel (.recCall dT kT) rho = some sa /\
                forall q, q < nv -> exists p, sa q = some p
  | .allNatLtIntro n child =>
      exists bound, n.eval cb fuel rho E = some bound /\
        forall x, x < bound -> DefinedObligations child (Env.cons x rho) E
  | .foldCongr n bound _ _ child =>
      exists nv bv, n.eval cb fuel rho E = some nv /\
        bound.eval cb fuel rho E = some bv /\ DefinedObligations child rho E
  | .eqStabOfPointwiseEq n A B child =>
      exists nv Av Bv,
        n.eval cb fuel rho E = some nv /\
          A.eval cb fuel rho E = some Av /\
            B.eval cb fuel rho E = some Bv /\
              DefinedObligations child rho E
  | .arithBool _ _ _ => True
  | .iteSelectThen n _ S1 _ child =>
      exists nv s1, n.eval cb fuel rho E = some nv /\
        DefinedObligations child rho E /\
          Term.eval cb fuel S1 rho = some s1 /\
            forall q, q < nv -> exists p, s1 q = some p
  | .iteSelectElse n _ _ S2 child =>
      exists nv s2, n.eval cb fuel rho E = some nv /\
        DefinedObligations child rho E /\
          Term.eval cb fuel S2 rho = some s2 /\
            forall q, q < nv -> exists p, s2 q = some p
  | .eqPauliProj n _ _ q child =>
      exists nv qv, n.eval cb fuel rho E = some nv /\
        q.eval cb fuel rho E = some qv /\ qv < nv /\
          DefinedObligations child rho E
  | .eqPauliRefl a =>
      exists av, a.eval cb fuel rho E = some av
  | .eqPauliSymm _ _ child =>
      DefinedObligations child rho E
  | .eqPauliTrans _ _ _ child1 child2 =>
      DefinedObligations child1 rho E /\ DefinedObligations child2 rho E
  | .pauliIteSelectThen _ p1 _ child =>
      DefinedObligations child rho E /\
        exists pv, Term.eval cb fuel p1 rho = some pv
  | .pauliIteSelectElse _ _ p2 child =>
      DefinedObligations child rho E /\
        exists pv, Term.eval cb fuel p2 rho = some pv
  | .closedStabAtSplit s q =>
      exists pv, Term.eval cb fuel (.stabAt s q) rho = some pv
  | .weightLeBySupport n Eterm w _ child =>
      exists nv Ev wv,
        n.eval cb fuel rho E = some nv /\
          Eterm.eval cb fuel rho E = some Ev /\
            w.eval cb fuel rho E = some wv /\
              (exists v, weightUpTo nv Ev = some v) /\
                DefinedObligations child rho E
  | .cut1 Dcore hA =>
      Dcore.DefinedObligations cb fuel rho E /\ DefinedObligations hA rho E
  | .cut2 Dcore hA hB =>
      Dcore.DefinedObligations cb fuel rho E /\
        DefinedObligations hA rho E /\ DefinedObligations hB rho E

theorem sound {cb : Term 2 .stab} {fuel arity : Nat} {A : SFormula arity}
    (D : PureFamilyDerivA cb fuel A) :
    forall (rho : Env arity) (E : PartialStabilizer),
      DefinedObligations D rho E -> A.eval cb fuel rho E = some true := by
  induction D with
  | core Dcore =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      exact Dcore.sound hdef (fun B hmem => by cases hmem)
  | recUnfold n dT kT hdPure hkPure =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨nv, dv, kv, sa, hn, hd, hk, hrec, hentries⟩ := hdef
      exact recUnfoldAtomA_sound hdPure hkPure hn hd hk hrec hentries
  | allNatLtIntro n child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨bound, hn, hbody⟩ := hdef
      simp only [SFormula.eval, hn, bind, Option.bind]
      exact allNatLt_complete fun x hx => ih (Env.cons x rho) E (hbody x hx)
  | foldCongr n bound body1 body2 child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨nv, bv, hn, hbound, hchildDef⟩ := hdef
      have hchildEval := ih rho E hchildDef
      simp only [SFormula.eval, hbound, bind, Option.bind] at hchildEval
      have hrows :
          forall i, i < bv -> forall q, q < nv ->
            exists p,
              (match STerm.eval cb fuel body1 (Env.cons i rho) E with
                | some row => row
                | none => fun _ => none) q = some p /\
              (match STerm.eval cb fuel body2 (Env.cons i rho) E with
                | some row => row
                | none => fun _ => none) q = some p := by
        intro i hi q hq
        have hpoint := allNatLt_sound hchildEval i hi
        have hnW : STerm.eval cb fuel n.weaken (Env.cons i rho) E = some nv := by
          rw [STerm.eval_weaken_top n cb fuel i rho E, hn]
        simp only [SFormula.eval, hnW, bind, Option.bind] at hpoint
        cases hbody1 : STerm.eval cb fuel body1 (Env.cons i rho) E with
        | none =>
            simp [hbody1] at hpoint
        | some row1 =>
            cases hbody2 : STerm.eval cb fuel body2 (Env.cons i rho) E with
            | none =>
                simp [hbody1, hbody2] at hpoint
            | some row2 =>
                have hstab : stabEqUpTo nv row1 row2 = some true := by
                  simpa [hbody1, hbody2] using hpoint
                exact stabEqUpTo_sound hstab q hq
      simp only [SFormula.eval, SC.stabFold, STerm.eval, hn, hbound, bind, Option.bind]
      apply stabEqUpTo_complete
      intro q hq
      exact partialStabilizerFold_congrUpTo hrows q hq
  | eqStabOfPointwiseEq n A B child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨nv, Av, Bv, hn, hA, hB, hchildDef⟩ := hdef
      have hchildEval := ih rho E hchildDef
      simp only [SFormula.eval, bind, Option.bind] at hchildEval ⊢
      simp only [hn, hA, hB, bind, Option.bind] at hchildEval ⊢
      apply stabEqUpTo_complete
      intro q hq
      have hpoint := allNatLt_sound hchildEval q hq
      simp only [SFormula.eval, STerm.eval, SFormula.boundNat, SC.closed,
        Term.eval, Env.cons, bind, Option.bind] at hpoint
      have hAw :
          STerm.eval cb fuel A.weaken (Env.cons q rho) E = some Av := by
        rw [STerm.eval_weaken_top A cb fuel q rho E, hA]
      have hBw :
          STerm.eval cb fuel B.weaken (Env.cons q rho) E = some Bv := by
        rw [STerm.eval_weaken_top B cb fuel q rho E, hB]
      simp only [hAw, hBw, bind, Option.bind] at hpoint
      cases hAvq : Av q with
      | none =>
          simp [hAvq] at hpoint
      | some pA =>
          cases hBvq : Bv q with
          | none =>
              simp [hAvq, hBvq] at hpoint
          | some pB =>
              simp [hAvq, hBvq] at hpoint
              refine ⟨pA, rfl, ?_⟩
              simpa [hpoint] using hBvq
  | arithBool A hFrag hValid =>
      intro rho E _hdef
      exact hValid rho E
  | iteSelectThen n cond S1 S2 child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨nv, s1, hn, hchildDef, hS1, hS1def⟩ := hdef
      have hchildEval := ih rho E hchildDef
      have hcond : Term.eval cb fuel cond rho = some true := by
        simp only [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, bind,
          Option.bind] at hchildEval
        cases hc : Term.eval cb fuel cond rho with
        | none => simp [hc] at hchildEval
        | some cv =>
            simp [hc] at hchildEval
            rw [hchildEval]
      simp only [SFormula.eval, SC.closed, STerm.eval, Term.eval, hn, hcond, hS1,
        if_true, bind, Option.bind]
      apply stabEqUpTo_complete
      intro q hq
      obtain ⟨p, hp⟩ := hS1def q hq
      exact ⟨p, hp, hp⟩
  | iteSelectElse n cond S1 S2 child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨nv, s2, hn, hchildDef, hS2, hS2def⟩ := hdef
      have hchildEval := ih rho E hchildDef
      have hcond : Term.eval cb fuel cond rho = some false := by
        simp only [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, bind,
          Option.bind] at hchildEval
        cases hc : Term.eval cb fuel cond rho with
        | none => simp [hc] at hchildEval
        | some cv =>
            simp [hc] at hchildEval
            rw [hchildEval]
      simp only [SFormula.eval, SC.closed, STerm.eval, Term.eval, hn, hcond, hS2,
        if_false, bind, Option.bind]
      apply stabEqUpTo_complete
      intro q hq
      obtain ⟨p, hp⟩ := hS2def q hq
      exact ⟨p, hp, hp⟩
  | eqPauliProj n A B q child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨nv, qv, hn, hq, hqlt, hchildDef⟩ := hdef
      have hchild := ih rho E hchildDef
      simp only [SFormula.eval, hn, bind, Option.bind] at hchild
      cases hA : STerm.eval cb fuel A rho E with
      | none => simp [hA] at hchild
      | some sa =>
          cases hB : STerm.eval cb fuel B rho E with
          | none => simp [hA, hB] at hchild
          | some sb =>
              simp only [hA, hB] at hchild
              obtain ⟨p, hsa, hsb⟩ := stabEqUpTo_sound hchild qv hqlt
              simp [SFormula.eval, STerm.eval, hA, hB, hq, hsa, hsb]
  | eqPauliRefl a =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨av, ha⟩ := hdef
      simp [SFormula.eval, ha]
  | eqPauliSymm a b child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      have hchild := ih rho E hdef
      simp only [SFormula.eval, bind, Option.bind] at hchild ⊢
      cases ha : STerm.eval cb fuel a rho E with
      | none => simp [ha] at hchild
      | some av =>
          cases hb : STerm.eval cb fuel b rho E with
          | none => simp [ha, hb] at hchild
          | some bv =>
              simp only [ha, hb] at hchild ⊢
              have e : av = bv := by simpa using hchild
              subst e
              simp
  | eqPauliTrans a b c child1 child2 ih1 ih2 =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨hdef1, hdef2⟩ := hdef
      have h1 := ih1 rho E hdef1
      have h2 := ih2 rho E hdef2
      simp only [SFormula.eval, bind, Option.bind] at h1 h2 ⊢
      cases ha : STerm.eval cb fuel a rho E with
      | none => simp [ha] at h1
      | some av =>
          cases hb : STerm.eval cb fuel b rho E with
          | none => simp [ha, hb] at h1
          | some bv =>
              cases hc : STerm.eval cb fuel c rho E with
              | none => simp [hb, hc] at h2
              | some cv =>
                  simp only [ha, hb] at h1
                  simp only [hb, hc] at h2
                  have e1 : av = bv := by simpa using h1
                  have e2 : bv = cv := by simpa using h2
                  subst e1; subst e2; simp
  | pauliIteSelectThen cond p1 p2 child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨hchildDef, pv, hp1⟩ := hdef
      have hchildEval := ih rho E hchildDef
      have hcond : Term.eval cb fuel cond rho = some true := by
        simp only [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, bind,
          Option.bind] at hchildEval
        cases hc : Term.eval cb fuel cond rho with
        | none => simp [hc] at hchildEval
        | some cv =>
            simp [hc] at hchildEval
            rw [hchildEval]
      simp [SFormula.eval, SC.closed, STerm.eval, Term.eval, hcond, hp1]
  | pauliIteSelectElse cond p1 p2 child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨hchildDef, pv, hp2⟩ := hdef
      have hchildEval := ih rho E hchildDef
      have hcond : Term.eval cb fuel cond rho = some false := by
        simp only [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, bind,
          Option.bind] at hchildEval
        cases hc : Term.eval cb fuel cond rho with
        | none => simp [hc] at hchildEval
        | some cv =>
            simp [hc] at hchildEval
            rw [hchildEval]
      simp [SFormula.eval, SC.closed, STerm.eval, Term.eval, hcond, hp2]
  | closedStabAtSplit s q =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨pv, hp⟩ := hdef
      simp only [SFormula.eval, SC.closed, STerm.eval, Term.eval, bind, Option.bind] at hp ⊢
      cases hs : Term.eval cb fuel s rho with
      | none => simp [hs] at hp
      | some sv =>
          cases hq : Term.eval cb fuel q rho with
          | none => simp [hs, hq] at hp
          | some qv =>
              simp only [hs, hq] at hp ⊢
              rw [hp]
              simp
  | weightLeBySupport n Eterm w cover child ih =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      obtain ⟨nv, Ev, wv, hn, hEterm, hw, ⟨v, hWeight⟩, hchildDef⟩ := hdef
      have hchildEval := ih rho E hchildDef
      simp only [supportCoveredF, SFormula.eval, hn, bind, Option.bind] at hchildEval
      -- Reconstruct the cover function used by the cardinality lemma.
      let coverFn : Nat -> Nat := fun i =>
        match STerm.eval cb fuel cover (Env.cons i rho) E with
        | some c => c
        | none => 0
      have hcover :
          forall q, q < nv -> SFormula.nonIBool Ev q = true ->
            exists i, i < wv /\ coverFn i = q := by
        intro q hqLt hNonI
        have hBody := allNatLt_sound hchildEval q hqLt
        obtain ⟨i, hiLt, hcov⟩ :=
          supportCoveredBody_eval_true (cb := cb) (fuel := fuel) (rho := rho)
            (E := E) (Eterm := Eterm) (w := w) (cover := cover) (q := q)
            (wv := wv) (Ev := Ev) hBody hw hEterm hNonI
        exact ⟨i, hiLt, by simp only [coverFn, hcov]⟩
      have hVle : v <= wv :=
        weight_le_of_support_cover (n := nv) (w := wv) (v := v) (E := Ev)
          (cover := coverFn) hcover hWeight
      simp only [SFormula.eval, hn, hEterm, hw, hWeight, bind, Option.bind]
      simp [hVle]
  | cut1 Dcore hA ihA =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      rcases hdef with ⟨hcoreDef, hADef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA rho E hADef
          | tail _ htail => cases htail)
  | cut2 Dcore hA hB ihA ihB =>
      intro rho E hdef
      simp only [DefinedObligations] at hdef
      rcases hdef with ⟨hcoreDef, hADef, hBDef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA rho E hADef
          | tail _ htail =>
              cases htail with
              | head => exact ihB rho E hBDef
              | tail _ hnil => cases hnil)

end PureFamilyDerivA

/-- **Pure family derivations.**

A derivation tree over closed formulas whose only non-logical leaf is the
recursion-unfold rule `recUnfold`.  No `checkedBoundFree`, no evaluator leaf. -/
inductive PureFamilyDeriv (cb : Term 2 .stab) (fuel : Nat) :
    SFormula 0 -> Type where
  | arity0 {A : SFormula 0} :
      PureFamilyDerivA cb fuel A -> PureFamilyDeriv cb fuel A
  | core {A : SFormula 0} :
      SFormula.Deriv [] A -> PureFamilyDeriv cb fuel A
  | recUnfold (n d k : Nat) :
      PureFamilyDeriv cb fuel (recUnfoldAtom cb n d k)
  | gridRowStripRange (dist : Nat) :
      PureFamilyDeriv cb fuel (gridRowStripRangeF dist)
  | gridColStripRange (dist : Nat) :
      PureFamilyDeriv cb fuel (gridColStripRangeF dist)
  | foldTelescope (cut : CutFamily) (outerBound N : Nat) :
      PureFamilyDeriv cb fuel (foldTelescopeF cut outerBound N)
  | foldDisjoint (lhs : STerm 1 .stab) (body : STerm 2 .stab)
      (outerBound width N : Nat) :
      PureFamilyDeriv cb fuel (foldDisjointF lhs body outerBound width N)
  | cut1 {A B : SFormula 0} :
      SFormula.Deriv [A] B ->
        PureFamilyDeriv cb fuel A ->
          PureFamilyDeriv cb fuel B
  | cut2 {A B C : SFormula 0} :
      SFormula.Deriv [A, B] C ->
        PureFamilyDeriv cb fuel A ->
          PureFamilyDeriv cb fuel B ->
            PureFamilyDeriv cb fuel C
  | cut3 {A B C D : SFormula 0} :
      SFormula.Deriv [A, B, C] D ->
        PureFamilyDeriv cb fuel A ->
          PureFamilyDeriv cb fuel B ->
            PureFamilyDeriv cb fuel C ->
              PureFamilyDeriv cb fuel D
  | cut4 {A B C D E : SFormula 0} :
      SFormula.Deriv [A, B, C, D] E ->
        PureFamilyDeriv cb fuel A ->
          PureFamilyDeriv cb fuel B ->
            PureFamilyDeriv cb fuel C ->
              PureFamilyDeriv cb fuel D ->
                PureFamilyDeriv cb fuel E

namespace PureFamilyDeriv

/-- Structural size, mirroring `FamilyDeriv.size`. -/
def size {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0} :
    PureFamilyDeriv cb fuel A -> Nat
  | .arity0 D => 1 + PureFamilyDerivA.size D
  | .core D => 1 + D.size
  | .recUnfold _ _ _ => 1
  | .gridRowStripRange _ => 1
  | .gridColStripRange _ => 1
  | .foldTelescope _ _ _ => 1
  | .foldDisjoint _ _ _ _ _ => 1
  | .cut1 D hA => 1 + D.size + size hA
  | .cut2 D hA hB => 1 + D.size + size hA + size hB
  | .cut3 D hA hB hC => 1 + D.size + size hA + size hB + size hC
  | .cut4 D hA hB hC hD => 1 + D.size + size hA + size hB + size hC + size hD

/-- Definedness side conditions, mirroring `FamilyDeriv.DefinedObligations`.

* `core` reuses the underlying `SFormula.Deriv.DefinedObligations`.
* `recUnfold n d k` packages exactly `recUnfold_sound`'s two hypotheses: the
  `recCall` evaluates to some partial stabilizer `sa` (`hrec`) and every queried
  entry `q < n` is defined in `sa` (`hdef`).
* `foldTelescope cut outerBound N` packages exactly `foldTelescopeF_eval`'s
  side-condition: the closed cut family is *total* — there is a Pauli
  interpretation `g` such that the cut evaluates to `fun q => some (g · q)` at the
  fold index, its successor, `0`, and the row variable, under the relevant
  environments.  (This is the analogue of `recUnfold`'s definedness obligation;
  the telescoping algebra itself is unconditional.)
* `cut*` is the conjunction of the core's obligations with the sub-derivations'
  obligations, exactly as in `FamilyDeriv`. -/
def DefinedObligations {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    (D : PureFamilyDeriv cb fuel A) (E : PartialStabilizer) : Prop :=
  match D with
  | .arity0 D => PureFamilyDerivA.DefinedObligations D Env.empty E
  | .core Dcore => Dcore.DefinedObligations cb fuel Env.empty E
  | .recUnfold n d k =>
      exists sa,
        Term.eval cb fuel (.recCall (.natLit d) (.natLit k)) Env.empty = some sa /\
          forall q, q < n -> exists p, sa q = some p
  | .gridRowStripRange _ => True
  | .gridColStripRange _ => True
  | .foldTelescope cut _outerBound _N =>
      exists g : Nat -> Nat -> Pauli,
        (forall (row iv : Nat),
          Term.eval cb fuel (cut telFoldVar) (Env.cons iv (Env.cons row Env.empty)) =
            some (fun q => some (g iv q))) /\
        (forall (row iv : Nat),
          Term.eval cb fuel (cut (.add telFoldVar (.natLit 1)))
              (Env.cons iv (Env.cons row Env.empty)) =
            some (fun q => some (g (iv + 1) q))) /\
        (forall (row : Nat),
          Term.eval cb fuel (cut (.natLit 0)) (Env.cons row Env.empty) =
            some (fun q => some (g 0 q))) /\
        (forall (row : Nat),
          Term.eval cb fuel (cut telRowVar) (Env.cons row Env.empty) =
            some (fun q => some (g row q)))
  | .foldDisjoint lhs body _outerBound width _N =>
      exists (g : Nat -> Nat -> Nat -> Pauli) (t : Nat -> Nat -> Pauli),
        (forall (row iv : Nat),
          STerm.eval cb fuel body (Env.cons iv (Env.cons row Env.empty)) E =
            some (fun q => some (g row iv q))) /\
        (forall (row : Nat),
          STerm.eval cb fuel lhs (Env.cons row Env.empty) E =
            some (fun q => some (t row q))) /\
        (forall (row q : Nat),
          partialStabilizerFold width (fun i => fun q => some (g row i q)) q =
            some (t row q))
  | .cut1 Dcore hA =>
      Dcore.DefinedObligations cb fuel Env.empty E /\ DefinedObligations hA E
  | .cut2 Dcore hA hB =>
      Dcore.DefinedObligations cb fuel Env.empty E /\
        DefinedObligations hA E /\ DefinedObligations hB E
  | .cut3 Dcore hA hB hC =>
      Dcore.DefinedObligations cb fuel Env.empty E /\
        DefinedObligations hA E /\ DefinedObligations hB E /\ DefinedObligations hC E
  | .cut4 Dcore hA hB hC hD =>
      Dcore.DefinedObligations cb fuel Env.empty E /\
        DefinedObligations hA E /\ DefinedObligations hB E /\
          DefinedObligations hC E /\ DefinedObligations hD E

/-- The `recUnfold` atom's evaluation is exactly the `stabEqUpTo` shape that
    `recUnfold_sound` concludes is `some true`.  This is a `rfl`-level fact: the
    `SC.closed` wrappers make `STerm.eval` collapse to `Term.eval`, and the
    leading `natLit n` operand evaluates to `some n`, discharging the first
    monadic bind. -/
private theorem recUnfoldAtom_eval (cb : Term 2 .stab) (fuel n d k : Nat)
    (E : PartialStabilizer) :
    (recUnfoldAtom cb n d k).eval cb fuel Env.empty E =
      (do
        let a <- Term.eval cb fuel (.recCall (.natLit d) (.natLit k)) Env.empty
        let b <- Term.eval cb fuel (codeSubst cb d k) Env.empty
        stabEqUpTo n a b) := by
  simp only [recUnfoldAtom, SFormula.eval, STerm.eval, SC.closed, Term.eval]
  rfl

/-- **Structural soundness of pure family derivations.**

No `check = true` hypothesis: every leaf is justified by a soundness lemma.

* `core`     -> `SFormula.Deriv.sound`, with the empty-context premise
  discharged trivially (`Γ = []`).
* `recUnfold` -> `recUnfold_sound` (at successor fuel) / vacuous (at fuel `0`,
  where the packaged `recCall = some sa` is impossible).
* `gridRowStripRange` / `gridColStripRange` -> `gridRowStripRangeF_eval` /
  `gridColStripRangeF_eval`; the obligation is `True` (the fact is closed and
  unconditionally true), so nothing has to be supplied.
* `foldTelescope` -> `foldTelescopeF_eval`, fed the cut-totality witness `g` and
  its four evaluation facts packaged in the obligation.
* `cut*`     -> `SFormula.Deriv.sound` of the cut formula, with the
  context-holds premise supplied by the sub-derivations' soundness.  Mirrors
  `FamilyDeriv.sound`'s cut cases exactly. -/
theorem sound {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    (D : PureFamilyDeriv cb fuel A) (E : PartialStabilizer) :
    DefinedObligations D E -> A.eval cb fuel Env.empty E = some true := by
  intro hdef
  induction D with
  | arity0 D =>
      exact PureFamilyDerivA.sound D Env.empty E hdef
  | core Dcore =>
      simp only [DefinedObligations] at hdef
      exact Dcore.sound hdef (fun B hmem => by cases hmem)
  | recUnfold n d k =>
      simp only [DefinedObligations] at hdef
      obtain ⟨sa, hrec, hdefEntries⟩ := hdef
      rw [recUnfoldAtom_eval]
      cases fuel with
      | zero =>
          rw [Term.eval] at hrec
          exact absurd hrec (by simp)
      | succ f =>
          exact recUnfold_sound hrec hdefEntries
  | gridRowStripRange dist =>
      exact gridRowStripRangeF_eval cb fuel dist E
  | gridColStripRange dist =>
      exact gridColStripRangeF_eval cb fuel dist E
  | foldTelescope cut outerBound N =>
      simp only [DefinedObligations] at hdef
      obtain ⟨g, hFold, hFoldSucc, hZero, hRow⟩ := hdef
      exact foldTelescopeF_eval cb fuel E cut outerBound N g hFold hFoldSucc hZero hRow
  | foldDisjoint lhs body outerBound width N =>
      simp only [DefinedObligations] at hdef
      obtain ⟨g, t, hbody, hlhs, hunion⟩ := hdef
      exact foldDisjointF_eval cb fuel E lhs body outerBound width N g t hbody hlhs hunion
  | cut1 Dcore hA ihA =>
      simp only [DefinedObligations] at hdef
      rcases hdef with ⟨hcoreDef, hADef⟩
      exact Dcore.sound hcoreDef
        (fun B hmem => by
          cases hmem with
          | head => exact ihA hADef
          | tail _ htail => cases htail)
  | cut2 Dcore hA hB ihA ihB =>
      simp only [DefinedObligations] at hdef
      rcases hdef with ⟨hcoreDef, hADef, hBDef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA hADef
          | tail _ htail =>
              cases htail with
              | head => exact ihB hBDef
              | tail _ hnil => cases hnil)
  | cut3 Dcore hA hB hC ihA ihB ihC =>
      simp only [DefinedObligations] at hdef
      rcases hdef with ⟨hcoreDef, hADef, hBDef, hCDef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA hADef
          | tail _ htail =>
              cases htail with
              | head => exact ihB hBDef
              | tail _ htail2 =>
                  cases htail2 with
                  | head => exact ihC hCDef
                  | tail _ hnil => cases hnil)
  | cut4 Dcore hA hB hC hD ihA ihB ihC ihD =>
      simp only [DefinedObligations] at hdef
      rcases hdef with ⟨hcoreDef, hADef, hBDef, hCDef, hDDef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA hADef
          | tail _ htail =>
              cases htail with
              | head => exact ihB hBDef
              | tail _ htail2 =>
                  cases htail2 with
                  | head => exact ihC hCDef
                  | tail _ htail3 =>
                      cases htail3 with
                      | head => exact ihD hDDef
                      | tail _ hnil => cases hnil)

end PureFamilyDeriv

/-! ## Pure universal-stabilizer derivations

The `forall E : Stab[width], body(E)` wrapper over `PureFamilyDeriv`, mirroring
`ForallStabFamilyDeriv` (CodeStabBinder ~5172) but with the pure, structural
soundness (no `check` hypothesis). -/

/-- A universal-stabilizer derivation whose body is a `PureFamilyDeriv`. -/
inductive PureForallStabDeriv (cb : Term 2 .stab) (fuel : Nat) :
    ForallStabFormula 0 -> Type where
  | intro {Q : ForallStabFormula 0} :
      PureFamilyDeriv cb fuel Q.body ->
        PureForallStabDeriv cb fuel Q

namespace PureForallStabDeriv

def size {cb : Term 2 .stab} {fuel : Nat} {Q : ForallStabFormula 0} :
    PureForallStabDeriv cb fuel Q -> Nat
  | .intro body => 1 + PureFamilyDeriv.size body

def DefinedObligations {cb : Term 2 .stab} {fuel : Nat} {Q : ForallStabFormula 0}
    (D : PureForallStabDeriv cb fuel Q) (E : PartialStabilizer) : Prop :=
  match D with
  | .intro body => PureFamilyDeriv.DefinedObligations body E

/-- **Structural soundness of pure universal-stabilizer derivations.**

Mirrors `ForallStabFamilyDeriv.sound` MINUS the `check = true` hypothesis: the
body's closed facts are justified structurally by `PureFamilyDeriv.sound`. -/
theorem sound {cb : Term 2 .stab} {fuel : Nat} {Q : ForallStabFormula 0}
    (D : PureForallStabDeriv cb fuel Q) :
    (forall E n,
      Q.width.eval cb fuel Env.empty E = some n ->
        TotalUpTo n E ->
          D.DefinedObligations E) ->
      Q.holds cb fuel Env.empty := by
  intro hdef E n hWidth hTotal
  cases D with
  | intro body =>
      exact PureFamilyDeriv.sound body E (hdef E n hWidth hTotal)

end PureForallStabDeriv

/-! ## Smoke tests for the pure derivation system -/

/-- A trivially-true closed formula provable by the logic core alone. -/
private def trivTop : SFormula 0 := .top

/-- A `core`-only pure derivation of `⊤`. -/
private def pureTopDeriv (cb : Term 2 .stab) (fuel : Nat) :
    PureFamilyDeriv cb fuel trivTop :=
  .core (.top)

-- The `core` leaf is structurally sound with trivial obligations.
example (cb : Term 2 .stab) (fuel : Nat) (E : PartialStabilizer) :
    trivTop.eval cb fuel Env.empty E = some true :=
  (pureTopDeriv cb fuel).sound E (by trivial)

-- A `recUnfold` leaf typechecks at the expected atom.
example (cb : Term 2 .stab) (fuel : Nat) :
    PureFamilyDeriv cb fuel (recUnfoldAtom cb 3 2 5) :=
  .recUnfold 3 2 5

#print axioms PureFamilyDeriv.sound
#print axioms PureForallStabDeriv.sound

end QHL.CodeLang.Verify
