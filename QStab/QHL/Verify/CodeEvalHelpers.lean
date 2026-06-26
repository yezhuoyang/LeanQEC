import QStab.QHL.CodeLang

namespace QHL.CodeLang.Verify.CodeEvalHelpers

open QHL.CodeLang

theorem eval_recCall_succ {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {dT kT : Term arity .nat} {rho : Env arity} {dv kv : Nat}
    (hd : Term.eval codeBody fuel dT rho = some dv)
    (hk : Term.eval codeBody fuel kT rho = some kv) :
    Term.eval codeBody (fuel + 1) (.recCall dT kT) rho =
      Term.eval codeBody fuel codeBody (Env.code dv kv) := by
  simp [Term.eval, hd, hk]

theorem eval_stabAt_recCall_natLit {arity : Nat} (F : CodeFn) (fuel d k q : Nat)
    (rho : Env arity) :
    Term.eval F.body (fuel + 1)
        (.stabAt (.recCall (.natLit d) (.natLit k)) (.natLit q)) rho =
      F.evalEntry? fuel d k q := by
  simp [Term.eval, CodeFn.evalEntry?, CodeFn.evalStabilizer?, Env.code]

theorem eval_stabAt_recCall {arity : Nat} (F : CodeFn) {fuel : Nat}
    {dT kT qT : Term arity .nat} {rho : Env arity} {dv kv qv : Nat}
    (hd : Term.eval F.body fuel dT rho = some dv)
    (hk : Term.eval F.body fuel kT rho = some kv)
    (hq : Term.eval F.body (fuel + 1) qT rho = some qv) :
    Term.eval F.body (fuel + 1) (.stabAt (.recCall dT kT) qT) rho =
      F.evalEntry? fuel dv kv qv := by
  simp [Term.eval, CodeFn.evalEntry?, CodeFn.evalStabilizer?, hd, hk, hq, Env.code]

theorem eval_recCall_natLit {arity : Nat} (F : CodeFn) (fuel d k : Nat)
    (rho : Env arity) :
    Term.eval F.body (fuel + 1) (.recCall (.natLit d) (.natLit k)) rho =
      F.evalStabilizer? fuel d k := by
  simp [Term.eval, CodeFn.evalStabilizer?, Env.code]

end QHL.CodeLang.Verify.CodeEvalHelpers
