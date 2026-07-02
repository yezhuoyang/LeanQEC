import QStab.QHL.CodeHGP
import QStab.Examples.HGPParametric

/-!
# Certified evaluation of the HGP object program

The anchor closing the source-level loop for HGP(Rep(d), Rep(d)): the
parametric spec of `HGPParametric.lean` is stated over the meta entry formula
`stabEntry`; this file proves that formula **is** the evaluation of the
object-language program `QHL.CodeLang.HGP.code`, at every `(d, k, q)`.

Two steps, as for the surface schedule programs:

* `hgpEntryAST_eval_arith` — the object program evaluates to the
  short-circuit-shaped mirror `hgpEntryArith` (identical tree, atomic
  conditions), fuel- and `codeBody`-irrelevant since no `recCall` appears.
* `hgpEntryArith_eq_stabEntry` — the mirror reconciles with `stabEntry`
  (pure propositional casework: `∧`/`∨` conditions versus their
  short-circuit expansions).

Headline: `code_evalAt?_eq_stabEntry` and the `Fin`-level wrapper
`mkHGPRepStabilizers_eq_code_eval`, after which every `HGPParametric`
statement about `mkHGPRepStabilizers` is a statement about `HGP.code`.
-/

namespace QHL.CodeLang.HGP

open QHL.CodeLang

-- Environment-lookup facts, restated locally (as in `CodeSurfaceScheduleEval`).
private lemma env3_zero (q d k : Nat) : (Env.cons q (Env.code d k)) 0 = q := rfl
private lemma env3_one (q d k : Nat) : (Env.cons q (Env.code d k)) 1 = k := rfl
private lemma env3_two (q d k : Nat) : (Env.cons q (Env.code d k)) 2 = d := rfl


/-- Short-circuit-shaped mirror of `hgpEntryAST`: the `.and`/`.or` conditions
    expanded to nested atomic `if`s, exactly as `Term.eval` unfolds them. -/
def hgpEntryArith (d k q : Nat) : Pauli :=
  if k < 2 * ((d - 1) * d) then
    if q < d * d + (d - 1) * (d - 1) then
      if k < (d - 1) * d then
        if q < d * d then
          if q % d = k % d then
            if q / d = k / d then Pauli.X
            else if q / d = k / d + 1 then Pauli.X else Pauli.I
          else Pauli.I
        else
          if (q - d * d) / (d - 1) = k / d then
            if (q - d * d) % (d - 1) = k % d then Pauli.X
            else if (q - d * d) % (d - 1) + 1 = k % d then Pauli.X else Pauli.I
          else Pauli.I
      else
        if q < d * d then
          if q / d = (k - (d - 1) * d) / (d - 1) then
            if q % d = (k - (d - 1) * d) % (d - 1) then Pauli.Z
            else if q % d = (k - (d - 1) * d) % (d - 1) + 1 then Pauli.Z else Pauli.I
          else Pauli.I
        else
          if (q - d * d) % (d - 1) = (k - (d - 1) * d) % (d - 1) then
            if (q - d * d) / (d - 1) = (k - (d - 1) * d) / (d - 1) then Pauli.Z
            else if (q - d * d) / (d - 1) + 1 = (k - (d - 1) * d) / (d - 1) then Pauli.Z
            else Pauli.I
          else Pauli.I
    else Pauli.I
  else Pauli.I

/-- **Certified evaluation of `hgpEntryAST`** to its arithmetic mirror.  No
    `recCall` appears, so the value is independent of `codeBody` and `fuel`. -/
theorem hgpEntryAST_eval_arith (cb : Term 2 .stab) (fuel : Nat) (d k q : Nat) :
    Term.eval cb fuel hgpEntryAST (Env.cons q (Env.code d k))
      = some (hgpEntryArith d k q) := by
  simp only [hgpEntryAST, hgpEntryArith, qv, kv, dv, dm1, s2start, xCount, pOff, nQ,
    s1row, s1col, s2row, s2col, xI, xJ, zT, zA, zJ,
    Term.eval, env3_zero, env3_one, env3_two, bind, Option.bind, decide_eq_true_eq]
  split_ifs <;> simp [*]

/-- The short-circuit mirror reconciles with the spec-side entry formula. -/
theorem hgpEntryArith_eq_stabEntry (d k q : Nat) :
    hgpEntryArith d k q = QStab.Examples.HGPParametric.stabEntry d k q := by
  unfold hgpEntryArith QStab.Examples.HGPParametric.stabEntry
  split_ifs <;> first | rfl | tauto

/-- **The object program evaluates to the spec-side entry formula** at every
    `(d, k, q)` — `HGPParametric`'s stabilizers are `HGP.code`'s evaluation. -/
theorem code_evalAt?_eq_stabEntry (d k q : Nat) :
    code.evalAt? d k q = some (QStab.Examples.HGPParametric.stabEntry d k q) := by
  show CodeFn.evalEntry? code (CodeFn.fuelForDistance d) d k q = _
  simp only [CodeFn.evalEntry?, CodeFn.evalStabilizer?, code, Term.eval,
    bind, Option.bind]
  rw [hgpEntryAST_eval_arith, hgpEntryArith_eq_stabEntry]

/-- `Fin`-level anchor: the parametric spec's generator family **is** the
    object program's evaluation (the `mkSurfaceStabilizers` anchor analogue). -/
theorem mkHGPRepStabilizers_eq_code_eval (d : Nat)
    (k : Fin (QStab.Examples.HGPParametric.hgpNumStab d))
    (q : Fin (QStab.Examples.HGPParametric.hgpN d)) :
    code.evalAt? d k.val q.val
      = some (QStab.Examples.HGPParametric.mkHGPRepStabilizers d k q) :=
  code_evalAt?_eq_stabEntry d k.val q.val

#print axioms code_evalAt?_eq_stabEntry
#print axioms mkHGPRepStabilizers_eq_code_eval

end QHL.CodeLang.HGP
