import QStab.QHL.CodeSurfaceSchedule

/-!
# Milestone S1 (completion): certified evaluation of the NZ object programs

This downstream file discharges the certified-evaluation obligations for the object
programs `nzOrderProg` / `nzLenProg` defined in `CodeSurfaceSchedule`.  It is kept
separate and small so the borderline-heartbeat `nzOrderProg_eval_arith` script (a single
`simp only`/`split_ifs`/`rfl` over the fused `classifyStab` cascade) has room without
raising `maxHeartbeats`.

* `nzOrderProg_eval_arith` / `nzLenProg_eval_arith` — the object programs evaluate to the
  meta arithmetic mirrors `nzOrderArith` / `nzLenArith` (fuel- and `codeBody`-irrelevant,
  since neither program contains `recCall`).
* `nzOrderFlat_eq_arith` / `nzLenFlat_eq_arith` — the arithmetic mirrors reconcile with the
  reference classifiers `nzOrderFlat` / `nzLenFlat`.
* `nzOrderProg_eval` / `nzLenProg_eval` — composition: the object programs evaluate to the
  reference classifiers.
-/

namespace QHL.CodeSurfaceSchedule

open QStab.Examples.SurfaceParametric
open QHL.CodeLang

-- The environment-lookup facts (`private` in `CodeSurfaceSchedule`), restated locally.
private lemma env3_zero (j d k : Nat) : (Env.cons j (Env.code d k)) 0 = j := rfl
private lemma env3_one (j d k : Nat) : (Env.cons j (Env.code d k)) 1 = k := rfl
private lemma env3_two (j d k : Nat) : (Env.cons j (Env.code d k)) 2 = d := rfl
private lemma env2_zero (d k : Nat) : (Env.code d k) 0 = k := rfl
private lemma env2_one (d k : Nat) : (Env.code d k) 1 = d := rfl

/-- **Certified evaluation of `nzOrderProg`** to its arithmetic mirror.  No `recCall`
appears, so the value is independent of `codeBody` and `fuel`. -/
theorem nzOrderProg_eval_arith (cb : Term 2 .stab) (fuel : Nat) (d k j : Nat) :
    Term.eval cb fuel nzOrderProg (Env.cons j (Env.code d k)) = some (nzOrderArith d k j) := by
  simp only [nzOrderProg, nzOrderArith, Term.eval, env3_zero, env3_one, env3_two,
    bind, Option.bind, decide_eq_true_eq]
  split_ifs <;> rfl

/-- Meta mirror of `nzLenProg`: `4` for bulk stabilizers, `2` for boundary ones. -/
def nzLenArith (d k : Nat) : Nat := if k < (d - 1) * (d - 1) then 4 else 2

/-- **Certified evaluation of `nzLenProg`** to its arithmetic mirror. -/
theorem nzLenProg_eval_arith (cb : Term 2 .stab) (fuel : Nat) (d k : Nat) :
    Term.eval cb fuel nzLenProg (Env.code d k) = some (nzLenArith d k) := by
  simp only [nzLenProg, nzLenArith, Term.eval, env2_zero, env2_one, bind, Option.bind,
    decide_eq_true_eq]
  split_ifs <;> rfl

/-- The length mirror reconciles with the reference classifier `nzLenFlat`. -/
theorem nzLenFlat_eq_arith (d k : Nat) : nzLenFlat d k = nzLenArith d k := by
  unfold nzLenArith
  split_ifs with h
  · exact nzLenFlat_bulk d k h
  · exact nzLenFlat_boundary d k h

/-- **`nzLenProg` evaluates to the reference length** `nzLenFlat`. -/
theorem nzLenProg_eval (cb : Term 2 .stab) (fuel : Nat) (d k : Nat) :
    Term.eval cb fuel nzLenProg (Env.code d k) = some (nzLenFlat d k) := by
  rw [nzLenProg_eval_arith, nzLenFlat_eq_arith]

/-- The order mirror reconciles with the reference classifier `nzOrderFlat`: pure `Nat`
casework aligning `classifyStab`'s cascade + `kindOrderRC` selection (`gridIdx` of the
`j`-th coordinate) with the fused arithmetic form. -/
theorem nzOrderFlat_eq_arith (d k j : Nat) : nzOrderFlat d k j = nzOrderArith d k j := by
  unfold nzOrderFlat nzOrderArith
  simp only [classifyStab]
  by_cases hbulk : k < (d - 1) * (d - 1)
  · rw [if_pos hbulk, if_pos hbulk]
    by_cases hpar : (k / (d - 1) + k % (d - 1)) % 2 = 0
    · rw [if_pos hpar, if_pos hpar]
      rcases j with _ | _ | _ | _ | j <;> simp [kindOrderRC, gridIdx]
    · rw [if_neg hpar, if_neg hpar]
      rcases j with _ | _ | _ | _ | j <;> simp [kindOrderRC, gridIdx]
  · rw [if_neg hbulk, if_neg hbulk]
    by_cases h1 : k - (d - 1) * (d - 1) < (d - 1) / 2
    · rw [if_pos h1, if_pos h1]
      rcases j with _ | _ | j <;> simp [kindOrderRC, gridIdx]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · rw [if_pos h2, if_pos h2]
        rcases j with _ | _ | j <;> simp [kindOrderRC, gridIdx]
      · rw [if_neg h2, if_neg h2]
        by_cases h3 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · rw [if_pos h3, if_pos h3]
          rcases j with _ | _ | j <;> simp [kindOrderRC, gridIdx]
        · rw [if_neg h3, if_neg h3]
          rcases j with _ | _ | j <;> simp [kindOrderRC, gridIdx]

/-- **`nzOrderProg` evaluates to the reference classifier** `nzOrderFlat`: the compiler's
NZ order is exactly the certified evaluation of the object program. -/
theorem nzOrderProg_eval (cb : Term 2 .stab) (fuel : Nat) (d k j : Nat) :
    Term.eval cb fuel nzOrderProg (Env.cons j (Env.code d k)) = some (nzOrderFlat d k j) := by
  rw [nzOrderProg_eval_arith, nzOrderFlat_eq_arith]

end QHL.CodeSurfaceSchedule
