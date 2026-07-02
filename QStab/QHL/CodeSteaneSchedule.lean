import QStab.QHL.CodeLang

/-!
# Steane schedule programs: order + length as object-language terms

`Steane.code` (`CodeSteane.lean`) gives the *content* of the six `[[7,1,3]]` generators.
This file gives their **schedule** as two object programs, so the code-blind generator
`xzProgramOfPrograms` produces Steane's real `XZProgram` (just as `nzOrderProg`/`nzLenProg`
do for the surface code).

**Scheme choice (documented, like NZ's row/column rule):** each generator's support is
traversed in **ascending qubit index within its Hamming row**.  Steane is fixed-size, so
the length is `4` for all six generators and the order depends only on the Hamming row
`k % 3`:

* row 0 (`k ∈ {0,3}`): `[0, 2, 4, 6]`
* row 1 (`k ∈ {1,4}`): `[1, 2, 5, 6]`
* row 2 (`k ∈ {2,5}`): `[3, 4, 5, 6]`

This choice fixes the hook set (the back-action residuals are the suffixes of these
orders); a different ascending order would give a different hook set, exactly as for NZ.
Everything is literal branch tables (no recursion), so evaluation is fuel- and
`codeBody`-irrelevant.
-/

namespace QHL.CodeSteaneSchedule

open QHL.CodeLang

/-- Steane length program: `4` for every generator (fixed-size code). -/
def steaneLenProg : Term 2 .nat := .natLit 4

/-- Steane order program `(d, k, j) ↦` the `j`-th scheduled qubit of generator `k`,
ascending within the Hamming row `k % 3`.  `j = var 0`, `k = var 1`, `d = var 2` (`d`
unused — fixed size). -/
def steaneOrderProg : Term 3 .nat :=
  let jv : Term 3 .nat := .var 0
  let kv : Term 3 .nat := .var 1
  let row : Term 3 .nat := .mod kv (.natLit 3)
  let pick : Nat → Nat → Nat → Nat → Term 3 .nat := fun a b c e =>
    .ite (.eqNat jv (.natLit 0)) (.natLit a)
      (.ite (.eqNat jv (.natLit 1)) (.natLit b)
        (.ite (.eqNat jv (.natLit 2)) (.natLit c) (.natLit e)))
  .ite (.eqNat row (.natLit 0)) (pick 0 2 4 6)
    (.ite (.eqNat row (.natLit 1)) (pick 1 2 5 6) (pick 3 4 5 6))

/-- Meta mirror of `steaneLenProg`. -/
def steaneLenArith (_d _k : Nat) : Nat := 4

/-- Meta mirror of `steaneOrderProg` — identical branch structure. -/
def steaneOrderArith (_d k j : Nat) : Nat :=
  if k % 3 = 0 then (if j = 0 then 0 else if j = 1 then 2 else if j = 2 then 4 else 6)
  else if k % 3 = 1 then (if j = 0 then 1 else if j = 1 then 2 else if j = 2 then 5 else 6)
  else (if j = 0 then 3 else if j = 1 then 4 else if j = 2 then 5 else 6)

private lemma env3_zero (j d k : Nat) : (Env.cons j (Env.code d k)) 0 = j := rfl
private lemma env3_one (j d k : Nat) : (Env.cons j (Env.code d k)) 1 = k := rfl

/-- **Certified evaluation of `steaneLenProg`** (`= 4`, any code/fuel). -/
theorem steaneLenProg_eval (cb : Term 2 .stab) (fuel : Nat) (d k : Nat) :
    Term.eval cb fuel steaneLenProg (Env.code d k) = some (steaneLenArith d k) := by
  simp [steaneLenProg, steaneLenArith, Term.eval]

/-- **Certified evaluation of `steaneOrderProg`** to its arithmetic mirror. -/
theorem steaneOrderProg_eval (cb : Term 2 .stab) (fuel : Nat) (d k j : Nat) :
    Term.eval cb fuel steaneOrderProg (Env.cons j (Env.code d k)) =
      some (steaneOrderArith d k j) := by
  simp only [steaneOrderProg, steaneOrderArith, Term.eval, env3_zero, env3_one,
    bind, Option.bind, decide_eq_true_eq]
  split_ifs <;> rfl

end QHL.CodeSteaneSchedule
