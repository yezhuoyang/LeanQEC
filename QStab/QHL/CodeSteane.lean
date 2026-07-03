import QStab.QHL.CodeLang

/-!
# The Steane [[7,1,3]] code as an object-language program

Six stabilizer generators over seven qubits, both CSS halves given by the rows of
the [7,4] Hamming parity-check matrix: row `r` supports qubit `q` iff bit `r` of
`q + 1` is set.  Generators `k < 3` are the X-type rows, `k ∈ {3,4,5}` the Z-type
rows; out-of-range `(k, q)` yield `I`.  The language has no exponentiation, so the
three Hamming bits use literal divisors `1, 2, 4` selected by branching on `k`.

Fixed-size code: no `recCall`, so evaluation is fuel- and distance-irrelevant
(the `d` argument of the `CodeFn` convention is ignored).
-/

namespace QHL.CodeLang.Steane

open QHL.CodeLang

private def qv : Term 3 .nat := .var 0
private def kv : Term 3 .nat := .var 1

/-- Hamming membership: bit `r ∈ {0,1,2}` of `q + 1`, via the literal divisor `2^r`. -/
private def hammingBit (r : Nat) : Term 3 .bool :=
  .eqNat (.mod (.div (.add qv (.natLit 1)) (.natLit (2 ^ r))) (.natLit 2)) (.natLit 1)

/-- The row-`k` Hamming membership of qubit `q`, `k` taken mod the CSS half. -/
private def rowBit (base : Nat) : Term 3 .bool :=
  .ite (.eqNat kv (.natLit base)) (hammingBit 0)
    (.ite (.eqNat kv (.natLit (base + 1))) (hammingBit 1) (hammingBit 2))

/-- Steane entry: `(d, k, q) ↦ Pauli` (the `d` slot is unused — fixed-size code). -/
def steaneEntryAST : Term 3 .pauli :=
  .ite (.and (.ltNat kv (.natLit 6)) (.ltNat qv (.natLit 7)))
    (.ite (.ltNat kv (.natLit 3))
      (.ite (rowBit 0) (.pauliLit Pauli.X) (.pauliLit Pauli.I))
      (.ite (rowBit 3) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
    (.pauliLit Pauli.I)

/-- **The Steane code as a `CodeFn`** — one object-language AST, all six generators
obtained by evaluating it at `k = 0..5`. -/
def code : CodeFn where
  body := .stabLam steaneEntryAST

/-! ## Sanity cross-validation (reduce to closed literals)

Hamming rows: bit 0 hits `q+1 ∈ {1,3,5,7}` (qubits 0,2,4,6); bit 1 hits
`q+1 ∈ {2,3,6,7}` (qubits 1,2,5,6); bit 2 hits `q+1 ∈ {4,…,7}` (qubits 3,4,5,6). -/

-- X-generators (k = 0,1,2):
#eval (List.range 7).map fun q => Steane.code.evalAt? 7 0 q
-- expect [X, I, X, I, X, I, X]
#eval (List.range 7).map fun q => Steane.code.evalAt? 7 1 q
-- expect [I, X, X, I, I, X, X]
#eval (List.range 7).map fun q => Steane.code.evalAt? 7 2 q
-- expect [I, I, I, X, X, X, X]
-- Z-generators (k = 3,4,5):
#eval (List.range 7).map fun q => Steane.code.evalAt? 7 3 q
-- expect [Z, I, Z, I, Z, I, Z]
#eval (List.range 7).map fun q => Steane.code.evalAt? 7 5 q
-- expect [I, I, I, Z, Z, Z, Z]

/-! ## Certified evaluation (Route B): axiom-clean, no `native_decide`. -/

private lemma env3_zero (a b c : Nat) : (Env.cons a (Env.code b c)) 0 = a := rfl
private lemma env3_one (a b c : Nat) : (Env.cons a (Env.code b c)) 1 = c := rfl

/-- Nat-mirror of `hammingBit`: bit `r` of `qq + 1`. -/
def hammingBitN (r qq : Nat) : Bool := decide ((qq + 1) / (2 ^ r) % 2 = 1)

/-- Nat-mirror of `rowBit`. -/
def steaneRowBitN (base kk qq : Nat) : Bool :=
  if kk = base then hammingBitN 0 qq
  else if kk = base + 1 then hammingBitN 1 qq
  else hammingBitN 2 qq

/-- Arithmetic mirror of `steaneEntryAST` (the `.and` short-circuit expanded to nested ifs). -/
def steaneEntryArith (kk qq : Nat) : Pauli :=
  if kk < 6 then
    if qq < 7 then
      if kk < 3 then
        (if steaneRowBitN 0 kk qq then Pauli.X else Pauli.I)
      else
        (if steaneRowBitN 3 kk qq then Pauli.Z else Pauli.I)
    else Pauli.I
  else Pauli.I

/-- **Certified evaluation**: the Steane object program evaluates to its arithmetic mirror
at every `(d, k, q)` — through `Term.eval`'s equation lemmas, no `native_decide`. -/
theorem code_evalAt?_eq_arith (dd kk qq : Nat) :
    code.evalAt? dd kk qq = some (steaneEntryArith kk qq) := by
  show CodeFn.evalEntry? code (CodeFn.fuelForDistance dd) dd kk qq = _
  simp only [CodeFn.evalEntry?, CodeFn.evalStabilizer?, code, steaneEntryAST, rowBit,
    hammingBit, qv, kv, steaneEntryArith, steaneRowBitN, hammingBitN, Term.eval,
    Env.cons, Env.code, Env.empty, env3_zero, env3_one, bind, Option.bind,
    decide_eq_true_eq]
  split_ifs <;> simp_all

end QHL.CodeLang.Steane
