import QStab.QHL.Verify.SurfaceBridgeTotality
import QStab.QHL.Verify.SurfaceRecConvergence

/-!
# `FormulaDefined` eval-totality library for the Surface derivations

This file is the **foundational leaf-discharger** for the two remaining
definedness `sorry`s in `SurfaceDistanceProver.lean`.  Both
`codeLevelDefined` (over `PureFamilyDerivA.DefinedObligations`) and
`lowerDefined` (over `PureFamilyDeriv.DefinedObligations`) ultimately bottom out
— at every `FormulaDefined`-bearing `SFormula.Deriv` constructor — in goals of
the shape

    FormulaDefined cb fuel rho E A  :=  ∃ b, A.eval cb fuel rho E = some b

for the *surface atom formula shapes* `A`.  This file proves `FormulaDefined`
for those shapes, reusing the already-proved totality assets:

* `recCall_total` / `recCall_total_symbolicK` (SurfaceRecConvergence) — totality
  of the recursively-defined surface stabilizer `recCall` at the literal Surface
  distance, with fuel `≥ index + 2`;
* `eval_stabMul_closed` / `rowCutInnerTerm_eval` / `colCutInnerTerm_eval`
  (SurfaceBridgeTotality) — totality of the closed `rowCut`/`colCut`/bridge
  stabilizers;
* `PureTerm.eval_total` (CodeStabBinder) — totality of every pure nat/bool/pauli
  term;
* the `TotalUpTo n E` hypothesis carried by the lower-bound obligation, for the
  *open* error stabilizer `E`.

The core of the open-`E` story is `stabEqUpTo` / `parityUpTo` / `weightUpTo`
totality from pointwise totality of the two partial stabilizers (the `…_total`
lemmas in the first section).

No `sorry` / `native_decide` / new `axiom` / `Formula.check` is used.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

/-! ## Pointwise totality of a partial stabilizer up to a bound

`StabTotalUpTo n A` says `A` is defined at every queried entry below `n`.  This
is the common denominator of every closed cut totality fact (which give a value
`some (g · ·)`, hence `StabTotalUpTo` for any `n`) and the open-`E`
`TotalUpTo n E` hypothesis.  -/

/-- A partial stabilizer is defined at every entry strictly below `n`. -/
def StabTotalUpTo (n : Nat) (A : PartialStabilizer) : Prop :=
  ∀ q, q < n → ∃ p, A q = some p

/-- `TotalUpTo` (the kernel notion, used by the lower-bound obligation) is
literally `StabTotalUpTo`. -/
theorem StabTotalUpTo_of_TotalUpTo {n : Nat} {E : PartialStabilizer}
    (h : TotalUpTo n E) : StabTotalUpTo n E := h

/-- An everywhere-`some` stabilizer is total up to any bound. -/
theorem StabTotalUpTo.ofTotal {n : Nat} {g : Nat → Pauli} :
    StabTotalUpTo n (fun q => some (g q)) := by
  intro q _; exact ⟨g q, rfl⟩

/-! ### `stabEqUpTo` / `parityUpTo` / `weightUpTo` totality -/

/-- `stabEqUpTo` converges when both stabilizers are total up to the bound. -/
theorem stabEqUpTo_total {n : Nat} {A B : PartialStabilizer}
    (hA : StabTotalUpTo n A) (hB : StabTotalUpTo n B) :
    ∃ b, stabEqUpTo n A B = some b := by
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ m ih =>
      obtain ⟨b, hb⟩ := ih (fun q hq => hA q (Nat.lt_succ_of_lt hq))
        (fun q hq => hB q (Nat.lt_succ_of_lt hq))
      obtain ⟨av, hav⟩ := hA m (Nat.lt_succ_self m)
      obtain ⟨bv, hbv⟩ := hB m (Nat.lt_succ_self m)
      cases b with
      | true => exact ⟨decide (av = bv), by simp [stabEqUpTo, hb, hav, hbv, bind, Option.bind]⟩
      | false => exact ⟨false, by simp [stabEqUpTo, hb, bind, Option.bind]⟩

/-- `parityUpTo` converges when both stabilizers are total up to the bound. -/
theorem parityUpTo_total {n : Nat} {A B : PartialStabilizer}
    (hA : StabTotalUpTo n A) (hB : StabTotalUpTo n B) :
    ∃ b, parityUpTo n A B = some b := by
  induction n with
  | zero => exact ⟨false, rfl⟩
  | succ m ih =>
      obtain ⟨b, hb⟩ := ih (fun q hq => hA q (Nat.lt_succ_of_lt hq))
        (fun q hq => hB q (Nat.lt_succ_of_lt hq))
      obtain ⟨av, hav⟩ := hA m (Nat.lt_succ_self m)
      obtain ⟨bv, hbv⟩ := hB m (Nat.lt_succ_self m)
      exact ⟨xor b (ErrorVec.Pauli.anticommutes av bv),
        by simp [parityUpTo, hb, hav, hbv, bind, Option.bind]⟩

/-- `weightUpTo` converges when the stabilizer is total up to the bound. -/
theorem weightUpTo_total {n : Nat} {A : PartialStabilizer}
    (hA : StabTotalUpTo n A) :
    ∃ w, weightUpTo n A = some w := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
      obtain ⟨w, hw⟩ := ih (fun q hq => hA q (Nat.lt_succ_of_lt hq))
      obtain ⟨av, hav⟩ := hA m (Nat.lt_succ_self m)
      exact ⟨if av = Pauli.I then w else w + 1,
        by simp [weightUpTo, hw, hav, bind, Option.bind]⟩

/-! ## `STerm`-eval totality for the atom subterm shapes

The atom formulas are built from a small grammar of `STerm`s:
* closed terms `SC.closed t` (eval = `Term.eval t`) — total when `t` evaluates;
* literals `SC.b`/`SC.p`/`SC.n` — always total;
* `.anticommutes`/`.pauliMul`/`.ltNat`/`.ite` over total subterms;
* `.stabAt s q` — total when `s` evaluates to a stabilizer total at the value of
  `q` (covers both closed cuts and the open `E`).

These short lemmas feed the `eqPauli`/`eqBool` workhorses above. -/

/-- A closed term is total exactly when its underlying `Term` evaluates. -/
theorem sterm_eval_closed {arity : Nat} {ty : Ty} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {t : Term arity ty}
    (h : ∃ v, Term.eval cb fuel t rho = some v) :
    ∃ v, (SC.closed t).eval cb fuel rho E = some v := by
  obtain ⟨v, hv⟩ := h; exact ⟨v, by simp [SC.closed, STerm.eval, hv]⟩

/-- A closed *pure* term is total. -/
theorem sterm_eval_closedPure {arity : Nat} {ty : Ty} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {t : Term arity ty}
    (ht : SFormula.PureTerm t) :
    ∃ v, (SC.closed t).eval cb fuel rho E = some v :=
  sterm_eval_closed (ht.eval_total cb fuel rho)

/-- The bool literal is total. -/
theorem sterm_eval_b {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} (x : Bool) :
    ∃ v, (SC.b x : STerm arity .bool).eval cb fuel rho E = some v :=
  ⟨x, by simp [SC.b, STerm.eval, Term.eval]⟩

/-- The Pauli literal is total. -/
theorem sterm_eval_p {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} (x : Pauli) :
    ∃ v, (SC.p x : STerm arity .pauli).eval cb fuel rho E = some v :=
  ⟨x, by simp [SC.p, STerm.eval, Term.eval]⟩

/-- `anticommutes` of two total pauli terms is total. -/
theorem sterm_eval_anticommutes {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : STerm arity .pauli}
    (ha : ∃ av, a.eval cb fuel rho E = some av)
    (hb : ∃ bv, b.eval cb fuel rho E = some bv) :
    ∃ v, (STerm.anticommutes a b).eval cb fuel rho E = some v := by
  obtain ⟨av, hav⟩ := ha; obtain ⟨bv, hbv⟩ := hb
  exact ⟨ErrorVec.Pauli.anticommutes av bv, by simp [STerm.eval, hav, hbv, bind, Option.bind]⟩

/-- `pauliMul` of two total pauli terms is total. -/
theorem sterm_eval_pauliMul {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : STerm arity .pauli}
    (ha : ∃ av, a.eval cb fuel rho E = some av)
    (hb : ∃ bv, b.eval cb fuel rho E = some bv) :
    ∃ v, (STerm.pauliMul a b).eval cb fuel rho E = some v := by
  obtain ⟨av, hav⟩ := ha; obtain ⟨bv, hbv⟩ := hb
  exact ⟨Pauli.mul av bv, by simp [STerm.eval, hav, hbv, bind, Option.bind]⟩

/-- `stabAt s q` is total when `s` evaluates to a stabilizer defined at the value
of `q`. -/
theorem sterm_eval_stabAt {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {s : STerm arity .stab} {q : STerm arity .nat} {sv : PartialStabilizer} {qv : Nat}
    (hs : s.eval cb fuel rho E = some sv)
    (hq : q.eval cb fuel rho E = some qv)
    (hsq : ∃ p, sv qv = some p) :
    ∃ v, (STerm.stabAt s q).eval cb fuel rho E = some v := by
  obtain ⟨p, hp⟩ := hsq
  exact ⟨p, by simp [STerm.eval, hs, hq, hp, bind, Option.bind]⟩

/-- The bound stabilizer `E` at a closed index `q < n`, given `TotalUpTo n E`. -/
theorem sterm_eval_boundStab_at {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {q : STerm arity .nat} {qv n : Nat}
    (hq : q.eval cb fuel rho E = some qv) (hqlt : qv < n) (hE : TotalUpTo n E) :
    ∃ v, (STerm.stabAt STerm.boundStab q).eval cb fuel rho E = some v :=
  sterm_eval_stabAt (by simp [STerm.eval]) hq (hE qv hqlt)

/-! ## Boolean-combinator `FormulaDefined`

`FormulaDefined (.not A)`/`(.and A B)`/`(.or A B)`/`(.imp A B)` follow from the
component formulas being defined.  `localCommutesAt` is `.not (.eqBool …)`, and
several `Deriv` nodes (`notIntro`, `impIntro`, `orIntroRight`) carry a
`FormulaDefined` of a compound formula. -/

/-- `FormulaDefined (.not A)` from `FormulaDefined A`. -/
theorem formulaDefined_not {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {A : SFormula arity}
    (hA : SFormula.Deriv.FormulaDefined cb fuel rho E A) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.not A) := by
  obtain ⟨av, hav⟩ := hA
  exact ⟨!av, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, bind, Option.bind]⟩

/-- `FormulaDefined (.and A B)` from both components defined. -/
theorem formulaDefined_and {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {A B : SFormula arity}
    (hA : SFormula.Deriv.FormulaDefined cb fuel rho E A)
    (hB : SFormula.Deriv.FormulaDefined cb fuel rho E B) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.and A B) := by
  obtain ⟨av, hav⟩ := hA; obtain ⟨bv, hbv⟩ := hB
  cases av with
  | true => exact ⟨bv, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, hbv, bind, Option.bind]⟩
  | false => exact ⟨false, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, bind, Option.bind]⟩

/-- `FormulaDefined (.or A B)` from both components defined. -/
theorem formulaDefined_or {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {A B : SFormula arity}
    (hA : SFormula.Deriv.FormulaDefined cb fuel rho E A)
    (hB : SFormula.Deriv.FormulaDefined cb fuel rho E B) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.or A B) := by
  obtain ⟨av, hav⟩ := hA; obtain ⟨bv, hbv⟩ := hB
  cases av with
  | true => exact ⟨true, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, bind, Option.bind]⟩
  | false => exact ⟨bv, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, hbv, bind, Option.bind]⟩

/-- `FormulaDefined (.imp A B)` from both components defined. -/
theorem formulaDefined_imp {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {A B : SFormula arity}
    (hA : SFormula.Deriv.FormulaDefined cb fuel rho E A)
    (hB : SFormula.Deriv.FormulaDefined cb fuel rho E B) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.imp A B) := by
  obtain ⟨av, hav⟩ := hA; obtain ⟨bv, hbv⟩ := hB
  cases av with
  | true => exact ⟨bv, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, hbv, bind, Option.bind]⟩
  | false => exact ⟨true, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, bind, Option.bind]⟩

/-! ## Generic congruence-leaf shapes (`eqNat`/`eqBool`/`eqPauli`)

The simplest atoms — `eqNat`, `eqBool`, `eqPauli` — are `FormulaDefined` as soon
as **both** sides evaluate to *some* value.  Their eval clause is a two-`bind`
`decide (· = ·)`; if both bind succeed, the result is `some (decide …)`.  These
are the workhorses for the `pauliIteSelect*`, `stabAtClosedIteLamEq*`,
`anticommutesTransport`, and `noAntiAtSubst` obligations. -/

/-- `FormulaDefined` for `eqNat a b` from totality of both nat terms. -/
theorem formulaDefined_eqNat {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : STerm arity .nat}
    (ha : ∃ av, a.eval cb fuel rho E = some av)
    (hb : ∃ bv, b.eval cb fuel rho E = some bv) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.eqNat a b) := by
  obtain ⟨av, hav⟩ := ha
  obtain ⟨bv, hbv⟩ := hb
  exact ⟨decide (av = bv), by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, hbv, bind, Option.bind]⟩

/-- `FormulaDefined` for `eqBool a b` from totality of both bool terms. -/
theorem formulaDefined_eqBool {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : STerm arity .bool}
    (ha : ∃ av, a.eval cb fuel rho E = some av)
    (hb : ∃ bv, b.eval cb fuel rho E = some bv) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.eqBool a b) := by
  obtain ⟨av, hav⟩ := ha
  obtain ⟨bv, hbv⟩ := hb
  exact ⟨decide (av = bv), by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, hbv, bind, Option.bind]⟩

/-- `FormulaDefined` for `eqPauli a b` from totality of both pauli terms. -/
theorem formulaDefined_eqPauli {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : STerm arity .pauli}
    (ha : ∃ av, a.eval cb fuel rho E = some av)
    (hb : ∃ bv, b.eval cb fuel rho E = some bv) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.eqPauli a b) := by
  obtain ⟨av, hav⟩ := ha
  obtain ⟨bv, hbv⟩ := hb
  exact ⟨decide (av = bv), by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hav, hbv, bind, Option.bind]⟩

/-- `FormulaDefined (localCommutesAt A B q)` from totality of `A`/`B` at the value
of `q`.  `localCommutesAt A B q = ¬(anticommutes (A@q) (B@q) = true)`. -/
theorem formulaDefined_localCommutesAt {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {A B : STerm arity .stab} {q : STerm arity .nat}
    (hAq : ∃ v, (STerm.stabAt A q).eval cb fuel rho E = some v)
    (hBq : ∃ v, (STerm.stabAt B q).eval cb fuel rho E = some v) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (SFormula.localCommutesAt A B q) := by
  apply formulaDefined_not
  apply formulaDefined_eqBool
  · exact sterm_eval_anticommutes hAq hBq
  · exact sterm_eval_b true

/-! ## Stabilizer-level atoms (`eqStabUpTo`/`commutesUpTo`/`weightLe`)

These atoms' eval clauses first evaluate `nv`, then both stabilizer terms to
`Av`/`Bv`, then run `stabEqUpTo`/`parityUpTo`/`weightUpTo`.  Hence the
`FormulaDefined` follows from: (i) `nv` defined, (ii) both stabilizer terms
evaluate, and (iii) the resulting partial stabilizers are total up to `nv`.

The two consumers are:
* `eqStabRefl`/`eqStabFold*` (reflexive `eqStabUpTo n A A`): same stabilizer on
  both sides — `StabTotalUpTo nv` of `A` suffices.
* `commutesStabFoldLeft`/`commutesOfPointwise` (`commutesUpTo n A B`) and the
  `finite*WeightLower` (`weightLe n E w`): the `weightLe` one is over the open
  `E`, discharged from `TotalUpTo nv E`. -/

/-- `FormulaDefined` for `eqStabUpTo n A B` from totality of `n`, of both
stabilizer terms, and pointwise totality of the two resulting partial
stabilizers up to the evaluated bound. -/
theorem formulaDefined_eqStabUpTo {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {n : STerm arity .nat}
    {A B : STerm arity .stab} {nv : Nat} {Av Bv : PartialStabilizer}
    (hn : n.eval cb fuel rho E = some nv)
    (hA : A.eval cb fuel rho E = some Av)
    (hB : B.eval cb fuel rho E = some Bv)
    (htA : StabTotalUpTo nv Av) (htB : StabTotalUpTo nv Bv) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.eqStabUpTo n A B) := by
  obtain ⟨b, hb⟩ := stabEqUpTo_total htA htB
  exact ⟨b, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hn, hA, hB, hb, bind, Option.bind]⟩

/-- `FormulaDefined` for `commutesUpTo n A B`. -/
theorem formulaDefined_commutesUpTo {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {n : STerm arity .nat}
    {A B : STerm arity .stab} {nv : Nat} {Av Bv : PartialStabilizer}
    (hn : n.eval cb fuel rho E = some nv)
    (hA : A.eval cb fuel rho E = some Av)
    (hB : B.eval cb fuel rho E = some Bv)
    (htA : StabTotalUpTo nv Av) (htB : StabTotalUpTo nv Bv) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.commutesUpTo n A B) := by
  obtain ⟨b, hb⟩ := parityUpTo_total htA htB
  exact ⟨!b, by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hn, hA, hB, hb, bind, Option.bind]⟩

/-- `FormulaDefined` for `weightLe n A w`. -/
theorem formulaDefined_weightLe {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {n : STerm arity .nat}
    {A : STerm arity .stab} {w : STerm arity .nat} {nv wv : Nat} {Av : PartialStabilizer}
    (hn : n.eval cb fuel rho E = some nv)
    (hA : A.eval cb fuel rho E = some Av)
    (hw : w.eval cb fuel rho E = some wv)
    (htA : StabTotalUpTo nv Av) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.weightLe n A w) := by
  obtain ⟨weight, hweight⟩ := weightUpTo_total htA
  exact ⟨decide (weight ≤ wv),
    by simp [SFormula.Deriv.FormulaDefined, SFormula.eval, hn, hA, hw, hweight, bind, Option.bind]⟩

/-! ## Closed-term convenience forms

The `pauliIteSelect*` and `stabAtClosedIteLamEq*` obligations are `eqPauli`s
between *closed* pauli terms.  For these, totality is `Term.eval` totality of the
two underlying closed terms — supplied either directly or (in the surface case)
through `PureTerm.eval_total`. -/

/-- `FormulaDefined (.eqPauli (SC.closed a) (SC.closed b))` from `Term.eval`
totality of both closed terms. -/
theorem formulaDefined_eqPauli_closed {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : Term arity .pauli}
    (ha : ∃ av, Term.eval cb fuel a rho = some av)
    (hb : ∃ bv, Term.eval cb fuel b rho = some bv) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.eqPauli (SC.closed a) (SC.closed b)) :=
  formulaDefined_eqPauli (sterm_eval_closed ha) (sterm_eval_closed hb)

/-- `FormulaDefined (.eqPauli (SC.closed a) (SC.closed b))` for **pure** closed
pauli terms (the surface `pauliIteSelect*` shape). -/
theorem formulaDefined_eqPauli_closedPure {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : Term arity .pauli}
    (ha : SFormula.PureTerm a) (hb : SFormula.PureTerm b) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.eqPauli (SC.closed a) (SC.closed b)) :=
  formulaDefined_eqPauli_closed (ha.eval_total cb fuel rho) (hb.eval_total cb fuel rho)

/-! ## The keystone `stabAtClosedIteLam` leaf (the `PurePauli` collapse)

The keystone base/rec masters bottom out at `stabAtClosedIteLamEqThen/Else` peels,
whose `FormulaDefined` leaf obligation is an `eqPauli` between
`stabAt (closed (stabLam (ite cond thenP elseP))) (closed q)` and
`closed (instantiateTopNat q thenP/elseP)`.  BOTH sides are recursion-free
(`PurePauli`/`codeSubstAt`-of-`PurePauli`), so totality is two uniform calls
(`stabLam_eval_total` for the LHS lam body, `…instantiateTopNat…`/closed-eval for
the RHS) — replacing the previously-estimated ~50-70 LOC of bespoke `Term.eval`
discharge per leaf with ~1 helper invocation.  This is the cost-collapse the
optimization delivers. -/

/-- `FormulaDefined` for the `stabAtClosedIteLam` leaf shape:
`eqPauli (stabAt (closed (stabLam (ite cond thenP elseP))) (closed q)) (closed rhs)`,
from (i) eval-totality of the lam body `ite cond thenP elseP` at every extended env,
and (ii) eval-totality of the closed `rhs`.  `q` is pure.  The LHS is discharged by
`stabLam_eval_total`; the RHS by `sterm_eval_closed`. -/
theorem formulaDefined_stabAtClosedIteLam {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {cond : Term (arity + 1) .bool} {thenP elseP : Term (arity + 1) .pauli}
    {q : Term arity .nat} {rhs : Term arity .pauli}
    (hq : SFormula.PureNatTerm q)
    (hbody : ∀ qv, ∃ p, Term.eval cb fuel (.ite cond thenP elseP) (Env.cons qv rho) = some p)
    (hrhs : ∃ v, Term.eval cb fuel rhs rho = some v) :
    SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
        (SC.closed rhs)) :=
  formulaDefined_eqPauli
    (by
      obtain ⟨p, hp⟩ := stabLam_eval_total hq cb fuel rho hbody
      refine ⟨p, ?_⟩
      simpa [SC.closed, STerm.eval, Term.eval, bind, Option.bind] using hp)
    (sterm_eval_closed hrhs)

/-! ## `StabTotalUpTo` providers for the surface stabilizers

The two stab-level atoms (`eqStabUpTo`/`commutesUpTo`/`weightLe`) need
`StabTotalUpTo nv` of the stabilizer arguments.  The stabilizers occurring in the
surface obligations are: the recursive `recCall` at the literal distance, the
closed `rowCut`/`colCut`/bridge cuts, and the open `E`.  We package the
totality facts already proved in `SurfaceRecConvergence`/`SurfaceBridgeTotality`
into the `StabTotalUpTo` shape. -/

/-- The recursive surface stabilizer `recCall (natLit (2m+3)) (natLit k)` is total
up to `(2m+3)^2` at fuel `≥ m+2` — repackaged from `recCall_total`. -/
theorem stabTotalUpTo_recCall (m k fuel : Nat) (hfuel : m + 2 ≤ fuel) {arity : Nat}
    (rho : Env arity) :
    ∃ sa, Term.eval Surface.code.body fuel
        (.recCall (.natLit (2 * m + 3)) (.natLit k)) rho = some sa ∧
      StabTotalUpTo ((2 * m + 3) * (2 * m + 3)) sa :=
  recCall_total m k fuel hfuel rho

/-- The recursive surface stabilizer at the bridge fuel, total up to `nQubits`. -/
theorem stabTotalUpTo_recCall_bridgeFuel (D : OddSurfaceDistance) (k : Nat) {arity : Nat}
    (rho : Env arity) :
    ∃ sa, Term.eval Surface.code.body (D.distance + 2)
        (.recCall (.natLit D.distance) (.natLit k)) rho = some sa ∧
      StabTotalUpTo (Surface.nQubits D.distance) sa :=
  recCall_total_at_bridgeFuel D k rho

/-- A closed `rowCut` inner term is everywhere total (its eval is `some (g · )`). -/
theorem stabTotalUpTo_rowCutInner {arity : Nat} (dist : Nat) (cb : Term 2 .stab)
    (fuel rv n : Nat) (idx : Term arity .nat) (rho : Env arity)
    (hidx : Term.eval cb fuel idx rho = some rv) :
    ∃ sa, Term.eval cb fuel (rowCutInnerTerm dist idx) rho = some sa ∧
      StabTotalUpTo n sa :=
  ⟨_, rowCutInnerTerm_eval dist cb fuel rv idx rho hidx, StabTotalUpTo.ofTotal⟩

/-- A closed `colCut` inner term is everywhere total. -/
theorem stabTotalUpTo_colCutInner {arity : Nat} (dist : Nat) (cb : Term 2 .stab)
    (fuel cv n : Nat) (idx : Term arity .nat) (rho : Env arity)
    (hidx : Term.eval cb fuel idx rho = some cv) :
    ∃ sa, Term.eval cb fuel (colCutInnerTerm dist idx) rho = some sa ∧
      StabTotalUpTo n sa :=
  ⟨_, colCutInnerTerm_eval dist cb fuel cv idx rho hidx, StabTotalUpTo.ofTotal⟩

/-! ## Axiom audit -/

#print axioms stabEqUpTo_total
#print axioms parityUpTo_total
#print axioms weightUpTo_total
#print axioms formulaDefined_eqNat
#print axioms formulaDefined_eqBool
#print axioms formulaDefined_eqPauli
#print axioms formulaDefined_localCommutesAt
#print axioms formulaDefined_not
#print axioms formulaDefined_and
#print axioms formulaDefined_or
#print axioms formulaDefined_imp
#print axioms formulaDefined_eqStabUpTo
#print axioms formulaDefined_commutesUpTo
#print axioms formulaDefined_weightLe
#print axioms formulaDefined_eqPauli_closed
#print axioms formulaDefined_eqPauli_closedPure
#print axioms sterm_eval_closed
#print axioms sterm_eval_anticommutes
#print axioms sterm_eval_pauliMul
#print axioms sterm_eval_stabAt
#print axioms sterm_eval_boundStab_at
#print axioms stabTotalUpTo_recCall
#print axioms stabTotalUpTo_recCall_bridgeFuel
#print axioms stabTotalUpTo_rowCutInner
#print axioms stabTotalUpTo_colCutInner

end QHL.CodeLang.Surface.Verify
