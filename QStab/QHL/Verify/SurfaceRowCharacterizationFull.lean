import QStab.QHL.Verify.SurfaceRowCharacterizationSym

/-!
# Parametric generated-row entry characterization with a genuinely discharged
  `OddSurfaceDistance.index` induction.

`SurfaceRowCharacterizationSym.lean` validates the recursion *chain* but leaves
the inductive step STUBBED: `surfaceD5Rec_k5_interior_withIH` takes the inner
characterization (the IH) as an explicit ARGUMENT, and the distance is the fixed
literal `5`.

This file removes that stub.  It builds, by structural recursion on the index
`m` of an `OddSurfaceDistance`, a parametric per-entry characterization whose
recursive (`d ≥ 5`) case supplies the IH *from the recursion itself* — there is
no `ih` hypothesis in the signature.  The inner-code reference produced by the
recursive peel (`recCall (d-2) …`) is resolved by the recursive call at index
`m-1`, exactly the structural heart that the distance proof's `O(d)`-deep tree
consumes.

Nothing here adds a trusted rule, uses `native_decide`, `Formula.check`,
`Formula.eval`-as-distance, `deriveTrue?`, `admit`, or a new axiom.  Everything is
built from the foundation combinators of
`SurfaceRowCharacterization{,Sym}.lean` (themselves only `PureFamilyDerivA`
constructors) plus `arithBool`-discharged closed numeric guards.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## A distance term keyed to an index

The recursion descends the index `m`.  At each layer the *distance term* fed to
the foundation combinators is allowed to be any pure Nat term that numerically
equals `oddDistance m` — not just the literal `.natLit (oddDistance m)`.  This is
essential: the recursive peel produces the inner distance argument as the
*unreduced* term `.sub dT (.natLit 2)`, which evaluates to `oddDistance (m-1)`
but is a distinct `Term` tree from `.natLit (oddDistance (m-1))`.  Carrying a
"`dT` evaluates to `oddDistance m`" certificate lets the IH plug in at the
unreduced inner term directly. -/

/-- A pure Nat distance term together with a proof it evaluates (at every fuel,
under the canonical body) to `oddDistance m`. -/
structure DistAt (m : Nat) where
  dT : Term 0 .nat
  pure : SFormula.PureNatTerm dT
  evalsTo : ∀ {fuel : Nat} (rho : Env 0),
    Term.eval Surface.code.body fuel dT rho = some (oddDistance m)

/-- The literal distance term at index `m`. -/
def DistAt.lit (m : Nat) : DistAt m where
  dT := .natLit (oddDistance m)
  pure := SFormula.PureNatTerm.nat (oddDistance m)
  evalsTo := by intro fuel rho; simp [Term.eval]

/-- Descend the distance term one recursion layer: `dT - 2` evaluates to
`oddDistance (m-1)` when `dT` evaluates to `oddDistance m` and `m ≥ 1`.  Used to
feed the IH the *unreduced* inner distance argument the recursive peel produces. -/
def DistAt.pred {m : Nat} (D : DistAt (m + 1)) : DistAt m where
  dT := .sub D.dT (.natLit 2)
  pure := SFormula.PureNatTerm.sub D.pure (SFormula.PureNatTerm.nat 2)
  evalsTo := by
    intro fuel rho
    simp only [Term.eval, D.evalsTo rho]
    have : oddDistance (m + 1) - 2 = oddDistance m := by
      simp [oddDistance]; omega
    simp [this]

/-! ## Center cell of the recursive Surface code

The *center* stabilizer/qubit of the distance-`d` Surface code is the bulk
plaquette and data qubit at grid position `((d-1)/2, (d-1)/2)` / `(d/2, d/2)`.
It is the canonical self-similar cell: at every recursion layer it is an interior
bulk cell whose inner reference is the center cell of the distance-`(d-2)` code,
bottoming out at the `d = 3` base cell `(k = 3, q = 4)`, which carries `Z`.

These closed forms are *numbers*; the parametric lemma below carries them as
`evalsTo` certificates so the symbolic peel can discharge each grid guard. -/

/-- Center stabilizer index of the distance-`oddDistance m` code. -/
def centerK (m : Nat) : Nat :=
  let d := oddDistance m
  ((d - 1) / 2) * (d - 1) + (d - 1) / 2

/-- Center qubit index of the distance-`oddDistance m` code. -/
def centerQ (m : Nat) : Nat :=
  let d := oddDistance m
  (d / 2) * d + d / 2

/-! ## Closed-guard discharge from an evaluation certificate

For the parametric peel the grid guards are closed arithmetic booleans built from
`dT`, `kT`, `qT` (all closed pure terms with known values), so they evaluate to a
fixed boolean.  `guardTrueEval`/`guardFalseEval` discharge such a guard from an
explicit `Term.eval` proof — the same `arithBool` route used by `guardTrue`, but
without the literal `decide`/`rfl` defaults (the terms here are not literals). -/

/-- A pure term lies in the arithmetic-boolean *term* fragment.  This is the
bridge from the `PureTerm` certificate to the syntactic fragment gate that
`PureFamilyDerivA.arithBool` requires, valid for non-literal pure terms. -/
theorem pureTerm_in_fragment {arity : Nat} {ty : Ty} {x : Term arity ty}
    (hx : SFormula.PureTerm x) : ArithBoolFragment.term x = true := by
  induction hx with
  | var v => rfl
  | natLit n => rfl
  | boolLit b => rfl
  | add _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | sub _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | mul _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | div _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | mod _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | eqNat _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | ltNat _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | leNat _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | not _ iha => simp [ArithBoolFragment.term, iha]
  | and _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | or _ _ iha ihb => simp [ArithBoolFragment.term, iha, ihb]
  | ite _ _ _ ihc iha ihb => simp [ArithBoolFragment.term, ihc, iha, ihb]

/-- The `eqBool (closed cond) (b v)` formula is in the arithmetic-boolean
fragment whenever `cond` is a pure boolean term. -/
theorem pureBool_eqBool_in_fragment {cond : Term 0 .bool} (v : Bool)
    (hc : SFormula.PureBoolTerm cond) :
    arithBoolFragment (.eqBool (SC.closed cond) (SC.b v)) = true := by
  simp [arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term, pureTerm_in_fragment hc]

def guardTrueEval {fuel : Nat} {cond : Term 0 .bool}
    (hc : SFormula.PureBoolTerm cond)
    (hEval : ∀ (rho : Env 0), Term.eval Surface.code.body fuel cond rho = some true) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed cond) (SC.b true)) :=
  PureFamilyDerivA.arithBool _ (pureBool_eqBool_in_fragment true hc) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho])

def guardFalseEval {fuel : Nat} {cond : Term 0 .bool}
    (hc : SFormula.PureBoolTerm cond)
    (hEval : ∀ (rho : Env 0), Term.eval Surface.code.body fuel cond rho = some false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed cond) (SC.b false)) :=
  PureFamilyDerivA.arithBool _ (pureBool_eqBool_in_fragment false hc) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho])

/-! ## Instantiate-of-weaken cancellation

The outer recursive-entry `ite` conditions reference the distance/index terms
through `Term.lift 0 dT` / `Term.lift 0 kT` (weakened under the `stabLam`-bound
qubit variable).  After the qubit substitution `Term.instantiateTopNat qT`, every
such `lift 0 _` collapses back to its plain closed form.  This is the generic
cancellation `instantiateNatAt cutoff x (lift cutoff t) = t`, which lets a
consumer transport the plain-form grid guards (`bulkGuardT dT kT`, …) to the
`instantiateTopNat`-of-lift form the peel combinators demand. -/

theorem instTop_lift {arity : Nat} {ty : Ty} (t : Term arity ty) :
    ∀ (cutoff : Nat) (x : Term arity .nat) (hcut : cutoff ≤ arity),
      Term.instantiateNatAt cutoff x hcut (Term.lift cutoff t) = t := by
  induction t with
  | var v =>
      intro cutoff x hcut
      simp only [Term.lift, Term.instantiateNatAt, Term.weakenVar]
      by_cases h : v.val < cutoff
      · simp only [h, dif_pos]
      · rw [dif_neg h]
        have h1 : ¬ (v.val + 1 < cutoff) := by omega
        have h2 : ¬ (v.val + 1 = cutoff) := by omega
        simp only [h1, h2, dite_false, Nat.add_sub_cancel, Fin.eta]
  | _ => intros; simp_all [Term.instantiateNatAt, Term.lift]

/-- The closed-term specialization used by the peel: `instantiateTopNat x` undoes
`Term.lift 0` on any closed term. -/
theorem instTopNat_weaken {ty : Ty} (x : Term 0 .nat) (t : Term 0 ty) :
    Term.instantiateTopNat x (Term.lift 0 t) = t :=
  instTop_lift t 0 x (Nat.zero_le 0)

/-! ## Parametric recursive interior-cell peel

For symbolic `dT`/`kT`/`qT` (closed pure terms) satisfying the three grid
guards (outer bulk `kT < bulkCount`, `interiorCell`, `inside`), the generated
recursive entry stabilizer-lambda at `qT` equals the inner-code reference
`stabAt (recCall (dT-2) interiorK) innerQ`.  The three guards are supplied as
`PureFamilyDerivA` derivations (so a consumer discharges them from its own
`evalsTo` certificates via `guardTrueEval`).  The leaf is the honest unreduced
inner reference (exactly what `instantiateTopNat qT` produces), captured by
`eqPauliRefl`. -/

/-- The grid-coordinate helper terms of the recursive entry, substituted at
`dT`/`kT`/`qT`. -/
def dm1T (dT : Term 0 .nat) : Term 0 .nat := .sub dT (.natLit 1)
def bulkCountT (dT : Term 0 .nat) : Term 0 .nat := .mul (dm1T dT) (dm1T dT)
def rT (dT kT : Term 0 .nat) : Term 0 .nat := .div kT (dm1T dT)
def cT (dT kT : Term 0 .nat) : Term 0 .nat := .mod kT (dm1T dT)
def innerDT (dT : Term 0 .nat) : Term 0 .nat := .sub dT (.natLit 2)
def innerDm1T (dT : Term 0 .nat) : Term 0 .nat := .sub (innerDT dT) (.natLit 1)
def lastCellT (dT : Term 0 .nat) : Term 0 .nat := .sub (dm1T dT) (.natLit 1)
def rowT (dT qT : Term 0 .nat) : Term 0 .nat := .div qT dT
def colT (dT qT : Term 0 .nat) : Term 0 .nat := .mod qT dT

/-- Outer bulk guard `kT < (dT-1)^2`. -/
def bulkGuardT (dT kT : Term 0 .nat) : Term 0 .bool :=
  .ltNat kT (bulkCountT dT)

/-- `interiorCell` guard `1 ≤ r < lastCell ∧ 1 ≤ c < lastCell`. -/
def interiorCellGuardT (dT kT : Term 0 .nat) : Term 0 .bool :=
  band4 (le (.natLit 1) (rT dT kT)) (.ltNat (rT dT kT) (lastCellT dT))
    (le (.natLit 1) (cT dT kT)) (.ltNat (cT dT kT) (lastCellT dT))

/-- `inside` guard `1 ≤ row < dm1 ∧ 1 ≤ col < dm1`. -/
def insideGuardT (dT qT : Term 0 .nat) : Term 0 .bool :=
  band4 (le (.natLit 1) (rowT dT qT)) (.ltNat (rowT dT qT) (dm1T dT))
    (le (.natLit 1) (colT dT qT)) (.ltNat (colT dT qT) (dm1T dT))

/-- `interiorK = (r-1)*innerDm1 + (c-1)`. -/
def interiorKT (dT kT : Term 0 .nat) : Term 0 .nat :=
  .add (.mul (.sub (rT dT kT) (.natLit 1)) (innerDm1T dT))
    (.sub (cT dT kT) (.natLit 1))

/-- `innerQ = (row-1)*innerD + (col-1)`. -/
def innerQT (dT qT : Term 0 .nat) : Term 0 .nat :=
  .add (.mul (.sub (rowT dT qT) (.natLit 1)) (innerDT dT))
    (.sub (colT dT qT) (.natLit 1))

/-- The inner-code reference produced by the interior cell peel. -/
def centerInnerRef (dT kT qT : Term 0 .nat) : Term 0 .pauli :=
  .stabAt (.recCall (innerDT dT) (interiorKT dT kT)) (innerQT dT qT)

/-- **Parametric recursive interior-cell peel.**

Given the three grid guards as derivations, the generated recursive entry
stabilizer-lambda at `qT` equals the inner-code reference `centerInnerRef`. -/
def recInteriorPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (centerInnerRef dT kT qT))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Term.lift, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  -- Step 1: strip `stabLam`, select the outer closed `bulk` branch.
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  -- Step 2: push the qubit instantiation through the residual `ite` tree.
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  -- Step 3: select `interiorCell` (via `hInterior`), then `inside` (via `hInside`).
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hInteriorG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hInsideG)
      (PureFamilyDerivA.eqPauliRefl _))
  case hInteriorG =>
    have heq : interiorCellGuardT dT kT
        = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
            (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
              (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
                ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
      simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T]
    rw [heq] at hInterior; exact hInterior
  case hInsideG =>
    have heq : insideGuardT dT qT
        = ((Term.natLit 1).leNat (qT.div dT)).and
            (((qT.div dT).ltNat (dT.sub (Term.natLit 1))).and
              (((Term.natLit 1).leNat (qT.mod dT)).and
                ((qT.mod dT).ltNat (dT.sub (Term.natLit 1))))) := by
      simp only [insideGuardT, band4, band3, le, rowT, colT, dm1T]
    simp only [Nat.lt_irrefl, dite_false, dite_true]
    rw [heq] at hInside; exact hInside

/-! ## Numeric value certificates for the center cell

For the recursion, the inner-cell index/qubit terms `interiorKT dT kT` /
`innerQT dT qT` must be shown to evaluate to the *next-layer* center values
`centerK m` / `centerQ m`, given that `dT`/`kT`/`qT` evaluate to the current
layer's `oddDistance (m+1)` / `centerK (m+1)` / `centerQ (m+1)`.  These are the
arithmetic facts the IH consumes; they are pure `Nat` identities about the
self-similar center recursion. -/

/-- Closed form of the center stabilizer index: `centerK m = (m+1)*(2m+3)`. -/
theorem centerK_closed (m : Nat) : centerK m = (m + 1) * (2 * m + 3) := by
  simp only [centerK, oddDistance]
  have h1 : (2 * m + 3 - 1) / 2 = m + 1 := by omega
  have h2 : 2 * m + 3 - 1 = 2 * m + 2 := by omega
  rw [h1, h2]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
  omega

/-- Closed form of the center qubit index: `centerQ m = (m+1)*(2m+4)`. -/
theorem centerQ_closed (m : Nat) : centerQ m = (m + 1) * (2 * m + 4) := by
  simp only [centerQ, oddDistance]
  have h1 : (2 * m + 3) / 2 = m + 1 := by omega
  rw [h1]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
  omega

/-- Center stabilizer index of distance `oddDistance (m+1)` divided by `dm1` gives
its grid row `m+2`; modulo gives its grid column `m+2`. -/
theorem centerK_div (m : Nat) :
    centerK (m + 1) / (oddDistance (m + 1) - 1) = m + 2 := by
  rw [centerK_closed]; simp only [oddDistance]
  have hd : 2 * (m + 1) + 3 - 1 = (m + 2) * 2 := by omega
  have he : (m + 1 + 1) * (2 * (m + 1) + 3) = (m + 2) + (m + 2) * 2 * (m + 2) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
    omega
  rw [hd, he, Nat.add_mul_div_left _ _ (by omega : 0 < (m + 2) * 2),
    Nat.div_eq_of_lt (by omega : m + 2 < (m + 2) * 2)]
  omega

theorem centerK_mod (m : Nat) :
    centerK (m + 1) % (oddDistance (m + 1) - 1) = m + 2 := by
  rw [centerK_closed]; simp only [oddDistance]
  have hd : 2 * (m + 1) + 3 - 1 = (m + 2) * 2 := by omega
  have he : (m + 1 + 1) * (2 * (m + 1) + 3) = (m + 2) + (m + 2) * 2 * (m + 2) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
    omega
  rw [hd, he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : m + 2 < (m + 2) * 2)]

theorem centerQ_div (m : Nat) :
    centerQ (m + 1) / oddDistance (m + 1) = m + 2 := by
  rw [centerQ_closed]; simp only [oddDistance]
  have he : (m + 1 + 1) * (2 * (m + 1) + 4) = (m + 2) + (2 * (m + 1) + 3) * (m + 2) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
    omega
  rw [he, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * (m + 1) + 3),
    Nat.div_eq_of_lt (by omega : m + 2 < 2 * (m + 1) + 3)]
  omega

theorem centerQ_mod (m : Nat) :
    centerQ (m + 1) % oddDistance (m + 1) = m + 2 := by
  rw [centerQ_closed]; simp only [oddDistance]
  have he : (m + 1 + 1) * (2 * (m + 1) + 4) = (m + 2) + (2 * (m + 1) + 3) * (m + 2) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
    omega
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : m + 2 < 2 * (m + 1) + 3)]

/-- The center recursion's arithmetic core: the interior index of the center cell
at distance `oddDistance (m+1)` maps to `centerK m` one layer down. -/
theorem centerK_step (m : Nat) :
    ((centerK (m + 1) / (oddDistance (m + 1) - 1) - 1) * ((oddDistance (m + 1) - 2) - 1)
      + (centerK (m + 1) % (oddDistance (m + 1) - 1) - 1)) = centerK m := by
  rw [centerK_div, centerK_mod, centerK_closed]
  simp only [oddDistance]
  have hsub : 2 * (m + 1) + 3 - 2 - 1 = 2 * m + 2 := by omega
  have hm : m + 2 - 1 = m + 1 := by omega
  rw [hsub, hm]
  -- goal: (m+1)*(2m+2) + (m+1) = (m+1)*(2m+3)
  have he : (m + 1) * (2 * m + 3) = (m + 1) * (2 * m + 2) + (m + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
    omega
  omega

/-- The center recursion's qubit core: center qubit maps to `centerQ m` one layer
down. -/
theorem centerQ_step (m : Nat) :
    ((centerQ (m + 1) / oddDistance (m + 1) - 1) * (oddDistance (m + 1) - 2)
      + (centerQ (m + 1) % oddDistance (m + 1) - 1)) = centerQ m := by
  rw [centerQ_div, centerQ_mod, centerQ_closed]
  simp only [oddDistance]
  have hsub : 2 * (m + 1) + 3 - 2 = 2 * m + 3 := by omega
  have hm : m + 2 - 1 = m + 1 := by omega
  rw [hsub, hm]
  have he : (m + 1) * (2 * m + 4) = (m + 1) * (2 * m + 3) + (m + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_one, Nat.one_mul]
    omega
  omega

/-! ## Eval certificates for the inner index/qubit terms

The recursion feeds the IH the *unreduced* inner index/qubit terms
`interiorKT D.dT kT` / `innerQT D.dT qT`.  These are pure Nat terms; their values
are the next-layer center indices (`centerK m` / `centerQ m`), which is exactly
the `centerK_step` / `centerQ_step` arithmetic.  The two lemmas below package that
as `DistAt`-style evaluation certificates. -/

/-- `interiorKT dT kT` evaluates to `centerK m` when `dT`/`kT` evaluate to the
distance/center index at index `m+1`. -/
theorem interiorKT_evalsTo {m : Nat} {dT kT : Term 0 .nat} {fuel : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some (oddDistance (m + 1)))
    (hkv : Term.eval Surface.code.body fuel kT rho = some (centerK (m + 1))) :
    Term.eval Surface.code.body fuel (interiorKT dT kT) rho = some (centerK m) := by
  simp only [interiorKT, innerDm1T, innerDT, rT, cT, dm1T, Term.eval, hdv, hkv,
    Option.bind, Option.pure_def, Option.bind_eq_bind]
  rw [centerK_step]

/-- `innerQT dT qT` evaluates to `centerQ m` when `dT`/`qT` evaluate to the
distance/center qubit at index `m+1`. -/
theorem innerQT_evalsTo {m : Nat} {dT qT : Term 0 .nat} {fuel : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some (oddDistance (m + 1)))
    (hqv : Term.eval Surface.code.body fuel qT rho = some (centerQ (m + 1))) :
    Term.eval Surface.code.body fuel (innerQT dT qT) rho = some (centerQ m) := by
  simp only [innerQT, innerDT, rowT, colT, Term.eval, hdv, hqv,
    Option.bind, Option.pure_def, Option.bind_eq_bind]
  rw [centerQ_step]

/-! ## Purity of the grid guards

Each grid guard is a pure boolean term (built from `div`/`mod`/`sub`/`ltNat`/
`leNat`/`and`), so `guardTrueEval` accepts it once we supply purity certificates
for `dT`/`kT`/`qT`. -/

def bulkGuardT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (bulkGuardT dT kT) :=
  SFormula.PureBoolTerm.ltNat hk
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))

def interiorCellGuardT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (interiorCellGuardT dT kT) := by
  have hdm1 : SFormula.PureNatTerm (dm1T dT) :=
    SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hr : SFormula.PureNatTerm (rT dT kT) := SFormula.PureNatTerm.div hk hdm1
  have hc : SFormula.PureNatTerm (cT dT kT) := SFormula.PureNatTerm.mod hk hdm1
  have hlast : SFormula.PureNatTerm (lastCellT dT) :=
    SFormula.PureNatTerm.sub hdm1 (SFormula.PureNatTerm.nat 1)
  exact SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.leNat (SFormula.PureNatTerm.nat 1) hr)
    (SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.ltNat hr hlast)
      (SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.leNat (SFormula.PureNatTerm.nat 1) hc)
        (SFormula.PureBoolTerm.ltNat hc hlast)))

def insideGuardT_pure {dT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (insideGuardT dT qT) := by
  have hdm1 : SFormula.PureNatTerm (dm1T dT) :=
    SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hrow : SFormula.PureNatTerm (rowT dT qT) := SFormula.PureNatTerm.div hq hd
  have hcol : SFormula.PureNatTerm (colT dT qT) := SFormula.PureNatTerm.mod hq hd
  exact SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.leNat (SFormula.PureNatTerm.nat 1) hrow)
    (SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.ltNat hrow hdm1)
      (SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.leNat (SFormula.PureNatTerm.nat 1) hcol)
        (SFormula.PureBoolTerm.ltNat hcol hdm1)))

/-! ## Numeric facts: the center cell satisfies all three grid guards -/

theorem center_bulk_lt (m : Nat) :
    centerK (m + 1) < (oddDistance (m + 1) - 1) * (oddDistance (m + 1) - 1) := by
  rw [centerK_closed]; simp only [oddDistance]
  have hd : 2 * (m + 1) + 3 - 1 = 2 * m + 4 := by omega
  rw [hd]
  have hmm : m * (2 * m) = 2 * (m * m) := by rw [Nat.mul_left_comm]
  have hmm4 : (2 * m) * (2 * m) = 4 * (m * m) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm m 2 m, ← Nat.mul_assoc]
  have e1 : (m + 1 + 1) * (2 * (m + 1) + 3) = 2 * (m * m) + 9 * m + 10 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have e2 : (2 * m + 4) * (2 * m + 4) = 4 * (m * m) + 16 * m + 16 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  rw [e1, e2]; omega

/-! ## Grid-guard derivations at the center cell (recursive case)

For the recursive step the consumer must supply `recInteriorPeel` with the three
grid guards as `PureFamilyDerivA` derivations.  Each is discharged by
`guardTrueEval`, with the boolean evaluating to `true` at the center values: the
center cell is a bulk interior cell whose qubit is inside the interior block, at
every layer `m+1`. -/

/-- The bulk guard holds at the center cell of distance `oddDistance (m+1)`. -/
def centerBulkGuard {fuel : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some (oddDistance (m + 1)))
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some (centerK (m + 1))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)) :=
  guardTrueEval (bulkGuardT_pure hd hk) (by
    intro rho
    simp only [bulkGuardT, bulkCountT, dm1T, Term.eval, hdv rho, hkv rho,
      Option.bind, Option.pure_def, Option.bind_eq_bind, Option.some.injEq,
      decide_eq_true_eq]
    exact center_bulk_lt m)

/-- The interior-cell guard holds at the center cell. -/
def centerInteriorGuard {fuel : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some (oddDistance (m + 1)))
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some (centerK (m + 1))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b true)) :=
  guardTrueEval (interiorCellGuardT_pure hd hk) (by
    intro rho
    simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T, Term.eval,
      hdv rho, hkv rho, Option.bind, Option.pure_def, Option.bind_eq_bind]
    rw [centerK_div, centerK_mod]
    simp only [oddDistance, decide_eq_true_eq]
    have hb1 : (1 : Nat) ≤ m + 2 := by omega
    have hb2 : m + 2 < 2 * (m + 1) + 3 - 1 - 1 := by omega
    rw [if_pos hb1, if_pos hb2, if_pos hb1]
    simp only [Option.some.injEq, decide_eq_true_eq]; omega)

/-- The inside guard holds at the center cell. -/
def centerInsideGuard {fuel : Nat} {dT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some (oddDistance (m + 1)))
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some (centerQ (m + 1))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)) :=
  guardTrueEval (insideGuardT_pure hd hq) (by
    intro rho
    simp only [insideGuardT, band4, band3, le, rowT, colT, dm1T, Term.eval,
      hdv rho, hqv rho, Option.bind, Option.pure_def, Option.bind_eq_bind]
    rw [centerQ_div, centerQ_mod]
    simp only [oddDistance, decide_eq_true_eq]
    have hb1 : (1 : Nat) ≤ m + 2 := by omega
    have hb2 : m + 2 < 2 * (m + 1) + 3 - 1 := by omega
    rw [if_pos hb1, if_pos hb2, if_pos hb1]
    simp only [Option.some.injEq, decide_eq_true_eq]; omega)

/-! ## Base-case peel: the `d = 3` center cell carries `Z`

At the base index `m = 0` (`d = 3`) the center cell is the bulk plaquette
`k = 3` at grid `(1,1)`, qubit `q = 4` at grid `(1,1)`.  It carries `Z`.  This is
the recursion's base leaf, parametric in the (symbolic) `DistAt 0` distance term
and the center index/qubit terms (carried with their `evalsTo 3`/`evalsTo 3`/
`evalsTo 4` certificates so the bulk band + kind guards are dischargeable). -/

/-- The bulk band guard of the `baseEntry` at distance `dT`, stabilizer `kT`,
qubit `qT`: `band3 (orEqSucc row r) (orEqSucc col c) (kT < bulkCount)` with
`row = qT/dT`, `col = qT%dT`, `r = kT/(dT-1)`, `c = kT%(dT-1)`. -/
def baseBulkBandGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  band3
    (orEqSucc (.div qT dT) (.div kT (dm1T dT)))
    (orEqSucc (.mod qT dT) (.mod kT (dm1T dT)))
    (.ltNat kT (bulkCountT dT))

/-- The plaquette-kind guard of the `baseEntry`: `(r + c) % 2 = 0` (i.e. the cell
is a `Z`-plaquette), with `r = kT/(dT-1)`, `c = kT%(dT-1)`. -/
def baseKindGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  .eqNat (.mod (.add (.div kT (dm1T dT)) (.mod kT (dm1T dT))) (.natLit 2)) (.natLit 0)

/-- **Parametric base-entry bulk-cell peel.**

For symbolic `dT`/`kT`/`qT` (closed pure terms) satisfying the outer bulk guard
(`kT < bulkCount`), the bulk band guard, and the kind guard (`(r+c)%2 = 0`), the
generated base entry stabilizer-lambda at `qT` carries `Z`.  The peel selects the
closed outer `bulk` branch (guard `kT < bulkCount`), the inner band branch (via
`hBand`), then the closed kind branch (via `hKind`), landing on `Z`. -/
def recBasePeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuard dT kT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Term.lift, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  -- Step 1: strip `stabLam`, select the outer closed `bulk` branch (guard `kT < bulkCount`).
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  -- Step 2: push the qubit instantiation through the residual bulk inner `ite` tree.
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  -- Step 3: select the band branch (via `hBand`), then the kind branch (via `hKind`), landing on `Z`.
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBandG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hKindG)
      (PureFamilyDerivA.eqPauliRefl _))
  case hBandG =>
    have heq : baseBulkBandGuard dT kT qT
        = ((((qT.div dT).eqNat (kT.div (dT.sub (Term.natLit 1)))).or
                ((qT.div dT).eqNat ((kT.div (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
            ((((qT.mod dT).eqNat (kT.mod (dT.sub (Term.natLit 1)))).or
                  ((qT.mod dT).eqNat ((kT.mod (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
              (kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))) := by
      simp only [baseBulkBandGuard, band3, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hBand; exact hBand
  case hKindG =>
    have heq : baseKindGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).add (kT.mod (dT.sub (Term.natLit 1)))).mod
              (Term.natLit 2)).eqNat (Term.natLit 0) := by
      simp only [baseKindGuard, dm1T]
    rw [heq] at hKind; exact hKind

/-! ## Grid-guard derivations at the `d = 3` base center cell

For the recursion's base case the consumer supplies `recBasePeel` with the bulk
guard, bulk band guard, and kind guard.  At `m = 0` the center cell is `k = 3`,
`q = 4` of distance `d = 3`, so each guard evaluates numerically to `true`. -/

def baseBulkBandGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (baseBulkBandGuard dT kT qT) := by
  have hdm1 : SFormula.PureNatTerm (dm1T dT) :=
    SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) (SFormula.PureNatTerm.div hk hdm1))
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.div hk hdm1) (SFormula.PureNatTerm.nat 1))))
    (SFormula.PureBoolTerm.and
      (SFormula.PureBoolTerm.or
        (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) (SFormula.PureNatTerm.mod hk hdm1))
        (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd)
          (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mod hk hdm1) (SFormula.PureNatTerm.nat 1))))
      (SFormula.PureBoolTerm.ltNat hk (SFormula.PureNatTerm.mul hdm1 hdm1)))

def baseKindGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (baseKindGuard dT kT) := by
  have hdm1 : SFormula.PureNatTerm (dm1T dT) :=
    SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  exact SFormula.PureBoolTerm.eqNat
    (SFormula.PureNatTerm.mod
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.div hk hdm1) (SFormula.PureNatTerm.mod hk hdm1))
      (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 0)

/-- The base bulk guard `kT < bulkCount` holds at the `d = 3` center cell. -/
def baseCenterBulkGuard {fuel : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some (oddDistance 0))
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some (centerK 0)) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)) :=
  guardTrueEval (bulkGuardT_pure hd hk) (by
    intro rho
    have hd3 : Term.eval Surface.code.body fuel dT rho = some 3 := by
      rw [hdv rho]; rfl
    have hk3 : Term.eval Surface.code.body fuel kT rho = some 3 := by
      rw [hkv rho]; rfl
    simp only [bulkGuardT, bulkCountT, dm1T, Term.eval, hd3, hk3,
      Option.bind, Option.pure_def, Option.bind_eq_bind]
    decide)

/-- The base bulk band guard holds at the `d = 3` center cell. -/
def baseCenterBandGuard {fuel : Nat} {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some (oddDistance 0))
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some (centerK 0))
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some (centerQ 0)) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b true)) :=
  guardTrueEval (baseBulkBandGuard_pure hd hk hq) (by
    intro rho
    have hd3 : Term.eval Surface.code.body fuel dT rho = some 3 := by rw [hdv rho]; rfl
    have hk3 : Term.eval Surface.code.body fuel kT rho = some 3 := by rw [hkv rho]; rfl
    have hq4 : Term.eval Surface.code.body fuel qT rho = some 4 := by rw [hqv rho]; rfl
    simp only [baseBulkBandGuard, band3, orEqSucc, bulkCountT, dm1T, Term.eval,
      hd3, hk3, hq4, Option.bind, Option.pure_def, Option.bind_eq_bind]
    decide)

/-- The base kind guard holds at the `d = 3` center cell (`(r+c)%2 = 0`). -/
def baseCenterKindGuard {fuel : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some (oddDistance 0))
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some (centerK 0)) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuard dT kT)) (SC.b true)) :=
  guardTrueEval (baseKindGuard_pure hd hk) (by
    intro rho
    have hd3 : Term.eval Surface.code.body fuel dT rho = some 3 := by rw [hdv rho]; rfl
    have hk3 : Term.eval Surface.code.body fuel kT rho = some 3 := by rw [hkv rho]; rfl
    simp only [baseKindGuard, dm1T, Term.eval, hd3, hk3,
      Option.bind, Option.pure_def, Option.bind_eq_bind]
    decide)

/-! ## Distance-branch guards keyed to the index

The foundation combinators `surfaceCodeBaseEntryEq` / `surfaceCodeRecursiveEntryEq`
select the base / recursive body branch from the closed guard `dT < 5`.  At index
`0` the distance term evaluates to `3` (`< 5`, base branch); at index `m+1` it
evaluates to `2m+5 ≥ 7` (`≥ 5`, recursive branch).  These two derivations are the
parametric analogues of `closedLtFiveTrue` / `closedLtFiveFalse`. -/

def distLtFiveTrue_of_DistAt {fuel : Nat} (D : DistAt 0) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat D.dT (n5 : Term 0 .nat))) (SC.b true)) :=
  guardTrueEval (SFormula.PureBoolTerm.ltNat D.pure (SFormula.PureNatTerm.nat 5)) (by
    intro rho
    simp only [n5, Term.eval, D.evalsTo rho, Option.bind, Option.pure_def, Option.bind_eq_bind]
    decide)

def distLtFiveFalse_of_DistAt {fuel m : Nat} (D : DistAt (m + 1)) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat D.dT (n5 : Term 0 .nat))) (SC.b false)) :=
  guardFalseEval (SFormula.PureBoolTerm.ltNat D.pure (SFormula.PureNatTerm.nat 5)) (by
    intro rho
    have hlt : ¬ (oddDistance (m + 1) < 5) := by simp only [oddDistance]; omega
    simp only [n5, Term.eval, D.evalsTo rho, Option.bind, Option.pure_def, Option.bind_eq_bind,
      Option.some.injEq, decide_eq_false_iff_not, hlt, not_false_eq_true])

/-! ## The genuinely-recursive center characterization

This is the deliverable: a per-entry characterization recursive on
`OddSurfaceDistance.index`.  At index `m`, with a distance term `D : DistAt m`
and pure index/qubit terms `kT`/`qT` carrying their `centerK m` / `centerQ m`
evaluation certificates, the generated code row `recCall D.dT kT` at `qT` carries
`Z`.

The induction is **genuinely discharged**: the recursive (`m+1`) case applies the
function to itself at index `m` with the inner index/qubit terms produced by the
interior peel — there is NO `ih` hypothesis in the signature (contrast
`surfaceD5Rec_k5_interior_withIH`, which takes the IH as an argument). -/

def recCenterChar {fuel : Nat} :
    (m : Nat) → (D : DistAt m) → (kT qT : Term 0 .nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some (centerK m)) →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some (centerQ m)) →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall D.dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z)))
  | 0, D, kT, qT, hk, hq, hkv, hqv =>
      -- Base case: d = 3, center cell (k = 3, q = 4) is a bulk Z-plaquette.
      surfaceCodeBaseEntryEq (SC.n (nQubits 3)) D.dT kT qT (.pauliLit Pauli.Z)
        D.pure hk
        (distLtFiveTrue_of_DistAt D)
        (recBasePeel D.dT kT qT D.pure hk hq
          (baseCenterBulkGuard D.pure hk D.evalsTo hkv)
          (baseCenterBandGuard D.pure hk hq D.evalsTo hkv hqv)
          (baseCenterKindGuard D.pure hk D.evalsTo hkv))
  | m + 1, D, kT, qT, hk, hq, hkv, hqv =>
      -- Recursive case: d ≥ 5, interior cell references recCall (d-2) at the
      -- inner center cell, resolved by the recursive call at index m.
      surfaceCodeRecursiveEntryEq (SC.n (nQubits (oddDistance (m + 1)))) D.dT kT qT
        (.pauliLit Pauli.Z) D.pure hk
        (distLtFiveFalse_of_DistAt D)
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (recInteriorPeel D.dT kT qT D.pure hk hq
            (centerBulkGuard D.pure hk D.evalsTo hkv)
            (centerInteriorGuard D.pure hk D.evalsTo hkv)
            (centerInsideGuard D.pure hq D.evalsTo hqv))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.closedStabAtSplit
              (.recCall (innerDT D.dT) (interiorKT D.dT kT)) (innerQT D.dT qT))
            (recCenterChar m D.pred (interiorKT D.dT kT) (innerQT D.dT qT)
              (SFormula.PureNatTerm.add
                (SFormula.PureNatTerm.mul
                  (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.div hk
                    (SFormula.PureNatTerm.sub D.pure (SFormula.PureNatTerm.nat 1)))
                    (SFormula.PureNatTerm.nat 1))
                  (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub D.pure (SFormula.PureNatTerm.nat 2))
                    (SFormula.PureNatTerm.nat 1)))
                (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.mod hk
                  (SFormula.PureNatTerm.sub D.pure (SFormula.PureNatTerm.nat 1)))
                  (SFormula.PureNatTerm.nat 1)))
              (SFormula.PureNatTerm.add
                (SFormula.PureNatTerm.mul
                  (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.div hq D.pure)
                    (SFormula.PureNatTerm.nat 1))
                  (SFormula.PureNatTerm.sub D.pure (SFormula.PureNatTerm.nat 2)))
                (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.mod hq D.pure)
                  (SFormula.PureNatTerm.nat 1)))
              (fun rho => interiorKT_evalsTo rho (D.evalsTo rho) (hkv rho))
              (fun rho => innerQT_evalsTo rho (D.evalsTo rho) (hqv rho)))))

/-! ## Consumer-facing form over an `OddSurfaceDistance`

The literal-distance specialization: for every odd distance `D`, the *generated
code row* `recCall D.distance (centerK D.index)` at the center qubit
`centerQ D.index` carries `Z`.  This is the row-entry shape the distance-proof
consumers project, now established for ALL odd distances by the discharged
induction. -/

def centerRowEntryChar (D : OddSurfaceDistance) {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed ((.recCall (.natLit D.distance) (.natLit (centerK D.index))) : Term 0 .stab))
          (SC.closed ((.natLit (centerQ D.index)) : Term 0 .nat)))
        (SC.closed ((.pauliLit Pauli.Z) : Term 0 .pauli))) := by
  have h := recCenterChar (fuel := fuel) D.index (DistAt.lit D.index)
    (.natLit (centerK D.index)) (.natLit (centerQ D.index))
    (SFormula.PureNatTerm.nat _) (SFormula.PureNatTerm.nat _)
    (by intro rho; simp [Term.eval]) (by intro rho; simp [Term.eval])
  simpa only [DistAt.lit, OddSurfaceDistance.distance] using h

/-! ## Axiom audit and non-vacuity cross-checks -/

-- The discharged-induction headline and its building blocks:
#print axioms recCenterChar
#print axioms recInteriorPeel
#print axioms recBasePeel
#print axioms centerRowEntryChar

/-- Non-vacuity cross-check at `d = 5` (index 1): the center cell is `(k = 10,
q = 12)`, recovering a concrete `Z` entry through the discharged recursion (one
genuine recursion layer down to the `d = 3` base). -/
def recCenterChar_d5_check {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed ((.recCall (.natLit 5) (.natLit 10)) : Term 0 .stab)) (SC.closed ((.natLit 12) : Term 0 .nat)))
        (SC.closed ((.pauliLit Pauli.Z) : Term 0 .pauli))) :=
  centerRowEntryChar OddSurfaceDistance.d5

/-- Non-vacuity cross-check at `d = 7` (index 2): center `(k = 21, q = 24)`,
exercising TWO genuine recursion layers (`d = 7 → 5 → 3`). -/
def recCenterChar_d7_check {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed ((.recCall (.natLit 7) (.natLit 21)) : Term 0 .stab)) (SC.closed ((.natLit 24) : Term 0 .nat)))
        (SC.closed ((.pauliLit Pauli.Z) : Term 0 .pauli))) :=
  centerRowEntryChar OddSurfaceDistance.d7

end QHL.CodeLang.Surface.Verify
