import QStab.QHL.Verify.SurfaceRowsCommute.Router

/-!
# Rows-commute (pairwise generated-row commutation) — Families

The ∀∀-quantified different-type dispatch, the ∀∀ same-type dispatches, and instantiation at
the pair indices.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## The ∀∀-quantified DIFFERENT-type dispatch (`dispatchDiffType`)

`dispatchRouter` is fixed to `k1 = var 1` X-type, `k2 = var 0` Z-type and concludes
the canonical-orientation `pairGoal D = commutesUpTo (nP2 D) (recCall k1) (recCall k2)`.
The `(Z,X)` leaf of `rowsCommuteSym` has the X/Z roles in the OPPOSITE De Bruijn
slots, so `dispatchRouter` does not apply directly.  We therefore prove a
`∀ kA, ∀ kB`-quantified bounded fact over BOTH stabilizer indices,

  `∀ kA < numStab, ∀ kB < numStab,
     isX kA = true → isX kB = false → commutesUpTo N (recCall kA) (recCall kB)`,

at arity 0 (the two binders re-introduce `kA = var 1`, `kB = var 0` at arity 2,
where `dispatchRouter` applies verbatim).  In the `(Z,X)` leaf we instantiate it at
the SWAPPED witnesses `kA := k2`, `kB := k1`, obtaining
`commutesUpTo N (recCall k2) (recCall k1)` — exactly the post-`commutesSymm` goal —
for free, with no row-swapped re-derivation of the dispatcher. -/

/-- The body of `DDF`, at arity 2 (after the two stabilizer binders, `kA = k1 = var 1`,
`kB = k2 = var 0`): the X→Z implication chain guarding the canonical pair goal. -/
abbrev diffTypeBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (k1IsX D true) (.imp (k2IsX D false) (pairGoal D))

/-- The ∀∀-quantified DIFFERENT-type dispatch formula (arity 0).  The two bounds
match `rowsCommuteOddF`/`codeRowsCommuteUpTo` EXACTLY (`numStab` then its weakening),
so an `allNatLtElim` lines up with the `boundNatLt` hypotheses the bounded binders
expose in `rowsCommuteSym`. -/
abbrev DDF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.closed (Term.natLit (numStab D.distance)))
    (.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
      (diffTypeBody D))

/-- **The ∀∀-quantified DIFFERENT-type dispatch.**  Built by two UNBOUNDED
`PureFamilyDerivA.allNatLtIntro`s (the dispatcher does not consume the `k < numStab`
side conditions) down to arity 2, where the canonical `dispatchRouter` discharges the
guarded `pairGoal` from the split combined bundle. -/
def dispatchDiffType (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (DDF D) :=
  PureFamilyDerivA.allNatLtIntro _
    (PureFamilyDerivA.allNatLtIntro _
      (PureFamilyDerivA.cut1
        (by
          -- Context: [.and (pairBundleF D) (megaPacksF D)].  Goal: diffTypeBody D.
          refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
          -- Context now:
          --   [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
          have hbundleD : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (pairBundleF D) :=
            SFormula.Deriv.andElimLeft (.hyp (by right; right; exact List.mem_cons_self))
          have hmegaD : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (megaPacksF D) :=
            SFormula.Deriv.andElimRight (.hyp (by right; right; exact List.mem_cons_self))
          have hk1X : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (k1IsX D true) :=
            .hyp (by right; exact List.mem_cons_self)
          have hk2notX : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (k2IsX D false) :=
            .assumption
          exact dispatchRouter D hbundleD hmegaD hk1X hk2notX)
        (pfdaAnd2 (pairBundle D) (megaPacks D))))

#print axioms dispatchDiffType

/-! ## The ∀∀-quantified SAME-type dispatches (`sameTypeXFamily` / `sameTypeZFamily`)

The same-type closers `pairCommuteSameTypeX` / `pairCommuteSameTypeZ` also need the
pair bundle.  To assemble the entire pair goal from a SINGLE arity-0 cut (so the
`(Z,X)` leaf can elim `DDF` at swapped indices in the SAME bounded-binder context as
the other leaves), we quantify the two same-type closers identically to `DDF`. -/

/-- The body of `sameTypeXFamily` (both rows X-type ⇒ commute). -/
abbrev sameTypeXBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (k1IsX D true) (.imp (k2IsX D true) (pairGoal D))

/-- The body of `sameTypeZFamily` (both rows Z-type ⇒ commute). -/
abbrev sameTypeZBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (k1IsX D false) (.imp (k2IsX D false) (pairGoal D))

/-- ∀∀-quantified SAME-type-X dispatch (arity 0), bounds matching `rowsCommuteOddF`. -/
abbrev SDFX (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.closed (Term.natLit (numStab D.distance)))
    (.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
      (sameTypeXBody D))

/-- ∀∀-quantified SAME-type-Z dispatch (arity 0), bounds matching `rowsCommuteOddF`. -/
abbrev SDFZ (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.closed (Term.natLit (numStab D.distance)))
    (.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
      (sameTypeZBody D))

/-- The combined four-fact bundle used as the single arity-0 cut for `rowsCommuteSym`. -/
abbrev allDispatchF (D : OddSurfaceDistance) : SFormula 0 :=
  .and (DDF D) (.and (SDFX D) (SDFZ D))

/-- Extract the four pair packs of `pairBundleF` from a derivation of it. -/
private def bundlePieces (D : OddSurfaceDistance)
    (Γ : List (SFormula 2)) (hb : SFormula.Deriv Γ (pairBundleF D)) :
    SFormula.Deriv Γ (entryAQuant D) × SFormula.Deriv Γ (entryBQuant D) ×
      SFormula.Deriv Γ (typeExclF D k1P) × SFormula.Deriv Γ (typeExclF D k2P) :=
  ⟨SFormula.Deriv.andElimLeft hb,
   SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hb),
   SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hb)),
   SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hb))⟩

/-- The ∀∀-quantified SAME-type-X dispatch. -/
def sameTypeXFamily (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (SDFX D) :=
  PureFamilyDerivA.allNatLtIntro _
    (PureFamilyDerivA.allNatLtIntro _
      (PureFamilyDerivA.cut1
        (by
          refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
          set Γ : List (SFormula 2) :=
            [k2IsX D true, k1IsX D true, pairBundleF D] with hΓ
          have hbundleD : SFormula.Deriv Γ (pairBundleF D) :=
            .hyp (by right; right; exact List.mem_cons_self)
          obtain ⟨hEntryA, hEntryB, hExcl1, hExcl2⟩ := bundlePieces D Γ hbundleD
          have hk1X : SFormula.Deriv Γ (k1IsX D true) :=
            .hyp (by right; exact List.mem_cons_self)
          have hk2X : SFormula.Deriv Γ (k2IsX D true) := .assumption
          exact pairCommuteSameTypeX D hEntryA hEntryB hk1X hk2X hExcl1 hExcl2)
        (pairBundle D)))

/-- The ∀∀-quantified SAME-type-Z dispatch. -/
def sameTypeZFamily (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (SDFZ D) :=
  PureFamilyDerivA.allNatLtIntro _
    (PureFamilyDerivA.allNatLtIntro _
      (PureFamilyDerivA.cut1
        (by
          refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
          set Γ : List (SFormula 2) :=
            [k2IsX D false, k1IsX D false, pairBundleF D] with hΓ
          have hbundleD : SFormula.Deriv Γ (pairBundleF D) :=
            .hyp (by right; right; exact List.mem_cons_self)
          obtain ⟨hEntryA, hEntryB, hExcl1, hExcl2⟩ := bundlePieces D Γ hbundleD
          have hk1X : SFormula.Deriv Γ (k1IsX D false) :=
            .hyp (by right; exact List.mem_cons_self)
          have hk2X : SFormula.Deriv Γ (k2IsX D false) := .assumption
          exact pairCommuteSameTypeZ D hEntryA hEntryB hk1X hk2X hExcl1 hExcl2)
        (pairBundle D)))

/-- Arity-generic conjunction introduction for `PureFamilyDerivA`. -/
def pfdaAndG {D : OddSurfaceDistance} {arity : Nat} {A B : SFormula arity}
    (hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A)
    (hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (.and A B) :=
  PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption
    (.hyp (by right; exact List.mem_cons_self))) hA hB

/-- The combined four-fact dispatch family. -/
def allDispatch (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (allDispatchF D) :=
  pfdaAndG (dispatchDiffType D) (pfdaAndG (sameTypeXFamily D) (sameTypeZFamily D))

#print axioms allDispatch

/-! ## Instantiating the ∀∀ families at the pair indices

Each family `F = allNatLt numStab (allNatLt numStab.weaken B)` (with `B` an arity-2
body referencing `k1 = var 1`, `k2 = var 0`), once weakened into the per-pair
context, is eliminated at two pure witnesses.  Eliminating at `(k1, k2)` returns `B`
verbatim (identity substitution on the matching De Bruijn slots); eliminating at the
SWAPPED `(k2, k1)` returns `B` with `k1`/`k2` exchanged.  The reductions below are
purely the capture-avoiding lift/instantiate book-keeping (Fin-index arithmetic), so
they go through by structural `simp` on the closed numeral bound and the concrete
body — no `arithBool`-fragment reasoning, no `decide` on Pauli content. -/

/-- The closed outer bound `numStab` (arity 2) shared by every `∀∀` family. -/
abbrev famN0 (D : OddSurfaceDistance) : STerm 2 .nat :=
  SC.closed (Term.lift 0 (Term.lift 0 (Term.natLit (numStab D.distance))))

/-- The DIFFERENT-type family, weakened into a per-pair context, instantiated at the
SWAPPED indices `(k2, k1)` — yielding the row-swapped pair goal `commutesUpTo (nP2 D)
(rowB D) (rowA D)` guarded by `k2 X-type → k1 Z-type`.  This is the `(Z,X)` workhorse.
The full structural `simp` set reduces only the lift/instantiate book-keeping. -/
def instDDFswap {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (diffTypeBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ
      (.imp (k2IsX D true) (.imp (k1IsX D false)
        (SFormula.commutesUpTo (nP2 D) (rowB D) (rowA D)))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hF hk2Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hStep1b hk1Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep2
  simpa [diffTypeBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- The DIFFERENT-type family, instantiated at the NATURAL order `(k1, k2)` (identity
substitution), yielding `k1 X-type → k2 Z-type → pairGoal D`.  The `(X,Z)` workhorse. -/
def instDDFid {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (diffTypeBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ (.imp (k1IsX D true) (.imp (k2IsX D false) (pairGoal D))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hF hk1Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hStep1b hk2Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep2
  simpa [diffTypeBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- The SAME-type-X family, instantiated at `(k1, k2)`: `k1 X-type → k2 X-type →
pairGoal D`. -/
def instSDFXid {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (sameTypeXBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ (.imp (k1IsX D true) (.imp (k2IsX D true) (pairGoal D))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hF hk1Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hStep1b hk2Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep2
  simpa [sameTypeXBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- The SAME-type-Z family, instantiated at `(k1, k2)`: `k1 Z-type → k2 Z-type →
pairGoal D`. -/
def instSDFZid {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (sameTypeZBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ (.imp (k1IsX D false) (.imp (k2IsX D false) (pairGoal D))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hF hk1Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hStep1b hk2Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep2
  simpa [sameTypeZBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- **Pairwise row commutation, all `D`.**

FULLY sorry-free and axiom-clean.  A single arity-0 cut introduces the four
∀∀-quantified dispatch families (`allDispatch` = `dispatchDiffType` ∧
`sameTypeXFamily` ∧ `sameTypeZFamily`); the two stabilizer binders are introduced with
their `k < numStab` side conditions exposed (`allNatLtIntroBounded`); both rows are
classified by CSS type (`isXTypeTA`, a `k`-only function); and each of the four combos
is closed by instantiating the matching family at the per-leaf indices:
* `(X,X)` / `(Z,Z)`: the SAME-type closers (`instSDFXid` / `instSDFZid`, internalising
  `pairCommuteSameTypeX` / `pairCommuteSameTypeZ`) at the natural order `(k1, k2)`;
* `(X,Z)`: the DIFFERENT-type dispatcher (`instDDFid`, internalising `dispatchRouter`)
  at `(k1, k2)`;
* `(Z,X)`: the SAME DIFFERENT-type family instantiated at the SWAPPED indices
  `(k2, k1)` (`instDDFswap`), composed with `commutesSymm` to recover the canonical
  orientation — so the `(Z,X)` leaf reuses the `(X,Z)` dispatcher verbatim, with the
  X/Z roles exchanged purely by the ∀∀ instantiation (no row-swapped re-derivation). -/
def rowsCommuteSym (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (rowsCommuteOddF D)) :=
  PureFamilyDerivA.cut1
    (by
      -- Context: [allDispatchF D] (a single arity-0 cut of the four ∀∀ dispatch
      -- families).  Goal: closedSF (rowsCommuteOddF D), i.e. after unfolding,
      -- `allNatLt numStab (allNatLt numStab.weaken (pairGoal D))`.
      unfold closedSF rowsCommuteOddF rowsCommuteF Formula.codeRowsCommuteUpTo
      simp only [closedSF, Formula.codeRow, Term.weaken]
      -- Introduce both stabilizer binders with their `k < numStab` side conditions
      -- exposed (needed to ELIM the ∀∀ dispatch families at `k1`/`k2`).
      refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
      refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
      -- The arity-2 context (innermost first):
      --   [ boundNatLt N₁ , (boundNatLt N₀).weaken , (allDispatchF D).weaken.weaken ]
      -- with N₀ = numStab, N₁ = numStab.weaken.  `hk1Lt`/`hk2Lt` are the two
      -- exposed side conditions; `hAll` is the cut.
      have hAll : SFormula.Deriv
          [SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance)))),
            (SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken,
            (allDispatchF D).weaken.weaken]
          ((allDispatchF D).weaken.weaken) :=
        .hyp (by right; right; exact List.mem_cons_self)
      have hDDF := SFormula.Deriv.andElimLeft hAll
      have hSDFX := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hAll)
      have hSDFZ := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hAll)
      have hk2Lt : SFormula.Deriv
          [SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance)))),
            (SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken,
            (allDispatchF D).weaken.weaken]
          (SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))) :=
        .assumption
      have hk1Lt : SFormula.Deriv
          [SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance)))),
            (SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken,
            (allDispatchF D).weaken.weaken]
          ((SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken) :=
        .hyp (by right; exact List.mem_cons_self)
      -- Classify both rows by CSS type, routing each combo through the matching
      -- ∀∀-dispatch family instantiated at the appropriate (possibly swapped) indices.
      refine SFormula.Deriv.boolCases (SC.closed (isXTypeTA (dP2 D) k1P)) _ ?k1T ?k1F
      case k1T =>
        refine SFormula.Deriv.boolCases (SC.closed (isXTypeTA (dP2 D) k2P)) _ ?k1Tk2T ?k1Tk2F
        case k1Tk2T =>
          -- (X, X): SAME-type-X family at (k1, k2).
          exact ((instSDFXid D (cw2 hSDFX) (cw2 hk1Lt) (cw2 hk2Lt)).mp
            (.hyp (by right; exact List.mem_cons_self))).mp .assumption
        case k1Tk2F =>
          -- (X, Z): DIFFERENT-type family at (k1, k2).
          exact ((instDDFid D (cw2 hDDF) (cw2 hk1Lt) (cw2 hk2Lt)).mp
            (.hyp (by right; exact List.mem_cons_self))).mp .assumption
      case k1F =>
        refine SFormula.Deriv.boolCases (SC.closed (isXTypeTA (dP2 D) k2P)) _ ?k1Fk2T ?k1Fk2F
        case k1Fk2T =>
          -- (Z, X): DIFFERENT-type family at the SWAPPED indices (k2, k1), then
          -- `commutesSymm` to recover the canonical orientation.
          refine SFormula.Deriv.commutesSymm (nP2 D) (rowB D) (rowA D) ?_
          exact ((instDDFswap D (cw2 hDDF) (cw2 hk1Lt) (cw2 hk2Lt)).mp .assumption).mp
            (.hyp (by right; exact List.mem_cons_self))
        case k1Fk2F =>
          -- (Z, Z): SAME-type-Z family at (k1, k2).
          exact ((instSDFZid D (cw2 hSDFZ) (cw2 hk1Lt) (cw2 hk2Lt)).mp
            (.hyp (by right; exact List.mem_cons_self))).mp .assumption)
    (allDispatch D)

-- The bulk–bulk class-combo dispatcher (validation spike): routing + kind-bridge +
-- validity/non-adjacency derivations, sorry-free and axiom-clean.
#print axioms dispatchBulkBulk
#print axioms dbbKindK1OfIsX
#print axioms dbbBhRowImp
#print axioms dbbBvRowImp
#print axioms dbbBhlColImp
#print axioms dbbNonAdjAll
#print axioms dbbNonAdjVu
#print axioms dbbPacks

-- Axiom hygiene of the proven (sorry-free) infrastructure spine and the two
-- SAME-type closers.  `rowsCommuteSym` is now FULLY sorry-free and axiom-clean: all
-- four CSS-type combos are dispatched through the ∀∀-quantified `dispatchDiffType` /
-- `sameTypeXFamily` / `sameTypeZFamily` families (cut once at arity 0, instantiated
-- per leaf):
--   * `(X,Z)`: `instDDFid` (canonical orientation, dispatchRouter verbatim);
--   * `(Z,X)`: `instDDFswap` (DIFFERENT-type family at the SWAPPED indices `(k2,k1)`)
--      composed with the `commutesSymm` step — no row-swapped re-derivation needed;
--   * `(X,X)` / `(Z,Z)`: the two SAME-type closers via `instSDFXid` / `instSDFZid`.
-- The reusable two-anti spine they plug into (`commTwoAntiXZ` / `twoAntiRestXZ`)
-- and the entire pointwise / leaf / type-exclusion infrastructure are sorry-free
-- and axiom-clean (verified below).
#print axioms localDispatch
#print axioms pairCommutePointwise
#print axioms withLeafG
#print axioms typeExclPackK1
#print axioms typeExclPackK2
#print axioms pairCommuteSameTypeX
#print axioms pairCommuteSameTypeZ
-- The new reusable DIFFERENT-type (X-vs-Z) two-anti spines (sorry-free, axiom-clean).
#print axioms entryAAtQ
#print axioms entryBAtQ
#print axioms commTwoAntiXZ
#print axioms twoAntiRestXZ
-- The bulk–top overlap-class closer (sorry-free, axiom-clean).
#print axioms commBulkTopXZ
-- The bulk–top joint pin pack and the full bulk–top class closer (sorry-free, axiom-clean).
#print axioms btPinPack
#print axioms btPinAt
#print axioms btTopBandFromX
#print axioms btBulkBandFromZ
#print axioms commBulkTop
-- The bulk–bottom overlap-class closer + its arithmetic packs (sorry-free, axiom-clean).
#print axioms bbRangePack
#print axioms bbBottomBandPack
#print axioms bbBulkBandPack
#print axioms bbPinPack
#print axioms bbPinAt
#print axioms bbBottomBandFromX
#print axioms bbBulkBandFromZ
#print axioms commBottomBulk
-- The bulk–right overlap-class closer + its arithmetic packs (sorry-free, axiom-clean).
#print axioms brRangePack
#print axioms brRightBandPack
#print axioms brBulkBandPack
#print axioms brPinPack
#print axioms brPinAt
#print axioms brBulkBandFromX
#print axioms brRightBandFromZ
#print axioms commRightBulk
-- The bulk–left overlap-class closer + its arithmetic packs (sorry-free, axiom-clean).
#print axioms blRangePack
#print axioms blLeftBandPack
#print axioms blBulkBandPack
#print axioms blPinPack
#print axioms blPinAt
#print axioms blBulkBandFromX
#print axioms blLeftBandFromZ
#print axioms commLeftBulk
#print axioms rowsCommuteSym

end QHL.CodeLang.Surface.Verify
