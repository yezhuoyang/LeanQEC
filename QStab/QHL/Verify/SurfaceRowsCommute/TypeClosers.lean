import QStab.QHL.Verify.SurfaceRowsCommute.Assembly

/-!
# Rows-commute (pairwise generated-row commutation) — TypeClosers

Same-type pair commutation (both X-type or both Z-type) and the generic two-anti closer for
the different-type (X-vs-Z) overlapping case.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ### Same-type pair commutation (both X-type, or both Z-type)

A same-type pair never overlaps, so both `localDispatch` anti-handlers are vacuous.
We discharge them by RE-RESOLVING the offending row's leaf with guards exposed
(`withLeafG`) and contradicting:
* an `I`/`X` re-resolution against the `Z` leaf value (`leafNotPandZ`);
* a `Z` re-resolution (bulk-`Z`/right-`Z`/left-`Z` class guards) against the row's
  X-type fact via the `typeExcl` arithmetic pack. -/

/-- Both rows X-type ⟹ pair commutes. -/
def pairCommuteSameTypeX {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hk2X : SFormula.Deriv Γ (k2IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hExcl2 : SFormula.Deriv Γ (typeExclF D k2P)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryAF hEntryBF ?_ ?_
  · -- (X, Z): A leaf = X, B leaf = Z.  B is X-type → re-resolve B, contradict.
    intro Δ' lift hLeafA hLeafB
    -- type fact + exclusion pack for k2 in Δ'.
    have hk2Xd : SFormula.Deriv Δ' (k2IsX D true).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k2IsX D true) hk2X))
    have hExcl2d : SFormula.Deriv Δ' (typeExclF D k2P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k2P) hExcl2))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl2d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl2d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d))
    refine withLeafG D k2P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- I vs Z
      intro Δ'' lift2 hI
      exact leafNotPandZ D k2P3 Pauli.I rfl hI (lift2 hLeafB)
    · -- bulkZ: bulk=true, kind=true; exclusion gives kind=false.
      intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk2Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · -- bulkX vs Z
      intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k2P3 Pauli.X rfl hX (lift2 hLeafB)
    · -- topX vs Z
      intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k2P3 Pauli.X rfl hX (lift2 hLeafB)
    · -- rightZ: bulk=false, top=false, right=true; exclusion gives right=false.
      intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk2Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · -- leftZ: exclusion gives left=false.
      intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk2Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · -- bottomX vs Z
      intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k2P3 Pauli.X rfl hX (lift2 hLeafB)
  · -- (Z, X): A leaf = Z, B leaf = X.  A is X-type → re-resolve A, contradict.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D true).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k1IsX D true) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl1d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandZ D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk1Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)

/-- Both rows Z-type ⟹ pair commutes.  Dual of `pairCommuteSameTypeX`: a Z-type row
never produces an `X` leaf, so the offending `X` leaf is re-resolved and contradicted
via the `ztNotBulkXF`/`ztNotTopXF`/`ztNotBottomXF` arithmetic exclusions, while the
`Z` re-resolutions contradict the `X` leaf value. -/
def pairCommuteSameTypeZ {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D false))
    (hk2X : SFormula.Deriv Γ (k2IsX D false))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hExcl2 : SFormula.Deriv Γ (typeExclF D k2P)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryAF hEntryBF ?_ ?_
  · -- (X, Z): A leaf = X, B leaf = Z.  A is Z-type → re-resolve A, contradict.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D false).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k1IsX D false) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hznbx := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d)))
    have hzntx := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))))
    have hznbtx := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- I vs X
      intro Δ'' lift2 hI
      exact leafNotPandX D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · -- bulkZ vs X
      intro Δ'' lift2 hZ _ _
      exact leafNotPandX D k1P3 Pauli.Z rfl hZ (lift2 hLeafA)
    · -- bulkX: bulk=true, kind=false; exclusion gives kind=true.
      intro Δ'' lift2 _ hbulk hkind
      have hkindT := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hznbx) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkindT hkind
    · -- topX: bulk=false, top=true; exclusion gives top=false.
      intro Δ'' lift2 _ hbulk htop
      have htopF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hzntx) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ htop htopF
    · -- rightZ vs X
      intro Δ'' lift2 hZ _ _ _
      exact leafNotPandX D k1P3 Pauli.Z rfl hZ (lift2 hLeafA)
    · -- leftZ vs X
      intro Δ'' lift2 hZ _ _ _ _
      exact leafNotPandX D k1P3 Pauli.Z rfl hZ (lift2 hLeafA)
    · -- bottomX: bulk=false, top=false, right=false, left=false; exclusion gives left=true.
      intro Δ'' lift2 _ hbulk htop _ hleft
      have hleftT := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hznbtx) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hleftT hleft
  · -- (Z, X): A leaf = Z, B leaf = X.  B is Z-type → re-resolve B, contradict.
    intro Δ' lift hLeafA hLeafB
    have hk2Xd : SFormula.Deriv Δ' (k2IsX D false).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k2IsX D false) hk2X))
    have hExcl2d : SFormula.Deriv Δ' (typeExclF D k2P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k2P) hExcl2))
    have hznbx := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d)))
    have hzntx := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d))))
    have hznbtx := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d))))
    refine withLeafG D k2P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandX D k2P3 Pauli.I rfl hI (lift2 hLeafB)
    · intro Δ'' lift2 hZ _ _
      exact leafNotPandX D k2P3 Pauli.Z rfl hZ (lift2 hLeafB)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindT := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hznbx) (lift2 hk2Xd)) hbulk
      exact eqBoolContra _ hkindT hkind
    · intro Δ'' lift2 _ hbulk htop
      have htopF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hzntx) (lift2 hk2Xd)) hbulk
      exact eqBoolContra _ htop htopF
    · intro Δ'' lift2 hZ _ _ _
      exact leafNotPandX D k2P3 Pauli.Z rfl hZ (lift2 hLeafB)
    · intro Δ'' lift2 hZ _ _ _ _
      exact leafNotPandX D k2P3 Pauli.Z rfl hZ (lift2 hLeafB)
    · intro Δ'' lift2 _ hbulk htop _ hleft
      have hleftT := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hznbtx) (lift2 hk2Xd)) hbulk) htop
      exact eqBoolContra _ hleftT hleft

/-- Conjoin two arity-2 family-derivations. -/
def pfdaAnd2 {D : OddSurfaceDistance} {A B : SFormula 2}
    (hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A)
    (hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (.and A B) :=
  PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption
    (.hyp (by right; exact List.mem_cons_self))) hA hB

/-! ## Generic two-anti closer for the DIFFERENT-type (X-vs-Z) overlapping case

The reusable spine for an overlapping `(X-type, Z-type)` pair, the two-generated-row
analogue of `commTwoAntiA`/`commTwoAntiB` in `SurfaceNormalizers.lean` (there one
operand was a fixed `logicalX`; here both are generated rows resolved via
`rowEntryFlatSym`).  Given:
* the two anti qubits `q0`, `q1` (closed arithmetic terms) with purity witnesses;
* that they are `< nQubits`, distinct;
* that row A resolves to `X` and row B to `Z` at both `q0` and `q1` (the verified
  overlap geometry — `#eval`-confirmed, d = 3,5,7);
* an all-others handler closing local commutation at every qubit `q ∉ {q0, q1}`
  (where the only obstruction is the `(X,Z)` leaf-pair, dispatched via `localDispatch`),

the rows commute by the even-parity rule `commutesOfTwoAnti`.  Each overlap
class-pair supplies `q0`/`q1` and the band-fires / joint-pin packs and plugs in. -/

/-- Row-A entry at a concrete pure qubit term `qT` (arity 2): the flat classifier. -/
def entryAAtQ (D : OddSurfaceDistance) (qT : Term 2 .nat) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dP2 D) k1P)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dP2 D) k1P qT))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distP2 D) k1P qT
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hq

/-- Row-B entry at a concrete pure qubit term `qT` (arity 2): the flat classifier. -/
def entryBAtQ (D : OddSurfaceDistance) (qT : Term 2 .nat) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dP2 D) k2P)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dP2 D) k2P qT))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distP2 D) k2P qT
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hq

/-- The `commutesOfTwoAnti` all-others premise, as a goal abbreviation: local
commutation at `boundNat` for every `q < nQubits` away from `q0`, `q1`. -/
abbrev twoAntiRest (D : OddSurfaceDistance) (q0 q1 : Term 2 .nat) : SFormula 2 :=
  .allNatLt (nP2 D)
    (.imp (.not (.eqNat SFormula.boundNat (SC.closed q0).weaken))
      (.imp (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken))
        (SFormula.localCommutesAt (rowA D).weaken (rowB D).weaken SFormula.boundNat)))

/-- **Generic X-vs-Z two-anti closer.**  Mirrors `commTwoAntiA`: assemble
`commutesOfTwoAnti` from the in-range / distinctness witnesses, the `X`/`Z`
resolutions at `q0`/`q1` (so they anticommute there), and the all-others premise. -/
def commTwoAntiXZ {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (q0 q1 : Term 2 .nat)
    (hLt0 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q0) (nP2 D)))
    (hLt1 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q1) (nP2 D)))
    (hNe : SFormula.Deriv Γ (.eqBool (SC.closed (.eqNat q0 q1)) (SC.b false)))
    (hAX0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowA D) (SC.closed q0)) (SC.p Pauli.X)))
    (hAX1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowA D) (SC.closed q1)) (SC.p Pauli.X)))
    (hBZ0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowB D) (SC.closed q0)) (SC.p Pauli.Z)))
    (hBZ1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowB D) (SC.closed q1)) (SC.p Pauli.Z)))
    (hRest : SFormula.Deriv Γ (twoAntiRest D q0 q1)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine SFormula.Deriv.commutesOfTwoAnti (nP2 D) (rowA D) (rowB D)
    (SC.closed q0) (SC.closed q1) hLt0 hLt1 ?wne ?wanti0 ?wanti1 hRest
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) q0 q1 .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    -- A = X, B = Z at q0 ⟹ anticommute (true).
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hAX0 hBZ0 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hAX1 hBZ1 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)

/-- **All-others discharger for the X-vs-Z overlapping case.**  Discharges the
`commutesOfTwoAnti` all-others premise `twoAntiRest D q0 q1`.

Row A is X-type (`hk1X`), row B is Z-type (`hk2X`).  After introducing the qubit
binder and the two `≠ q0`/`≠ q1` exclusions, `localDispatch` reduces the obstruction
to the two genuinely-anticommuting leaf-pairs:
* `(Z, X)` (A leaf `Z`) — impossible: A is X-type, contradicted via the type-
  exclusion pack (exactly as in `pairCommuteSameTypeX`'s `(Z,X)` branch);
* `(X, Z)` (A leaf `X`, B leaf `Z`) — the genuine overlap, delegated to `hXZpin`,
  which (per overlap class) re-resolves the two leaves' band guards and pins
  `boundNat ∈ {q0, q1}`, contradicting the two `≠` exclusions.

The `hXZpin` handler receives the deepened qubit-binder context (with both `≠`
exclusions and `boundNat < nQubits` available as the first hyps), plus the `X`/`Z`
leaf facts; it must close `lcGoalP D` (typically `botElim` after the pin). -/
def twoAntiRestXZ {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (q0 q1 : Term 2 .nat)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hXZpin : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv
        (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
          :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
          :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A →
        SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D)) :
    SFormula.Deriv Γ (twoAntiRest D q0 q1) := by
  unfold twoAntiRest
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
  -- context Δ0 := [¬q=q1, ¬q=q0, boundNatLt (nP2 D), Γ.map weaken]
  set Δ0 : List (SFormula 3) :=
    .not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
      :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
      :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ with hΔ0
  -- the local-commutation goal is exactly `lcGoalP D`.
  have hgoalEq : SFormula.localCommutesAt (rowA D).weaken (rowB D).weaken SFormula.boundNat
      = lcGoalP D := rfl
  rw [hgoalEq]
  -- qubit-in-range, entries at the qubit binder.
  have hq : SFormula.Deriv Δ0 (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    SFormula.Deriv.hyp (by rw [hΔ0]; right; right; exact List.mem_cons_self)
  have hEntryAW : SFormula.Deriv Δ0 (entryAQuant D).weaken :=
    cw3 (SFormula.Deriv.weakenFresh (A := entryAQuant D) hEntryAF)
  have hEntryBW : SFormula.Deriv Δ0 (entryBQuant D).weaken :=
    cw3 (SFormula.Deriv.weakenFresh (A := entryBQuant D) hEntryBF)
  have hEntryA := entryAAtBound D hEntryAW hq
  have hEntryB := entryBAtBound D hEntryBW hq
  refine localDispatch D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): the genuine overlap → delegate to the pin handler.
    intro Δ' lift hLeafA hLeafB
    exact hXZpin Δ' (fun h => lift h) hLeafA hLeafB
  · -- (Z, X): A leaf = Z impossible since A is X-type → type-exclusion contradiction.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D true).weaken :=
      lift (cw3 (SFormula.Deriv.weakenFresh (A := k1IsX D true) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw3 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl1d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandZ D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk1Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)

end QHL.CodeLang.Surface.Verify
