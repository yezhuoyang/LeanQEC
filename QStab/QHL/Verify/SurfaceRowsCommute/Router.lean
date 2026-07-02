import QStab.QHL.Verify.SurfaceRowsCommute.Dispatchers

/-!
# Rows-commute (pairwise generated-row commutation) — Router

The mega-pack bundle and the top-level (X,Z) router.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Mega-pack bundle and top-level (X,Z) router

`megaPacksF` is the `.and`-conjunction of all nine per-combo `PacksF` super-bundles,
in the fixed RIGHT-NESTED association (combo order: bulk–bulk, bulk–right, bulk–left,
top–bulk, bottom–bulk, top–right, top–left, bottom–right, bottom–left):

  dbbPacksF ∧ (dbrPacksF ∧ (dblPacksF ∧ (dtbPacksF ∧ (dbtbPacksF ∧
    (dtrPacksF ∧ (dtlPacksF ∧ (dbtrPacksF ∧ dbtlPacksF)))))))

`megaPacks` is the matching right-nested `pfdaAnd2` chain of the nine `Packs`. -/
abbrev megaPacksF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (dbbPacksF D) (.and (dbrPacksF D) (.and (dblPacksF D) (.and (dtbPacksF D)
    (.and (dbtbPacksF D) (.and (dtrPacksF D) (.and (dtlPacksF D)
      (.and (dbtrPacksF D) (dbtlPacksF D))))))))

def megaPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (megaPacksF D) :=
  pfdaAnd2 (dbbPacks D) (pfdaAnd2 (dbrPacks D) (pfdaAnd2 (dblPacks D) (pfdaAnd2 (dtbPacks D)
    (pfdaAnd2 (dbtbPacks D) (pfdaAnd2 (dtrPacks D) (pfdaAnd2 (dtlPacks D)
      (pfdaAnd2 (dbtrPacks D) (dbtlPacks D))))))))

#print axioms megaPacks

/-- **Top-level (X,Z) class-combo router.**

`k1` is X-type (`hkAX`), `k2` is Z-type (`hkBZ`).  A `boolCases` TREE on the bulk /
top / right / left class guards of both rows establishes each of the nine concrete
class contexts and dispatches to the matching combo dispatcher, extracting the
combo's `PacksF` super-bundle from `hmega` (the right-nested mega-bundle) by
`andElim`.  The impossible boundary classes (`k2` = bottom under Z-type;
`k1` = right/left under X-type) are ruled out via the `typeExclF` exclusion
implications already carried in `pairBundleF` (`ztNotTopXF`/`ztNotBottomXF` for the
Z-type `k2`, `xtNotRightZF`/`xtNotLeftZF` for the X-type `k1`). -/
def dispatchRouter {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hmega : SFormula.Deriv Γ (megaPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false)) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Extract the type-exclusion packs (the isX bridges) from `hbundle`.
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  have hExcl2 : SFormula.Deriv Γ (typeExclF D k2P) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  -- Extract each combo's PacksF from the right-nested `hmega`.
  have hMdbb : SFormula.Deriv Γ (dbbPacksF D) := SFormula.Deriv.andElimLeft hmega
  have hMr1 := SFormula.Deriv.andElimRight hmega
  have hMdbr : SFormula.Deriv Γ (dbrPacksF D) := SFormula.Deriv.andElimLeft hMr1
  have hMr2 := SFormula.Deriv.andElimRight hMr1
  have hMdbl : SFormula.Deriv Γ (dblPacksF D) := SFormula.Deriv.andElimLeft hMr2
  have hMr3 := SFormula.Deriv.andElimRight hMr2
  have hMdtb : SFormula.Deriv Γ (dtbPacksF D) := SFormula.Deriv.andElimLeft hMr3
  have hMr4 := SFormula.Deriv.andElimRight hMr3
  have hMdbtb : SFormula.Deriv Γ (dbtbPacksF D) := SFormula.Deriv.andElimLeft hMr4
  have hMr5 := SFormula.Deriv.andElimRight hMr4
  have hMdtr : SFormula.Deriv Γ (dtrPacksF D) := SFormula.Deriv.andElimLeft hMr5
  have hMr6 := SFormula.Deriv.andElimRight hMr5
  have hMdtl : SFormula.Deriv Γ (dtlPacksF D) := SFormula.Deriv.andElimLeft hMr6
  have hMr7 := SFormula.Deriv.andElimRight hMr6
  have hMdbtr : SFormula.Deriv Γ (dbtrPacksF D) := SFormula.Deriv.andElimLeft hMr7
  have hMdbtl : SFormula.Deriv Γ (dbtlPacksF D) := SFormula.Deriv.andElimRight hMr7
  -- The isX exclusion implications for `k1` (X-type) and `k2` (Z-type).
  -- k1: xtNotRightZF / xtNotLeftZF (rule out right/left under X-type boundary).
  have hXtNotRightZ : SFormula.Deriv Γ (xtNotRightZF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1)
  have hXtNotLeftZ : SFormula.Deriv Γ (xtNotLeftZF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1))
  -- k2: ztNotTopXF / ztNotBottomXF (rule out top, and bottom-vacuity under Z-type).
  have hZtNotTopX : SFormula.Deriv Γ (ztNotTopXF D k2P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2))))
  have hZtNotBottomX : SFormula.Deriv Γ (ztNotBottomXF D k2P) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2))))
  -- ROOT: case on bulk(k1).
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP2 D) k1P)) _ ?k1bulk ?k1nbulk
  case k1bulk =>
    -- ctx0: bulk(k1)=true :: Γ
    have hbulkA : SFormula.Deriv
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) :=
      .hyp List.mem_cons_self
    refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP2 D) k2P)) _ ?k1b_k2bulk ?k1b_k2nbulk
    case k1b_k2bulk =>
      -- ctx1: bulk(k2)=true :: bulk(k1)=true :: Γ
      have hbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) :=
        .hyp List.mem_cons_self
      exact dispatchBulkBulk D (cw2 hbundle) (cw2 hMdbb) (cw2 hkAX) (cw2 hkBZ)
        (cw1 hbulkA) hbulkB
    case k1b_k2nbulk =>
      -- ctx1: bulk(k2)=false :: bulk(k1)=true :: Γ
      have hnbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) :=
        .hyp List.mem_cons_self
      -- hntopB := ztNotTopXF(k2) hkBZ hnbulkB
      have hntopB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
        SFormula.Deriv.mp (SFormula.Deriv.mp (cw2 hZtNotTopX) (cw2 hkBZ)) hnbulkB
      refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP2 D) k2P)) _ ?rT ?rF
      case rT =>
        have hrightB : SFormula.Deriv
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
          .hyp List.mem_cons_self
        exact dispatchBulkRight D (cw3 hbundle) (cw3 hMdbr) (cw3 hkAX) (cw3 hkBZ)
          (cw2 hbulkA) (cw1 hnbulkB) (cw1 hntopB) hrightB
      case rF =>
        have hnrightB : SFormula.Deriv
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
          .hyp List.mem_cons_self
        refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP2 D) k2P)) _ ?lT ?lF
        case lT =>
          have hleftB : SFormula.Deriv
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)
                :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            .hyp List.mem_cons_self
          exact dispatchBulkLeft D (cw4 hbundle) (cw4 hMdbl) (cw4 hkAX) (cw4 hkBZ)
            (cw3 hbulkA) (cw2 hnbulkB) (cw2 hntopB) (cw1 hnrightB) hleftB
        case lF =>
          -- vacuous: k2 has ¬bulk ¬top ¬right ¬left → bottom = X-type, contradicting Z-type.
          have hnleftB : SFormula.Deriv
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
            .hyp List.mem_cons_self
          have hleftBtrue : SFormula.Deriv
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw4 hZtNotBottomX) (cw4 hkBZ))
              (cw2 hnbulkB)) (cw2 hntopB)
          exact SFormula.Deriv.botElim
            (SFormula.Deriv.notElim hleftBtrue (SFormula.Deriv.eqBoolFalseNotTrue _ hnleftB))
  case k1nbulk =>
    -- ctx0: bulk(k1)=false :: Γ
    have hnbulkA : SFormula.Deriv
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) :=
      .hyp List.mem_cons_self
    refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP2 D) k2P)) _ ?k1nb_k2bulk ?k1nb_k2nbulk
    case k1nb_k2bulk =>
      -- ctx1: bulk(k2)=true :: bulk(k1)=false :: Γ
      have hbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) :=
        .hyp List.mem_cons_self
      refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dP2 D) k1P)) _ ?tbT ?tbF
      case tbT =>
        have htopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)) :=
          .hyp List.mem_cons_self
        exact dispatchTopBulk D (cw3 hbundle) (cw3 hMdtb) (cw3 hkAX) (cw3 hkBZ)
          (cw2 hnbulkA) htopA (cw1 hbulkB)
      case tbF =>
        have hntopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          .hyp List.mem_cons_self
        -- hnrightA := xtNotRightZF(k1) hkAX hnbulkA hntopA ; hnleftA := xtNotLeftZF(k1) ... hnrightA
        have hnrightA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw3 hXtNotRightZ) (cw3 hkAX))
            (cw2 hnbulkA)) hntopA
        have hnleftA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
            (cw3 hXtNotLeftZ) (cw3 hkAX)) (cw2 hnbulkA)) hntopA) hnrightA
        exact dispatchBottomBulk D (cw3 hbundle) (cw3 hMdbtb) (cw3 hkAX) (cw3 hkBZ)
          (cw2 hnbulkA) hntopA hnrightA hnleftA (cw1 hbulkB)
    case k1nb_k2nbulk =>
      -- ctx1: bulk(k2)=false :: bulk(k1)=false :: Γ
      have hnbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) :=
        .hyp List.mem_cons_self
      have hntopB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
          (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
        SFormula.Deriv.mp (SFormula.Deriv.mp (cw2 hZtNotTopX) (cw2 hkBZ)) hnbulkB
      refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dP2 D) k1P)) _ ?topT ?topF
      case topT =>
        have htopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)) :=
          .hyp List.mem_cons_self
        refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP2 D) k2P)) _ ?trT ?trF
        case trT =>
          have hrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            .hyp List.mem_cons_self
          exact dispatchTopRight D (cw4 hbundle) (cw4 hMdtr) (cw4 hkAX) (cw4 hkBZ)
            (cw3 hnbulkA) (cw1 htopA) (cw2 hnbulkB) (cw2 hntopB) hrightB
        case trF =>
          have hnrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
            .hyp List.mem_cons_self
          refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP2 D) k2P)) _ ?tlT ?tlF
          case tlT =>
            have hleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              .hyp List.mem_cons_self
            exact dispatchTopLeft D (cw5 hbundle) (cw5 hMdtl) (cw5 hkAX) (cw5 hkBZ)
              (cw4 hnbulkA) (cw2 htopA) (cw3 hnbulkB) (cw3 hntopB) (cw1 hnrightB) hleftB
          case tlF =>
            have hnleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
              .hyp List.mem_cons_self
            have hleftBtrue : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw5 hZtNotBottomX) (cw5 hkBZ))
                (cw3 hnbulkB)) (cw3 hntopB)
            exact SFormula.Deriv.botElim
              (SFormula.Deriv.notElim hleftBtrue (SFormula.Deriv.eqBoolFalseNotTrue _ hnleftB))
      case topF =>
        have hntopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          .hyp List.mem_cons_self
        have hnrightA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw3 hXtNotRightZ) (cw3 hkAX))
            (cw2 hnbulkA)) hntopA
        have hnleftA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
            (cw3 hXtNotLeftZ) (cw3 hkAX)) (cw2 hnbulkA)) hntopA) hnrightA
        refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP2 D) k2P)) _ ?brT ?brF
        case brT =>
          have hrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            .hyp List.mem_cons_self
          exact dispatchBottomRight D (cw4 hbundle) (cw4 hMdbtr) (cw4 hkAX) (cw4 hkBZ)
            (cw3 hnbulkA) (cw1 hntopA) (cw1 hnrightA) (cw1 hnleftA) (cw2 hnbulkB) (cw2 hntopB) hrightB
        case brF =>
          have hnrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
            .hyp List.mem_cons_self
          refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP2 D) k2P)) _ ?blT ?blF
          case blT =>
            have hleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              .hyp List.mem_cons_self
            exact dispatchBottomLeft D (cw5 hbundle) (cw5 hMdbtl) (cw5 hkAX) (cw5 hkBZ)
              (cw4 hnbulkA) (cw2 hntopA) (cw2 hnrightA) (cw2 hnleftA) (cw3 hnbulkB) (cw3 hntopB)
              (cw1 hnrightB) hleftB
          case blF =>
            have hnleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
              .hyp List.mem_cons_self
            have hleftBtrue : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw5 hZtNotBottomX) (cw5 hkBZ))
                (cw3 hnbulkB)) (cw3 hntopB)
            exact SFormula.Deriv.botElim
              (SFormula.Deriv.notElim hleftBtrue (SFormula.Deriv.eqBoolFalseNotTrue _ hnleftB))

#print axioms dispatchRouter

end QHL.CodeLang.Surface.Verify
