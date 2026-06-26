import QStab.QClifford.PCC.SurfaceD3ShorBase

/-!
# Surface-d3 Shor PCC: global detection completeness (heavy leaf)

This module contains `globalHookSafePred_true` (the checked finite fact that
every global site is `detected ∨ DeltaSafe`) and `surfaceNoUndetectedHook_global`
(the honest `NoUndetectedHook` for the whole Shor surface circuit).

It is a **leaf module** in the import DAG: `SurfaceD3Shor` imports this, so
editing `SurfaceD3Shor` does NOT rebuild the heavy `decide`s here.  Each chunk
is kept under 6M heartbeats to stay well within the 8-minute per-job limit.
-/

namespace QStab.QClifford.PCC.SurfaceD3Shor

/-- The list of *global* error-location sites of the whole Shor surface circuit.
Each `site.suffix` is the deterministic remainder of the **entire** circuit after
that location, so policy detection observes the full run, not one gadget. -/
def globalSites : List (ErrLocWithContext Nq) :=
  errLocsWithContext shorSurfaceCircuit

/-- Decidable Bool predicate over a global site list: every `(site, p)` branch
(`p ∈ {X,Y,Z}`) is either globally policy-detected (full-circuit syndrome/flag
XOR vector nonzero) or has a `DeltaSafe` data delta (`surfaceBarrierData ≤ 1`).
This is the Bool image of `NoUndetectedHook`'s `FiresDetector ∨ BranchSafeβ`. -/
def globalHookSafePred (sites : List (ErrLocWithContext Nq)) : Bool :=
  sites.all (fun site =>
    [Pauli.X, Pauli.Y, Pauli.Z].all (fun p =>
      let free := propagateCircuit site.suffix (cleanAtDetector site.detectorStart)
      let flt := propagateCircuit site.suffix
        ((cleanAtDetector site.detectorStart).inject site.q p)
      let detected := (List.finRange (surfaceSpecShor.numStab + surfaceSpecShor.numFlags)).any
        (fun k => policyDiff free flt k)
      let safe := decide (SurfaceD3.surfaceBarrierData (dataPart flt) ≤ 1)
      detected || safe))

/-- Plain data delta of a `(site, p)` branch (matches `gDelta` of the
corresponding `GBranch`). -/
def gSiteDelta (site : ErrLocWithContext Nq) (p : Pauli) : DataPauli :=
  dataPart (propagateCircuit site.suffix
    ((cleanAtDetector site.detectorStart).inject site.q p))

/-- Plain policy detector vector of a `(site, p)` branch as a `Bool` list (the
`policyDiff` evaluated on the full policy index range).  Matches `gPolicy` of the
corresponding `GBranch` pointwise; the `Bool`-list form keeps the `decide`
comparison shallow. -/
def gSitePolicyList (site : ErrLocWithContext Nq) (p : Pauli) : List Bool :=
  let free := propagateCircuit site.suffix (cleanAtDetector site.detectorStart)
  let flt := propagateCircuit site.suffix ((cleanAtDetector site.detectorStart).inject site.q p)
  (List.finRange (surfaceSpecShor.numStab + surfaceSpecShor.numFlags)).map
    (fun k => policyDiff free flt k)

/-- **The scoped pairwise danger check.**  For every `(site0, p0)` branch in
`sites` that is *dangerous* (data barrier `≥ 2`), and every branch `(site1, p1)`
over the whole circuit whose policy detector vector *equals* `(site0,p0)`'s, the
product data barrier is `≤ 2`.  Benign first branches (`barrier ≤ 1`) are skipped
(the both-benign case is closed by subadditivity, not by this check).  Since only
four global branches are dangerous, the inner whole-circuit sweep fires only four
times. -/
def dangerPairPred (sites : List (ErrLocWithContext Nq)) : Bool :=
  sites.all (fun s0 => [Pauli.X, Pauli.Y, Pauli.Z].all (fun p0 =>
    if decide (SurfaceD3.surfaceBarrierData (gSiteDelta s0 p0) ≥ 2) then
      globalSites.all (fun s1 => [Pauli.X, Pauli.Y, Pauli.Z].all (fun p1 =>
        if gSitePolicyList s0 p0 == gSitePolicyList s1 p1 then
          decide (SurfaceD3.surfaceBarrierData
            (QStab.Paper.SurfaceD3CircuitDistance.pmul (gSiteDelta s0 p0) (gSiteDelta s1 p1)) ≤ 2)
        else true))
    else true))

/-- `dangerPairPred` distributes over list append via `List.all_append`. -/
theorem dangerPairPred_append (s1 s2 : List (ErrLocWithContext Nq)) :
    dangerPairPred (s1 ++ s2) = (dangerPairPred s1 && dangerPairPred s2) := by
  simp [dangerPairPred, List.all_append]

/-- `globalHookSafePred` distributes over list append via `List.all_append`. -/
theorem globalHookSafePred_append (s1 s2 : List (ErrLocWithContext Nq)) :
    globalHookSafePred (s1 ++ s2) = (globalHookSafePred s1 && globalHookSafePred s2) := by
  simp [globalHookSafePred, List.all_append]

/-! ### Chunked verification of `globalHookSafePred globalSites = true`

`globalSites` has 176 sites.  We split into 18 chunks of ≤ 10 sites each.
Each chunk is proved by `decide` with 6M heartbeats (≈ 3 min, well under 8 min).
The chunks are combined via `globalHookSafePred_append` and `List.take_append_drop`.
-/

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c00 :
    globalHookSafePred (globalSites.take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c01 :
    globalHookSafePred ((globalSites.drop 10).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c02 :
    globalHookSafePred ((globalSites.drop 20).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c03 :
    globalHookSafePred ((globalSites.drop 30).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c04 :
    globalHookSafePred ((globalSites.drop 40).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c05 :
    globalHookSafePred ((globalSites.drop 50).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c06 :
    globalHookSafePred ((globalSites.drop 60).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c07 :
    globalHookSafePred ((globalSites.drop 70).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c08 :
    globalHookSafePred ((globalSites.drop 80).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c09 :
    globalHookSafePred ((globalSites.drop 90).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c10 :
    globalHookSafePred ((globalSites.drop 100).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c11 :
    globalHookSafePred ((globalSites.drop 110).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c12 :
    globalHookSafePred ((globalSites.drop 120).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c13 :
    globalHookSafePred ((globalSites.drop 130).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c14 :
    globalHookSafePred ((globalSites.drop 140).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c15 :
    globalHookSafePred ((globalSites.drop 150).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c16 :
    globalHookSafePred ((globalSites.drop 160).take 10) = true := by
  unfold globalSites; decide

set_option maxHeartbeats 6000000 in
theorem globalHookSafePred_c17 :
    globalHookSafePred (globalSites.drop 170) = true := by
  unfold globalSites; decide

/-- Combine the 18 chunks via an explicit `rw` chain to avoid simp recursion depth issues. -/
theorem globalHookSafePred_true :
    globalHookSafePred globalSites = true := by
  rw [show globalSites = globalSites.take 10 ++ globalSites.drop 10 from
      (List.take_append_drop 10 globalSites).symm,
    globalHookSafePred_append, globalHookSafePred_c00, Bool.true_and,
    show globalSites.drop 10 = (globalSites.drop 10).take 10 ++ globalSites.drop 20 from
      (List.take_append_drop 10 (globalSites.drop 10)).symm,
    globalHookSafePred_append, globalHookSafePred_c01, Bool.true_and,
    show globalSites.drop 20 = (globalSites.drop 20).take 10 ++ globalSites.drop 30 from
      (List.take_append_drop 10 (globalSites.drop 20)).symm,
    globalHookSafePred_append, globalHookSafePred_c02, Bool.true_and,
    show globalSites.drop 30 = (globalSites.drop 30).take 10 ++ globalSites.drop 40 from
      (List.take_append_drop 10 (globalSites.drop 30)).symm,
    globalHookSafePred_append, globalHookSafePred_c03, Bool.true_and,
    show globalSites.drop 40 = (globalSites.drop 40).take 10 ++ globalSites.drop 50 from
      (List.take_append_drop 10 (globalSites.drop 40)).symm,
    globalHookSafePred_append, globalHookSafePred_c04, Bool.true_and,
    show globalSites.drop 50 = (globalSites.drop 50).take 10 ++ globalSites.drop 60 from
      (List.take_append_drop 10 (globalSites.drop 50)).symm,
    globalHookSafePred_append, globalHookSafePred_c05, Bool.true_and,
    show globalSites.drop 60 = (globalSites.drop 60).take 10 ++ globalSites.drop 70 from
      (List.take_append_drop 10 (globalSites.drop 60)).symm,
    globalHookSafePred_append, globalHookSafePred_c06, Bool.true_and,
    show globalSites.drop 70 = (globalSites.drop 70).take 10 ++ globalSites.drop 80 from
      (List.take_append_drop 10 (globalSites.drop 70)).symm,
    globalHookSafePred_append, globalHookSafePred_c07, Bool.true_and,
    show globalSites.drop 80 = (globalSites.drop 80).take 10 ++ globalSites.drop 90 from
      (List.take_append_drop 10 (globalSites.drop 80)).symm,
    globalHookSafePred_append, globalHookSafePred_c08, Bool.true_and,
    show globalSites.drop 90 = (globalSites.drop 90).take 10 ++ globalSites.drop 100 from
      (List.take_append_drop 10 (globalSites.drop 90)).symm,
    globalHookSafePred_append, globalHookSafePred_c09, Bool.true_and,
    show globalSites.drop 100 = (globalSites.drop 100).take 10 ++ globalSites.drop 110 from
      (List.take_append_drop 10 (globalSites.drop 100)).symm,
    globalHookSafePred_append, globalHookSafePred_c10, Bool.true_and,
    show globalSites.drop 110 = (globalSites.drop 110).take 10 ++ globalSites.drop 120 from
      (List.take_append_drop 10 (globalSites.drop 110)).symm,
    globalHookSafePred_append, globalHookSafePred_c11, Bool.true_and,
    show globalSites.drop 120 = (globalSites.drop 120).take 10 ++ globalSites.drop 130 from
      (List.take_append_drop 10 (globalSites.drop 120)).symm,
    globalHookSafePred_append, globalHookSafePred_c12, Bool.true_and,
    show globalSites.drop 130 = (globalSites.drop 130).take 10 ++ globalSites.drop 140 from
      (List.take_append_drop 10 (globalSites.drop 130)).symm,
    globalHookSafePred_append, globalHookSafePred_c13, Bool.true_and,
    show globalSites.drop 140 = (globalSites.drop 140).take 10 ++ globalSites.drop 150 from
      (List.take_append_drop 10 (globalSites.drop 140)).symm,
    globalHookSafePred_append, globalHookSafePred_c14, Bool.true_and,
    show globalSites.drop 150 = (globalSites.drop 150).take 10 ++ globalSites.drop 160 from
      (List.take_append_drop 10 (globalSites.drop 150)).symm,
    globalHookSafePred_append, globalHookSafePred_c15, Bool.true_and,
    show globalSites.drop 160 = (globalSites.drop 160).take 10 ++ globalSites.drop 170 from
      (List.take_append_drop 10 (globalSites.drop 160)).symm,
    globalHookSafePred_append, globalHookSafePred_c16, Bool.true_and,
    globalHookSafePred_c17]

/-! ### Chunked verification of `dangerPairPred globalSites = true`

Same 18-chunk split as `globalHookSafePred`.  Only the two chunks containing the
four dangerous branches (site `4` in chunk `00`, site `88` in chunk `08`) do real
product work; the other sixteen chunks have no dangerous first branch, so the
`barrier ≥ 2` guard is `false` and each `(site, p)` is dispatched immediately. -/

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c00 :
    dangerPairPred (globalSites.take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c01 :
    dangerPairPred ((globalSites.drop 10).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c02 :
    dangerPairPred ((globalSites.drop 20).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c03 :
    dangerPairPred ((globalSites.drop 30).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c04 :
    dangerPairPred ((globalSites.drop 40).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c05 :
    dangerPairPred ((globalSites.drop 50).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c06 :
    dangerPairPred ((globalSites.drop 60).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c07 :
    dangerPairPred ((globalSites.drop 70).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c08 :
    dangerPairPred ((globalSites.drop 80).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c09 :
    dangerPairPred ((globalSites.drop 90).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c10 :
    dangerPairPred ((globalSites.drop 100).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c11 :
    dangerPairPred ((globalSites.drop 110).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c12 :
    dangerPairPred ((globalSites.drop 120).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c13 :
    dangerPairPred ((globalSites.drop 130).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c14 :
    dangerPairPred ((globalSites.drop 140).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c15 :
    dangerPairPred ((globalSites.drop 150).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c16 :
    dangerPairPred ((globalSites.drop 160).take 10) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

set_option maxHeartbeats 6000000 in
theorem dangerPairPred_c17 :
    dangerPairPred (globalSites.drop 170) = true := by
  unfold dangerPairPred globalSites
  set_option maxRecDepth 8000 in decide

/-- Combine the 18 chunks via an explicit `rw` chain. -/
theorem dangerPairPred_true :
    dangerPairPred globalSites = true := by
  rw [show globalSites = globalSites.take 10 ++ globalSites.drop 10 from
      (List.take_append_drop 10 globalSites).symm,
    dangerPairPred_append, dangerPairPred_c00, Bool.true_and,
    show globalSites.drop 10 = (globalSites.drop 10).take 10 ++ globalSites.drop 20 from
      (List.take_append_drop 10 (globalSites.drop 10)).symm,
    dangerPairPred_append, dangerPairPred_c01, Bool.true_and,
    show globalSites.drop 20 = (globalSites.drop 20).take 10 ++ globalSites.drop 30 from
      (List.take_append_drop 10 (globalSites.drop 20)).symm,
    dangerPairPred_append, dangerPairPred_c02, Bool.true_and,
    show globalSites.drop 30 = (globalSites.drop 30).take 10 ++ globalSites.drop 40 from
      (List.take_append_drop 10 (globalSites.drop 30)).symm,
    dangerPairPred_append, dangerPairPred_c03, Bool.true_and,
    show globalSites.drop 40 = (globalSites.drop 40).take 10 ++ globalSites.drop 50 from
      (List.take_append_drop 10 (globalSites.drop 40)).symm,
    dangerPairPred_append, dangerPairPred_c04, Bool.true_and,
    show globalSites.drop 50 = (globalSites.drop 50).take 10 ++ globalSites.drop 60 from
      (List.take_append_drop 10 (globalSites.drop 50)).symm,
    dangerPairPred_append, dangerPairPred_c05, Bool.true_and,
    show globalSites.drop 60 = (globalSites.drop 60).take 10 ++ globalSites.drop 70 from
      (List.take_append_drop 10 (globalSites.drop 60)).symm,
    dangerPairPred_append, dangerPairPred_c06, Bool.true_and,
    show globalSites.drop 70 = (globalSites.drop 70).take 10 ++ globalSites.drop 80 from
      (List.take_append_drop 10 (globalSites.drop 70)).symm,
    dangerPairPred_append, dangerPairPred_c07, Bool.true_and,
    show globalSites.drop 80 = (globalSites.drop 80).take 10 ++ globalSites.drop 90 from
      (List.take_append_drop 10 (globalSites.drop 80)).symm,
    dangerPairPred_append, dangerPairPred_c08, Bool.true_and,
    show globalSites.drop 90 = (globalSites.drop 90).take 10 ++ globalSites.drop 100 from
      (List.take_append_drop 10 (globalSites.drop 90)).symm,
    dangerPairPred_append, dangerPairPred_c09, Bool.true_and,
    show globalSites.drop 100 = (globalSites.drop 100).take 10 ++ globalSites.drop 110 from
      (List.take_append_drop 10 (globalSites.drop 100)).symm,
    dangerPairPred_append, dangerPairPred_c10, Bool.true_and,
    show globalSites.drop 110 = (globalSites.drop 110).take 10 ++ globalSites.drop 120 from
      (List.take_append_drop 10 (globalSites.drop 110)).symm,
    dangerPairPred_append, dangerPairPred_c11, Bool.true_and,
    show globalSites.drop 120 = (globalSites.drop 120).take 10 ++ globalSites.drop 130 from
      (List.take_append_drop 10 (globalSites.drop 120)).symm,
    dangerPairPred_append, dangerPairPred_c12, Bool.true_and,
    show globalSites.drop 130 = (globalSites.drop 130).take 10 ++ globalSites.drop 140 from
      (List.take_append_drop 10 (globalSites.drop 130)).symm,
    dangerPairPred_append, dangerPairPred_c13, Bool.true_and,
    show globalSites.drop 140 = (globalSites.drop 140).take 10 ++ globalSites.drop 150 from
      (List.take_append_drop 10 (globalSites.drop 140)).symm,
    dangerPairPred_append, dangerPairPred_c14, Bool.true_and,
    show globalSites.drop 150 = (globalSites.drop 150).take 10 ++ globalSites.drop 160 from
      (List.take_append_drop 10 (globalSites.drop 150)).symm,
    dangerPairPred_append, dangerPairPred_c15, Bool.true_and,
    show globalSites.drop 160 = (globalSites.drop 160).take 10 ++ globalSites.drop 170 from
      (List.take_append_drop 10 (globalSites.drop 160)).symm,
    dangerPairPred_append, dangerPairPred_c16, Bool.true_and,
    dangerPairPred_c17]

/-! ### Global bridge lemmas and `surfaceNoUndetectedHook_global` -/

private theorem barrierLe1_deltaSafe_global
    (E : QStab.Paper.SurfaceD3CircuitDistance.DataPauli)
    (h : SurfaceD3.surfaceBarrierData E ≤ 1) :
    QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe E :=
  surfaceBarrierData_le1_implies_deltaSafe E h

private theorem deltaSafe_branchSafe_global (site : ErrLocWithContext Nq) (p : Pauli)
    (hSafe : QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe
      (dataPart (propagateCircuit site.suffix
        ((cleanAtDetector site.detectorStart).inject site.q p)))) :
    BranchSafeβ surfaceBarrier site.toSuffix p := by
  intro es
  unfold surfaceBarrier ErrLocWithContext.toSuffix
  rw [dataPart_inject_factor site.suffix es site.q p]
  have hconv : dataPart (propagateCircuit site.suffix ((ErrorState.clean Nq).inject site.q p))
      = dataPart (propagateCircuit site.suffix
          ((cleanAtDetector site.detectorStart).inject site.q p)) := by
    unfold dataPart; funext q
    have hpaulis : ((ErrorState.clean Nq).inject site.q p).paulis
        = ((cleanAtDetector site.detectorStart).inject site.q p).paulis := by
      funext r; simp [ErrorState.inject, cleanAtDetector, ErrorState.clean]
    rw [propagateCircuit_paulis_congr site.suffix _ _ hpaulis]
  rw [hconv]
  exact SurfaceD3.surfaceBarrierData_step hSafe

private theorem policyDiff_fires_global (a b : ErrorState Nq) (k : PolicyIdx)
    (hk : policyDiff a b k = true) :
    detectorObservableDiff surfaceSpecShor a b := by
  unfold policyDiff policyXor policyObservation at hk
  by_cases hks : k.val < surfaceSpecShor.numStab
  · simp only [hks, dite_true] at hk
    left; refine ⟨⟨k.val, hks⟩, ?_⟩
    intro heq; rw [heq] at hk; simp at hk
  · simp only [hks, dite_false] at hk
    set f : Fin surfaceSpecShor.numFlags :=
      ⟨k.val - surfaceSpecShor.numStab, by have := k.isLt; omega⟩ with hf
    have hsel : surfaceSpecShor.postselectFlag f = true := by
      by_contra hsel; simp only [Bool.not_eq_true] at hsel
      rw [hsel] at hk; simp at hk
    rw [hsel] at hk; simp only [if_true] at hk
    right; refine ⟨f, hsel, ?_⟩
    intro heq; rw [heq] at hk; simp at hk

/-- **Global single-fault completeness.**  Every error location of the whole
Shor surface circuit with a nontrivial Pauli either is benign for the barrier
(`BranchSafeβ`) or fires a policy detector over the full remaining circuit
(`FiresDetector`).  Proved by `globalHookSafePred_true`. -/
theorem surfaceNoUndetectedHook_global :
    NoUndetectedHook shorSurfaceCircuit surfaceSpecShor surfaceBarrier := by
  intro site hmem p hp
  have hPred := globalHookSafePred_true
  unfold globalHookSafePred globalSites at hPred
  rw [List.all_eq_true] at hPred
  have hsite := hPred site hmem
  rw [List.all_eq_true] at hsite
  have hp3 := hsite p (pauli_mem_XYZ hp)
  simp only at hp3
  set free := propagateCircuit site.suffix (cleanAtDetector site.detectorStart) with hfree
  set flt := propagateCircuit site.suffix
    ((cleanAtDetector site.detectorStart).inject site.q p) with hflt
  rcases Bool.or_eq_true_iff.mp hp3 with hdet | hsafe
  · right
    unfold FiresDetector
    rw [List.any_eq_true] at hdet
    obtain ⟨k, _, hk⟩ := hdet
    rw [← hfree, ← hflt]
    exact policyDiff_fires_global free flt k hk
  · left
    rw [decide_eq_true_eq] at hsafe
    apply deltaSafe_branchSafe_global site p
    rw [← hflt]
    exact barrierLe1_deltaSafe_global _ hsafe

end QStab.QClifford.PCC.SurfaceD3Shor