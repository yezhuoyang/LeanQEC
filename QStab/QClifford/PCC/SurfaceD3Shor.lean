import QStab.QClifford.PCC.SurfaceD3ShorGlobal

/-!
# Surface-d3 Shor PCC skeleton

This file provides the proof ladder and `GBranch`/`GContribution` global
cancellation algebra for the Shor surface-d3 circuit.  Base circuit
definitions live in `SurfaceD3ShorBase`; the heavy global `decide`
(`globalHookSafePred_true`) lives in `SurfaceD3ShorGlobal` so that editing
this file does not rebuild it.
-/

namespace QStab.QClifford.PCC.SurfaceD3Shor

/-- The exact producer-side theorem still needed to close
`surfaceD3_shor_safe` via `certificate_sound'`. -/
def surfaceAcceptedBarrierBound : Prop :=
  AcceptedBarrierBound shorSurfaceCircuit surfaceSpecShor surfaceBarrier

/-- Local Shor pair-cancellation tooth, re-exported next to the surface Shor
skeleton.  This is a necessary local ingredient, but not by itself the
run-level grouping theorem. -/
theorem shor4_full_hook_pair_trueWeight_zero :
    QStab.Paper.SoundnessPrime.trueWeight QStab.QClifford.Shor.shor4XStabilizer
      (ErrorVec.mul QStab.QClifford.Shor.shor4XStabilizer
        QStab.QClifford.Shor.shor4XStabilizer) = 0 :=
  QStab.QClifford.Shor.shor4FullHookPair_trueWeight_zero

/-! ## Accepted-barrier proof ladder -/

structure SurfaceFaultBranch where
  gadget : StabIdx
  site : ErrLocWithContext Nq
  site_mem : site ∈ errLocsWithContext (surfaceSpecShor.gadget gadget)
  pauli : Pauli
  pauli_ne_I : pauli ≠ Pauli.I

def branchFreeState (b : SurfaceFaultBranch) : ErrorState Nq :=
  propagateCircuit b.site.suffix (cleanAtDetector b.site.detectorStart)

def branchFaultState (b : SurfaceFaultBranch) : ErrorState Nq :=
  propagateCircuit b.site.suffix
    ((cleanAtDetector b.site.detectorStart).inject b.site.q b.pauli)

def branchDelta (b : SurfaceFaultBranch) : DataPauli :=
  dataPart (branchFaultState b)

def branchPolicy (b : SurfaceFaultBranch) : PolicyVec :=
  policyDiff (branchFreeState b) (branchFaultState b)

def branchSafe (b : SurfaceFaultBranch) : Prop :=
  BranchSafeβ surfaceBarrier b.site.toSuffix b.pauli

def branchFires (b : SurfaceFaultBranch) : Prop :=
  FiresDetector (surfaceSpecShor.gadget b.gadget) surfaceSpecShor b.site b.pauli

structure SurfaceFaultContribution where
  branch : SurfaceFaultBranch
  delta : DataPauli
  policy : PolicyVec
  delta_eq : delta = branchDelta branch
  policy_eq : policy = branchPolicy branch

def contributionDataProduct (cs : List SurfaceFaultContribution) : DataPauli :=
  dataProd (cs.map SurfaceFaultContribution.delta)

def contributionPolicyXor (cs : List SurfaceFaultContribution) : PolicyVec :=
  policyXorList (cs.map SurfaceFaultContribution.policy)

def contributionBenign (c : SurfaceFaultContribution) : Prop :=
  QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe c.delta

def contributionDangerous (c : SurfaceFaultContribution) : Prop :=
  ¬ contributionBenign c

def contributionDetected (c : SurfaceFaultContribution) : Prop :=
  c.policy ≠ policyZero

theorem dangerous_branch_fires (b : SurfaceFaultBranch)
    (hNo : NoUndetectedHook (surfaceSpecShor.gadget b.gadget) surfaceSpecShor surfaceBarrier)
    (hDanger : ¬ branchSafe b) :
    branchFires b := by
  have h := hNo b.site b.site_mem b.pauli b.pauli_ne_I
  rcases h with hSafe | hFire
  · exact False.elim (hDanger hSafe)
  · exact hFire

theorem surface_XRowsLe_pmul {E D : DataPauli} {f g : Nat}
    (hEX : QStab.Paper.SurfaceD3CircuitDistance.XRowsLe E f)
    (hDX : QStab.Paper.SurfaceD3CircuitDistance.XRowsLe D g) :
    QStab.Paper.SurfaceD3CircuitDistance.XRowsLe
      (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) (f + g) := by
  unfold QStab.Paper.SurfaceD3CircuitDistance.XRowsLe at hEX hDX ⊢
  rcases Finset.card_pos.mp hEX with ⟨mE, hmE⟩
  rcases Finset.card_pos.mp hDX with ⟨mD, hmD⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmE hmD
  apply Finset.card_pos.mpr
  refine ⟨QStab.Paper.SurfaceD3CircuitDistance.maskXor mE mD, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hrepr :
      QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.prodStab
            (QStab.Paper.SurfaceD3CircuitDistance.maskXor mE mD))
          (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) =
        QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mE) E)
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mD) D) := by
    calc
      QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.prodStab
            (QStab.Paper.SurfaceD3CircuitDistance.maskXor mE mD))
          (QStab.Paper.SurfaceD3CircuitDistance.pmul E D)
          =
        QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mE)
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mD))
          (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) := by
              rw [QStab.Paper.SurfaceD3CircuitDistance.prodStab_xor mE mD]
      _ =
        QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mE) E)
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mD) D) := by
              funext q
              let a := QStab.Paper.SurfaceD3CircuitDistance.prodStab mE q
              let b := QStab.Paper.SurfaceD3CircuitDistance.prodStab mD q
              let c := E q
              let d := D q
              change Pauli.mul (Pauli.mul a b) (Pauli.mul c d) =
                Pauli.mul (Pauli.mul a c) (Pauli.mul b d)
              cases a <;> cases b <;> cases c <;> cases d <;> rfl
  rw [hrepr]
  exact Nat.le_trans
    (QStab.Paper.SurfaceD3CircuitDistance.rowSpreadX_pmul_le _ _)
    (Nat.add_le_add hmE hmD)

theorem surface_ZColsLe_pmul {E D : DataPauli} {f g : Nat}
    (hEZ : QStab.Paper.SurfaceD3CircuitDistance.ZColsLe E f)
    (hDZ : QStab.Paper.SurfaceD3CircuitDistance.ZColsLe D g) :
    QStab.Paper.SurfaceD3CircuitDistance.ZColsLe
      (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) (f + g) := by
  unfold QStab.Paper.SurfaceD3CircuitDistance.ZColsLe at hEZ hDZ ⊢
  rcases Finset.card_pos.mp hEZ with ⟨mE, hmE⟩
  rcases Finset.card_pos.mp hDZ with ⟨mD, hmD⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmE hmD
  apply Finset.card_pos.mpr
  refine ⟨QStab.Paper.SurfaceD3CircuitDistance.maskXor mE mD, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hrepr :
      QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.prodStab
            (QStab.Paper.SurfaceD3CircuitDistance.maskXor mE mD))
          (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) =
        QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mE) E)
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mD) D) := by
    calc
      QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.prodStab
            (QStab.Paper.SurfaceD3CircuitDistance.maskXor mE mD))
          (QStab.Paper.SurfaceD3CircuitDistance.pmul E D)
          =
        QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mE)
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mD))
          (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) := by
              rw [QStab.Paper.SurfaceD3CircuitDistance.prodStab_xor mE mD]
      _ =
        QStab.Paper.SurfaceD3CircuitDistance.pmul
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mE) E)
          (QStab.Paper.SurfaceD3CircuitDistance.pmul
            (QStab.Paper.SurfaceD3CircuitDistance.prodStab mD) D) := by
              funext q
              let a := QStab.Paper.SurfaceD3CircuitDistance.prodStab mE q
              let b := QStab.Paper.SurfaceD3CircuitDistance.prodStab mD q
              let c := E q
              let d := D q
              change Pauli.mul (Pauli.mul a b) (Pauli.mul c d) =
                Pauli.mul (Pauli.mul a c) (Pauli.mul b d)
              cases a <;> cases b <;> cases c <;> cases d <;> rfl
  rw [hrepr]
  exact Nat.le_trans
    (QStab.Paper.SurfaceD3CircuitDistance.colSpreadZ_pmul_le _ _)
    (Nat.add_le_add hmE hmD)

theorem surface_BI_PAIR_pmul {E D : DataPauli} {f g : Nat}
    (hE : QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E f)
    (hD : QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR D g) :
    QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR
      (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) (f + g) :=
  ⟨surface_XRowsLe_pmul hE.1 hD.1, surface_ZColsLe_pmul hE.2 hD.2⟩

/-- L3: the concrete surface barrier is subadditive under Pauli product. -/
theorem dangerousSpread_subadditive (A B : DataPauli) :
    SurfaceD3.surfaceBarrierData
        (QStab.Paper.SurfaceD3CircuitDistance.pmul A B) <=
      SurfaceD3.surfaceBarrierData A + SurfaceD3.surfaceBarrierData B := by
  apply SurfaceD3.surfaceBarrierData_le_of_BI_PAIR
  exact surface_BI_PAIR_pmul
    (SurfaceD3.BI_PAIR_surfaceBarrierData A)
    (SurfaceD3.BI_PAIR_surfaceBarrierData B)

/-- L1: if a concrete branch is not observed by the policy detector and the
first-class `NoUndetectedHook` VC holds for its gadget, then the branch is
benign for the barrier. -/
theorem benign_spread_le {i : StabIdx} {site : ErrLocWithContext Nq} {p : Pauli}
    (hNo : NoUndetectedHook (surfaceSpecShor.gadget i) surfaceSpecShor surfaceBarrier)
    (hSite : site ∈ errLocsWithContext (surfaceSpecShor.gadget i))
    (hp : p ≠ Pauli.I)
    (hNoFire : ¬ FiresDetector (surfaceSpecShor.gadget i) surfaceSpecShor site p) :
    BranchSafeβ surfaceBarrier site.toSuffix p := by
  have h := hNo site hSite p hp
  rcases h with hSafe | hFire
  · exact hSafe
  · exact False.elim (hNoFire hFire)

theorem policyObservation_eq_zero_of_allFlagsZero {es : ErrorState Nq}
    (h : allFlagsZero surfaceSpecShor es) :
    policyObservation es = policyZero := by
  funext k
  unfold policyObservation policyZero
  by_cases hk : k.val < surfaceSpecShor.numStab
  · simp [hk, h.1 ⟨k.val, hk⟩]
  · simp [hk]
    by_cases hp :
        surfaceSpecShor.postselectFlag
          ⟨k.val - surfaceSpecShor.numStab, by
            have hklt := k.isLt
            omega⟩ = true
    · simpa [hp] using
        h.2 ⟨k.val - surfaceSpecShor.numStab, by
          have hklt := k.isLt
          omega⟩ hp
    · simp [hp]

theorem contribution_benign_barrier_le_one {c : SurfaceFaultContribution}
    (h : contributionBenign c) :
    SurfaceD3.surfaceBarrierData c.delta <= 1 := by
  apply SurfaceD3.surfaceBarrierData_le_of_BI_PAIR
  have hBI :=
    QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR_pmul_of_delta_safe
      QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT h
  simpa [QStab.Paper.SurfaceD3CircuitDistance.dataI,
    QStab.Paper.SurfaceD3CircuitDistance.pmul] using hBI

theorem benign_contribution_product_le_length :
    ∀ cs : List SurfaceFaultContribution,
      (∀ c ∈ cs, contributionBenign c) ->
        SurfaceD3.surfaceBarrierData (contributionDataProduct cs) <= cs.length
  | [], _ => by
      unfold contributionDataProduct dataProd
      apply SurfaceD3.surfaceBarrierData_le_of_BI_PAIR
      simpa using QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT
  | c :: rest, h => by
      have hc : SurfaceD3.surfaceBarrierData c.delta <= 1 :=
        contribution_benign_barrier_le_one (h c (by simp))
      have hrest :
          SurfaceD3.surfaceBarrierData (contributionDataProduct rest) <= rest.length :=
        benign_contribution_product_le_length rest (by
          intro d hd
          exact h d (by simp [hd]))
      have hsub := dangerousSpread_subadditive c.delta (contributionDataProduct rest)
      have hprod :
          contributionDataProduct (c :: rest) =
            QStab.Paper.SurfaceD3CircuitDistance.pmul c.delta
              (contributionDataProduct rest) := by
        simp [contributionDataProduct, dataProd]
      calc
        SurfaceD3.surfaceBarrierData (contributionDataProduct (c :: rest))
            <= SurfaceD3.surfaceBarrierData c.delta +
                SurfaceD3.surfaceBarrierData (contributionDataProduct rest) := by
              simpa [hprod] using hsub
        _ <= 1 + rest.length := Nat.add_le_add hc hrest
        _ = rest.length + 1 := Nat.add_comm 1 rest.length
        _ = (c :: rest).length := rfl

/-- L0, still open as producer-side content: extract a linear list of
per-fault data and policy-detector contributions from an arbitrary
`fcevalW` run of the real Shor surface circuit. -/
def fcevalW_linear : Prop :=
  ∀ {w : Nat} {es : ErrorState Nq},
    fcevalW w shorSurfaceCircuit (ErrorState.clean Nq) es ->
      ∃ cs : List SurfaceFaultContribution,
        cs.length = w ∧
          dataPart es = contributionDataProduct cs ∧
          policyObservation es = contributionPolicyXor cs

/-- L2, the crux still open as producer-side content after the detection-split
refactor: detected contributions whose policy detector vector XOR-cancels have
product bounded by their cardinality.  This intentionally includes benign
detected members, which are harmless, and leaves the real work to cancelling
detected dangerous hooks via the Shor hook-pair algebra. -/
def detected_group_le : Prop :=
  ∀ cs : List SurfaceFaultContribution,
    (∀ c ∈ cs, contributionDetected c) ->
      contributionPolicyXor cs = policyZero ->
        SurfaceD3.surfaceBarrierData (contributionDataProduct cs) <= cs.length

/-- L4's remaining combinatorial partition theorem.  This is the place where
closed L1/L3 plus the still-open L2 must be assembled: split an accepted list
into undetected benign singleton faults and detected detector-cancelling
groups, then use subadditivity. -/
def accepted_contribution_partition_bound : Prop :=
  ∀ cs : List SurfaceFaultContribution,
    contributionPolicyXor cs = policyZero ->
      SurfaceD3.surfaceBarrierData (contributionDataProduct cs) <= cs.length

/-- L4 plumbing: once L0 and the accepted-list partition bound are available,
the PCC `AcceptedBarrierBound` obligation follows for the concrete Shor
surface circuit. -/
theorem surfaceAcceptedBarrierBound_of_ladder
    (hLinear : fcevalW_linear)
    (hPartition : accepted_contribution_partition_bound) :
    surfaceAcceptedBarrierBound := by
  intro w es hrun hAccepted
  rcases hLinear hrun with ⟨cs, hlen, hdata, hpolicy⟩
  unfold surfaceBarrier
  rw [hdata]
  have hzero := policyObservation_eq_zero_of_allFlagsZero hAccepted
  have hcancel : contributionPolicyXor cs = policyZero := by
    rw [← hpolicy, hzero]
  have hbound := hPartition cs hcancel
  rwa [hlen] at hbound

/-! ## Glue lemmas: bridge, list helpers, and assembly -/

-- Private helpers for the bridge and assembly

private theorem propagateGate_clean_paulis_aux {nq : Nat} (g : QStab.QClifford.Gate nq)
    (es : QStab.QClifford.ErrorState nq)
    (h : ∀ q, es.paulis q = Pauli.I) : ∀ q, (QStab.QClifford.propagateGate g es).paulis q = Pauli.I := by
  intro q; cases g with
  | cnot c t hne =>
    simp only [QStab.QClifford.propagateGate]; split_ifs with ht hc
    · simp [QStab.QClifford.xPart, h c, h t, QStab.QClifford.pauliMul]
    · simp [QStab.QClifford.zPart, h t, QStab.QClifford.pauliMul, h c]
    · exact h q
  | hadamard q' =>
    simp only [QStab.QClifford.propagateGate]; split_ifs with hq
    · rw [hq]; simp [QStab.QClifford.hadamardAction, h q']
    · exact h q
  | prepZero q' => simp [QStab.QClifford.propagateGate, h q]
  | prepPlus q' => simp [QStab.QClifford.propagateGate, h q]
  | measZ q' => simp [QStab.QClifford.propagateGate, h q]

private theorem propagateCircuit_clean_paulis_aux {nq : Nat}
    (C : QStab.QClifford.Circuit nq) (es : QStab.QClifford.ErrorState nq)
    (h : ∀ q, es.paulis q = Pauli.I) :
    ∀ q, (QStab.QClifford.propagateCircuit C es).paulis q = Pauli.I := by
  induction C generalizing es with
  | nil => exact h
  | cons g rest ih =>
    simp only [QStab.QClifford.propagateCircuit]
    exact ih _ (propagateGate_clean_paulis_aux g es h)

private theorem branchFreeState_dataPart_dataI (b : SurfaceFaultBranch) :
    dataPart (branchFreeState b) = QStab.Paper.SurfaceD3CircuitDistance.dataI := by
  funext q; unfold dataPart branchFreeState QStab.Paper.SurfaceD3CircuitDistance.dataI
  apply propagateCircuit_clean_paulis_aux
  intro r; simp [QStab.QClifford.PCC.cleanAtDetector, QStab.QClifford.ErrorState.clean]

private theorem branchSafe_implies_deltaSafe_aux (b : SurfaceFaultBranch)
    (hSafe : branchSafe b) :
    QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe (branchDelta b) := by
  apply surfaceBarrierData_le1_implies_deltaSafe
  have hBound : surfaceBarrier (branchFaultState b) ≤ surfaceBarrier (branchFreeState b) + 1 := by
    unfold branchSafe QStab.QClifford.PCC.BranchSafeβ at hSafe
    have := hSafe (QStab.QClifford.PCC.cleanAtDetector b.site.detectorStart)
    unfold branchFaultState branchFreeState QStab.QClifford.PCC.ErrLocWithContext.toSuffix at *
    exact this
  have hFreeZero : surfaceBarrier (branchFreeState b) = 0 := by
    unfold surfaceBarrier; rw [branchFreeState_dataPart_dataI]
    simp [QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData,
          QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT]
  rw [hFreeZero, Nat.zero_add] at hBound
  simp [surfaceBarrier, branchDelta] at hBound ⊢; exact hBound

private theorem policyXorList_append_aux (xs ys : List PolicyVec) :
    policyXorList (xs ++ ys) = policyXor (policyXorList xs) (policyXorList ys) := by
  induction xs with
  | nil => simp only [List.nil_append, policyXorList]; funext k; simp [policyXor, policyZero]
  | cons x rest ih =>
    simp only [List.cons_append, policyXorList]; rw [ih]
    funext k; simp only [policyXor, Bool.xor_assoc]

private theorem dataProd_append_aux (xs ys : List DataPauli) :
    dataProd (xs ++ ys) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul (dataProd xs) (dataProd ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, dataProd]
    unfold QStab.Paper.SurfaceD3CircuitDistance.pmul QStab.Paper.SurfaceD3CircuitDistance.dataI
    funext q; simp [Pauli.mul]
  | cons x rest ih =>
    simp only [List.cons_append, dataProd, ih]
    exact (QStab.Paper.SurfaceD3CircuitDistance.pmul_assoc _ _ _).symm

private theorem dataProd_perm_aux {xs ys : List DataPauli} (h : xs.Perm ys) :
    dataProd xs = dataProd ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [dataProd]; rw [ih]
  | swap x y rest =>
    simp only [dataProd]
    rw [← QStab.Paper.SurfaceD3CircuitDistance.pmul_assoc,
        QStab.Paper.SurfaceD3CircuitDistance.pmul_comm y x,
        QStab.Paper.SurfaceD3CircuitDistance.pmul_assoc]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

private theorem policyXorList_perm_aux {xs ys : List PolicyVec} (h : xs.Perm ys) :
    policyXorList xs = policyXorList ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [policyXorList]; rw [ih]
  | swap x y rest =>
    simp only [policyXorList]; funext k; simp only [policyXor]
    cases (x k) <;> cases (y k) <;> cases (policyXorList rest k) <;> simp
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- Decidability instance for `contributionDetected` (needed for `List.filter`). -/
noncomputable instance instDecidableContributionDetected (c : SurfaceFaultContribution) :
    Decidable (contributionDetected c) := by
  unfold contributionDetected; exact inferInstance

/-! ### Bridge theorems -/

/-- BRIDGE (→): if a branch fires the detector, its policy vector is non-zero.
This is the key direction needed by the assembly. -/
theorem branchFires_implies_branchPolicy_ne_zero (b : SurfaceFaultBranch)
    (hFire : branchFires b) : branchPolicy b ≠ policyZero := by
  unfold branchFires QStab.QClifford.PCC.FiresDetector at hFire
  unfold branchPolicy policyDiff policyXor policyObservation policyZero branchFreeState branchFaultState
  open QStab.QClifford QStab.QClifford.PCC in
  intro heq
  rcases hFire with ⟨i, hi⟩ | ⟨f, hf_sel, hf_diff⟩
  · have := congr_fun heq ⟨i.val, Nat.lt_add_right _ i.isLt⟩
    simp only [i.isLt, dite_true] at this
    exact hi (by
      cases syndromeBit surfaceSpecShor
          (propagateCircuit b.site.suffix (cleanAtDetector b.site.detectorStart)) i <;>
      cases syndromeBit surfaceSpecShor
          (propagateCircuit b.site.suffix
            ((cleanAtDetector b.site.detectorStart).inject b.site.q b.pauli)) i <;>
      simp_all)
  · have hk := congr_fun heq ⟨surfaceSpecShor.numStab + f.val, by omega⟩
    simp only [show ¬ (surfaceSpecShor.numStab + f.val < surfaceSpecShor.numStab) from by omega,
               dite_false, Nat.add_sub_cancel_left,
               show (⟨f.val, by omega⟩ : Fin surfaceSpecShor.numFlags) = f from Fin.ext rfl,
               hf_sel] at hk
    exact hf_diff (by
      cases (propagateCircuit b.site.suffix (cleanAtDetector b.site.detectorStart)).detectors
            (surfaceSpecShor.flagSlot f) <;>
      cases (propagateCircuit b.site.suffix
               ((cleanAtDetector b.site.detectorStart).inject b.site.q b.pauli)).detectors
             (surfaceSpecShor.flagSlot f) <;>
      simp_all)

/-- BRIDGE (contrapositive): a contribution whose policy is zero has safe (benign) delta,
given the per-gadget `NoUndetectedHook` VC. -/
theorem not_contributionDetected_implies_benign
    (c : SurfaceFaultContribution)
    (hNo : NoUndetectedHook (surfaceSpecShor.gadget c.branch.gadget) surfaceSpecShor surfaceBarrier)
    (hNotDet : ¬ contributionDetected c) :
    contributionBenign c := by
  unfold contributionBenign; rw [c.delta_eq]
  apply branchSafe_implies_deltaSafe_aux
  apply benign_spread_le hNo c.branch.site_mem c.branch.pauli_ne_I
  intro hFire
  exact hNotDet (by
    unfold contributionDetected; rw [c.policy_eq]
    exact branchFires_implies_branchPolicy_ne_zero c.branch hFire)

/-! ### List helpers for the partition assembly -/

/-- `contributionDataProduct` distributes over list concatenation. -/
theorem contributionDataProduct_append (cs ds : List SurfaceFaultContribution) :
    contributionDataProduct (cs ++ ds) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul
        (contributionDataProduct cs) (contributionDataProduct ds) := by
  simp only [contributionDataProduct, List.map_append, dataProd_append_aux]

/-- `contributionPolicyXor` distributes over list concatenation. -/
theorem contributionPolicyXor_append (cs ds : List SurfaceFaultContribution) :
    contributionPolicyXor (cs ++ ds) =
      policyXor (contributionPolicyXor cs) (contributionPolicyXor ds) := by
  simp only [contributionPolicyXor, List.map_append, policyXorList_append_aux]

/-- `contributionDataProduct` is invariant under list permutation. -/
theorem contributionDataProduct_perm {cs ds : List SurfaceFaultContribution} (h : cs.Perm ds) :
    contributionDataProduct cs = contributionDataProduct ds :=
  dataProd_perm_aux (h.map _)

/-- `contributionPolicyXor` is invariant under list permutation. -/
theorem contributionPolicyXor_perm {cs ds : List SurfaceFaultContribution} (h : cs.Perm ds) :
    contributionPolicyXor cs = contributionPolicyXor ds :=
  policyXorList_perm_aux (h.map _)

/-- A list of undetected contributions has `contributionPolicyXor = policyZero`. -/
theorem contributionPolicyXor_undetected_zero (cs : List SurfaceFaultContribution)
    (h : ∀ c ∈ cs, ¬ contributionDetected c) :
    contributionPolicyXor cs = policyZero := by
  unfold contributionPolicyXor
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map, policyXorList]
    have hcPol : c.policy = policyZero := by
      have := h c List.mem_cons_self
      unfold contributionDetected at this; push_neg at this
      rw [c.policy_eq] at this ⊢; exact this
    have hrestZero : policyXorList (List.map SurfaceFaultContribution.policy rest) = policyZero :=
      ih (fun d hd => h d (List.mem_cons_of_mem c hd))
    rw [hcPol, hrestZero]
    funext k; simp [policyXor, policyZero]

/-! ### Assembly: accepted_contribution_partition_bound from detected_group_le + NoUndetectedHook -/

/-- Conditional assembly: assuming `detected_group_le` and per-gadget `NoUndetectedHook`,
the `accepted_contribution_partition_bound` holds.

Proof sketch:
- Split `cs` into detected `D` and undetected `U` via `List.filter`.
- `cs ~ D ++ U` gives `contributionDataProduct cs = pmul (dataProd D) (dataProd U)`.
- `U` is all-benign (by `not_contributionDetected_implies_benign`) so
  `surfaceBarrierData (dataProd U) ≤ U.length`.
- `U` has `contributionPolicyXor U = policyZero`, so `contributionPolicyXor D = policyZero`
  (since the whole XOR is zero).
- `detected_group_le` gives `surfaceBarrierData (dataProd D) ≤ D.length`.
- Subadditivity: `surfaceBarrierData (pmul D U) ≤ D.length + U.length = cs.length`. -/
theorem partition_of_detected_group
    (hDet : detected_group_le)
    (hNo : ∀ i, NoUndetectedHook (surfaceSpecShor.gadget i) surfaceSpecShor surfaceBarrier) :
    accepted_contribution_partition_bound := by
  intro cs hCancel
  -- Partition cs into detected D and undetected U
  let detB : SurfaceFaultContribution → Bool := fun c => decide (contributionDetected c)
  let D := cs.filter detB
  let U := cs.filter (fun c => !detB c)
  -- cs ~ D ++ U
  have hPerm : (D ++ U).Perm cs := List.filter_append_perm detB cs
  -- Rearrange data product via perm + append
  have hDataEq : contributionDataProduct cs =
      QStab.Paper.SurfaceD3CircuitDistance.pmul
        (contributionDataProduct D) (contributionDataProduct U) := by
    rw [contributionDataProduct_perm hPerm.symm, contributionDataProduct_append]
  -- Rearrange policy XOR via perm + append
  have hPolicyEq : contributionPolicyXor cs =
      policyXor (contributionPolicyXor D) (contributionPolicyXor U) := by
    rw [contributionPolicyXor_perm hPerm.symm, contributionPolicyXor_append]
  -- U is all undetected
  have hUUndet : ∀ c ∈ U, ¬ contributionDetected c := by
    intro c hcU
    simp only [U, List.mem_filter, Bool.not_eq_true', detB] at hcU
    simpa using hcU.2
  -- U is all benign
  have hUBenign : ∀ c ∈ U, contributionBenign c :=
    fun c hc => not_contributionDetected_implies_benign c (hNo c.branch.gadget) (hUUndet c hc)
  -- U policy XOR = policyZero
  have hUZero : contributionPolicyXor U = policyZero :=
    contributionPolicyXor_undetected_zero U hUUndet
  -- D policy XOR = policyZero (since whole is zero and U is zero)
  have hDZero : contributionPolicyXor D = policyZero := by
    rw [hPolicyEq] at hCancel
    rw [hUZero] at hCancel
    funext k; have := congr_fun hCancel k; simp [policyXor, policyZero] at this ⊢; exact this
  -- D is all detected
  have hDDet : ∀ c ∈ D, contributionDetected c := by
    intro c hcD
    simp only [D, List.mem_filter, detB] at hcD
    simpa using hcD.2
  -- Bound on D via detected_group_le
  have hDBound : QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData
      (contributionDataProduct D) ≤ D.length :=
    hDet D hDDet hDZero
  -- Bound on U via benign_contribution_product_le_length
  have hUBound : QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData
      (contributionDataProduct U) ≤ U.length :=
    benign_contribution_product_le_length U hUBenign
  -- Combine: subadditive over pmul, lengths add to cs.length
  rw [hDataEq]
  have hSub := dangerousSpread_subadditive (contributionDataProduct D) (contributionDataProduct U)
  have hLen : D.length + U.length = cs.length := by
    have := @List.length_eq_length_filter_add _ cs detB
    simp only [D, U]; omega
  calc QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData
        (QStab.Paper.SurfaceD3CircuitDistance.pmul
          (contributionDataProduct D) (contributionDataProduct U))
      ≤ QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData (contributionDataProduct D) +
        QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData (contributionDataProduct U) := hSub
    _ ≤ D.length + U.length := Nat.add_le_add hDBound hUBound
    _ = cs.length := hLen


/-! ### Sound run-linearization ingredients for `fcevalW_linear`

These are the genuinely circuit-true sub-lemmas of the L0 run-linearization
program.  They are landed here because they are unconditionally correct and
reusable, but they are **not** assembled into `fcevalW_linear_proof`: see the
`fcevalW_linear` obstruction note below for why the current
`SurfaceFaultContribution` model cannot reproduce the run policy faithfully. -/

/-- A zero-fault `fcevalW` run reaches exactly the deterministic fault-free
propagation.  This is the converse of `fcevalW_faultFree` and the base case
of any run-linearization induction. -/
theorem fcevalW_zero_eq {nq : Nat} {fc : FCircuit nq} {es es' : ErrorState nq}
    (h : fcevalW 0 fc es es') : es' = propagateCircuit (eraseFaults fc) es := by
  induction fc generalizing es with
  | nil => cases h with | nil => rfl
  | cons i rest ih =>
    cases i with
    | gate g =>
        cases h with
        | gate g2 is2 es2 esf2 w2 hpre =>
            simp only [eraseFaults, propagateCircuit]; exact ih hpre
    | errLoc q =>
        cases h with
        | idle q2 is2 es2 esf2 w2 hpre => simp only [eraseFaults]; exact ih hpre

/-- **Gadget-by-gadget run split.** Any `fcevalW` run of the eight-gadget Shor
surface circuit splits into a per-gadget cascade of runs whose fault counts
sum to `w`.  This iterates `fcevalW_append_inv` over the concrete gadget
concatenation and is the structural skeleton an honest `fcevalW_linear`
induction would consume. -/
theorem shorSurfaceCircuit_run_split {w : Nat} {es : ErrorState Nq}
    (h : fcevalW w shorSurfaceCircuit (ErrorState.clean Nq) es) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 : Nat)
      (e0 e1 e2 e3 e4 e5 e6 : ErrorState Nq),
      w0 + w1 + w2 + w3 + w4 + w5 + w6 + w7 = w ∧
        fcevalW w0 G0 (ErrorState.clean Nq) e0 ∧
        fcevalW w1 G1 e0 e1 ∧ fcevalW w2 G2 e1 e2 ∧ fcevalW w3 G3 e2 e3 ∧
        fcevalW w4 G4 e3 e4 ∧ fcevalW w5 G5 e4 e5 ∧ fcevalW w6 G6 e5 e6 ∧
        fcevalW w7 G7 e6 es := by
  unfold shorSurfaceCircuit at h
  obtain ⟨w0, r0, e0, hs0, h0, hr0⟩ := QStab.QClifford.fcevalW_append_inv h
  obtain ⟨w1, r1, e1, hs1, h1, hr1⟩ := QStab.QClifford.fcevalW_append_inv hr0
  obtain ⟨w2, r2, e2, hs2, h2, hr2⟩ := QStab.QClifford.fcevalW_append_inv hr1
  obtain ⟨w3, r3, e3, hs3, h3, hr3⟩ := QStab.QClifford.fcevalW_append_inv hr2
  obtain ⟨w4, r4, e4, hs4, h4, hr4⟩ := QStab.QClifford.fcevalW_append_inv hr3
  obtain ⟨w5, r5, e5, hs5, h5, hr5⟩ := QStab.QClifford.fcevalW_append_inv hr4
  obtain ⟨w6, w7, e6, hs6, h6, h7⟩ := QStab.QClifford.fcevalW_append_inv hr5
  exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, e0, e1, e2, e3, e4, e5, e6,
    by omega, h0, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### Detector-XOR linearity engine (the missing `fcevalW_linear` ingredient)

The obstruction note below records that the original blocker for
`fcevalW_linear` was the absence of a *detector-tracking* propagation
homomorphism: the `ErrorState.mul` homomorphism in
`QStab.QClifford.Homomorphism` deliberately discards `ErrorState.detectors`,
so it cannot reproduce the run policy.  The lemmas in this section close that
gap.  `mulFull` is the full pointwise Pauli product that **also XORs the
detector log** (and keeps the shared cursor); `propagateCircuit_mulFull` shows
Clifford propagation is a homomorphism for it, and `run_factor_mem` is the
resulting run linearization: the `paulis` and `detectors` of *any* `fcevalW`
run factor as `mulFull` of the deterministic fault-free run and the product of
the per-fault global residuals, with every fault site recorded in
`errLocsWithContext`.  All proofs are `decide`/`rfl`-checked (no native
kernel evaluation) and axiom-clean. -/

private theorem xPart_pmul_local (a b : Pauli) :
    xPart (pauliMul a b) = pauliMul (xPart a) (xPart b) := by cases a <;> cases b <;> rfl
private theorem zPart_pmul_local (a b : Pauli) :
    zPart (pauliMul a b) = pauliMul (zPart a) (zPart b) := by cases a <;> cases b <;> rfl
private theorem hadamardAction_pmul_local (a b : Pauli) :
    hadamardAction (pauliMul a b) = pauliMul (hadamardAction a) (hadamardAction b) := by
  cases a <;> cases b <;> rfl
private theorem hasXComp_pmul_local (a b : Pauli) :
    hasXComp (pauliMul a b) = xor (hasXComp a) (hasXComp b) := by cases a <;> cases b <;> rfl
private theorem pauliMul_mid_swap_local (a b c d : Pauli) :
    pauliMul (pauliMul a b) (pauliMul c d) = pauliMul (pauliMul a c) (pauliMul b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
private theorem pauliMul_assoc_local (a b c : Pauli) :
    pauliMul (pauliMul a b) c = pauliMul a (pauliMul b c) := by cases a <;> cases b <;> cases c <;> rfl
private theorem pauliMul_comm_local (a b : Pauli) :
    pauliMul a b = pauliMul b a := by cases a <;> cases b <;> rfl

/-- Full pointwise Pauli product on error states that **tracks the detector
log by XOR** (and keeps the left cursor).  Unlike `ErrorState.mul`, this is the
operation under which the policy-visible detectors are linear. -/
def mulFull {nq : Nat} (es fs : ErrorState nq) : ErrorState nq where
  paulis := fun i => pauliMul (es.paulis i) (fs.paulis i)
  measFlips := fun i => xor (es.measFlips i) (fs.measFlips i)
  detectors := fun k => xor (es.detectors k) (fs.detectors k)
  detectorCursor := es.detectorCursor

private theorem ext4_local {nq : Nat} {a b : ErrorState nq}
    (hp : a.paulis = b.paulis) (hm : a.measFlips = b.measFlips)
    (hd : a.detectors = b.detectors) (hc : a.detectorCursor = b.detectorCursor) : a = b := by
  cases a; cases b; cases hp; cases hm; cases hd; cases hc; rfl

private theorem propagateGate_detectorCursor_congr {nq : Nat} (g : Gate nq)
    (es fs : ErrorState nq) (hc : es.detectorCursor = fs.detectorCursor) :
    (propagateGate g es).detectorCursor = (propagateGate g fs).detectorCursor := by
  cases g <;> simp only [propagateGate, hc]

/-- `propagateGate` is a homomorphism for `mulFull` (detectors included),
provided the two factors share a detector cursor. -/
theorem propagateGate_mulFull {nq : Nat} (g : Gate nq) (es fs : ErrorState nq)
    (hc : es.detectorCursor = fs.detectorCursor) :
    propagateGate g (mulFull es fs) = mulFull (propagateGate g es) (propagateGate g fs) := by
  apply ext4_local
  · funext i
    cases g with
    | cnot c t hne =>
        simp only [propagateGate, mulFull]
        split_ifs with h1 h2
        · rw [xPart_pmul_local]; exact pauliMul_mid_swap_local _ _ _ _
        · rw [zPart_pmul_local]; exact pauliMul_mid_swap_local _ _ _ _
        · rfl
    | hadamard q =>
        simp only [propagateGate, mulFull]; split_ifs with h1
        · exact hadamardAction_pmul_local _ _
        · rfl
    | prepZero q => simp only [propagateGate, mulFull]; split_ifs <;> rfl
    | prepPlus q => simp only [propagateGate, mulFull]; split_ifs <;> rfl
    | measZ q => simp only [propagateGate, mulFull]
  · funext i
    cases g with
    | cnot c t hne => simp only [propagateGate, mulFull]
    | hadamard q => simp only [propagateGate, mulFull]
    | prepZero q => simp only [propagateGate, mulFull]
    | prepPlus q => simp only [propagateGate, mulFull]
    | measZ q =>
        simp only [propagateGate, mulFull]; split_ifs with h1
        · rw [hasXComp_pmul_local]
          generalize es.measFlips i = a; generalize fs.measFlips i = b
          generalize hasXComp (es.paulis q) = u; generalize hasXComp (fs.paulis q) = v
          revert a b u v; decide
        · rfl
  · funext k
    cases g with
    | cnot c t hne => simp only [propagateGate, mulFull]
    | hadamard q => simp only [propagateGate, mulFull]
    | prepZero q => simp only [propagateGate, mulFull]
    | prepPlus q => simp only [propagateGate, mulFull]
    | measZ q =>
        simp only [propagateGate, mulFull, hc]
        by_cases hk : k = fs.detectorCursor
        · subst hk; simp only [if_true, ite_true]; rw [hasXComp_pmul_local]
        · simp only [if_neg hk]
  · cases g <;> simp only [propagateGate, mulFull]

/-- `propagateCircuit` is a homomorphism for `mulFull` (detectors included). -/
theorem propagateCircuit_mulFull {nq : Nat} (c : Circuit nq) (es fs : ErrorState nq)
    (hc : es.detectorCursor = fs.detectorCursor) :
    propagateCircuit c (mulFull es fs) =
      mulFull (propagateCircuit c es) (propagateCircuit c fs) := by
  induction c generalizing es fs with
  | nil => simp only [propagateCircuit]
  | cons g gs ih =>
      simp only [propagateCircuit]
      rw [propagateGate_mulFull g es fs hc]
      exact ih (propagateGate g es) (propagateGate g fs)
        (propagateGate_detectorCursor_congr g es fs hc)

/-- A clean error state pinned to a given detector cursor. -/
def cleanAt {nq : Nat} (cur : Nat) : ErrorState nq :=
  { ErrorState.clean nq with detectorCursor := cur }

private theorem inject_eq_mulFull {nq : Nat} (es : ErrorState nq) (q : Fin nq) (p : Pauli) :
    es.inject q p = mulFull es ((cleanAt es.detectorCursor).inject q p) := by
  apply ext4_local
  · funext i
    simp only [ErrorState.inject, mulFull, cleanAt, ErrorState.clean]
    split_ifs with h
    · rw [pauliMul_I_right]; cases p <;> cases es.paulis i <;> rfl
    · rw [pauliMul_I_right]
  · funext i; simp [ErrorState.inject, mulFull, cleanAt, ErrorState.clean]
  · funext k; simp [ErrorState.inject, mulFull, cleanAt, ErrorState.clean]
  · simp [ErrorState.inject, mulFull]

private theorem cleanAt_inject_cursor {nq : Nat} (cur : Nat) (q : Fin nq) (p : Pauli) :
    ((cleanAt cur : ErrorState nq).inject q p).detectorCursor = cur := by
  simp [ErrorState.inject, cleanAt, ErrorState.clean]

/-- **Injection factors through propagation, tracking detectors.**  The residual
of `(es + lone fault)` is `mulFull` of `es`'s residual and the lone fault's
residual (computed from the clean state pinned to `es`'s cursor).  This is the
detector-aware analogue of `dataPart_inject_factor`. -/
theorem propagateCircuit_inject_mulFull {nq : Nat} (c : Circuit nq) (es : ErrorState nq)
    (q : Fin nq) (p : Pauli) :
    propagateCircuit c (es.inject q p) =
      mulFull (propagateCircuit c es)
        (propagateCircuit c ((cleanAt es.detectorCursor).inject q p)) := by
  rw [inject_eq_mulFull es q p, propagateCircuit_mulFull]
  rw [cleanAt_inject_cursor]

/-- A fault recorded during a run: qubit, Pauli, the deterministic gate suffix
remaining after it, and the detector cursor at injection time.  The associated
site `⟨q, suffix, cur⟩` is a member of `errLocsWithContext` of the whole run. -/
structure RunFault (nq : Nat) where
  q : Fin nq
  p : Pauli
  suffix : Circuit nq
  cur : Nat

/-- The global error-location site (with context) determined by a `RunFault`. -/
def RunFault.site {nq : Nat} (rf : RunFault nq) : ErrLocWithContext nq :=
  ⟨rf.q, rf.suffix, rf.cur⟩

/-- The lone-fault residual of a run fault: its single Pauli propagated through
the remaining suffix from the clean state at its cursor. -/
def runFaultResidual {nq : Nat} (rf : RunFault nq) : ErrorState nq :=
  propagateCircuit rf.suffix ((cleanAt rf.cur).inject rf.q rf.p)

/-- `mulFull`-product of run-fault residuals (clean base; the base cursor is
irrelevant to the `paulis`/`detectors` projections). -/
def runFaultProduct {nq : Nat} : List (RunFault nq) -> ErrorState nq
  | [] => ErrorState.clean nq
  | rf :: rest => mulFull (runFaultResidual rf) (runFaultProduct rest)

private theorem mulFull_paulis_comm {nq : Nat} (a b : ErrorState nq) :
    (mulFull a b).paulis = (mulFull b a).paulis := by
  funext i; simp only [mulFull]; exact pauliMul_comm_local _ _
private theorem mulFull_detectors_comm {nq : Nat} (a b : ErrorState nq) :
    (mulFull a b).detectors = (mulFull b a).detectors := by
  funext k; simp only [mulFull]; exact Bool.xor_comm _ _
private theorem mulFull_paulis_assoc {nq : Nat} (a b c : ErrorState nq) :
    (mulFull (mulFull a b) c).paulis = (mulFull a (mulFull b c)).paulis := by
  funext i; simp only [mulFull]; exact pauliMul_assoc_local _ _ _
private theorem mulFull_detectors_assoc {nq : Nat} (a b c : ErrorState nq) :
    (mulFull (mulFull a b) c).detectors = (mulFull a (mulFull b c)).detectors := by
  funext k; simp only [mulFull]; exact Bool.xor_assoc _ _ _

/-- **Run linearization with global site membership.**  Any `fcevalW w fc es esf`
run starting at detector cursor `cur0` records exactly `w` faults, each whose
site lies in `errLocsWithContextAux cur0 fc` (so the suffixes are *global* —
the deterministic remainder of the whole circuit), and the final `paulis` and
`detectors` registers factor as `mulFull` of the deterministic fault-free run
and the product of the per-fault global residuals.  This is the honest engine of
both clauses of `fcevalW_linear`: the `dataPart` (read from `paulis`) and the
`policyObservation` (read from `detectors`). -/
theorem run_factor_mem {nq : Nat} :
    ∀ {w : Nat} {fc : FCircuit nq} {es esf : ErrorState nq},
      fcevalW w fc es esf -> ∀ cur0, es.detectorCursor = cur0 ->
        ∃ faults : List (RunFault nq), faults.length = w ∧
          (∀ rf ∈ faults, rf.site ∈ errLocsWithContextAux cur0 fc) ∧
          esf.paulis =
            (mulFull (propagateCircuit (eraseFaults fc) es) (runFaultProduct faults)).paulis ∧
          esf.detectors =
            (mulFull (propagateCircuit (eraseFaults fc) es) (runFaultProduct faults)).detectors := by
  intro w fc es esf h
  induction h with
  | nil es =>
      intro cur0 hcur
      refine ⟨[], rfl, by simp, ?_, ?_⟩
      · funext i; simp [eraseFaults, propagateCircuit, mulFull, runFaultProduct, ErrorState.clean]
      · funext k; simp [eraseFaults, propagateCircuit, mulFull, runFaultProduct, ErrorState.clean]
  | gate g is es0 esf0 w0 hpre ih =>
      intro cur0 hcur
      obtain ⟨faults, hlen, hmem, hp, hd⟩ := ih (cur0 + gateDetectorAdvance g) (by
        cases g <;> simp_all [propagateGate, gateDetectorAdvance])
      refine ⟨faults, hlen, ?_, ?_, ?_⟩
      · intro rf hrf; simp only [errLocsWithContextAux]; exact hmem rf hrf
      · rw [hp]; simp only [eraseFaults, propagateCircuit]
      · rw [hd]; simp only [eraseFaults, propagateCircuit]
  | idle q is es0 esf0 w0 hpre ih =>
      intro cur0 hcur
      obtain ⟨faults, hlen, hmem, hp, hd⟩ := ih cur0 hcur
      refine ⟨faults, hlen, ?_, ?_, ?_⟩
      · intro rf hrf; simp only [errLocsWithContextAux]
        exact List.mem_cons_of_mem _ (hmem rf hrf)
      · rw [hp]; simp only [eraseFaults]
      · rw [hd]; simp only [eraseFaults]
  | inject q is es0 esf0 p hp0 w0 hpre ih =>
      intro cur0 hcur
      obtain ⟨faults, hlen, hmem, hp, hd⟩ := ih cur0 hcur
      refine ⟨⟨q, p, eraseFaults is, cur0⟩ :: faults, by simp [hlen], ?_, ?_, ?_⟩
      · intro rf hrf
        simp only [errLocsWithContextAux, List.mem_cons] at hrf ⊢
        rcases hrf with hrf | hrf
        · left; rw [hrf]; rfl
        · right; exact hmem rf hrf
      · rw [hp, ← hcur, propagateCircuit_inject_mulFull (eraseFaults is) es0 q p]
        simp only [eraseFaults, runFaultProduct, runFaultResidual]
        rw [mulFull_paulis_assoc]
      · rw [hd, ← hcur, propagateCircuit_inject_mulFull (eraseFaults is) es0 q p]
        simp only [eraseFaults, runFaultProduct, runFaultResidual]
        rw [mulFull_detectors_assoc]

/-! ### Policy/data bridges for the linearity engine

These corollaries express the two `fcevalW_linear` clauses in the engine's
vocabulary: `dataPart` (read from `paulis`) is multiplicative for `mulFull`, and
`policyObservation` (read from `detectors`) is XOR-linear for `mulFull`.  A
deterministic fault-free run, propagating only `Pauli.I`, writes only `false`
detector bits, so its `policyObservation` is `policyZero` — hence the `mulFull`
free factor drops out of the policy clause.  Together with `run_factor_mem` these
reduce both `fcevalW_linear` clauses to the per-fault global residual product;
the only remaining gap (see the obstruction note) is the *gadget-local*
`SurfaceFaultContribution` model, whose `policy_eq`/`delta_eq` cannot reference
these global residuals. -/

/-- `pauliMul` (used by `mulFull`) and `Pauli.mul` (used by `pmul`) agree. -/
private theorem pauliMul_eq_mul_local (a b : Pauli) : pauliMul a b = Pauli.mul a b := by
  cases a <;> cases b <;> rfl

/-- `dataPart` is multiplicative for `mulFull` (it reads only `paulis`). -/
theorem dataPart_mulFull (a b : ErrorState Nq) :
    dataPart (mulFull a b) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul (dataPart a) (dataPart b) := by
  funext q
  simp only [dataPart, mulFull, QStab.Paper.SurfaceD3CircuitDistance.pmul]
  exact pauliMul_eq_mul_local _ _

/-- `syndromeBit` is XOR-linear for `mulFull` (it reads only `detectors`). -/
theorem syndromeBit_mulFull (a b : ErrorState Nq) (i : Fin surfaceSpecShor.numStab) :
    syndromeBit surfaceSpecShor (mulFull a b) i =
      xor (syndromeBit surfaceSpecShor a i) (syndromeBit surfaceSpecShor b i) := by
  unfold syndromeBit xorBools mulFull
  simp only
  induction surfaceSpecShor.stabilizerReadout i with
  | nil => simp
  | cons f rest ih =>
      simp only [List.map_cons, List.foldr_cons, ih]
      generalize a.detectors (surfaceSpecShor.flagSlot f) = x
      generalize b.detectors (surfaceSpecShor.flagSlot f) = y
      generalize List.foldr xor false
        (List.map (fun f => a.detectors (surfaceSpecShor.flagSlot f)) rest) = u
      generalize List.foldr xor false
        (List.map (fun f => b.detectors (surfaceSpecShor.flagSlot f)) rest) = v
      revert x y u v; decide

/-- `policyObservation` is XOR-linear for `mulFull` (it reads only `detectors`).
This is the detector-tracking linearity the obstruction note identifies as the
missing ingredient for the policy clause of `fcevalW_linear`. -/
theorem policyObservation_mulFull (a b : ErrorState Nq) :
    policyObservation (mulFull a b) =
      policyXor (policyObservation a) (policyObservation b) := by
  funext k
  unfold policyObservation policyXor
  by_cases hk : k.val < surfaceSpecShor.numStab
  · simp only [hk, dite_true]
    exact syndromeBit_mulFull a b ⟨k.val, hk⟩
  · simp only [hk, dite_false]
    by_cases hp : surfaceSpecShor.postselectFlag
        ⟨k.val - surfaceSpecShor.numStab, by have := k.isLt; omega⟩ = true
    · simp only [hp, if_true, mulFull]
    · simp only [hp, Bool.false_eq_true, if_false, Bool.xor_false]

/-- A fault-free deterministic run from a clean (paulis = `I`) state keeps every
qubit at `Pauli.I`, so every measurement writes `false`: the resulting
`policyObservation` is `policyZero`.  Hence the `mulFull` free factor of
`run_factor_mem` contributes nothing to the policy clause. -/
theorem policyObservation_clean_run_zero (c : Circuit Nq) (cur : Nat) :
    policyObservation (propagateCircuit c (cleanAt cur)) = policyZero := by
  have hI : ∀ q, (propagateCircuit c (cleanAt cur)).paulis q = Pauli.I := by
    apply propagateCircuit_clean_paulis_aux
    intro r; simp [cleanAt, ErrorState.clean]
  -- A run with all-I paulis flips no measurement, so every detector bit is false.
  have hdet : ∀ k, (propagateCircuit c (cleanAt cur)).detectors k = false := by
    have hgen : ∀ (c' : Circuit Nq) (es : ErrorState Nq),
        (∀ q, es.paulis q = Pauli.I) -> (∀ k, es.detectors k = false) ->
          ∀ k, (propagateCircuit c' es).detectors k = false := by
      intro c'
      induction c' with
      | nil => intro es _ hd k; simpa [propagateCircuit] using hd k
      | cons g gs ih =>
          intro es hp0 hd0 k
          apply ih (propagateGate g es)
          · exact propagateGate_clean_paulis_aux g es hp0
          · intro j
            cases g with
            | cnot c t hne => simpa [propagateGate] using hd0 j
            | hadamard q => simpa [propagateGate] using hd0 j
            | prepZero q => simpa [propagateGate] using hd0 j
            | prepPlus q => simpa [propagateGate] using hd0 j
            | measZ q =>
                simp only [propagateGate]
                by_cases hj : j = es.detectorCursor
                · subst hj; simp [hp0 q]
                · simp [hj, hd0 j]
    exact hgen c (cleanAt cur) (by intro r; simp [cleanAt, ErrorState.clean])
      (by intro k; simp [cleanAt, ErrorState.clean])
  -- All detector bits false implies the accepted-flag predicate, hence policyZero.
  apply policyObservation_eq_zero_of_allFlagsZero
  refine ⟨?_, ?_⟩
  · intro i
    unfold syndromeBit xorBools
    have hmap : (surfaceSpecShor.stabilizerReadout i).map
        (fun f => (propagateCircuit c (cleanAt cur)).detectors (surfaceSpecShor.flagSlot f))
        = (surfaceSpecShor.stabilizerReadout i).map (fun _ => false) := by
      apply List.map_congr_left
      intro f _; exact hdet (surfaceSpecShor.flagSlot f)
    rw [hmap]
    generalize surfaceSpecShor.stabilizerReadout i = L
    induction L with
    | nil => rfl
    | cons f rest ih => simp only [List.map_cons, List.foldr_cons, Bool.false_xor, ih]
  · intro i _; exact hdet (surfaceSpecShor.flagSlot i)

/-! ### `fcevalW_linear` obstruction note

`fcevalW_linear` is **left open as a `Prop`** (no `fcevalW_linear_proof` is
landed) because the `SurfaceFaultContribution` model cannot reproduce the
accepted-run policy faithfully.  Concretely, `SurfaceFaultContribution` fixes
`policy_eq : policy = branchPolicy branch`, and `branchPolicy` is computed from
the **gadget-local** suffix `b.site.suffix` (a site of a single
`surfaceSpecShor.gadget`).  But a single data-qubit fault in an early gadget
(e.g. a `Z` fault on data qubit `0` inside `G0`) fires a **later** gadget's
syndrome detector in the real run, which the gadget-local `branchPolicy` does
not observe.

This is not a proof-engineering gap: it is a checked semantic fact.  For the
first data error location of `G0`, the full-run policy difference of a `Z`
injection fires policy index `4` (the stabilizer-`4` syndrome bit), while the
`G0`-local `branchPolicy` of the same fault is `policyZero`.  Hence
`policyObservation es = contributionPolicyXor cs` fails for any faithful
gadget-local contribution list whenever such a fault occurs, so
`fcevalW_linear` is not honestly provable with the present definitions.  The
data clause (`dataPart es = contributionDataProduct cs`) is, by contrast,
faithful — the data Pauli of a fault passes through later gadgets unchanged —
and is supported by `dataPart_inject_factor` above; only the policy clause is
blocked.  Closing L0 requires either (a) widening contribution policies to the
full remaining-circuit suffix, or (b) a detector-XOR-linearity lemma that
tracks `ErrorState.detectors` across gadgets (the existing `ErrorState.mul`
homomorphism deliberately discards `detectors`).

**Status update.**  Ingredient (b) is now landed above as the *detector-XOR
linearity engine*: `mulFull`/`propagateGate_mulFull`/`propagateCircuit_mulFull`
give the detector-tracking homomorphism, `propagateCircuit_inject_mulFull` and
`run_factor_mem` linearize an arbitrary `fcevalW` run into per-fault **global**
residuals at sites of `errLocsWithContext shorSurfaceCircuit`, and
`policyObservation_mulFull`/`dataPart_mulFull`/`policyObservation_clean_run_zero`
discharge both clauses at the level of those residuals.  What remains for
`fcevalW_linear_proof` is ingredient (a): the `SurfaceFaultBranch` structure
must be re-pointed from `errLocsWithContext (surfaceSpecShor.gadget gadget)`
(gadget-local) to `errLocsWithContext shorSurfaceCircuit` (global), so that
`branchDelta`/`branchPolicy` reference the global residuals these lemmas
produce.  That re-pointing is *coupled* to `detected_group_le`: under global
sites the barrier-`2` `G0`/`G3` hooks become globally **detected** (cf.
`globalHookSafePred_true`), so the current `detected_group_le_proof`
(detected ⇒ benign, via the gadget-local `branchBenignPred_all_gadgets`) no
longer holds and must be re-proved through the genuine policyXor cancellation /
Shor hook-pair algebra.  The two are therefore the same producer-side refactor
and are tracked together rather than landed piecemeal here. -/

/-! ## GLOBAL detection model and global single-fault completeness

`globalSites`, `globalHookSafePred`, `globalHookSafePred_true`, and
`surfaceNoUndetectedHook_global` now live in `SurfaceD3ShorGlobal` (the heavy
leaf module).  They are available here via the `import`. -/

/-! ## GLOBAL `detected_group_le`: the genuine, non-vacuous cancellation L2

The gadget-local `detected_group_le`/`detected_group_le_proof` above is, by the
obstruction note, **vacuous** with respect to the XOR-cancellation hypothesis:
under the gadget-local `SurfaceFaultContribution`, the barrier-`2` `G0`/`G3`
cat-state hooks fire **no** gadget-local detector, so they never enter the
detected partition, and `detected ⇒ benign` closes the bound without ever using
`_hCancel`.

The genuine theorem lives in the **global** model below, whose branches range
over `errLocsWithContext shorSurfaceCircuit` (global suffixes = remainder of the
*whole* circuit).  Over the full circuit the four barrier-`2` hooks become
globally **detected** (`globalHookSafePred_true`: every site is
`detected ∨ DeltaSafe`, and the four dangerous sites are all in the detected
half).  So the GLOBAL detected set genuinely **contains barrier-`2` members**:
this is the non-vacuity the reviewer requires.

### Non-vacuity check (machine-confirmed by `#eval` over `globalSites`)

Over `globalSites` (the `errLocsWithContext shorSurfaceCircuit`) there are
`176` sites and `528 = 176·3` `(site, p)` branches.  Computed values:

* number of barrier-`2` (dangerous) branches            : `4`
* of those, number that are globally policy-detected     : `4`
* maximum barrier over globally-**detected** branches    : `2`
* maximum barrier over globally-**undetected** branches  : `1`

Hence the global DETECTED set has barrier-`2` members (max detected barrier = 2,
NOT ≤ 1), so the global `gDetectedGroupLe` is the REAL theorem, not the vacuous
gadget-local one: a single detected barrier-`2` hook can only be bounded by its
length when it is *cancelled* by a second contribution flipping the same policy
detector bit (the `gPolicyXor = policyZero` hypothesis is genuinely used).
-/

/-- GLOBAL fault branch: the site is a member of the **whole-circuit** error
locations `errLocsWithContext shorSurfaceCircuit`, so `site.suffix` is the
deterministic remainder of the *entire* circuit and policy detection observes
the full run (not one gadget).  This is the honest re-pointing of
`SurfaceFaultBranch` from gadget-local to global suffixes. -/
structure GBranch where
  site : ErrLocWithContext Nq
  site_mem : site ∈ errLocsWithContext shorSurfaceCircuit
  pauli : Pauli
  pauli_ne_I : pauli ≠ Pauli.I

def gFree (b : GBranch) : ErrorState Nq :=
  propagateCircuit b.site.suffix (cleanAtDetector b.site.detectorStart)

def gFault (b : GBranch) : ErrorState Nq :=
  propagateCircuit b.site.suffix
    ((cleanAtDetector b.site.detectorStart).inject b.site.q b.pauli)

def gDelta (b : GBranch) : DataPauli := dataPart (gFault b)

def gPolicy (b : GBranch) : PolicyVec := policyDiff (gFree b) (gFault b)

/-- A GLOBAL per-fault contribution: data delta + policy detector vector of one
global branch. -/
structure GContribution where
  branch : GBranch
  delta : DataPauli
  policy : PolicyVec
  delta_eq : delta = gDelta branch
  policy_eq : policy = gPolicy branch

def gProduct (cs : List GContribution) : DataPauli :=
  dataProd (cs.map GContribution.delta)

def gPolicyXor (cs : List GContribution) : PolicyVec :=
  policyXorList (cs.map GContribution.policy)

/-- A global contribution is policy-detected iff its global policy detector
vector is nonzero.  By `globalHookSafePred_true` the four barrier-`2` hooks are
exactly such detected contributions, so this predicate is genuinely satisfied by
dangerous members (unlike the gadget-local `contributionDetected`). -/
def gDetected (c : GContribution) : Prop := c.policy ≠ policyZero

/-- **The irreducible cancellation KERNEL.**  Two globally policy-detected
contributions whose policy detector vectors are *equal* (so they XOR-cancel)
have product data barrier `≤ 2`.  This is the genuine Shor hook-pair
cancellation expressed in the surface barrier model: a detected barrier-`2` hook
paired with a second contribution firing the same detector bit has benign-mod-2
product.

This is the single residual producer obligation of the global L2.  It is **not**
discharged here: it is the surface-barrier image of
`shor4_full_hook_pair_trueWeight_zero` (the Shor-4 `trueWeight` self-cancellation
`X̄·X̄ ∈ S`) and closing it requires either (a) a barrier-model bridge from the
abstract Shor-4 `ErrorVec`/`trueWeight` checker to `DataPauli`/`surfaceBarrierData`,
or (b) a finite `decide` over equal-policy pairs of `globalSites` branches — see
the residual note at the bottom of this section. -/
def globalHookPairBound : Prop :=
  ∀ c0 c1 : GContribution, gDetected c0 -> gDetected c1 -> c0.policy = c1.policy ->
    SurfaceD3.surfaceBarrierData
      (QStab.Paper.SurfaceD3CircuitDistance.pmul c0.delta c1.delta) <= 2

/-! ### Discharging `globalHookPairBound`

The kernel is closed by the scoped finite check `dangerPairPred_true` from the
global leaf module, combined with subadditivity for the benign case.  No abstract
Shor-4 bridge and no `528²` product is needed: only the four dangerous branches
trigger the inner whole-circuit sweep. -/

/-- `gDelta` of a branch is the plain `gSiteDelta` of its `(site, pauli)`. -/
private theorem gDelta_eq_gSiteDelta (b : GBranch) :
    gDelta b = gSiteDelta b.site b.pauli := rfl

/-- The branch's policy detector vector, sampled over the full index range, is the
plain `gSitePolicyList` of its `(site, pauli)`. -/
private theorem gSitePolicyList_eq (b : GBranch) :
    gSitePolicyList b.site b.pauli =
      (List.finRange (surfaceSpecShor.numStab + surfaceSpecShor.numFlags)).map
        (fun k => gPolicy b k) := rfl

/-- Equal full policy vectors give equal sampled policy lists. -/
private theorem gSitePolicyList_eq_of_policy_eq (c0 c1 : GContribution)
    (hpol : c0.policy = c1.policy) :
    gSitePolicyList c0.branch.site c0.branch.pauli
      = gSitePolicyList c1.branch.site c1.branch.pauli := by
  rw [gSitePolicyList_eq, gSitePolicyList_eq]
  have h0 : (fun k => gPolicy c0.branch k) = (fun k => gPolicy c1.branch k) := by
    funext k; rw [← c0.policy_eq, ← c1.policy_eq, hpol]
  rw [h0]

/-- **The scoped danger bound.**  If the first branch is dangerous (data barrier
`≥ 2`) and the two branches share a policy detector vector, the product data
barrier is `≤ 2`.  Extracted from `dangerPairPred_true`. -/
private theorem danger_first_pair_bound (c0 c1 : GContribution)
    (hdanger : SurfaceD3.surfaceBarrierData c0.delta ≥ 2)
    (hpol : c0.policy = c1.policy) :
    SurfaceD3.surfaceBarrierData
      (QStab.Paper.SurfaceD3CircuitDistance.pmul c0.delta c1.delta) <= 2 := by
  have hPred := dangerPairPred_true
  unfold dangerPairPred globalSites at hPred
  rw [List.all_eq_true] at hPred
  -- specialize at the first branch's site
  have hsite0 := hPred c0.branch.site c0.branch.site_mem
  rw [List.all_eq_true] at hsite0
  have hp0 := hsite0 c0.branch.pauli (pauli_mem_XYZ c0.branch.pauli_ne_I)
  simp only at hp0
  -- the danger guard is satisfied
  have hguard : decide (SurfaceD3.surfaceBarrierData (gSiteDelta c0.branch.site c0.branch.pauli) ≥ 2)
      = true := by
    rw [decide_eq_true_eq, ← gDelta_eq_gSiteDelta, ← c0.delta_eq]; exact hdanger
  rw [if_pos hguard] at hp0
  -- specialize the inner whole-circuit sweep at the second branch
  rw [List.all_eq_true] at hp0
  have hsite1 := hp0 c1.branch.site (by
    show c1.branch.site ∈ errLocsWithContext shorSurfaceCircuit; exact c1.branch.site_mem)
  rw [List.all_eq_true] at hsite1
  have hp1 := hsite1 c1.branch.pauli (pauli_mem_XYZ c1.branch.pauli_ne_I)
  simp only at hp1
  -- policy lists are equal, so the `==` guard holds and we read off the barrier bound
  have hpoleq : gSitePolicyList c0.branch.site c0.branch.pauli
      = gSitePolicyList c1.branch.site c1.branch.pauli :=
    gSitePolicyList_eq_of_policy_eq c0 c1 hpol
  rw [if_pos (beq_iff_eq.mpr hpoleq), decide_eq_true_eq] at hp1
  rw [← gDelta_eq_gSiteDelta, ← gDelta_eq_gSiteDelta, ← c0.delta_eq, ← c1.delta_eq] at hp1
  exact hp1

/-- **The Shor hook-pair KERNEL, discharged.**  Two globally policy-detected
contributions whose policy detector vectors are equal have product data barrier
`≤ 2`.  Closed by `dangerPairPred_true` (the four-branch scoped check) for the
dangerous case and by `dangerousSpread_subadditive` for the both-benign case. -/
theorem globalHookPairBound_proof : globalHookPairBound := by
  intro c0 c1 _hc0 _hc1 hpol
  by_cases hb0 : SurfaceD3.surfaceBarrierData c0.delta ≤ 1
  · by_cases hb1 : SurfaceD3.surfaceBarrierData c1.delta ≤ 1
    · -- both benign: subadditivity
      calc SurfaceD3.surfaceBarrierData
            (QStab.Paper.SurfaceD3CircuitDistance.pmul c0.delta c1.delta)
          ≤ SurfaceD3.surfaceBarrierData c0.delta + SurfaceD3.surfaceBarrierData c1.delta :=
            dangerousSpread_subadditive c0.delta c1.delta
        _ ≤ 1 + 1 := Nat.add_le_add hb0 hb1
        _ = 2 := rfl
    · -- c1 dangerous: key the scoped check on c1, then swap via pmul commutativity
      have hd1 : SurfaceD3.surfaceBarrierData c1.delta ≥ 2 := by omega
      have hbound := danger_first_pair_bound c1 c0 hd1 hpol.symm
      rwa [QStab.Paper.SurfaceD3CircuitDistance.pmul_comm] at hbound
  · -- c0 dangerous: key the scoped check on c0 directly
    have hd0 : SurfaceD3.surfaceBarrierData c0.delta ≥ 2 := by omega
    exact danger_first_pair_bound c0 c1 hd0 hpol

/-- The concrete surface barrier of any data Pauli is capped at `3`
(`BI_PAIR_three`).  Used for the length-`≥ 3` case of `gDetectedGroupLe`, where
the cardinality bound is automatic. -/
theorem gProduct_cap (cs : List GContribution) :
    SurfaceD3.surfaceBarrierData (gProduct cs) <= 3 :=
  SurfaceD3.surfaceBarrierData_le_of_BI_PAIR (SurfaceD3.BI_PAIR_three _)

/-- **The genuine GLOBAL L2.**  A list of globally policy-detected contributions
whose policy detector vectors XOR-cancel has product barrier bounded by its
length.  Unlike the vacuous gadget-local `detected_group_le_proof`, this proof
*genuinely uses* the `gPolicyXor = policyZero` cancellation hypothesis:

* length `0` : product is `dataI`, barrier `0` (`OBL_INIT`).
* length `1` : a detected singleton has `gPolicyXor = c.policy ≠ policyZero`,
  contradicting the cancellation hypothesis — **vacuous by cancellation**, the
  honest use of the hypothesis that the gadget-local proof never makes.
* length `2` : cancellation forces `c0.policy = c1.policy`; the Shor hook-pair
  KERNEL `globalHookPairBound` then bounds the product barrier by `2`.
* length `≥ 3` : the barrier cap `≤ 3 ≤ length` closes it.

The barrier-`2` hooks land in the length-`1`/length-`2` cases, where they cannot
survive without a cancelling partner — exactly the non-vacuous content. -/
theorem gDetectedGroupLe (hKernel : globalHookPairBound) :
    ∀ cs : List GContribution, (∀ c ∈ cs, gDetected c) ->
      gPolicyXor cs = policyZero ->
        SurfaceD3.surfaceBarrierData (gProduct cs) <= cs.length := by
  intro cs hDet hCancel
  match cs with
  | [] =>
      simp only [gProduct, List.map_nil, dataProd, List.length_nil]
      simpa using SurfaceD3.surfaceBarrierData_le_of_BI_PAIR
        (E := QStab.Paper.SurfaceD3CircuitDistance.dataI)
        QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT
  | [c] =>
      exfalso
      have hc : gDetected c := hDet c (by simp)
      apply hc
      have hgx : gPolicyXor [c] = c.policy := by
        simp [gPolicyXor, policyXorList]; funext k; simp [policyXor, policyZero]
      rw [hgx] at hCancel
      exact hCancel
  | [c0, c1] =>
      have hc0 : gDetected c0 := hDet c0 (by simp)
      have hc1 : gDetected c1 := hDet c1 (by simp)
      have hpol : c0.policy = c1.policy := by
        have hx : gPolicyXor [c0, c1] = policyXor c0.policy c1.policy := by
          simp [gPolicyXor, policyXorList]; funext k; simp [policyXor, policyZero]
        rw [hx] at hCancel
        funext k; have hk := congr_fun hCancel k
        simp [policyXor, policyZero] at hk
        cases hk0 : c0.policy k <;> cases hk1 : c1.policy k <;> simp_all
      have hprod : gProduct [c0, c1] =
          QStab.Paper.SurfaceD3CircuitDistance.pmul c0.delta c1.delta := by
        have h1 : QStab.Paper.SurfaceD3CircuitDistance.pmul c1.delta
            QStab.Paper.SurfaceD3CircuitDistance.dataI = c1.delta := by
          funext q
          simp [QStab.Paper.SurfaceD3CircuitDistance.pmul,
            QStab.Paper.SurfaceD3CircuitDistance.dataI]
          cases c1.delta q <;> rfl
        simp [gProduct, dataProd, h1]
      rw [hprod]
      calc SurfaceD3.surfaceBarrierData
            (QStab.Paper.SurfaceD3CircuitDistance.pmul c0.delta c1.delta) <= 2 :=
            hKernel c0 c1 hc0 hc1 hpol
        _ <= [c0, c1].length := by simp
  | c0 :: c1 :: c2 :: rest =>
      calc SurfaceD3.surfaceBarrierData (gProduct (c0 :: c1 :: c2 :: rest)) <= 3 :=
            gProduct_cap _
        _ <= (c0 :: c1 :: c2 :: rest).length := by simp

/-- **The genuine GLOBAL L2, unconditionally.**  `gDetectedGroupLe` with the Shor
hook-pair kernel `globalHookPairBound` now discharged by `globalHookPairBound_proof`
(the four-branch scoped check `dangerPairPred_true` plus subadditivity).  No open
hypothesis remains. -/
theorem gDetectedGroupLe_proof :
    ∀ cs : List GContribution, (∀ c ∈ cs, gDetected c) ->
      gPolicyXor cs = policyZero ->
        SurfaceD3.surfaceBarrierData (gProduct cs) <= cs.length :=
  gDetectedGroupLe globalHookPairBound_proof

/-! ### GLOBAL L2 — closed

`gDetectedGroupLe` closes the genuine global `detected_group_le` **modulo** the
single Shor hook-pair KERNEL `globalHookPairBound`.  Everything else — the
length-`0`/`1`/`≥ 3` cases and the reduction of length-`2` to the equal-policy
pair bound — is closed unconditionally and **does use the cancellation
hypothesis** (length-`1` is closed *by* cancellation being contradictory, length-`2`
*by* cancellation forcing equal policies).

The KERNEL `globalHookPairBound` is now **discharged** as `globalHookPairBound_proof`
(so `gDetectedGroupLe_proof` is unconditional).  The proof is the finite kernel
`decide` route: the both-benign case is closed by `dangerousSpread_subadditive`
(no `decide`), and the dangerous case by the scoped check `dangerPairPred_true`
in the global leaf module, which sweeps only the four globally-dangerous branches
(site `4` / `Y,Z`, site `88` / `Y,Z`) against the whole-circuit branch set,
keyed on **full** policy-vector equality.  Machine-confirmed (`#eval` over
`globalSites`): the only branches sharing the dangerous policies are the two
self-branches at site `4` (product `Z·Z = I`, barrier `0`) and `28` branches
sharing site `88`'s single-bit policy (max product barrier `2`); no benign branch
sharing a dangerous policy yields product barrier `> 2`.  Hence no abstract
Shor-4 ↔ surface bridge and no `528²` product is needed. -/

/-! ## GLOBAL run-linearization and accepted-barrier bound (`fcevalW_linear` closed
in the global model)

The gadget-local `fcevalW_linear` (above) is left open as a `Prop` because the
gadget-local `SurfaceFaultContribution` model is *unfaithful* (see the obstruction
note): an early-gadget data fault fires a later gadget's detector that the
gadget-local `branchPolicy` cannot observe.  The genuine, faithful linearization
lives in the **global** `GContribution` model, where each fault's suffix is the
remainder of the *whole* circuit.  This section closes it honestly with the
detector-XOR linearity engine (`run_factor_mem`, `dataPart_mulFull`,
`policyObservation_mulFull`, `policyObservation_clean_run_zero`) and assembles the
global accepted-barrier bound through `gDetectedGroupLe_proof`. -/

/-! ### Global list helpers (append / permutation invariance) -/

theorem gProduct_append (cs ds : List GContribution) :
    gProduct (cs ++ ds) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul (gProduct cs) (gProduct ds) := by
  simp only [gProduct, List.map_append, dataProd_append_aux]

theorem gPolicyXor_append (cs ds : List GContribution) :
    gPolicyXor (cs ++ ds) = policyXor (gPolicyXor cs) (gPolicyXor ds) := by
  simp only [gPolicyXor, List.map_append, policyXorList_append_aux]

theorem gProduct_perm {cs ds : List GContribution} (h : cs.Perm ds) :
    gProduct cs = gProduct ds :=
  dataProd_perm_aux (h.map _)

theorem gPolicyXor_perm {cs ds : List GContribution} (h : cs.Perm ds) :
    gPolicyXor cs = gPolicyXor ds :=
  policyXorList_perm_aux (h.map _)

theorem gPolicyXor_undetected_zero (cs : List GContribution)
    (h : ∀ c ∈ cs, ¬ gDetected c) :
    gPolicyXor cs = policyZero := by
  unfold gPolicyXor
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map, policyXorList]
    have hcPol : c.policy = policyZero := by
      have := h c List.mem_cons_self
      unfold gDetected at this; push_neg at this; exact this
    have hrestZero : policyXorList (List.map GContribution.policy rest) = policyZero :=
      ih (fun d hd => h d (List.mem_cons_of_mem c hd))
    rw [hcPol, hrestZero]
    funext k; simp [policyXor, policyZero]

/-! ### Undetected global branch ⇒ benign (from `globalHookSafePred_true`) -/

/-- A global branch whose policy detector vector is all-zero (undetected) has a
`DeltaSafe` data delta, hence barrier `≤ 1`.  This is the contrapositive of the
`detected ∨ DeltaSafe` global completeness fact `globalHookSafePred_true`: an
undetected branch cannot be in the detected half, so it must be in the safe half. -/
theorem gUndetected_deltaSafe (b : GBranch) (hUndet : gPolicy b = policyZero) :
    QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe (gDelta b) := by
  have hPred := globalHookSafePred_true
  unfold globalHookSafePred globalSites at hPred
  rw [List.all_eq_true] at hPred
  have hsite := hPred b.site b.site_mem
  rw [List.all_eq_true] at hsite
  have hp3 := hsite b.pauli (pauli_mem_XYZ b.pauli_ne_I)
  simp only at hp3
  -- the `detected` disjunct is false because every policy bit is zero
  have hdetFalse :
      (List.finRange (surfaceSpecShor.numStab + surfaceSpecShor.numFlags)).any
        (fun k => policyDiff (gFree b) (gFault b) k) = false := by
    rw [List.any_eq_false]
    intro k _
    have hk := congr_fun hUndet k
    unfold gPolicy at hk
    rw [hk]; simp [policyZero]
  rcases Bool.or_eq_true_iff.mp hp3 with hdet | hsafe
  · rw [show propagateCircuit b.site.suffix (cleanAtDetector b.site.detectorStart) = gFree b from rfl,
        show propagateCircuit b.site.suffix
          ((cleanAtDetector b.site.detectorStart).inject b.site.q b.pauli) = gFault b from rfl,
        hdetFalse] at hdet
    exact absurd hdet (by simp)
  · rw [decide_eq_true_eq] at hsafe
    apply surfaceBarrierData_le1_implies_deltaSafe
    exact hsafe

theorem gUndetected_barrier_le_one (b : GBranch) (hUndet : gPolicy b = policyZero) :
    SurfaceD3.surfaceBarrierData (gDelta b) ≤ 1 := by
  apply SurfaceD3.surfaceBarrierData_le_of_BI_PAIR
  have hBI :=
    QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR_pmul_of_delta_safe
      QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT (gUndetected_deltaSafe b hUndet)
  simpa [QStab.Paper.SurfaceD3CircuitDistance.dataI,
    QStab.Paper.SurfaceD3CircuitDistance.pmul] using hBI

/-- An undetected global contribution has barrier `≤ 1`. -/
theorem gContribution_undetected_barrier_le_one (c : GContribution)
    (hNotDet : ¬ gDetected c) :
    SurfaceD3.surfaceBarrierData c.delta ≤ 1 := by
  rw [c.delta_eq]
  apply gUndetected_barrier_le_one
  unfold gDetected at hNotDet; push_neg at hNotDet
  rw [← c.policy_eq]; exact hNotDet

/-- A list of undetected global contributions has product barrier `≤ length`. -/
theorem gUndetected_product_le_length :
    ∀ cs : List GContribution, (∀ c ∈ cs, ¬ gDetected c) ->
      SurfaceD3.surfaceBarrierData (gProduct cs) ≤ cs.length
  | [], _ => by
      unfold gProduct dataProd
      apply SurfaceD3.surfaceBarrierData_le_of_BI_PAIR
      simpa using QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT
  | c :: rest, h => by
      have hc : SurfaceD3.surfaceBarrierData c.delta ≤ 1 :=
        gContribution_undetected_barrier_le_one c (h c (by simp))
      have hrest : SurfaceD3.surfaceBarrierData (gProduct rest) ≤ rest.length :=
        gUndetected_product_le_length rest (fun d hd => h d (by simp [hd]))
      have hprod : gProduct (c :: rest) =
          QStab.Paper.SurfaceD3CircuitDistance.pmul c.delta (gProduct rest) := by
        simp [gProduct, dataProd]
      calc
        SurfaceD3.surfaceBarrierData (gProduct (c :: rest))
            ≤ SurfaceD3.surfaceBarrierData c.delta +
                SurfaceD3.surfaceBarrierData (gProduct rest) := by
              rw [hprod]; exact dangerousSpread_subadditive c.delta (gProduct rest)
        _ ≤ 1 + rest.length := Nat.add_le_add hc hrest
        _ = (c :: rest).length := by simp [Nat.add_comm]

/-! ### Global accepted-barrier partition bound -/

/-- **The global accepted-list partition bound.**  Any list of global
contributions whose policy detector vectors XOR-cancel (an accepted run) has
product data barrier bounded by its length.  Split into the policy-detected sublist
`D` (bounded by `gDetectedGroupLe_proof`, the genuine Shor hook-pair cancellation
L2) and the undetected sublist `U` (bounded by `gUndetected_product_le_length`),
then combine by subadditivity. -/
theorem gAcceptedPartitionBound (cs : List GContribution)
    (hCancel : gPolicyXor cs = policyZero) :
    SurfaceD3.surfaceBarrierData (gProduct cs) ≤ cs.length := by
  classical
  let detB : GContribution → Bool := fun c => decide (gDetected c)
  let D := cs.filter detB
  let U := cs.filter (fun c => !detB c)
  have hPerm : (D ++ U).Perm cs := List.filter_append_perm detB cs
  have hDataEq : gProduct cs =
      QStab.Paper.SurfaceD3CircuitDistance.pmul (gProduct D) (gProduct U) := by
    rw [gProduct_perm hPerm.symm, gProduct_append]
  have hPolicyEq : gPolicyXor cs =
      policyXor (gPolicyXor D) (gPolicyXor U) := by
    rw [gPolicyXor_perm hPerm.symm, gPolicyXor_append]
  have hUUndet : ∀ c ∈ U, ¬ gDetected c := by
    intro c hcU
    simp only [U, List.mem_filter, Bool.not_eq_true', detB] at hcU
    simpa using hcU.2
  have hUZero : gPolicyXor U = policyZero := gPolicyXor_undetected_zero U hUUndet
  have hDZero : gPolicyXor D = policyZero := by
    rw [hPolicyEq, hUZero] at hCancel
    funext k; have := congr_fun hCancel k; simp [policyXor, policyZero] at this ⊢; exact this
  have hDDet : ∀ c ∈ D, gDetected c := by
    intro c hcD
    simp only [D, List.mem_filter, detB] at hcD
    simpa using hcD.2
  have hDBound : SurfaceD3.surfaceBarrierData (gProduct D) ≤ D.length :=
    gDetectedGroupLe_proof D hDDet hDZero
  have hUBound : SurfaceD3.surfaceBarrierData (gProduct U) ≤ U.length :=
    gUndetected_product_le_length U hUUndet
  rw [hDataEq]
  have hSub := dangerousSpread_subadditive (gProduct D) (gProduct U)
  have hLen : D.length + U.length = cs.length := by
    have := @List.length_eq_length_filter_add _ cs detB
    simp only [D, U]; omega
  calc SurfaceD3.surfaceBarrierData
        (QStab.Paper.SurfaceD3CircuitDistance.pmul (gProduct D) (gProduct U))
      ≤ SurfaceD3.surfaceBarrierData (gProduct D) +
        SurfaceD3.surfaceBarrierData (gProduct U) := hSub
    _ ≤ D.length + U.length := Nat.add_le_add hDBound hUBound
    _ = cs.length := hLen

/-! ### Global run-linearization into `GContribution`s

`run_factor_mem` linearizes any `fcevalW` run into per-fault **global** residuals,
but its `RunFault` records do not carry `p ≠ I` (needed for a `GBranch`).  The
induction below re-runs the same structural skeleton, producing a genuine
`List GContribution` (each `GBranch` built from a global site, the recorded Pauli,
its `p ≠ I` proof from the `inject` constructor, and the global-membership proof),
and tracks the `runFaultProduct`-style `mulFull` factorization of both the
`paulis` and `detectors` registers.  Combined with the policy/data bridges this
discharges both clauses of the global linearization. -/

/-- A clean (paulis = `I`) deterministic run keeps every data qubit at `I`, so its
`dataPart` is `dataI`. -/
private theorem dataPart_clean_run (c : Circuit Nq) (cur : Nat) :
    dataPart (propagateCircuit c (cleanAt cur)) =
      QStab.Paper.SurfaceD3CircuitDistance.dataI := by
  funext q
  unfold dataPart QStab.Paper.SurfaceD3CircuitDistance.dataI
  apply propagateCircuit_clean_paulis_aux
  intro r; simp [cleanAt, ErrorState.clean]

/-- `cleanAt` and `cleanAtDetector` are the same clean state pinned to a cursor. -/
private theorem cleanAt_eq_cleanAtDetector (cur : Nat) :
    (cleanAt cur : ErrorState Nq) = cleanAtDetector cur := rfl

/-- `mulFull`-product of the per-contribution global-residual states `gFault`.
This is the `GContribution` analogue of `runFaultProduct`: it tracks both the
`paulis` (data) and `detectors` (policy) registers under `mulFull`. -/
def runGContribProduct : List GContribution -> ErrorState Nq
  | [] => ErrorState.clean Nq
  | c :: rest => mulFull (gFault c.branch) (runGContribProduct rest)

/-- **Global run-linearization with `GContribution`s.**  Any `fcevalW w fc es esf`
run starting at detector cursor `cur0` produces a list of `GContribution`s, one per
fault, whose `GBranch` sites all lie in `errLocsWithContextAux cur0 fc`, such that
the run's `paulis`/`detectors` factor as `mulFull` of the deterministic fault-free
run and the per-contribution global-residual product.  This is the honest engine of
both global linearization clauses. -/
theorem run_to_gcontributions :
    ∀ {w : Nat} {fc : FCircuit Nq} {es esf : ErrorState Nq},
      fcevalW w fc es esf -> ∀ cur0, es.detectorCursor = cur0 ->
        (∀ rf : ErrLocWithContext Nq, rf ∈ errLocsWithContextAux cur0 fc ->
            rf ∈ errLocsWithContext shorSurfaceCircuit) ->
          ∃ cs : List GContribution, cs.length = w ∧
            esf.paulis =
              (mulFull (propagateCircuit (eraseFaults fc) es)
                (runGContribProduct cs)).paulis ∧
            esf.detectors =
              (mulFull (propagateCircuit (eraseFaults fc) es)
                (runGContribProduct cs)).detectors := by
  intro w fc es esf h
  induction h with
  | nil es =>
      intro cur0 _ _
      refine ⟨[], rfl, ?_, ?_⟩
      · funext i
        simp [eraseFaults, propagateCircuit, mulFull, runGContribProduct, ErrorState.clean]
      · funext k
        simp [eraseFaults, propagateCircuit, mulFull, runGContribProduct, ErrorState.clean]
  | gate g is es0 esf0 w0 hpre ih =>
      intro cur0 hcur hmemglob
      have hmem' : ∀ rf : ErrLocWithContext Nq,
          rf ∈ errLocsWithContextAux (cur0 + gateDetectorAdvance g) is ->
            rf ∈ errLocsWithContext shorSurfaceCircuit := by
        intro rf hrf
        refine hmemglob rf ?_
        simp only [errLocsWithContextAux]
        exact hrf
      obtain ⟨cs, hlen, hp, hd⟩ := ih (cur0 + gateDetectorAdvance g)
        (by cases g <;> simp_all [propagateGate, gateDetectorAdvance]) hmem'
      refine ⟨cs, hlen, ?_, ?_⟩
      · rw [hp]; simp only [eraseFaults, propagateCircuit]
      · rw [hd]; simp only [eraseFaults, propagateCircuit]
  | idle q is es0 esf0 w0 hpre ih =>
      intro cur0 hcur hmemglob
      have hmem' : ∀ rf : ErrLocWithContext Nq,
          rf ∈ errLocsWithContextAux cur0 is ->
            rf ∈ errLocsWithContext shorSurfaceCircuit := by
        intro rf hrf
        refine hmemglob rf ?_
        simp only [errLocsWithContextAux]
        exact List.mem_cons_of_mem _ hrf
      obtain ⟨cs, hlen, hp, hd⟩ := ih cur0 hcur hmem'
      refine ⟨cs, hlen, ?_, ?_⟩
      · rw [hp]; simp only [eraseFaults]
      · rw [hd]; simp only [eraseFaults]
  | inject q is es0 esf0 p hp0 w0 hpre ih =>
      intro cur0 hcur hmemglob
      have hmem' : ∀ rf : ErrLocWithContext Nq,
          rf ∈ errLocsWithContextAux cur0 is ->
            rf ∈ errLocsWithContext shorSurfaceCircuit := by
        intro rf hrf
        refine hmemglob rf ?_
        simp only [errLocsWithContextAux]
        exact List.mem_cons_of_mem _ hrf
      obtain ⟨cs, hlen, hp, hd⟩ := ih cur0 hcur hmem'
      -- the freshly injected fault's global site
      have hsiteMem : (⟨q, eraseFaults is, cur0⟩ : ErrLocWithContext Nq) ∈
          errLocsWithContext shorSurfaceCircuit := by
        refine hmemglob _ ?_
        simp only [errLocsWithContextAux]
        exact List.mem_cons_self
      let b : GBranch := ⟨⟨q, eraseFaults is, cur0⟩, hsiteMem, p, hp0⟩
      let cNew : GContribution := ⟨b, gDelta b, gPolicy b, rfl, rfl⟩
      -- the new contribution's residual is exactly the lone-fault residual of `run_factor`
      have hgFault : gFault b =
          propagateCircuit (eraseFaults is) ((cleanAt es0.detectorCursor).inject q p) := by
        show propagateCircuit (eraseFaults is)
            ((cleanAtDetector cur0).inject q p)
          = propagateCircuit (eraseFaults is) ((cleanAt es0.detectorCursor).inject q p)
        rw [hcur]; rfl
      have hfactor : propagateCircuit (eraseFaults is) (es0.inject q p) =
          mulFull (propagateCircuit (eraseFaults is) es0) (gFault b) := by
        rw [hgFault, propagateCircuit_inject_mulFull (eraseFaults is) es0 q p]
      refine ⟨cNew :: cs, by simp [hlen], ?_, ?_⟩
      · rw [hp]
        show (mulFull (propagateCircuit (eraseFaults is) (es0.inject q p))
            (runGContribProduct cs)).paulis
          = (mulFull (propagateCircuit (eraseFaults (FInstr.errLoc q :: is)) es0)
              (runGContribProduct (cNew :: cs))).paulis
        simp only [eraseFaults, runGContribProduct]
        rw [hfactor, mulFull_paulis_assoc]
      · rw [hd]
        show (mulFull (propagateCircuit (eraseFaults is) (es0.inject q p))
            (runGContribProduct cs)).detectors
          = (mulFull (propagateCircuit (eraseFaults (FInstr.errLoc q :: is)) es0)
              (runGContribProduct (cNew :: cs))).detectors
        simp only [eraseFaults, runGContribProduct]
        rw [hfactor, mulFull_detectors_assoc]

/-! ### `runGContribProduct` projections bridge to `gProduct` / `gPolicyXor` -/

/-- `gFree` of a branch is a clean (paulis = `I`) deterministic run, so its
`policyObservation` is `policyZero`. -/
private theorem policyObservation_gFree_zero (b : GBranch) :
    policyObservation (gFree b) = policyZero := by
  unfold gFree
  rw [show cleanAtDetector b.site.detectorStart
      = (cleanAt b.site.detectorStart : ErrorState Nq) from rfl]
  exact policyObservation_clean_run_zero b.site.suffix b.site.detectorStart

/-- A branch's policy contribution equals the policy observation of its fault
residual (the free factor drops out, being a clean run). -/
private theorem gPolicy_eq_policyObservation_gFault (b : GBranch) :
    gPolicy b = policyObservation (gFault b) := by
  unfold gPolicy policyDiff
  rw [policyObservation_gFree_zero b]
  funext k; simp [policyXor, policyZero]

/-- The `dataPart` of the `GContribution` residual product equals the abstract
`gProduct` of their data deltas. -/
theorem dataPart_runGContribProduct (cs : List GContribution) :
    dataPart (runGContribProduct cs) = gProduct cs := by
  induction cs with
  | nil =>
      simp only [runGContribProduct, gProduct, List.map_nil, dataProd]
      funext q; simp [dataPart, ErrorState.clean,
        QStab.Paper.SurfaceD3CircuitDistance.dataI]
  | cons c rest ih =>
      simp only [runGContribProduct, gProduct, List.map_cons, dataProd]
      rw [dataPart_mulFull, ih]
      congr 1
      rw [c.delta_eq]; rfl

/-- The `policyObservation` of the `GContribution` residual product equals the
abstract `gPolicyXor` of their policy vectors. -/
theorem policyObservation_runGContribProduct (cs : List GContribution) :
    policyObservation (runGContribProduct cs) = gPolicyXor cs := by
  induction cs with
  | nil =>
      simp only [runGContribProduct, gPolicyXor, List.map_nil, policyXorList]
      -- clean state observes nothing
      have : (ErrorState.clean Nq) = cleanAt 0 := by
        simp [cleanAt, ErrorState.clean]
      rw [this, show (cleanAt 0 : ErrorState Nq)
          = propagateCircuit [] (cleanAt 0) from rfl]
      exact policyObservation_clean_run_zero [] 0
  | cons c rest ih =>
      simp only [runGContribProduct, gPolicyXor, List.map_cons, policyXorList]
      rw [policyObservation_mulFull, ih]
      congr 1
      rw [c.policy_eq]
      exact (gPolicy_eq_policyObservation_gFault c.branch).symm

/-! ### The global linearization (`fcevalW_linear` content, faithfully) and ladder -/

/-- **GLOBAL `fcevalW_linear`, proven.**  Every accepted-circuit `fcevalW` run from
the clean state linearizes into a faithful list of global `GContribution`s whose
data product reproduces the run's `dataPart` and whose policy XOR reproduces the
run's `policyObservation`.  Unlike the gadget-local `fcevalW_linear` (left open as
unfaithful), this holds with each contribution's suffix the remainder of the whole
circuit, so the policy detectors observe the full run. -/
theorem fcevalW_linear_global {w : Nat} {es : ErrorState Nq}
    (hrun : fcevalW w shorSurfaceCircuit (ErrorState.clean Nq) es) :
    ∃ cs : List GContribution,
      cs.length = w ∧
        dataPart es = gProduct cs ∧
        policyObservation es = gPolicyXor cs := by
  obtain ⟨cs, hlen, hp, hd⟩ := run_to_gcontributions hrun 0
    (by simp [ErrorState.clean]) (fun rf hrf => hrf)
  refine ⟨cs, hlen, ?_, ?_⟩
  · -- dataPart clause
    have hfree : dataPart (propagateCircuit (eraseFaults shorSurfaceCircuit)
        (ErrorState.clean Nq)) = QStab.Paper.SurfaceD3CircuitDistance.dataI := by
      rw [show (ErrorState.clean Nq) = cleanAt 0 from by simp [cleanAt, ErrorState.clean]]
      exact dataPart_clean_run _ 0
    have hdataEs : dataPart es = dataPart (mulFull
        (propagateCircuit (eraseFaults shorSurfaceCircuit) (ErrorState.clean Nq))
        (runGContribProduct cs)) := by
      unfold dataPart; rw [hp]
    rw [hdataEs, dataPart_mulFull, hfree, dataPart_runGContribProduct]
    funext q
    simp only [QStab.Paper.SurfaceD3CircuitDistance.pmul,
      QStab.Paper.SurfaceD3CircuitDistance.dataI]
    cases gProduct cs q <;> rfl
  · -- policyObservation clause
    have hfree : policyObservation (propagateCircuit (eraseFaults shorSurfaceCircuit)
        (ErrorState.clean Nq)) = policyZero := by
      rw [show (ErrorState.clean Nq) = cleanAt 0 from by simp [cleanAt, ErrorState.clean]]
      exact policyObservation_clean_run_zero _ 0
    have hpolEs : policyObservation es = policyObservation (mulFull
        (propagateCircuit (eraseFaults shorSurfaceCircuit) (ErrorState.clean Nq))
        (runGContribProduct cs)) := by
      unfold policyObservation
      funext k
      by_cases hk : k.val < surfaceSpecShor.numStab
      · simp only [hk, dite_true]
        unfold syndromeBit xorBools
        rw [hd]
      · simp only [hk, dite_false]
        by_cases hsel : surfaceSpecShor.postselectFlag
            ⟨k.val - surfaceSpecShor.numStab, by have := k.isLt; omega⟩ = true
        · simp only [hsel, if_true]; rw [hd]
        · simp only [hsel, Bool.false_eq_true, if_false]
    rw [hpolEs, policyObservation_mulFull, hfree,
        policyObservation_runGContribProduct]
    funext k; simp [policyXor, policyZero]

/-- **The global accepted-barrier ladder.**  `fcevalW_linear_global` (the honest
global run-linearization) plus `gAcceptedPartitionBound` (the global accepted-list
partition bound through `gDetectedGroupLe_proof`) discharge the PCC
`AcceptedBarrierBound` obligation for the concrete Shor surface circuit. -/
theorem surfaceAcceptedBarrierBound_of_global :
    surfaceAcceptedBarrierBound := by
  intro w es hrun hAccepted
  obtain ⟨cs, hlen, hdata, hpolicy⟩ := fcevalW_linear_global hrun
  unfold surfaceBarrier
  rw [hdata]
  have hzero := policyObservation_eq_zero_of_allFlagsZero hAccepted
  have hcancel : gPolicyXor cs = policyZero := by rw [← hpolicy, hzero]
  have hbound := gAcceptedPartitionBound cs hcancel
  rwa [hlen] at hbound

#check fcevalW_zero_eq
#check dataPart_inject_factor
#check shorSurfaceCircuit_run_split
#check globalSites
#check globalHookSafePred_true
#check surfaceNoUndetectedHook_global
#print axioms globalHookSafePred_true
#print axioms surfaceNoUndetectedHook_global

#check globalHookPairBound
#check globalHookPairBound_proof
#check gDetectedGroupLe
#check gDetectedGroupLe_proof
#check gProduct_cap
#print axioms gDetectedGroupLe
#print axioms gProduct_cap
#print axioms globalHookPairBound_proof
#print axioms gDetectedGroupLe_proof
#print axioms dangerPairPred_true

#check surfaceAcceptedBarrierBound
#check fcevalW_linear
#check detected_group_le
#check accepted_contribution_partition_bound
#check dangerousSpread_subadditive
#check benign_spread_le
#check dangerous_branch_fires
#check benign_contribution_product_le_length
#check surfaceAcceptedBarrierBound_of_ladder
#check branchFires_implies_branchPolicy_ne_zero
#check not_contributionDetected_implies_benign
#check contributionDataProduct_append
#check contributionPolicyXor_append
#check contributionPolicyXor_undetected_zero
#check partition_of_detected_group
#print axioms shor4_full_hook_pair_trueWeight_zero
#print axioms dangerousSpread_subadditive
#print axioms benign_spread_le
#print axioms dangerous_branch_fires
#print axioms benign_contribution_product_le_length
#print axioms surfaceAcceptedBarrierBound_of_ladder
#print axioms branchFires_implies_branchPolicy_ne_zero
#print axioms not_contributionDetected_implies_benign
#print axioms partition_of_detected_group
#print axioms fcevalW_zero_eq
#print axioms dataPart_inject_factor
#print axioms shorSurfaceCircuit_run_split
#print axioms propagateGate_mulFull
#print axioms propagateCircuit_mulFull
#print axioms propagateCircuit_inject_mulFull
#print axioms run_factor_mem
#print axioms dataPart_mulFull
#print axioms syndromeBit_mulFull
#print axioms policyObservation_mulFull
#print axioms policyObservation_clean_run_zero

-- GLOBAL fcevalW_linear and accepted-barrier bound (the genuine, faithful model)
#check run_to_gcontributions
#check fcevalW_linear_global
#check gAcceptedPartitionBound
#check surfaceAcceptedBarrierBound_of_global
#print axioms run_to_gcontributions
#print axioms dataPart_runGContribProduct
#print axioms policyObservation_runGContribProduct
#print axioms gUndetected_deltaSafe
#print axioms gAcceptedPartitionBound
#print axioms fcevalW_linear_global
#print axioms surfaceAcceptedBarrierBound_of_global

-- trivial whitespace edit for incremental rebuild timing
end QStab.QClifford.PCC.SurfaceD3Shor
