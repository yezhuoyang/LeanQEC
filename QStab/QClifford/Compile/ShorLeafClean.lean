import QStab.QClifford.Compile.SiteSplitGen
import QStab.QClifford.Compile.HGPShorProgram
import QStab.QClifford.Compile.XZProgramOfProgramsLeaves

/-!
# The Shor `LeafClean` witness: clean-helper data preservation

The per-leaf bundle that instantiates `compileProgramAux_site_split_gen` for
the Shor-extraction HGP program.  The acts-below half is
`cab_erase_compileShorOrdered` (already in `SiteSplitGen`); this file proves
the preservation half — the **clean-cat form** pinned by the scout probe:

* a fault-free Shor gadget block whose own cat helpers and verifier are clean
  on entry preserves every non-cat Pauli (in particular all data);
* the junk-tolerant form is genuinely FALSE for Shor (junk `Z` on a non-first
  cat backflows onto data through the coupling CNOTs), which is exactly why
  `LeafClean`'s preservation floor is `n + st` and not `n + st + helperCount`.

Structure: per-gate clean no-ops → cascade / coupling chain inductions
(the coupling invariant is "every cat stays Z-free": data faults only ever
deposit `X` on cats, so data controls are preserved) → block walk →
`compileGadgetBlock` unfold (`rfl`) → the `LeafClean` witness for
`hgpShorProgram` via the scheme-generic foldr leaf pin.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford
open QHL QHL.CodeHGPSchedule

/-! ## Per-gate clean no-ops -/

/-- A CNOT whose control and target both carry `I` changes no Pauli. -/
theorem propagateGate_cnot_clean_both {nq : Nat} (c t : Fin nq) (h : c ≠ t)
    (es : ErrorState nq) (hc : es.paulis c = Pauli.I) (ht : es.paulis t = Pauli.I)
    (i : Fin nq) :
    (propagateGate (Gate.cnot c t h) es).paulis i = es.paulis i := by
  by_cases hit : i = t
  · subst hit
    rw [propagateGate_cnot_target, hc]
    simp [xPart, pauliMul]
  · by_cases hic : i = c
    · subst hic
      rw [propagateGate_cnot_control, ht]
      simp [zPart, pauliMul]
    · exact propagateGate_cnot_paulis_ne c t h es i hic hit

/-- `prepPlus` resets its qubit to the identity Pauli. -/
theorem propagateGate_prepPlus_self {nq : Nat} (q : Fin nq) (es : ErrorState nq) :
    (propagateGate (Gate.prepPlus q) es).paulis q = Pauli.I := by
  show (if q = q then Pauli.I else es.paulis q) = Pauli.I
  rw [if_pos rfl]

/-- A prep on an already-clean qubit changes no Pauli. -/
theorem propagateGate_prepZero_noop {nq : Nat} (q : Fin nq) (es : ErrorState nq)
    (h : es.paulis q = Pauli.I) (i : Fin nq) :
    (propagateGate (Gate.prepZero q) es).paulis i = es.paulis i := by
  by_cases hiq : i = q
  · rw [hiq, propagateGate_prepZero_self, h]
  · exact propagateGate_prepZero_paulis_ne q es i hiq

theorem propagateGate_prepPlus_noop {nq : Nat} (q : Fin nq) (es : ErrorState nq)
    (h : es.paulis q = Pauli.I) (i : Fin nq) :
    (propagateGate (Gate.prepPlus q) es).paulis i = es.paulis i := by
  by_cases hiq : i = q
  · rw [hiq, propagateGate_prepPlus_self, h]
  · exact propagateGate_prepPlus_paulis_ne q es i hiq

/-- A Hadamard on a clean qubit changes no Pauli. -/
theorem propagateGate_hadamard_noop {nq : Nat} (q : Fin nq) (es : ErrorState nq)
    (h : es.paulis q = Pauli.I) (i : Fin nq) :
    (propagateGate (Gate.hadamard q) es).paulis i = es.paulis i := by
  by_cases hiq : i = q
  · rw [hiq, propagateGate_hadamard_self, h]; rfl
  · exact propagateGate_hadamard_paulis_ne q es i hiq

/-- A compiled `cnot` between two clean qubits changes no Pauli (the `c = t`
degenerate compiles to the empty circuit). -/
theorem cnotCircuit_clean_noop {nq : Nat} (c t : Fin nq) (es : ErrorState nq)
    (hc : es.paulis c = Pauli.I) (ht : es.paulis t = Pauli.I) (i : Fin nq) :
    (propagateCircuit (eraseFaults (cnot c t)) es).paulis i = es.paulis i := by
  by_cases h : c = t
  · simp [cnot, h, propagateCircuit]
  · have he : eraseFaults (cnot c t) = [Gate.cnot c t h] := by
      simp [cnot, h, eraseFaults]
    rw [he]
    simp only [propagateCircuit]
    exact propagateGate_cnot_clean_both c t h es hc ht i

/-! ## Chain inductions -/

/-- The cat cascade over pairwise-clean pairs changes no Pauli. -/
theorem cnotPairs_clean_noop {nq : Nat} :
    ∀ (ps : List (Fin nq × Fin nq)) (es : ErrorState nq),
      (∀ p ∈ ps, es.paulis p.1 = Pauli.I ∧ es.paulis p.2 = Pauli.I) →
      ∀ i : Fin nq,
        (propagateCircuit (eraseFaults ((ps.map (fun cc => cnot cc.1 cc.2)).flatten)) es).paulis i
          = es.paulis i := by
  intro ps
  induction ps with
  | nil => intro es _ i; simp [propagateCircuit]
  | cons p rest ih =>
      intro es hcl i
      have hcirc : eraseFaults (((p :: rest).map (fun cc => cnot cc.1 cc.2)).flatten)
          = eraseFaults (cnot p.1 p.2) ++
            eraseFaults ((rest.map (fun cc => cnot cc.1 cc.2)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      have hp := hcl p (List.mem_cons_self ..)
      set es1 := propagateCircuit (eraseFaults (cnot p.1 p.2)) es with hes1
      have hpt : ∀ j : Fin nq, es1.paulis j = es.paulis j := fun j =>
        cnotCircuit_clean_noop p.1 p.2 es hp.1 hp.2 j
      have hcl1 : ∀ p' ∈ rest, es1.paulis p'.1 = Pauli.I ∧ es1.paulis p'.2 = Pauli.I := by
        intro p' hp'
        have := hcl p' (List.mem_cons.mpr (Or.inr hp'))
        exact ⟨(hpt p'.1).trans this.1, (hpt p'.2).trans this.2⟩
      rw [ih es1 hcl1 i, hpt i]

/-- The trailing raw cat measurements change no Pauli. -/
theorem rawMeasZ_flatten_paulis {nq : Nat} :
    ∀ (cs : List (Fin nq)) (es : ErrorState nq) (i : Fin nq),
      (propagateCircuit (eraseFaults ((cs.map rawMeasZ).flatten)) es).paulis i = es.paulis i := by
  intro cs
  induction cs with
  | nil => intro es i; simp [propagateCircuit]
  | cons c rest ih =>
      intro es i
      have hcirc : eraseFaults (((c :: rest).map rawMeasZ).flatten)
          = Gate.measZ c :: eraseFaults ((rest.map rawMeasZ).flatten) := by
        simp [List.map_cons, List.flatten_cons, rawMeasZ, eraseFaults]
      rw [hcirc]
      simp only [propagateCircuit]
      rw [ih (propagateGate (Gate.measZ c) es) i, propagateGate_measZ_paulis]

/-- One Shor coupling slot: preserves every qubit that is not the slot's cat
(including the slot's own data qubit, via control-preservation), provided the
cat is Z-free on entry. -/
theorem shorCouplingSlot_preserves_offcat {nq : Nat} (slot : ScheduledPauli nq)
    (cat : Fin nq) (hqc : slot.qubit ≠ cat) (es : ErrorState nq)
    (hcat : zPart (es.paulis cat) = Pauli.I) (d : Fin nq) (hd : d ≠ cat) :
    (propagateCircuit (eraseFaults (shorCouplingSlot slot cat)) es).paulis d
      = es.paulis d := by
  obtain ⟨sk, sq⟩ := slot
  cases sk with
  | X =>
      by_cases hdq : d = sq
      · rw [hdq]
        exact propagate_hSandwich_preserves_control sq cat hqc es hcat
      · have hc : eraseFaults (shorCouplingSlot ⟨.X, sq⟩ cat) =
            [Gate.hadamard sq, Gate.cnot sq cat hqc, Gate.hadamard sq] := by
          simp [shorCouplingSlot, hadamard, cnot, hqc, eraseFaults]
        rw [hc]
        simp only [propagateCircuit]
        rw [propagateGate_hadamard_paulis_ne sq _ d hdq,
          propagateGate_cnot_paulis_ne sq cat hqc _ d hdq hd,
          propagateGate_hadamard_paulis_ne sq es d hdq]
  | Z =>
      have hc : eraseFaults (shorCouplingSlot ⟨.Z, sq⟩ cat) = [Gate.cnot sq cat hqc] := by
        simp [shorCouplingSlot, cnot, hqc, eraseFaults]
      rw [hc]
      simp only [propagateCircuit]
      by_cases hdq : d = sq
      · rw [hdq]
        exact propagateGate_cnot_control_preserved sq cat hqc es hcat
      · exact propagateGate_cnot_paulis_ne sq cat hqc es d hdq hd

/-- One Shor coupling slot keeps its own cat Z-free (it only receives `X`). -/
theorem shorCouplingSlot_keeps_catZfree {nq : Nat} (slot : ScheduledPauli nq)
    (cat : Fin nq) (hqc : slot.qubit ≠ cat) (es : ErrorState nq)
    (hcat : zPart (es.paulis cat) = Pauli.I) :
    zPart ((propagateCircuit (eraseFaults (shorCouplingSlot slot cat)) es).paulis cat)
      = Pauli.I := by
  obtain ⟨sk, sq⟩ := slot
  cases sk with
  | X => exact propagate_hSandwich_keeps_ancZfree sq cat hqc es hcat
  | Z =>
      have hc : eraseFaults (shorCouplingSlot ⟨.Z, sq⟩ cat) = [Gate.cnot sq cat hqc] := by
        simp [shorCouplingSlot, cnot, hqc, eraseFaults]
      rw [hc]
      simp only [propagateCircuit]
      rw [propagateGate_cnot_target sq cat hqc]
      exact zPart_pauliMul_xPart hcat

/-- **Coupling-chain preservation**: the zipped Shor couplings preserve every
non-cat qubit, when the cats are pairwise distinct, disjoint from the slot
qubits, and Z-free on entry. -/
theorem shorCouplings_preserve_data {nq : Nat} :
    ∀ (pairs : List (ScheduledPauli nq × Fin nq)),
      (pairs.map (·.2)).Nodup →
      (∀ pc ∈ pairs, ∀ c' ∈ pairs.map (·.2), pc.1.qubit ≠ c') →
      ∀ es : ErrorState nq, (∀ c' ∈ pairs.map (·.2), zPart (es.paulis c') = Pauli.I) →
        ∀ d : Fin nq, d ∉ pairs.map (·.2) →
          (propagateCircuit (eraseFaults
              ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)) es).paulis d
            = es.paulis d := by
  intro pairs
  induction pairs with
  | nil => intro _ _ es _ d _; simp [propagateCircuit]
  | cons pc rest ih =>
      intro hnd hqc es hZ d hd
      have hcatmem : pc.2 ∈ (pc :: rest).map (·.2) := by simp
      have hqcat : pc.1.qubit ≠ pc.2 := hqc pc (List.mem_cons_self ..) pc.2 hcatmem
      have hcirc : eraseFaults (((pc :: rest).map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)
          = eraseFaults (shorCouplingSlot pc.1 pc.2) ++
            eraseFaults ((rest.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      have hdcat : d ≠ pc.2 := fun h => hd (h ▸ hcatmem)
      have hZ0 : zPart (es.paulis pc.2) = Pauli.I := hZ pc.2 hcatmem
      set es1 := propagateCircuit (eraseFaults (shorCouplingSlot pc.1 pc.2)) es with hes1
      have hnd0 : (pc.2 :: rest.map (·.2)).Nodup := hnd
      have hnd' : (rest.map (·.2)).Nodup := (List.nodup_cons.mp hnd0).2
      have hfresh : pc.2 ∉ rest.map (·.2) := (List.nodup_cons.mp hnd0).1
      have hqc' : ∀ pc' ∈ rest, ∀ c' ∈ rest.map (·.2), pc'.1.qubit ≠ c' := by
        intro pc' hpc' c' hc'
        exact hqc pc' (List.mem_cons.mpr (Or.inr hpc')) c'
          (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hc')
      have hZ' : ∀ c' ∈ rest.map (·.2), zPart (es1.paulis c') = Pauli.I := by
        intro c' hc'
        have hc'cat : c' ≠ pc.2 := fun h => hfresh (h ▸ hc')
        rw [hes1, shorCouplingSlot_preserves_offcat pc.1 pc.2 hqcat es hZ0 c' hc'cat]
        exact hZ c' (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hc')
      have hd' : d ∉ rest.map (·.2) := fun h =>
        hd (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)
      rw [ih hnd' hqc' es1 hZ' d hd']
      rw [hes1]
      exact shorCouplingSlot_preserves_offcat pc.1 pc.2 hqcat es hZ0 d hdcat

/-! ## Zip projection helper -/

theorem zip_snd_sublist {α β : Type} : ∀ (as : List α) (bs : List β),
    ((List.zip as bs).map Prod.snd).Sublist bs := by
  intro as
  induction as with
  | nil => intro bs; simp
  | cons a as' ih =>
      intro bs
      cases bs with
      | nil => simp
      | cons b bs' => simpa using List.Sublist.cons₂ b (ih bs')

/-! ## The block-level clean-helper preservation -/

/-- **Shor block preserves data from clean helpers**: with the cat list and
verifier clean on entry (and the cats pairwise distinct and disjoint from the
scheduled data qubits), the fault-free Shor gadget block leaves every non-cat
qubit's Pauli unchanged. -/
theorem compileShorOrdered_preserves_data_cleanHelpers {nq : Nat}
    (sigma : RuleSchedule nq) (cats : List (Fin nq)) (v : Fin nq)
    (hndcat : cats.Nodup)
    (hslots_cats : ∀ s ∈ sigma.slots, ∀ c ∈ cats, s.qubit ≠ c)
    (es : ErrorState nq)
    (hclean_cats : ∀ c ∈ cats, es.paulis c = Pauli.I)
    (hclean_v : es.paulis v = Pauli.I)
    (d : Fin nq) (hd_cats : d ∉ cats) :
    (propagateCircuit (eraseFaults (compileShorOrdered sigma cats v)) es).paulis d
      = es.paulis d := by
  cases cats with
  | nil => rfl
  | cons c0 rest =>
      have hlast_mem : (c0 :: rest).getLast (by simp) ∈ (c0 :: rest) := List.getLast_mem _
      have hc0_mem : c0 ∈ (c0 :: rest) := List.mem_cons_self ..
      show (propagateCircuit (eraseFaults (
        orderedCatPrepZ (c0 :: rest) ++
        prepP v ++
        cnot v c0 ++
        cnot v ((c0 :: rest).getLast (by simp)) ++
        hadamard v ++
        flagMeasZ v ++
        ((List.zip sigma.slots (c0 :: rest)).map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten ++
        ((c0 :: rest).map rawMeasZ).flatten)) es).paulis d = es.paulis d
      simp only [eraseFaults_append, QHL.Target.propagateCircuit_append]
      -- segment 1: prep0 c0 ++ cascade — full pointwise no-op on clean cats
      have hprep0 : eraseFaults (prep0 c0) = [Gate.prepZero c0] := by
        simp [prep0, eraseFaults]
      have hseg1 : ∀ i : Fin nq,
          (propagateCircuit (eraseFaults (orderedCatPrepZ (c0 :: rest))) es).paulis i
            = es.paulis i := by
        intro i
        show (propagateCircuit (eraseFaults (prep0 c0 ++
          ((List.zip (c0 :: rest) rest).map (fun cc => cnot cc.1 cc.2)).flatten)) es).paulis i
          = es.paulis i
        rw [eraseFaults_append, QHL.Target.propagateCircuit_append, hprep0]
        simp only [propagateCircuit]
        set es1 := propagateGate (Gate.prepZero c0) es with hes1
        have hpt1 : ∀ j : Fin nq, es1.paulis j = es.paulis j := fun j =>
          propagateGate_prepZero_noop c0 es (hclean_cats c0 hc0_mem) j
        have hcl1 : ∀ p ∈ List.zip (c0 :: rest) rest,
            es1.paulis p.1 = Pauli.I ∧ es1.paulis p.2 = Pauli.I := by
          intro p hp
          have h1 : p.1 ∈ (c0 :: rest) := (List.of_mem_zip hp).1
          have h2 : p.2 ∈ (c0 :: rest) := List.mem_cons_of_mem c0 (List.of_mem_zip hp).2
          exact ⟨(hpt1 p.1).trans (hclean_cats p.1 h1),
            (hpt1 p.2).trans (hclean_cats p.2 h2)⟩
        rw [cnotPairs_clean_noop _ es1 hcl1 i, hpt1 i]
      have hprepP : eraseFaults (prepP v) = [Gate.prepPlus v] := by simp [prepP, eraseFaults]
      have hflag : eraseFaults (flagMeasZ v) = [Gate.measZ v] := by simp [flagMeasZ, eraseFaults]
      have hhad : eraseFaults (hadamard v) = [Gate.hadamard v] := by simp [hadamard, eraseFaults]
      -- chain pointwise equalities through segments 2..6
      set esA := propagateCircuit (eraseFaults (orderedCatPrepZ (c0 :: rest))) es with hesA
      set esB := propagateCircuit (eraseFaults (prepP v)) esA with hesB
      set esC := propagateCircuit (eraseFaults (cnot v c0)) esB with hesC
      set esD := propagateCircuit (eraseFaults (cnot v ((c0 :: rest).getLast (by simp)))) esC
        with hesD
      set esE := propagateCircuit (eraseFaults (hadamard v)) esD with hesE
      set esF := propagateCircuit (eraseFaults (flagMeasZ v)) esE with hesF
      have hptB : ∀ j : Fin nq, esB.paulis j = esA.paulis j := by
        intro j
        rw [hesB, hprepP]
        simp only [propagateCircuit]
        exact propagateGate_prepPlus_noop v esA ((hseg1 v).trans hclean_v) j
      have hcleanB_v : esB.paulis v = Pauli.I := (hptB v).trans ((hseg1 v).trans hclean_v)
      have hcleanB_cats : ∀ c ∈ (c0 :: rest), esB.paulis c = Pauli.I := fun c hc =>
        (hptB c).trans ((hseg1 c).trans (hclean_cats c hc))
      have hptC : ∀ j : Fin nq, esC.paulis j = esB.paulis j := fun j =>
        cnotCircuit_clean_noop v c0 esB hcleanB_v (hcleanB_cats c0 hc0_mem) j
      have hcleanC_v : esC.paulis v = Pauli.I := (hptC v).trans hcleanB_v
      have hcleanC_cats : ∀ c ∈ (c0 :: rest), esC.paulis c = Pauli.I := fun c hc =>
        (hptC c).trans (hcleanB_cats c hc)
      have hptD : ∀ j : Fin nq, esD.paulis j = esC.paulis j := fun j =>
        cnotCircuit_clean_noop v _ esC hcleanC_v (hcleanC_cats _ hlast_mem) j
      have hcleanD_v : esD.paulis v = Pauli.I := (hptD v).trans hcleanC_v
      have hcleanD_cats : ∀ c ∈ (c0 :: rest), esD.paulis c = Pauli.I := fun c hc =>
        (hptD c).trans (hcleanC_cats c hc)
      have hptE : ∀ j : Fin nq, esE.paulis j = esD.paulis j := by
        intro j
        rw [hesE, hhad]
        simp only [propagateCircuit]
        exact propagateGate_hadamard_noop v esD hcleanD_v j
      have hptF : ∀ j : Fin nq, esF.paulis j = esE.paulis j := by
        intro j
        rw [hesF, hflag]
        simp only [propagateCircuit]
        exact propagateGate_measZ_paulis v j esE
      -- the coupling chain over the zip, then the raw measurements
      set pairs := List.zip sigma.slots (c0 :: rest) with hpairs
      have hsub : (pairs.map Prod.snd).Sublist (c0 :: rest) := zip_snd_sublist _ _
      have hndp : (pairs.map (·.2)).Nodup := hsub.nodup hndcat
      have hqcp : ∀ pc ∈ pairs, ∀ c' ∈ pairs.map (·.2), pc.1.qubit ≠ c' := by
        intro pc hpc c' hc'
        have hs : pc.1 ∈ sigma.slots := (List.of_mem_zip hpc).1
        exact hslots_cats pc.1 hs c' (hsub.subset hc')
      have hZp : ∀ c' ∈ pairs.map (·.2), zPart (esF.paulis c') = Pauli.I := by
        intro c' hc'
        rw [(hptF c').trans ((hptE c').trans (hcleanD_cats c' (hsub.subset hc')))]
        rfl
      have hdp : d ∉ pairs.map (·.2) := fun h => hd_cats (hsub.subset h)
      rw [rawMeasZ_flatten_paulis (c0 :: rest) _ d,
        shorCouplings_preserve_data pairs hndp hqcp esF hZp d hdp,
        hptF d, hptE d, hptD d, hptC d, hptB d, hseg1 d]

/-! ## Block-shape facts and the `LeafClean` fields -/

/-- The compiled Shor gadget block is `compileShorOrdered` over the lifted
schedule with the block's cat helpers and verifier. -/
theorem compileGadgetBlock_Shor_eq {n total : Nat} (sigma : RuleSchedule n)
    (start : Nat) (hfit : start + helperCount Scheme.Shor sigma ≤ total) :
    compileGadgetBlock Scheme.Shor sigma start hfit
      = compileShorOrdered (liftSchedule (k := total) sigma)
          (blockShorCat n total start sigma.slots.length hfit)
          (blockHelperQ n total start (sigma.slots.length + 1) hfit
            ⟨sigma.slots.length, Nat.lt_succ_self _⟩) := rfl

/-- Value window of a block cat helper. -/
theorem mem_blockShorCat_val {n total start w : Nat} {hfit : start + (w + 1) ≤ total}
    {c : Fin (n + total)} (hc : c ∈ blockShorCat n total start w hfit) :
    n + start ≤ c.val ∧ c.val < n + start + w := by
  unfold blockShorCat at hc
  rw [List.mem_map] at hc
  obtain ⟨a, _, rfl⟩ := hc
  have := a.isLt
  simp only [blockHelperQ]
  omega

/-- The block cat helpers are pairwise distinct. -/
theorem blockShorCat_nodup (n total start w : Nat) (hfit : start + (w + 1) ≤ total) :
    (blockShorCat n total start w hfit).Nodup := by
  unfold blockShorCat
  refine List.Nodup.map ?_ (List.nodup_finRange w)
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [blockHelperQ] at hv
  omega

/-- Acts-below (the `LeafClean` first field) for the Shor block. -/
theorem shorBlock_cab {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.Shor sigma ≤ total) :
    circuitActsBelow (eraseFaults (compileGadgetBlock Scheme.Shor sigma start hfit))
      (n + start + helperCount Scheme.Shor sigma) := by
  rw [compileGadgetBlock_Shor_eq]
  have hw : helperCount Scheme.Shor sigma = sigma.slots.length + 1 := rfl
  have hcat : ∀ c ∈ blockShorCat n total start sigma.slots.length hfit,
      c.val < n + start + helperCount Scheme.Shor sigma := by
    intro c hc
    have := (mem_blockShorCat_val hc).2
    omega
  have hver : (blockHelperQ n total start (sigma.slots.length + 1) hfit
      ⟨sigma.slots.length, Nat.lt_succ_self _⟩).val
      < n + start + helperCount Scheme.Shor sigma := by
    simp only [blockHelperQ]
    omega
  have hslots : ∀ s ∈ (liftSchedule (k := total) sigma).slots,
      s.qubit.val < n + start + helperCount Scheme.Shor sigma := by
    intro s hs
    simp only [liftSchedule, List.mem_map] at hs
    obtain ⟨s', _, rfl⟩ := hs
    simp only [liftSlot, freshDataQ_val]
    have := s'.qubit.isLt
    omega
  cases hcs : blockShorCat n total start sigma.slots.length hfit with
  | nil =>
      show circuitActsBelow (eraseFaults (compileShorOrdered _ [] _)) _
      exact cab_nil
  | cons c0 rest =>
      refine cab_erase_compileShorOrdered _ (c0 :: rest) _ (by simp) ?_ hver ?_
      · intro c hc
        exact hcat c (hcs ▸ hc)
      · exact hslots

/-- Preservation at floor `n + start` (the `LeafClean` second field) for the
Shor block: helpers at `≥ n + start` clean ⟹ data preserved. -/
theorem shorBlock_PDA {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.Shor sigma ≤ total) :
    PreservesDataAbove (eraseFaults (compileGadgetBlock Scheme.Shor sigma start hfit))
      (n + start) := by
  intro es hc d hd
  rw [compileGadgetBlock_Shor_eq]
  refine compileShorOrdered_preserves_data_cleanHelpers _ _ _
    (blockShorCat_nodup n total start sigma.slots.length hfit) ?_ es ?_ ?_ d ?_
  · intro s hs c hcm
    simp only [liftSchedule, List.mem_map] at hs
    obtain ⟨s', _, rfl⟩ := hs
    have h1 := (mem_blockShorCat_val hcm).1
    have h2 := s'.qubit.isLt
    refine Fin.ne_of_val_ne ?_
    simp only [liftSlot, freshDataQ_val]
    omega
  · intro c hcm
    exact hc c (mem_blockShorCat_val hcm).1
  · exact hc _ (by simp only [blockHelperQ]; omega)
  · intro hmem
    have := (mem_blockShorCat_val hmem).1
    omega

/-! ## The `LeafClean` witness for the Shor-extraction HGP program -/

/-- Every measurement leaf of `hgpShorProgram` is `(.Shor, hgpSchedule d hd i)` —
the generic generator-level pin `xzProgramOfProgramsWith_measLeaf` specialized
through the certified `genSchedule_eq_hgpSchedule`. -/
theorem hgpShorProgram_measLeaf (d : Nat) (hd : 2 ≤ d) (scheme : Scheme)
    (sigma : RuleSchedule (d * d + (d - 1) * (d - 1))) :
    MeasLeaf (hgpShorProgram d) scheme sigma →
      ∃ i : Fin (2 * ((d - 1) * d)), scheme = Scheme.Shor ∧ sigma = hgpSchedule d hd i := by
  intro h
  unfold hgpShorProgram at h
  obtain ⟨k, hk, hs, hσ⟩ :=
    xzProgramOfProgramsWith_measLeaf .Shor QHL.CodeLang.HGP.code hgpOrderProg hgpLenProg
      (2 * ((d - 1) * d)) (d * d + (d - 1) * (d - 1)) d scheme sigma h
  exact ⟨⟨k, hk⟩, hs, hσ.trans (genSchedule_eq_hgpSchedule d hd ⟨k, hk⟩)⟩

/-- **The Shor `LeafClean` witness**: every leaf of `hgpShorProgram` acts below
its own helper ceiling and preserves data from clean own helpers — the bundle
`compileProgramAux_site_split_gen` consumes. -/
theorem hgpShor_leafClean (d : Nat) (hd : 2 ≤ d) :
    LeafClean (total := programHelperCount (hgpShorProgram d)) (hgpShorProgram d) := by
  intro sc sg hml st hf
  obtain ⟨i, rfl, rfl⟩ := hgpShorProgram_measLeaf d hd sc sg hml
  exact ⟨shorBlock_cab _ _ _, shorBlock_PDA _ _ _⟩

/-! ## Regression guards (axiom pins) -/

/--
info: 'QStab.QClifford.Compile.compileShorOrdered_preserves_data_cleanHelpers' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms compileShorOrdered_preserves_data_cleanHelpers

/--
info: 'QStab.QClifford.Compile.shorBlock_PDA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shorBlock_PDA

/--
info: 'QStab.QClifford.Compile.hgpShor_leafClean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpShor_leafClean

end QStab.QClifford.Compile
