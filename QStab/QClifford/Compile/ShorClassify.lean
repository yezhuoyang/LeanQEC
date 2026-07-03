import QStab.QClifford.Compile.ShorBackAction

/-!
# Shor gadget site classification, stage 1: the pre-coupling (hook) branch

Every fault site of the compiled Shor gadget block splits at the coupling
boundary into a **pre-coupling** site (prep / cat cascade / verifier legs) and
a **coupling-or-measurement** site.  This file handles the pre-coupling half:
those gates act only on *helper* qubits (`≥ P.n`) below the block ceiling, so a
fault there leaves the data block clean at coupling entry, and the couplings
then image the cats' Z-parts onto the schedule's data qubits — a subset hook.

The result is the generic (`sigma`-parametric, kind-uniform, `Nodup`) statement
that a pre-coupling site's residual is `dominatedByScheduleHook`: pointwise the
schedule kind on a subset of scheduled data qubits, identity elsewhere.  The
`Nodup` + kind-uniformity binder shape matches the NZ classifier exactly.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford

/-- Pointwise: the schedule's CSS kind on a subset of scheduled data qubits,
identity elsewhere — the form a subset hook takes, and the exact shape the
per-code domination lemma consumes. -/
def dominatedByScheduleHook {n : Nat} (sigma : RuleSchedule n) (R : ErrorVec n) : Prop :=
  ∀ q : Fin n, R q = Pauli.I ∨ (R q = scheduleKind sigma ∧ q ∈ sigma.slots.map (·.qubit))

/-! ## `circuitActsAbove`: the lower-bound mirror of `circuitActsBelow` -/

/-- Every gate of `c` acts only on qubits with value `≥ n` (helpers). -/
def circuitActsAbove {nq : Nat} (c : Circuit nq) (n : Nat) : Prop :=
  ∀ g ∈ c, ∀ q : Fin nq, gateActsOn g q → n ≤ q.val

theorem caa_nil {nq n : Nat} : circuitActsAbove ([] : Circuit nq) n :=
  fun _ hg => absurd hg (List.not_mem_nil)

theorem caa_append {nq n : Nat} {a b : Circuit nq}
    (ha : circuitActsAbove a n) (hb : circuitActsAbove b n) :
    circuitActsAbove (a ++ b) n := by
  intro g hg q hq
  rcases List.mem_append.mp hg with h | h
  · exact ha g h q hq
  · exact hb g h q hq

theorem caa_flatten {nq n : Nat} {ls : List (Circuit nq)}
    (h : ∀ c ∈ ls, circuitActsAbove c n) : circuitActsAbove ls.flatten n := by
  intro g hg q hq
  rw [List.mem_flatten] at hg
  obtain ⟨c, hc, hgc⟩ := hg
  exact h c hc g hgc q hq

theorem caa_erase_flatten_map {nq n : Nat} {α : Type} (l : List α) (f : α → FCircuit nq)
    (hf : ∀ a ∈ l, circuitActsAbove (eraseFaults (f a)) n) :
    circuitActsAbove (eraseFaults ((l.map f).flatten)) n := by
  rw [eraseFaults_flatten, List.map_map]
  apply caa_flatten
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨a, ha, rfl⟩ := hc
  exact hf a ha

theorem caa_erase_prep0 {nq n : Nat} (q : Fin nq) (hq : n ≤ q.val) :
    circuitActsAbove (eraseFaults (prep0 q)) n := by
  intro g hg q' hq'; simp only [prep0, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl; cases hq'; exact hq

theorem caa_erase_prepP {nq n : Nat} (q : Fin nq) (hq : n ≤ q.val) :
    circuitActsAbove (eraseFaults (prepP q)) n := by
  intro g hg q' hq'; simp only [prepP, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl; cases hq'; exact hq

theorem caa_erase_hadamard {nq n : Nat} (q : Fin nq) (hq : n ≤ q.val) :
    circuitActsAbove (eraseFaults (hadamard q)) n := by
  intro g hg q' hq'; simp only [hadamard, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl; cases hq'; exact hq

theorem caa_erase_flagMeasZ {nq n : Nat} (q : Fin nq) (hq : n ≤ q.val) :
    circuitActsAbove (eraseFaults (flagMeasZ q)) n := by
  intro g hg q' hq'; simp only [flagMeasZ, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl; cases hq'; exact hq

theorem caa_erase_cnot {nq n : Nat} (c t : Fin nq) (hc : n ≤ c.val) (ht : n ≤ t.val) :
    circuitActsAbove (eraseFaults (cnot c t)) n := by
  intro g hg q' hq'; unfold cnot at hg
  by_cases h : c = t
  · rw [dif_pos h] at hg; exact absurd hg (List.not_mem_nil)
  · rw [dif_neg h] at hg
    simp only [eraseFaults, List.mem_singleton] at hg
    rcases hg with rfl
    rcases hq' with rfl | rfl
    · exact hc
    · exact ht

/-- The cat cascade acts only on cats. -/
theorem caa_erase_orderedCatPrepZ {nq n : Nat} (cat : List (Fin nq))
    (hcat : ∀ c ∈ cat, n ≤ c.val) :
    circuitActsAbove (eraseFaults (orderedCatPrepZ cat)) n := by
  cases cat with
  | nil => simp only [orderedCatPrepZ, eraseFaults]; exact caa_nil
  | cons c0 rest =>
      simp only [orderedCatPrepZ]
      rw [eraseFaults_append]
      refine caa_append (caa_erase_prep0 c0 (hcat c0 (List.mem_cons_self ..))) ?_
      apply caa_erase_flatten_map
      intro cc hcc
      have h1 : cc.1 ∈ (c0 :: rest) := (List.of_mem_zip hcc).1
      have h2 : cc.2 ∈ rest := (List.of_mem_zip hcc).2
      exact caa_erase_cnot cc.1 cc.2 (hcat cc.1 h1) (hcat cc.2 (List.mem_cons_of_mem c0 h2))

/-! ## The generic helper-only prefix-site decomposition -/

/-- **Every fault site of a helper-only, ceiling-bounded circuit** has its qubit
in `[P.n, L)` and a suffix `Xr ++ eraseFaults tail`, where `Xr` is again
helper-only and ceiling-bounded.  (`gateActsOn` bounds the *gates*; the
`herr` hypothesis bounds the *errLoc markers*.) -/
theorem helperPrefix_site {P : QECParams} {total : Nat} (C : FCircuit (P.n + total))
    (L : Nat)
    (hbelow : circuitActsBelow (eraseFaults C) L)
    (habove : circuitActsAbove (eraseFaults C) P.n)
    (herr : ∀ q0 : Fin (P.n + total), FInstr.errLoc q0 ∈ C → P.n ≤ q0.val ∧ q0.val < L) :
    ∀ (cursor : Nat) (tail : FCircuit (P.n + total))
      (site : PCC.ErrLocWithContext (P.n + total)),
      site ∈ prefixErrLocsWithContextAux cursor C tail →
        (P.n ≤ site.q.val ∧ site.q.val < L) ∧
        ∃ Xr : Circuit (P.n + total), site.suffix = Xr ++ eraseFaults tail ∧
          circuitActsBelow Xr L ∧ circuitActsAbove Xr P.n := by
  induction C with
  | nil => intro cursor tail site hsite; simp [prefixErrLocsWithContextAux] at hsite
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          intro cursor tail site hsite
          have hbelow' : circuitActsBelow (eraseFaults rest) L := by
            intro g' hg' q hq; exact hbelow g' (by simp [eraseFaults, hg']) q hq
          have habove' : circuitActsAbove (eraseFaults rest) P.n := by
            intro g' hg' q hq; exact habove g' (by simp [eraseFaults, hg']) q hq
          have herr' : ∀ q0 : Fin (P.n + total), FInstr.errLoc q0 ∈ rest →
              P.n ≤ q0.val ∧ q0.val < L :=
            fun q0 h => herr q0 (List.mem_cons.mpr (Or.inr h))
          simp only [prefixErrLocsWithContextAux] at hsite
          exact ih hbelow' habove' herr' _ tail site hsite
      | errLoc q0 =>
          intro cursor tail site hsite
          have heF : eraseFaults (FInstr.errLoc q0 :: rest) = eraseFaults rest := by
            simp [eraseFaults]
          have hbelow' : circuitActsBelow (eraseFaults rest) L := heF ▸ hbelow
          have habove' : circuitActsAbove (eraseFaults rest) P.n := heF ▸ habove
          have herr' : ∀ q0' : Fin (P.n + total), FInstr.errLoc q0' ∈ rest →
              P.n ≤ q0'.val ∧ q0'.val < L :=
            fun q0' h => herr q0' (List.mem_cons.mpr (Or.inr h))
          simp only [prefixErrLocsWithContextAux, List.mem_cons] at hsite
          rcases hsite with rfl | hsite
          · refine ⟨herr q0 (List.mem_cons_self ..), eraseFaults rest, rfl, ?_, ?_⟩
            · exact hbelow'
            · exact habove'
          · exact ih hbelow' habove' herr' cursor tail site hsite

/-! ## Stage 2: the pre-coupling segment and the hook branch -/

/-- The Shor gadget block's pre-coupling part (prep + cat cascade + verifier
legs), for cats `c0 :: rest`.  Acts only on cats and the verifier. -/
def shorPreSeg {nq : Nat} (c0 : Fin nq) (rest : List (Fin nq)) (v : Fin nq) : FCircuit nq :=
  orderedCatPrepZ (c0 :: rest) ++ prepP v ++ cnot v c0 ++
    cnot v ((c0 :: rest).getLast (by simp)) ++ hadamard v ++ flagMeasZ v

/-- errLoc marker of a single two-instruction builder `[errLoc a, gate g]`. -/
theorem errLoc_mem_pair {nq : Nat} {a q0 : Fin nq} {g : Gate nq}
    (h : FInstr.errLoc q0 ∈ [FInstr.errLoc a, FInstr.gate g]) : q0 = a := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
    FInstr.errLoc.injEq] at h
  exact h

/-- errLoc markers of a single compiled `cnot`. -/
theorem errLoc_mem_cnot {nq : Nat} {c t q0 : Fin nq} (h : FInstr.errLoc q0 ∈ cnot c t) :
    q0 = c ∨ q0 = t := by
  unfold cnot at h
  by_cases hct : c = t
  · rw [dif_pos hct] at h; exact absurd h (List.not_mem_nil)
  · rw [dif_neg hct] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      FInstr.errLoc.injEq] at h
    exact h

/-- errLoc markers of the pre-coupling segment lie in `cats ∪ {v}`. -/
theorem shorPreSeg_errLoc {nq : Nat} (c0 : Fin nq) (rest : List (Fin nq)) (v : Fin nq)
    (q0 : Fin nq) (h : FInstr.errLoc q0 ∈ shorPreSeg c0 rest v) :
    q0 ∈ (c0 :: rest) ∨ q0 = v := by
  unfold shorPreSeg at h
  simp only [List.mem_append] at h
  have hcat : FInstr.errLoc q0 ∈ orderedCatPrepZ (c0 :: rest) → q0 ∈ (c0 :: rest) := by
    intro hh
    simp only [orderedCatPrepZ, List.mem_append] at hh
    rcases hh with hh | hh
    · rw [(errLoc_mem_pair hh : q0 = c0)]; exact List.mem_cons_self
    · rw [List.mem_flatten] at hh
      obtain ⟨ci, hci, hmem⟩ := hh
      rw [List.mem_map] at hci
      obtain ⟨cc, hcc, rfl⟩ := hci
      rcases errLoc_mem_cnot hmem with rfl | rfl
      · exact (List.of_mem_zip hcc).1
      · exact List.mem_cons_of_mem c0 (List.of_mem_zip hcc).2
  rcases h with ((((hpre | hpp) | hc0) | hlast) | hhad) | hflag
  · exact Or.inl (hcat hpre)
  · exact Or.inr (errLoc_mem_pair hpp)
  · rcases errLoc_mem_cnot hc0 with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl List.mem_cons_self
  · rcases errLoc_mem_cnot hlast with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (List.getLast_mem _)
  · exact Or.inr (errLoc_mem_pair hhad)
  · exact Or.inr (errLoc_mem_pair hflag)

/-- The pre-coupling segment acts below the ceiling `L`. -/
theorem shorPreSeg_cab {nq L : Nat} (c0 : Fin nq) (rest : List (Fin nq)) (v : Fin nq)
    (hcat : ∀ c ∈ (c0 :: rest), c.val < L) (hv : v.val < L) :
    circuitActsBelow (eraseFaults (shorPreSeg c0 rest v)) L := by
  unfold shorPreSeg
  rw [eraseFaults_append, eraseFaults_append, eraseFaults_append, eraseFaults_append,
    eraseFaults_append]
  refine cab_append (cab_append (cab_append (cab_append (cab_append ?_ ?_) ?_) ?_) ?_) ?_
  · exact cab_erase_orderedCatPrepZ (c0 :: rest) hcat
  · exact cab_erase_prepP v hv
  · exact cab_erase_cnot v c0 hv (hcat c0 (List.mem_cons_self))
  · exact cab_erase_cnot v _ hv (hcat _ (List.getLast_mem _))
  · exact cab_erase_hadamard v hv
  · exact cab_erase_flagMeasZ v hv

/-- The pre-coupling segment acts above `P.n` (on helpers only). -/
theorem shorPreSeg_caa {nq n : Nat} (c0 : Fin nq) (rest : List (Fin nq)) (v : Fin nq)
    (hcat : ∀ c ∈ (c0 :: rest), n ≤ c.val) (hv : n ≤ v.val) :
    circuitActsAbove (eraseFaults (shorPreSeg c0 rest v)) n := by
  unfold shorPreSeg
  rw [eraseFaults_append, eraseFaults_append, eraseFaults_append, eraseFaults_append,
    eraseFaults_append]
  refine caa_append (caa_append (caa_append (caa_append (caa_append ?_ ?_) ?_) ?_) ?_) ?_
  · exact caa_erase_orderedCatPrepZ (c0 :: rest) hcat
  · exact caa_erase_prepP v hv
  · exact caa_erase_cnot v c0 hv (hcat c0 (List.mem_cons_self))
  · exact caa_erase_cnot v _ hv (hcat _ (List.getLast_mem _))
  · exact caa_erase_hadamard v hv
  · exact caa_erase_flagMeasZ v hv

/-- errLoc bounds for the pre-coupling segment (the `helperPrefix_site` premise). -/
theorem shorPreSeg_herr {P : QECParams} {total : Nat} (c0 : Fin (P.n + total))
    (rest : List (Fin (P.n + total))) (v : Fin (P.n + total)) (L : Nat)
    (hcat : ∀ c ∈ (c0 :: rest), P.n ≤ c.val ∧ c.val < L) (hv : P.n ≤ v.val ∧ v.val < L) :
    ∀ q0 : Fin (P.n + total), FInstr.errLoc q0 ∈ shorPreSeg c0 rest v →
      P.n ≤ q0.val ∧ q0.val < L :=
  fun q0 h => (shorPreSeg_errLoc c0 rest v q0 h).elim (fun hc => hcat q0 hc) (fun hq => hq ▸ hv)

/-- Zip left-projection is a sublist of the first list. -/
theorem zip_fst_sublist {α β : Type} : ∀ (as : List α) (bs : List β),
    ((List.zip as bs).map Prod.fst).Sublist as := by
  intro as
  induction as with
  | nil => intro bs; simp
  | cons a as' ih =>
      intro bs
      cases bs with
      | nil => simp
      | cons b bs' => simpa using List.Sublist.cons₂ a (ih bs')

/-- **Branch A: a pre-coupling fault site produces a subset hook.**  For a site
in the pre-coupling segment (helpers only), the data residual is pointwise the
schedule kind `kk.toPauli` on a subset of the (lifted) scheduled qubits,
identity elsewhere — because the pre-coupling gates leave the data clean at
coupling entry and the couplings image the cats' Z-parts onto their own data
qubits (`shor_hook_tail_residual`).  The tail guarantee is the conditional
`PreservesDataAbove` at the ceiling, discharged from the acts-below half. -/
theorem shorPRE_site_hook {P : QECParams} {total : Nat}
    (σ' : RuleSchedule (P.n + total)) (kk : XZPauli)
    (hkindL : ∀ s ∈ σ'.slots, s.kind = kk)
    (c0 : Fin (P.n + total)) (rest : List (Fin (P.n + total))) (v : Fin (P.n + total))
    (L : Nat) (hnL : P.n ≤ L)
    (hcatNd : (c0 :: rest).Nodup)
    (hcatA : ∀ c ∈ (c0 :: rest), P.n ≤ c.val) (hcatB : ∀ c ∈ (c0 :: rest), c.val < L)
    (hvA : P.n ≤ v.val) (hvB : v.val < L)
    (hqA : ∀ s ∈ σ'.slots, s.qubit.val < P.n)
    (hqNd : (σ'.slots.map (·.qubit)).Nodup)
    (tail : FCircuit (P.n + total)) (htailPDA : PreservesDataAbove (eraseFaults tail) L)
    (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I)
    (hsite : site ∈ prefixErrLocsWithContextAux cursor (shorPreSeg c0 rest v)
      (((List.zip σ'.slots (c0 :: rest)).map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten
        ++ ((c0 :: rest).map rawMeasZ).flatten ++ tail)) :
    ∀ q' : Fin P.n,
      targetFaultDataResidual P ⟨site, p, hp⟩ q' = Pauli.I ∨
        (targetFaultDataResidual P ⟨site, p, hp⟩ q' = kk.toPauli ∧
          freshDataQ P.n total q' ∈ σ'.slots.map (·.qubit)) := by
  intro q'
  set pairs := List.zip σ'.slots (c0 :: rest) with hpairs
  -- decompose the site through the helper-only pre-coupling segment
  have hcab := shorPreSeg_cab (L := L) c0 rest v hcatB hvB
  have hcaa := shorPreSeg_caa (n := P.n) c0 rest v hcatA hvA
  have hherr := shorPreSeg_herr (P := P) c0 rest v L
    (fun c hc => ⟨hcatA c hc, hcatB c hc⟩) ⟨hvA, hvB⟩
  obtain ⟨⟨hq0A, hq0B⟩, Xr, hsuf, hXrB, hXrA⟩ :=
    helperPrefix_site (shorPreSeg c0 rest v) L hcab hcaa hherr cursor _ site hsite
  -- residual through the suffix
  have hcirc : Xr ++ eraseFaults
        (((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten
          ++ ((c0 :: rest).map rawMeasZ).flatten) ++ tail)
      = Xr ++ (eraseFaults ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)
          ++ (eraseFaults (((c0 :: rest).map rawMeasZ).flatten) ++ eraseFaults tail)) := by
    rw [eraseFaults_append, eraseFaults_append, List.append_assoc]
  set es1 := propagateCircuit Xr ((PCC.cleanAtDetector site.detectorStart).inject site.q p)
    with hes1
  -- coupling-entry state: clean data + clean-above-ceiling
  obtain ⟨hdata, hclean⟩ := preCoupling_to_entry Xr
    (fun g hg q hq => hXrA g hg q hq) L hXrB site.q hq0B hq0A p site.detectorStart
  -- pairs facts
  have hndc : (pairs.map (·.2)).Nodup :=
    (zip_snd_sublist σ'.slots (c0 :: rest)).nodup hcatNd
  have hndq : (pairs.map (·.1.qubit)).Nodup := by
    have hsub : ((pairs.map (·.1)).map (·.qubit)).Sublist (σ'.slots.map (·.qubit)) :=
      (zip_fst_sublist σ'.slots (c0 :: rest)).map _
    rw [List.map_map] at hsub
    exact hsub.nodup hqNd
  have hkindp : ∀ pc ∈ pairs, pc.1.kind = kk := fun pc hpc =>
    hkindL pc.1 (List.of_mem_zip hpc).1
  have hqvals : ∀ pc ∈ pairs, pc.1.qubit.val < P.n := fun pc hpc =>
    hqA pc.1 (List.of_mem_zip hpc).1
  have hcvals : ∀ pc ∈ pairs, P.n ≤ pc.2.val := fun pc hpc =>
    hcatA pc.2 (List.of_mem_zip hpc).2
  have hcatsL : ∀ pc ∈ pairs, pc.2.val < L := fun pc hpc =>
    hcatB pc.2 (List.of_mem_zip hpc).2
  have hmeasL : ∀ c ∈ (c0 :: rest), c.val < L := hcatB
  -- the uniform hook residual
  have hR := shor_hook_tail_residual pairs kk hkindp hndc hndq hqvals hcvals L hcatsL hnL
    (c0 :: rest) hmeasL tail htailPDA es1 hclean hdata q'
  have hval : targetFaultDataResidual P ⟨site, p, hp⟩ q'
      = if freshDataQ P.n total q'
            ∈ (pairs.filter (fun pc => zPart (es1.paulis pc.2) == Pauli.Z)).map (·.1.qubit)
        then kk.toPauli else Pauli.I := by
    show (propagateCircuit site.suffix
        ((PCC.cleanAtDetector site.detectorStart).inject site.q p)).paulis
        (freshDataQ P.n total q') = _
    rw [hsuf, hcirc, QHL.Target.propagateCircuit_append]
    exact hR
  rw [hval]
  by_cases hmem : freshDataQ P.n total q'
      ∈ (pairs.filter (fun pc => zPart (es1.paulis pc.2) == Pauli.Z)).map (·.1.qubit)
  · rw [if_pos hmem]
    refine Or.inr ⟨rfl, ?_⟩
    rw [List.mem_map] at hmem ⊢
    obtain ⟨pc, hpc, hq⟩ := hmem
    rw [List.mem_filter] at hpc
    exact ⟨pc.1, (List.of_mem_zip hpc.1).1, hq⟩
  · rw [if_neg hmem]; exact Or.inl rfl

end QStab.QClifford.Compile
