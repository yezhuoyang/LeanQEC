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

/-- **Predicate-generic prefix-site decomposition.**  Every fault site of a
circuit whose errLoc markers and acted-on qubits all satisfy `S` has `S site.q`
and a suffix `Ys ++ eraseFaults tail` with `Ys` again acting within `S`. -/
theorem prefixSite_local {P : QECParams} {total : Nat} (C : FCircuit (P.n + total))
    (S : Fin (P.n + total) → Prop)
    (hgates : ∀ g ∈ eraseFaults C, ∀ q : Fin (P.n + total), gateActsOn g q → S q)
    (herr : ∀ q0 : Fin (P.n + total), FInstr.errLoc q0 ∈ C → S q0) :
    ∀ (cursor : Nat) (tail : FCircuit (P.n + total))
      (site : PCC.ErrLocWithContext (P.n + total)),
      site ∈ prefixErrLocsWithContextAux cursor C tail →
        S site.q ∧ ∃ Ys : Circuit (P.n + total), site.suffix = Ys ++ eraseFaults tail ∧
          (∀ g ∈ Ys, ∀ q : Fin (P.n + total), gateActsOn g q → S q) := by
  induction C with
  | nil => intro cursor tail site hsite; simp [prefixErrLocsWithContextAux] at hsite
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          intro cursor tail site hsite
          have hgates' : ∀ g' ∈ eraseFaults rest, ∀ q, gateActsOn g' q → S q :=
            fun g' hg' q hq => hgates g' (by simp [eraseFaults, hg']) q hq
          have herr' : ∀ q0, FInstr.errLoc q0 ∈ rest → S q0 :=
            fun q0 h => herr q0 (List.mem_cons.mpr (Or.inr h))
          simp only [prefixErrLocsWithContextAux] at hsite
          exact ih hgates' herr' _ tail site hsite
      | errLoc q0 =>
          intro cursor tail site hsite
          have heF : eraseFaults (FInstr.errLoc q0 :: rest) = eraseFaults rest := by
            simp [eraseFaults]
          have hgates' : ∀ g' ∈ eraseFaults rest, ∀ q, gateActsOn g' q → S q := heF ▸ hgates
          have herr' : ∀ q0', FInstr.errLoc q0' ∈ rest → S q0' :=
            fun q0' h => herr q0' (List.mem_cons.mpr (Or.inr h))
          simp only [prefixErrLocsWithContextAux, List.mem_cons] at hsite
          rcases hsite with rfl | hsite
          · exact ⟨herr q0 (List.mem_cons_self ..), eraseFaults rest, rfl, hgates'⟩
          · exact ih hgates' herr' cursor tail site hsite

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

/-- errLoc markers of one coupling slot lie in `{slot.qubit, cat}`. -/
theorem shorCouplingSlot_errLoc {nq : Nat} (slot : ScheduledPauli nq) (cat q0 : Fin nq)
    (h : FInstr.errLoc q0 ∈ shorCouplingSlot slot cat) : q0 = slot.qubit ∨ q0 = cat := by
  obtain ⟨sk, sq⟩ := slot
  cases sk with
  | X =>
      simp only [shorCouplingSlot, List.append_assoc, List.mem_append] at h
      rcases h with hh | hh | hh
      · exact Or.inl (errLoc_mem_pair hh)
      · exact errLoc_mem_cnot hh
      · exact Or.inl (errLoc_mem_pair hh)
  | Z => exact errLoc_mem_cnot h

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

/-! ## Stage 3: the coupling / measurement branch (weight ≤ 1) -/

/-- **Branch B: a coupling or measurement fault site has weight-`≤ 1` residual.**
The fault touches a single pair (its data qubit and cat); the rest of that pair
localizes to those two qubits, the later couplings run on clean cats (so they
preserve the data block), and the measurements / tail preserve data.  Hence the
residual is supported on the one pair's data qubit. -/
theorem shorCOUP_site_wle1 {P : QECParams} {total : Nat}
    (measCats : List (Fin (P.n + total))) (tail : FCircuit (P.n + total)) (L : Nat)
    (hnL : P.n ≤ L) (htailPDA : PreservesDataAbove (eraseFaults tail) L)
    (hmeasB : ∀ c ∈ measCats, c.val < L) :
    ∀ (pairs : List (ScheduledPauli (P.n + total) × Fin (P.n + total)))
      (hqA : ∀ pc ∈ pairs, pc.1.qubit.val < P.n)
      (hcA : ∀ pc ∈ pairs, P.n ≤ pc.2.val) (hcB : ∀ pc ∈ pairs, pc.2.val < L)
      (hcNd : (pairs.map (·.2)).Nodup)
      (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I),
      site ∈ prefixErrLocsWithContextAux cursor
        ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)
        (((measCats.map rawMeasZ).flatten) ++ tail) →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 := by
  intro pairs
  induction pairs with
  | nil => intro _ _ _ _ cursor site p hp hsite; simp [prefixErrLocsWithContextAux] at hsite
  | cons p0 rest ih =>
      intro hqA hcA hcB hcNd cursor site p hp hsite
      have hcirc : ((p0 :: rest).map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten
          = shorCouplingSlot p0.1 p0.2 ++
            (rest.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten := by
        simp only [List.map_cons, List.flatten_cons]
      rw [hcirc, prefixErrLocs_append, List.mem_append] at hsite
      have hqA' : ∀ pc ∈ rest, pc.1.qubit.val < P.n := fun pc h => hqA pc (List.mem_cons_of_mem _ h)
      have hcA' : ∀ pc ∈ rest, P.n ≤ pc.2.val := fun pc h => hcA pc (List.mem_cons_of_mem _ h)
      have hcB' : ∀ pc ∈ rest, pc.2.val < L := fun pc h => hcB pc (List.mem_cons_of_mem _ h)
      have hcNd0 : (p0.2 :: rest.map (·.2)).Nodup := hcNd
      have hcNd' : (rest.map (·.2)).Nodup := (List.nodup_cons.mp hcNd0).2
      have hfresh0 : p0.2 ∉ rest.map (·.2) := (List.nodup_cons.mp hcNd0).1
      rcases hsite with hleft | hright
      · -- Case A: the fault is in `p0`'s own coupling slot
        set S : Fin (P.n + total) → Prop := fun q => q = p0.1.qubit ∨ q = p0.2 with hS
        obtain ⟨hSq, Ys, hsuf, hYs⟩ :=
          prefixSite_local (shorCouplingSlot p0.1 p0.2) S
            (fun g hg q hq => shorCouplingSlot_gates_actOn p0.1 p0.2 g hg q hq)
            (fun q0 h => shorCouplingSlot_errLoc p0.1 p0.2 q0 h) cursor _ site hleft
        -- bounds
        have hq0lt : p0.1.qubit.val < P.n := hqA p0 List.mem_cons_self
        have hSlt : ∀ q, S q → q.val < L := by
          intro q hq; rcases hq with rfl | rfl
          · exact lt_of_lt_of_le hq0lt hnL
          · exact hcB p0 List.mem_cons_self
        have hSqL : site.q.val < L := hSlt site.q hSq
        -- the affected data qubit
        refine weight_le_one_of_single _ ⟨p0.1.qubit.val, hq0lt⟩ ?_
        intro q' hq'
        have hqne : freshDataQ P.n total q' ≠ p0.1.qubit := by
          intro he
          apply hq'; apply Fin.ext
          simpa [freshDataQ_val] using congrArg Fin.val he
        have hqnc : freshDataQ P.n total q' ≠ p0.2 := by
          refine Fin.ne_of_val_ne ?_
          have h1 := q'.isLt
          have h2 := hcA p0 List.mem_cons_self
          simp only [freshDataQ_val]
          omega
        have hqnS : ¬ S (freshDataQ P.n total q') := fun h => h.elim hqne hqnc
        show (propagateCircuit site.suffix
            ((PCC.cleanAtDetector site.detectorStart).inject site.q p)).paulis
            (freshDataQ P.n total q') = Pauli.I
        set es0 := (PCC.cleanAtDetector site.detectorStart).inject site.q p with hes0
        rw [hsuf, eraseFaults_append, eraseFaults_append, QHL.Target.propagateCircuit_append]
        set esA := propagateCircuit Ys es0 with hesA
        have hp02L : p0.2.val < L := hcB p0 List.mem_cons_self
        have hes0_off : ∀ d : Fin (P.n + total), ¬ S d → es0.paulis d = Pauli.I := by
          intro d hd
          have hcond : ¬ (d = site.q) := fun he => hd (by rw [he]; exact hSq)
          rw [hes0, injectClean_paulis, if_neg hcond]
        have hYsBelow : circuitActsBelow Ys L :=
          fun g hg q hq => hSlt q (hYs g hg q hq)
        have hesA_off : ∀ d : Fin (P.n + total), ¬ S d → esA.paulis d = Pauli.I := by
          intro d hd
          rw [hesA, propagateCircuit_paulis_off Ys d (fun g hg hq => hd (hYs g hg d hq)) es0]
          exact hes0_off d hd
        have hcleanA : cleanAbove esA L := by
          rw [hesA]
          refine cleanAbove_preserved_of_actsBelow Ys L hYsBelow es0 ?_
          intro h hh
          refine hes0_off h ?_
          rintro (rfl | rfl) <;> omega
        have hZfree : ∀ c' ∈ rest.map (·.2), zPart (esA.paulis c') = Pauli.I := by
          intro c' hc'
          have hnotS : ¬ S c' := by
            rintro (rfl | rfl)
            · rw [List.mem_map] at hc'; obtain ⟨pc', hpc', he⟩ := hc'
              have := hcA' pc' hpc'; rw [he] at this; omega
            · exact hfresh0 hc'
          rw [hesA_off c' hnotS]; rfl
        have hdisj : ∀ pc ∈ rest, ∀ c' ∈ rest.map (·.2), pc.1.qubit ≠ c' := by
          intro pc hpc c' hc'
          rw [List.mem_map] at hc'
          obtain ⟨pc', hpc', rfl⟩ := hc'
          exact Fin.ne_of_val_ne (by have := hqA' pc hpc; have := hcA' pc' hpc'; omega)
        have hfreshNc : freshDataQ P.n total q' ∉ rest.map (·.2) := by
          intro hmem; rw [List.mem_map] at hmem
          obtain ⟨pc', hpc', he⟩ := hmem
          have hge : P.n ≤ pc'.2.val := hcA' pc' hpc'
          rw [he] at hge; simp only [freshDataQ_val] at hge
          have := q'.isLt; omega
        -- stage restCoup
        rw [QHL.Target.propagateCircuit_append]
        set esB := propagateCircuit
          (eraseFaults ((rest.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)) esA with hesB
        have hesB_data : esB.paulis (freshDataQ P.n total q') = Pauli.I := by
          rw [hesB, shorCouplings_preserve_data rest hcNd' hdisj esA hZfree
            (freshDataQ P.n total q') hfreshNc]
          exact hesA_off _ hqnS
        have hcleanB : cleanAbove esB L := by
          rw [hesB]
          refine cleanAbove_preserved_of_actsBelow _ L ?_ esA hcleanA
          apply cab_erase_flatten_map
          intro pc hpc
          exact cab_erase_shorCouplingSlot pc.1 pc.2 (hcB' pc hpc)
            (lt_of_lt_of_le (hqA' pc hpc) hnL)
        -- stage measSeg
        rw [QHL.Target.propagateCircuit_append]
        set esC := propagateCircuit (eraseFaults ((measCats.map rawMeasZ).flatten)) esB with hesC
        have hesC_data : esC.paulis (freshDataQ P.n total q') = Pauli.I := by
          rw [hesC, rawMeasZ_flatten_paulis, hesB_data]
        have hcleanC : cleanAbove esC L := by
          rw [hesC]
          refine cleanAbove_preserved_of_actsBelow _ L ?_ esB hcleanB
          apply cab_erase_flatten_map
          intro c hc
          exact cab_erase_rawMeasZ c (hmeasB c hc)
        -- stage tail
        rw [htailPDA esC hcleanC (freshDataQ P.n total q') q'.isLt]
        exact hesC_data
      · -- Case B: the fault is in a later coupling slot — recurse
        exact ih hqA' hcA' hcB' hcNd' _ site p hp hright

/-- **Branch B′: a raw-measurement fault site has weight-`0` residual.**  The
measurement gates act only on cats (`≥ P.n`), never on data, and the tail
preserves data. -/
theorem shorMEAS_site_wle1 {P : QECParams} {total : Nat}
    (measCats : List (Fin (P.n + total))) (tail : FCircuit (P.n + total)) (L : Nat)
    (htailPDA : PreservesDataAbove (eraseFaults tail) L)
    (hmeasA : ∀ c ∈ measCats, P.n ≤ c.val) (hmeasB : ∀ c ∈ measCats, c.val < L)
    (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I)
    (hsite : site ∈ prefixErrLocsWithContextAux cursor
      ((measCats.map rawMeasZ).flatten) tail) :
    ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 := by
  have hgates : ∀ g ∈ eraseFaults ((measCats.map rawMeasZ).flatten),
      ∀ q : Fin (P.n + total), gateActsOn g q → q ∈ measCats := by
    intro g hg q hq
    rw [eraseFaults_flatten, List.map_map, List.mem_flatten] at hg
    obtain ⟨c, hc, hgc⟩ := hg
    rw [List.mem_map] at hc; obtain ⟨cc, hcc, rfl⟩ := hc
    simp only [Function.comp_apply, rawMeasZ, eraseFaults, List.mem_singleton] at hgc
    subst hgc; cases hq; exact hcc
  have herr : ∀ q0 : Fin (P.n + total),
      FInstr.errLoc q0 ∈ (measCats.map rawMeasZ).flatten → q0 ∈ measCats := by
    intro q0 h
    rw [List.mem_flatten] at h; obtain ⟨c, hc, hmem⟩ := h
    rw [List.mem_map] at hc; obtain ⟨cc, hcc, rfl⟩ := hc
    rw [errLoc_mem_pair hmem]; exact hcc
  obtain ⟨hSq, Ys, hsuf, hYs⟩ :=
    prefixSite_local ((measCats.map rawMeasZ).flatten) (· ∈ measCats) hgates herr
      cursor tail site hsite
  have hall : ∀ q' : Fin P.n, targetFaultDataResidual P ⟨site, p, hp⟩ q' = Pauli.I := by
    intro q'
    have hqnS : freshDataQ P.n total q' ∉ measCats := by
      intro hm
      have hge : P.n ≤ (freshDataQ P.n total q').val := hmeasA _ hm
      simp only [freshDataQ_val] at hge
      have := q'.isLt; omega
    show (propagateCircuit site.suffix
        ((PCC.cleanAtDetector site.detectorStart).inject site.q p)).paulis
        (freshDataQ P.n total q') = Pauli.I
    set es0 := (PCC.cleanAtDetector site.detectorStart).inject site.q p with hes0
    rw [hsuf, QHL.Target.propagateCircuit_append]
    set esA := propagateCircuit Ys es0 with hesA
    have hSqL : site.q.val < L := hmeasB site.q hSq
    have hYsBelow : circuitActsBelow Ys L := fun g hg q hq => hmeasB q (hYs g hg q hq)
    have hcondf : ¬ (freshDataQ P.n total q' = site.q) :=
      fun he => hqnS (by rw [he]; exact hSq)
    have hesA_data : esA.paulis (freshDataQ P.n total q') = Pauli.I := by
      rw [hesA, propagateCircuit_paulis_off Ys _ (fun g hg hq => hqnS (hYs g hg _ hq)) es0,
        hes0, injectClean_paulis, if_neg hcondf]
    have hcleanA : cleanAbove esA L := by
      rw [hesA]
      refine cleanAbove_preserved_of_actsBelow Ys L hYsBelow es0 ?_
      intro h hh
      have hcond : ¬ (h = site.q) := fun he => by rw [he] at hh; omega
      rw [hes0, injectClean_paulis, if_neg hcond]
    rw [htailPDA esA hcleanA (freshDataQ P.n total q') q'.isLt, hesA_data]
  have h0 : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) = 0 :=
    weight_zero_of_allI _ hall
  omega

end QStab.QClifford.Compile
