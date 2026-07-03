import QStab.QClifford.Compile.SurfaceHValid

/-!
# `site_split_gen`: the scheme-generic site split (additive generalization)

The `allNZ` hypothesis of `compileProgramAux_site_split` is replaced by the
per-leaf `LeafClean` bundle: every measurement leaf's compiled block (i) acts
below its own helper ceiling and (ii) preserves data above its own helper
floor.  The `∀es` tail hypothesis becomes the threshold predicate
`PreservesDataAbove`.  NZ satisfies `LeafClean` trivially (its `prep0`
sanitizes the single ancilla, so it preserves data on all states); Shor
satisfies it via the clean-cat form (probe-confirmed, proved at the Shor
call site).

**Additive discipline.**  `compileProgramAux_site_split` (the `allNZ` form)
is left BYTE-IDENTICAL in `SurfaceHValid`; this file only ADDS the generic
lemma and its block-locality / threshold-threading infrastructure.  Nothing
existing is re-routed, so every NZ/HGP consumer is provably unchanged.

Block-locality is a shared `circuitActsBelow` calculus plus a thin per-scheme
assembler (`cab_erase_compileStandardOrdered` / `_compileShorOrdered`); the
per-scheme split exists only because `compileGadgetOrdered` dispatches on
scheme — the compiler's own architecture, not an artifact of this file.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford

/-! keystone (copy of the proven scratch) -/
def gateActsOn {nq : Nat} : Gate nq → Fin nq → Prop
  | .cnot c t _, q => q = c ∨ q = t
  | .hadamard a, q => q = a
  | .prepZero a, q => q = a
  | .prepPlus a, q => q = a
  | .measZ a, q => q = a

theorem propagateGate_paulis_off {nq : Nat} (g : Gate nq) (es : ErrorState nq) (d : Fin nq)
    (h : ¬ gateActsOn g d) : (propagateGate g es).paulis d = es.paulis d := by
  cases g with
  | cnot c t hne =>
      exact propagateGate_cnot_paulis_ne c t hne es d (fun he => h (Or.inl he)) (fun he => h (Or.inr he))
  | hadamard a => exact propagateGate_hadamard_paulis_ne a es d (fun he => h he)
  | prepZero a => exact propagateGate_prepZero_paulis_ne a es d (fun he => h he)
  | prepPlus a => exact propagateGate_prepPlus_paulis_ne a es d (fun he => h he)
  | measZ a => exact propagateGate_measZ_paulis a d es

theorem propagateCircuit_paulis_off {nq : Nat} (c : Circuit nq) (d : Fin nq)
    (h : ∀ g ∈ c, ¬ gateActsOn g d) :
    ∀ es : ErrorState nq, (propagateCircuit c es).paulis d = es.paulis d := by
  induction c with
  | nil => intro es; rfl
  | cons g gs ih =>
      intro es
      rw [propagateCircuit,
        ih (fun g' hg' => h g' (List.mem_cons.mpr (Or.inr hg'))) (propagateGate g es),
        propagateGate_paulis_off g es d (h g (List.mem_cons.mpr (Or.inl rfl)))]

/-! ## `circuitActsBelow` calculus -/
def circuitActsBelow {nq : Nat} (c : Circuit nq) (L : Nat) : Prop :=
  ∀ g ∈ c, ∀ q : Fin nq, gateActsOn g q → q.val < L

theorem cab_nil {nq L : Nat} : circuitActsBelow ([] : Circuit nq) L := by
  intro g hg; exact absurd hg (List.not_mem_nil)

theorem cab_append {nq L : Nat} {a b : Circuit nq}
    (ha : circuitActsBelow a L) (hb : circuitActsBelow b L) :
    circuitActsBelow (a ++ b) L := by
  intro g hg q hq
  rcases List.mem_append.mp hg with h | h
  · exact ha g h q hq
  · exact hb g h q hq

theorem cab_flatten {nq L : Nat} {ls : List (Circuit nq)}
    (h : ∀ c ∈ ls, circuitActsBelow c L) : circuitActsBelow ls.flatten L := by
  intro g hg q hq
  rw [List.mem_flatten] at hg
  obtain ⟨c, hc, hgc⟩ := hg
  exact h c hc g hgc q hq

/-- erase of the base builders, as `circuitActsBelow` facts. -/
theorem cab_erase_prep0 {nq L : Nat} (q : Fin nq) (hq : q.val < L) :
    circuitActsBelow (eraseFaults (prep0 q)) L := by
  intro g hg q' hq'
  simp only [prep0, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl
  cases hq'; exact hq

theorem cab_erase_prepP {nq L : Nat} (q : Fin nq) (hq : q.val < L) :
    circuitActsBelow (eraseFaults (prepP q)) L := by
  intro g hg q' hq'
  simp only [prepP, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl
  cases hq'; exact hq

theorem cab_erase_hadamard {nq L : Nat} (q : Fin nq) (hq : q.val < L) :
    circuitActsBelow (eraseFaults (hadamard q)) L := by
  intro g hg q' hq'
  simp only [hadamard, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl
  cases hq'; exact hq

theorem cab_erase_flagMeasZ {nq L : Nat} (q : Fin nq) (hq : q.val < L) :
    circuitActsBelow (eraseFaults (flagMeasZ q)) L := by
  intro g hg q' hq'
  simp only [flagMeasZ, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl
  cases hq'; exact hq

theorem cab_erase_rawMeasZ {nq L : Nat} (q : Fin nq) (hq : q.val < L) :
    circuitActsBelow (eraseFaults (rawMeasZ q)) L := by
  intro g hg q' hq'
  simp only [rawMeasZ, eraseFaults] at hg
  rcases List.mem_singleton.mp hg with rfl
  cases hq'; exact hq

theorem cab_erase_cnot {nq L : Nat} (c t : Fin nq) (hc : c.val < L) (ht : t.val < L) :
    circuitActsBelow (eraseFaults (cnot c t)) L := by
  intro g hg q' hq'
  unfold cnot at hg
  by_cases h : c = t
  · rw [dif_pos h] at hg; exact absurd hg (List.not_mem_nil)
  · rw [dif_neg h] at hg
    simp only [eraseFaults, List.mem_singleton] at hg
    rcases hg with rfl
    rcases hq' with rfl | rfl
    · exact hc
    · exact ht

/-! ## Composite builders -/
theorem cab_erase_zParitySlot {nq L : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (hanc : anc.val < L) (hq : slot.qubit.val < L) :
    circuitActsBelow (eraseFaults (zParitySlot anc slot)) L := by
  unfold zParitySlot
  cases slot.kind with
  | X =>
      rw [eraseFaults_append, eraseFaults_append]
      exact cab_append (cab_append (cab_erase_hadamard slot.qubit hq)
        (cab_erase_cnot slot.qubit anc hq hanc)) (cab_erase_hadamard slot.qubit hq)
  | Z => exact cab_erase_cnot slot.qubit anc hq hanc

theorem cab_erase_shorCouplingSlot {nq L : Nat} (slot : ScheduledPauli nq) (cat : Fin nq)
    (hcat : cat.val < L) (hq : slot.qubit.val < L) :
    circuitActsBelow (eraseFaults (shorCouplingSlot slot cat)) L := by
  unfold shorCouplingSlot
  cases slot.kind with
  | X =>
      rw [eraseFaults_append, eraseFaults_append]
      exact cab_append (cab_append (cab_erase_hadamard slot.qubit hq)
        (cab_erase_cnot slot.qubit cat hq hcat)) (cab_erase_hadamard slot.qubit hq)
  | Z => exact cab_erase_cnot slot.qubit cat hq hcat

/-- flatten-of-map helper. -/
theorem cab_erase_flatten_map {nq L : Nat} {α : Type} (l : List α) (f : α → FCircuit nq)
    (hf : ∀ a ∈ l, circuitActsBelow (eraseFaults (f a)) L) :
    circuitActsBelow (eraseFaults ((l.map f).flatten)) L := by
  rw [eraseFaults_flatten, List.map_map]
  apply cab_flatten
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨a, ha, rfl⟩ := hc
  exact hf a ha

/-! ## NZ block-locality -/
theorem cab_erase_compileStandardOrdered {nq L : Nat} (sigma : RuleSchedule nq) (anc : Fin nq)
    (hanc : anc.val < L) (hslots : ∀ s ∈ sigma.slots, s.qubit.val < L) :
    circuitActsBelow (eraseFaults (compileStandardOrdered sigma anc)) L := by
  have h1 : compileStandardOrdered sigma anc =
      prep0 anc ++ (sigma.slots.map (zParitySlot anc)).flatten ++ flagMeasZ anc := rfl
  rw [h1, eraseFaults_append, eraseFaults_append]
  refine cab_append (cab_append (cab_erase_prep0 anc hanc) ?_) (cab_erase_flagMeasZ anc hanc)
  exact cab_erase_flatten_map sigma.slots (zParitySlot anc)
    (fun s hs => cab_erase_zParitySlot anc s hanc (hslots s hs))

/-! ## Shor block-locality (structural, parametric in cat/verifier) -/
theorem cab_erase_orderedCatPrepZ {nq L : Nat} (cat : List (Fin nq))
    (hcat : ∀ c ∈ cat, c.val < L) :
    circuitActsBelow (eraseFaults (orderedCatPrepZ cat)) L := by
  cases cat with
  | nil => simp only [orderedCatPrepZ, eraseFaults]; exact cab_nil
  | cons c0 rest =>
      simp only [orderedCatPrepZ]
      rw [eraseFaults_append]
      refine cab_append (cab_erase_prep0 c0 (hcat c0 (List.mem_cons_self ..))) ?_
      apply cab_erase_flatten_map
      intro cc hcc
      have h1 : cc.1 ∈ (c0 :: rest) := List.of_mem_zip hcc |>.1
      have h2 : cc.2 ∈ rest := List.of_mem_zip hcc |>.2
      exact cab_erase_cnot cc.1 cc.2 (hcat cc.1 h1) (hcat cc.2 (List.mem_cons_of_mem c0 h2))

theorem cab_erase_compileShorOrdered {nq L : Nat} (sigma : RuleSchedule nq)
    (cat : List (Fin nq)) (verifier : Fin nq) (hne : cat ≠ [])
    (hcat : ∀ c ∈ cat, c.val < L) (hver : verifier.val < L)
    (hslots : ∀ s ∈ sigma.slots, s.qubit.val < L) :
    circuitActsBelow (eraseFaults (compileShorOrdered sigma cat verifier)) L := by
  obtain ⟨c0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hlast : (c0 :: rest).getLast (by simp) ∈ (c0 :: rest) := List.getLast_mem _
  have hc0 : c0 ∈ (c0 :: rest) := List.mem_cons_self ..
  simp only [compileShorOrdered]
  rw [eraseFaults_append, eraseFaults_append, eraseFaults_append, eraseFaults_append,
    eraseFaults_append, eraseFaults_append, eraseFaults_append]
  refine cab_append (cab_append (cab_append (cab_append (cab_append (cab_append (cab_append
    (cab_erase_orderedCatPrepZ (c0 :: rest) hcat)
    (cab_erase_prepP verifier hver))
    (cab_erase_cnot verifier c0 hver (hcat c0 hc0)))
    (cab_erase_cnot verifier _ hver (hcat _ hlast)))
    (cab_erase_hadamard verifier hver))
    (cab_erase_flagMeasZ verifier hver))
    ?couplings) ?meas
  case couplings =>
    apply cab_erase_flatten_map
    intro sc hsc
    exact cab_erase_shorCouplingSlot sc.1 sc.2 (hcat sc.2 (List.of_mem_zip hsc).2)
      (hslots sc.1 (List.of_mem_zip hsc).1)
  case meas =>
    apply cab_erase_flatten_map
    intro c hc
    exact cab_erase_rawMeasZ c (hcat c hc)

/-! ## Preservation-above corollary -/
theorem preserves_above_of_cab {nq : Nat} (c : Circuit nq) (L : Nat)
    (h : circuitActsBelow c L) (es : ErrorState nq) (d : Fin nq) (hd : L ≤ d.val) :
    (propagateCircuit c es).paulis d = es.paulis d :=
  propagateCircuit_paulis_off c d
    (fun g hg hact => absurd (h g hg d hact) (Nat.not_lt.mpr hd)) es

theorem cab_mono {nq L L' : Nat} {c : Circuit nq}
    (h : circuitActsBelow c L) (hle : L ≤ L') : circuitActsBelow c L' :=
  fun g hg q hq => Nat.lt_of_lt_of_le (h g hg q hq) hle

/-- Program-level acts-below: the whole compiled program acts below `n + start +
programHelperCount program`. -/
theorem compileProgramAux_actsBelow {n total : Nat} (program : XZProgram n)
    (hleaf : ∀ (sc : Scheme) (sg : RuleSchedule n), MeasLeaf program sc sg →
      ∀ (st : Nat) (hf : st + helperCount sc sg ≤ total),
        circuitActsBelow (eraseFaults (compileGadgetBlock sc sg st hf))
            (n + st + helperCount sc sg)) :
    ∀ (start : Nat) (hfit : start + programHelperCount program ≤ total),
      circuitActsBelow (eraseFaults (compileProgramAux start program hfit))
        (n + start + programHelperCount program) := by
  induction program with
  | skip =>
      intro start hfit
      simp only [compileProgramAux, eraseFaults]
      exact cab_nil
  | meas scheme sigma =>
      intro start hfit
      have hfit' : start + helperCount scheme sigma ≤ total := by
        simpa [programHelperCount] using hfit
      have hab := hleaf scheme sigma (MeasLeaf.here _ _) start hfit'
      simpa [programHelperCount] using hab
  | seq first second ihf ihs =>
      intro start hfit
      have H1 : start + programHelperCount first ≤ total := by
        simp only [programHelperCount] at hfit; omega
      have H2 : (start + programHelperCount first) + programHelperCount second ≤ total := by
        simp only [programHelperCount] at hfit; omega
      have hleafF := fun sc sg (hml : MeasLeaf first sc sg) => hleaf sc sg (MeasLeaf.left hml)
      have hleafS := fun sc sg (hml : MeasLeaf second sc sg) => hleaf sc sg (MeasLeaf.right hml)
      simp only [compileProgramAux, eraseFaults_append, programHelperCount]
      refine cab_append (cab_mono (ihf hleafF start H1) (by omega))
        (cab_mono (ihs hleafS (start + programHelperCount first) H2) (by omega))

/-! ## Threshold preservation predicate + threading (#2) -/
def cleanAbove {nq : Nat} (es : ErrorState nq) (L : Nat) : Prop :=
  ∀ h : Fin nq, L ≤ h.val → es.paulis h = Pauli.I

def PreservesDataAbove {n total : Nat} (c : Circuit (n + total)) (L : Nat) : Prop :=
  ∀ es : ErrorState (n + total), cleanAbove es L →
    ∀ d : Fin (n + total), d.val < n → (propagateCircuit c es).paulis d = es.paulis d

theorem cleanAbove_mono {nq : Nat} {es : ErrorState nq} {L L' : Nat}
    (h : cleanAbove es L) (hle : L ≤ L') : cleanAbove es L' :=
  fun q hq => h q (Nat.le_trans hle hq)

theorem PDA_mono {n total : Nat} {c : Circuit (n + total)} {L L' : Nat}
    (h : PreservesDataAbove c L') (hle : L ≤ L') : PreservesDataAbove c L :=
  fun es hc d hd => h es (cleanAbove_mono hc hle) d hd

/-- A block that acts below `L` leaves every qubit `≥ L` fixed, so `cleanAbove`
is preserved across it. -/
theorem cleanAbove_preserved_of_actsBelow {n total : Nat} (c : Circuit (n + total)) (L : Nat)
    (hab : circuitActsBelow c L) (es : ErrorState (n + total)) (hes : cleanAbove es L) :
    cleanAbove (propagateCircuit c es) L := by
  intro h hh
  rw [preserves_above_of_cab c L hab es h hh]
  exact hes h hh

/-- **Program-level threshold threading (#2).**  Given every measurement leaf's
compiled block both acts below its own ceiling and preserves data from any state
in which its own helper block (and everything above) is clean — floor `n + st`,
the weakest form the threading needs, and the strongest a cat-state gadget can
provide: a Shor block does *not* preserve data under junk on its own non-first
cats — the whole compiled program preserves data above `n + start`. -/
theorem compileProgramAux_preservesDataAbove {n total : Nat} (program : XZProgram n)
    (hleaf : ∀ (sc : Scheme) (sg : RuleSchedule n), MeasLeaf program sc sg →
      ∀ (st : Nat) (hf : st + helperCount sc sg ≤ total),
        circuitActsBelow (eraseFaults (compileGadgetBlock sc sg st hf))
            (n + st + helperCount sc sg) ∧
        PreservesDataAbove (eraseFaults (compileGadgetBlock sc sg st hf))
            (n + st)) :
    ∀ (start : Nat) (hfit : start + programHelperCount program ≤ total),
      PreservesDataAbove (eraseFaults (compileProgramAux start program hfit)) (n + start) := by
  induction program with
  | skip =>
      intro start hfit es hc d hd
      simp [compileProgramAux, propagateCircuit]
  | meas scheme sigma =>
      intro start hfit
      have hfit' : start + helperCount scheme sigma ≤ total := by
        simpa [programHelperCount] using hfit
      obtain ⟨_, hpres⟩ := hleaf scheme sigma (MeasLeaf.here _ _) start hfit'
      have : PreservesDataAbove (eraseFaults (compileGadgetBlock scheme sigma start hfit'))
          (n + start) := PDA_mono hpres (by omega)
      intro es hc d hd
      exact this es hc d hd
  | seq first second ihf ihs =>
      intro start hfit es hc d hd
      have H1 : start + programHelperCount first ≤ total := by
        simp only [programHelperCount] at hfit; omega
      have H2 : (start + programHelperCount first) + programHelperCount second ≤ total := by
        simp only [programHelperCount] at hfit; omega
      have hleafF := fun sc sg (hml : MeasLeaf first sc sg) => hleaf sc sg (MeasLeaf.left hml)
      have hleafS := fun sc sg (hml : MeasLeaf second sc sg) => hleaf sc sg (MeasLeaf.right hml)
      -- acts-below for first's whole compiled sub-program (to keep ≥ floor clean)
      have hfirstAB : circuitActsBelow (eraseFaults (compileProgramAux start first H1))
          (n + start + programHelperCount first) :=
        compileProgramAux_actsBelow first
          (fun sc sg hml st hf => (hleafF sc sg hml st hf).1) start H1
      simp only [compileProgramAux, eraseFaults_append, QHL.Target.propagateCircuit_append]
      set esMid := propagateCircuit (eraseFaults (compileProgramAux start first H1)) es with hMid
      -- data preserved by first (at floor n+start)
      have hdF : ∀ d' : Fin (n+total), d'.val < n → esMid.paulis d' = es.paulis d' :=
        fun d' hd' => ihf hleafF start H1 es hc d' hd'
      -- cleanAbove advances to second's floor
      have hcMid0 : cleanAbove esMid (n + start + programHelperCount first) :=
        cleanAbove_preserved_of_actsBelow _ _ hfirstAB es
          (cleanAbove_mono hc (by omega))
      have hcMid : cleanAbove esMid (n + (start + programHelperCount first)) :=
        cleanAbove_mono hcMid0 (by omega)
      have hdS := ihs hleafS (start + programHelperCount first) H2 esMid hcMid d hd
      rw [hdS, hdF d hd]

/-! ## PDA append-advance + site_split_gen (#3) -/
theorem PDA_append_advance {n total : Nat} (a b : Circuit (n + total)) (Llo Lhi : Nat)
    (hle : Llo ≤ Lhi) (haAB : circuitActsBelow a Lhi) (haPDA : PreservesDataAbove a Llo)
    (hbPDA : PreservesDataAbove b Lhi) : PreservesDataAbove (a ++ b) Llo := by
  intro es hc d hd
  rw [QHL.Target.propagateCircuit_append]
  have hmid := cleanAbove_preserved_of_actsBelow a Lhi haAB es (cleanAbove_mono hc hle)
  rw [hbPDA _ hmid d hd, haPDA es hc d hd]

/-- Per-leaf clean bundle: every measurement leaf's block acts below its own
ceiling and preserves data from any state whose own helper block (and
everything above) is clean.  The preservation floor is `n + st` — *not*
`n + st + helperCount` — because a cat-state gadget genuinely needs its own
helpers clean on entry (junk `Z` on a non-first Shor cat backflows onto data
through the coupling CNOTs); the program threading only ever applies a leaf at
states where its helpers are still untouched, so this weaker field suffices. -/
def LeafClean {n total : Nat} (program : XZProgram n) : Prop :=
  ∀ (sc : Scheme) (sg : RuleSchedule n), MeasLeaf program sc sg →
    ∀ (st : Nat) (hf : st + helperCount sc sg ≤ total),
      circuitActsBelow (eraseFaults (compileGadgetBlock sc sg st hf))
          (n + st + helperCount sc sg) ∧
      PreservesDataAbove (eraseFaults (compileGadgetBlock sc sg st hf))
          (n + st)

/-- **The generalized site split (#3).**  Replacing `allNZ` with the per-leaf
`LeafClean` bundle and the `∀es` tail hypothesis with `PreservesDataAbove`. -/
theorem compileProgramAux_site_split_gen {n total : Nat} (program : XZProgram n)
    (hleaf : LeafClean (total := total) program) :
    ∀ (start : Nat) (hfit : start + programHelperCount program ≤ total) (cursor : Nat)
      (tail : FCircuit (n + total)) (site : QStab.QClifford.PCC.ErrLocWithContext (n + total)),
    PreservesDataAbove (eraseFaults tail) (n + start + programHelperCount program) →
    site ∈ prefixErrLocsWithContextAux cursor (compileProgramAux start program hfit) tail →
    ∃ (scheme : Scheme) (sigma : RuleSchedule n) (gstart gcursor : Nat)
      (gtail : FCircuit (n + total)) (ghfit : gstart + helperCount scheme sigma ≤ total),
      MeasLeaf program scheme sigma ∧
      PreservesDataAbove (eraseFaults gtail) (n + gstart + helperCount scheme sigma) ∧
      site ∈ prefixErrLocsWithContextAux gcursor
        (compileGadgetBlock scheme sigma gstart ghfit) gtail := by
  induction program with
  | skip =>
      intro start hfit cursor tail site _ hsite
      simp only [compileProgramAux, prefixErrLocsWithContextAux, List.not_mem_nil] at hsite
  | meas scheme sigma =>
      intro start hfit cursor tail site htail hsite
      exact ⟨scheme, sigma, start, cursor, tail, hfit, MeasLeaf.here _ _, htail, hsite⟩
  | seq first second ihf ihs =>
      intro start hfit cursor tail site htail hsite
      have H1 : start + programHelperCount first ≤ total := by
        simp only [programHelperCount] at hfit; omega
      have H2 : (start + programHelperCount first) + programHelperCount second ≤ total := by
        simp only [programHelperCount] at hfit; omega
      have hleafF : LeafClean (total := total) first :=
        fun sc sg hml => hleaf sc sg (MeasLeaf.left hml)
      have hleafS : LeafClean (total := total) second :=
        fun sc sg hml => hleaf sc sg (MeasLeaf.right hml)
      simp only [compileProgramAux, prefixErrLocs_append, List.mem_append] at hsite
      rcases hsite with hleft | hright
      · have htail' : PreservesDataAbove
            (eraseFaults (compileProgramAux (start + programHelperCount first) second H2 ++ tail))
            (n + start + programHelperCount first) := by
          rw [eraseFaults_append]
          refine PDA_append_advance _ _ (n + start + programHelperCount first)
            (n + start + programHelperCount first + programHelperCount second)
            (by omega) ?_ ?_ ?_
          · have := compileProgramAux_actsBelow second
              (fun sc sg hml st hf => (hleafS sc sg hml st hf).1)
              (start + programHelperCount first) H2
            have he : n + (start + programHelperCount first) + programHelperCount second
                = n + start + programHelperCount first + programHelperCount second := by omega
            rw [he] at this; exact this
          · have := compileProgramAux_preservesDataAbove second hleafS
              (start + programHelperCount first) H2
            have he : n + (start + programHelperCount first)
                = n + start + programHelperCount first := by omega
            rw [he] at this; exact this
          · have he : n + start + programHelperCount (XZProgram.seq first second)
                = n + start + programHelperCount first + programHelperCount second := by
              simp only [programHelperCount]; omega
            rw [he] at htail; exact htail
        obtain ⟨sc, sg, gs, gc, gt, gh, hml, hgt, hgm⟩ :=
          ihf hleafF start H1 cursor _ site htail' hleft
        exact ⟨sc, sg, gs, gc, gt, gh, MeasLeaf.left hml, hgt, hgm⟩
      · have htail2 : PreservesDataAbove (eraseFaults tail)
            (n + (start + programHelperCount first) + programHelperCount second) := by
          have he : n + (start + programHelperCount first) + programHelperCount second
              = n + start + programHelperCount (XZProgram.seq first second) := by
            simp only [programHelperCount]; omega
          rw [he]; exact htail
        obtain ⟨sc, sg, gs, gc, gt, gh, hml, hgt, hgm⟩ :=
          ihs hleafS (start + programHelperCount first) H2 _ tail site htail2 hright
        exact ⟨sc, sg, gs, gc, gt, gh, MeasLeaf.right hml, hgt, hgm⟩

-- Regression guards (axiom pins).
/-- info: 'QStab.QClifford.Compile.propagateCircuit_paulis_off' depends on axioms: [propext] -/
#guard_msgs in
#print axioms propagateCircuit_paulis_off

/-- info: 'QStab.QClifford.Compile.cab_erase_compileStandardOrdered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cab_erase_compileStandardOrdered

/-- info: 'QStab.QClifford.Compile.cab_erase_compileShorOrdered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cab_erase_compileShorOrdered

/-- info: 'QStab.QClifford.Compile.compileProgramAux_preservesDataAbove' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compileProgramAux_preservesDataAbove

/-- info: 'QStab.QClifford.Compile.compileProgramAux_site_split_gen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compileProgramAux_site_split_gen

end QStab.QClifford.Compile
