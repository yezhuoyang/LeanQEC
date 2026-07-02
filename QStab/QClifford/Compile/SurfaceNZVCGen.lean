import QStab.QClifford.Compile.SurfaceHValid

/-!
# Milestone 4b: packaging the closed distance content as the VCGen discharge

`SurfaceHValid.lean` closed pieces 2–4a: the compiled Surface/NZ circuit satisfies the
compiled barrier invariant and the bar-Z circuit-level distance
(`surface_compiled_barZ_distance`).  This file packages that content against the
independent VCGen verifier — the `Safe` predicate of `QStab.QClifford.PCC` — for the
distance-parametric code spec, discharging every slot that does *not* have its own
open milestone.

The verifier's obligation set is `[programEq, wf, syn, ftDistance, reach]`.  Two slots
are deferred to their own milestones:

* **`ftDistance`** — the fault-tolerance distance lift (C1).  We deliver honest partial
  progress here: piece (2) schedule faithfulness, piece (3) the `logicalFailure`
  alignment, and piece (4) the *bar-Z-restricted* ftDistance obligation derived from
  `surface_compiled_barZ_distance`.  The FULL `ftDistance` slot additionally needs
  any-logical (bar-X) coverage — its own milestone; we do NOT weaken the CodeSpec
  failure predicate to make it pass early.
* **`reach`** — the parametric reach witness.

The remaining three slots (`programEq`, `wf`, `syn`) are discharged here for the
distance-parametric spec `fullProgramCodeSpecD` (which kills the `d := 1` hardcode of
`fullProgramCodeSpec` additively, without touching that def or its slot theorems).

## Map (per-item status)
* **Piece (1) — DONE, axiom-free.**  `fullProgramCodeSpecD`, `fullProgramVCInputD` /
  `generatedFullProgramVCInputD`, and the three slot theorems `..._programEqD / _wfD /
  _synD` (+ `generatedFullProgramSyndromeHoareCertificateD`).  The existing proofs
  transfer verbatim: no slot denotation reads `spec.d`.
* **Capstone — DONE, axiom-free.**  `programCompiled_Safe_of_ftDistance_reach` (generic)
  and `surfaceNZ_Safe_of_ftDistance_reach` (surface instance): full `Safe` from the three
  discharged slots plus the two deferred slot obligations as hypotheses.
* **Piece (2) — DONE, axiom-clean.**  `scheduleRow_eval_uniform` (reusable foldl collapse)
  and its surface instances `scheduleRow_nzSchedule_dataRestrict` (= `mkSurfaceStabilizers`
  on data) / `scheduleRow_nzSchedule_helperTrivial` (= `I` on helpers).
* **Piece (3) — DONE, axiom-clean.**  `compiled_centralizer_transport` transports the
  `Centralizer` half; the `Stab`-half transport (`surfaceNZ_Stab_iff_InStab`) and the
  schedule alignment (`surfaceXZProgram_schedule_get`, `programNumStab_surfaceXZProgram`)
  landed in `SurfaceNZStabTransport.lean` / `SurfaceNZSpecAlign.lean`, giving the full
  `surfaceNZ_logicalFailure_iff` consumed by `SurfaceNZFtDistance.lean`.
* **Piece (4) — SCOPED, not weakened.**  The bar-Z circuit-level distance is already
  closed as `surface_compiled_barZ_distance` (over `surfaceCircuit d hd`, which is
  definitionally `compileProgram (surfaceXZProgram d hd)`).  Turning it into the
  `ftDistance` slot needs piece (3)'s iff to relate `(surfaceLogicalClass …).contains` to
  `logicalFailure`, and — crucially — the **any-logical (bar-X) coverage** for the other
  logical class (`mkSurfaceLogicalX` + coverage lemma + the X-side circuit barrier).  The
  `CodeSpec` failure predicate is left exactly as the verifier defines it; nothing is
  weakened to make the slot pass early.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric

/-! ## Piece (1): the distance-parametric code spec and its discharged slots

`fullProgramCodeSpecD` is `fullProgramCodeSpec` with the `d := 1` hardcode replaced by a
caller-supplied `dist`.  Because the record update touches only `d` / `d_pos`, every
other field (`numStab`, `gadget`, `stabilizer`, `expectedProgram`, …) is *definitionally*
the original; the `programEq` / `wf` / `syn` obligations never mention `spec.d`, so the
existing proofs transfer verbatim. -/

/-- Distance-parametric full-program code spec: `fullProgramCodeSpec` with an arbitrary
positive distance `dist` in place of the `d := 1` hardcode. -/
def fullProgramCodeSpecD {n : Nat} (program : XZProgram n)
    (hdisjoint : fullProgramReadoutDisjoint program) (dist : Nat) (hdist : 0 < dist) :
    CodeSpec (n + programHelperCount program) :=
  { fullProgramCodeSpec program hdisjoint with d := dist, d_pos := hdist }

/-- `specCircuit` ignores `spec.d`, so the D-variant produces the same circuit. -/
theorem specCircuit_fullProgramCodeSpecD {n : Nat} (program : XZProgram n)
    (hdisjoint : fullProgramReadoutDisjoint program) (dist : Nat) (hdist : 0 < dist) :
    specCircuit (fullProgramCodeSpecD program hdisjoint dist hdist) = compileProgram program :=
  specCircuit_fullProgramCodeSpec program hdisjoint

/-- VC input built from the distance-parametric spec. -/
def fullProgramVCInputD {n : Nat} (program : XZProgram n)
    (hdisjoint : fullProgramReadoutDisjoint program) (dist : Nat) (hdist : 0 < dist)
    (hnq : 0 < n + programHelperCount program)
    (hnumStab : 0 < programNumStab program) :
    VCInput (n + programHelperCount program) :=
  VCInput.ofPCC (compileProgram program) (fullProgramCodeSpecD program hdisjoint dist hdist)
    .unconditional hnq hnumStab

theorem fullProgram_vcgen_programEqD {n : Nat} (program : XZProgram n)
    (hdisjoint : fullProgramReadoutDisjoint program) (dist : Nat) (hdist : 0 < dist)
    (hnq : 0 < n + programHelperCount program) (hnumStab : 0 < programNumStab program) :
    (vcgen (fullProgramVCInputD program hdisjoint dist hdist hnq hnumStab)).denoteSlot
      .programEq := by
  simpa [vcgen, GeneratedVCs.denoteSlot, VCSlot.denote, fullProgramVCInputD,
    VCInput.toCodeSpec_ofPCC] using
    (specCircuit_fullProgramCodeSpecD program hdisjoint dist hdist).symm

theorem fullProgram_vcgen_wfD {n : Nat} (program : XZProgram n)
    (hdisjoint : fullProgramReadoutDisjoint program) (dist : Nat) (hdist : 0 < dist)
    (hnq : 0 < n + programHelperCount program) (hnumStab : 0 < programNumStab program) :
    (vcgen (fullProgramVCInputD program hdisjoint dist hdist hnq hnumStab)).denoteSlot .wf := by
  change WellFormed (compileProgram program) (fullProgramCodeSpecD program hdisjoint dist hdist)
  rfl

/-- The "generated" (auto-disjoint) distance-parametric VC input. -/
def generatedFullProgramVCInputD {n : Nat} (program : XZProgram n) (dist : Nat) (hdist : 0 < dist)
    (hnq : 0 < n + programHelperCount program) (hnumStab : 0 < programNumStab program) :
    VCInput (n + programHelperCount program) :=
  fullProgramVCInputD program (fullProgramReadoutDisjoint_auto program) dist hdist hnq hnumStab

theorem generatedFullProgram_vcgen_programEqD {n : Nat} (program : XZProgram n) (dist : Nat)
    (hdist : 0 < dist) (hnq : 0 < n + programHelperCount program)
    (hnumStab : 0 < programNumStab program) :
    (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot
      .programEq :=
  fullProgram_vcgen_programEqD program (fullProgramReadoutDisjoint_auto program) dist hdist
    hnq hnumStab

theorem generatedFullProgram_vcgen_wfD {n : Nat} (program : XZProgram n) (dist : Nat)
    (hdist : 0 < dist) (hnq : 0 < n + programHelperCount program)
    (hnumStab : 0 < programNumStab program) :
    (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot .wf :=
  fullProgram_vcgen_wfD program (fullProgramReadoutDisjoint_auto program) dist hdist hnq hnumStab

/-- Syndrome Hoare certificate for the D-variant: the gadget Hoare derivations are
`d`-independent, so they transfer from the non-parametric certificate. -/
def generatedFullProgramSyndromeHoareCertificateD {n : Nat} (program : XZProgram n) (dist : Nat)
    (hdist : 0 < dist) (hnq : 0 < n + programHelperCount program)
    (hnumStab : 0 < programNumStab program) :
    SyndromeHoareCertificate (generatedFullProgramVCInputD program dist hdist hnq hnumStab) where
  programEq := generatedFullProgram_vcgen_programEqD program dist hdist hnq hnumStab
  wf := generatedFullProgram_vcgen_wfD program dist hdist hnq hnumStab
  deriv := (generatedFullProgramSyndromeHoareCertificate program hnq hnumStab).deriv

theorem generatedFullProgram_vcgen_synD {n : Nat} (program : XZProgram n) (dist : Nat)
    (hdist : 0 < dist) (hnq : 0 < n + programHelperCount program)
    (hnumStab : 0 < programNumStab program) :
    (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot .syn :=
  (generatedFullProgramSyndromeHoareCertificateD program dist hdist hnq hnumStab).syn

/-! ## Capstone (generic): `Safe` minus the two deferred slots

Given the two deferred slot obligations (`ftDistance` and `reach`) as hypotheses, the
three discharged slots assemble — through `VCGen.ofSyndromeHoareCertificate` and the
trusted `vcgen_sound` — into full `Safe` for the compiled program against the
distance-parametric spec. -/
theorem programCompiled_Safe_of_ftDistance_reach {n : Nat} (program : XZProgram n) (dist : Nat)
    (hdist : 0 < dist) (hnq : 0 < n + programHelperCount program)
    (hnumStab : 0 < programNumStab program)
    (ftD : (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot
      .ftDistance)
    (reachScript : List (Option Pauli))
    (reachOk : (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot
      .reach reachScript) :
    Safe (compileProgram program)
      (fullProgramCodeSpecD program (fullProgramReadoutDisjoint_auto program) dist hdist) :=
  vcgen_sound (VCGen.ofSyndromeHoareCertificate
    (generatedFullProgramSyndromeHoareCertificateD program dist hdist hnq hnumStab)
    ftD reachScript reachOk)

/-! ## Piece (2): schedule faithfulness

The compiled spec's `i`-th stabilizer row is `scheduleRow (nzSchedule d hd i)`, the
phase-free product of one singleton row per scheduled slot.  For a CSS-uniform schedule
with `Nodup` qubit support (both true of `nzSchedule`), that product collapses to "the
CSS kind on the scheduled support, identity elsewhere" — which is exactly
`nzSuffixResidual … 0`, hence (`nzSuffixResidual_zero_eq_mkSurfaceStabilizers`) the
surface stabilizer `mkSurfaceStabilizers d hd i` on data qubits, and `I` on helpers. -/

private lemma Pmul_I_left (x : Pauli) : Pauli.mul Pauli.I x = x := by
  rw [← pauliMul_eq_mul]; exact pauliMul_I_left x

private lemma Pmul_I_right (x : Pauli) : Pauli.mul x Pauli.I = x := by
  rw [← pauliMul_eq_mul]; exact pauliMul_I_right x

/-- Evaluate a `scheduleRow`-style `ErrorVec.mul` fold at a single point `q`: the fold of
`ErrorVec` products becomes a fold of pointwise `Pauli.mul`s. -/
private theorem foldl_scheduleSlotRow_eval {n k : Nat} (q : Fin (n + k)) :
    ∀ (slots : List (ScheduledPauli n)) (base : ErrorVec (n + k)),
      (slots.foldl (fun acc slot => ErrorVec.mul acc (scheduleSlotRow (k := k) slot)) base) q =
        slots.foldl (fun acc slot => Pauli.mul acc (scheduleSlotRow (k := k) slot q)) (base q) := by
  intro slots
  induction slots with
  | nil => intro base; rfl
  | cons slot rest ih =>
      intro base
      simp only [List.foldl_cons]
      rw [ih (ErrorVec.mul base (scheduleSlotRow (k := k) slot))]
      rfl

/-- **Foldl collapse for a uniform, `Nodup`-keyed contribution list.**  A left fold of
`Pauli.mul` whose per-element contribution is `K` on a unique matching key and `I`
elsewhere evaluates to `K` if some element matches `q`, and `I` otherwise. -/
private theorem foldl_singleKind {α : Type} {m : Nat} (K : Pauli) (key : α → Fin m)
    (val : α → Pauli) (q : Fin m) :
    ∀ (l : List α), (l.map key).Nodup → (∀ a ∈ l, val a = K) → ∀ base : Pauli,
      l.foldl (fun acc a => Pauli.mul acc (if q = key a then val a else Pauli.I)) base =
        Pauli.mul base (if l.any (fun a => decide (key a = q)) then K else Pauli.I) := by
  intro l
  induction l with
  | nil => intro _ _ base; exact (Pmul_I_right base).symm
  | cons a rest ih =>
      intro hnd hval base
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnotin, hndrest⟩ := hnd
      have hvala : val a = K := hval a (List.mem_cons_self ..)
      have hvalrest : ∀ b ∈ rest, val b = K := fun b hb => hval b (List.mem_cons.mpr (Or.inr hb))
      simp only [List.foldl_cons, List.any_cons]
      rw [ih hndrest hvalrest (Pauli.mul base (if q = key a then val a else Pauli.I))]
      by_cases hqa : q = key a
      · have hrestfalse : rest.any (fun b => decide (key b = q)) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          rw [List.any_eq_true] at hc
          obtain ⟨b, hb, hkb⟩ := hc
          rw [decide_eq_true_eq] at hkb
          exact hnotin (List.mem_map.mpr ⟨b, hb, by rw [hkb]; exact hqa⟩)
        have hdec : decide (key a = q) = true := decide_eq_true_eq.mpr hqa.symm
        rw [if_pos hqa, hvala]
        simp [hrestfalse, hdec, Pmul_I_right]
      · have hda : decide (key a = q) = false := decide_eq_false_iff_not.mpr fun h => hqa h.symm
        rw [if_neg hqa]
        simp [hda, Pmul_I_right]

/-- **Pointwise value of a uniform-kind schedule row.**  For a schedule all of whose
slots carry CSS kind `K` and whose qubit support is `Nodup`, the row is `K` on the
scheduled (`freshDataQ`-embedded) support and `I` elsewhere. -/
theorem scheduleRow_eval_uniform {n k : Nat} (sigma : RuleSchedule n) (K : Pauli)
    (hnd : (sigma.slots.map (·.qubit)).Nodup)
    (huniform : ∀ slot ∈ sigma.slots, slot.kind.toPauli = K)
    (q : Fin (n + k)) :
    scheduleRow (k := k) sigma q =
      if sigma.slots.any (fun slot => decide (freshDataQ n k slot.qubit = q)) then K
      else Pauli.I := by
  rw [scheduleRow, foldl_scheduleSlotRow_eval q sigma.slots (ErrorVec.identity (n + k))]
  have hkeynd : (sigma.slots.map (fun slot => freshDataQ n k slot.qubit)).Nodup := by
    rw [show (sigma.slots.map (fun slot => freshDataQ n k slot.qubit)) =
        (sigma.slots.map (·.qubit)).map (freshDataQ n k) from by rw [List.map_map]; rfl]
    exact hnd.map (fun _ _ => freshDataQ_inj)
  have hsingle := foldl_singleKind K (fun slot : ScheduledPauli n => freshDataQ n k slot.qubit)
    (fun slot => slot.kind.toPauli) q sigma.slots hkeynd huniform Pauli.I
  rw [Pmul_I_left] at hsingle
  exact hsingle

/-- **Schedule faithfulness on data qubits.**  The compiled `i`-th stabilizer row,
restricted to the data qubits via `freshDataQ`, is exactly the surface stabilizer
`mkSurfaceStabilizers d hd i` (both are the CSS kind on the scheduled support). -/
theorem scheduleRow_nzSchedule_dataRestrict {d : Nat} (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) (k : Nat) (q : Fin (d * d)) :
    scheduleRow (k := k) (nzSchedule d hd i) (freshDataQ (d * d) k q) =
      mkSurfaceStabilizers d hd i q := by
  rw [scheduleRow_eval_uniform (nzSchedule d hd i) (kindPauli (classifyStab d i.val))
        (nzSchedule_support_nodup d hd hd3 hodd i)
        (fun slot hslot => by
          rw [nzSchedule_kind_uniform d hd i slot hslot]; exact kindXZ_toPauli_eq_kindPauli _)
        (freshDataQ (d * d) k q),
      ← nzSuffixResidual_zero_eq_mkSurfaceStabilizers d hd hd3 hodd i]
  simp only [nzSuffixResidual, List.drop_zero, scheduleKind_nzSchedule d hd i]
  have hdec : ∀ slot : ScheduledPauli (d * d),
      decide (freshDataQ (d * d) k slot.qubit = freshDataQ (d * d) k q) = decide (slot.qubit = q) :=
    fun slot => decide_eq_decide.mpr ⟨fun h => freshDataQ_inj h, fun h => by rw [h]⟩
  simp only [hdec]

/-- **Schedule triviality on helper qubits.**  The compiled `i`-th stabilizer row is `I`
on every helper qubit (`q.val ≥ d*d`): no scheduled slot embeds there. -/
theorem scheduleRow_nzSchedule_helperTrivial {d : Nat} (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) (k : Nat) (q : Fin (d * d + k))
    (hq : d * d ≤ q.val) :
    scheduleRow (k := k) (nzSchedule d hd i) q = Pauli.I := by
  rw [scheduleRow_eval_uniform (nzSchedule d hd i) (kindPauli (classifyStab d i.val))
        (nzSchedule_support_nodup d hd hd3 hodd i)
        (fun slot hslot => by
          rw [nzSchedule_kind_uniform d hd i slot hslot]; exact kindXZ_toPauli_eq_kindPauli _) q]
  rw [if_neg (by
    intro hc
    rw [List.any_eq_true] at hc
    obtain ⟨slot, _, hslot⟩ := hc
    rw [decide_eq_true_eq] at hslot
    have hv := congrArg Fin.val hslot
    rw [freshDataQ_val] at hv
    have := slot.qubit.isLt
    omega)]

/-! ## Piece (3, partial): the `Centralizer` half of the `logicalFailure` transport

The compiled spec's `i`-th stabilizer row is, *by definition*, `scheduleRow` of the
`i`-th measured schedule, so `scheduleRow_vectorParity` transports the ambient
`Centralizer` obligation to a `scheduleParity` over the source data-error — no
`programMeasuresAt`↔`nzSchedule` alignment required for this half.  (The full piece (3)
`logicalFailure` iff over `mkSurfaceStabilizers` additionally needs the `Stab`-half
transport and that schedule alignment; see the closing note.) -/
theorem compiled_centralizer_transport {n : Nat} (program : XZProgram n)
    (hdisjoint : fullProgramReadoutDisjoint program) (dist : Nat) (hdist : 0 < dist)
    (es : ErrorState (n + programHelperCount program)) :
    Centralizer (fullProgramCodeSpecD program hdisjoint dist hdist)
        (dataVector (fullProgramCodeSpecD program hdisjoint dist hdist) es) ↔
      ∀ i : Fin (programNumStab program),
        scheduleParity ((programMeasuresAt program).get i).schedule
          (fun q => es.paulis (freshDataQ n (programHelperCount program) q)) = false := by
  have key : ∀ i : Fin (programNumStab program),
      vectorParity ((fullProgramCodeSpecD program hdisjoint dist hdist).stabilizer i)
          (dataVector (fullProgramCodeSpecD program hdisjoint dist hdist) es) =
        scheduleParity ((programMeasuresAt program).get i).schedule
          (fun q => es.paulis (freshDataQ n (programHelperCount program) q)) := by
    intro i
    rw [show (fullProgramCodeSpecD program hdisjoint dist hdist).stabilizer i =
          scheduleRow (k := programHelperCount program) ((programMeasuresAt program).get i).schedule
        from rfl,
      scheduleRow_vectorParity]
    congr 1
    funext q
    show (if (fullProgramCodeSpecD program hdisjoint dist hdist).isData
          (freshDataQ n (programHelperCount program) q) then _ else _) = _
    rw [if_pos]
    show decide ((freshDataQ n (programHelperCount program) q).val < n) = true
    rw [freshDataQ_val]
    exact decide_eq_true q.isLt
  unfold Centralizer
  simp only [key]
  exact Iff.rfl

/-! ## Surface instance of the capstone

The compiled Surface/NZ circuit is `Safe` against the distance-parametric spec at distance
`d`, given the two deferred slot obligations.  `surfaceCircuit d hd` is definitionally
`compileProgram (surfaceXZProgram d hd)`.  The two positivity side conditions
(`0 < d*d + helpers`, `0 < programNumStab`) are genuine and trivially true; discharging
`hnumStab` in closed form additionally needs the `programMeasuresAt`↔`nzSchedule`
alignment (`programNumStab (surfaceXZProgram d hd) = numStabFormula d`), which is left as
a hypothesis here. -/
theorem surfaceNZ_Safe_of_ftDistance_reach (d : Nat) (hd : 0 < d) (_hd3 : 3 ≤ d)
    (_hodd : d % 2 = 1)
    (hnq : 0 < d * d + programHelperCount (surfaceXZProgram d hd))
    (hnumStab : 0 < programNumStab (surfaceXZProgram d hd))
    (ftD : (vcgen (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd hnq hnumStab)).denoteSlot
      .ftDistance)
    (reachScript : List (Option Pauli))
    (reachOk : (vcgen (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd hnq hnumStab)).denoteSlot
      .reach reachScript) :
    Safe (compileProgram (surfaceXZProgram d hd))
      (fullProgramCodeSpecD (surfaceXZProgram d hd)
        (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd) :=
  programCompiled_Safe_of_ftDistance_reach (surfaceXZProgram d hd) d hd hnq hnumStab
    ftD reachScript reachOk

end QStab.QClifford.Compile
