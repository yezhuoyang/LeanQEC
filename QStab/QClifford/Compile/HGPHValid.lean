import QStab.QClifford.Compile.HGPNZAssembly
import QStab.QClifford.Compile.XZProgramOfProgramsLeaves

/-!
# Discharging `HGPHValid`: the compiled HGP distance, unconditional

The HGP instance of the surface piece-2 pipeline, with the generic machinery
reused as-is: site split (`errLocsWithContextAux_eq_prefix_nil` +
`compileProgramAux_site_split`), leaf pinning at the **generator** level
(`xzProgramOfPrograms_measLeaf`), the two generic per-gadget classifiers
(`nz_gadget_site_classified` / `_X`), and then the membership step — where the
schedule-independent back-action design pays off: every suffix residual is
pointwise dominated by its own generator (`stabEntry_mem_supportList`), hence
a member of the union machine's back-action set, constant in the current
stabilizer.

Deliverables: `hgp_hvalid`, and the unconditional
`hgp_compiled_FHoare` / **`hgp_compiled_barZ_distance`** — the second code
family through the complete compiled pipeline, for every `d ≥ 2`.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QHL
open QHL.CodeHGPSchedule
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec

/-! ## Schedule facts -/

/-- The HGP schedule is kind-uniform (the `hx`/`hz` hypothesis shape). -/
theorem hgpSchedule_kind_uniform (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) :
    ∀ s ∈ (hgpSchedule d hd i).slots, s.kind = hgpKind d i.val :=
  uniform_kind _ _

/-- The scheduled qubits of one HGP check are pairwise distinct. -/
theorem hgpSchedule_support_nodup (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) :
    ((hgpSchedule d hd i).slots.map (·.qubit)).Nodup := by
  have hxq : (hgpSchedule d hd i).slots.map (·.qubit)
      = (hgpSupportList d i.val).map (hgpFin d hd) := by
    unfold hgpSchedule RuleSchedule.uniform
    simp [List.map_map, Function.comp]
  rw [hxq]
  refine List.Nodup.map_on ?_ (hgpSupportList_nodup d i.val hd i.isLt)
  intro x hx y hy hxy
  have hxlt := hgpSupportList_lt d i.val hd i.isLt x hx
  have hylt := hgpSupportList_lt d i.val hd i.isLt y hy
  have hval : x % (d * d + (d - 1) * (d - 1)) = y % (d * d + (d - 1) * (d - 1)) :=
    congrArg Fin.val hxy
  rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hval

/-- The CSS `XZPauli` kind of an HGP check agrees with its `Pauli` kind. -/
theorem hgpKind_toPauli (d k : Nat) :
    (hgpKind d k).toPauli = hgpKindPauli d k := by
  unfold hgpKind hgpKindPauli
  by_cases hx : k < (d - 1) * d
  · rw [if_pos hx, if_pos hx]; rfl
  · rw [if_neg hx, if_neg hx]; rfl

/-- The head kind of the HGP schedule is the check's CSS Pauli. -/
theorem scheduleKind_hgpSchedule (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) :
    scheduleKind (hgpSchedule d hd i) = hgpKindPauli d i.val := by
  have hne : hgpSupportList d i.val ≠ [] := by
    intro h
    have h3 := (hgpLenFlat_window d i.val hd i.isLt).1
    rw [show hgpLenFlat d i.val = (hgpSupportList d i.val).length from rfl, h] at h3
    simp at h3
  rw [← hgpKind_toPauli]
  unfold scheduleKind hgpSchedule RuleSchedule.uniform
  cases hsl : hgpSupportList d i.val with
  | nil => exact absurd hsl hne
  | cons q0 rest => simp

/-! ## The membership bridge (the domination payoff) -/

/-- **Every suffix residual is pointwise dominated by its own generator**: at a
scheduled qubit the residual is the check's CSS Pauli, which is exactly the
generator's entry there (`stabEntry_mem_supportList`); elsewhere it is `I`. -/
theorem nzSuffixResidual_hgpSchedule_dominated (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) (j : Nat)
    (q : Fin (d * d + (d - 1) * (d - 1))) :
    nzSuffixResidual (hgpSchedule d hd i) j q = Pauli.I ∨
      nzSuffixResidual (hgpSchedule d hd i) j q
        = QStab.Examples.HGPParametric.mkHGPRepStabilizers d ⟨i.val, i.isLt⟩ q := by
  unfold nzSuffixResidual
  by_cases hin : ((hgpSchedule d hd i).slots.drop j).any
      (fun slot => decide (slot.qubit = q))
  · right
    rw [if_pos hin]
    -- extract the scheduled source qubit q₀ with `hgpFin q₀ = q`
    obtain ⟨slot, hslot_mem, hslot_q⟩ := List.any_eq_true.mp hin
    have hslot_mem' : slot ∈ (hgpSchedule d hd i).slots :=
      List.mem_of_mem_drop hslot_mem
    have hq0 : ∃ q₀ ∈ hgpSupportList d i.val, hgpFin d hd q₀ = slot.qubit := by
      unfold hgpSchedule RuleSchedule.uniform at hslot_mem'
      simp only [List.mem_map] at hslot_mem'
      obtain ⟨qf, hqf, rfl⟩ := hslot_mem'
      obtain ⟨q₀, hq₀, rfl⟩ := hqf
      exact ⟨q₀, hq₀, rfl⟩
    obtain ⟨q₀, hq₀mem, hq₀⟩ := hq0
    have hqeq : slot.qubit = q := of_decide_eq_true hslot_q
    have hqval : q.val = q₀ := by
      rw [← hqeq, ← hq₀]
      show q₀ % (d * d + (d - 1) * (d - 1)) = q₀
      exact Nat.mod_eq_of_lt (hgpSupportList_lt d i.val hd i.isLt q₀ hq₀mem)
    show scheduleKind (hgpSchedule d hd i)
      = QStab.Examples.HGPParametric.stabEntry d i.val q.val
    rw [scheduleKind_hgpSchedule d hd i, hqval,
      stabEntry_mem_supportList d i.val q₀ hd i.isLt hq₀mem]
  · left
    rw [if_neg hin]

/-! ## The discharge -/

/-- **`HGPHValid` holds for every `d ≥ 2`.** -/
theorem hgp_hvalid (d : Nat) (hd : 2 ≤ d) : HGPHValid d hd := by
  intro f hf
  obtain ⟨site, p, hp⟩ := f
  rw [errLocsWithContextAux_eq_prefix_nil] at hf
  obtain ⟨scheme, sigma, gstart, gcursor, gtail, ghfit, hML, hgtail_split, hsite⟩ :=
    compileProgramAux_site_split (total := programHelperCount (hgpXZProgram d))
      (hgpXZProgram d) 0 (by simp) _ [] site
      (xzProgramOfPrograms_allNZ _ _ _ _ _ _)
      (fun es dd _ => by simp [eraseFaults, propagateCircuit]) hf
  obtain ⟨k, hk, rfl, rfl⟩ :=
    xzProgramOfPrograms_measLeaf _ _ _ _ _ _ _ _ hML
  rw [genSchedule_eq_hgpSchedule d hd ⟨k, hk⟩] at hsite
  have hgtail : ∀ (es : ErrorState ((hgpUParams d hd).n + hgpHelpers d))
      (q'' : Fin (hgpUParams d hd).n),
      (propagateCircuit (eraseFaults gtail) es).paulis
          (freshDataQ (hgpUParams d hd).n (hgpHelpers d) q'') =
        es.paulis (freshDataQ (hgpUParams d hd).n (hgpHelpers d) q'') :=
    fun es q'' => hgtail_split es
      (freshDataQ (hgpUParams d hd).n (hgpHelpers d) q'')
      (by rw [freshDataQ_val]; exact q''.isLt)
  have hclass :
      ErrorVec.weight (targetFaultDataResidual (hgpUParams d hd) ⟨site, p, hp⟩) ≤ 1 ∨
        ∃ j, j < (hgpSchedule d hd ⟨k, hk⟩).slots.length ∧
          targetFaultDataResidual (hgpUParams d hd) ⟨site, p, hp⟩ =
            nzSuffixResidual (hgpSchedule d hd ⟨k, hk⟩) j := by
    by_cases hxk : k < (d - 1) * d
    · exact nz_gadget_site_classified_X (P := hgpUParams d hd)
        (hgpSchedule d hd ⟨k, hk⟩) gstart ghfit
        (fun s hs => by
          rw [hgpSchedule_kind_uniform d hd ⟨k, hk⟩ s hs]
          unfold hgpKind
          rw [if_pos hxk])
        (hgpSchedule_support_nodup d hd ⟨k, hk⟩) gcursor gtail hgtail site p hp hsite
    · exact nz_gadget_site_classified (P := hgpUParams d hd)
        (hgpSchedule d hd ⟨k, hk⟩) gstart ghfit
        (fun s hs => by
          rw [hgpSchedule_kind_uniform d hd ⟨k, hk⟩ s hs]
          unfold hgpKind
          rw [if_neg hxk])
        (hgpSchedule_support_nodup d hd ⟨k, hk⟩) gcursor gtail hgtail site p hp hsite
  rcases hclass with hle | ⟨j, hj, hres⟩
  · exact Or.inl hle
  · refine Or.inr fun _ => ?_
    rw [hres]
    exact ⟨⟨k, hk⟩, fun q =>
      nzSuffixResidual_hgpSchedule_dominated d hd ⟨k, hk⟩ j q⟩

/-! ## The unconditional corollaries -/

/-- **Unconditional compiled invariant.** -/
theorem hgp_compiled_FHoare (d : Nat) (hd : 2 ≤ d) :
    FHoare
      (fun sigma : QCState ((hgpUParams d hd).n + hgpHelpers d) =>
        sigma = QCState.clean ((hgpUParams d hd).n + hgpHelpers d))
      (hgpCircuit d)
      (compileFormulaWithinBudget (hgpHelpers d)
        (hgp_inv_formula d (exactUnionHGPSpec d hd))) :=
  hgpNZ_compiled_FHoare d hd (hgp_hvalid d hd)

/-- **Unconditional compiled bar-Z circuit-level distance for the HGP family**:
every clean-start run of `compileProgram (hgpXZProgram d)` whose data residual
lies in the bar-Z logical class fired at least `d` faults — for every
`d ≥ 2`. -/
theorem hgp_compiled_barZ_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpHelpers d),
      qceval (hgpCircuit d)
        (QCState.clean ((hgpUParams d hd).n + hgpHelpers d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpHelpers d) sigma) →
      d ≤ sigma.lambda :=
  hgpNZ_compiled_barZ_distance d hd (hgp_hvalid d hd)

#print axioms hgp_hvalid
#print axioms hgp_compiled_FHoare
#print axioms hgp_compiled_barZ_distance

end QStab.QClifford.Compile
