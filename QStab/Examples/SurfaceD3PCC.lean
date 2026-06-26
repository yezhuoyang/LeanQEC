import QStab.Examples.SurfaceVerification
import QStab.Paper.SurfaceBarrier

/-! # Surface d=3 with non-empty backActionSet: IsLAligned mechanized

The existing `Paper/SurfaceBarrier.lean` proves `surface_isLAligned`
for `D3Witness.nzSpec.params = SurfaceD3.code`, which has
`backActionSet := fun _ => ∅` — making `IsLAligned` trivially true
(vacuous).

This module upgrades the surface-d=3 instance to a NON-VACUOUS
backActionSet containing the actual hooks of the NZ-scheduled standard
CNOT scheme (the `hookErrors` enumeration from
`SurfaceVerification.lean`). The hook-spread-bound theorem
`projRowsX_hook_le` (already proven in `SurfaceVerification.lean`) is
the central paper claim "NZ hooks shift the perpendicular spread by
at most one" — we re-package it into an `NZSurfaceSpec 3` whose
`hook_spread_bound` field is no longer vacuous.

The resulting `surfaceBarrier nzSpecPCC` + `surface_isLAligned nzSpecPCC`
give:
* `BarrierFunction surfaceD3PCC (barZClass nzSpecPCC.toAligned)` — the
  perpendicular-spread barrier with `d_L = 3`.
* `IsLAligned (surfaceBarrier nzSpecPCC)` — NOW NON-VACUOUS: alignment
  holds for every actual hook in the surface-d=3 NZ schedule.

All axiom-clean.
-/

namespace QStab.Examples.SurfaceD3PCC

open QStab QStab.Examples QStab.Examples.SurfaceGeneral
     QStab.Paper.BarrierFramework QStab.Paper.AlignedBarrier

/-! ## QECParams with non-empty backActionSet -/

/-- The extended hook set for stabilizer `s`: the existing
    `hookErrors` (mid-CNOT hooks) PLUS the stabilizer itself
    (the "pre-first-CNOT" hook from an ancilla Y/Z fault between
    `prepX/Z` and the first CNOT, which propagates through the entire
    support).

    Reusing the existing `projRowsX_hook_le` for the mid-CNOT hooks +
    the stabilizer-invariance of perpendicular spread for the new
    stabilizer hook. -/
def hookSet (s : Fin 8) : Set (ErrorVec 9) :=
  { e | e ∈ SurfaceD3.hookErrors s ∨ e = SurfaceD3.stabilizers s }

theorem hookSet_weight_bound (s : Fin 8) (e : ErrorVec 9) (he : e ∈ hookSet s) :
    ErrorVec.weight e ≤ 4 := by
  rcases he with hookHe | rfl
  · exact (SurfaceD3.hook_weight_bound s e hookHe).trans (by decide)
  · -- e = stabilizers s; weight ≤ 4 for surface d=3 stabilizers
    fin_cases s <;> decide

/-- `surfaceD3PCC` — `SurfaceD3.code` augmented with the actual
    non-empty backActionSet from the NZ schedule. `r := 4` to
    accommodate the weight-4 bulk-stabilizer hooks. -/
def surfaceD3PCC : QECParams where
  n := 9
  k := 1
  d := 3
  R := 5
  numStab := 8
  stabilizers := SurfaceD3.stabilizers
  backActionSet := hookSet
  r := 4
  backAction_weight_bound := hookSet_weight_bound
  C_budget := 1
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Transport InStab between equivalent QECParams -/

/-- InStab transports from `SurfaceD3.code` to `surfaceD3PCC`. -/
def InStab_to_PCC : ∀ {S : ErrorVec 9},
    QStab.InStab SurfaceD3.code S → QStab.InStab surfaceD3PCC S
  | _, .identity      => QStab.InStab.identity (P := surfaceD3PCC)
  | _, .gen i         => QStab.InStab.gen (P := surfaceD3PCC) i
  | _, .mul h1 h2     => QStab.InStab.mul (InStab_to_PCC h1) (InStab_to_PCC h2)

/-- Reverse transport. -/
def InStab_from_PCC : ∀ {S : ErrorVec 9},
    QStab.InStab surfaceD3PCC S → QStab.InStab SurfaceD3.code S
  | _, .identity      => QStab.InStab.identity (P := SurfaceD3.code)
  | _, .gen i         => QStab.InStab.gen (P := SurfaceD3.code) i
  | _, .mul h1 h2     => QStab.InStab.mul (InStab_from_PCC h1) (InStab_from_PCC h2)

/-! ## NZSurfaceSpec 3 with the new params -/

/-- `projRowsX` equals the filter-form over `q.val / 3 = row.val`. -/
theorem projRowsX_eq_filter (E : ErrorVec surfaceD3PCC.n) :
    projRowsX (d := 3) E = (Finset.univ.filter fun row : Fin 3 =>
      ∃ q : Fin surfaceD3PCC.n, q.val / 3 = row.val ∧
        Pauli.hasXComponent (E q) = true).card := by
  unfold projRowsX
  congr 1
  ext row
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hjx⟩
    refine ⟨toIdx 3 row j, ?_, hjx⟩
    show (3 * row.val + j.val) / 3 = row.val
    have hjlt : j.val < 3 := j.isLt
    have h1 : (j.val + 3 * row.val) / 3 = j.val / 3 + row.val :=
      Nat.add_mul_div_left j.val row.val (by decide : (0 : Nat) < 3)
    have h2 : j.val / 3 = 0 := Nat.div_eq_of_lt hjlt
    have h3 : 3 * row.val + j.val = j.val + 3 * row.val := by omega
    rw [h3, h1, h2]; omega
  · rintro ⟨q, hq_div, hqx⟩
    have hjlt : q.val % 3 < 3 := Nat.mod_lt _ (by decide)
    refine ⟨⟨q.val % 3, hjlt⟩, ?_⟩
    have h_eq : toIdx 3 row ⟨q.val % 3, hjlt⟩ = q := by
      apply Fin.ext
      show 3 * row.val + q.val % 3 = q.val
      have hdm := Nat.div_add_mod q.val 3
      have : q.val / 3 = row.val := hq_div
      omega
    rw [h_eq]
    exact hqx

/-- The upgraded NZSurfaceSpec 3 with non-empty backActionSet.
    `hook_spread_bound` is proved via `projRowsX_hook_le`. -/
def nzSpecPCC : NZSurfaceSpec 3 where
  params := surfaceD3PCC
  hn := by decide
  hd_pos := by decide
  logicalZ := SurfaceD3.logicalZ
  rowCut := D3Witness.rowCutFin
  rowCut_zero := D3Witness.rowCutFin_zero
  rowCut_succ := fun ⟨iv, hiv_lt⟩ hi => by
    -- The rowCut_succ proofs use InStab SurfaceD3.code; transport to surfaceD3PCC.
    match iv, hiv_lt, hi with
    | 0, _, _ =>
        obtain ⟨S, hS, hZ, hRow⟩ := D3Witness.rowCutFin_succ_0
        exact ⟨S, InStab_to_PCC hS, hZ, hRow⟩
    | 1, _, _ =>
        obtain ⟨S, hS, hZ, hRow⟩ := D3Witness.rowCutFin_succ_1
        exact ⟨S, InStab_to_PCC hS, hZ, hRow⟩
  logicalZ_normalizer := D3Witness.logicalZ_norm
  rowCut_spec := D3Witness.rowCutFin_spec
  stab_commute := D3Witness.stab_commute_d3
  hook_spread_bound := by
    intro s_idx e_B he E S_wit hS
    have hS_d3 : QStab.InStab SurfaceD3.code S_wit := InStab_from_PCC hS
    -- he : e_B ∈ hookSet s_idx = (hookErrors s_idx ∨ e_B = stabilizers s_idx)
    rcases he with he_hook | rfl
    · -- Mid-CNOT hook case: use projRowsX_hook_le directly.
      have he' : e_B ∈ SurfaceD3.hookErrors s_idx := he_hook
      obtain ⟨corr, hcorr_stab, hbound⟩ :=
        SurfaceD3.projRowsX_hook_le (ErrorVec.mul S_wit E) s_idx e_B he'
      refine ⟨ErrorVec.mul corr S_wit, ?_, ?_⟩
      · exact InStab_to_PCC (QStab.InStab.mul hcorr_stab hS_d3)
      · have h_reorder :
            ErrorVec.mul (ErrorVec.mul corr S_wit) (ErrorVec.mul e_B E) =
            ErrorVec.mul (ErrorVec.mul corr e_B) (ErrorVec.mul S_wit E) := by
          funext i
          show Pauli.mul (Pauli.mul (corr i) (S_wit i))
                         (Pauli.mul (e_B i) (E i)) =
               Pauli.mul (Pauli.mul (corr i) (e_B i))
                         (Pauli.mul (S_wit i) (E i))
          cases (corr i) <;> cases (S_wit i) <;> cases (e_B i) <;> cases (E i) <;> rfl
        have h_bound : projRowsX (d := 3) (ErrorVec.mul (ErrorVec.mul corr S_wit)
                                                        (ErrorVec.mul e_B E)) ≤
                       projRowsX (d := 3) (ErrorVec.mul S_wit E) + 1 := by
          rw [h_reorder]; exact hbound
        have h_eq_lhs := projRowsX_eq_filter
          (ErrorVec.mul (ErrorVec.mul corr S_wit) (ErrorVec.mul e_B E))
        have h_eq_rhs := projRowsX_eq_filter (ErrorVec.mul S_wit E)
        rw [← h_eq_lhs, ← h_eq_rhs]
        exact h_bound
    · -- Stabilizer case: e_B = stabilizers s_idx. Set S' := S_wit · stab.
      -- Then S' · (stab · E) = S_wit · stab · stab · E = S_wit · E.
      refine ⟨ErrorVec.mul S_wit (SurfaceD3.stabilizers s_idx), ?_, ?_⟩
      · exact InStab_to_PCC
          (QStab.InStab.mul hS_d3 (@QStab.InStab.gen SurfaceD3.code s_idx))
      · -- (S_wit · stab) · (stab · E) = S_wit · E (since stab² = I).
        have h_collapse :
            ErrorVec.mul (ErrorVec.mul S_wit (SurfaceD3.stabilizers s_idx))
                         (ErrorVec.mul (SurfaceD3.stabilizers s_idx) E) =
            ErrorVec.mul S_wit E := by
          funext i
          show Pauli.mul (Pauli.mul (S_wit i) (SurfaceD3.stabilizers s_idx i))
                         (Pauli.mul (SurfaceD3.stabilizers s_idx i) (E i)) =
               Pauli.mul (S_wit i) (E i)
          cases (S_wit i) <;> cases (SurfaceD3.stabilizers s_idx i) <;> cases (E i) <;> rfl
        rw [show (Finset.univ.filter fun row : Fin 3 =>
                    ∃ q : Fin surfaceD3PCC.n, q.val / 3 = row.val ∧
                      Pauli.hasXComponent
                        (ErrorVec.mul (ErrorVec.mul S_wit (SurfaceD3.stabilizers s_idx))
                                      (ErrorVec.mul (SurfaceD3.stabilizers s_idx) E) q)
                        = true).card
                  = (Finset.univ.filter fun row : Fin 3 =>
                      ∃ q : Fin surfaceD3PCC.n, q.val / 3 = row.val ∧
                        Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card
              from by rw [h_collapse]]
        omega

/-! ## Get BarrierFunction + IsLAligned for the new params -/

/-- Surface d=3 barrier for the new (non-empty backActionSet) params. -/
noncomputable def barrier : BarrierFunction surfaceD3PCC
    (QStab.Paper.SurfaceBarrier.barZClass nzSpecPCC) :=
  QStab.Paper.SurfaceBarrier.surfaceBarrier nzSpecPCC

/-- **`IsLAligned` for surface d=3 with non-empty backActionSet** —
    NOW NON-VACUOUS. Every actual NZ hook in the surface code's
    schedule shifts the perpendicular-spread barrier by at most one.
    This is the paper's central alignment claim, mechanized end-to-end
    with QStab-level types. -/
theorem aligned : IsLAligned barrier :=
  QStab.Paper.SurfaceBarrier.surface_isLAligned nzSpecPCC

/-! ## Axiom inspection in-file (`#print axioms`) -/

#print axioms nzSpecPCC

end QStab.Examples.SurfaceD3PCC
