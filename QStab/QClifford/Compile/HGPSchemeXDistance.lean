import QStab.QClifford.Compile.HGPXDistance
import QStab.QClifford.Compile.HGPKnillAssembly
import QStab.QClifford.Compile.HGPFlagAssembly

/-!
# Compiled HGP bar-X distance for every extraction scheme, by duality transport

`HGPXDistance.lean` proves the bar-X floor for the NZ compiled circuit
(`hgp_compiled_barX_distance`) by conjugating the run with the HGP transpose
self-duality automorphism and applying the *generic*
`compiled_barX_of_dualityAutomorphism`.  Every step of that transport is
code-level, not scheme-level: the ambient permutation `hgpDualPermAmbient d nq`
is generic in the ambient dimension `nq`, `hgpPhi`/`hgpBackAction_phi`/`weight_phi`
act on the data block only, and the functor (`hConjCircuit`, `qceval_hConj`,
`errLocsWithContextAux_hConj`, `propagateCircuit_hConj_paulis`) is fully generic.

So the whole path parameterizes over exactly three scheme-dependent inputs — the
helper count `hgpSchemeHelpers scheme d`, the circuit `hgpSchemeCircuit scheme d`,
and an `HGPSchemeHValid scheme d hd` witness — the last of which every scheme
already supplies (`hgpScheme_hvalid` from its `LeafClean` + `SchemeClassifier`).

This file lifts the transport to that generic form and closes
`hgpShor_compiled_barX_distance`, `hgpKnill_compiled_barX_distance`, and
`hgpFlag_compiled_barX_distance` — the scheme-specific bar-X floors that were
previously NZ-only.  Everything goes through `hgpSchemeCircuit scheme d`
(= `compileProgram (hgpSchemeProgram scheme d)`); the conjugated image circuit is
a proof-internal transport target, never claimed to be a `compileProgram` image.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QStab.Examples.HGPParametric
open QHL
open QHL.AssertionLang
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec

/-! ## The ambient dual permutation and conjugated circuit, per scheme -/

/-- The HGP dual permutation on the scheme's compiled layout: sector transpose on
the data block, identity on the compiler's helper qubits — the same ambient
permutation as NZ, now over the scheme's helper count. -/
def hgpSchemeAmbientPerm (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    Equiv.Perm (Fin ((hgpUParams d hd).n + hgpSchemeHelpers scheme d)) :=
  hgpDualPermAmbient d ((hgpUParams d hd).n + hgpSchemeHelpers scheme d) hd
    (Nat.le_add_right _ _)

/-- The H-conjugated image of the scheme's compiled HGP circuit — a proof-internal
transport target.  **Not** claimed to be a `compileProgram` image. -/
def hgpSchemeCircuitD (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    FCircuit ((hgpUParams d hd).n + hgpSchemeHelpers scheme d) :=
  hConjCircuit (hgpSchemeAmbientPerm scheme d hd) (hgpSchemeCircuit scheme d)

/-! ## Residual transport (generic in helper count + circuit) -/

/-- The two injected clean states are `π`/`hadamardAction`-related (generic in the
ambient permutation; re-proved here since the NZ copy is `private`). -/
private theorem injectCleanHConjRel {nq : Nat} (π : Equiv.Perm (Fin nq))
    (cur : Nat) (q0 : Fin nq) (p : Pauli) :
    ∀ x, ((QStab.QClifford.PCC.cleanAtDetector cur).inject (π q0) p).paulis (π x)
      = hadamardAction
          (((QStab.QClifford.PCC.cleanAtDetector cur).inject q0
            (hadamardAction p)).paulis x) := by
  intro x
  simp only [ErrorState.inject]
  by_cases hx : x = q0
  · subst hx
    rw [if_pos rfl, if_pos rfl]
    cases p <;> rfl
  · rw [if_neg (fun h => hx (π.injective h)), if_neg hx]
    rfl

/-- **Residual transport** for the scheme's conjugated circuit: the data residual
of an image fault is the `Φ`-image of the original site's residual at the
H-conjugated Pauli.  Identical to the NZ proof, over the scheme's ambient perm. -/
theorem targetFaultDataResidual_hConj_scheme (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (s : QStab.QClifford.PCC.ErrLocWithContext
      ((hgpUParams d hd).n + hgpSchemeHelpers scheme d))
    (p : Pauli) (hp : p ≠ Pauli.I) :
    targetFaultDataResidual (hgpUParams d hd)
        (⟨⟨hgpSchemeAmbientPerm scheme d hd s.q,
            hConjGates (hgpSchemeAmbientPerm scheme d hd) s.suffix, s.detectorStart⟩, p, hp⟩)
      = hgpPhi d hd (targetFaultDataResidual (hgpUParams d hd)
          ⟨s, hadamardAction p, hadamardAction_ne_I hp⟩) := by
  funext q
  have hkey := propagateCircuit_hConj_paulis (hgpSchemeAmbientPerm scheme d hd) s.suffix
    (injectCleanHConjRel (hgpSchemeAmbientPerm scheme d hd) s.detectorStart s.q p)
    (freshDataQ (hgpUParams d hd).n (hgpSchemeHelpers scheme d)
      ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩)
  have hidx : hgpSchemeAmbientPerm scheme d hd
        (freshDataQ (hgpUParams d hd).n (hgpSchemeHelpers scheme d)
          ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩)
      = freshDataQ (hgpUParams d hd).n (hgpSchemeHelpers scheme d) q :=
    Fin.ext (hgpDualNat_involutive d hd q.val)
  rw [hidx] at hkey
  exact hkey

/-! ## `hvalid` for the image circuit, transported from the scheme's `HValid` -/

/-- **`hvalid` transported along the functor** for the scheme circuit: every fault
site of the image circuit has a weight-`≤ 1` data residual or an
in-back-action-set hook — from the scheme's `HGPSchemeHValid` via residual
transport and `Φ`-closure of the (scheme-independent) union back-action set. -/
theorem hgpScheme_hvalid_hConj (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) :
    ∀ f : FiredFaultWithContext ((hgpUParams d hd).n + hgpSchemeHelpers scheme d),
      f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers scheme d)).es.detectorCursor
        (hgpSchemeCircuitD scheme d hd) →
      ErrorVec.weight (targetFaultDataResidual (hgpUParams d hd) f) ≤ 1 ∨
        ∀ st' : State (hgpUParams d hd),
          targetFaultDataResidual (hgpUParams d hd) f ∈
            (hgpUParams d hd).backActionSet
              (currentStab (hgpProgram d (exactUnionHGPSpec d hd)) st') := by
  rintro ⟨site, p, hp⟩ hmem
  rw [show hgpSchemeCircuitD scheme d hd
        = hConjCircuit (hgpSchemeAmbientPerm scheme d hd) (hgpSchemeCircuit scheme d) from rfl,
    errLocsWithContextAux_hConj] at hmem
  obtain ⟨s, hs, hsite⟩ := List.mem_map.mp hmem
  cases hsite
  rw [targetFaultDataResidual_hConj_scheme scheme d hd s p hp]
  rcases hv ⟨s, hadamardAction p, hadamardAction_ne_I hp⟩ hs with hw | hbk
  · left
    exact le_of_eq_of_le (weight_phi d hd _) hw
  · right
    intro st'
    obtain ⟨k, hk⟩ := hbk st'
    exact ⟨_, hgpBackAction_phi d hd k _ hk⟩

/-! ## The bridge on the image circuit (instantiated, never widened) -/

/-- The compiled bar-Z invariant holds on the scheme's **image** circuit: the same
source certificate, `hFold_of_valid`, and `barrier_hMatch` as the bar-Z assembly,
with the transported scheme `hvalid`. -/
theorem hgpSchemeD_compiled_FHoare (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) :
    FHoare
      (fun sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers scheme d) =>
        sigma = QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers scheme d))
      (hgpSchemeCircuitD scheme d hd)
      (compileFormulaWithinBudget (hgpSchemeHelpers scheme d)
        (hgp_inv_formula d (exactUnionHGPSpec d hd))) :=
  etildeC_hoare_preservation
    (hgp_invariant_certificate d (exactUnionHGPSpec d hd))
    (fun _ hrun hb => hFold_of_valid hrun hb (hgpScheme_hvalid_hConj scheme d hd hv))
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- The bar-Z distance floor on the scheme's **image** circuit. -/
theorem hgpSchemeD_compiled_barZ_distance (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers scheme d),
      qceval (hgpSchemeCircuitD scheme d hd)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers scheme d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers scheme d) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (hgpSchemeD_compiled_FHoare scheme d hd hv)
    (fun E hE => alignedBarZ_barrier_eval_zero "hgp.beta" "hgp.rows" "hgp.barZ"
      (exactUnionHGPSpec d hd).toAligned E hE)
    (Nat.le_refl d)

/-! ## The scheme `DualityAutomorphism` bundle and the headline -/

/-- **The scheme HGP `DualityAutomorphism` bundle**: the transpose self-duality as
a code automorphism.  The code-level fields (`perm`, `Phi`, `dualData`,
`parity_Phi`, `stab_surj`, `Phi_Xbar`, `perm_freshData`) are identical to the NZ
bundle (they depend only on the HGP code, not the extraction scheme); only the
helper count, circuit, and image bar-Z floor are scheme-specific. -/
def hgpSchemeDualityAutomorphism (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) : DualityAutomorphism where
  params  := hgpUParams d hd
  helpers := hgpSchemeHelpers scheme d
  d       := d
  fc      := hgpSchemeCircuit scheme d
  Xbar    := mkHGPRepLogicalX d hd
  Zbar    := mkHGPRepLogicalZ d
  perm     := hgpSchemeAmbientPerm scheme d hd
  Phi      := hgpPhi d hd
  dualData := fun q => ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩
  Phi_def        := fun _ _ => rfl
  perm_freshData := fun q => Fin.ext (hgpDualNat_involutive d hd q.val)
  parity_Phi := parity_phi d hd
  stab_surj  := fun i => by
    have hb : hgpDualCheck d i.val < 2 * ((d - 1) * d) := by
      rcases Nat.lt_or_ge i.val ((d - 1) * d) with hx | hz
      · exact (hgpDualCheck_z d i.val hd hx).2
      · exact Nat.lt_of_lt_of_le (hgpDualCheck_x d i.val hd hz i.isLt) (by omega)
    refine ⟨⟨hgpDualCheck d i.val, hb⟩, ?_⟩
    show hgpPhi d hd (mkHGPRepStabilizers d ⟨hgpDualCheck d i.val, hb⟩)
        = mkHGPRepStabilizers d i
    rw [show mkHGPRepStabilizers d ⟨hgpDualCheck d i.val, hb⟩
          = hgpPhi d hd (mkHGPRepStabilizers d i)
        from (mkHGPRepStabilizers_phi d hd i).symm,
      hgpPhi_involutive d hd (mkHGPRepStabilizers d i)]
  Phi_Xbar   := hgpPhi_involutive d hd (mkHGPRepLogicalZ d)
  image_barZ_floor := fun tau hrunD hcent hz =>
    hgpSchemeD_compiled_barZ_distance scheme d hd hv tau hrunD
      ⟨fun S hS => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS; exact hcent i,
       fun T hT => by rw [List.mem_singleton.mp hT]; exact hz⟩

/-- **Generic compiled bar-X distance floor for any HGP extraction scheme**, given
its `HGPSchemeHValid` witness — a one-line instance of the generic
`compiled_barX_of_dualityAutomorphism` for the transpose bundle.  The run goes
through `hgpSchemeCircuit scheme d`; the bar-X class input is unfolded to its
parity-coset form and fed to the generic lemma. -/
theorem hgpScheme_compiled_barX_distance (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers scheme d),
      qceval (hgpSchemeCircuit scheme d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers scheme d)) sigma →
      (hgpLogicalClassX d hd).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers scheme d) sigma) →
      d ≤ sigma.lambda := by
  intro sigma hrun hcls
  obtain ⟨h0, h1⟩ := hcls
  exact compiled_barX_of_dualityAutomorphism (hgpSchemeDualityAutomorphism scheme d hd hv)
    sigma hrun
    (fun i => h0 _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
    (h1 _ (List.mem_singleton.mpr rfl))

/-! ## The three scheme-specific bar-X floors -/

/-- **Compiled HGP bar-X distance under Shor extraction.** -/
theorem hgpShor_compiled_barX_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Shor d),
      qceval (hgpSchemeCircuit Scheme.Shor d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Shor d)) sigma →
      (hgpLogicalClassX d hd).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers Scheme.Shor d) sigma) →
      d ≤ sigma.lambda :=
  hgpScheme_compiled_barX_distance Scheme.Shor d hd
    (hgpScheme_hvalid Scheme.Shor d hd (hgpShor_leafClean d hd) shor_SchemeClassifier)

/-- **Compiled HGP bar-X distance under Knill extraction.** -/
theorem hgpKnill_compiled_barX_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Knill d),
      qceval (hgpSchemeCircuit Scheme.Knill d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Knill d)) sigma →
      (hgpLogicalClassX d hd).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers Scheme.Knill d) sigma) →
      d ≤ sigma.lambda :=
  hgpScheme_compiled_barX_distance Scheme.Knill d hd
    (hgpScheme_hvalid Scheme.Knill d hd (hgpKnill_leafClean d hd) knill_SchemeClassifier)

/-- **Compiled HGP bar-X distance under Flag extraction** — the fourth-scheme
X-side floor, joining its bar-Z floor to complete both logical directions. -/
theorem hgpFlag_compiled_barX_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Flag d),
      qceval (hgpSchemeCircuit Scheme.Flag d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Flag d)) sigma →
      (hgpLogicalClassX d hd).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers Scheme.Flag d) sigma) →
      d ≤ sigma.lambda :=
  hgpScheme_compiled_barX_distance Scheme.Flag d hd
    (hgpScheme_hvalid Scheme.Flag d hd (hgpFlag_leafClean d hd) flag_SchemeClassifier)

/-! ## Regression guards (axiom pins) -/

/--
info: 'QStab.QClifford.Compile.hgpScheme_compiled_barX_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpScheme_compiled_barX_distance

/--
info: 'QStab.QClifford.Compile.hgpShor_compiled_barX_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpShor_compiled_barX_distance

/--
info: 'QStab.QClifford.Compile.hgpKnill_compiled_barX_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpKnill_compiled_barX_distance

/--
info: 'QStab.QClifford.Compile.hgpFlag_compiled_barX_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpFlag_compiled_barX_distance

end QStab.QClifford.Compile
