import QStab.QClifford.Compile.HGPDuality
import QStab.QClifford.Compile.HGPHValid
import QStab.QClifford.Compile.DualityAutomorphism

/-!
# The compiled HGP bar-X distance, by duality transport (chunk 3)

The X-side floor for the **original** compiled circuit
`compileProgram (hgpXZProgram d)`, obtained without any X-side framework
objects:

1. the parametric site table (`errLocsWithContextAux_hConj`) identifies the
   image circuit's fault sites with `π`-relabeled, H-conjugated originals;
2. deterministic residual equivariance (`propagateCircuit_hConj_paulis`)
   turns each image residual into the `Φ`-image of an original residual;
3. the landed `hgp_hvalid` plus `Φ`-closure of the union back-action set
   (`hgpBackAction_phi`) discharge `hvalid` for the image circuit;
4. the **generic** bridge (`etildeC_hoare_preservation` + `hFold_of_valid` +
   `barrier_hMatch` + `compiled_barrier_distance`) is instantiated on the
   image circuit with the *same* bar-Z certificate — never widened;
5. `qceval_hConj` pulls the image floor back: a clean-start run of the
   original circuit with a bar-X-class residual is matched by an image run
   with a bar-Z-class residual and the same `λ`.

The image circuit `hgpCircuitD` is a proof-internal object: **no claim is
made that it equals any `compileProgram` image**, and nothing
detector-conditioned is transported through `HRel` (paulis + `λ` only).
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QStab.Examples.HGPParametric
open QHL
open QHL.AssertionLang
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec

/-! ## The ambient dual permutation of the compiled HGP layout -/

/-- The HGP dual permutation on the compiled layout: sector transpose on the
    data block, identity on the compiler's helper qubits. -/
def hgpAmbientPerm (d : Nat) (hd : 2 ≤ d) :
    Equiv.Perm (Fin ((hgpUParams d hd).n + hgpHelpers d)) :=
  hgpDualPermAmbient d ((hgpUParams d hd).n + hgpHelpers d) hd
    (Nat.le_add_right _ _)

/-- The H-conjugated image of the compiled HGP circuit — a proof-internal
    transport target.  **Not** claimed to be a `compileProgram` image. -/
def hgpCircuitD (d : Nat) (hd : 2 ≤ d) :
    FCircuit ((hgpUParams d hd).n + hgpHelpers d) :=
  hConjCircuit (hgpAmbientPerm d hd) (hgpCircuit d)

/-! ## Residual transport -/

/-- The two injected clean states are `π`/`hadamardAction`-related. -/
private theorem inject_clean_hConj_rel {nq : Nat} (π : Equiv.Perm (Fin nq))
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

/-- **Residual transport.**  The data residual of an image fault is the
    `Φ`-image of the original site's residual at the H-conjugated Pauli. -/
theorem targetFaultDataResidual_hConj (d : Nat) (hd : 2 ≤ d)
    (s : QStab.QClifford.PCC.ErrLocWithContext ((hgpUParams d hd).n + hgpHelpers d))
    (p : Pauli) (hp : p ≠ Pauli.I) :
    targetFaultDataResidual (hgpUParams d hd)
        (⟨⟨hgpAmbientPerm d hd s.q, hConjGates (hgpAmbientPerm d hd) s.suffix,
            s.detectorStart⟩, p, hp⟩)
      = hgpPhi d hd (targetFaultDataResidual (hgpUParams d hd)
          ⟨s, hadamardAction p, hadamardAction_ne_I hp⟩) := by
  funext q
  have hkey := propagateCircuit_hConj_paulis (hgpAmbientPerm d hd) s.suffix
    (inject_clean_hConj_rel (hgpAmbientPerm d hd) s.detectorStart s.q p)
    (freshDataQ (hgpUParams d hd).n (hgpHelpers d)
      ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩)
  have hidx : hgpAmbientPerm d hd (freshDataQ (hgpUParams d hd).n (hgpHelpers d)
        ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩)
      = freshDataQ (hgpUParams d hd).n (hgpHelpers d) q :=
    Fin.ext (hgpDualNat_involutive d hd q.val)
  rw [hidx] at hkey
  exact hkey

private theorem hadamardAction_ne_I_iff (p : Pauli) :
    hadamardAction p ≠ Pauli.I ↔ p ≠ Pauli.I := by
  cases p <;> simp [hadamardAction]

/-- `Φ` preserves the residual weight (`hadamardAction` fixes non-identity,
    the sector transpose permutes coordinates). -/
theorem weight_phi (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (d * d + (d - 1) * (d - 1))) :
    ErrorVec.weight (hgpPhi d hd E) = ErrorVec.weight E := by
  unfold ErrorVec.weight
  apply Finset.card_equiv (hgpDualPermData d hd)
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show hgpPhi d hd E q ≠ Pauli.I ↔ E (hgpDualPermData d hd q) ≠ Pauli.I
  rw [show hgpPhi d hd E q
      = hadamardAction (E (hgpDualPermData d hd q)) from rfl]
  exact hadamardAction_ne_I_iff _

/-! ## `hvalid` for the image circuit -/

/-- **`hvalid` transported along the functor**: every fault site of the image
    circuit has a weight-`≤ 1` data residual or an in-back-action-set hook —
    from the landed `hgp_hvalid` via residual transport and `Φ`-closure of
    the union back-action set. -/
theorem hgp_hvalid_hConj (d : Nat) (hd : 2 ≤ d) :
    ∀ f : FiredFaultWithContext ((hgpUParams d hd).n + hgpHelpers d),
      f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
        (QCState.clean ((hgpUParams d hd).n + hgpHelpers d)).es.detectorCursor
        (hgpCircuitD d hd) →
      ErrorVec.weight (targetFaultDataResidual (hgpUParams d hd) f) ≤ 1 ∨
        ∀ st' : State (hgpUParams d hd),
          targetFaultDataResidual (hgpUParams d hd) f ∈
            (hgpUParams d hd).backActionSet
              (currentStab (hgpProgram d (exactUnionHGPSpec d hd)) st') := by
  rintro ⟨site, p, hp⟩ hmem
  rw [show hgpCircuitD d hd
        = hConjCircuit (hgpAmbientPerm d hd) (hgpCircuit d) from rfl,
    errLocsWithContextAux_hConj] at hmem
  obtain ⟨s, hs, hsite⟩ := List.mem_map.mp hmem
  cases hsite
  rw [targetFaultDataResidual_hConj d hd s p hp]
  rcases hgp_hvalid d hd ⟨s, hadamardAction p, hadamardAction_ne_I hp⟩ hs
    with hw | hbk
  · left
    exact le_of_eq_of_le (weight_phi d hd _) hw
  · right
    intro st'
    obtain ⟨k, hk⟩ := hbk st'
    exact ⟨_, hgpBackAction_phi d hd k _ hk⟩

/-! ## The bridge on the image circuit (instantiated, never widened) -/

/-- The compiled bar-Z invariant holds on the **image** circuit: the same
    source certificate, `hFold_of_valid`, and `barrier_hMatch` as the bar-Z
    assembly, with the transported `hvalid`. -/
theorem hgpD_compiled_FHoare (d : Nat) (hd : 2 ≤ d) :
    FHoare
      (fun sigma : QCState ((hgpUParams d hd).n + hgpHelpers d) =>
        sigma = QCState.clean ((hgpUParams d hd).n + hgpHelpers d))
      (hgpCircuitD d hd)
      (compileFormulaWithinBudget (hgpHelpers d)
        (hgp_inv_formula d (exactUnionHGPSpec d hd))) :=
  etildeC_hoare_preservation
    (hgp_invariant_certificate d (exactUnionHGPSpec d hd))
    (fun _ hrun hb => hFold_of_valid hrun hb (hgp_hvalid_hConj d hd))
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- The bar-Z distance floor on the **image** circuit. -/
theorem hgpD_compiled_barZ_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpHelpers d),
      qceval (hgpCircuitD d hd)
        (QCState.clean ((hgpUParams d hd).n + hgpHelpers d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpHelpers d) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (hgpD_compiled_FHoare d hd)
    (fun E hE => alignedBarZ_barrier_eval_zero "hgp.beta" "hgp.rows" "hgp.barZ"
      (exactUnionHGPSpec d hd).toAligned E hE)
    (Nat.le_refl d)

/-! ## The bar-X class and the parity conversion -/

/-- Row-level self-duality: the `Φ`-image of a stabilizer generator row is
    the dual check's row. -/
theorem mkHGPRepStabilizers_phi (d : Nat) (hd : 2 ≤ d)
    (k : Fin (hgpNumStab d)) :
    hgpPhi d hd (mkHGPRepStabilizers d k)
      = mkHGPRepStabilizers d
          ⟨hgpDualCheck d k.val, by
            rcases Nat.lt_or_ge k.val ((d - 1) * d) with hx | hz
            · exact (hgpDualCheck_z d k.val hd hx).2
            · exact Nat.lt_of_lt_of_le (hgpDualCheck_x d k.val hd hz k.isLt)
                (by omega)⟩ := by
  funext q
  show hadamardAction
      (QStab.Examples.HGPParametric.stabEntry d k.val (hgpDualNat d q.val))
    = QStab.Examples.HGPParametric.stabEntry d (hgpDualCheck d k.val) q.val
  rw [← stabEntry_dual d k.val (hgpDualNat d q.val) hd k.isLt,
    hgpDualNat_involutive d hd q.val]

/-- **The bar-X logical class** of the compiled HGP machine: commutes with
    every stabilizer generator and anticommutes with the logical-X
    representative `X̄ = Φ Z̄` (`mkHGPRepLogicalX`, X exactly on the sector-1
    row-0 qubits). -/
def hgpLogicalClassX (d : Nat) (hd : 2 ≤ d) :
    LogicalClassSymbol (hgpUParams d hd) where
  name := "hgp.barX"
  parityZero := alignedBarZParityZero (exactUnionHGPSpec d hd).toAligned
  parityOne := [mkHGPRepLogicalX d hd]
  distance := d

/-- **The parity conversion**: a bar-X-class residual maps under `Φ` to a
    bar-Z-class residual.  The stabilizer-commutation leg is `σ`-transport
    of the *same* generator list; the anticommutation leg is the chunk-2
    parity-swap identity. -/
theorem hgpLogicalClassX_contains_phi (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (hgpUParams d hd).n)
    (hE : (hgpLogicalClassX d hd).contains E) :
    (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains (hgpPhi d hd E) := by
  obtain ⟨h0, h1⟩ := hE
  refine ⟨?_, ?_⟩
  · intro S hS
    have hS' : S ∈ (List.finRange (exactUnionHGPSpec d hd).params.numStab).map
        (exactUnionHGPSpec d hd).params.stabilizers := hS
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS'
    show ErrorVec.parity (mkHGPRepStabilizers d i) (hgpPhi d hd E) = false
    have hmem : (exactUnionHGPSpec d hd).params.stabilizers
        ⟨hgpDualCheck d i.val, by
          rcases Nat.lt_or_ge i.val ((d - 1) * d) with hx | hz
          · exact (hgpDualCheck_z d i.val hd hx).2
          · exact Nat.lt_of_lt_of_le (hgpDualCheck_x d i.val hd hz i.isLt)
              (by omega)⟩
        ∈ (hgpLogicalClassX d hd).parityZero :=
      List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
    calc ErrorVec.parity (mkHGPRepStabilizers d i) (hgpPhi d hd E)
        = ErrorVec.parity (hgpPhi d hd (hgpPhi d hd (mkHGPRepStabilizers d i)))
            (hgpPhi d hd E) :=
          (congrArg (fun S => ErrorVec.parity S (hgpPhi d hd E))
            (hgpPhi_involutive d hd (mkHGPRepStabilizers d i))).symm
      _ = ErrorVec.parity (hgpPhi d hd (mkHGPRepStabilizers d i)) E :=
          parity_phi d hd _ E
      _ = false := by rw [mkHGPRepStabilizers_phi d hd i]; exact h0 _ hmem
  · intro T hT
    have hT' : T = mkHGPRepLogicalZ d := List.mem_singleton.mp hT
    subst hT'
    show ErrorVec.parity (mkHGPRepLogicalZ d) (hgpPhi d hd E) = true
    rw [← parity_logicalX_phi d hd E]
    exact h1 _ (List.mem_singleton.mpr rfl)

/-! ## The bundle and the headline -/

/-- **The HGP `DualityAutomorphism` bundle**: the transpose self-duality (`Φ`
involutive) as a code automorphism.  `parity_Φ = parity_phi`, `Φ(X̄)=Z̄` is
`hgpPhi_involutive` on `X̄ = Φ Z̄`, stab-row surjectivity comes from
`mkHGPRepStabilizers_phi` + involutivity, and the image bar-Z floor is
`hgpD_compiled_barZ_distance` (wrapped into parity form). -/
def hgpDualityAutomorphism (d : Nat) (hd : 2 ≤ d) : DualityAutomorphism where
  params  := hgpUParams d hd
  helpers := hgpHelpers d
  d       := d
  fc      := hgpCircuit d
  Xbar    := mkHGPRepLogicalX d hd
  Zbar    := mkHGPRepLogicalZ d
  perm     := hgpAmbientPerm d hd
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
    hgpD_compiled_barZ_distance d hd tau hrunD
      ⟨fun S hS => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS; exact hcent i,
       fun T hT => by rw [List.mem_singleton.mp hT]; exact hz⟩

/-- **Compiled bar-X circuit-level distance for the HGP family** — now a one-line
instance of the generic `compiled_barX_of_dualityAutomorphism` for the transpose
bundle (formerly a bespoke transport proof).  The bar-X class input is unfolded to
its parity-coset form and fed to the generic lemma. -/
theorem hgp_compiled_barX_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpHelpers d),
      qceval (hgpCircuit d)
        (QCState.clean ((hgpUParams d hd).n + hgpHelpers d)) sigma →
      (hgpLogicalClassX d hd).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpHelpers d) sigma) →
      d ≤ sigma.lambda := by
  intro sigma hrun hcls
  obtain ⟨h0, h1⟩ := hcls
  exact compiled_barX_of_dualityAutomorphism (hgpDualityAutomorphism d hd) sigma hrun
    (fun i => h0 _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
    (h1 _ (List.mem_singleton.mpr rfl))

-- Regression guards (axiom pins) for the chunk-3 headliners.
/--
info: 'QStab.QClifford.Compile.errLocsWithContextAux_hConj' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms errLocsWithContextAux_hConj

/--
info: 'QStab.QClifford.Compile.propagateCircuit_hConj_paulis' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms propagateCircuit_hConj_paulis

/--
info: 'QStab.QClifford.Compile.targetFaultDataResidual_hConj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms targetFaultDataResidual_hConj

/--
info: 'QStab.QClifford.Compile.hgp_hvalid_hConj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_hvalid_hConj

/--
info: 'QStab.QClifford.Compile.hgpD_compiled_barZ_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpD_compiled_barZ_distance

/--
info: 'QStab.QClifford.Compile.hgp_compiled_barX_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_compiled_barX_distance

end QStab.QClifford.Compile
