import QStab.QClifford.Compile.SurfaceRhoSpread
import QStab.QClifford.Compile.SurfaceNZAssembly
import QStab.QClifford.Compile.SurfaceHValid

/-!
# The compiled bar-X distance floor by ρ-duality transport (F2b)

The surface mirror of `HGPXDistance.lean`, with the order-4 ρ in place of the
involutive transpose and the ρ-rotated union machine (`rhoSurfaceSpec`) in place
of exact Φ-closure:

* **residual transport** along the generic functor (`hConjCircuit` /
  `propagateCircuit_hConj_paulis`, reused verbatim): the data residual of an
  image fault is the `rhoPhi`-image of the original site's residual;
* **hvalid transport**: weight-1 sites stay weight-1 (`rhoPhi_weight`); hook
  sites land in the ρ-machine's back-action set by the right injection;
* **the bridge on the image circuit** (instantiated, never widened): the same
  `etildeC_hoare_preservation` / `hFold_of_valid` / `compiled_barrier_distance`
  chain over `rhoSurfaceSpec`'s certificate gives the bar-Z floor on `fc†`;
* **class conversion + pullback**: parity ρ-equivariance and the σρ-inverse
  composition identity convert a bar-X residual of the real run into a bar-Z
  residual of the simulated run (`qceval_hConj` transports paulis + λ only);
  `ρ(X̄) = Z̄` closes the anticommutation leg.

Headline: `surface_compiled_barX_distance` — stated over the real
`compileProgram (surfaceXZProgram d hd)` in the exact `SurfaceBarXFloor` shape.
-/

namespace QStab.QClifford.Compile

open QStab QStab.Examples QStab.Examples.SurfaceParametric QStab.Examples.SurfaceGeneral
open QStab.QClifford QStab.QClifford.PCC.SurfaceNZ
open QHL QHL.AssertionLang
open QHL.Source.Examples.Surface
open QHL.Source.Examples.SurfaceExactDistance QHL.Source.Examples.SurfaceUnionSpec
open QHL.Source.Examples.SurfaceParametricUpperBound

/-! ## The ambient ρ-permutation and the image circuit -/

/-- QEC params of the ρ-rotated bridge (budget `d`). -/
abbrev surfaceRhoParams (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : QECParams :=
  (rhoSurfaceSpec d hd3 hodd).params

/-- The ambient ρ-permutation on the compiled layout: 90° rotation on the data
block, identity on the compiler's helper qubits. -/
def surfaceRhoAmbientPerm (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    Equiv.Perm (Fin ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd)) :=
  rhoPermAmbient d _ hd (Nat.le_add_right _ _)

/-- The ρ-conjugated image of the compiled surface circuit — a proof-internal
transport target.  **Not** claimed to be a `compileProgram` image. -/
def surfaceCircuitRhoD (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    FCircuit ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd) :=
  hConjCircuit (surfaceRhoAmbientPerm d hd hd3 hodd) (surfaceCircuit d hd)

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
`rhoPhi`-image of the original site's residual at the H-conjugated Pauli. -/
theorem targetFaultDataResidual_rho (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1)
    (s : QStab.QClifford.PCC.ErrLocWithContext
      ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd))
    (p : Pauli) (hp : p ≠ Pauli.I) :
    targetFaultDataResidual (surfaceUParams d hd3 hodd)
        (⟨⟨surfaceRhoAmbientPerm d hd hd3 hodd s.q,
            hConjGates (surfaceRhoAmbientPerm d hd hd3 hodd) s.suffix,
            s.detectorStart⟩, p, hp⟩)
      = rhoPhi d hd (targetFaultDataResidual (surfaceUParams d hd3 hodd)
          ⟨s, hadamardAction p, hadamardAction_ne_I hp⟩) := by
  funext q
  have hkey := propagateCircuit_hConj_paulis (surfaceRhoAmbientPerm d hd hd3 hodd) s.suffix
    (inject_clean_hConj_rel (surfaceRhoAmbientPerm d hd hd3 hodd) s.detectorStart s.q p)
    (freshDataQ (surfaceUParams d hd3 hodd).n (surfaceHelpers d hd)
      ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩)
  have hidx : surfaceRhoAmbientPerm d hd hd3 hodd
        (freshDataQ (surfaceUParams d hd3 hodd).n (surfaceHelpers d hd)
          ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩)
      = freshDataQ (surfaceUParams d hd3 hodd).n (surfaceHelpers d hd) q :=
    Fin.ext (rho_rightInv d q.val hd)
  rw [hidx] at hkey
  exact hkey

/-! ## `hvalid` for the image circuit -/

/-- The image-circuit `hvalid` obligation over the ρ-rotated machine. -/
def SurfaceHValidRhoD (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : Prop :=
  ∀ f : FiredFaultWithContext
      ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd),
    f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
      (QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd)).es.detectorCursor
      (surfaceCircuitRhoD d hd hd3 hodd) →
    ErrorVec.weight (targetFaultDataResidual (surfaceUParams d hd3 hodd) f) ≤ 1 ∨
      ∀ st' : State (surfaceRhoParams d hd3 hodd),
        targetFaultDataResidual (surfaceUParams d hd3 hodd) f ∈
          (surfaceRhoParams d hd3 hodd).backActionSet
            (currentStab (surfaceProgram d (rhoSurfaceSpec d hd3 hodd)) st')

/-- **`hvalid` transported along the functor**: every fault site of the image
circuit has a weight-`≤ 1` data residual or a hook in the ρ-machine's
back-action set (the right injection of the rotated union). -/
theorem surface_hvalid_rhoD (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    SurfaceHValidRhoD d hd hd3 hodd := by
  rintro ⟨site, p, hp⟩ hmem
  rw [show surfaceCircuitRhoD d hd hd3 hodd
        = hConjCircuit (surfaceRhoAmbientPerm d hd hd3 hodd) (surfaceCircuit d hd) from rfl,
    errLocsWithContextAux_hConj] at hmem
  obtain ⟨s, hs, hsite⟩ := List.mem_map.mp hmem
  cases hsite
  have hres := targetFaultDataResidual_rho d hd hd3 hodd s p hp
  rw [hres]
  rcases surface_hvalid d hd hd3 hodd ⟨s, hadamardAction p, hadamardAction_ne_I hp⟩ hs
    with hw | hbk
  · left
    exact le_of_eq_of_le (rhoPhi_weight d hd _) hw
  · right
    intro _
    obtain ⟨s₀, hs₀⟩ := hbk (State.init _)
    exact Or.inr ⟨s₀, _, hs₀, rfl⟩

/-! ## The bridge on the image circuit (instantiated, never widened) -/

/-- The compiled bar-Z invariant holds on the **image** circuit, over the
ρ-machine's certificate. -/
theorem surfaceRhoD_compiled_FHoare (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) :
    FHoare
      (fun sigma : QCState ((surfaceRhoParams d hd3 hodd).n + surfaceHelpers d hd) =>
        sigma = QCState.clean ((surfaceRhoParams d hd3 hodd).n + surfaceHelpers d hd))
      (surfaceCircuitRhoD d hd hd3 hodd)
      (compileFormulaWithinBudget (surfaceHelpers d hd)
        (surface_inv_formula d (rhoSurfaceSpec d hd3 hodd))) :=
  etildeC_hoare_preservation
    (surface_invariant_certificate d (rhoSurfaceSpec d hd3 hodd))
    (fun _ hrun hb => hFold_of_valid hrun hb (surface_hvalid_rhoD d hd hd3 hodd))
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- The bar-Z distance floor on the **image** circuit. -/
theorem surfaceRhoD_compiled_barZ_distance (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) :
    ∀ sigma : QCState ((surfaceRhoParams d hd3 hodd).n + surfaceHelpers d hd),
      qceval (surfaceCircuitRhoD d hd hd3 hodd)
        (QCState.clean ((surfaceRhoParams d hd3 hodd).n + surfaceHelpers d hd)) sigma →
      (surfaceLogicalClass d (rhoSurfaceSpec d hd3 hodd)).contains
        (dataErrorOfQCState (surfaceRhoParams d hd3 hodd) (surfaceHelpers d hd) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (surfaceRhoD_compiled_FHoare d hd hd3 hodd)
    (fun E hE => alignedBarZ_barrier_eval_zero "surface.beta" "surface.rows" "surface.barZ"
      (rhoSurfaceSpec d hd3 hodd).toAligned E hE)
    (Nat.le_refl d)

/-! ## The σρ-inverse composition (order-4 bookkeeping) -/

/-- The inverse check permutation (270° on blocks). -/
def rhoCheckInv (d k : Nat) : Nat :=
  if k < (d - 1) * (d - 1) then
    bulkIdx d (d - 2 - k % (d - 1)) (k / (d - 1))
  else if k < (d - 1) * (d - 1) + (d - 1) / 2 then
    leftZIdx d ((d - 1) / 2 - 1 - (k - (d - 1) * (d - 1)))
  else if k < (d - 1) * (d - 1) + 2 * ((d - 1) / 2) then
    topXIdx d (k - ((d - 1) * (d - 1) + (d - 1) / 2))
  else if k < (d - 1) * (d - 1) + 3 * ((d - 1) / 2) then
    bottomXIdx d (k - ((d - 1) * (d - 1) + 2 * ((d - 1) / 2)))
  else
    rightZIdx d ((d - 1) / 2 - 1 - (k - ((d - 1) * (d - 1) + 3 * ((d - 1) / 2))))

theorem rhoCheckInv_lt_numStab (d k : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hk : k < numStabFormula d) : rhoCheckInv d k < numStabFormula d := by
  have hk' : k < (d - 1) * (d - 1) + 2 * (d - 1) := by
    unfold numStabFormula at hk; omega
  have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
  unfold rhoCheckInv
  by_cases h1 : k < (d - 1) * (d - 1)
  · rw [if_pos h1]
    exact bulkIdx_lt_numStab d _ _ hd
      (Nat.lt_of_le_of_lt (Nat.sub_le (d - 2) (k % (d - 1))) (by omega : d - 2 < d - 1))
      (Nat.div_lt_of_lt_mul h1)
  · rw [if_neg h1]
    by_cases h2 : k < (d - 1) * (d - 1) + (d - 1) / 2
    · rw [if_pos h2]; exact leftZIdx_lt_numStab d _ hd (by omega)
    · rw [if_neg h2]
      by_cases h3 : k < (d - 1) * (d - 1) + 2 * ((d - 1) / 2)
      · rw [if_pos h3]; exact topXIdx_lt_numStab d _ hd (by omega)
      · rw [if_neg h3]
        by_cases h4 : k < (d - 1) * (d - 1) + 3 * ((d - 1) / 2)
        · rw [if_pos h4]; exact bottomXIdx_lt_numStab d _ hd hodd (by omega)
        · rw [if_neg h4]; exact rightZIdx_lt_numStab d _ hd (by omega)

/-- **σρ ∘ σρ⁻¹ = id** on check indices. -/
theorem rhoCheck_rhoCheckInv (d k : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hk : k < numStabFormula d) : rhoCheck d (rhoCheckInv d k) = k := by
  have hk' : k < (d - 1) * (d - 1) + 2 * (d - 1) := by
    unfold numStabFormula at hk; omega
  have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
  unfold rhoCheckInv
  by_cases h1 : k < (d - 1) * (d - 1)
  · rw [if_pos h1]
    obtain ⟨r', hr'⟩ : ∃ x, k / (d - 1) = x := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ x, k % (d - 1) = x := ⟨_, rfl⟩
    have hr'lt : r' < d - 1 := hr' ▸ Nat.div_lt_of_lt_mul h1
    have hc'lt : c' < d - 1 := hc' ▸ Nat.mod_lt _ (by omega)
    rw [hr', hc']
    unfold rhoCheck
    have hblt : bulkIdx d (d - 2 - c') r' < (d - 1) * (d - 1) :=
      bulkIdx_lt_bulkCount d _ _
        (Nat.lt_of_le_of_lt (Nat.sub_le (d - 2) c') (by omega : d - 2 < d - 1)) hr'lt
    rw [if_pos hblt]
    obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d (d - 2 - c') r' hd hr'lt
    rw [hdiv, hmod, show d - 2 - (d - 2 - c') = c' by omega]
    show r' * (d - 1) + c' = k
    rw [← hr', ← hc', Nat.mul_comm]
    exact Nat.div_add_mod k (d - 1)
  · rw [if_neg h1]
    by_cases h2 : k < (d - 1) * (d - 1) + (d - 1) / 2
    · rw [if_pos h2]
      unfold rhoCheck
      have e1 : ¬(leftZIdx d ((d - 1) / 2 - 1 - (k - (d - 1) * (d - 1))) < (d - 1) * (d - 1)) := by
        unfold leftZIdx; omega
      have e2 : ¬(leftZIdx d ((d - 1) / 2 - 1 - (k - (d - 1) * (d - 1)))
          < (d - 1) * (d - 1) + (d - 1) / 2) := by
        unfold leftZIdx; omega
      have e3 : ¬(leftZIdx d ((d - 1) / 2 - 1 - (k - (d - 1) * (d - 1)))
          < (d - 1) * (d - 1) + 2 * ((d - 1) / 2)) := by
        unfold leftZIdx; omega
      have e4 : leftZIdx d ((d - 1) / 2 - 1 - (k - (d - 1) * (d - 1)))
          < (d - 1) * (d - 1) + 3 * ((d - 1) / 2) := by
        unfold leftZIdx; omega
      rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4]
      unfold topXIdx leftZIdx
      omega
    · rw [if_neg h2]
      by_cases h3 : k < (d - 1) * (d - 1) + 2 * ((d - 1) / 2)
      · rw [if_pos h3]
        unfold rhoCheck
        have e1 : ¬(topXIdx d (k - ((d - 1) * (d - 1) + (d - 1) / 2)) < (d - 1) * (d - 1)) := by
          unfold topXIdx; omega
        have e2 : topXIdx d (k - ((d - 1) * (d - 1) + (d - 1) / 2))
            < (d - 1) * (d - 1) + (d - 1) / 2 := by
          unfold topXIdx; omega
        rw [if_neg e1, if_pos e2]
        unfold rightZIdx topXIdx
        omega
      · rw [if_neg h3]
        by_cases h4 : k < (d - 1) * (d - 1) + 3 * ((d - 1) / 2)
        · rw [if_pos h4]
          unfold rhoCheck
          have e1 : ¬(bottomXIdx d (k - ((d - 1) * (d - 1) + 2 * ((d - 1) / 2)))
              < (d - 1) * (d - 1)) := by
            unfold bottomXIdx; omega
          have e2 : ¬(bottomXIdx d (k - ((d - 1) * (d - 1) + 2 * ((d - 1) / 2)))
              < (d - 1) * (d - 1) + (d - 1) / 2) := by
            unfold bottomXIdx; omega
          have e3 : ¬(bottomXIdx d (k - ((d - 1) * (d - 1) + 2 * ((d - 1) / 2)))
              < (d - 1) * (d - 1) + 2 * ((d - 1) / 2)) := by
            unfold bottomXIdx; omega
          have e4 : ¬(bottomXIdx d (k - ((d - 1) * (d - 1) + 2 * ((d - 1) / 2)))
              < (d - 1) * (d - 1) + 3 * ((d - 1) / 2)) := by
            unfold bottomXIdx; omega
          rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4]
          unfold leftZIdx bottomXIdx
          omega
        · rw [if_neg h4]
          unfold rhoCheck
          have e1 : ¬(rightZIdx d ((d - 1) / 2 - 1
              - (k - ((d - 1) * (d - 1) + 3 * ((d - 1) / 2)))) < (d - 1) * (d - 1)) := by
            unfold rightZIdx; omega
          have e2 : ¬(rightZIdx d ((d - 1) / 2 - 1
              - (k - ((d - 1) * (d - 1) + 3 * ((d - 1) / 2))))
              < (d - 1) * (d - 1) + (d - 1) / 2) := by
            unfold rightZIdx; omega
          have e3 : rightZIdx d ((d - 1) / 2 - 1
              - (k - ((d - 1) * (d - 1) + 3 * ((d - 1) / 2))))
              < (d - 1) * (d - 1) + 2 * ((d - 1) / 2) := by
            unfold rightZIdx; omega
          rw [if_neg e1, if_neg e2, if_pos e3]
          unfold bottomXIdx rightZIdx
          omega

/-- **Stab-row surjectivity of the ρ-transport**: every generator row is the
`Φρ`-image of its σρ-preimage's row. -/
theorem mkSurfaceStabilizers_rho_surj (d : Nat) (hd0 : 0 < d) (hd : 1 < d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) :
    ∃ j : Fin (numStabFormula d),
      rhoPhi d hd0 (mkSurfaceStabilizers d hd0 j) = mkSurfaceStabilizers d hd0 i := by
  refine ⟨⟨rhoCheckInv d i.val, rhoCheckInv_lt_numStab d i.val hd hodd i.isLt⟩, ?_⟩
  rw [mkSurfaceStabilizers_rho d hd0 hd hodd]
  exact congrArg _ (Fin.ext (rhoCheck_rhoCheckInv d i.val hd hodd i.isLt))

/-! ## Parity ρ-equivariance and the logical conversion -/

private theorem anticommutes_hadamardAction (a b : Pauli) :
    ErrorVec.Pauli.anticommutes (hadamardAction a) (hadamardAction b)
      = ErrorVec.Pauli.anticommutes a b := by
  cases a <;> cases b <;> rfl

/-- **Parity is ρ-equivariant** (the rotation permutes anticommuting positions,
`hadamardAction` preserves anticommutation). -/
theorem parity_rhoPhi (d : Nat) (hd : 0 < d) (F E : ErrorVec (d * d)) :
    ErrorVec.parity (rhoPhi d hd F) (rhoPhi d hd E) = ErrorVec.parity F E := by
  unfold ErrorVec.parity
  have hcard : (Finset.univ.filter fun i =>
        ErrorVec.Pauli.anticommutes (F i) (E i)).card
      = (Finset.univ.filter fun i =>
        ErrorVec.Pauli.anticommutes (rhoPhi d hd F i) (rhoPhi d hd E i)).card := by
    refine Finset.card_equiv (rhoPermAmbient d (d * d) hd (Nat.le_refl _)) fun q => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have himg : ∀ (G : ErrorVec (d * d)),
        rhoPhi d hd G ((rhoPermAmbient d (d * d) hd (Nat.le_refl _)) q)
          = hadamardAction (G q) := by
      intro G
      show hadamardAction (G ⟨rhoInvNat d (rhoNat d q.val), _⟩) = hadamardAction (G q)
      exact congrArg _ (congrArg G (Fin.ext (rho_leftInv d q.val hd)))
    rw [himg F, himg E, anticommutes_hadamardAction]
  rw [hcard]

/-- **`ρ(X̄) = Z̄`**: the column-0 X string rotates onto the row-0 Z string. -/
theorem rhoPhi_attackerX (d : Nat) (hd : 0 < d) :
    rhoPhi d hd (mkSurfaceAttackerX d) = mkSurfaceLogicalZ d := by
  funext q
  show hadamardAction
    (mkSurfaceAttackerX d ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩)
    = mkSurfaceLogicalZ d q
  have hx : mkSurfaceAttackerX d ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩
      = if rhoInvNat d q.val % d = 0 then Pauli.X else Pauli.I := rfl
  rw [hx, rhoInvNat_mod d q.val hd q.isLt]
  unfold mkSurfaceLogicalZ
  by_cases h : q.val / d = 0
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-! ## ★ The compiled bar-X distance floor ★ -/

/-- **Compiled bar-X circuit-level distance for the rotated surface code.**
Every clean-start run of `compileProgram (surfaceXZProgram d hd)` whose data
residual commutes with every stabilizer and anticommutes with
`X̄ = mkSurfaceAttackerX` fired at least `d` faults — for every odd `d ≥ 3`.
Proved by ρ-duality transport: the run is simulated on the ρ-conjugated image
circuit, where its residual is bar-Z-class over the ρ-machine and the bar-Z
bridge applies; `λ` agrees between the two runs. -/
theorem surface_compiled_barX_distance (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) :
    ∀ sigma : QCState (d * d + programHelperCount (surfaceXZProgram d hd)),
      qceval (compileProgram (surfaceXZProgram d hd))
        (QCState.clean (d * d + programHelperCount (surfaceXZProgram d hd))) sigma →
      (∀ j : Fin (mkSurfaceQECParams d hd hodd).numStab,
        ErrorVec.parity ((mkSurfaceQECParams d hd hodd).stabilizers j)
          (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
            (programHelperCount (surfaceXZProgram d hd)) sigma) = false) →
      ErrorVec.parity (mkSurfaceAttackerX d)
        (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
          (programHelperCount (surfaceXZProgram d hd)) sigma) = true →
      d ≤ sigma.lambda := by
  intro sigma hrun hcent hx
  have hd1 : 1 < d := by omega
  obtain ⟨tau, hrunD, hlam, hpauli⟩ :=
    qceval_hConj (surfaceRhoAmbientPerm d hd hd3 hodd) hrun
      (HRel_clean (surfaceRhoAmbientPerm d hd hd3 hodd))
  have hdata : dataErrorOfQCState (surfaceRhoParams d hd3 hodd) (surfaceHelpers d hd) tau
      = rhoPhi d hd (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
          (programHelperCount (surfaceXZProgram d hd)) sigma) := by
    funext q
    show tau.es.paulis (freshDataQ (d * d) (surfaceHelpers d hd) q)
      = hadamardAction (sigma.es.paulis (freshDataQ (d * d) (surfaceHelpers d hd)
          ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩))
    rw [show freshDataQ (d * d) (surfaceHelpers d hd) q
        = surfaceRhoAmbientPerm d hd hd3 hodd (freshDataQ (d * d) (surfaceHelpers d hd)
            ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩)
      from Fin.ext (rho_rightInv d q.val hd).symm]
    exact hpauli _
  have hcls : (surfaceLogicalClass d (rhoSurfaceSpec d hd3 hodd)).contains
      (dataErrorOfQCState (surfaceRhoParams d hd3 hodd) (surfaceHelpers d hd) tau) := by
    rw [hdata]
    constructor
    · intro S hS
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS
      show ErrorVec.parity (mkSurfaceStabilizers d hd i) _ = false
      obtain ⟨j, hj⟩ := mkSurfaceStabilizers_rho_surj d hd hd1 hodd i
      rw [← hj, parity_rhoPhi]
      exact hcent j
    · intro T hT
      rw [List.mem_singleton.mp hT]
      show ErrorVec.parity (mkSurfaceLogicalZ d) _ = true
      rw [← rhoPhi_attackerX d hd, parity_rhoPhi]
      exact hx
  have hfloor := surfaceRhoD_compiled_barZ_distance d hd hd3 hodd tau hrunD hcls
  exact hlam ▸ hfloor

-- Regression guards (axiom pins) for the transport headliners.
/--
info: 'QStab.QClifford.Compile.surface_hvalid_rhoD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surface_hvalid_rhoD

/--
info: 'QStab.QClifford.Compile.surfaceRhoD_compiled_barZ_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surfaceRhoD_compiled_barZ_distance

/--
info: 'QStab.QClifford.Compile.surface_compiled_barX_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surface_compiled_barX_distance

end QStab.QClifford.Compile

