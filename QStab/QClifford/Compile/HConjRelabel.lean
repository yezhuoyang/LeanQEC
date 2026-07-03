import QStab.QClifford.Compile.HGPNZAssembly

/-!
# The H-conjugation relabel functor (duality transport, chunk 1)

`hConjCircuit π fc` conjugates every qubit by Hadamard and permutes qubits by
`π`: CNOTs reverse, `|0⟩`-preps become `|+⟩`-preps, and each `measZ` becomes
the synthesized X-measurement `H; measZ; H` — with **no new error locations**
(the site structure maps 1-1) and **no new detector advances** (only `measZ`
advances the cursor).

This is *not* a pure relabeling: the image circuit is not a
`compileGadgetBlock` stream.  Nothing downstream re-runs the gadget
classifiers on the image; the X-side floor transports `hvalid` along the
functor instead (chunk 3).

## The pin (falsify before proving)

Before any equivariance proof, the functor is `#eval`-pinned on the **real**
`compileProgram (hgpXZProgram 3)`: error-location counts, per-site detector
cursors, and the full per-site data-residual tables of the image circuit must
be exactly the sector-transpose + X↔Z image of the original's — for every
site and every injected Pauli.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford

/-- One-gate H-conjugation + relabel: the deterministic (gate-only) kernel of
    the functor.  CNOTs reverse; `measZ` synthesizes the X-measurement. -/
def hConjGate {nq : Nat} (π : Equiv.Perm (Fin nq)) : Gate nq → List (Gate nq)
  | .cnot c t hne => [.cnot (π t) (π c) (fun h => hne (π.injective h).symm)]
  | .hadamard q => [.hadamard (π q)]
  | .prepZero q => [.prepPlus (π q)]
  | .prepPlus q => [.prepZero (π q)]
  | .measZ q => [.hadamard (π q), .measZ (π q), .hadamard (π q)]

/-- One-instruction H-conjugation + relabel.  `errLoc` maps 1-1; `measZ`
    synthesizes the X-measurement from raw gates (no error locations). -/
def hConjInstr {nq : Nat} (π : Equiv.Perm (Fin nq)) : FInstr nq → List (FInstr nq)
  | .errLoc q => [.errLoc (π q)]
  | .gate g => (hConjGate π g).map .gate

/-- The circuit-level functor. -/
def hConjCircuit {nq : Nat} (π : Equiv.Perm (Fin nq)) (fc : FCircuit nq) :
    FCircuit nq :=
  fc.flatMap (hConjInstr π)

/-- The gate-level functor: the deterministic suffix of an image site. -/
def hConjGates {nq : Nat} (π : Equiv.Perm (Fin nq)) (c : Circuit nq) :
    Circuit nq :=
  c.flatMap (hConjGate π)

/-! ## The Pauli equivariance layer -/

theorem hadamardAction_ne_I {p : Pauli} (hp : p ≠ Pauli.I) :
    hadamardAction p ≠ Pauli.I := by cases p <;> simp_all [hadamardAction]

theorem hadamardAction_pauliMul (a b : Pauli) :
    hadamardAction (pauliMul a b) = pauliMul (hadamardAction a) (hadamardAction b) := by
  cases a <;> cases b <;> rfl

theorem xPart_hadamardAction (p : Pauli) :
    xPart (hadamardAction p) = hadamardAction (zPart p) := by cases p <;> rfl

theorem zPart_hadamardAction (p : Pauli) :
    zPart (hadamardAction p) = hadamardAction (xPart p) := by cases p <;> rfl

/-! ## The per-gate H-conjugation algebra (deterministic level)

The whole Pauli case analysis of the functor lives here, once, at the
deterministic `propagateCircuit` level; both the `qceval` simulation
(`qcstep_hConj`) and the residual-classification transport (chunk 3)
consume it. -/

/-- **One gate.**  The image block of one gate propagates a `π`-permuted,
    H-conjugated Pauli field to the `π`-permuted, H-conjugated image of the
    original gate's propagation. -/
theorem propagateGate_hConj_paulis {nq : Nat} (π : Equiv.Perm (Fin nq))
    (g : Gate nq) {es fs : ErrorState nq}
    (hp : ∀ q, fs.paulis (π q) = hadamardAction (es.paulis q)) :
    ∀ q, (propagateCircuit (hConjGate π g) fs).paulis (π q)
      = hadamardAction ((propagateGate g es).paulis q) := by
  intro q
  cases g with
  | cnot c t hne =>
    show (propagateGate (.cnot (π t) (π c)
        (fun h => hne (π.injective h).symm)) fs).paulis (π q)
      = hadamardAction ((propagateGate (.cnot c t hne) es).paulis q)
    simp only [propagateGate]
    by_cases hqc : q = c
    · subst hqc
      -- `π q` is the image TARGET; the original takes its control-branch
      rw [if_pos rfl, if_neg (fun h : q = t => hne h), if_pos rfl,
        hp t, hp q, xPart_hadamardAction, ← hadamardAction_pauliMul]
    · by_cases hqt : q = t
      · subst hqt
        -- `π q` is the image CONTROL; the original takes its target-branch
        rw [if_neg (fun h => hqc (π.injective h)), if_pos rfl, if_pos rfl,
          hp c, hp q, zPart_hadamardAction, ← hadamardAction_pauliMul]
      · rw [if_neg (fun h => hqc (π.injective h)),
          if_neg (fun h => hqt (π.injective h)),
          if_neg hqt, if_neg hqc, hp q]
  | hadamard q0 =>
    show (propagateGate (.hadamard (π q0)) fs).paulis (π q)
      = hadamardAction ((propagateGate (.hadamard q0) es).paulis q)
    simp only [propagateGate]
    by_cases hq : q = q0
    · subst hq; rw [if_pos rfl, if_pos rfl, hp q]
    · rw [if_neg (fun h => hq (π.injective h)), if_neg hq, hp q]
  | prepZero q0 =>
    show (propagateGate (.prepPlus (π q0)) fs).paulis (π q)
      = hadamardAction ((propagateGate (.prepZero q0) es).paulis q)
    simp only [propagateGate]
    by_cases hq : q = q0
    · subst hq; rw [if_pos rfl, if_pos rfl]; rfl
    · rw [if_neg (fun h => hq (π.injective h)), if_neg hq, hp q]
  | prepPlus q0 =>
    show (propagateGate (.prepZero (π q0)) fs).paulis (π q)
      = hadamardAction ((propagateGate (.prepPlus q0) es).paulis q)
    simp only [propagateGate]
    by_cases hq : q = q0
    · subst hq; rw [if_pos rfl, if_pos rfl]; rfl
    · rw [if_neg (fun h => hq (π.injective h)), if_neg hq, hp q]
  | measZ q0 =>
    -- image block: H; measZ; H — net pauli action is the identity, as is
    -- the original `measZ`'s
    show (propagateGate (.hadamard (π q0)) (propagateGate (.measZ (π q0))
        (propagateGate (.hadamard (π q0)) fs))).paulis (π q)
      = hadamardAction ((propagateGate (.measZ q0) es).paulis q)
    simp only [propagateGate]
    by_cases hq : q = q0
    · subst hq
      rw [if_pos rfl, if_pos rfl, hadamardAction_involutive, hp q]
    · rw [if_neg (fun h => hq (π.injective h)), if_neg (fun h => hq (π.injective h)),
        hp q]

/-- **A gate list.**  `propagateCircuit` along the H-conjugated image of a
    deterministic circuit intertwines with `π` + `hadamardAction` on the
    Pauli field — the residual-equivariance workhorse of chunk 3. -/
theorem propagateCircuit_hConj_paulis {nq : Nat} (π : Equiv.Perm (Fin nq)) :
    ∀ (c : Circuit nq) {es fs : ErrorState nq},
      (∀ q, fs.paulis (π q) = hadamardAction (es.paulis q)) →
      ∀ q, (propagateCircuit (hConjGates π c) fs).paulis (π q)
        = hadamardAction ((propagateCircuit c es).paulis q)
  | [], _, _, hp, q => hp q
  | g :: gs, es, fs, hp, q => by
    show (propagateCircuit (hConjGate π g ++ hConjGates π gs) fs).paulis (π q)
      = hadamardAction ((propagateCircuit gs (propagateGate g es)).paulis q)
    rw [Standard.propagateCircuit_append]
    exact propagateCircuit_hConj_paulis π gs
      (propagateGate_hConj_paulis π g hp) q

/-! ## `qceval` equivariance along the functor -/

/-- The simulation relation: same fault count, paulis `π`-permuted and
    H-conjugated.  Flips/detectors are unconstrained — the compiled distance
    floors read only paulis and `λ`. -/
def HRel {nq : Nat} (π : Equiv.Perm (Fin nq)) (σ τ : QCState nq) : Prop :=
  τ.lambda = σ.lambda ∧ ∀ q, τ.es.paulis (π q) = hadamardAction (σ.es.paulis q)

theorem HRel_clean {nq : Nat} (π : Equiv.Perm (Fin nq)) :
    HRel π (QCState.clean nq) (QCState.clean nq) :=
  ⟨rfl, fun _ => rfl⟩

private theorem qceval_append {nq : Nat} {l1 l2 : FCircuit nq} {σ σ1 σ2 : QCState nq}
    (h1 : qceval l1 σ σ1) (h2 : qceval l2 σ1 σ2) : qceval (l1 ++ l2) σ σ2 := by
  induction h1 with
  | nil _ => exact h2
  | cons i is σ σm σ' hstep _ ih => exact qceval.cons i _ σ σm σ2 hstep (ih h2)

/-- A raw gate list runs deterministically: `qceval` reaches exactly the
    `propagateCircuit` image with unchanged `λ`. -/
private theorem qceval_gateList {nq : Nat} :
    ∀ (gl : List (Gate nq)) (τ : QCState nq),
      qceval (gl.map .gate) τ ⟨propagateCircuit gl τ.es, τ.lambda⟩
  | [], τ => qceval.nil τ
  | g :: gs, τ =>
    qceval.cons _ _ _ _ _ (qcstep.step_gate g τ)
      (qceval_gateList gs ⟨propagateGate g τ.es, τ.lambda⟩)

/-- One-instruction simulation: every step of `fc` is matched by a run of its
    image block preserving `HRel`.  The gate case is the factored
    `propagateGate_hConj_paulis`. -/
private theorem qcstep_hConj {nq : Nat} (π : Equiv.Perm (Fin nq))
    {i : FInstr nq} {σ σ' τ : QCState nq}
    (hstep : qcstep i σ σ') (hrel : HRel π σ τ) :
    ∃ τ', qceval (hConjInstr π i) τ τ' ∧ HRel π σ' τ' := by
  obtain ⟨hlam, hp⟩ := hrel
  cases hstep with
  | step_gate g σ =>
    exact ⟨⟨propagateCircuit (hConjGate π g) τ.es, τ.lambda⟩,
      qceval_gateList (hConjGate π g) τ, hlam,
      propagateGate_hConj_paulis π g hp⟩
  | step_idle q σ =>
    exact ⟨τ, qceval.cons _ [] _ _ _ (qcstep.step_idle (π q) τ) (qceval.nil _),
      hlam, hp⟩
  | step_inject q σ p hpne =>
    refine ⟨⟨τ.es.inject (π q) (hadamardAction p), τ.lambda + 1⟩,
      qceval.cons _ [] _ _ _
        (qcstep.step_inject (π q) τ (hadamardAction p) (hadamardAction_ne_I hpne))
        (qceval.nil _),
      by show τ.lambda + 1 = σ.lambda + 1; omega, fun q' => ?_⟩
    show (τ.es.inject (π q) (hadamardAction p)).paulis (π q')
      = hadamardAction ((σ.es.inject q p).paulis q')
    simp only [ErrorState.inject]
    by_cases hq : q' = q
    · subst hq
      rw [if_pos rfl, if_pos rfl, hadamardAction_pauliMul, hp q']
    · rw [if_neg (fun h => hq (π.injective h)), if_neg hq, hp q']

/-- **`qceval` equivariance.**  Every run of `fc` is matched by a run of
    `hConjCircuit π fc` with the same fault count and `π`-permuted,
    H-conjugated paulis. -/
theorem qceval_hConj {nq : Nat} (π : Equiv.Perm (Fin nq))
    {fc : FCircuit nq} {σ σ' : QCState nq}
    (hrun : qceval fc σ σ') :
    ∀ {τ : QCState nq}, HRel π σ τ →
      ∃ τ', qceval (hConjCircuit π fc) τ τ' ∧ HRel π σ' τ' := by
  induction hrun with
  | nil σ =>
    intro τ hrel
    exact ⟨τ, qceval.nil τ, hrel⟩
  | cons i is σ σm σ' hstep _ ih =>
    intro τ hrel
    obtain ⟨τm, hτm, hrelm⟩ := qcstep_hConj π hstep hrel
    obtain ⟨τ', hτ', hrel'⟩ := ih hrelm
    exact ⟨τ', by
      show qceval (hConjInstr π i ++ (is.flatMap (hConjInstr π))) τ τ'
      exact qceval_append hτm hτ', hrel'⟩

/-! ## The parametric site table of the image circuit

The parametric form of pins 2–3 below: error sites of `hConjCircuit π fc`
are exactly the sites of `fc` with `π`-relabeled qubits, H-conjugated
deterministic suffixes, and **identical** detector cursors (the synthesized
`H` gates advance no detector). -/

private theorem eraseFaults_gateMap_append {nq : Nat} (gl : List (Gate nq))
    (fc : FCircuit nq) :
    eraseFaults (gl.map .gate ++ fc) = gl ++ eraseFaults fc := by
  induction gl with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.cons_append, eraseFaults_gate, ih]

/-- Fault erasure intertwines the two functor levels. -/
theorem eraseFaults_hConj {nq : Nat} (π : Equiv.Perm (Fin nq)) :
    ∀ fc : FCircuit nq,
      eraseFaults (hConjCircuit π fc) = hConjGates π (eraseFaults fc)
  | [] => rfl
  | .gate g :: rest => by
    show eraseFaults ((hConjGate π g).map .gate ++ hConjCircuit π rest) = _
    rw [eraseFaults_gateMap_append, eraseFaults_hConj π rest]
    rfl
  | .errLoc q :: rest => by
    show eraseFaults (.errLoc (π q) :: hConjCircuit π rest) = _
    rw [eraseFaults_errLoc]
    exact eraseFaults_hConj π rest

private theorem errLocsWithContextAux_gateMap {nq : Nat} (gl : List (Gate nq)) :
    ∀ (cursor : Nat) (fc : FCircuit nq),
      PCC.errLocsWithContextAux cursor (gl.map .gate ++ fc)
        = PCC.errLocsWithContextAux
            (cursor + (gl.map PCC.gateDetectorAdvance).sum) fc := by
  induction gl with
  | nil => intro cursor fc; simp
  | cons g gs ih =>
    intro cursor fc
    simp only [List.map_cons, List.cons_append, PCC.errLocsWithContextAux,
      List.sum_cons]
    rw [ih]
    congr 1
    omega

private theorem hConjGate_advance {nq : Nat} (π : Equiv.Perm (Fin nq))
    (g : Gate nq) :
    ((hConjGate π g).map PCC.gateDetectorAdvance).sum
      = PCC.gateDetectorAdvance g := by
  cases g <;> rfl

/-- **The parametric site table** (the parametric form of pins 2–3): the
    image circuit's error sites are the `π`-relabeled sites of the original
    with H-conjugated suffixes and identical detector cursors. -/
theorem errLocsWithContextAux_hConj {nq : Nat} (π : Equiv.Perm (Fin nq)) :
    ∀ (fc : FCircuit nq) (cursor : Nat),
      PCC.errLocsWithContextAux cursor (hConjCircuit π fc)
        = (PCC.errLocsWithContextAux cursor fc).map
            (fun s => ⟨π s.q, hConjGates π s.suffix, s.detectorStart⟩)
  | [], _ => rfl
  | .gate g :: rest, cursor => by
    show PCC.errLocsWithContextAux cursor
        ((hConjGate π g).map .gate ++ hConjCircuit π rest) = _
    rw [errLocsWithContextAux_gateMap, hConjGate_advance]
    exact errLocsWithContextAux_hConj π rest _
  | .errLoc q :: rest, cursor => by
    show (⟨π q, eraseFaults (hConjCircuit π rest), cursor⟩ :
          PCC.ErrLocWithContext nq)
        :: PCC.errLocsWithContextAux cursor (hConjCircuit π rest) = _
    rw [eraseFaults_hConj, errLocsWithContextAux_hConj π rest cursor]
    rfl

/-! ## The HGP dual permutation (ambient form) -/

/-- Sector-wise transpose on the HGP data block, identity on helpers:
    sector 1 `(a,b) ↦ (b,a)`, sector 2 `(r,c) ↦ (c,r)`, `q ≥ d²+(d-1)²`
    fixed. -/
def hgpDualNat (d q : Nat) : Nat :=
  if q < d * d then (q % d) * d + q / d
  else if q < d * d + (d - 1) * (d - 1) then
    d * d + ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1)
  else q

/-! ## Pin at `d = 3` (before any proof)

The concrete permutation on the 25 ambient qubits (13 data + 12 helpers),
inverses checked by kernel `decide`; then the functor is run on the real
compiled circuit. -/

private def nq3 : Nat := 13 + programHelperCount (hgpXZProgram 3)

private def hgpDualFin3 : Fin nq3 → Fin nq3 :=
  fun q => ⟨hgpDualNat 3 q.val % nq3, Nat.mod_lt _ (by decide)⟩

private def hgpDualPerm3 : Equiv.Perm (Fin nq3) where
  toFun := hgpDualFin3
  invFun := hgpDualFin3
  left_inv := by decide
  right_inv := by decide

private def fc3 : FCircuit nq3 := compileProgram (hgpXZProgram 3)
private def fc3D : FCircuit nq3 := hConjCircuit hgpDualPerm3 fc3

private def sites (fc : FCircuit nq3) : List (PCC.ErrLocWithContext nq3) :=
  PCC.errLocsWithContextAux (QCState.clean nq3).es.detectorCursor fc

private theorem thirteen_le_nq3 : 13 ≤ nq3 := by decide

/-- Data residual of injecting `p` at a site, rendered as a support table. -/
private def residualTable (s : PCC.ErrLocWithContext nq3) (p : Pauli) :
    List (Nat × Pauli) :=
  let es := propagateCircuit s.suffix
    ((PCC.cleanAtDetector s.detectorStart).inject s.q p)
  (List.finRange 13).filterMap fun q =>
    match es.paulis ⟨q.val, Nat.lt_of_lt_of_le q.isLt thirteen_le_nq3⟩ with
    | Pauli.I => none
    | pp => some (q.val, pp)

/-- The expected dual image of a residual table: qubit sector-transposed,
    Pauli H-conjugated, re-sorted by qubit. -/
private def dualTable (t : List (Nat × Pauli)) : List (Nat × Pauli) :=
  ((t.map fun (q, p) => (hgpDualNat 3 q, hadamardAction p)).toArray.qsort
    (fun a b => a.1 < b.1)).toList

-- Pin 1: error-location counts agree (144 sites each: prep + per-coupling
-- (2 for a bare CNOT, 4 for an H-sandwiched one) + measure, per gadget).
/-- info: (144, 144) -/
#guard_msgs in
#eval ((sites fc3).length, (sites fc3D).length)

-- Pin 2: per-site detector cursors agree (H adds no detector advance).
/-- info: true -/
#guard_msgs in
#eval ((sites fc3).map (·.detectorStart)) == ((sites fc3D).map (·.detectorStart))

-- Pin 3: per-site qubits are the π-image.
/-- info: true -/
#guard_msgs in
#eval ((sites fc3).map (fun s => (hgpDualPerm3 s.q).val))
  == ((sites fc3D).map (·.q.val))

-- Pin 4 (the classification table): at every site and every injected Pauli,
-- the image circuit's data residual is exactly the sector-transposed,
-- H-conjugated residual of the original at the H-conjugated Pauli.
/-- info: true -/
#guard_msgs in
#eval ((sites fc3).zip (sites fc3D)).all fun (s, sD) =>
  [Pauli.X, Pauli.Y, Pauli.Z].all fun p =>
    dualTable (residualTable s (hadamardAction p)) == residualTable sD p

-- Pin 5 (chunk 3): the parametric site-table lemma's `d = 3` specialization
-- reproduces the pinned site data — all three fields, suffix gates included.
private def gateBEq : Gate nq3 → Gate nq3 → Bool
  | .cnot c t _, .cnot c' t' _ => c == c' && t == t'
  | .hadamard q, .hadamard q' => q == q'
  | .prepZero q, .prepZero q' => q == q'
  | .prepPlus q, .prepPlus q' => q == q'
  | .measZ q, .measZ q' => q == q'
  | _, _ => false

private def siteBEq (a b : PCC.ErrLocWithContext nq3) : Bool :=
  a.q == b.q && a.detectorStart == b.detectorStart
    && a.suffix.length == b.suffix.length
    && (a.suffix.zip b.suffix).all fun (g, g') => gateBEq g g'

/-- info: true -/
#guard_msgs in
#eval ((sites fc3D).length == 144)
  && (((sites fc3D).zip ((sites fc3).map fun s =>
      ⟨hgpDualPerm3 s.q, hConjGates hgpDualPerm3 s.suffix, s.detectorStart⟩)).all
        fun (a, b) => siteBEq a b)

-- Regression guards: an axiom drift in the chunk-1 headliners breaks the build.
/-- info: 'QStab.QClifford.Compile.qceval_hConj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms qceval_hConj

/-- info: 'QStab.QClifford.Compile.HRel_clean' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms HRel_clean

end QStab.QClifford.Compile
