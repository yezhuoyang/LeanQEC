import QStab.QClifford.Compile.HoarePreservation

/-!
# (E_tilde, C)-refinement preservation layer

The generic `ProgramInvariantSimulation` interface pins a *fixed* abstraction map
`QCState → State P` and requires the compiler-built `SourceTraceDeriv` to reproduce
the target QStab state **exactly** — including path-dependent bookkeeping fields
(`cnt0..cnt3`, `lam_E`, `G`, `F`) that are not functions of the QClifford state.

But the surface barrier invariant only reads `(E_tilde, C)`
(`surfaceBarrierSymbol.eval E_tilde + (C_budget − C)`), and the compiled backend
`qcliffordDataBackend` only exposes the data residual and the fault budget.  So the
sound and sufficient refinement is the **`(E_tilde, C)`-only** one:

  for every budgeted QClifford run reaching `σ`, *some* QStab state `st` is reachable
  with `st.E_tilde = dataErrorOfQCState σ` and `st.C = C_budget − σ.λ`;

the auxiliary fields of `st` are then free (they never enter the invariant).  This
file provides the preservation theorem for that refinement, reducing the compiler
Hoare-logic preservation to two obligations:

* `hFold`  — the semantic simulation core: build the reachable `st` (drives `G1`);
* `hMatch` — the barrier translation `I.denote st → compileFormula`.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QHL
open QHL.AssertionLang
open QHL.Source.Branch

/-- **(E_tilde, C)-refinement Hoare-logic preservation.**  A QStab invariant
certificate plus an `(E_tilde, C)`-only simulation (`hFold`) and the barrier
translation (`hMatch`) yield the compiled target `FHoare`.  Unlike the generic
interface this never reconstructs the path-dependent QStab bookkeeping. -/
theorem etildeC_hoare_preservation {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {fc : FCircuit (P.n + k)} {I : Formula P []}
    (cert : InvariantCertificate prog I)
    (hFold : ∀ sigma : QCState (P.n + k),
      qceval fc (QCState.clean (P.n + k)) sigma → sigma.lambda ≤ P.C_budget →
        ∃ st : State P,
          MultiStep prog (.active (State.init P)) (.active st) ∧
            st.E_tilde = dataErrorOfQCState P k sigma ∧
            st.C = P.C_budget - sigma.lambda)
    (hMatch : ∀ (st : State P) (sigma : QCState (P.n + k)),
      st.E_tilde = dataErrorOfQCState P k sigma → st.C = P.C_budget - sigma.lambda →
        sigma.lambda ≤ P.C_budget → I.denote st → compileFormula k I sigma) :
    FHoare
      (fun sigma : QCState (P.n + k) => sigma = QCState.clean (P.n + k))
      fc
      (compileFormulaWithinBudget k I) := by
  intro sigma sigma' hrun hclean hbudget
  subst hclean
  obtain ⟨st, hreach, hE, hC⟩ := hFold sigma' hrun hbudget
  exact hMatch st sigma' hE hC hbudget (cert.check_active_sound st hreach)

/-- **`hMatch` for any barrier invariant.**  The barrier reads only `error`,
`remaining`, `budget`, and these agree between the QStab backend at `st` and the
compiled `qcliffordDataBackend` at `sigma` whenever `(E_tilde, C)` match — so the
barrier denotation transports across the abstraction. -/
theorem barrier_hMatch {P : QECParams} {k : Nat} (beta : BarrierSymbol P)
    (L : LogicalClassSymbol P) (st : State P) (sigma : QCState (P.n + k))
    (hE : st.E_tilde = dataErrorOfQCState P k sigma)
    (hC : st.C = P.C_budget - sigma.lambda)
    (hbudget : sigma.lambda ≤ P.C_budget)
    (hden : (barrierInvF beta L).denote st) :
    compileFormula k (barrierInvF beta L) sigma := by
  simp only [barrierInvF, barrierPotentialF, spentF, Formula.denote, Formula.eval,
    Term.eval, qstabBackend] at hden
  simp only [compileFormula, Formula.denoteWith, barrierInvF, barrierPotentialF, spentF,
    Formula.evalWith, Term.evalWith, qcliffordDataBackend]
  rw [hE, hC] at hden
  refine ⟨?_, ?_⟩
  · have := hden.1; omega
  · have := hden.2; omega

/-! ## `hFold` keystone: the composition soundness (`E_tilde = net residual`)

The remaining obligation `hFold` builds a reachable QStab state whose `E_tilde` is
the net QClifford data residual.  The keystone is that the net residual is the Pauli
composition of the per-fault residuals — a pure soundness fact resting on the
`Homomorphism.lean` factorisation.  We start with the fault-free base case. -/

/-- A fault-free QClifford run (`λ` unchanged) leaves the error state equal to plain
gate propagation of the initial one — the base of the fault composition. -/
theorem qceval_clean_run {nq : Nat} : ∀ {fc : FCircuit nq} {σ σ' : QCState nq},
    qceval fc σ σ' → σ'.lambda = σ.lambda →
      σ'.es = propagateCircuit (eraseFaults fc) σ.es := by
  intro fc σ σ' hrun
  induction hrun with
  | nil σ => intro _; simp [eraseFaults, propagateCircuit]
  | cons i is σ σm σ' hstep hrest ih =>
      intro hlam
      cases hstep with
      | step_gate g σ0 =>
          simp only [eraseFaults_gate, propagateCircuit]
          exact ih hlam
      | step_idle q σ0 =>
          simp only [eraseFaults_errLoc]
          exact ih hlam
      | step_inject q _ p hp =>
          exfalso
          have hlm : σ.lambda + 1 ≤ σ'.lambda := (fcevalW_of_qceval hrest).1
          omega

/-! ### Self-contained paulis-only Pauli homomorphism

`Homomorphism.lean` predates the `detectors`/`detectorCursor` fields of `ErrorState`
and its full-state `propagateGate_mul` is now false on `detectors` (`measZ` updates
them).  Only the *data residual* (`paulis`) matters here, and the paulis part **is** a
homomorphism, so we rebuild exactly that, self-contained. -/

/-- Paulis-only product: pointwise `pauliMul` on the Pauli field (other fields from
`es`). `dataErrorOfQCState` reads only `paulis`, so this is all we need. -/
def pmulS {nq : Nat} (es fs : ErrorState nq) : ErrorState nq :=
  { es with paulis := fun i => pauliMul (es.paulis i) (fs.paulis i) }

private theorem xPart_pmul (a b : Pauli) : xPart (pauliMul a b) = pauliMul (xPart a) (xPart b) := by
  cases a <;> cases b <;> rfl
private theorem zPart_pmul (a b : Pauli) : zPart (pauliMul a b) = pauliMul (zPart a) (zPart b) := by
  cases a <;> cases b <;> rfl
private theorem had_pmul (a b : Pauli) :
    hadamardAction (pauliMul a b) = pauliMul (hadamardAction a) (hadamardAction b) := by
  cases a <;> cases b <;> rfl
private theorem pmul_midswap (a b c d : Pauli) :
    pauliMul (pauliMul a b) (pauliMul c d) = pauliMul (pauliMul a c) (pauliMul b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
private theorem pmul_comm (a b : Pauli) : pauliMul a b = pauliMul b a := by
  cases a <;> cases b <;> rfl

/-- Gate propagation is a homomorphism on the Pauli field. -/
theorem propagateGate_pmulS {nq : Nat} (g : Gate nq) (es fs : ErrorState nq) (d : Fin nq) :
    (propagateGate g (pmulS es fs)).paulis d =
      pauliMul ((propagateGate g es).paulis d) ((propagateGate g fs).paulis d) := by
  cases g with
  | cnot c t h =>
      simp only [propagateGate, pmulS]
      split_ifs with h1 h2
      · rw [xPart_pmul]; exact pmul_midswap _ _ _ _
      · rw [zPart_pmul]; exact pmul_midswap _ _ _ _
      · rfl
  | hadamard q =>
      simp only [propagateGate, pmulS]
      split_ifs with h1
      · rw [had_pmul]
      · rfl
  | prepZero q =>
      simp only [propagateGate, pmulS]; split_ifs with h1 <;> rfl
  | prepPlus q =>
      simp only [propagateGate, pmulS]; split_ifs with h1 <;> rfl
  | measZ q =>
      simp only [propagateGate, pmulS]

/-- Gate propagation's Pauli field depends only on the input Pauli field. -/
theorem propagateGate_paulis_congr {nq : Nat} (g : Gate nq) {es fs : ErrorState nq}
    (h : es.paulis = fs.paulis) : (propagateGate g es).paulis = (propagateGate g fs).paulis := by
  cases g <;> (funext i; simp only [propagateGate, h])

/-- Circuit propagation's Pauli field depends only on the input Pauli field. -/
theorem propagateCircuit_paulis_congr {nq : Nat} (c : Circuit nq) {es fs : ErrorState nq}
    (h : es.paulis = fs.paulis) (d : Fin nq) :
    (propagateCircuit c es).paulis d = (propagateCircuit c fs).paulis d := by
  induction c generalizing es fs with
  | nil => simp only [propagateCircuit]; rw [h]
  | cons g gs ih => simp only [propagateCircuit]; exact ih (propagateGate_paulis_congr g h)

/-- Circuit propagation is a homomorphism on the Pauli field. -/
theorem propagateCircuit_pmulS {nq : Nat} (c : Circuit nq) (es fs : ErrorState nq) (d : Fin nq) :
    (propagateCircuit c (pmulS es fs)).paulis d =
      pauliMul ((propagateCircuit c es).paulis d) ((propagateCircuit c fs).paulis d) := by
  induction c generalizing es fs with
  | nil => rfl
  | cons g gs ih =>
      simp only [propagateCircuit]
      rw [propagateCircuit_paulis_congr gs
        (show (propagateGate g (pmulS es fs)).paulis =
            (pmulS (propagateGate g es) (propagateGate g fs)).paulis from by
          funext i; rw [propagateGate_pmulS]; rfl) d]
      exact ih _ _

/-- A single injection on the Pauli field is right-multiplication by the lone fault. -/
theorem inject_pmulS_paulis {nq : Nat} (es : ErrorState nq) (q : Fin nq) (p : Pauli) (i : Fin nq) :
    (es.inject q p).paulis i =
      (pmulS es ((ErrorState.clean nq).inject q p)).paulis i := by
  simp only [ErrorState.inject, pmulS, ErrorState.clean]
  split_ifs with h
  · rw [pauliMul_I_right]; exact pmul_comm _ _
  · rw [pauliMul_I_right]

/-- **Single-fault factorisation through a circuit** (paulis field): the residual of
`inject`-then-propagate is the product of the ambient residual and the lone-fault
residual. -/
theorem propagateCircuit_inject_paulis_factor {nq : Nat} (c : Circuit nq) (es : ErrorState nq)
    (q : Fin nq) (p : Pauli) (d : Fin nq) :
    (propagateCircuit c (es.inject q p)).paulis d =
      pauliMul ((propagateCircuit c es).paulis d)
        ((propagateCircuit c ((ErrorState.clean nq).inject q p)).paulis d) := by
  rw [propagateCircuit_paulis_congr c (funext (fun i => inject_pmulS_paulis es q p i))]
  exact propagateCircuit_pmulS c es ((ErrorState.clean nq).inject q p) d

/-- `foldr pmulS` reads only the base's Pauli field. -/
theorem foldr_pmulS_paulis_congr {nq : Nat} (l : List (ErrorState nq)) {x y : ErrorState nq}
    (h : x.paulis = y.paulis) (d : Fin nq) :
    (l.foldr pmulS x).paulis d = (l.foldr pmulS y).paulis d := by
  induction l with
  | nil => show x.paulis d = y.paulis d; rw [h]
  | cons c cs ih => simp only [List.foldr, pmulS]; rw [ih]

/-- **Fault composition of a QClifford run** (paulis field).  The net data residual
factors as the clean gate propagation times a product of per-fault residuals — each a
lone fault propagated through the remaining circuit.  This is the keystone soundness
that ties `dataErrorOfQCState σ'` to the accumulated QStab `E_tilde`. -/
theorem qceval_es_factor {nq : Nat} : ∀ {fc : FCircuit nq} {σ σ' : QCState nq},
    qceval fc σ σ' →
      ∃ contribs : List (ErrorState nq),
        contribs.length = σ'.lambda - σ.lambda ∧
          ∀ d, σ'.es.paulis d =
            (contribs.foldr pmulS (propagateCircuit (eraseFaults fc) σ.es)).paulis d := by
  intro fc σ σ' hrun
  induction hrun with
  | nil σ =>
      exact ⟨[], by simp, fun d => by simp [eraseFaults, propagateCircuit, List.foldr]⟩
  | cons i is σ σm σ' hstep hrest ih =>
      obtain ⟨contribs, hlen, hes⟩ := ih
      cases hstep with
      | step_gate g σ0 =>
          exact ⟨contribs, by simpa using hlen, fun d => by
            rw [hes d]; simp only [eraseFaults_gate, propagateCircuit]⟩
      | step_idle q σ0 =>
          exact ⟨contribs, by simpa using hlen, fun d => by
            rw [hes d]; simp only [eraseFaults_errLoc]⟩
      | step_inject q σ0 p hp =>
          refine ⟨contribs ++ [propagateCircuit (eraseFaults is) ((ErrorState.clean nq).inject q p)],
            ?_, fun d => ?_⟩
          · have hmono : σ.lambda + 1 ≤ σ'.lambda := (fcevalW_of_qceval hrest).1
            have hlen' : contribs.length = σ'.lambda - (σ.lambda + 1) := hlen
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · rw [hes d]
            simp only [eraseFaults_errLoc, List.foldr_append, List.foldr]
            refine foldr_pmulS_paulis_congr contribs (funext fun d' => ?_) d
            simp only [pmulS]
            rw [propagateCircuit_inject_paulis_factor]
            exact pmul_comm _ _

/-! ### `E_tilde` tracking through a `StepAt` derivation node

Each syntactic `StepAt` branch is, semantically, left-multiplication of `E_tilde`
by the branch's `dataResidual`.  This per-step soundness lets a chained
`SourceTraceDeriv` accumulate `E_tilde` into exactly the `qceval_es_factor`
product — the bridge between the compiler-side derivation and the composition. -/

private theorem qmul_I_left (p : Pauli) : Pauli.mul Pauli.I p = p := by cases p <;> rfl
private theorem qmul_I_right (p : Pauli) : Pauli.mul p Pauli.I = p := by cases p <;> rfl

/-- `identity` is a left unit for `ErrorVec.mul`. -/
theorem errorVec_mul_identity_left {n : Nat} (e : ErrorVec n) :
    ErrorVec.mul (ErrorVec.identity n) e = e := by
  funext i; simp only [ErrorVec.mul, ErrorVec.identity]; exact qmul_I_left _

/-- A single-qubit `update` is left-multiplication by the corresponding singleton
residual — the key identity making `err0`/`errI` compose like `errII`. -/
theorem update_eq_mul_singleton {P : QECParams} (e : ErrorVec P.n) (i : Fin P.n) (p : Pauli) :
    ErrorVec.update e i p = ErrorVec.mul (singleDataResidual P i p) e := by
  funext j
  simp only [ErrorVec.update, ErrorVec.mul, singleDataResidual, ErrorVec.identity,
    Function.update_apply]
  split_ifs with h
  · subst h; rw [qmul_I_right]
  · rw [qmul_I_left]

/-- **Per-step `E_tilde` law.**  Every syntactic `StepAt` branch multiplies
`E_tilde` on the left by its `dataResidual`. -/
theorem stepAt_E_tilde {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {fault : FiredFaultWithContext (P.n + k)} {branch : CompiledFaultBranch P}
    {st st' : State P}
    (h : CompiledFaultBranch.StepAt prog fault branch st st') :
    st'.E_tilde = ErrorVec.mul branch.dataResidual st.E_tilde := by
  cases h with
  | silent st =>
      simp only [CompiledFaultBranch.dataResidual]; rw [errorVec_mul_identity_left]
  | branch hlabel hstep =>
      cases branch with
      | silent => simp [CompiledFaultBranch.label] at hlabel
      | err0 i p hp =>
          simp only [CompiledFaultBranch.label, Option.some.injEq] at hlabel
          subst hlabel; cases hstep
          simp only [CompiledFaultBranch.dataResidual]; rw [update_eq_mul_singleton]
      | errI i p hp mf =>
          simp only [CompiledFaultBranch.label, Option.some.injEq] at hlabel
          subst hlabel; cases hstep
          simp only [CompiledFaultBranch.dataResidual]; rw [update_eq_mul_singleton]
      | errII e mf =>
          simp only [CompiledFaultBranch.label, Option.some.injEq] at hlabel
          subst hlabel; cases hstep
          simp only [CompiledFaultBranch.dataResidual]
      | errIII =>
          simp only [CompiledFaultBranch.label, Option.some.injEq] at hlabel
          subst hlabel; cases hstep
          simp only [CompiledFaultBranch.dataResidual]; rw [errorVec_mul_identity_left]

/-- The data residual a `TransitionLabel` contributes to `E_tilde`. -/
def labelDataResidual {P : QECParams} : TransitionLabel P → ErrorVec P.n
  | .err0 i p => singleDataResidual P i p
  | .errI i p _ => singleDataResidual P i p
  | .errII e _ => e
  | .errIII => ErrorVec.identity P.n
  | .meas => ErrorVec.identity P.n

/-- **Per-transition `E_tilde` law.**  Every QStab branch transition left-muls
`E_tilde` by its label's data residual; the scheduled measurement leaves `E_tilde`
fixed.  This is the transition-tree analogue of `stepAt_E_tilde`, and drives the
`SourceTraceDeriv`-level accumulation used by the fault-fold consumer. -/
theorem transitionStep_E_tilde {P : QECParams} {prog : QStabProgram P}
    {label : TransitionLabel P} {st st' : State P}
    (h : TransitionStep prog label st st') :
    st'.E_tilde = ErrorVec.mul (labelDataResidual label) st.E_tilde := by
  cases h with
  | err0 st i p hp hC => simp only [labelDataResidual]; rw [update_eq_mul_singleton]
  | errI st i p hp mf hC => simp only [labelDataResidual]; rw [update_eq_mul_singleton]
  | errII st e he mf hC => simp only [labelDataResidual]
  | errIII st hC => simp only [labelDataResidual]; rw [errorVec_mul_identity_left]
  | meas st nc hN =>
      simp only [labelDataResidual]; rw [errorVec_mul_identity_left]; rfl

/-- **`SourceTraceDeriv`-level `E_tilde` accumulation.**  The endpoint `E_tilde` of a
syntactic source derivation is the product (in circuit order) of every fault node's
label residual, applied to the start `E_tilde`.  `silent`/`meas` nodes contribute
nothing.  This is the derivation-tree accumulation law that, combined with
`qceval_es_factor`, closes `hFold`. -/
theorem sourceTraceDeriv_E_tilde {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {st st' : State P} {faults : List (FiredFaultWithContext (P.n + k))}
    (d : SourceTraceDeriv prog st faults st') :
    ∃ residuals : List (ErrorVec P.n),
      st'.E_tilde = residuals.foldr ErrorVec.mul st.E_tilde := by
  induction d with
  | nil st => exact ⟨[], rfl⟩
  | @fault st st1 st2 fault faults sourceStep _ ih =>
      obtain ⟨residuals, hres⟩ := ih
      refine ⟨residuals ++ [labelDataResidual sourceStep.label], ?_⟩
      rw [hres, List.foldr_append]
      simp only [List.foldr]
      rw [transitionStep_E_tilde sourceStep.step]
  | silent _ ih => exact ih
  | @meas st st1 st2 faults measStep _ ih =>
      obtain ⟨residuals, hres⟩ := ih
      have hm : st1.E_tilde = st.E_tilde := by
        rw [transitionStep_E_tilde measStep]; exact errorVec_mul_identity_left _
      exact ⟨residuals, by rw [hres, hm]⟩

/-! ### `ErrorVec.mul` is a commutative monoid, and `foldr`-product normalisation

The chain accumulates each fault residual as a left-multiplication, so we need the
Pauli-group commutativity/associativity to normalise the product into circuit order. -/

private theorem qmul_comm (a b : Pauli) : Pauli.mul a b = Pauli.mul b a := by
  cases a <;> cases b <;> rfl
private theorem qmul_assoc (a b c : Pauli) :
    Pauli.mul (Pauli.mul a b) c = Pauli.mul a (Pauli.mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem errorVec_mul_comm {n : Nat} (a b : ErrorVec n) : ErrorVec.mul a b = ErrorVec.mul b a := by
  funext i; simp only [ErrorVec.mul]; exact qmul_comm _ _

theorem errorVec_mul_assoc {n : Nat} (a b c : ErrorVec n) :
    ErrorVec.mul (ErrorVec.mul a b) c = ErrorVec.mul a (ErrorVec.mul b c) := by
  funext i; simp only [ErrorVec.mul]; exact qmul_assoc _ _ _

/-- Pull a left factor into a `foldr` product base (commutative monoid). -/
theorem foldr_mul_pull {n : Nat} (a b : ErrorVec n) (l : List (ErrorVec n)) :
    ErrorVec.mul a (l.foldr ErrorVec.mul b) = l.foldr ErrorVec.mul (ErrorVec.mul a b) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldr]
      rw [← errorVec_mul_assoc, errorVec_mul_comm a c, errorVec_mul_assoc, ih]

/-! ### The fault-fold consumer (piece 1)

For each fired fault the residual weight selects the QStab rule that realises it —
`errIII` (weight 0), `err0` (weight 1), or `errII` (multi-qubit hook, valid by the
closedness of the back-action set).  In every case the rule's data residual is the
fault's data residual, so chaining the rules accumulates `E_tilde` into the product. -/

/-- The QStab step realising one fault, with the residual/budget bookkeeping. -/
structure StepOut {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (f : FiredFaultWithContext (P.n + k)) (st : State P) where
  label : TransitionLabel P
  target : State P
  step : TransitionStep prog label st target
  residual : labelDataResidual label = targetFaultDataResidual P f
  budget : target.C = st.C - 1

/-- Realise one fault as a QStab transition, selecting the rule by residual weight.
The validity hypothesis supplies `backActionSet` membership for multi-qubit hooks. -/
noncomputable def buildStep {P : QECParams} {prog : QStabProgram P} {k : Nat}
    (f : FiredFaultWithContext (P.n + k)) (st : State P) (hC : 0 < st.C)
    (hvalid : ErrorVec.weight (targetFaultDataResidual P f) ≤ 1 ∨
       ∀ st' : State P, targetFaultDataResidual P f ∈ P.backActionSet (currentStab prog st')) :
    StepOut prog f st := by
  by_cases hw0 : ErrorVec.weight (targetFaultDataResidual P f) = 0
  · exact
      { label := .errIII, target := _
        step := TransitionStep.errIII (prog := prog) st hC
        residual := by
          simp only [labelDataResidual]
          exact (errorVec_eq_identity_of_weight_zero _ hw0).symm
        budget := rfl }
  · by_cases hw1 : ErrorVec.weight (targetFaultDataResidual P f) = 1
    · let s := errorVecSingletonOfWeightOne (targetFaultDataResidual P f) hw1
      exact
        { label := .err0 s.i s.p, target := _
          step := TransitionStep.err0 (prog := prog) st s.i s.p s.hp hC
          residual := by simp only [labelDataResidual, singleDataResidual]; exact s.eq_singleton.symm
          budget := rfl }
    · have hba : ∀ st' : State P,
          targetFaultDataResidual P f ∈ P.backActionSet (currentStab prog st') := by
        rcases hvalid with hle | hba
        · exfalso; omega
        · exact hba
      exact
        { label := .errII (targetFaultDataResidual P f) false, target := _
          step := TransitionStep.errII (prog := prog) st _ (hba st) false hC
          residual := rfl
          budget := rfl }

/-- The whole fault-fold: chaining the per-fault steps into one source derivation,
its endpoint `E_tilde` the residual product, its `C` the decremented budget. -/
structure ChainOut {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (faults : List (FiredFaultWithContext (P.n + k))) (st : State P) where
  target : State P
  deriv : SourceTraceDeriv prog st faults target
  etilde : target.E_tilde =
    (faults.map (targetFaultDataResidual P)).foldr ErrorVec.mul st.E_tilde
  budget : target.C = st.C - faults.length

/-- Fold the run's faults into a syntactic source derivation whose endpoint matches
the QClifford data residual (`E_tilde`) and remaining budget (`C`). -/
noncomputable def buildChain {P : QECParams} {prog : QStabProgram P} {k : Nat} :
    (faults : List (FiredFaultWithContext (P.n + k))) → (st : State P) →
      faults.length ≤ st.C →
      (∀ f ∈ faults, ErrorVec.weight (targetFaultDataResidual P f) ≤ 1 ∨
        ∀ st' : State P, targetFaultDataResidual P f ∈ P.backActionSet (currentStab prog st')) →
      ChainOut prog faults st
  | [], st, _, _ =>
      { target := st, deriv := .nil st, etilde := by simp, budget := by simp }
  | f :: rest, st, hC, hvalid =>
      let so := buildStep f st (by simp only [List.length_cons] at hC; omega)
        (hvalid f List.mem_cons_self)
      let recr := buildChain rest so.target
        (by simp only [List.length_cons] at hC; rw [so.budget]; omega)
        (fun f' hf' => hvalid f' (List.mem_cons_of_mem _ hf'))
      { target := recr.target
        deriv := SourceTraceDeriv.fault { label := so.label, step := so.step } recr.deriv
        etilde := by
          have hso : so.target.E_tilde =
              ErrorVec.mul (targetFaultDataResidual P f) st.E_tilde := by
            rw [transitionStep_E_tilde so.step, so.residual]
          rw [recr.etilde, hso]
          simp only [List.map_cons, List.foldr]
          rw [foldr_mul_pull]
        budget := by
          simp only [List.length_cons] at hC ⊢
          rw [recr.budget, so.budget]; omega }

/-- **Assembly.**  Given the run's faults with per-fault validity and the residual-
product connection, fold them into a reachable QStab state whose `E_tilde` is the
QClifford data residual and whose `C` is the remaining budget — the `hFold` shape
consumed by `etildeC_hoare_preservation`. -/
theorem faults_to_reachable {P : QECParams} {prog : QStabProgram P} {k : Nat}
    (σ : QCState (P.n + k)) (faults : List (FiredFaultWithContext (P.n + k)))
    (hlen : faults.length = σ.lambda)
    (hbudget : σ.lambda ≤ P.C_budget)
    (hvalid : ∀ f ∈ faults, ErrorVec.weight (targetFaultDataResidual P f) ≤ 1 ∨
      ∀ st' : State P, targetFaultDataResidual P f ∈ P.backActionSet (currentStab prog st'))
    (hproduct : dataErrorOfQCState P k σ =
      (faults.map (targetFaultDataResidual P)).foldr ErrorVec.mul (ErrorVec.identity P.n)) :
    ∃ st : State P, MultiStep prog (.active (State.init P)) (.active st) ∧
      st.E_tilde = dataErrorOfQCState P k σ ∧ st.C = P.C_budget - σ.lambda := by
  have hC : faults.length ≤ (State.init P).C := by rw [hlen]; exact hbudget
  let chain := buildChain faults (State.init P) hC hvalid
  refine ⟨chain.target, chain.deriv.toMultiStep, ?_, ?_⟩
  · rw [chain.etilde]; exact hproduct.symm
  · rw [chain.budget, hlen]; rfl

/-! ### `hproduct`: the residual-product connection

`targetFaultEffect` injects on `cleanAtDetector`, which differs from `clean` only in
`detectorCursor` — invisible to `paulis`.  So `targetFaultEffect`'s Pauli field is the
`clean`-injection propagated through the suffix, matching `qceval_es_factor`'s contribs. -/

/-- `targetFaultEffect`'s Pauli field is the lone `clean` injection propagated through
the fault's suffix (`cleanAtDetector` differs from `clean` only in `detectorCursor`). -/
theorem targetFaultEffect_paulis {P : QECParams} {k : Nat}
    (f : FiredFaultWithContext (P.n + k)) (d : Fin (P.n + k)) :
    (targetFaultEffect f).paulis d =
      (propagateCircuit f.site.suffix
        ((ErrorState.clean (P.n + k)).inject f.site.q f.pauli)).paulis d := by
  simp only [targetFaultEffect]
  refine propagateCircuit_paulis_congr f.site.suffix ?_ d
  funext i
  simp only [ErrorState.inject, QStab.QClifford.PCC.cleanAtDetector, ErrorState.clean]

/-- **Combined fault extraction with data product.**  One induction over the
`fcevalW` run yields the fired faults (with detector-cursor sites), their
`errLocsWithContextAux` membership, and the fact that the final Pauli field is the
`pmulS`-product of the per-fault `targetFaultEffect`s over the clean gate propagation.
This is the `fcevalW`-level statement underlying `hproduct`. -/
theorem fcevalW_faults_product {P : QECParams} {k : Nat} :
    ∀ {w : Nat} {fc : FCircuit (P.n + k)} {es es' : ErrorState (P.n + k)},
      fcevalW w fc es es' →
        ∀ cursor : Nat, es.detectorCursor = cursor →
          ∃ faults : List (FiredFaultWithContext (P.n + k)),
            faults.length = w ∧
            (∀ fault ∈ faults,
              fault.site ∈ QStab.QClifford.PCC.errLocsWithContextAux cursor fc) ∧
            (∀ d, es'.paulis d =
              ((faults.map (fun f => targetFaultEffect f)).foldr pmulS
                (propagateCircuit (eraseFaults fc) es)).paulis d) := by
  intro w fc es es' hrun
  induction hrun with
  | nil es =>
      intro cursor _
      exact ⟨[], rfl, fun _ h => by simp at h,
        fun d => by simp [eraseFaults, propagateCircuit, List.foldr]⟩
  | gate g rest es es' w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem, hprod⟩ :=
        ih (cursor + QStab.QClifford.PCC.gateDetectorAdvance g)
          (by rw [propagateGate_detectorCursor_eq, hcursor])
      refine ⟨faults, hlen, ?_, ?_⟩
      · intro fault hfault
        simpa [QStab.QClifford.PCC.errLocsWithContextAux] using hmem fault hfault
      · intro d; rw [hprod d]; simp only [eraseFaults_gate, propagateCircuit]
  | idle q rest es es' w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem, hprod⟩ := ih cursor hcursor
      refine ⟨faults, hlen, ?_, ?_⟩
      · intro fault hfault
        simp only [QStab.QClifford.PCC.errLocsWithContextAux, List.mem_cons]
        exact Or.inr (hmem fault hfault)
      · intro d; rw [hprod d]; simp only [eraseFaults_errLoc]
  | inject q rest es es' p hp w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem, hprod⟩ := ih cursor (by simp [ErrorState.inject, hcursor])
      let fired : FiredFaultWithContext (P.n + k) := ⟨⟨q, eraseFaults rest, cursor⟩, p, hp⟩
      refine ⟨faults ++ [fired], by simp [hlen], ?_, ?_⟩
      · intro fault hfault
        simp only [List.mem_append, List.mem_singleton] at hfault
        simp only [QStab.QClifford.PCC.errLocsWithContextAux, List.mem_cons]
        rcases hfault with h | rfl
        · exact Or.inr (hmem fault h)
        · exact Or.inl rfl
      · intro d
        rw [hprod d]
        simp only [List.map_append, List.map_cons, List.map_nil, List.foldr_append,
          List.foldr, eraseFaults_errLoc]
        refine foldr_pmulS_paulis_congr _ (funext fun d' => ?_) d
        rw [propagateCircuit_inject_paulis_factor]
        simp only [pmulS]
        rw [targetFaultEffect_paulis fired d']
        exact pmul_comm _ _

/-- Gate propagation fixes the clean Pauli field (`I` maps to `I`). -/
theorem propagateGate_clean_paulis {nq : Nat} (g : Gate nq) :
    (propagateGate g (ErrorState.clean nq)).paulis = (ErrorState.clean nq).paulis := by
  funext d; cases g <;> simp only [propagateGate, ErrorState.clean] <;> split_ifs <;> rfl

/-- Clean gate propagation leaves every Pauli `I` — the base of the fault product. -/
theorem propagateCircuit_clean_paulis {nq : Nat} (c : Circuit nq) (d : Fin nq) :
    (propagateCircuit c (ErrorState.clean nq)).paulis d = Pauli.I := by
  induction c generalizing d with
  | nil => rfl
  | cons g gs ih =>
      simp only [propagateCircuit]
      rw [propagateCircuit_paulis_congr gs (propagateGate_clean_paulis g)]
      exact ih d

/-- The `pmulS`-product over data qubits is the `ErrorVec.mul`-product of the
per-state data residuals — the bridge from `pmulS` (QClifford) to `ErrorVec.mul`
(QStab). -/
theorem foldr_pmulS_data {P : QECParams} {k : Nat} (l : List (ErrorState (P.n + k)))
    (base : ErrorState (P.n + k)) (q : Fin P.n) :
    (l.foldr pmulS base).paulis (freshDataQ P.n k q) =
      ((l.map (fun es => fun q' => es.paulis (freshDataQ P.n k q'))).foldr ErrorVec.mul
        (fun q' => base.paulis (freshDataQ P.n k q'))) q := by
  induction l with
  | nil => rfl
  | cons es rest ih =>
      simp only [List.foldr, List.map_cons, pmulS, ErrorVec.mul]
      rw [ih, QStab.QClifford.PCC.pauliMul_eq_mul]

/-- **`hproduct`.**  For a clean-start QClifford run, the data residual is the
`ErrorVec.mul`-product of the per-fault `targetFaultDataResidual`s over the extracted
faults — with their `errLocsWithContextAux` membership.  This is exactly the
`(hproduct, faults, site_mem)` bundle `faults_to_reachable` consumes. -/
theorem hproduct_of_qceval {P : QECParams} {k : Nat} {fc : FCircuit (P.n + k)}
    {σ : QCState (P.n + k)} (hrun : qceval fc (QCState.clean (P.n + k)) σ) :
    ∃ faults : List (FiredFaultWithContext (P.n + k)),
      faults.length = σ.lambda ∧
      (∀ fault ∈ faults, fault.site ∈
        QStab.QClifford.PCC.errLocsWithContextAux (QCState.clean (P.n + k)).es.detectorCursor fc) ∧
      dataErrorOfQCState P k σ =
        (faults.map (targetFaultDataResidual P)).foldr ErrorVec.mul (ErrorVec.identity P.n) := by
  obtain ⟨_, hindex⟩ := fcevalW_of_qceval hrun
  obtain ⟨faults, hlen, hmem, hprod⟩ := fcevalW_faults_product hindex _ rfl
  refine ⟨faults, by simpa using hlen, hmem, ?_⟩
  funext q
  show σ.es.paulis (freshDataQ P.n k q) = _
  rw [hprod (freshDataQ P.n k q), foldr_pmulS_data, List.map_map]
  have hbase : (fun q' => (propagateCircuit (eraseFaults fc)
      (QCState.clean (P.n + k)).es).paulis (freshDataQ P.n k q')) = ErrorVec.identity P.n := by
    funext q'
    simp [QCState.clean_es, propagateCircuit_clean_paulis, ErrorVec.identity]
  rw [hbase]
  rfl

/-- **Generic `hFold`.**  Combining `hproduct_of_qceval` (composition) with
`faults_to_reachable` (fold): a clean-start QClifford run reaches a QStab state whose
`E_tilde` is the QClifford data residual and whose `C` is the remaining budget —
provided each fired fault is a low-weight data error or an in-`backActionSet` hook.
This is the exact `hFold` hypothesis of `etildeC_hoare_preservation`, reduced to the
per-fault validity `hvalid` (supplied per scheme by its `G1`/closedness). -/
theorem hFold_of_valid {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {fc : FCircuit (P.n + k)} {σ : QCState (P.n + k)}
    (hrun : qceval fc (QCState.clean (P.n + k)) σ) (hbudget : σ.lambda ≤ P.C_budget)
    (hvalid : ∀ f : FiredFaultWithContext (P.n + k),
      f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
        (QCState.clean (P.n + k)).es.detectorCursor fc →
      ErrorVec.weight (targetFaultDataResidual P f) ≤ 1 ∨
        ∀ st' : State P, targetFaultDataResidual P f ∈ P.backActionSet (currentStab prog st')) :
    ∃ st : State P, MultiStep prog (.active (State.init P)) (.active st) ∧
      st.E_tilde = dataErrorOfQCState P k σ ∧ st.C = P.C_budget - σ.lambda := by
  obtain ⟨faults, hlen, hmem, hprod⟩ := hproduct_of_qceval hrun
  exact faults_to_reachable σ faults hlen hbudget (fun f hf => hvalid f (hmem f hf)) hprod

end QStab.QClifford.Compile
