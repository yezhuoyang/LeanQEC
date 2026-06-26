import QStab.QClifford.StatefulFault
import QStab.QClifford.ToleratesFaults

/-! # QClifford fault-aware Hoare logic over `QCState` (the canonical F-Hoare)

This file is the **sole** F-Hoare logic for QClifford. It operates on
`QCState = (E, M, λ)` with the state-resident fault counter, and its
`F_ErrLoc` rule correctly bumps `λ` in the injection conjunct. Soundness
is proved against the `qceval` operational semantics of
`StatefulFault.lean`.

## History

Audit finding **PH-3** (2026-06-13) flagged an unsoundness in the
previous `ErrorState`-based F-Hoare: its `F_ErrLoc` precondition
`Q es ∧ ∀ p ≠ I, Q (es.inject q p)` did NOT include the `λ`-bump,
so any postcondition mentioning `λ` (the fault-tolerance condition
`λ ≤ t`) would be evaluated at the wrong state. The unsound version
has been **deleted** from the codebase (along with its only legacy
consumer, `QHL/Compile/SimTransport.lean`, a dead compiler).

This file is the sound replacement. The F-Hoare logic operates on
`QCState = (E, M, λ)` with the `λ`-bump in `F_ErrLoc`'s injection
conjunct. No other F-Hoare system exists in the project.

## Rule set (matches paper Fig fig:fault-hoare-rules exactly)

| Lean constructor | Paper rule       | Form                                                          |
|------------------|------------------|----------------------------------------------------------------|
| `F_Nil`          | F-Nil            | `{P} ε {P}`                                                    |
| `F_Gate`         | F-Gate           | `{Q[E ↦ ⟦g⟧(E)]} [g] {Q}`                                      |
| `F_ErrLoc`       | F-ErrLoc         | `{Q ∧ ⋀_{p≠I} Q[E_q ↦ p·E_q, λ ↦ λ+1]} [err(q)] {Q}`            |
| `F_App`          | F-App            | `{P} c₁ {M} {M} c₂ {Q} → {P} c₁ · c₂ {Q}`                       |
| `F_Conseq`       | F-Conseq         | strengthen pre, weaken post                                    |

The `λ`-bump in `F_ErrLoc` is the audit-PH-3 fix.

## Relationship to indexed `ToleratesFaults`

`ToleratesFaults` (in `ToleratesFaults.lean`) is the indexed form
quantifying over `fcevalW`'s error count `w`. The Hoare-triple form
of FT is

  `{ σ = QCState.clean nq } fc { σ.lambda ≤ t → ¬ failure σ.es }`

and is logically equivalent (see `toleratesFaultsΛ_of_hoare` and
`hoare_of_toleratesFaultsΛ` in `StatefulFault.lean`). The barrier-
descent path uses the indexed form; the Hoare-triple form is what
composes with the F-rules below.
-/

namespace QStab.QClifford

/-- A QCState-level fault assertion: a predicate on `QCState nq`
    (i.e. `(paulis, measFlips, lambda)`). -/
abbrev AssertionF (nq : Nat) := QCState nq → Prop

/-- **Semantic Hoare triple** over the λ-aware fault semantics: every
    `qceval` resolution from a `P`-state lands in a `Q`-state. -/
def FHoare {nq : Nat} (P : AssertionF nq) (fc : FCircuit nq) (Q : AssertionF nq) : Prop :=
  ∀ σ σ', qceval fc σ σ' → P σ → Q σ'

/-- **Hoare derivations** over the QCState fault semantics. One rule per
    `qcstep` constructor:

    * `F_Nil`    — empty program.
    * `F_Gate`   — deterministic weakest precondition for one gate:
      `Q` pulled back along `propagateGate g` on the `es` field; `λ` is
      preserved by gates so the precondition does not constrain it.
    * `F_ErrLoc` — **demonic** rule for an error location. The
      precondition must imply `Q` after the idle choice (`Q σ` itself)
      *and* after every single-qubit injection `p ≠ I` on the site's
      qubit (`Q ⟨σ.es.inject q p, σ.lambda + 1⟩`). The injection conjunct
      bumps `λ` — this is the audit-PH-3 λ-bump fix.

      **Caution**: with a tautological `Q` (e.g., `fun _ => True`), the
      precondition is also tautological and the rule is vacuous. Concrete
      applications must supply a non-trivial `Q` (e.g., a failure
      predicate or a barrier function) to obtain meaningful triples.
    * `F_App`, `F_Conseq` — standard structural rules. -/
inductive FDeriv {nq : Nat} : AssertionF nq → FCircuit nq → AssertionF nq → Type where
  | F_Nil (P : AssertionF nq) : FDeriv P [] P
  | F_Gate (g : Gate nq) (Q : AssertionF nq) :
      FDeriv (fun σ => Q ⟨propagateGate g σ.es, σ.lambda⟩) [.gate g] Q
  | F_ErrLoc (q : Fin nq) (Q : AssertionF nq) :
      FDeriv
        (fun σ => Q σ ∧ ∀ p, p ≠ Pauli.I →
                    Q ⟨σ.es.inject q p, σ.lambda + 1⟩)
        [.errLoc q] Q
  | F_App {P M Q : AssertionF nq} {c1 c2 : FCircuit nq} :
      FDeriv P c1 M → FDeriv M c2 Q → FDeriv P (c1 ++ c2) Q
  | F_And {P₁ P₂ Q₁ Q₂ : AssertionF nq} {c : FCircuit nq} :
      FDeriv P₁ c Q₁ → FDeriv P₂ c Q₂ →
      FDeriv (fun σ => P₁ σ ∧ P₂ σ) c (fun σ => Q₁ σ ∧ Q₂ σ)
  | F_Conseq {P P' Q Q' : AssertionF nq} {c : FCircuit nq} :
      FDeriv P' c Q' →
      (∀ σ, P σ → P' σ) → (∀ σ, Q' σ → Q σ) →
      FDeriv P c Q

/-! ## Inversion lemmas for `qceval` -/

/-- Running the empty program leaves the QCState unchanged. -/
theorem qceval_nil {nq : Nat} {σ σ' : QCState nq} (h : qceval [] σ σ') :
    σ' = σ := by
  cases h with | nil => rfl

/-- Inversion of a `cons` execution into a head step and a tail run. -/
theorem qceval_cons_inv {nq : Nat} {i : FInstr nq} {is : FCircuit nq}
    {σ σ' : QCState nq} (h : qceval (i :: is) σ σ') :
    ∃ σm, qcstep i σ σm ∧ qceval is σm σ' := by
  cases h with | cons _ _ _ σm _ hstep hrest => exact ⟨σm, hstep, hrest⟩

/-- Execution splits over instruction-list concatenation. -/
theorem qceval_append {nq : Nat} (c1 c2 : FCircuit nq) (σ σ' : QCState nq) :
    qceval (c1 ++ c2) σ σ' ↔ ∃ m, qceval c1 σ m ∧ qceval c2 m σ' := by
  induction c1 generalizing σ with
  | nil =>
      constructor
      · intro h; exact ⟨σ, qceval.nil σ, by simpa using h⟩
      · rintro ⟨m, h1, h2⟩
        have hm : m = σ := qceval_nil h1
        subst hm; simpa using h2
  | cons a c1' ih =>
      constructor
      · intro h
        obtain ⟨σm, hstep, hrest⟩ := qceval_cons_inv (by simpa using h)
        obtain ⟨m, hc1, hc2⟩ := (ih σm).mp hrest
        exact ⟨m, qceval.cons a c1' σ σm m hstep hc1, hc2⟩
      · rintro ⟨m, hc1, hc2⟩
        obtain ⟨σm, hstep, hrest⟩ := qceval_cons_inv hc1
        have htail : qceval (c1' ++ c2) σm σ' := (ih σm).mpr ⟨m, hrest, hc2⟩
        simpa using qceval.cons a (c1' ++ c2) σ σm σ' hstep htail

/-! ## Soundness -/

/-- **Soundness of the canonical QClifford fault Hoare logic.** Every
    derivable triple holds for every `qceval` execution. The `F_ErrLoc`
    case correctly handles the `λ`-bump: from the injection-conjunct
    hypothesis `Q ⟨σ.es.inject q p, σ.lambda + 1⟩`, the postcondition `Q`
    holds at the post-injection QCState whose `λ` is already bumped. -/
theorem fhoare_sound {nq : Nat} {P : AssertionF nq} {fc : FCircuit nq}
    {Q : AssertionF nq} (d : FDeriv P fc Q) : FHoare P fc Q := by
  induction d with
  | F_Nil P =>
      intro σ σ' hev hP
      cases hev with | nil => exact hP
  | F_Gate g Q =>
      intro σ σ' hev hP
      obtain ⟨σm, hstep, hrest⟩ := qceval_cons_inv hev
      have hσm : σm = ⟨propagateGate g σ.es, σ.lambda⟩ := by
        cases hstep with | step_gate => rfl
      have hσ' : σ' = σm := qceval_nil hrest
      subst hσ'; subst hσm; exact hP
  | F_ErrLoc q Q =>
      intro σ σ' hev hP
      obtain ⟨σm, hstep, hrest⟩ := qceval_cons_inv hev
      have hσ' : σ' = σm := qceval_nil hrest
      subst hσ'
      cases hstep with
      | step_idle => exact hP.1
      | step_inject q2 _σ p hp => exact hP.2 p hp
  | F_App d1 d2 ih1 ih2 =>
      intro σ σ' hev hP
      obtain ⟨m, hev1, hev2⟩ := (qceval_append _ _ _ _).mp hev
      exact ih2 _ _ hev2 (ih1 _ _ hev1 hP)
  | F_And d1 d2 ih1 ih2 =>
      intro σ σ' hev hP
      exact ⟨ih1 _ _ hev hP.1, ih2 _ _ hev hP.2⟩
  | F_Conseq d hP' hQ' ih =>
      intro σ σ' hev hP
      exact hQ' _ (ih _ _ hev (hP' _ hP))

/-! ## Direct Hoare-form fault tolerance

The QClifford fault-tolerance condition is expressible as a single
Hoare triple over `QCState`:

  `{ σ = QCState.clean nq } fc { σ.lambda ≤ t → ¬ failure σ.es }`

Logically equivalent to `ToleratesFaultsΛ fc failure t`.
-/

/-- A Hoare derivation establishing FT directly on QCState. -/
theorem toleratesFaultsΛ_of_hoare {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq → Prop) (t : Nat)
    (h : FHoare
            (fun σ => σ = QCState.clean nq)
            fc
            (fun σ => σ.lambda ≤ t → ¬ failure σ.es)) :
    ToleratesFaultsΛ fc failure t := by
  intro σ' hev hbound
  exact h (QCState.clean nq) σ' hev rfl hbound

/-- And conversely: FT-Λ gives the Hoare triple. -/
theorem hoare_of_toleratesFaultsΛ {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq → Prop) (t : Nat)
    (h : ToleratesFaultsΛ fc failure t) :
    FHoare
      (fun σ => σ = QCState.clean nq)
      fc
      (fun σ => σ.lambda ≤ t → ¬ failure σ.es) := by
  intro σ σ' hev hP hbound
  subst hP
  exact h σ' hev hbound

end QStab.QClifford
