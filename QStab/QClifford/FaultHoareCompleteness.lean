import QStab.QClifford.FaultHoare
import QStab.QClifford.StatefulFault

/-! # Relative completeness of QClifford F-Hoare logic

This file is the QClifford analogue of QStab's
`QHL/Source/Completeness.lean`. It proves that the canonical F-Hoare
calculus over `QCState` (the λ-aware fault-Hoare logic of
`FaultHoare.lean`) is **relatively complete**:

  `FHoare P fc Q → FDeriv P fc Q`     for every `FCircuit nq`.

## Why no `Executable` restriction is needed (vs. QStab)

The QStab completeness proof has to restrict to an `Executable`
fragment because four atomic commands (`t0 _ Pauli.I`, `t2 e mf` with
`e ∉ backActionSet`, `t3` with `C = 0`, `meas` with no successor
coordinate) admit no `ceval` step: their semantics is uninhabited at
the offending states, so a vacuously-valid triple cannot be matched by
the WP-form rule. Concretely the syntactic logic is incomplete on the
stuck fragment.

QClifford has **no such gap**. The operational relation `qcstep` is
**total** on every `FInstr`:

  * `.gate g` always fires `step_gate` (gates are total Clifford maps).
  * `.errLoc q` always admits BOTH `step_idle` (no injection) AND
    `step_inject q p hp` for every non-identity Pauli `p`.

Consequently every `FInstr` admits at least one `qcstep` from every
QCState, so no `FCircuit` is vacuously stuck. The completeness
theorem `relative_completeness_FDeriv` holds for the entire syntactic
fragment, with no executability predicate.

## Structure (mirrors QStab Completeness.lean)

1. Semantic weakest-precondition `FCircuit.wp`.
2. Validity = alias of `FHoare`.
3. Basic properties: `wp_is_valid`, `valid_implies_wp`.
4. Sequencing: `wp_append`, `Valid_append_split`.
5. Per-constructor completeness: `complete_F_Nil`, `complete_F_Gate`,
   `complete_F_ErrLoc`, `complete_F_App`.
6. Headline theorem `relative_completeness_FDeriv` by induction over
   the `FCircuit` list shape.
7. Worked example: a concrete derivation re-derived via the headline.

The file contains **zero `sorry`**, **zero `native_decide`**, and
**no custom axioms** — `#print axioms relative_completeness_FDeriv`
prints `[propext, Classical.choice, Quot.sound]` (only).
-/

namespace QStab.QClifford

/-! ## Semantic weakest precondition and validity -/

/-- **Semantic weakest precondition** of `fc` with respect to a
postcondition `Q`. By definition, a QCState `σ` satisfies `fc.wp Q`
iff every QCState reachable by executing `fc` from `σ` satisfies `Q`.

This is the standard textbook definition (cf. Winskel, Apt). For
`qceval`-stuck states `σ` (no successors) `fc.wp Q σ` is vacuously
true — but in QClifford no such stuck states exist, so the wp is
operationally meaningful at every QCState. -/
def FCircuit.wp {nq : Nat} (fc : FCircuit nq) (Q : AssertionF nq) :
    AssertionF nq :=
  fun σ => ∀ σ', qceval fc σ σ' → Q σ'

/-- **Validity** of a F-Hoare triple — alias of `FHoare`. -/
def Valid {nq : Nat} (P : AssertionF nq) (fc : FCircuit nq)
    (Q : AssertionF nq) : Prop :=
  FHoare P fc Q

/-! ## Basic properties of `wp` and `Valid` -/

/-- The weakest precondition is itself a valid precondition: the
triple `{wp fc Q} fc {Q}` holds semantically. -/
theorem wp_is_valid {nq : Nat} (fc : FCircuit nq) (Q : AssertionF nq) :
    FHoare (FCircuit.wp fc Q) fc Q := by
  intro σ σ' hev hwp
  exact hwp σ' hev

/-- A semantically valid triple's precondition is pointwise stronger
than the weakest precondition. -/
theorem valid_implies_wp {nq : Nat} {P Q : AssertionF nq}
    {fc : FCircuit nq} (h : FHoare P fc Q) :
    ∀ σ, P σ → FCircuit.wp fc Q σ := by
  intro σ hP σ' hev
  exact h σ σ' hev hP

/-! ## Splitting `wp` and `Valid` over append -/

/-- For `c1 ++ c2`, the semantic wp factors through `wp c2 Q`. -/
theorem wp_append {nq : Nat} (c1 c2 : FCircuit nq)
    (Q : AssertionF nq) (σ : QCState nq) :
    FCircuit.wp (c1 ++ c2) Q σ ↔
      FCircuit.wp c1 (FCircuit.wp c2 Q) σ := by
  constructor
  · intro h σm hev1 σ' hev2
    have hcat : qceval (c1 ++ c2) σ σ' :=
      (qceval_append c1 c2 σ σ').mpr ⟨σm, hev1, hev2⟩
    exact h σ' hcat
  · intro h σ' hev
    obtain ⟨σm, hev1, hev2⟩ := (qceval_append c1 c2 σ σ').mp hev
    exact h σm hev1 σ' hev2

/-- If `FHoare P (c1 ++ c2) Q`, both halves are individually valid
through the semantic midpoint `wp c2 Q`. -/
theorem Valid_append_split {nq : Nat} {P Q : AssertionF nq}
    {c1 c2 : FCircuit nq} (h : FHoare P (c1 ++ c2) Q) :
    FHoare P c1 (FCircuit.wp c2 Q) ∧
    FHoare (FCircuit.wp c2 Q) c2 Q := by
  refine ⟨?_, ?_⟩
  · intro σ σm hev1 hP σ' hev2
    have hcat : qceval (c1 ++ c2) σ σ' :=
      (qceval_append c1 c2 σ σ').mpr ⟨σm, hev1, hev2⟩
    exact h σ σ' hcat hP
  · intro σm σ' hev hwp
    exact hwp σ' hev

/-! ## Per-constructor completeness -/

/-- **Completeness for the empty program `[]`.**

`FHoare P [] Q` semantically forces `P σ → Q σ` for every `σ`
(because `qceval [] σ σ' ⇒ σ' = σ`). We derive the triple by
`F_Conseq` applied to `F_Nil Q`: the weakened-pre side discharges
`P σ → Q σ`. -/
noncomputable def complete_F_Nil {nq : Nat} {P Q : AssertionF nq}
    (h : FHoare P ([] : FCircuit nq) Q) :
    FDeriv P ([] : FCircuit nq) Q := by
  -- F_Nil Q : FDeriv Q [] Q. Weaken pre from P to Q via validity.
  refine FDeriv.F_Conseq (FDeriv.F_Nil Q) ?_ ?_
  · -- ∀ σ, P σ → Q σ : from validity instantiated at qceval.nil σ.
    intro σ hP
    exact h σ σ (qceval.nil σ) hP
  · -- ∀ σ, Q σ → Q σ.
    intro _ hQ
    exact hQ

/-- **Completeness for a single gate `[.gate g]`.**

`F_Gate` derives the WP-form triple
`{σ ↦ Q ⟨propagateGate g σ.es, σ.lambda⟩} [.gate g] {Q}`. We weaken
its precondition to `P` using the fact that, from a `P`-state, the
unique `qceval` execution of `[.gate g]` lands at exactly that
gate-propagated QCState. -/
noncomputable def complete_F_Gate {nq : Nat} {P Q : AssertionF nq}
    (g : Gate nq) (h : FHoare P [.gate g] Q) :
    FDeriv P [.gate g] Q := by
  refine FDeriv.F_Conseq (FDeriv.F_Gate g Q) ?_ ?_
  · -- ∀ σ, P σ → Q ⟨propagateGate g σ.es, σ.lambda⟩.
    intro σ hP
    -- Build the canonical qceval witness via step_gate + qceval.nil.
    have hstep : qcstep (FInstr.gate g) σ
        ⟨propagateGate g σ.es, σ.lambda⟩ :=
      qcstep.step_gate g σ
    have hrest : qceval ([] : FCircuit nq)
        (⟨propagateGate g σ.es, σ.lambda⟩ : QCState nq)
        ⟨propagateGate g σ.es, σ.lambda⟩ :=
      qceval.nil _
    have hev : qceval [.gate g] σ ⟨propagateGate g σ.es, σ.lambda⟩ :=
      qceval.cons (FInstr.gate g) [] σ
        ⟨propagateGate g σ.es, σ.lambda⟩
        ⟨propagateGate g σ.es, σ.lambda⟩ hstep hrest
    exact h σ _ hev hP
  · intro _ hQ
    exact hQ

/-- **Completeness for a single error location `[.errLoc q]`.**

`F_ErrLoc` derives the WP-form triple
`{σ ↦ Q σ ∧ ∀ p ≠ I, Q ⟨inject q p, λ+1⟩} [.errLoc q] {Q}`. We weaken
its precondition to `P` using validity at both possible step rules:

* `step_idle` reaches `σ` unchanged ⇒ `Q σ`;
* `step_inject q σ p hp` reaches `⟨σ.es.inject q p, σ.lambda+1⟩` ⇒ the
  injection conjunct with `λ`-bump.

Both step rules fire from every `σ` (no executability gap), so the
weakened-pre lemma is unconditional. -/
noncomputable def complete_F_ErrLoc {nq : Nat} {P Q : AssertionF nq}
    (q : Fin nq) (h : FHoare P [.errLoc q] Q) :
    FDeriv P [.errLoc q] Q := by
  refine FDeriv.F_Conseq (FDeriv.F_ErrLoc q Q) ?_ ?_
  · -- ∀ σ, P σ → (Q σ ∧ ∀ p ≠ I, Q ⟨σ.es.inject q p, σ.lambda + 1⟩).
    intro σ hP
    refine ⟨?_, ?_⟩
    · -- Idle branch: qceval [.errLoc q] σ σ via step_idle + nil.
      have hstep : qcstep (FInstr.errLoc q) σ σ := qcstep.step_idle q σ
      have hrest : qceval ([] : FCircuit nq) σ σ := qceval.nil σ
      have hev : qceval [.errLoc q] σ σ :=
        qceval.cons (FInstr.errLoc q) [] σ σ σ hstep hrest
      exact h σ σ hev hP
    · -- Inject branch: for each p ≠ I, step_inject + nil reaches
      -- ⟨σ.es.inject q p, σ.lambda + 1⟩.
      intro p hp
      let σ' : QCState nq := ⟨σ.es.inject q p, σ.lambda + 1⟩
      have hstep : qcstep (FInstr.errLoc q) σ σ' :=
        qcstep.step_inject q σ p hp
      have hrest : qceval ([] : FCircuit nq) σ' σ' := qceval.nil σ'
      have hev : qceval [.errLoc q] σ σ' :=
        qceval.cons (FInstr.errLoc q) [] σ σ' σ' hstep hrest
      exact h σ σ' hev hP
  · intro _ hQ
    exact hQ

/-- **Completeness for `c1 ++ c2`** given completeness of both halves.

Split the valid triple through `FCircuit.wp c2 Q` and apply `F_App`. -/
noncomputable def complete_F_App {nq : Nat} {P Q : AssertionF nq}
    {c1 c2 : FCircuit nq}
    (d1c : ∀ {P' Q' : AssertionF nq}, FHoare P' c1 Q' → FDeriv P' c1 Q')
    (d2c : ∀ {P' Q' : AssertionF nq}, FHoare P' c2 Q' → FDeriv P' c2 Q')
    (h : FHoare P (c1 ++ c2) Q) :
    FDeriv P (c1 ++ c2) Q := by
  obtain ⟨h1, h2⟩ := Valid_append_split h
  exact FDeriv.F_App (d1c h1) (d2c h2)

/-! ## Headline: relative completeness -/

/-- **Relative completeness of QClifford F-Hoare logic.**

For every `FCircuit fc` and every semantically valid F-Hoare triple
`FHoare P fc Q`, there is a syntactic derivation `FDeriv P fc Q`.

**No `Executable` restriction needed.** The QStab analogue requires
restricting to programs whose atomic commands have inhabited `ceval`
relations (the "executable fragment"). QClifford has no such gap:
`qcstep` is total on every `FInstr`, so the theorem applies to the
*entire* syntactic fragment.

Structure of the proof: induction on the list `fc`. The empty case
dispatches to `complete_F_Nil`. The cons case `i :: tail` rewrites
to `[i] ++ tail` and dispatches via `complete_F_App`, with one
inner case per `FInstr` constructor (`complete_F_Gate`,
`complete_F_ErrLoc`) for the head. The tail-IH is supplied via the
recursive call. -/
noncomputable def relative_completeness_FDeriv {nq : Nat} :
    ∀ (fc : FCircuit nq) {P Q : AssertionF nq},
      FHoare P fc Q → FDeriv P fc Q
  | [], _P, _Q, h => complete_F_Nil h
  | (FInstr.gate g) :: tail, _P, _Q, h =>
      -- View `g :: tail` as `[g] ++ tail` (definitional equality) and
      -- split through the wp midpoint.
      complete_F_App
        (c1 := [FInstr.gate g]) (c2 := tail)
        (d1c := fun {_P' _Q'} h' => complete_F_Gate g h')
        (d2c := fun {_P' _Q'} h' =>
          relative_completeness_FDeriv tail h')
        h
  | (FInstr.errLoc q) :: tail, _P, _Q, h =>
      complete_F_App
        (c1 := [FInstr.errLoc q]) (c2 := tail)
        (d1c := fun {_P' _Q'} h' => complete_F_ErrLoc q h')
        (d2c := fun {_P' _Q'} h' =>
          relative_completeness_FDeriv tail h')
        h

/-! ## Worked completeness derivation

A re-derivation of the canonical
"`[.errLoc q]` from clean state ⇒ λ ≤ 1" triple via the headline. The
explicit `deriv_full` in `FaultHoareExamples.lean` builds this by
hand; here we obtain it as a corollary of `relative_completeness_FDeriv`
plus a tiny semantic argument that the triple is indeed valid. -/

/-- The triple `{σ = clean} [.errLoc q] {σ.lambda ≤ 1}` is semantically
valid: every `qceval` execution from the clean state ends with at most
one fault injected. -/
theorem clean_to_lambda_le_one_valid {nq : Nat} (q : Fin nq) :
    FHoare
      (fun σ => σ = QCState.clean nq)
      [FInstr.errLoc q]
      (fun σ => σ.lambda ≤ 1) := by
  intro σ σ' hev hP
  subst hP
  -- One-step inversion of qceval on [.errLoc q].
  obtain ⟨σm, hstep, hrest⟩ := qceval_cons_inv hev
  have hσ' : σ' = σm := qceval_nil hrest
  subst hσ'
  cases hstep with
  | step_idle q' =>
      -- λ unchanged at 0.
      show ((QCState.clean nq).lambda) ≤ 1
      simp [QCState.clean]
  | step_inject q' _σ p _hp =>
      -- λ becomes 0 + 1 = 1.
      show ((QCState.clean nq).lambda + 1) ≤ 1
      simp [QCState.clean]

/-- **Worked example via completeness**: derive the canonical
"clean → λ ≤ 1" F-Hoare triple by feeding the semantic validity proof
through `relative_completeness_FDeriv`. This is the analogue of the
hand-built `deriv_full` in `FaultHoareExamples.lean`. -/
noncomputable def complete_example_clean_to_lambda_le_one {nq : Nat}
    (q : Fin nq) :
    FDeriv
      (fun σ => σ = QCState.clean nq)
      [FInstr.errLoc q]
      (fun σ => σ.lambda ≤ 1) :=
  relative_completeness_FDeriv [FInstr.errLoc q]
    (clean_to_lambda_le_one_valid q)

#print axioms relative_completeness_FDeriv

end QStab.QClifford
