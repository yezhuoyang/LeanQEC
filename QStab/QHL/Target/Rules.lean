import QStab.QHL.Target.Hoare

/-! # Per-gate Hoare rules at the QClifford level (model-theoretic layer)

QClifford execution is deterministic, so each gate is essentially an
"assignment": its weakest-precondition rule is

  ⦃ fun es => Q (propagateGate g es) ⦄ [g] ⦃Q⦄

This is the analog of the standard `hoare_asgn`. From it, sequencing
(`hoare_seq_c`) and consequence (`hoare_consequence_c`) are derivable;
they discharge by the same induction pattern as in `QHL.Source.Rules`.

Reader guide:
- `hoare_nil_c` — empty circuit (matches `hoare_skip`).
- `hoare_gate_c` — generic gate WP rule (matches `hoare_asgn`).
- `hoare_cons_c` — extend a derivation by one gate at the front.
- `hoare_app_c` — sequence two circuits (analog of `hoare_seq`).
- `hoare_consequence_c` — combined consequence rule.

These are framework code, not user-facing. The user writes a `DerivC`
tree in `Deriv.lean` and lets `hoare_sound_c` extract the triple.
-/

namespace QHL.Target

open QStab.QClifford

/-! ## Nil (empty circuit) -/

/-- **Rule `hoare_nil_c`** : `⦃P⦄ [] ⦃P⦄`. -/
theorem hoare_nil_c {nq : Nat} (Pre : AssertionC nq) :
    ⦃Pre⦄ ([] : Circuit nq) ⦃Pre⦄c := by
  intro es es' hev hPre
  cases hev
  exact hPre

/-! ## Generic gate (WP form) -/

/-- The WP substitution for a single gate `g`: `Q ↦ Q ∘ propagateGate g`.
    Mirrors the QStab `t0_sub`/`t1_sub`/... family but in the simpler
    deterministic gate-level setting. -/
def gate_sub {nq : Nat} (g : Gate nq) (Q : AssertionC nq) : AssertionC nq :=
  fun es => Q (propagateGate g es)

/-- **Rule `hoare_gate_c`** (WP form, the QClifford analog of `hoare_asgn`):
        `⦃ Q[g-update] ⦄ [g] ⦃Q⦄`.
    For a single-gate circuit, the precondition is the postcondition
    pulled back along `propagateGate g`. -/
theorem hoare_gate_c {nq : Nat} (g : Gate nq) (Q : AssertionC nq) :
    ⦃gate_sub g Q⦄ ([g] : Circuit nq) ⦃Q⦄c := by
  intro es es' hev hPre
  cases hev with
  | E_cons _ _ _ _ hrest =>
    cases hrest
    exact hPre

/-! ## Cons (extend a derivation by one front gate) -/

/-- **Rule `hoare_cons_c`** :
        if  ⦃P'⦄ gs ⦃Q⦄  and  P es → P' (propagateGate g es)  for every es,
        then  ⦃P⦄ g :: gs ⦃Q⦄.
    The first hypothesis is a Hoare triple on the tail; the second is
    the WP-substitution check for the head gate. -/
theorem hoare_cons_c {nq : Nat} {Pre Mid Post : AssertionC nq}
    (g : Gate nq) (gs : Circuit nq)
    (h_pre : ∀ es : ErrorState nq, Pre es → Mid (propagateGate g es))
    (h_tail : ⦃Mid⦄ gs ⦃Post⦄c) :
    ⦃Pre⦄ (g :: gs) ⦃Post⦄c := by
  intro es es' hev hPre
  cases hev with
  | E_cons _ _ _ _ hrest =>
    exact h_tail _ _ hrest (h_pre es hPre)

/-! ## Append (sequence two sub-circuits) -/

/-- `propagateCircuit` splits over circuit concatenation. -/
theorem propagateCircuit_append {nq : Nat} (c1 c2 : Circuit nq)
    (es : ErrorState nq) :
    propagateCircuit (c1 ++ c2) es =
      propagateCircuit c2 (propagateCircuit c1 es) := by
  induction c1 generalizing es with
  | nil => simp [propagateCircuit]
  | cons g gs ih => simp [propagateCircuit, ih]

/-- Composition of `cevalC` over circuit concatenation.

    A run of `c1 ++ c2` from `es` factors uniquely through an
    intermediate state. Reduced to `propagateCircuit_append` via the
    functional/relational equivalence. -/
theorem cevalC_append {nq : Nat} (c1 c2 : Circuit nq)
    (es es' : ErrorState nq) :
    cevalC (c1 ++ c2) es es' ↔
    ∃ es_mid, cevalC c1 es es_mid ∧ cevalC c2 es_mid es' := by
  rw [cevalC_iff_propagateCircuit]
  constructor
  · intro h
    refine ⟨propagateCircuit c1 es, ?_, ?_⟩
    · exact cevalC_of_propagateCircuit c1 es
    · rw [cevalC_iff_propagateCircuit]
      rw [propagateCircuit_append] at h
      exact h
  · rintro ⟨es_mid, h1, h2⟩
    rw [cevalC_iff_propagateCircuit] at h1 h2
    rw [propagateCircuit_append, h1, h2]

/-- **Rule `hoare_app_c`** (sequencing, analog of `hoare_seq`). -/
theorem hoare_app_c {nq : Nat} {Pre Mid Post : AssertionC nq}
    {c1 c2 : Circuit nq}
    (h1 : ⦃Pre⦄ c1 ⦃Mid⦄c) (h2 : ⦃Mid⦄ c2 ⦃Post⦄c) :
    ⦃Pre⦄ (c1 ++ c2) ⦃Post⦄c := by
  intro es es' hev hPre
  obtain ⟨es_mid, hev1, hev2⟩ := (cevalC_append c1 c2 es es').mp hev
  exact h2 _ _ hev2 (h1 _ _ hev1 hPre)

/-! ## Consequence rules -/

/-- **Rule `hoare_consequence_pre_c`** (strengthen the precondition). -/
theorem hoare_consequence_pre_c {nq : Nat} {Pre Pre' Post : AssertionC nq}
    {c : Circuit nq}
    (h : ⦃Pre'⦄ c ⦃Post⦄c)
    (h_imp : ∀ es : ErrorState nq, Pre es → Pre' es) :
    ⦃Pre⦄ c ⦃Post⦄c := by
  intro es es' hev hPre
  exact h _ _ hev (h_imp es hPre)

/-- **Rule `hoare_consequence_post_c`** (weaken the postcondition). -/
theorem hoare_consequence_post_c {nq : Nat} {Pre Post Post' : AssertionC nq}
    {c : Circuit nq}
    (h : ⦃Pre⦄ c ⦃Post'⦄c)
    (h_imp : ∀ es : ErrorState nq, Post' es → Post es) :
    ⦃Pre⦄ c ⦃Post⦄c := by
  intro es es' hev hPre
  exact h_imp es' (h _ _ hev hPre)

/-- **Rule `hoare_consequence_c`** (combined). -/
theorem hoare_consequence_c {nq : Nat} {Pre Pre' Post Post' : AssertionC nq}
    {c : Circuit nq}
    (h : ⦃Pre'⦄ c ⦃Post'⦄c)
    (h_pre : ∀ es : ErrorState nq, Pre es → Pre' es)
    (h_post : ∀ es : ErrorState nq, Post' es → Post es) :
    ⦃Pre⦄ c ⦃Post⦄c :=
  hoare_consequence_post_c (hoare_consequence_pre_c h h_pre) h_post

end QHL.Target
