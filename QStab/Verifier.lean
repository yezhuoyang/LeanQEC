import QStab.Invariant
import QStab.MultiStep
import QStab.PauliOps
import QStab.Paper.GenericReachableBridge

/-!
# Fault-tolerance verifier (QStab level)

A **generic, scheme-agnostic** verifier for fault-tolerance certificates
at the QStab level. The verifier accepts any `(P, failure, inv, static,
bridge)` tuple — not just hardcoded codes — and the soundness theorem
`verifyQStab_sound` is proved once and applies uniformly.

## Bundle shape

```
QStabFTCertificate = ⟨P, failure, inv, static, bridge⟩
```
where:
  * `P : QECParams` — the QStab program (compiled from a CodeSpec by the
    verified compiler, which is a separate concern).
  * `failure : ErrorVec P.n → Prop` — what counts as a logical failure
    on the accumulated error vector `Ẽ`. Typical instances:
    `failure E = (bb_isSuccess E = true)` for one-logical FT,
    `failure E = (bb_isSuccessJoint E = true)` for joint X+Z FT.
  * `inv : Invariant P` — a dynamic QStab-level invariant on states.
  * `static : Bool` — a decidable side-condition (the "compiled-in
    SAT/native_decide content"; typically a code-specific finite check).
  * `bridge : static = true → ∀ s, inv.holds s → ¬ failure s.E_tilde`
    — the user-supplied proof that the invariant + static side-condition
    together rule out failure on any state.

## Soundness

`verifyQStab b = b.static`. If `verifyQStab b = true`, then for every
`MultiStep`-reachable state `s` from the initial state of `b.P`, the
failure predicate fails on `s.E_tilde` — i.e., the code is fault-tolerant
against the failure mode encoded by `b.failure`.

## Trust boundary

The verifier itself is a 5-line Lean function plus a 4-line theorem; the
only axioms it can possibly introduce are those used by `b.inv`, `b.bridge`,
and the kernel's interpretation of `b.static`'s decidability (`native_decide`
when applicable). The compiler-correctness story is a **separate** concern
(see `QStab.Compiler`); this verifier assumes the user is verifying their
already-compiled `P : QECParams` directly.

## Workflow

1. Define your `P` (e.g., via the verified compiler on a CodeSpec).
2. Pick a `failure` predicate.
3. Define `inv : Invariant P` with `holds_init` and `preservation`.
4. Establish `static : Bool` (typically by `native_decide` on a finite
   property).
5. Prove `bridge`.
6. Assemble `b : QStabFTCertificate` and invoke `verifyQStab_sound b _`.

The same `verifyQStab_sound` theorem applies to every code — surface,
HGP, BB[[72, 12, 6]], and any future instance.
-/

namespace QStab.Verifier

open QStab

/-- A fault-tolerance certificate bundle at the QStab (scheme-agnostic) level. -/
structure QStabFTCertificate where
  /-- The QStab program parameters. -/
  P       : QECParams
  /-- The failure predicate on accumulated errors. Logical failure
      means `failure E_tilde` holds. -/
  failure : ErrorVec P.n → Prop
  /-- The dynamic state invariant. Must hold at init and be preserved
      by every step (see `Invariant`). -/
  inv     : Invariant P
  /-- A decidable static side-condition. Typically a finite check
      (e.g., "no chain of length ≤ d-1 is a successful attack")
      discharged by `native_decide`. -/
  static  : Bool
  /-- The bridge: the static side-condition plus the invariant ruling
      out failure. -/
  bridge  : static = true → ∀ s : State P, inv.holds s → ¬ failure s.E_tilde

/-- The verifier function. Returns the bundle's static side-condition. -/
def verifyQStab (b : QStabFTCertificate) : Bool := b.static

/-- **Generic soundness theorem.** If the verifier accepts the bundle,
    then every `MultiStep`-reachable state from the initial state of
    `b.P` has its accumulated error outside the failure predicate. -/
theorem verifyQStab_sound (b : QStabFTCertificate) (h : verifyQStab b = true) :
    ∀ s : State b.P,
      MultiStep b.P (.active (State.init b.P)) (.active s) →
      ¬ b.failure s.E_tilde := by
  intro s hreach
  exact b.bridge h s (b.inv.holds_of_reachable s hreach)

/-! ## Smoke test: the trivial bundle

A sanity check that the bundle structure and verifier are well-formed
even for the simplest possible case: a code with empty failure predicate
(no error vector counts as a failure). The verifier trivially accepts.
-/

private def trivialInv (P : QECParams) : Invariant P where
  holds := fun _ => True
  holds_init := trivial
  preservation := fun _ _ _ _ => trivial

/-- A trivial bundle: every state passes (failure ≡ False). Sanity check
    that the soundness theorem applies generically. -/
def trivialBundle (P : QECParams) : QStabFTCertificate where
  P       := P
  failure := fun _ => False
  inv     := trivialInv P
  static  := true
  bridge  := fun _ _ _ hf => hf

example (P : QECParams) : verifyQStab (trivialBundle P) = true := rfl

example (P : QECParams) (s : State P)
    (hreach : MultiStep P (.active (State.init P)) (.active s)) :
    ¬ (trivialBundle P).failure s.E_tilde :=
  verifyQStab_sound (trivialBundle P) rfl s hreach

/-! ## Generic bundle constructor: reachable-set + static finite check

A reusable constructor that packages any QECParams equipped with:
  * a hook-upper-bound list (`allHooks`);
  * a `hooksUpperBound` proof;
  * a `Bool`-valued failure predicate;
  * a static finite check `∀ E ∈ reachableE allHooks C_budget, isSuccess E = false`
into a `QStabFTCertificate`. The dynamic invariant is the generic `reachInv` from
`GenericReachableBridge`; the bridge composes mono-lifting of the depth with
the finite check.

This is the canonical packaging for all codes whose distance proof factors
through `nonSuccess_op_d_circ_ge_d` (BB72 SE X-side, surface code, HGP code,
etc.). Code-specific bundles become one-liners.
-/

open QStab.Paper.GenericReachableBridge in
/-- Package any (QECParams, allHooks, hooks-upper-bound, isSuccess, finite-check)
    tuple into a `QStabFTCertificate`. -/
def QStabFTCertificate.ofReachInv
    (P : QECParams)
    (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks)
    (isSuccess : ErrorVec P.n → Bool)
    (h_finite : ∀ E ∈ reachableE allHooks P.C_budget, isSuccess E = false) :
    QStabFTCertificate where
  P       := P
  failure := fun E => isSuccess E = true
  inv     := reachInv P allHooks h_bound
  static  := true
  bridge  := fun _ s hinv hfail => by
    obtain ⟨h_in, _h_C⟩ := hinv
    have h_le : P.C_budget - s.C ≤ P.C_budget := Nat.sub_le _ _
    have h_in_full : s.E_tilde ∈ reachableE allHooks P.C_budget :=
      reachableE_mono_le allHooks h_le _ h_in
    have h_no : isSuccess s.E_tilde = false := h_finite s.E_tilde h_in_full
    rw [h_no] at hfail
    exact Bool.false_ne_true hfail

open QStab.Paper.GenericReachableBridge in
theorem QStabFTCertificate.ofReachInv_verified
    (P : QECParams)
    (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks)
    (isSuccess : ErrorVec P.n → Bool)
    (h_finite : ∀ E ∈ reachableE allHooks P.C_budget, isSuccess E = false) :
    verifyQStab (QStabFTCertificate.ofReachInv P allHooks h_bound isSuccess h_finite) = true := rfl

end QStab.Verifier
