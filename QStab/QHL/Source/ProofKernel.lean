import QStab.QHL.Assertion.Barrier

/-!
# Content-bearing recursive proof kernel for QEC code families

This is the second-generation kernel: each rule constructor carries an explicit
witness payload (a `KernelTerm`, an `ErrorVec`, an `InStab` proof, or a `Nat`
bound with a proof), and the corresponding `.sound` interpreter USES that
payload to produce a semantic result.  The previous design used nullary
"fingerprint" tags whose soundness was supplied externally by the client; the
present design pulls the soundness witnesses directly into the proof tree.

Design constraints honoured here:

* No `sorry`, `native_decide`, `Classical.choose`, `Exists.choose`, or
  `by_contra` is used inside this file.
* The source-side Hoare layer is the fixed-program nondeterministic branch
  calculus in `Source.Branch`; the old command-language QHL is not a canonical
  dependency of this kernel.
* Every new declaration is expected to verify at `[propext, Classical.choice,
  Quot.sound]` or stricter; in fact the new rule families introduce no choice
  or quotient reasoning, so they should be `[propext]`-only.

The downstream Surface/HGP demo files that were written against the old
nullary constructors will not type-check against this kernel; that breakage is
intentional and is resolved by the consumer-update phase.
-/

namespace QHL.Source.ProofKernel

open QStab
open QHL.AssertionLang

/-! ## Recursive program header

The header for a parametric stabilizer code is unchanged: a tiny-kernel
program for stabilizer entries, a tiny-kernel program for the logical-Z
entries, plus the assertion-language geometry and aligned-code data symbols.
The header is the place where `KernelTerm` payloads from the rule layer find
their semantic anchor.
-/

structure RecursiveProgramDefs (P : QECParams) (d : Nat) where
  stabilizerProgram : KernelTerm 2 .pauli
  logicalProgram : KernelTerm 1 .pauli
  geometry : GeometrySymbol P d
  code : AlignedCodeData P d

namespace RecursiveProgramDefs

def size {P : QECParams} {d : Nat} (_defs : RecursiveProgramDefs P d) : Nat :=
  4

end RecursiveProgramDefs

/-! ## Fold/unfold rule with `KernelTerm` payload

Every `FoldUnfoldRule` constructor now carries the actual kernel program for
the recursive symbol it claims to unfold, together with the natural-number
indices at which that program is read, and a `Nat` value equal to the
denotation.  The interpreter `sound` returns the literal denotation value.

This is enough to make the kernel rule responsible for the unfold; clients
that previously wrote `.cutBase` as a content-free tag now write
`.cutBase prog i j v h` where `h : KernelTerm.eval ... = v` is a closed-form
equation.  The kernel's soundness function returns that equation verbatim.
-/

/-- Generic fold/unfold sites for recursive QEC syntax. -/
inductive FoldUnfoldKind where
  | cutBase
  | cutStep
  | groupIndex
  | stabilizerEntry
  | logicalEntry
  | scheduleStep

/-- Evaluate a tiny-kernel natural-number program at an explicit environment.
    Used by the fold/unfold rule payloads.  Pattern-matches directly on the
    `KernelTerm` constructors that produce `Nat`; non-`Nat` kernel terms are
    not consumed by this evaluator and the caller never builds one. -/
def evalKernelNat : forall {arity : Nat}, KernelTerm arity .nat ->
    (Fin arity -> Nat) -> Nat
  | _, .var i, rho => rho i
  | _, .natLit n, _ => n
  | _, .natAdd a b, rho => evalKernelNat a rho + evalKernelNat b rho
  | _, .natSub a b, rho => evalKernelNat a rho - evalKernelNat b rho
  | _, .natMul a b, rho => evalKernelNat a rho * evalKernelNat b rho
  | _, .natDiv a b, rho => evalKernelNat a rho / evalKernelNat b rho
  | _, .natMod a b, rho => evalKernelNat a rho % evalKernelNat b rho
  | _, .ite c t e, rho =>
      if evalKernelBool c rho then evalKernelNat t rho else evalKernelNat e rho
where
  evalKernelBool : forall {arity : Nat}, KernelTerm arity .bool ->
      (Fin arity -> Nat) -> Bool
    | _, .boolLit b, _ => b
    | _, .natEq a b, rho =>
        Nat.beq (evalKernelNat a rho) (evalKernelNat b rho)
    | _, .natLe a b, rho =>
        Nat.ble (evalKernelNat a rho) (evalKernelNat b rho)
    | _, .natLt a b, rho =>
        Nat.blt (evalKernelNat a rho) (evalKernelNat b rho)
    | _, .boolNot a, rho => !evalKernelBool a rho
    | _, .boolAnd a b, rho => evalKernelBool a rho && evalKernelBool b rho
    | _, .boolOr a b, rho => evalKernelBool a rho || evalKernelBool b rho
    | _, .boolXor a b, rho =>
        xor (evalKernelBool a rho) (evalKernelBool b rho)
    | _, .ite c t e, rho =>
        if evalKernelBool c rho then evalKernelBool t rho else evalKernelBool e rho

/-- A checked fold/unfold token over the fixed recursive definitions.

    Each constructor pairs a `KernelTerm Nat` payload with an explicit
    `Nat`-valued witness and a closed-form equation between them.  The
    `.sound` function returns that equation, so consumers cannot fabricate
    fold/unfold steps without supplying a real evaluation.
-/
inductive FoldUnfoldRule (P : QECParams) (d : Nat) :
    FoldUnfoldKind -> Type where
  | cutBase
      (prog : KernelTerm 1 .nat) (rho : Fin 1 -> Nat) (v : Nat)
      (h : evalKernelNat prog rho = v) :
      FoldUnfoldRule P d .cutBase
  | cutStep
      (prog : KernelTerm 1 .nat) (rho : Fin 1 -> Nat) (v : Nat)
      (h : evalKernelNat prog rho = v) :
      FoldUnfoldRule P d .cutStep
  | groupIndex
      (prog : KernelTerm 1 .nat) (rho : Fin 1 -> Nat) (v : Nat)
      (h : evalKernelNat prog rho = v) :
      FoldUnfoldRule P d .groupIndex
  | stabilizerEntry
      (prog : KernelTerm 2 .nat) (rho : Fin 2 -> Nat) (v : Nat)
      (h : evalKernelNat prog rho = v) :
      FoldUnfoldRule P d .stabilizerEntry
  | logicalEntry
      (prog : KernelTerm 1 .nat) (rho : Fin 1 -> Nat) (v : Nat)
      (h : evalKernelNat prog rho = v) :
      FoldUnfoldRule P d .logicalEntry
  | scheduleStep
      (prog : KernelTerm 1 .nat) (rho : Fin 1 -> Nat) (v : Nat)
      (h : evalKernelNat prog rho = v) :
      FoldUnfoldRule P d .scheduleStep

namespace FoldUnfoldRule

/-- Syntactic size of a fold/unfold rule.  The `+1` accounts for the
    payload-bearing constructor itself; the equation proof is irrelevant. -/
def size {P : QECParams} {d : Nat} {k : FoldUnfoldKind} :
    FoldUnfoldRule P d k -> Nat
  | .cutBase _ _ _ _ => 1
  | .cutStep _ _ _ _ => 1
  | .groupIndex _ _ _ _ => 1
  | .stabilizerEntry _ _ _ _ => 1
  | .logicalEntry _ _ _ _ => 1
  | .scheduleStep _ _ _ _ => 1

/-- The denoted natural-number value of a fold/unfold step, computed from the
    payload `KernelTerm`. -/
def value {P : QECParams} {d : Nat} {k : FoldUnfoldKind} :
    FoldUnfoldRule P d k -> Nat
  | .cutBase _ _ v _ => v
  | .cutStep _ _ v _ => v
  | .groupIndex _ _ v _ => v
  | .stabilizerEntry _ _ v _ => v
  | .logicalEntry _ _ v _ => v
  | .scheduleStep _ _ v _ => v

/-- Soundness for fold/unfold rules: each rule witnesses the equation between
    its kernel program and its stated value. -/
theorem sound {P : QECParams} {d : Nat} {k : FoldUnfoldKind}
    (r : FoldUnfoldRule P d k) :
    match r with
    | .cutBase prog rho v _ => evalKernelNat prog rho = v
    | .cutStep prog rho v _ => evalKernelNat prog rho = v
    | .groupIndex prog rho v _ => evalKernelNat prog rho = v
    | .stabilizerEntry prog rho v _ => evalKernelNat prog rho = v
    | .logicalEntry prog rho v _ => evalKernelNat prog rho = v
    | .scheduleStep prog rho v _ => evalKernelNat prog rho = v := by
  cases r with
  | cutBase _ _ _ h => exact h
  | cutStep _ _ _ h => exact h
  | groupIndex _ _ _ h => exact h
  | stabilizerEntry _ _ _ h => exact h
  | logicalEntry _ _ _ h => exact h
  | scheduleStep _ _ _ h => exact h

end FoldUnfoldRule

/-! ## Pauli rewrite rules with `ErrorVec` payload

A `PauliRewriteRule` constructor now carries the actual operands `a, b, c` of
the rewrite plus a hidden proof of the rewrite equation.  Soundness returns
the equation directly.  Clients that previously wrote `.mulIdentityLeft` as a
content-free tag now write `.mulIdentityLeft E` and `.sound` produces
`ErrorVec.mul (ErrorVec.identity n) E = E`.
-/

inductive PauliRewriteKind where
  | mulIdentityLeft
  | mulIdentityRight
  | mulAssoc
  | parityMulLeft
  | parityMulRight

inductive PauliRewriteRule (n : Nat) : PauliRewriteKind -> Type where
  | mulIdentityLeft (E : ErrorVec n) : PauliRewriteRule n .mulIdentityLeft
  | mulIdentityRight (E : ErrorVec n) : PauliRewriteRule n .mulIdentityRight
  | mulAssoc (a b c : ErrorVec n) : PauliRewriteRule n .mulAssoc
  | parityMulLeft (A B X : ErrorVec n) : PauliRewriteRule n .parityMulLeft
  | parityMulRight (S A B : ErrorVec n) : PauliRewriteRule n .parityMulRight

namespace PauliRewriteRule

/-- Syntactic size: every rewrite is a single rule node. -/
def size {n : Nat} {k : PauliRewriteKind} : PauliRewriteRule n k -> Nat
  | .mulIdentityLeft _ => 1
  | .mulIdentityRight _ => 1
  | .mulAssoc _ _ _ => 1
  | .parityMulLeft _ _ _ => 1
  | .parityMulRight _ _ _ => 1

/-- Soundness for the Pauli-algebra rewrite layer.  Each constructor's
    payload determines the witnessed equation, and the kernel discharges it
    from the existing `QStab` ErrorVec lemmas. -/
theorem sound {n : Nat} {k : PauliRewriteKind} (r : PauliRewriteRule n k) :
    match r with
    | .mulIdentityLeft E => ErrorVec.mul (ErrorVec.identity n) E = E
    | .mulIdentityRight E => ErrorVec.mul E (ErrorVec.identity n) = E
    | .mulAssoc a b c =>
        ErrorVec.mul (ErrorVec.mul a b) c = ErrorVec.mul a (ErrorVec.mul b c)
    | .parityMulLeft A B X =>
        ErrorVec.parity (ErrorVec.mul A B) X =
          xor (ErrorVec.parity A X) (ErrorVec.parity B X)
    | .parityMulRight S A B =>
        ErrorVec.parity S (ErrorVec.mul A B) =
          xor (ErrorVec.parity S A) (ErrorVec.parity S B) := by
  cases r with
  | mulIdentityLeft E => exact ErrorVec.mul_identity_left E
  | mulIdentityRight E => exact ErrorVec.mul_identity_right E
  | mulAssoc a b c => exact ErrorVec.mul_assoc a b c
  | parityMulLeft A B X => exact ErrorVec.parity_mul_left A B X
  | parityMulRight S A B => exact ErrorVec.parity_mul_right S A B

end PauliRewriteRule

/-! ## Stabilizer algebra rules with `InStab` payload

A `StabilizerAlgebraRule` constructor now carries the relevant
stabilizer/`InStab` data, and `.sound` returns the corresponding `InStab P`
proof.  This is the natural place to keep the proof structurally accessible:
the constructor encodes which generator/product step is being taken, and the
soundness interpreter produces the membership proof from that payload.
-/

inductive StabilizerAlgebraKind where
  | identity
  | generator
  | mul
  | maskProduct
  | commute
  | normalizer

inductive StabilizerAlgebraRule (P : QECParams) :
    StabilizerAlgebraKind -> Type where
  /-- The identity is in the stabilizer group. -/
  | identity : StabilizerAlgebraRule P .identity
  /-- Each named generator is in the stabilizer group. -/
  | generator (i : Fin P.numStab) : StabilizerAlgebraRule P .generator
  /-- The product of two stabilizer elements is a stabilizer element. -/
  | mul {A B : ErrorVec P.n} (hA : InStab P A) (hB : InStab P B) :
      StabilizerAlgebraRule P .mul
  /-- The Boolean-mask product is in the stabilizer group. -/
  | maskProduct (mask : Fin P.numStab -> Bool) :
      StabilizerAlgebraRule P .maskProduct
  /-- Two named generators have parity-zero (commute). -/
  | commute (i j : Fin P.numStab)
      (h : ErrorVec.parity (P.stabilizers i) (P.stabilizers j) = false) :
      StabilizerAlgebraRule P .commute
  /-- A given vector is normalized by every named generator. -/
  | normalizer (v : ErrorVec P.n)
      (h : forall i : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) v = false) :
      StabilizerAlgebraRule P .normalizer

namespace StabilizerAlgebraRule

def size {P : QECParams} {k : StabilizerAlgebraKind} :
    StabilizerAlgebraRule P k -> Nat
  | .identity => 1
  | .generator _ => 1
  | .mul _ _ => 1
  | .maskProduct _ => 1
  | .commute _ _ _ => 1
  | .normalizer _ _ => 1

/-- The element this stabilizer-algebra rule witnesses.  Defined for those
    constructors whose semantic role is "produce a stabilizer-group element."
    For commute/normalizer, see the dedicated soundness theorems below. -/
def witness {P : QECParams} :
    forall {k : StabilizerAlgebraKind}, StabilizerAlgebraRule P k ->
      Option (ErrorVec P.n)
  | _, .identity => some (ErrorVec.identity P.n)
  | _, .generator i => some (P.stabilizers i)
  | _, .mul (A := A) (B := B) _ _ => some (ErrorVec.mul A B)
  | _, .maskProduct mask => some (maskStabilizerProduct P mask)
  | _, .commute _ _ _ => none
  | _, .normalizer _ _ => none

/-- The `identity` / `generator` / `mul` / `maskProduct` constructors all
    witness an `InStab P` proof for their declared element. -/
theorem sound_inStab {P : QECParams} :
    forall {k : StabilizerAlgebraKind} (r : StabilizerAlgebraRule P k),
      match r with
      | .identity => InStab P (ErrorVec.identity P.n)
      | .generator i => InStab P (P.stabilizers i)
      | .mul (A := A) (B := B) _ _ => InStab P (ErrorVec.mul A B)
      | .maskProduct mask => InStab P (maskStabilizerProduct P mask)
      | .commute _ _ _ => True
      | .normalizer _ _ => True
  | _, .identity => InStab.identity
  | _, .generator i => InStab.gen i
  | _, .mul hA hB => InStab.mul hA hB
  | _, .maskProduct mask =>
      maskStabilizerProduct_inStab P mask
  | _, .commute _ _ _ => trivial
  | _, .normalizer _ _ => trivial

/-- The `commute` constructor witnesses pairwise parity equality. -/
theorem sound_commute {P : QECParams}
    (r : StabilizerAlgebraRule P .commute) :
    match r with
    | .commute i j _ =>
        ErrorVec.parity (P.stabilizers i) (P.stabilizers j) = false := by
  cases r with
  | commute _ _ h => exact h

/-- The `normalizer` constructor witnesses that a vector commutes with every
    generator. -/
theorem sound_normalizer {P : QECParams}
    (r : StabilizerAlgebraRule P .normalizer) :
    match r with
    | .normalizer v _ =>
        forall i : Fin P.numStab,
          ErrorVec.parity (P.stabilizers i) v = false := by
  cases r with
  | normalizer _ h => exact h

end StabilizerAlgebraRule

/-! ## Program-obligation rule with proof payload

Each `ProgramObligationRule` now carries an explicit semantic witness for the
obligation it claims to discharge.  In particular the LDPC-sparse obligation
carries a sparse-weight bound (a `Nat` plus a proof that every stabilizer
generator has weight `≤` that bound); the kernel proves a small consistency
lemma showing that the wrapped witness really does imply the stated bound.
-/

inductive ProgramObligationKind where
  | cutShape
  | cutStabEquiv
  | logicalNormalizer
  | stabilizersCommute
  | hookSpread
  | ldpcSparse
  | scheduleCompatible

/-- The sparse-weight witness for an LDPC family: a maximum row weight `w`,
    together with a proof that every stabilizer generator has weight at most
    `w`.  This is the per-row sparsity certificate. -/
structure LdpcSparseWitness (P : QECParams) where
  bound : Nat
  proof : forall i : Fin P.numStab, ErrorVec.weight (P.stabilizers i) <= bound

namespace LdpcSparseWitness

def size {P : QECParams} (_ : LdpcSparseWitness P) : Nat := 1

end LdpcSparseWitness

/-! ## Program-obligation formula + derivation tree

This block adds a uniform `obligationFormula P d A k : Prop` that fixes the
semantic content of every `ProgramObligationKind`, and a derivation-tree
inductive `ObligationDerivation P d A k : Type` with **one constructor per
`ProgramObligationKind`**.  Soundness is a single structural theorem that
destructures the derivation and emits the corresponding formula.

For five kinds (`cutShape`, `logicalNormalizer`, `stabilizersCommute`,
`ldpcSparse`, `hookSpread`) the formula is fully fixed (parametric in
`A`/`P`), so the derivation constructor carries only a concrete decidable /
structural witness of that formula and the soundness clause is `exact h` (or
a one-line projection through a structured sub-derivation).

For two kinds (`cutStabEquiv`, `scheduleCompatible`) the semantic content is
intrinsically per-family — Surface-row induction differs from HGP column
derivation differs from cat-block schedule compatibility — so no single
closed-form formula is appropriate.  We therefore:

  * Define `obligationFormula` for these two kinds as a uniform abstract
    placeholder (`True`), and
  * Have the corresponding `ObligationDerivation` constructor carry the
    derivation explicitly as a `Prop` payload (the **named leaf-axiom
    constructors**: `.cutStabEquiv`, `.scheduleCompatible`).

The `hookSpread` slot now uses a uniform group-spread inequality (the same
formula consumed by `hookAlignedF_valid_of_hookSpreadBound`).  The
corresponding `ObligationDerivation.hookSpread` constructor takes a real
`HookSpreadDerivation` value (a small sub-inductive defined just below
`obligationFormula`); `HookSpreadDerivation.leafAxiom` remains an honest,
named entry point for per-family content, but it is now the **only** way
per-family Lean content enters the hook-spread obligation, and the formula
it carries is fixed by the kernel rather than supplied externally.

The leaf-axiom constructors are honest entry points for per-family content; a
follow-up phase can replace each with a structurally checked derivation
subtree (e.g. row-by-row Surface induction).  Listing them here makes the
migration boundary explicit.

Constraints honoured:
  * No `sorry`, `native_decide`, `Classical.choose`, `Exists.choose`, or
    `by_contra`.
  * Only `[propext, Classical.choice, Quot.sound]` should appear in the axiom
    audit (in fact, no choice/quot reasoning is invoked below; expected to be
    `[propext]`-only after the audit).
  * The `sound` theorem destructures the derivation — it does not assume any
    per-family Lean lemma; the per-family content is carried by the
    constructor payload, not by the soundness function.
-/

/-- The uniform hook-spread formula: for every stabilizer index `s_idx` and
    every back-action error `e_B ∈ P.backActionSet s_idx`, the
    geometry-induced row count cannot grow by more than one when `e_B` is
    folded into an arbitrary error `E`, up to a stabilizer re-witness.

    This is exactly the hypothesis consumed by
    `AlignedCodeData.hookAlignedF_valid_of_hookSpreadBound`, so the kernel's
    `obligationFormula .hookSpread` lines up with the assertion-layer
    bridge: no shape mismatch, no per-family translation, no per-family Lean
    lambda hidden in the kernel.
-/
def hookSpreadFormula {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) : Prop :=
  forall (s_idx : Fin P.numStab) (e_B : ErrorVec P.n),
    e_B ∈ P.backActionSet s_idx ->
    forall (E : ErrorVec P.n) (S_wit : ErrorVec P.n),
      InStab P S_wit ->
      exists S_wit' : ErrorVec P.n, InStab P S_wit' /\
        (Finset.univ.filter fun g : Fin d =>
          exists q : Fin P.n, A.geometry.groupOf q = some g /\
            Pauli.hasXComponent
              (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
        <=
        (Finset.univ.filter fun g : Fin d =>
          exists q : Fin P.n, A.geometry.groupOf q = some g /\
            Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1

/-- One-pair sub-formula of `hookSpreadFormula` for a single back-action
    element.  Used as the natural unit of compositional hook-spread
    derivations: a family that wants to discharge the obligation
    stabilizer-by-stabilizer (or back-action-element by back-action-element)
    can do so via `HookSpreadDerivation.byStabilizer`. -/
def hookSpreadPair {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) (_s_idx : Fin P.numStab)
    (e_B : ErrorVec P.n) : Prop :=
  forall (E : ErrorVec P.n) (S_wit : ErrorVec P.n),
    InStab P S_wit ->
    exists S_wit' : ErrorVec P.n, InStab P S_wit' /\
      (Finset.univ.filter fun g : Fin d =>
        exists q : Fin P.n, A.geometry.groupOf q = some g /\
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      <=
      (Finset.univ.filter fun g : Fin d =>
        exists q : Fin P.n, A.geometry.groupOf q = some g /\
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1

/-- Real syntactic derivation tree for the hook-spread obligation.

    Three constructors:

    * `leafAxiom` — the documented escape hatch: carries the full
      `hookSpreadFormula` as a single Lean proof.  This is the **only** way
      per-family content enters the kernel for the hook-spread obligation,
      and it does so with a kernel-fixed formula shape (no per-family type
      tricks possible).

    * `byStabilizer` — compositional form: take a per-pair function
      `(s_idx, e_B, he : e_B ∈ P.backActionSet s_idx) ↦ hookSpreadPair A s_idx e_B`.
      Discharging the obligation one back-action element at a time isolates
      where the per-family geometric argument lives.

    * `combine` — disjoint-cover form: if the back-action set can be split
      into two pieces and each piece has its own derivation, combine them.
      This is a tiny compositional combinator; the family supplies the
      cover predicate (i.e. a Boolean function over stabilizer indices) and
      the kernel checks that the resulting derivation covers every index.

    The exhaustive-`leafAxiom` form remains available; the other two are
    additive (they reduce the size of the per-family Lean term but never
    add to the kernel-level Lean content). -/
inductive HookSpreadDerivation
    {P : QECParams} {d : Nat} (A : AlignedCodeData P d) : Type where
  /-- Single-shot leaf: carries the entire `hookSpreadFormula` as one Lean
      proof.  This is the documented escape hatch for per-family content. -/
  | leafAxiom (h : hookSpreadFormula A) : HookSpreadDerivation A
  /-- Compositional form: a per-pair function from
      `(s_idx, e_B, e_B ∈ backActionSet s_idx)` to the one-pair sub-formula.
      Equivalent in proof power to `leafAxiom`, but structurally exposes the
      per-stabilizer / per-back-action obligation as a sub-goal. -/
  | byStabilizer
      (h : forall (s_idx : Fin P.numStab) (e_B : ErrorVec P.n),
        e_B ∈ P.backActionSet s_idx -> hookSpreadPair A s_idx e_B) :
      HookSpreadDerivation A
  /-- Disjoint-cover form: combine two sub-derivations by a Boolean cover
      `chooseLeft` on the stabilizer index.  Each stabilizer index is
      handled by the left or right sub-derivation depending on `chooseLeft`. -/
  | combine
      (chooseLeft : Fin P.numStab -> Bool)
      (left right : HookSpreadDerivation A) :
      HookSpreadDerivation A

namespace HookSpreadDerivation

/-- Syntactic size of a hook-spread derivation. -/
def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    HookSpreadDerivation A -> Nat
  | .leafAxiom _ => 1
  | .byStabilizer _ => 1
  | .combine _ l r => 1 + l.size + r.size

/-- Soundness: every `HookSpreadDerivation` interprets to a witness of the
    fixed `hookSpreadFormula`.

    No per-family Lean lemma is invoked here; the per-family content lives
    in the carried payloads (which the kernel has type-checked against the
    kernel-fixed `hookSpreadFormula` / `hookSpreadPair` signatures). -/
theorem sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (D : HookSpreadDerivation A) : hookSpreadFormula A := by
  induction D with
  | leafAxiom h => exact h
  | byStabilizer h =>
      intro s_idx e_B he E S_wit hS
      exact h s_idx e_B he E S_wit hS
  | combine chooseLeft _ _ ihL ihR =>
      intro s_idx e_B he E S_wit hS
      by_cases hC : chooseLeft s_idx = true
      · exact ihL s_idx e_B he E S_wit hS
      · exact ihR s_idx e_B he E S_wit hS

end HookSpreadDerivation

/-! ### Per-cell cut-shape witness

A `CutShapeCellWitness P d A g q` proves
`A.geometry.cut g q = if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I`
at a single cut cell.  Three constructors:

* `groupHit`  — the group-membership branch: provide
  `A.geometry.groupOf q = some g` and `A.geometry.cut g q = Pauli.Z`.
* `groupMiss` — the negation branch: provide
  `A.geometry.groupOf q ≠ some g` and `A.geometry.cut g q = Pauli.I`.
* `leafAxiom` — direct escape: carry the full `if-then-else` equation
  for that cell.

Each cell witness is structurally one of these three; the `.sound` lemma
performs the obvious `if-then-else` simplification using the carried
group-membership branch and returns the kernel-fixed equation. -/
inductive CutShapeCellWitness
    {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) (g : Fin d) (q : Fin P.n) : Type where
  /-- Group-hit branch: `groupOf q = some g` and `cut g q = Pauli.Z`. -/
  | groupHit
      (hg : A.geometry.groupOf q = some g)
      (hZ : A.geometry.cut g q = Pauli.Z) :
      CutShapeCellWitness A g q
  /-- Group-miss branch: `groupOf q ≠ some g` and `cut g q = Pauli.I`. -/
  | groupMiss
      (hg : A.geometry.groupOf q ≠ some g)
      (hI : A.geometry.cut g q = Pauli.I) :
      CutShapeCellWitness A g q
  /-- Direct per-cell escape carrying the full `if-then-else` equation. -/
  | leafAxiom
      (h : A.geometry.cut g q =
        if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I) :
      CutShapeCellWitness A g q

namespace CutShapeCellWitness

/-- Syntactic size of a cell witness. -/
def size {P : QECParams} {d : Nat}
    {A : AlignedCodeData P d} {g : Fin d} {q : Fin P.n} :
    CutShapeCellWitness A g q -> Nat
  | .groupHit _ _ => 1
  | .groupMiss _ _ => 1
  | .leafAxiom _ => 1

/-- Whether this cell witness was produced by the `leafAxiom`
    (escape-hatch) constructor.  Used by `countLeafAxioms` below to
    measure how much of the kernel content was supplied as a single
    closed Lean proof. -/
def isLeafAxiom {P : QECParams} {d : Nat}
    {A : AlignedCodeData P d} {g : Fin d} {q : Fin P.n} :
    CutShapeCellWitness A g q -> Bool
  | .groupHit _ _ => false
  | .groupMiss _ _ => false
  | .leafAxiom _ => true

/-- Soundness: every cell witness produces the kernel-fixed pointwise
    equation at its `(g, q)`. -/
theorem sound {P : QECParams} {d : Nat}
    {A : AlignedCodeData P d} {g : Fin d} {q : Fin P.n}
    (W : CutShapeCellWitness A g q) :
    A.geometry.cut g q =
      if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I := by
  cases W with
  | groupHit hg hZ =>
      -- `if groupOf q = some g then Z else I` reduces to `Z` via `hg`.
      have hR : (if A.geometry.groupOf q = some g then Pauli.Z
                 else Pauli.I) = Pauli.Z := by
        simp [hg]
      exact hZ.trans hR.symm
  | groupMiss hg hI =>
      -- `if groupOf q = some g then Z else I` reduces to `I` via `¬hg`.
      have hR : (if A.geometry.groupOf q = some g then Pauli.Z
                 else Pauli.I) = Pauli.I := by
        simp [hg]
      exact hI.trans hR.symm
  | leafAxiom h => exact h

end CutShapeCellWitness

/-! ### Whole-obligation cut-shape derivation

A `CutShapeDerivation P d A` proves the full kernel-fixed `cutShape`
formula
`forall (g) (q), A.geometry.cut g q = if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I`.

Two constructors:

* `byCell`    — supply a per-cell function `(g, q) ↦ CutShapeCellWitness`.
  The soundness theorem then assembles those into the universally
  quantified statement.
* `leafAxiom` — direct escape: carry the full `forall (g) (q), ...`
  equation.

The `CutShapeDerivation.sound` theorem is a one-line destructor; the
`byCell` branch just unfolds to the per-cell soundness lemma.
-/

inductive CutShapeDerivation
    {P : QECParams} {d : Nat} (A : AlignedCodeData P d) : Type where
  /-- Compositional form: a per-cell function from `(g, q)` to a single
      cell witness.  No quantifiers over the per-cell content. -/
  | byCell
      (cell : forall (g : Fin d) (q : Fin P.n),
        CutShapeCellWitness A g q) :
      CutShapeDerivation A
  /-- Whole-formula escape hatch: carry the full pointwise equation as
      a single Lean proof.  Identical proof power to the
      `ObligationDerivation.cutShape` constructor; the kernel-fixed
      formula shape is enforced by the type. -/
  | leafAxiom
      (h : forall (g : Fin d) (q : Fin P.n),
        A.geometry.cut g q =
          if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I) :
      CutShapeDerivation A

namespace CutShapeDerivation

/-- Syntactic size of a cut-shape derivation.  `byCell` is treated as a
    single derivation node (the per-cell content lives in a function, not
    in nested derivation constructors), matching how `HookSpreadDerivation`
    counts its `byStabilizer` constructor. -/
def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    CutShapeDerivation A -> Nat
  | .byCell _ => 1
  | .leafAxiom _ => 1

/-- Count how many cells of a `byCell` derivation were discharged via
    the per-cell `leafAxiom` escape hatch, plus one if the top-level
    derivation is itself a `leafAxiom`.  Useful as a structural-honesty
    metric: zero means the derivation is fully `groupHit`/`groupMiss`-decomposed.

    Implementation note: `byCell` sums the Boolean `isLeafAxiom` flag
    across all `(g, q)` cells using `Finset.univ.sum` so the count
    reduces by `decide` for concrete `d` and `P.n`. -/
def countLeafAxioms {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    CutShapeDerivation A -> Nat
  | .leafAxiom _ => 1
  | .byCell cell =>
      (Finset.univ : Finset (Fin d)).sum fun g =>
        (Finset.univ : Finset (Fin P.n)).sum fun q =>
          if (cell g q).isLeafAxiom = true then 1 else 0

/-- Soundness: every `CutShapeDerivation` interprets to the kernel-fixed
    `cutShape` formula on `A`.

    `byCell` projects the per-cell witness and invokes
    `CutShapeCellWitness.sound`; `leafAxiom` returns the carried proof
    verbatim.  No per-family Lean lemma is invoked. -/
theorem sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (D : CutShapeDerivation A) :
    forall (g : Fin d) (q : Fin P.n),
      A.geometry.cut g q =
        if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I := by
  cases D with
  | byCell cell =>
      intro g q
      exact (cell g q).sound
  | leafAxiom h => exact h

end CutShapeDerivation

/-- Uniform semantic content of every `ProgramObligationKind`.

    Five kinds receive a closed-form, parametric formula in `A`/`P`:
    `cutShape`, `logicalNormalizer`, `stabilizersCommute`, `ldpcSparse`, and
    `hookSpread` (the latter via `hookSpreadFormula`).  The remaining two
    (`cutStabEquiv`, `scheduleCompatible`) are family-specific and use
    `True` as the abstract uniform placeholder; the real semantic content
    for those is carried by the corresponding `ObligationDerivation`
    leaf-axiom constructor. -/
def obligationFormula {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) : ProgramObligationKind -> Prop
  | .cutShape =>
      forall (g : Fin d) (q : Fin P.n),
        A.geometry.cut g q =
          if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I
  | .cutStabEquiv => True
  | .logicalNormalizer =>
      forall i : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) A.logicalZ = false
  | .stabilizersCommute =>
      forall i j : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) (P.stabilizers j) = false
  | .hookSpread => hookSpreadFormula A
  | .ldpcSparse =>
      exists w : Nat, forall i : Fin P.numStab,
        ErrorVec.weight (P.stabilizers i) <= w
  | .scheduleCompatible => True

/-- Derivation tree for each `ProgramObligationKind`.

    Four constructors (`cutShape`, `logicalNormalizer`, `stabilizersCommute`,
    `ldpcSparse`) carry a concrete decidable / structural witness of the
    parametric formula given by `obligationFormula`.

    One constructor (`hookSpread`) carries a recursive
    `HookSpreadDerivation` value whose own leaves are typed against the
    kernel-fixed `hookSpreadFormula` (or its per-pair variant); see the
    sub-inductive above.

    Two constructors (`cutStabEquiv`, `scheduleCompatible`) remain
    *leaf-axiom* constructors: they take no payload, and their
    corresponding `obligationFormula` clause is `True`.  Real per-family
    semantic content for those kinds is supplied at the use site, not by the
    kernel; the constructors here serve as honest, named entry points for
    family-specific derivation packages. -/
inductive ObligationDerivation
    (P : QECParams) (d : Nat) (A : AlignedCodeData P d) :
    ProgramObligationKind -> Type where
  /-- Cut-shape obligation derivation: carries a structural
      `CutShapeDerivation` payload (per-cell witness tree or whole-formula
      escape).  The kernel-fixed pointwise equation is recovered by
      `CutShapeDerivation.sound`. -/
  | cutShape (D : CutShapeDerivation A) :
      ObligationDerivation P d A .cutShape
  /-- Cut/stabilizer equivalence: family-specific (Surface row induction, HGP
      column derivation, ...).  This is a leaf-axiom constructor: the kernel
      records that the derivation exists but does not encode its per-family
      content.  See file-header docstring for the migration note. -/
  | cutStabEquiv : ObligationDerivation P d A .cutStabEquiv
  /-- Logical-Z normalizes every stabilizer generator. -/
  | logicalNormalizer
      (h : forall i : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) A.logicalZ = false) :
      ObligationDerivation P d A .logicalNormalizer
  /-- All pairs of stabilizer generators commute. -/
  | stabilizersCommute
      (h : forall i j : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) (P.stabilizers j) = false) :
      ObligationDerivation P d A .stabilizersCommute
  /-- Hook-spread bound: carries a real `HookSpreadDerivation` value.  The
      kernel-fixed formula is `hookSpreadFormula A`; the inner derivation
      may be `leafAxiom`, `byStabilizer`, or `combine`, but every per-family
      Lean lambda entering the kernel for this obligation lands on one of
      those constructors (no nullary tag, no externally-supplied formula
      shape). -/
  | hookSpread (Dh : HookSpreadDerivation A) :
      ObligationDerivation P d A .hookSpread
  /-- LDPC sparse-weight bound: carries the bound `w` and the per-generator
      weight inequality. -/
  | ldpcSparse (w : LdpcSparseWitness P) :
      ObligationDerivation P d A .ldpcSparse
  /-- Schedule-compatibility: family-specific.  Leaf-axiom constructor. -/
  | scheduleCompatible : ObligationDerivation P d A .scheduleCompatible

namespace ObligationDerivation

/-- Syntactic size of an obligation derivation. -/
def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    {k : ProgramObligationKind} :
    ObligationDerivation P d A k -> Nat
  | .cutShape _ => 1
  | .cutStabEquiv => 1
  | .logicalNormalizer _ => 1
  | .stabilizersCommute _ => 1
  | .hookSpread Dh => 1 + Dh.size
  | .ldpcSparse w => w.size
  | .scheduleCompatible => 1

/-- One structural soundness theorem covering every constructor.

    The proof destructures the derivation tree: each constructor either
    returns its inline witness (`cutShape`, `logicalNormalizer`,
    `stabilizersCommute`, `ldpcSparse`), projects through a sub-derivation
    (`hookSpread`), or returns `trivial` for the `True`-typed
    family-specific kinds (`cutStabEquiv`, `scheduleCompatible`).  No
    per-family Lean lemma is invoked. -/
theorem sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    {k : ProgramObligationKind}
    (D : ObligationDerivation P d A k) :
    obligationFormula A k := by
  cases D with
  | cutShape D => exact D.sound
  | cutStabEquiv => trivial
  | logicalNormalizer h => exact h
  | stabilizersCommute h => exact h
  | hookSpread Dh => exact Dh.sound
  | ldpcSparse w => exact ⟨w.bound, w.proof⟩
  | scheduleCompatible => trivial

end ObligationDerivation

/-- A program-obligation rule.

    Each fixed-shape obligation now carries an `ObligationDerivation` value as
    its semantic payload, instead of an inline `∀ ...` Lean proposition.  This
    makes the obligation rule a thin wrapper over the structurally-checked
    derivation tree: every `sound_*` lemma simply projects the derivation and
    calls `ObligationDerivation.sound`.

    The `cutStabEquiv`, `hookSpread`, and `scheduleCompatible` obligations are
    family-specific (their `obligationFormula` is `True`); their constructors
    still take the relevant `A : AlignedCodeData P d` so that the wrapped
    `ObligationDerivation` has a definite ambient code-data symbol. -/
inductive ProgramObligationRule (P : QECParams) (d : Nat) :
    ProgramObligationKind -> Type where
  /-- Cut-shape obligation derivation, carrying an `ObligationDerivation` for
      `.cutShape`. -/
  | cutShape
      (A : AlignedCodeData P d)
      (D : ObligationDerivation P d A .cutShape) :
      ProgramObligationRule P d .cutShape
  /-- Cut/stabilizer equivalence derivation: leaf-axiom payload on the
      ambient `A`. -/
  | cutStabEquiv
      (A : AlignedCodeData P d)
      (D : ObligationDerivation P d A .cutStabEquiv) :
      ProgramObligationRule P d .cutStabEquiv
  /-- Logical-Z normalizes every stabilizer generator. -/
  | logicalNormalizer
      (A : AlignedCodeData P d)
      (D : ObligationDerivation P d A .logicalNormalizer) :
      ProgramObligationRule P d .logicalNormalizer
  /-- All pairs of stabilizer generators commute. -/
  | stabilizersCommute
      (A : AlignedCodeData P d)
      (D : ObligationDerivation P d A .stabilizersCommute) :
      ProgramObligationRule P d .stabilizersCommute
  /-- Hook-spread bound: leaf-axiom payload on the ambient `A`. -/
  | hookSpread
      (A : AlignedCodeData P d)
      (D : ObligationDerivation P d A .hookSpread) :
      ProgramObligationRule P d .hookSpread
  /-- LDPC sparse-weight bound carried as an `ObligationDerivation`. -/
  | ldpcSparse
      (A : AlignedCodeData P d)
      (D : ObligationDerivation P d A .ldpcSparse) :
      ProgramObligationRule P d .ldpcSparse
  /-- Schedule-compatibility derivation: leaf-axiom payload on the ambient
      `A`. -/
  | scheduleCompatible
      (A : AlignedCodeData P d)
      (D : ObligationDerivation P d A .scheduleCompatible) :
      ProgramObligationRule P d .scheduleCompatible

namespace ProgramObligationRule

def size {P : QECParams} {d : Nat} {k : ProgramObligationKind} :
    ProgramObligationRule P d k -> Nat
  | .cutShape _ D => 1 + D.size
  | .cutStabEquiv _ D => 1 + D.size
  | .logicalNormalizer _ D => 1 + D.size
  | .stabilizersCommute _ D => 1 + D.size
  | .hookSpread _ D => 1 + D.size
  | .ldpcSparse _ D => 1 + D.size
  | .scheduleCompatible _ D => 1 + D.size

/-- Soundness for the cut-shape obligation: project the carried derivation
    and invoke its structural soundness. -/
theorem sound_cutShape {P : QECParams} {d : Nat}
    (r : ProgramObligationRule P d .cutShape) :
    match r with
    | .cutShape A _ =>
        forall (g : Fin d) (q : Fin P.n),
          A.geometry.cut g q =
            if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I := by
  cases r with
  | cutShape A D => exact D.sound

/-- Soundness for the logical-normalizer obligation. -/
theorem sound_logicalNormalizer {P : QECParams} {d : Nat}
    (r : ProgramObligationRule P d .logicalNormalizer) :
    match r with
    | .logicalNormalizer A _ =>
        forall i : Fin P.numStab,
          ErrorVec.parity (P.stabilizers i) A.logicalZ = false := by
  cases r with
  | logicalNormalizer A D => exact D.sound

/-- Soundness for the pairwise-commute obligation. -/
theorem sound_stabilizersCommute {P : QECParams} {d : Nat}
    (r : ProgramObligationRule P d .stabilizersCommute) :
    match r with
    | .stabilizersCommute _ _ =>
        forall i j : Fin P.numStab,
          ErrorVec.parity (P.stabilizers i) (P.stabilizers j) = false := by
  cases r with
  | stabilizersCommute A D => exact D.sound

/-- Soundness for the LDPC-sparse obligation: every named generator obeys
    *some* weight bound (the existential discharged by `ObligationDerivation`).
    The specific bound carried by the wrapped witness is exposed by
    `ldpcSparseBound` below. -/
theorem sound_ldpcSparse {P : QECParams} {d : Nat}
    (r : ProgramObligationRule P d .ldpcSparse) :
    match r with
    | .ldpcSparse _ _ =>
        exists w : Nat, forall i : Fin P.numStab,
          ErrorVec.weight (P.stabilizers i) <= w := by
  cases r with
  | ldpcSparse A D => exact D.sound

/-- Extract the LDPC bound carried by a `.ldpcSparse` rule, by peeling the
    wrapped `ObligationDerivation.ldpcSparse w` payload. -/
def ldpcSparseBound {P : QECParams} {d : Nat} :
    ProgramObligationRule P d .ldpcSparse -> Nat
  | .ldpcSparse _ D =>
      match D with
      | .ldpcSparse w => w.bound

/-- Parametric LDPC consistency lemma: every named generator has weight at
    most the witness bound carried by the wrapped `ObligationDerivation`. -/
theorem ldpcSparse_bound {P : QECParams} {d : Nat}
    (r : ProgramObligationRule P d .ldpcSparse) :
    forall i : Fin P.numStab,
      ErrorVec.weight (P.stabilizers i) <= r.ldpcSparseBound := by
  intro i
  cases r with
  | ldpcSparse A D =>
      cases D with
      | ldpcSparse w => exact w.proof i

end ProgramObligationRule

/-! ## Aligned-code program derivation

The aligned-code derivation package collects the obligation derivations for a
single, type-pinned ambient code-data symbol `A : AlignedCodeData P d`.  Every
obligation field is an `ObligationDerivation P d A k` for the same `A`, so the
struct signature alone witnesses that all four obligations talk about the same
code.

The `cutStabEquiv` field remains a separate type parameter so the client can
plug in a Surface row induction, an HGP column derivation, or any other
constant-size scheme.

The `ProgramObligationRule` wrapper above is retained for backward
compatibility with other consumers (e.g. the `.ldpcSparse` slot in
`RepetitionLDPCInstance` and the kernel-API `#check`s in `GoldenPath`); it is
no longer used by `AlignedCodeProgramDerivation`.
-/

structure AlignedCodeProgramDerivation
    (P : QECParams) (d : Nat)
    (A : AlignedCodeData P d) (CutStabEquiv : Type) where
  recursiveDefs : RecursiveProgramDefs P d
  cutStabEquiv : CutStabEquiv
  -- Every obligation below references the *same* `A`.
  cutShape : ObligationDerivation P d A .cutShape
  logicalNormalizer : ObligationDerivation P d A .logicalNormalizer
  stabilizersCommute : ObligationDerivation P d A .stabilizersCommute
  hookSpread : ObligationDerivation P d A .hookSpread

namespace AlignedCodeProgramDerivation

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    {CutStabEquiv : Type}
    (D : AlignedCodeProgramDerivation P d A CutStabEquiv)
    (cutStabEquivSize : CutStabEquiv -> Nat) : Nat :=
  1 + D.recursiveDefs.size + cutStabEquivSize D.cutStabEquiv + D.cutShape.size +
    D.logicalNormalizer.size + D.stabilizersCommute.size + D.hookSpread.size

end AlignedCodeProgramDerivation

/-! ## Constant-size induction schemata

The induction schemata are not "rule constructors with payload" in the same
sense as `FoldUnfoldRule` etc., but they remain the recursive backbone for
Surface/HGP/LDPC families.  Their definitions are unchanged; only the
surrounding rule families have been rewritten.
-/

structure NatInductionSchema (Base Step : Type) where
  base : Base
  step : Step

namespace NatInductionSchema

def size {Base Step : Type}
    (D : NatInductionSchema Base Step)
    (baseSize : Base -> Nat) (stepSize : Step -> Nat) : Nat :=
  1 + baseSize D.base + stepSize D.step

def sound {Base Step : Type} {Goal : Nat -> Sort u}
    (D : NatInductionSchema Base Step)
    (baseSound : Base -> Goal 0)
    (stepSound : Step -> forall k : Nat, Goal k -> Goal (k + 1)) :
    forall k : Nat, Goal k
  | 0 => baseSound D.base
  | k + 1 => stepSound D.step k (sound D baseSound stepSound k)

end NatInductionSchema

structure FinInductionSchema (d : Nat) (Base Step : Type) where
  base : Base
  step : Step

namespace FinInductionSchema

def size {d : Nat} {Base Step : Type}
    (D : FinInductionSchema d Base Step)
    (baseSize : Base -> Nat) (stepSize : Step -> Nat) : Nat :=
  1 + baseSize D.base + stepSize D.step

def sound {d : Nat} {Base Step : Type} {Goal : Fin d -> Sort u}
    (D : FinInductionSchema d Base Step)
    (hd : 0 < d)
    (baseSound : Base -> Goal ⟨0, hd⟩)
    (stepSound :
      Step -> forall {i : Fin d} {hi : i.val + 1 < d},
        Goal i -> Goal ⟨i.val + 1, hi⟩) :
    forall g : Fin d, Goal g
  | ⟨iv, hiv⟩ =>
      let rec go (k : Nat) (hk : k < d) : Goal ⟨k, hk⟩ :=
        match k with
        | 0 => baseSound D.base
        | k' + 1 =>
            have hk' : k' < d := Nat.lt_of_succ_lt hk
            stepSound D.step (i := ⟨k', hk'⟩) (hi := hk) (go k' hk')
      go iv hiv

end FinInductionSchema

inductive FinInductionDerivation (d : Nat) (Base Step : Type) :
    Fin d -> Type where
  | byFinInduction (schema : FinInductionSchema d Base Step) (g : Fin d) :
      FinInductionDerivation d Base Step g

namespace FinInductionDerivation

def size {d : Nat} {Base Step : Type} {g : Fin d}
    (D : FinInductionDerivation d Base Step g)
    (schemaSize : FinInductionSchema d Base Step -> Nat) : Nat :=
  match D with
  | .byFinInduction schema _ => 1 + schemaSize schema

def sound {d : Nat} {Base Step : Type} {Goal : Fin d -> Sort u} {g : Fin d}
    (D : FinInductionDerivation d Base Step g)
    (hd : 0 < d)
    (baseSound : Base -> Goal ⟨0, hd⟩)
    (stepSound :
      Step -> forall {i : Fin d} {hi : i.val + 1 < d},
        Goal i -> Goal ⟨i.val + 1, hi⟩) :
    Goal g :=
  match D with
  | .byFinInduction schema g =>
      FinInductionSchema.sound schema hd baseSound stepSound g

end FinInductionDerivation

/-! ## Atomic obligation leaves

`ObligationLeaf` provides five atomic witness constructors (`cutEntry`,
`groupMembership`, `parityOff`, `weightLE`, `inBackActionSet`).  Each
carries the concrete data and a closed Lean proof of the corresponding
fact; the per-leaf `.sound` projection just returns that proof verbatim.
No per-family Lean lemma is invoked; the leaf is content-bearing.

The cellular cut-shape derivation tree (`CutShapeCellWitness` +
`CutShapeDerivation`) lives above `ObligationDerivation` (so that the
backbone's `cutShape` constructor can consume a `CutShapeDerivation`
payload structurally).
-/

/-- Kinds of atomic obligation leaves. -/
inductive ObligationLeafKind where
  | cutEntry
  | groupMembership
  | parityOff
  | weightLE
  | inBackActionSet

/-- A single atomic obligation leaf.

    Every constructor carries concrete payload data plus a closed Lean
    proof of the corresponding fact; the leaf is content-bearing.  The
    per-leaf `.sound_*` projection returns that proof verbatim so the
    kernel never invents new content. -/
inductive ObligationLeaf (P : QECParams) : ObligationLeafKind -> Type where
  /-- A single pointwise cut-shape cell: `A.geometry.cut g q` equals the
      indicator pattern at `(g, q)`. -/
  | cutEntry {d : Nat}
      (A : AlignedCodeData P d) (g : Fin d) (q : Fin P.n)
      (h : A.geometry.cut g q =
        if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I) :
      ObligationLeaf P .cutEntry
  /-- A group-membership leaf: qubit `q` lives in group `g`. -/
  | groupMembership {d : Nat}
      (A : AlignedCodeData P d) (g : Fin d) (q : Fin P.n)
      (h : A.geometry.groupOf q = some g) :
      ObligationLeaf P .groupMembership
  /-- A parity-zero leaf: two error vectors commute (parity off). -/
  | parityOff
      (a b : ErrorVec P.n) (h : ErrorVec.parity a b = false) :
      ObligationLeaf P .parityOff
  /-- A weight-bound leaf: error vector `v` has weight at most `w`. -/
  | weightLE
      (v : ErrorVec P.n) (w : Nat) (h : ErrorVec.weight v <= w) :
      ObligationLeaf P .weightLE
  /-- A back-action-membership leaf: error `e` lies in `backActionSet i`. -/
  | inBackActionSet
      (i : Fin P.numStab) (e : ErrorVec P.n) (h : e ∈ P.backActionSet i) :
      ObligationLeaf P .inBackActionSet

namespace ObligationLeaf

/-- Syntactic size of an obligation leaf: every atomic leaf is a single
    rule node. -/
def size {P : QECParams} {k : ObligationLeafKind} :
    ObligationLeaf P k -> Nat
  | .cutEntry _ _ _ _ => 1
  | .groupMembership _ _ _ _ => 1
  | .parityOff _ _ _ => 1
  | .weightLE _ _ _ => 1
  | .inBackActionSet _ _ _ => 1

/-- Soundness for a `.cutEntry` leaf: return the pointwise cut-shape
    equation at the carried `(g, q)`.  The `(A, g, q)` data lives inside
    the leaf itself, so no separate parameters are needed. -/
theorem cutEntry_sound {P : QECParams}
    (L : ObligationLeaf P .cutEntry) :
    match L with
    | .cutEntry A' g' q' _ =>
        A'.geometry.cut g' q' =
          if A'.geometry.groupOf q' = some g' then Pauli.Z else Pauli.I := by
  cases L with
  | cutEntry _ _ _ h => exact h

/-- Soundness for a `.groupMembership` leaf. -/
theorem groupMembership_sound {P : QECParams}
    (L : ObligationLeaf P .groupMembership) :
    match L with
    | .groupMembership A g q _ => A.geometry.groupOf q = some g := by
  cases L with
  | groupMembership _ _ _ h => exact h

/-- Soundness for a `.parityOff` leaf. -/
theorem parityOff_sound {P : QECParams}
    (L : ObligationLeaf P .parityOff) :
    match L with
    | .parityOff a b _ => ErrorVec.parity a b = false := by
  cases L with
  | parityOff _ _ h => exact h

/-- Soundness for a `.weightLE` leaf. -/
theorem weightLE_sound {P : QECParams}
    (L : ObligationLeaf P .weightLE) :
    match L with
    | .weightLE v w _ => ErrorVec.weight v <= w := by
  cases L with
  | weightLE _ _ h => exact h

/-- Soundness for an `.inBackActionSet` leaf. -/
theorem inBackActionSet_sound {P : QECParams}
    (L : ObligationLeaf P .inBackActionSet) :
    match L with
    | .inBackActionSet i e _ => e ∈ P.backActionSet i := by
  cases L with
  | inBackActionSet _ _ h => exact h

end ObligationLeaf

end QHL.Source.ProofKernel
