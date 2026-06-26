import QStab.QHL.Assertion.Semantics
import QStab.Paper.BarrierFramework
import QStab.Paper.AlignedBarrier

/-! # Syntactic barrier assertions

The barrier remains a named first-order function symbol. Its four mathematical
properties are carried by `BarrierFunction` and `IsLAligned`; the invariant
appearing in a Hoare triple is now a genuine `Formula`.
-/

namespace QHL.AssertionLang

open QStab QStab.Examples.SurfaceGeneral
open QStab.Paper.BarrierFramework QStab.Paper.AlignedBarrier

/-- The bar-Z parity-zero generator list for an `AlignedCodeSpec`: the
    stabilizer generators. Every member of the bar-Z class commutes with
    every stabilizer (i.e. has parity `false`). -/
def alignedBarZParityZero {d : Nat} (spec : AlignedCodeSpec d) :
    List (ErrorVec spec.params.n) :=
  (List.finRange spec.params.numStab).map spec.params.stabilizers

/-- The bar-Z parity-one generator list for an `AlignedCodeSpec`: the
    chosen logical-Z representative. Every member of the bar-Z class
    anticommutes with the logical-Z operator (i.e. has parity `true`). -/
def alignedBarZParityOne {d : Nat} (spec : AlignedCodeSpec d) :
    List (ErrorVec spec.params.n) :=
  [spec.logicalZ]

/-- The syntactic parity-coset membership predicate AGREES on the nose with
    `(AlignedBarrier.barZClass spec).contains`. The proof is mostly bookkeeping
    around `List.mem_map`/`List.mem_singleton`; nothing semantic. -/
theorem alignedBarZ_contains_iff {d : Nat} (spec : AlignedCodeSpec d)
    (E : ErrorVec spec.params.n) :
    ((∀ S, S ∈ alignedBarZParityZero spec → ErrorVec.parity S E = false) ∧
     (∀ T, T ∈ alignedBarZParityOne  spec → ErrorVec.parity T E = true)) ↔
    (QStab.Paper.AlignedBarrier.barZClass spec).contains E := by
  unfold QStab.Paper.AlignedBarrier.barZClass alignedBarZParityZero alignedBarZParityOne
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun i => ?_, h1 spec.logicalZ (List.mem_singleton.mpr rfl)⟩
    apply h0
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun S hS => ?_, fun T hT => ?_⟩
    · rcases List.mem_map.mp hS with ⟨i, _, rfl⟩
      exact h0 i
    · rcases List.mem_singleton.mp hT with rfl
      exact h1

/-- Expose an `AlignedCodeSpec`'s bar-Z parity class through a named
    assertion-language symbol via its SYNTACTIC parity-coset description.
    It detects the component that anticommutes with `spec.logicalZ`; it is not
    the full union of all nontrivial logical cosets.
    The classical `(AlignedBarrier.barZClass spec).contains` predicate is
    NOT plumbed through as a `Prop` atom; instead, the structure carries
    the two finite generator lists and `LogicalClassSymbol.contains`
    computes the conjunction. The denotational equivalence with the
    original predicate is the separate lemma `alignedBarZ_contains_iff`.

    This is the syntactic constructor used by every barrier example
    (Surface, HGP, ...). -/
def LogicalClassSymbol.ofAlignedBarZ {d : Nat} (name : String) (spec : AlignedCodeSpec d) :
    LogicalClassSymbol spec.params where
  name := name
  parityZero := alignedBarZParityZero spec
  parityOne  := alignedBarZParityOne spec
  distance := d

/-- Legacy bridge: build a `LogicalClassSymbol` from a `LogicalClass` ONLY
    when the caller supplies a syntactic parity-coset witness. The proof
    obligation `h_iff` ensures no arbitrary `Prop` predicate can hide.

    Existing call sites that previously wrote
    `LogicalClassSymbol.ofLogicalClass name (barZClass spec)` are migrated
    to the specialised `LogicalClassSymbol.ofAlignedBarZ name spec` which
    discharges `h_iff` by `alignedBarZ_contains_iff`. -/
def LogicalClassSymbol.ofLogicalClass {P : QECParams} (name : String)
    (L : LogicalClass P)
    (parityZero parityOne : List (ErrorVec P.n))
    (_h_iff : ∀ E,
      ((∀ S, S ∈ parityZero → ErrorVec.parity S E = false) ∧
       (∀ T, T ∈ parityOne  → ErrorVec.parity T E = true)) ↔ L.contains E) :
    LogicalClassSymbol P where
  name := name
  parityZero := parityZero
  parityOne  := parityOne
  distance := L.d_L

/-- Expose an existing barrier through a named assertion-language symbol. -/
def BarrierSymbol.ofBarrier {P : QECParams} {L : LogicalClass P} (name : String)
    (beta : BarrierFunction P L) : BarrierSymbol P where
  name := name
  body := .external beta.mu

/-- The syntactic barrier potential `beta(error) + (C_budget - C)`. -/
def spentF {P : QECParams} : Term P [] .nat :=
  .natSub .budget .remaining

/-- The circuit-distance lower-bound assertion `distance ≤ C_budget - C`. -/
def distanceLowerBoundF {P : QECParams} (L : LogicalClassSymbol P) : Formula P [] :=
  .le (.natLit L.distance) spentF

/-- If the current error is logical, at least the logical distance has been
    spent. This is the assertion-language statement of a circuit-level code
    distance lower bound. -/
def circuitDistanceF {P : QECParams} (L : LogicalClassSymbol P) : Formula P [] :=
  .imp (.logicalMember L .error) (distanceLowerBoundF L)

/-- The distance lower-bound assertion for a finite logical-coset union. -/
def distanceSetLowerBoundF {P : QECParams} (L : LogicalSetSymbol P) : Formula P [] :=
  .le (.natLit L.distance) spentF

/-- If the current error is in the finite logical-coset union, at least the
    logical distance has been spent.  This is the shared assertion-language
    form needed for a full "any nontrivial logical residual" theorem. -/
def circuitDistanceSetF {P : QECParams} (L : LogicalSetSymbol P) : Formula P [] :=
  .imp (.logicalSetMember L .error) (distanceSetLowerBoundF L)

/-- Finite conjunction that the error commutes with every stabilizer generator.

This is intentionally expanded over `List.finRange P.numStab` instead of being
an opaque centralizer predicate.  For surface d=3 it prints as the eight
stabilizer-parity equations. -/
def centralizerF {P : QECParams} {Γ : List (Ty P)} (E : Term P Γ .vec) :
    Formula P Γ :=
  (List.finRange P.numStab).foldr
    (fun i acc =>
      .and
        (.eq (.parity (.stabilizer (.stabLit i)) E) (.boolLit false))
        acc)
    .top

/-- Rigorous "any nontrivial logical residual" assertion:

`E` commutes with every stabilizer generator, but `E` is not in the stabilizer
group generated by those generators. -/
def logicalAnyResidualF {P : QECParams} {Γ : List (Ty P)} (E : Term P Γ .vec) :
    Formula P Γ :=
  .and (centralizerF E) (.not (.inStab E))

/-- Rigorous code-distance lower bound for any nontrivial logical residual. -/
def circuitDistanceAnyF {P : QECParams} (distance : Nat) : Formula P [] :=
  .imp (logicalAnyResidualF .error) (.le (.natLit distance) spentF)

/-- The syntactic barrier potential `beta(error) + (C_budget - C)`. -/
def barrierPotentialF {P : QECParams} (beta : BarrierSymbol P) : Term P [] .nat :=
  .natAdd (.barrier beta .error) spentF

/-- The barrier invariant as a closed formula in the QHL assertion language. -/
def barrierInvF {P : QECParams} (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
    Formula P [] :=
  .and (.le (.natLit L.distance) (barrierPotentialF beta)) (.le .remaining .budget)

/-- Syntactic barrier law: the identity has full logical distance. -/
def barrierIdentityF {P : QECParams} (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
    Formula P [] :=
  .eq (.barrier beta .identity) (.natLit L.distance)

/-- Syntactic barrier law: the barrier vanishes on the logical class. -/
def barrierLogicalF {P : QECParams} (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
    Formula P [] :=
  .all .vec
    (.imp (.logicalMember L (.var .zero))
      (.eq (.barrier beta (.var .zero)) (.natLit 0)))

/-- Syntactic triangle law for arbitrary Pauli errors `E` and `F`. -/
def barrierTriangleF {P : QECParams} (beta : BarrierSymbol P) : Formula P [] :=
  .all .vec (.all .vec
    (.le
      (.barrier beta (.var (.succ .zero)))
      (.natAdd
        (.barrier beta (.vecMul (.var .zero) (.var (.succ .zero))))
        (.weight (.var .zero)))))

/-- Syntactic schedule-alignment law for every legal back-action error. -/
def barrierAlignedF {P : QECParams} (beta : BarrierSymbol P) : Formula P [] :=
  .all .stab (.all .vec
    (.imp
      (.backAction (.var (.succ .zero)) (.var .zero))
      (.all .vec
        (.le
          (.barrier beta (.var .zero))
          (.natAdd
            (.barrier beta (.vecMul (.var (.succ .zero)) (.var .zero)))
            (.natLit 1))))))

/-- The four barrier obligations as one closed assertion-language certificate. -/
def barrierContractF {P : QECParams} (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
    Formula P [] :=
  .and (barrierIdentityF beta L)
    (.and (barrierLogicalF beta L) (.and (barrierTriangleF beta) (barrierAlignedF beta)))

/-- Checked evidence for the identity conjunct of a barrier contract.

    This is a first-class assertion-language proof leaf, not a proof of the
    whole `barrierContractF` formula. Existing mathematical examples may still
    build this leaf from their algebraic development, but the Hoare checker can
    inspect which barrier law is being used. -/
inductive BarrierIdentityCertificate {P : QECParams}
    (beta : BarrierSymbol P) (L : LogicalClassSymbol P) : Type where
  | checked :
      beta.eval (ErrorVec.identity P.n) = L.distance ->
      BarrierIdentityCertificate beta L

/-- Checked evidence for the logical-class zero conjunct. -/
inductive BarrierLogicalCertificate {P : QECParams}
    (beta : BarrierSymbol P) (L : LogicalClassSymbol P) : Type where
  | checked :
      (forall E : ErrorVec P.n, L.contains E -> beta.eval E = 0) ->
      BarrierLogicalCertificate beta L

/-- Checked evidence for the triangle conjunct. -/
inductive BarrierTriangleCertificate {P : QECParams}
    (beta : BarrierSymbol P) : Type where
  | checked :
      (forall E F : ErrorVec P.n,
        beta.eval E <= beta.eval (ErrorVec.mul F E) + ErrorVec.weight F) ->
      BarrierTriangleCertificate beta

/-- Checked evidence for the schedule-alignment conjunct. -/
inductive BarrierAlignedCertificate {P : QECParams}
    (beta : BarrierSymbol P) : Type where
  | checked :
      (forall (i : Fin P.numStab) (e : ErrorVec P.n),
        e ∈ P.backActionSet i ->
        forall E : ErrorVec P.n,
          beta.eval E <= beta.eval (ErrorVec.mul e E) + 1) ->
      BarrierAlignedCertificate beta

namespace BarrierIdentityCertificate

def size {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    BarrierIdentityCertificate beta L -> Nat
  | .checked _ => 1

def sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    BarrierIdentityCertificate beta L ->
      beta.eval (ErrorVec.identity P.n) = L.distance
  | .checked h => h

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (cert : BarrierIdentityCertificate beta L) :
    cert.size = 1 := by
  cases cert
  rfl

end BarrierIdentityCertificate

namespace BarrierLogicalCertificate

def size {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    BarrierLogicalCertificate beta L -> Nat
  | .checked _ => 1

def sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    BarrierLogicalCertificate beta L ->
      forall E : ErrorVec P.n, L.contains E -> beta.eval E = 0
  | .checked h => h

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (cert : BarrierLogicalCertificate beta L) :
    cert.size = 1 := by
  cases cert
  rfl

end BarrierLogicalCertificate

namespace BarrierTriangleCertificate

def size {P : QECParams} {beta : BarrierSymbol P} :
    BarrierTriangleCertificate beta -> Nat
  | .checked _ => 1

def sound {P : QECParams} {beta : BarrierSymbol P} :
    BarrierTriangleCertificate beta ->
      forall E F : ErrorVec P.n,
        beta.eval E <= beta.eval (ErrorVec.mul F E) + ErrorVec.weight F
  | .checked h => h

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P}
    (cert : BarrierTriangleCertificate beta) :
    cert.size = 1 := by
  cases cert
  rfl

end BarrierTriangleCertificate

namespace BarrierAlignedCertificate

def size {P : QECParams} {beta : BarrierSymbol P} :
    BarrierAlignedCertificate beta -> Nat
  | .checked _ => 1

def sound {P : QECParams} {beta : BarrierSymbol P} :
    BarrierAlignedCertificate beta ->
      forall (i : Fin P.numStab) (e : ErrorVec P.n),
        e ∈ P.backActionSet i ->
        forall E : ErrorVec P.n,
          beta.eval E <= beta.eval (ErrorVec.mul e E) + 1
  | .checked h => h

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P}
    (cert : BarrierAlignedCertificate beta) :
    cert.size = 1 := by
  cases cert
  rfl

end BarrierAlignedCertificate

/-- A tiny formula-proof checker for the barrier-contract fragment.

    The four barrier leaves are assertion-language laws; conjunction assembly
    is ordinary formula proof syntax. There is deliberately no constructor that
    accepts an arbitrary `Formula.Valid` theorem. -/
inductive BarrierFormulaCertificate {P : QECParams} : Formula P [] -> Type where
  | barrierIdentity (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
      BarrierIdentityCertificate beta L ->
      BarrierFormulaCertificate (barrierIdentityF beta L)
  | barrierLogical (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
      BarrierLogicalCertificate beta L ->
      BarrierFormulaCertificate (barrierLogicalF beta L)
  | barrierTriangle (beta : BarrierSymbol P) :
      BarrierTriangleCertificate beta ->
      BarrierFormulaCertificate (barrierTriangleF beta)
  | barrierAligned (beta : BarrierSymbol P) :
      BarrierAlignedCertificate beta ->
      BarrierFormulaCertificate (barrierAlignedF beta)
  | andIntro {A B : Formula P []} :
      BarrierFormulaCertificate A ->
      BarrierFormulaCertificate B ->
      BarrierFormulaCertificate (.and A B)

namespace BarrierFormulaCertificate

/-- Syntactic size of the accepted barrier-formula proof object. It counts
    proof-rule nodes, not the size of the denoted code family. -/
def size {P : QECParams} {A : Formula P []} :
    BarrierFormulaCertificate (P := P) A -> Nat
  | .barrierIdentity _ _ _ => 1
  | .barrierLogical _ _ _ => 1
  | .barrierTriangle _ _ => 1
  | .barrierAligned _ _ => 1
  | .andIntro hA hB => 1 + hA.size + hB.size

/-- Soundness of the barrier-fragment formula checker. -/
def sound {P : QECParams} {A : Formula P []} :
    BarrierFormulaCertificate (P := P) A -> A.Valid
  | .barrierIdentity beta L cert => by
      intro σ
      simpa [barrierIdentityF, Formula.denote, Formula.eval, Term.eval] using cert.sound
  | .barrierLogical beta L cert => by
      intro σ E hE
      simpa [barrierLogicalF, Formula.denote, Formula.eval, Term.eval] using cert.sound E hE
  | .barrierTriangle beta cert => by
      intro σ E F
      simpa [barrierTriangleF, Formula.denote, Formula.eval, Term.eval] using cert.sound E F
  | .barrierAligned beta cert => by
      intro σ i e he E
      simpa [barrierAlignedF, Formula.denote, Formula.eval, Term.eval] using cert.sound i e he E
  | .andIntro hA hB => by
      intro σ
      exact ⟨hA.sound σ, hB.sound σ⟩

end BarrierFormulaCertificate

/-- Checked evidence for the full barrier contract.

    The object is a tuple of the four law certificates. Its formula proof is
    assembled by the fixed assertion-language checker above; there is no
    escape hatch from an arbitrary closed-formula validity theorem. -/
structure BarrierContractCertificate {P : QECParams}
    (beta : BarrierSymbol P) (L : LogicalClassSymbol P) : Type where
  identity : BarrierIdentityCertificate beta L
  logical : BarrierLogicalCertificate beta L
  triangle : BarrierTriangleCertificate beta
  aligned : BarrierAlignedCertificate beta

namespace BarrierContractCertificate

def size {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) : Nat :=
  1 + contract.identity.size + contract.logical.size +
    contract.triangle.size + contract.aligned.size

/-- Every full barrier-contract certificate has constant syntactic size,
    independent of code distance, stabilizer count, or schedule size. -/
theorem size_eq_five {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    contract.size = 5 := by
  cases contract with
  | mk identity logical triangle aligned =>
      cases identity
      cases logical
      cases triangle
      cases aligned
      rfl

def formulaCertificate {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    BarrierFormulaCertificate (barrierContractF beta L) :=
  .andIntro (.barrierIdentity beta L contract.identity)
    (.andIntro (.barrierLogical beta L contract.logical)
      (.andIntro (.barrierTriangle beta contract.triangle)
        (.barrierAligned beta contract.aligned)))

/-- Soundness of an accepted barrier-contract certificate. -/
def sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    (barrierContractF beta L).Valid :=
  contract.formulaCertificate.sound

/-- The expanded conjunction proof also has constant size: four law leaves
    plus three conjunction nodes. -/
theorem formulaCertificate_size_eq_seven {P : QECParams}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    contract.formulaCertificate.size = 7 := by
  cases contract with
  | mk identity logical triangle aligned =>
      cases identity
      cases logical
      cases triangle
      cases aligned
      rfl

def identity_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    beta.eval (ErrorVec.identity P.n) = L.distance :=
  contract.identity.sound

def logical_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    forall E : ErrorVec P.n, L.contains E -> beta.eval E = 0 :=
  contract.logical.sound

def triangle_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    forall E F : ErrorVec P.n,
      beta.eval E <= beta.eval (ErrorVec.mul F E) + ErrorVec.weight F :=
  contract.triangle.sound

def aligned_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : BarrierContractCertificate beta L) :
    forall (i : Fin P.numStab) (e : ErrorVec P.n),
      e ∈ P.backActionSet i ->
      forall E : ErrorVec P.n,
        beta.eval E <= beta.eval (ErrorVec.mul e E) + 1 :=
  contract.aligned.sound

end BarrierContractCertificate

/-- Interpreting `barrierInvF` recovers the mathematical barrier predicate exactly.
    Note: only depends on `LogicalClassSymbol.distance` (set to `L.d_L`),
    not on the syntactic `parityZero/parityOne` lists. The proof is therefore
    independent of the parity-witness data. -/
theorem denote_barrierInvF {P : QECParams} {L : LogicalClass P}
    (name : String) (beta : BarrierFunction P L)
    (parityZero parityOne : List (ErrorVec P.n))
    (h_iff : ∀ E,
      ((∀ S, S ∈ parityZero → ErrorVec.parity S E = false) ∧
       (∀ T, T ∈ parityOne  → ErrorVec.parity T E = true)) ↔ L.contains E)
    (σ : State P) :
    (barrierInvF (BarrierSymbol.ofBarrier name beta)
      (LogicalClassSymbol.ofLogicalClass name L parityZero parityOne h_iff)).denote σ
        <-> BarrierInvPred beta σ := by
  rfl

/-- Generic aligned-code geometry as assertion syntax. -/
def GeometrySymbol.ofAlignedCodeSpec {d : Nat}
    (name : String) (spec : AlignedCodeSpec d) : GeometrySymbol spec.params d where
  name := name
  groupOf := spec.group
  cut := spec.cutOp

/-- Proof-free aligned-code data extracted from the legacy `AlignedCodeSpec`
    package. This is a compatibility compiler: the verifier-facing object is
    `AlignedCodeData`, while the old theorem fields are consumed only by the
    checked certificate compiler below. -/
def AlignedCodeData.ofAlignedCodeSpec {d : Nat}
    (name geomName : String) (spec : AlignedCodeSpec d) :
    AlignedCodeData spec.params d where
  name := name
  logicalZ := spec.logicalZ
  geometry := GeometrySymbol.ofAlignedCodeSpec geomName spec

@[simp] theorem AlignedCodeData.logicalClass_ofAlignedCodeSpec {d : Nat}
    (codeName geomName logicalName : String) (spec : AlignedCodeSpec d) :
    (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec).logicalClass logicalName =
      LogicalClassSymbol.ofAlignedBarZ logicalName spec := by
  rfl

theorem GeometrySymbol.groupsX_ofAlignedCodeSpec {d : Nat}
    (name : String) (spec : AlignedCodeSpec d)
    (S E : ErrorVec spec.params.n) :
    (GeometrySymbol.ofAlignedCodeSpec name spec).groupsX S E =
      QStab.Paper.AlignedBarrier.groupsX spec S E := by
  rfl

private theorem foldl_min_le_init {α : Type} (f : α -> Nat) :
    forall (l : List α) (init : Nat),
      l.foldl (fun best a => Nat.min best (f a)) init <= init
  | [], init => by simp
  | a :: rest, init => by
      simp [List.foldl]
      exact Nat.le_trans (foldl_min_le_init f rest (Nat.min init (f a)))
        (Nat.min_le_left init (f a))

private theorem foldl_min_le_of_mem {α : Type} (f : α -> Nat) (x : α)
    (l : List α) (init : Nat) (h : x ∈ l) :
    l.foldl (fun best a => Nat.min best (f a)) init <= f x := by
  induction l generalizing init with
  | nil => cases h
  | cons y ys ih =>
      simp only [List.foldl]
      simp only [List.mem_cons] at h
      rcases h with hxy | htail
      · subst hxy
        exact Nat.le_trans (foldl_min_le_init f ys (Nat.min init (f x)))
          (Nat.min_le_right init (f x))
      · exact ih (Nat.min init (f y)) htail

private theorem le_foldl_min {α : Type} (f : α -> Nat) (bound : Nat) :
    forall (l : List α) (init : Nat), bound <= init ->
      (forall x, x ∈ l -> bound <= f x) ->
      bound <= l.foldl (fun best a => Nat.min best (f a)) init
  | [], init, hinit, _ => by simpa using hinit
  | a :: rest, init, hinit, hall => by
      simp [List.foldl]
      apply le_foldl_min f bound rest (Nat.min init (f a))
      · exact Nat.le_min.mpr ⟨hinit, hall a (by simp)⟩
      · intro x hx
        exact hall x (by simp [hx])

private theorem maskProductFoldr_inStab (P : QECParams)
    (mask : Fin P.numStab -> Bool) :
    forall l : List (Fin P.numStab),
      InStab P (l.foldr
        (fun i acc => if mask i then ErrorVec.mul (P.stabilizers i) acc else acc)
        (ErrorVec.identity P.n))
  | [] => by exact InStab.identity
  | i :: rest => by
      by_cases h : mask i = true
      · simp [List.foldr, h]
        exact InStab.mul (InStab.gen i) (maskProductFoldr_inStab P mask rest)
      · have hf : mask i = false := by
          cases hm : mask i <;> simp_all
        simp [List.foldr, hf]
        exact maskProductFoldr_inStab P mask rest

/-- Every syntactic stabilizer mask denotes an element of the stabilizer group. -/
theorem maskStabilizerProduct_inStab (P : QECParams)
    (mask : Fin P.numStab -> Bool) :
    InStab P (maskStabilizerProduct P mask) := by
  unfold maskStabilizerProduct
  exact maskProductFoldr_inStab P mask (List.finRange P.numStab)

/-- Flip one Boolean coordinate of a stabilizer mask. -/
def toggleMask {P : QECParams} (mask : Fin P.numStab -> Bool)
    (i : Fin P.numStab) : Fin P.numStab -> Bool :=
  Function.update mask i (!mask i)

private def selectedProduct (P : QECParams) (mask : Fin P.numStab -> Bool)
    (l : List (Fin P.numStab)) : ErrorVec P.n :=
  l.foldr (fun i acc => if mask i then ErrorVec.mul (P.stabilizers i) acc else acc)
    (ErrorVec.identity P.n)

private theorem ErrorVec.mul_left_comm' {n : Nat} (a b c : ErrorVec n) :
    ErrorVec.mul a (ErrorVec.mul b c) = ErrorVec.mul b (ErrorVec.mul a c) := by
  rw [← ErrorVec.mul_assoc, ErrorVec.mul_comm a b, ErrorVec.mul_assoc]

private theorem ErrorVec.mul_self_left' {n : Nat} (a b : ErrorVec n) :
    ErrorVec.mul a (ErrorVec.mul a b) = b := by
  rw [← ErrorVec.mul_assoc, ErrorVec.mul_self_cancel, ErrorVec.mul_identity_left]

private theorem selectedProduct_congr_list {P : QECParams}
    {mask₁ mask₂ : Fin P.numStab -> Bool} :
    forall l : List (Fin P.numStab),
      (forall i, i ∈ l -> mask₁ i = mask₂ i) ->
      selectedProduct P mask₁ l = selectedProduct P mask₂ l
  | [], _ => by rfl
  | i :: rest, h => by
      unfold selectedProduct
      simp [List.foldr]
      have hi : mask₁ i = mask₂ i := h i (by simp)
      have hrest : selectedProduct P mask₁ rest = selectedProduct P mask₂ rest :=
        selectedProduct_congr_list rest (fun j hj => h j (by simp [hj]))
      unfold selectedProduct at hrest
      rw [hi, hrest]

private theorem selectedProduct_toggle_not_mem {P : QECParams}
    (mask : Fin P.numStab -> Bool) (i : Fin P.numStab) :
    forall l : List (Fin P.numStab), i ∉ l ->
      selectedProduct P (toggleMask mask i) l = selectedProduct P mask l := by
  intro l hnot
  apply selectedProduct_congr_list
  intro j hj
  unfold toggleMask
  have hji : j ≠ i := by
    intro hEq
    apply hnot
    simpa [hEq] using hj
  simp [Function.update, hji]

private theorem selectedProduct_toggle_mem {P : QECParams}
    (mask : Fin P.numStab -> Bool) (i : Fin P.numStab) :
    forall l : List (Fin P.numStab), l.Nodup -> i ∈ l ->
      selectedProduct P (toggleMask mask i) l =
        ErrorVec.mul (P.stabilizers i) (selectedProduct P mask l)
  | [], _, hmem => by cases hmem
  | j :: rest, hnodup, hmem => by
      have hnodup_parts := List.nodup_cons.mp hnodup
      have hnot_j_rest : j ∉ rest := hnodup_parts.1
      have hnodup_rest : rest.Nodup := hnodup_parts.2
      by_cases hEq : j = i
      ·
          subst j
          have hnot_i_rest : i ∉ rest := by simpa using hnot_j_rest
          have hrest := selectedProduct_toggle_not_mem mask i rest hnot_i_rest
          unfold selectedProduct
          simp only [List.foldr]
          have htoggle_i : toggleMask mask i i = !mask i := by
            simp [toggleMask, Function.update]
          rw [htoggle_i]
          unfold selectedProduct at hrest
          rw [hrest]
          cases hm : mask i <;> simp [ErrorVec.mul_self_left']
      ·
          have hi_rest : i ∈ rest := by
            have hij : i ≠ j := by
              intro hij
              exact hEq hij.symm
            simpa [hij] using hmem
          have ih := selectedProduct_toggle_mem mask i rest hnodup_rest hi_rest
          unfold selectedProduct
          simp only [List.foldr]
          have htoggle_j : toggleMask mask i j = mask j := by
            simp [toggleMask, Function.update, hEq]
          rw [htoggle_j]
          unfold selectedProduct at ih
          rw [ih]
          cases hm : mask j <;> simp [ErrorVec.mul_left_comm']

theorem maskStabilizerProduct_toggle {P : QECParams}
    (mask : Fin P.numStab -> Bool) (i : Fin P.numStab) :
    maskStabilizerProduct P (toggleMask mask i) =
      ErrorVec.mul (P.stabilizers i) (maskStabilizerProduct P mask) := by
  unfold maskStabilizerProduct
  exact selectedProduct_toggle_mem mask i (List.finRange P.numStab)
    (List.nodup_finRange P.numStab) (List.mem_finRange i)

/-- A stabilizer expression as a list of generator indices. -/
def stabExprProduct (P : QECParams) : List (Fin P.numStab) -> ErrorVec P.n
  | [] => ErrorVec.identity P.n
  | i :: rest => ErrorVec.mul (P.stabilizers i) (stabExprProduct P rest)

/-- Normalize a stabilizer expression to its parity mask. -/
def maskOfStabExpr {P : QECParams} :
    List (Fin P.numStab) -> Fin P.numStab -> Bool
  | [] => fun _ => false
  | i :: rest => toggleMask (maskOfStabExpr rest) i

theorem maskStabilizerProduct_maskOfStabExpr (P : QECParams) :
    forall expr : List (Fin P.numStab),
      maskStabilizerProduct P (maskOfStabExpr expr) = stabExprProduct P expr
  | [] => by
      unfold maskStabilizerProduct maskOfStabExpr stabExprProduct
      induction List.finRange P.numStab with
      | nil => rfl
      | cons i rest ih => simp [List.foldr]
  | i :: rest => by
      simp [maskOfStabExpr, stabExprProduct, maskStabilizerProduct_toggle,
        maskStabilizerProduct_maskOfStabExpr P rest]

theorem stabExprProduct_append (P : QECParams) :
    forall a b : List (Fin P.numStab),
      stabExprProduct P (a ++ b) =
        ErrorVec.mul (stabExprProduct P a) (stabExprProduct P b)
  | [], b => by simp [stabExprProduct, ErrorVec.mul_identity_left]
  | i :: rest, b => by
      simp [stabExprProduct, stabExprProduct_append P rest b]
      rw [ErrorVec.mul_assoc]

theorem inStab_exists_stabExprProduct (P : QECParams) {S : ErrorVec P.n} :
    InStab P S -> ∃ expr : List (Fin P.numStab), stabExprProduct P expr = S
  | InStab.identity => ⟨[], rfl⟩
  | InStab.gen i => by
      refine ⟨[i], ?_⟩
      simp [stabExprProduct, ErrorVec.mul_identity_right]
  | InStab.mul h₁ h₂ => by
      obtain ⟨e₁, he₁⟩ := inStab_exists_stabExprProduct P h₁
      obtain ⟨e₂, he₂⟩ := inStab_exists_stabExprProduct P h₂
      refine ⟨e₁ ++ e₂, ?_⟩
      rw [stabExprProduct_append, he₁, he₂]

/-- Every inductive stabilizer product has an equivalent finite Boolean mask. -/
theorem inStab_exists_maskStabilizerProduct (P : QECParams)
    {S : ErrorVec P.n} (hS : InStab P S) :
    ∃ mask : Fin P.numStab -> Bool, maskStabilizerProduct P mask = S := by
  obtain ⟨expr, hExpr⟩ := inStab_exists_stabExprProduct P hS
  exact ⟨maskOfStabExpr expr, (maskStabilizerProduct_maskOfStabExpr P expr).trans hExpr⟩

theorem GeometrySymbol.omegaMask_le_mask {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (E : ErrorVec P.n) (mask : Fin P.numStab -> Bool) :
    G.omegaMask E <= G.groupsX (maskStabilizerProduct P mask) E := by
  classical
  unfold GeometrySymbol.omegaMask
  exact foldl_min_le_of_mem
    (fun mask => G.groupsX (maskStabilizerProduct P mask) E) mask
    (allStabMasks P)
    (G.groupsX (maskStabilizerProduct P (fun _ => false)) E)
    (allStabMasks_complete P mask)

theorem GeometrySymbol.omegaGroup_le_omegaMask_of_groups {d : Nat}
    (spec : AlignedCodeSpec d) (G : GeometrySymbol spec.params d)
    (hG : forall S E, G.groupsX S E = QStab.Paper.AlignedBarrier.groupsX spec S E)
    (E : ErrorVec spec.params.n) :
    QStab.Paper.AlignedBarrier.omegaGroup spec E <= G.omegaMask E := by
  classical
  unfold GeometrySymbol.omegaMask
  apply le_foldl_min
  · rw [hG]
    exact QStab.Paper.AlignedBarrier.omegaGroup_le_of_witness spec E
      (maskStabilizerProduct_inStab spec.params (fun _ => false))
  · intro mask _hmask
    rw [hG]
    exact QStab.Paper.AlignedBarrier.omegaGroup_le_of_witness spec E
      (maskStabilizerProduct_inStab spec.params mask)

theorem GeometrySymbol.omegaMask_le_omegaGroup_of_groups {d : Nat}
    (spec : AlignedCodeSpec d) (G : GeometrySymbol spec.params d)
    (hG : forall S E, G.groupsX S E = QStab.Paper.AlignedBarrier.groupsX spec S E)
    (E : ErrorVec spec.params.n) :
    G.omegaMask E <= QStab.Paper.AlignedBarrier.omegaGroup spec E := by
  obtain ⟨S, hS, hOmega⟩ := QStab.Paper.AlignedBarrier.omegaGroup_attained spec E
  obtain ⟨mask, hmask⟩ := inStab_exists_maskStabilizerProduct spec.params hS
  calc
    G.omegaMask E <= G.groupsX (maskStabilizerProduct spec.params mask) E :=
      GeometrySymbol.omegaMask_le_mask G E mask
    _ = G.groupsX S E := by rw [hmask]
    _ = QStab.Paper.AlignedBarrier.groupsX spec S E := hG S E
    _ = QStab.Paper.AlignedBarrier.omegaGroup spec E := hOmega

theorem GeometrySymbol.omegaMask_eq_omegaGroup_of_groups {d : Nat}
    (spec : AlignedCodeSpec d) (G : GeometrySymbol spec.params d)
    (hG : forall S E, G.groupsX S E = QStab.Paper.AlignedBarrier.groupsX spec S E)
    (E : ErrorVec spec.params.n) :
    G.omegaMask E = QStab.Paper.AlignedBarrier.omegaGroup spec E :=
  Nat.le_antisymm
    (GeometrySymbol.omegaMask_le_omegaGroup_of_groups spec G hG E)
    (GeometrySymbol.omegaGroup_le_omegaMask_of_groups spec G hG E)

/-- The finite syntactic aligned-spread minimisation agrees with the generic
    semantic aligned barrier minimisation. -/
theorem GeometrySymbol.omegaMask_ofAlignedCodeSpec {d : Nat}
    (name : String) (spec : AlignedCodeSpec d) (E : ErrorVec spec.params.n) :
    (GeometrySymbol.ofAlignedCodeSpec name spec).omegaMask E =
      QStab.Paper.AlignedBarrier.omegaGroup spec E :=
  GeometrySymbol.omegaMask_eq_omegaGroup_of_groups spec
    (GeometrySymbol.ofAlignedCodeSpec name spec)
    (GeometrySymbol.groupsX_ofAlignedCodeSpec name spec) E

/-- Build an aligned-code barrier directly from finite assertion syntax. -/
def BarrierSymbol.ofAlignedCodeSpec {d : Nat}
    (betaName geomName : String) (spec : AlignedCodeSpec d) :
    BarrierSymbol spec.params :=
  BarrierSymbol.ofAlignedSpread betaName (GeometrySymbol.ofAlignedCodeSpec geomName spec)

@[simp] theorem AlignedCodeData.barrier_ofAlignedCodeSpec {d : Nat}
    (codeName geomName betaName : String) (spec : AlignedCodeSpec d) :
    (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec).barrier betaName =
      BarrierSymbol.ofAlignedCodeSpec betaName geomName spec := by
  rfl

theorem BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier {d : Nat}
    (betaName geomName : String) (spec : AlignedCodeSpec d)
    (E : ErrorVec spec.params.n) :
    (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec).eval E =
      (QStab.Paper.AlignedBarrier.alignedBarrier spec).mu E := by
  unfold BarrierSymbol.ofAlignedCodeSpec BarrierSymbol.eval BarrierSymbol.ofAlignedSpread
    BarrierBody.eval QStab.Paper.AlignedBarrier.alignedBarrier
  simp [GeometrySymbol.omegaMask_ofAlignedCodeSpec]

/-! ## Checked aligned-code formula certificates

The next layer rewrites the theorem fields of `AlignedCodeSpec` into explicit
assertion-language obligations.  The checked leaves below are still semantic
evidence, but each one is tied to one fixed formula.  The following
`SyntacticAlignedCodeContractCertificate` is the verifier-facing proof syntax:
it has no constructor that accepts an arbitrary closed-formula validity proof.
-/

/-- Checked evidence for the cut/stabilizer equivalence obligation. -/
inductive AlignedCutStabEquivCertificate {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) : Type where
  | checked :
      (forall g : Fin d,
        exists mask : Fin P.numStab -> Bool,
          A.geometry.cut g =
            ErrorVec.mul (maskStabilizerProduct P mask) A.logicalZ) ->
      AlignedCutStabEquivCertificate A

/-- Checked evidence that each cut is Z on its group and I elsewhere. -/
inductive AlignedCutShapeCertificate {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) : Type where
  | checked :
      (forall (g : Fin d) (q : Fin P.n),
        A.geometry.cut g q =
          if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I) ->
      AlignedCutShapeCertificate A

/-- Checked evidence that the logical-Z representative normalizes stabilizers. -/
inductive AlignedLogicalNormalizerCertificate {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) : Type where
  | checked :
      (forall i : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) A.logicalZ = false) ->
      AlignedLogicalNormalizerCertificate A

/-- Checked evidence that stabilizer generators commute pairwise. -/
inductive AlignedStabilizersCommuteCertificate {P : QECParams} {d : Nat}
    (A : AlignedCodeData P d) : Type where
  | checked :
      (forall i j : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) (P.stabilizers j) = false) ->
      AlignedStabilizersCommuteCertificate A

/-- Checked evidence for the schedule/hook alignment law of the aligned barrier. -/
inductive AlignedHookAlignedCertificate {P : QECParams} {d : Nat}
    (betaName : String) (A : AlignedCodeData P d) : Type where
  | checked :
      (forall (i : Fin P.numStab) (e : ErrorVec P.n),
        e ∈ P.backActionSet i ->
        forall E : ErrorVec P.n,
          (A.barrier betaName).eval E <=
            (A.barrier betaName).eval (ErrorVec.mul e E) + 1) ->
      AlignedHookAlignedCertificate betaName A

namespace AlignedCutStabEquivCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    AlignedCutStabEquivCertificate A -> Nat
  | .checked _ => 1

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedCutStabEquivCertificate A) :
    A.cutStabEquivF.Valid := by
  cases cert with
  | checked h =>
      intro σ g
      obtain ⟨mask, hmask⟩ := h g
      exact ⟨mask, hmask⟩

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedCutStabEquivCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end AlignedCutStabEquivCertificate

namespace AlignedCutShapeCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    AlignedCutShapeCertificate A -> Nat
  | .checked _ => 1

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedCutShapeCertificate A) :
    A.cutShapeF.Valid := by
  cases cert with
  | checked h =>
      intro σ g q
      constructor
      · intro hg
        change A.geometry.cut g q = Pauli.Z
        change A.geometry.groupOf q = some g at hg
        calc
          A.geometry.cut g q =
              (if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I) := h g q
          _ = Pauli.Z := if_pos hg
      · intro hng
        change A.geometry.cut g q = Pauli.I
        change ¬ A.geometry.groupOf q = some g at hng
        calc
          A.geometry.cut g q =
              (if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I) := h g q
          _ = Pauli.I := if_neg hng

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedCutShapeCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end AlignedCutShapeCertificate

namespace AlignedLogicalNormalizerCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    AlignedLogicalNormalizerCertificate A -> Nat
  | .checked _ => 1

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedLogicalNormalizerCertificate A) :
    A.logicalZNormalizerF.Valid := by
  cases cert with
  | checked h =>
      intro σ i
      exact h i

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedLogicalNormalizerCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end AlignedLogicalNormalizerCertificate

namespace AlignedStabilizersCommuteCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    AlignedStabilizersCommuteCertificate A -> Nat
  | .checked _ => 1

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedStabilizersCommuteCertificate A) :
    A.stabilizersCommuteF.Valid := by
  cases cert with
  | checked h =>
      intro σ i j
      exact h j i

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : AlignedStabilizersCommuteCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end AlignedStabilizersCommuteCertificate

namespace AlignedHookAlignedCertificate

def size {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d} :
    AlignedHookAlignedCertificate betaName A -> Nat
  | .checked _ => 1

def sound {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (cert : AlignedHookAlignedCertificate betaName A) :
    (A.hookAlignedF betaName).Valid := by
  cases cert with
  | checked h =>
      intro σ i e he E
      exact h i e he E

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (cert : AlignedHookAlignedCertificate betaName A) :
    cert.size = 1 := by
  cases cert
  rfl

end AlignedHookAlignedCertificate

/-- Formula-proof syntax for the aligned-code fragment. -/
inductive AlignedCodeFormulaCertificate {P : QECParams} : Formula P [] -> Type where
  | cutStabEquiv {d : Nat} (A : AlignedCodeData P d) :
      AlignedCutStabEquivCertificate A ->
      AlignedCodeFormulaCertificate A.cutStabEquivF
  | cutShape {d : Nat} (A : AlignedCodeData P d) :
      AlignedCutShapeCertificate A ->
      AlignedCodeFormulaCertificate A.cutShapeF
  | logicalNormalizer {d : Nat} (A : AlignedCodeData P d) :
      AlignedLogicalNormalizerCertificate A ->
      AlignedCodeFormulaCertificate A.logicalZNormalizerF
  | stabilizersCommute {d : Nat} (A : AlignedCodeData P d) :
      AlignedStabilizersCommuteCertificate A ->
      AlignedCodeFormulaCertificate A.stabilizersCommuteF
  | hookAligned {d : Nat} (betaName : String) (A : AlignedCodeData P d) :
      AlignedHookAlignedCertificate betaName A ->
      AlignedCodeFormulaCertificate (A.hookAlignedF betaName)
  | andIntro {A B : Formula P []} :
      AlignedCodeFormulaCertificate A ->
      AlignedCodeFormulaCertificate B ->
      AlignedCodeFormulaCertificate (.and A B)

namespace AlignedCodeFormulaCertificate

def size {P : QECParams} {F : Formula P []} :
    AlignedCodeFormulaCertificate (P := P) F -> Nat
  | .cutStabEquiv _ cert => cert.size
  | .cutShape _ cert => cert.size
  | .logicalNormalizer _ cert => cert.size
  | .stabilizersCommute _ cert => cert.size
  | .hookAligned _ _ cert => cert.size
  | .andIntro hA hB => 1 + hA.size + hB.size

def sound {P : QECParams} {F : Formula P []}
    (cert : AlignedCodeFormulaCertificate (P := P) F) : F.Valid := by
  induction cert with
  | cutStabEquiv A cert => exact cert.sound
  | cutShape A cert => exact cert.sound
  | logicalNormalizer A cert => exact cert.sound
  | stabilizersCommute A cert => exact cert.sound
  | hookAligned betaName A cert => exact cert.sound
  | andIntro hA hB ihA ihB =>
      intro σ
      exact ⟨ihA σ, ihB σ⟩

end AlignedCodeFormulaCertificate

/-- Full aligned-code contract as five verifier-known formula leaves. -/
structure AlignedCodeContractCertificate {P : QECParams} {d : Nat}
    (betaName : String) (A : AlignedCodeData P d) : Type where
  cutStabEquiv : AlignedCutStabEquivCertificate A
  cutShape : AlignedCutShapeCertificate A
  logicalNormalizer : AlignedLogicalNormalizerCertificate A
  stabilizersCommute : AlignedStabilizersCommuteCertificate A
  hookAligned : AlignedHookAlignedCertificate betaName A

namespace AlignedCodeContractCertificate

def size {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : AlignedCodeContractCertificate betaName A) : Nat :=
  1 + contract.cutStabEquiv.size + contract.cutShape.size +
    contract.logicalNormalizer.size + contract.stabilizersCommute.size +
    contract.hookAligned.size

theorem size_eq_six {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : AlignedCodeContractCertificate betaName A) :
    contract.size = 6 := by
  cases contract with
  | mk cutStabEquiv cutShape logicalNormalizer stabilizersCommute hookAligned =>
      cases cutStabEquiv
      cases cutShape
      cases logicalNormalizer
      cases stabilizersCommute
      cases hookAligned
      rfl

def formulaCertificate {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : AlignedCodeContractCertificate betaName A) :
    AlignedCodeFormulaCertificate (A.contractF betaName) :=
  .andIntro (.cutStabEquiv A contract.cutStabEquiv)
    (.andIntro (.cutShape A contract.cutShape)
      (.andIntro (.logicalNormalizer A contract.logicalNormalizer)
        (.andIntro (.stabilizersCommute A contract.stabilizersCommute)
          (.hookAligned betaName A contract.hookAligned))))

def sound {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : AlignedCodeContractCertificate betaName A) :
    (A.contractF betaName).Valid :=
  contract.formulaCertificate.sound

theorem formulaCertificate_size_eq_nine {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (contract : AlignedCodeContractCertificate betaName A) :
    contract.formulaCertificate.size = 9 := by
  simp [formulaCertificate, AlignedCodeFormulaCertificate.size]

end AlignedCodeContractCertificate

/-! ## Syntactic aligned-code certificates

The compatibility constructor below consumes a legacy `AlignedCodeSpec`, but
the object it builds is a proof of the five assertion-language formulas over
`AlignedCodeData`.  This lets the golden path check the formula interface now,
while future recursive-code frontends can add constructors that do not mention
`AlignedCodeSpec`.
-/

inductive SyntacticAlignedCutStabEquivCertificate :
    {P : QECParams} -> {d : Nat} -> AlignedCodeData P d -> Type where
  | ofAlignedCodeSpec {d : Nat}
      (codeName geomName : String) (spec : AlignedCodeSpec d) :
      SyntacticAlignedCutStabEquivCertificate
        (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec)

inductive SyntacticAlignedCutShapeCertificate :
    {P : QECParams} -> {d : Nat} -> AlignedCodeData P d -> Type where
  | ofAlignedCodeSpec {d : Nat}
      (codeName geomName : String) (spec : AlignedCodeSpec d) :
      SyntacticAlignedCutShapeCertificate
        (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec)

inductive SyntacticAlignedLogicalNormalizerCertificate :
    {P : QECParams} -> {d : Nat} -> AlignedCodeData P d -> Type where
  | ofAlignedCodeSpec {d : Nat}
      (codeName geomName : String) (spec : AlignedCodeSpec d) :
      SyntacticAlignedLogicalNormalizerCertificate
        (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec)

inductive SyntacticAlignedStabilizersCommuteCertificate :
    {P : QECParams} -> {d : Nat} -> AlignedCodeData P d -> Type where
  | ofAlignedCodeSpec {d : Nat}
      (codeName geomName : String) (spec : AlignedCodeSpec d) :
      SyntacticAlignedStabilizersCommuteCertificate
        (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec)

inductive SyntacticAlignedHookAlignedCertificate (betaName : String) :
    {P : QECParams} -> {d : Nat} -> AlignedCodeData P d -> Type where
  | ofAlignedCodeSpec {d : Nat}
      (codeName geomName : String) (spec : AlignedCodeSpec d) :
      SyntacticAlignedHookAlignedCertificate betaName
        (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec)

namespace SyntacticAlignedCutStabEquivCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    SyntacticAlignedCutStabEquivCertificate A -> Nat
  | .ofAlignedCodeSpec _ _ _ => 1

noncomputable def toChecked {P : QECParams} {d : Nat}
    {A : AlignedCodeData P d} :
    SyntacticAlignedCutStabEquivCertificate A ->
      AlignedCutStabEquivCertificate A
  | .ofAlignedCodeSpec codeName geomName spec =>
      .checked (by
        intro g
        obtain ⟨S, hS, hcut⟩ := spec.cutOp_stabEquiv g
        obtain ⟨mask, hmask⟩ := inStab_exists_maskStabilizerProduct spec.params hS
        refine ⟨mask, ?_⟩
        rw [hmask]
        exact hcut)

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedCutStabEquivCertificate A) :
    A.cutStabEquivF.Valid :=
  cert.toChecked.sound

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedCutStabEquivCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end SyntacticAlignedCutStabEquivCertificate

namespace SyntacticAlignedCutShapeCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    SyntacticAlignedCutShapeCertificate A -> Nat
  | .ofAlignedCodeSpec _ _ _ => 1

noncomputable def toChecked {P : QECParams} {d : Nat}
    {A : AlignedCodeData P d} :
    SyntacticAlignedCutShapeCertificate A ->
      AlignedCutShapeCertificate A
  | .ofAlignedCodeSpec codeName geomName spec =>
      .checked (by
        intro g q
        exact spec.cutOp_spec g q)

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedCutShapeCertificate A) :
    A.cutShapeF.Valid :=
  cert.toChecked.sound

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedCutShapeCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end SyntacticAlignedCutShapeCertificate

namespace SyntacticAlignedLogicalNormalizerCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    SyntacticAlignedLogicalNormalizerCertificate A -> Nat
  | .ofAlignedCodeSpec _ _ _ => 1

noncomputable def toChecked {P : QECParams} {d : Nat}
    {A : AlignedCodeData P d} :
    SyntacticAlignedLogicalNormalizerCertificate A ->
      AlignedLogicalNormalizerCertificate A
  | .ofAlignedCodeSpec codeName geomName spec =>
      .checked (by
        intro i
        exact spec.logicalZ_normalizer i)

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedLogicalNormalizerCertificate A) :
    A.logicalZNormalizerF.Valid :=
  cert.toChecked.sound

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedLogicalNormalizerCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end SyntacticAlignedLogicalNormalizerCertificate

namespace SyntacticAlignedStabilizersCommuteCertificate

def size {P : QECParams} {d : Nat} {A : AlignedCodeData P d} :
    SyntacticAlignedStabilizersCommuteCertificate A -> Nat
  | .ofAlignedCodeSpec _ _ _ => 1

noncomputable def toChecked {P : QECParams} {d : Nat}
    {A : AlignedCodeData P d} :
    SyntacticAlignedStabilizersCommuteCertificate A ->
      AlignedStabilizersCommuteCertificate A
  | .ofAlignedCodeSpec codeName geomName spec =>
      .checked (by
        intro i j
        exact spec.stab_commute i j)

def sound {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedStabilizersCommuteCertificate A) :
    A.stabilizersCommuteF.Valid :=
  cert.toChecked.sound

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {A : AlignedCodeData P d}
    (cert : SyntacticAlignedStabilizersCommuteCertificate A) :
    cert.size = 1 := by
  cases cert
  rfl

end SyntacticAlignedStabilizersCommuteCertificate

namespace SyntacticAlignedHookAlignedCertificate

def size {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d} :
    SyntacticAlignedHookAlignedCertificate betaName A -> Nat
  | .ofAlignedCodeSpec _ _ _ => 1

noncomputable def toChecked {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d} :
    SyntacticAlignedHookAlignedCertificate betaName A ->
      AlignedHookAlignedCertificate betaName A
  | .ofAlignedCodeSpec codeName geomName spec =>
      .checked (by
        intro i e he E
        change (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec).eval E <=
          (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec).eval
            (ErrorVec.mul e E) + 1
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        exact QStab.Paper.AlignedBarrier.aligned_isLAligned spec i e he E)

def sound {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (cert : SyntacticAlignedHookAlignedCertificate betaName A) :
    (A.hookAlignedF betaName).Valid :=
  cert.toChecked.sound

@[simp] theorem size_eq_one {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (cert : SyntacticAlignedHookAlignedCertificate betaName A) :
    cert.size = 1 := by
  cases cert
  rfl

end SyntacticAlignedHookAlignedCertificate

structure SyntacticAlignedCodeContractCertificate {P : QECParams} {d : Nat}
    (betaName : String) (A : AlignedCodeData P d) : Type where
  cutStabEquiv : SyntacticAlignedCutStabEquivCertificate A
  cutShape : SyntacticAlignedCutShapeCertificate A
  logicalNormalizer : SyntacticAlignedLogicalNormalizerCertificate A
  stabilizersCommute : SyntacticAlignedStabilizersCommuteCertificate A
  hookAligned : SyntacticAlignedHookAlignedCertificate betaName A

namespace SyntacticAlignedCodeContractCertificate

def size {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : SyntacticAlignedCodeContractCertificate betaName A) : Nat :=
  1 + contract.cutStabEquiv.size + contract.cutShape.size +
    contract.logicalNormalizer.size + contract.stabilizersCommute.size +
    contract.hookAligned.size

theorem size_eq_six {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : SyntacticAlignedCodeContractCertificate betaName A) :
    contract.size = 6 := by
  simp [size]

noncomputable def toChecked {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : SyntacticAlignedCodeContractCertificate betaName A) :
    AlignedCodeContractCertificate betaName A where
  cutStabEquiv := contract.cutStabEquiv.toChecked
  cutShape := contract.cutShape.toChecked
  logicalNormalizer := contract.logicalNormalizer.toChecked
  stabilizersCommute := contract.stabilizersCommute.toChecked
  hookAligned := contract.hookAligned.toChecked

noncomputable def formulaCertificate {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : SyntacticAlignedCodeContractCertificate betaName A) :
    AlignedCodeFormulaCertificate (A.contractF betaName) :=
  contract.toChecked.formulaCertificate

noncomputable def sound {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (contract : SyntacticAlignedCodeContractCertificate betaName A) :
    (A.contractF betaName).Valid :=
  contract.formulaCertificate.sound

theorem formulaCertificate_size_eq_nine {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (contract : SyntacticAlignedCodeContractCertificate betaName A) :
    contract.formulaCertificate.size = 9 := by
  exact AlignedCodeContractCertificate.formulaCertificate_size_eq_nine contract.toChecked

noncomputable def ofAlignedCodeSpec {d : Nat}
    (codeName geomName betaName : String) (spec : AlignedCodeSpec d) :
    SyntacticAlignedCodeContractCertificate betaName
      (AlignedCodeData.ofAlignedCodeSpec codeName geomName spec) where
  cutStabEquiv := .ofAlignedCodeSpec codeName geomName spec
  cutShape := .ofAlignedCodeSpec codeName geomName spec
  logicalNormalizer := .ofAlignedCodeSpec codeName geomName spec
  stabilizersCommute := .ofAlignedCodeSpec codeName geomName spec
  hookAligned := .ofAlignedCodeSpec codeName geomName spec

end SyntacticAlignedCodeContractCertificate

/-- User-facing synonym for the aligned-code assertion proof derivation.
    It is definitionally equal to the historical `Syntactic...Certificate`
    name, but the intended object is a derivation tree in the assertion
    language: five fixed leaves plus conjunction assembly. -/
abbrev AlignedCodeContractDerivation {P : QECParams} {d : Nat}
    (betaName : String) (A : AlignedCodeData P d) : Type :=
  SyntacticAlignedCodeContractCertificate betaName A

namespace AlignedCodeContractDerivation

def size {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (D : AlignedCodeContractDerivation betaName A) : Nat :=
  SyntacticAlignedCodeContractCertificate.size D

/-- The aligned-code derivation tree has constant shape for every distance.
    The distance may occur inside recursive code data, but not in the number
    of derivation-rule nodes. -/
theorem size_eq_six {P : QECParams} {d : Nat} {betaName : String}
    {A : AlignedCodeData P d}
    (D : AlignedCodeContractDerivation betaName A) :
    D.size = 6 :=
  SyntacticAlignedCodeContractCertificate.size_eq_six D

theorem formulaDerivation_size_eq_nine {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (D : AlignedCodeContractDerivation betaName A) :
    D.formulaCertificate.size = 9 :=
  SyntacticAlignedCodeContractCertificate.formulaCertificate_size_eq_nine D

end AlignedCodeContractDerivation

/-- Bridge from the old mathematical barrier package into the four checked
    barrier-law leaves. New frontends should produce these leaves directly
    from recursive assertion programs instead of through `BarrierFunction`. -/
def BarrierContractCertificate.ofBarrierFunction {P : QECParams} {L : LogicalClass P}
    (betaName logicalName : String)
    (beta : BarrierFunction P L) (h_aligned : IsLAligned beta)
    (parityZero parityOne : List (ErrorVec P.n))
    (h_iff : ∀ E,
      ((∀ S, S ∈ parityZero -> ErrorVec.parity S E = false) ∧
       (∀ T, T ∈ parityOne  -> ErrorVec.parity T E = true)) ↔ L.contains E) :
    BarrierContractCertificate
      (BarrierSymbol.ofBarrier betaName beta)
      (LogicalClassSymbol.ofLogicalClass logicalName L parityZero parityOne h_iff) :=
  let LS := LogicalClassSymbol.ofLogicalClass logicalName L parityZero parityOne h_iff
  { identity := .checked (by
      change beta.mu (ErrorVec.identity P.n) = L.d_L
      exact beta.mu_identity)
    logical := .checked (by
      intro E hE
      have hE' :
          ((forall S, S ∈ parityZero -> ErrorVec.parity S E = false) /\
           (forall T, T ∈ parityOne -> ErrorVec.parity T E = true)) := by
        simpa [LogicalClassSymbol.contains, LS] using hE
      change beta.mu E = 0
      exact beta.mu_at_logical E ((h_iff E).mp hE'))
    triangle := .checked (by
      intro E F
      change beta.mu E <= beta.mu (ErrorVec.mul F E) + ErrorVec.weight F
      exact beta.mu_triangle E F)
    aligned := .checked (by
      intro i e he E
      change beta.mu E <= beta.mu (ErrorVec.mul e E) + 1
      exact h_aligned i e he E) }

/-- Generic aligned-code schema for the four barrier-law leaves.

    This removes the Surface-specific bridge from the parametric path: any
    code family that provides an `AlignedCodeSpec` (Surface, HGP, LDPC-style
    families with a checked aligned decomposition) gets the same constant-size
    assertion-language contract. The remaining body is still the semantic
    `alignedBarrier`; replacing that with `BarrierSymbol.ofAlignedSpread`
    requires a separate finite-mask completeness theorem for `GeometrySymbol`.
-/
noncomputable def BarrierContractCertificate.ofAlignedCodeSpec {d : Nat}
    (betaName logicalName : String) (spec : AlignedCodeSpec d) :
    BarrierContractCertificate
      (BarrierSymbol.ofBarrier betaName
        (QStab.Paper.AlignedBarrier.alignedBarrier spec))
      (LogicalClassSymbol.ofAlignedBarZ logicalName spec) :=
  let beta := QStab.Paper.AlignedBarrier.alignedBarrier spec
  { identity := .checked (by
      change beta.mu (ErrorVec.identity spec.params.n) =
        (QStab.Paper.AlignedBarrier.barZClass spec).d_L
      exact beta.mu_identity)
    logical := .checked (by
      intro E hE
      have hE' : (QStab.Paper.AlignedBarrier.barZClass spec).contains E := by
        exact (alignedBarZ_contains_iff spec E).mp hE
      change beta.mu E = 0
      exact beta.mu_at_logical E hE')
    triangle := .checked (by
      intro E F
      change beta.mu E <= beta.mu (ErrorVec.mul F E) + ErrorVec.weight F
      exact beta.mu_triangle E F)
    aligned := .checked (by
      intro i e he E
      change beta.mu E <= beta.mu (ErrorVec.mul e E) + 1
      exact QStab.Paper.AlignedBarrier.aligned_isLAligned spec i e he E) }

/-- Generic aligned-code schema whose barrier body is the finite recursive
    `alignedSpread` syntax, not an external semantic callback. -/
noncomputable def BarrierContractCertificate.ofAlignedSpreadCodeSpec {d : Nat}
    (betaName geomName logicalName : String) (spec : AlignedCodeSpec d) :
    BarrierContractCertificate
      (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec)
      (LogicalClassSymbol.ofAlignedBarZ logicalName spec) :=
  let beta := QStab.Paper.AlignedBarrier.alignedBarrier spec
  { identity := .checked (by
      rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
      change beta.mu (ErrorVec.identity spec.params.n) =
        (QStab.Paper.AlignedBarrier.barZClass spec).d_L
      exact beta.mu_identity)
    logical := .checked (by
      intro E hE
      have hE' : (QStab.Paper.AlignedBarrier.barZClass spec).contains E := by
        exact (alignedBarZ_contains_iff spec E).mp hE
      rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
      change beta.mu E = 0
      exact beta.mu_at_logical E hE')
    triangle := .checked (by
      intro E F
      rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
      rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
      change beta.mu E <= beta.mu (ErrorVec.mul F E) + ErrorVec.weight F
      exact beta.mu_triangle E F)
    aligned := .checked (by
      intro i e he E
      rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
      rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
      change beta.mu E <= beta.mu (ErrorVec.mul e E) + 1
      exact QStab.Paper.AlignedBarrier.aligned_isLAligned spec i e he E) }

/-! ## Deriving aligned-spread barrier laws from assertion formulas -/

namespace AlignedCodeData

private theorem groupsX_le_distance {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (S E : ErrorVec P.n) :
    G.groupsX S E <= d := by
  classical
  unfold GeometrySymbol.groupsX
  calc
    (Finset.univ.filter fun g : Fin d =>
        exists q : Fin P.n, G.groupOf q = some g /\
          pauliHasXStatic (ErrorVec.mul S E q) = true).card
        <= Finset.univ.card := Finset.card_filter_le _ _
    _ = d := Fintype.card_fin d

private theorem omegaMask_le_distance {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (E : ErrorVec P.n) :
    G.omegaMask E <= d :=
  Nat.le_trans
    (GeometrySymbol.omegaMask_le_mask G E (fun _ => false))
    (groupsX_le_distance G (maskStabilizerProduct P (fun _ => false)) E)

private theorem foldl_min_attained_or_init {α : Type} (f : α -> Nat) :
    forall (xs : List α) (init : Nat),
      (exists x, x ∈ xs /\ xs.foldl (fun best a => Nat.min best (f a)) init = f x) \/
        xs.foldl (fun best a => Nat.min best (f a)) init = init
  | [], init => Or.inr rfl
  | x :: xs, init => by
      have ih := foldl_min_attained_or_init f xs (Nat.min init (f x))
      rcases ih with ⟨y, hy, hfold⟩ | hfold
      · exact Or.inl ⟨y, List.mem_cons_of_mem x hy, by simpa [List.foldl] using hfold⟩
      · by_cases hle : init <= f x
        · right
          simpa [List.foldl, Nat.min_eq_left hle] using hfold
        · left
          have hx : Nat.min init (f x) = f x := by
            exact Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hle))
          refine ⟨x, ?_, ?_⟩
          · simp
          · simpa [List.foldl, hx] using hfold

private theorem omegaMask_attained {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (E : ErrorVec P.n) :
    exists mask : Fin P.numStab -> Bool,
      G.omegaMask E = G.groupsX (maskStabilizerProduct P mask) E := by
  classical
  let f : (Fin P.numStab -> Bool) -> Nat :=
    fun mask => G.groupsX (maskStabilizerProduct P mask) E
  let init := f (fun _ => false)
  have h := foldl_min_attained_or_init f (allStabMasks P) init
  rcases h with ⟨mask, _hmem, hmask⟩ | hinit
  · exact ⟨mask, by simpa [GeometrySymbol.omegaMask, f, init] using hmask⟩
  · exact ⟨fun _ => false, by simpa [GeometrySymbol.omegaMask, f, init] using hinit⟩

private theorem omega_le_of_barrier_aligned {d omegaE omegaEF : Nat}
    (hE : omegaE <= d) (hEF : omegaEF <= d)
    (h : d - omegaE <= d - omegaEF + 1) :
    omegaEF <= omegaE + 1 := by
  omega

private theorem barrier_aligned_of_omega_le {d omegaE omegaEF : Nat}
    (hE : omegaE <= d) (hEF : omegaEF <= d)
    (h : omegaEF <= omegaE + 1) :
    d - omegaE <= d - omegaEF + 1 := by
  omega

private theorem cutStabEquiv_of_contract_valid {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (hContract : (A.contractF betaName).Valid) :
    forall g : Fin d,
      exists S : ErrorVec P.n, InStab P S /\
        A.geometry.cut g = ErrorVec.mul S A.logicalZ := by
  intro g
  have hCut : A.cutStabEquivF.Valid := by
    intro σ
    exact (hContract σ).1
  obtain ⟨mask, hmask⟩ := hCut (State.init P) g
  exact ⟨maskStabilizerProduct P mask, maskStabilizerProduct_inStab P mask, hmask⟩

private theorem cutShape_of_contract_valid {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (hContract : (A.contractF betaName).Valid) :
    forall (g : Fin d) (q : Fin P.n),
      A.geometry.cut g q = if A.geometry.groupOf q = some g then Pauli.Z else Pauli.I := by
  intro g q
  have hShape : A.cutShapeF.Valid := by
    intro σ
    exact (hContract σ).2.1
  have hq := hShape (State.init P) g q
  by_cases hg : A.geometry.groupOf q = some g
  · simpa [hg] using hq.1 hg
  · simpa [hg] using hq.2 hg

private theorem logicalNormalizer_of_contract_valid {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (hContract : (A.contractF betaName).Valid) :
    forall i : Fin P.numStab,
      ErrorVec.parity (P.stabilizers i) A.logicalZ = false := by
  intro i
  have hNorm : A.logicalZNormalizerF.Valid := by
    intro σ
    exact (hContract σ).2.2.1
  exact hNorm (State.init P) i

private theorem stabilizersCommute_of_contract_valid {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (hContract : (A.contractF betaName).Valid) :
    forall i j : Fin P.numStab,
      ErrorVec.parity (P.stabilizers i) (P.stabilizers j) = false := by
  intro i j
  have hComm : A.stabilizersCommuteF.Valid := by
    intro σ
    exact (hContract σ).2.2.2.1
  exact hComm (State.init P) j i

private theorem hookSpreadBound_of_contract_valid {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (hContract : (A.contractF betaName).Valid) :
    forall (s_idx : Fin P.numStab) (e_B : ErrorVec P.n),
      e_B ∈ P.backActionSet s_idx ->
      forall (E : ErrorVec P.n) (S_wit : ErrorVec P.n),
        InStab P S_wit ->
        exists S_wit' : ErrorVec P.n, InStab P S_wit' /\
          (Finset.univ.filter fun g : Fin d =>
            exists q : Fin P.n, A.geometry.groupOf q = some g /\
              Pauli.hasXComponent (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
          <=
          (Finset.univ.filter fun g : Fin d =>
            exists q : Fin P.n, A.geometry.groupOf q = some g /\
              Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  intro s_idx e_B he E S_wit hS
  have hAligned : (A.hookAlignedF betaName).Valid := by
    intro σ
    exact (hContract σ).2.2.2.2
  have hLaw := hAligned (State.init P) s_idx e_B he E
  obtain ⟨maskE, hmaskE⟩ := inStab_exists_maskStabilizerProduct P hS
  have hOmegaE :
      A.geometry.omegaMask E <= A.geometry.groupsX S_wit E := by
    calc
      A.geometry.omegaMask E
          <= A.geometry.groupsX (maskStabilizerProduct P maskE) E :=
            GeometrySymbol.omegaMask_le_mask A.geometry E maskE
      _ = A.geometry.groupsX S_wit E := by rw [hmaskE]
  obtain ⟨maskEF, hmaskEF⟩ := omegaMask_attained A.geometry (ErrorVec.mul e_B E)
  refine ⟨maskStabilizerProduct P maskEF, maskStabilizerProduct_inStab P maskEF, ?_⟩
  have hOmegaStep :
      A.geometry.omegaMask (ErrorVec.mul e_B E) <= A.geometry.omegaMask E + 1 := by
    exact omega_le_of_barrier_aligned
      (omegaMask_le_distance A.geometry E)
      (omegaMask_le_distance A.geometry (ErrorVec.mul e_B E))
      hLaw
  change A.geometry.groupsX (maskStabilizerProduct P maskEF) (ErrorVec.mul e_B E) <=
    A.geometry.groupsX S_wit E + 1
  rw [← hmaskEF]
  omega

/-- A schedule-level hook-spread bound directly proves the assertion-language
    hook-alignment formula for the finite aligned-spread barrier.  This is the
    reusable symbolic bridge used by Surface/NZ and intended for future LDPC
    families; it does not route through `AlignedCodeSpec` or `BarrierFunction`.
-/
theorem hookAlignedF_valid_of_hookSpreadBound {P : QECParams} {d : Nat}
    {betaName : String} {A : AlignedCodeData P d}
    (hHook :
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
                Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1) :
    (A.hookAlignedF betaName).Valid := by
  intro σ s_idx e_B he E
  change (A.barrier betaName).eval E <=
    (A.barrier betaName).eval (ErrorVec.mul e_B E) + 1
  unfold AlignedCodeData.barrier BarrierSymbol.ofAlignedSpread BarrierSymbol.eval
    BarrierBody.eval
  obtain ⟨maskE, hmaskE⟩ := omegaMask_attained A.geometry E
  let S_wit := maskStabilizerProduct P maskE
  have hS : InStab P S_wit := maskStabilizerProduct_inStab P maskE
  obtain ⟨S_wit', hS', hbound⟩ := hHook s_idx e_B he E S_wit hS
  obtain ⟨maskEF, hmaskEF⟩ := inStab_exists_maskStabilizerProduct P hS'
  have hOmegaStep :
      A.geometry.omegaMask (ErrorVec.mul e_B E) <= A.geometry.omegaMask E + 1 := by
    calc
      A.geometry.omegaMask (ErrorVec.mul e_B E)
          <= A.geometry.groupsX (maskStabilizerProduct P maskEF)
              (ErrorVec.mul e_B E) :=
            GeometrySymbol.omegaMask_le_mask A.geometry (ErrorVec.mul e_B E) maskEF
      _ = A.geometry.groupsX S_wit' (ErrorVec.mul e_B E) := by rw [hmaskEF]
      _ <= A.geometry.groupsX S_wit E + 1 := hbound
      _ = A.geometry.omegaMask E + 1 := by rw [← hmaskE]
  exact barrier_aligned_of_omega_le
    (omegaMask_le_distance A.geometry E)
    (omegaMask_le_distance A.geometry (ErrorVec.mul e_B E))
    hOmegaStep

noncomputable def toAlignedCodeSpecOfContractValid {P : QECParams} {d : Nat}
    (hd : 0 < d) (betaName : String) (A : AlignedCodeData P d)
    (hContract : (A.contractF betaName).Valid) : AlignedCodeSpec d where
  params := P
  hd_pos := hd
  logicalZ := A.logicalZ
  group := A.geometry.groupOf
  cutOp := A.geometry.cut
  cutOp_stabEquiv := cutStabEquiv_of_contract_valid hContract
  cutOp_spec := cutShape_of_contract_valid hContract
  logicalZ_normalizer := logicalNormalizer_of_contract_valid hContract
  stab_commute := stabilizersCommute_of_contract_valid hContract
  hook_spread_bound := hookSpreadBound_of_contract_valid hContract

private theorem barrier_eq_toAlignedCodeSpecOfContractValid {P : QECParams} {d : Nat}
    (hd : 0 < d) (betaName : String) (A : AlignedCodeData P d)
    (hContract : (A.contractF betaName).Valid) :
    A.barrier betaName =
      BarrierSymbol.ofAlignedCodeSpec betaName A.geometry.name
        (toAlignedCodeSpecOfContractValid hd betaName A hContract) := by
  cases A with
  | mk name logicalZ geometry =>
      cases geometry
      rfl

private theorem logicalClass_eq_toAlignedCodeSpecOfContractValid {P : QECParams} {d : Nat}
    (hd : 0 < d) (betaName logicalName : String) (A : AlignedCodeData P d)
    (hContract : (A.contractF betaName).Valid) :
    A.logicalClass logicalName =
      LogicalClassSymbol.ofAlignedBarZ logicalName
        (toAlignedCodeSpecOfContractValid hd betaName A hContract) := by
  cases A with
  | mk name logicalZ geometry =>
      cases geometry
      rfl

noncomputable def barrierContractCertificateOfContractValid {P : QECParams} {d : Nat}
    (hd : 0 < d) (betaName logicalName : String) (A : AlignedCodeData P d)
    (hContract : (A.contractF betaName).Valid) :
    BarrierContractCertificate (A.barrier betaName) (A.logicalClass logicalName) := by
  let specA := toAlignedCodeSpecOfContractValid hd betaName A hContract
  have hβ :
      A.barrier betaName = BarrierSymbol.ofAlignedCodeSpec betaName A.geometry.name specA :=
    barrier_eq_toAlignedCodeSpecOfContractValid hd betaName A hContract
  have hL :
      A.logicalClass logicalName = LogicalClassSymbol.ofAlignedBarZ logicalName specA :=
    logicalClass_eq_toAlignedCodeSpecOfContractValid hd betaName logicalName A hContract
  rw [hβ, hL]
  exact BarrierContractCertificate.ofAlignedSpreadCodeSpec betaName A.geometry.name logicalName specA

theorem barrierContractF_valid_of_alignedContractF_valid {P : QECParams} {d : Nat}
    (hd : 0 < d) (betaName logicalName : String) (A : AlignedCodeData P d)
    (hContract : (A.contractF betaName).Valid) :
    (barrierContractF (A.barrier betaName) (A.logicalClass logicalName)).Valid :=
  (barrierContractCertificateOfContractValid hd betaName logicalName A hContract).sound

end AlignedCodeData

/-! ## Syntactic barrier-contract certificates

The legacy `BarrierContractCertificate` stores four semantic proof leaves.  The
new certificate layer below stores only assertion-language proof constructors.
Its `toChecked` compiler is part of the trusted verifier implementation: users
provide syntax, while Lean proves once that every accepted constructor denotes a
valid barrier law.
-/

/-- Syntactic proof of the identity law for a recognised barrier schema. -/
inductive SyntacticBarrierIdentityCertificate :
    {P : QECParams} -> BarrierSymbol P -> LogicalClassSymbol P -> Type where
  | alignedSpreadCodeSpec {d : Nat}
      (betaName geomName logicalName : String) (spec : AlignedCodeSpec d) :
      SyntacticBarrierIdentityCertificate
        (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec)
        (LogicalClassSymbol.ofAlignedBarZ logicalName spec)

/-- Syntactic proof of the logical-class zero law. -/
inductive SyntacticBarrierLogicalCertificate :
    {P : QECParams} -> BarrierSymbol P -> LogicalClassSymbol P -> Type where
  | alignedSpreadCodeSpec {d : Nat}
      (betaName geomName logicalName : String) (spec : AlignedCodeSpec d) :
      SyntacticBarrierLogicalCertificate
        (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec)
        (LogicalClassSymbol.ofAlignedBarZ logicalName spec)

/-- Syntactic proof of the triangle law. -/
inductive SyntacticBarrierTriangleCertificate :
    {P : QECParams} -> BarrierSymbol P -> Type where
  | alignedSpreadCodeSpec {d : Nat}
      (betaName geomName : String) (spec : AlignedCodeSpec d) :
      SyntacticBarrierTriangleCertificate
        (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec)

/-- Syntactic proof of the schedule-alignment law. -/
inductive SyntacticBarrierAlignedCertificate :
    {P : QECParams} -> BarrierSymbol P -> Type where
  | alignedSpreadCodeSpec {d : Nat}
      (betaName geomName : String) (spec : AlignedCodeSpec d) :
      SyntacticBarrierAlignedCertificate
        (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec)

namespace SyntacticBarrierIdentityCertificate

def size {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    SyntacticBarrierIdentityCertificate beta L -> Nat
  | .alignedSpreadCodeSpec _ _ _ _ => 1

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P}
    {L : LogicalClassSymbol P}
    (cert : SyntacticBarrierIdentityCertificate beta L) :
    cert.size = 1 := by
  cases cert
  rfl

noncomputable def toChecked {P : QECParams}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    SyntacticBarrierIdentityCertificate beta L ->
      BarrierIdentityCertificate beta L
  | .alignedSpreadCodeSpec betaName geomName logicalName spec =>
      .checked (by
        let beta := QStab.Paper.AlignedBarrier.alignedBarrier spec
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        change beta.mu (ErrorVec.identity spec.params.n) =
          (QStab.Paper.AlignedBarrier.barZClass spec).d_L
        exact beta.mu_identity)

def sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (cert : SyntacticBarrierIdentityCertificate beta L) :
    beta.eval (ErrorVec.identity P.n) = L.distance :=
  cert.toChecked.sound

end SyntacticBarrierIdentityCertificate

namespace SyntacticBarrierLogicalCertificate

def size {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    SyntacticBarrierLogicalCertificate beta L -> Nat
  | .alignedSpreadCodeSpec _ _ _ _ => 1

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P}
    {L : LogicalClassSymbol P}
    (cert : SyntacticBarrierLogicalCertificate beta L) :
    cert.size = 1 := by
  cases cert
  rfl

noncomputable def toChecked {P : QECParams}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P} :
    SyntacticBarrierLogicalCertificate beta L ->
      BarrierLogicalCertificate beta L
  | .alignedSpreadCodeSpec betaName geomName logicalName spec =>
      .checked (by
        intro E hE
        let beta := QStab.Paper.AlignedBarrier.alignedBarrier spec
        have hE' : (QStab.Paper.AlignedBarrier.barZClass spec).contains E := by
          exact (alignedBarZ_contains_iff spec E).mp hE
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        change beta.mu E = 0
        exact beta.mu_at_logical E hE')

def sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (cert : SyntacticBarrierLogicalCertificate beta L) :
    forall E : ErrorVec P.n, L.contains E -> beta.eval E = 0 :=
  cert.toChecked.sound

end SyntacticBarrierLogicalCertificate

namespace SyntacticBarrierTriangleCertificate

def size {P : QECParams} {beta : BarrierSymbol P} :
    SyntacticBarrierTriangleCertificate beta -> Nat
  | .alignedSpreadCodeSpec _ _ _ => 1

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P}
    (cert : SyntacticBarrierTriangleCertificate beta) :
    cert.size = 1 := by
  cases cert
  rfl

noncomputable def toChecked {P : QECParams} {beta : BarrierSymbol P} :
    SyntacticBarrierTriangleCertificate beta -> BarrierTriangleCertificate beta
  | .alignedSpreadCodeSpec betaName geomName spec =>
      .checked (by
        intro E F
        let beta := QStab.Paper.AlignedBarrier.alignedBarrier spec
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        change beta.mu E <= beta.mu (ErrorVec.mul F E) + ErrorVec.weight F
        exact beta.mu_triangle E F)

def sound {P : QECParams} {beta : BarrierSymbol P}
    (cert : SyntacticBarrierTriangleCertificate beta) :
    forall E F : ErrorVec P.n,
      beta.eval E <= beta.eval (ErrorVec.mul F E) + ErrorVec.weight F :=
  cert.toChecked.sound

end SyntacticBarrierTriangleCertificate

namespace SyntacticBarrierAlignedCertificate

def size {P : QECParams} {beta : BarrierSymbol P} :
    SyntacticBarrierAlignedCertificate beta -> Nat
  | .alignedSpreadCodeSpec _ _ _ => 1

@[simp] theorem size_eq_one {P : QECParams} {beta : BarrierSymbol P}
    (cert : SyntacticBarrierAlignedCertificate beta) :
    cert.size = 1 := by
  cases cert
  rfl

noncomputable def toChecked {P : QECParams} {beta : BarrierSymbol P} :
    SyntacticBarrierAlignedCertificate beta -> BarrierAlignedCertificate beta
  | .alignedSpreadCodeSpec betaName geomName spec =>
      .checked (by
        intro i e he E
        let beta := QStab.Paper.AlignedBarrier.alignedBarrier spec
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
        change beta.mu E <= beta.mu (ErrorVec.mul e E) + 1
        exact QStab.Paper.AlignedBarrier.aligned_isLAligned spec i e he E)

def sound {P : QECParams} {beta : BarrierSymbol P}
    (cert : SyntacticBarrierAlignedCertificate beta) :
    forall (i : Fin P.numStab) (e : ErrorVec P.n),
      e ∈ P.backActionSet i ->
      forall E : ErrorVec P.n,
        beta.eval E <= beta.eval (ErrorVec.mul e E) + 1 :=
  cert.toChecked.sound

end SyntacticBarrierAlignedCertificate

/-- Formula-proof syntax for the recognised barrier-contract fragment. -/
inductive SyntacticBarrierFormulaCertificate {P : QECParams} : Formula P [] -> Type where
  | barrierIdentity (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
      SyntacticBarrierIdentityCertificate beta L ->
      SyntacticBarrierFormulaCertificate (barrierIdentityF beta L)
  | barrierLogical (beta : BarrierSymbol P) (L : LogicalClassSymbol P) :
      SyntacticBarrierLogicalCertificate beta L ->
      SyntacticBarrierFormulaCertificate (barrierLogicalF beta L)
  | barrierTriangle (beta : BarrierSymbol P) :
      SyntacticBarrierTriangleCertificate beta ->
      SyntacticBarrierFormulaCertificate (barrierTriangleF beta)
  | barrierAligned (beta : BarrierSymbol P) :
      SyntacticBarrierAlignedCertificate beta ->
      SyntacticBarrierFormulaCertificate (barrierAlignedF beta)
  | andIntro {A B : Formula P []} :
      SyntacticBarrierFormulaCertificate A ->
      SyntacticBarrierFormulaCertificate B ->
      SyntacticBarrierFormulaCertificate (.and A B)

namespace SyntacticBarrierFormulaCertificate

def size {P : QECParams} {A : Formula P []} :
    SyntacticBarrierFormulaCertificate (P := P) A -> Nat
  | .barrierIdentity _ _ cert => cert.size
  | .barrierLogical _ _ cert => cert.size
  | .barrierTriangle _ cert => cert.size
  | .barrierAligned _ cert => cert.size
  | .andIntro hA hB => 1 + hA.size + hB.size

noncomputable def toChecked {P : QECParams} {A : Formula P []} :
    SyntacticBarrierFormulaCertificate (P := P) A ->
      BarrierFormulaCertificate (P := P) A
  | .barrierIdentity beta L cert =>
      .barrierIdentity beta L cert.toChecked
  | .barrierLogical beta L cert =>
      .barrierLogical beta L cert.toChecked
  | .barrierTriangle beta cert =>
      .barrierTriangle beta cert.toChecked
  | .barrierAligned beta cert =>
      .barrierAligned beta cert.toChecked
  | .andIntro hA hB =>
      .andIntro hA.toChecked hB.toChecked

def sound {P : QECParams} {A : Formula P []}
    (cert : SyntacticBarrierFormulaCertificate (P := P) A) : A.Valid :=
  cert.toChecked.sound

end SyntacticBarrierFormulaCertificate

/-- A full barrier contract represented only by verifier-known proof syntax. -/
structure SyntacticBarrierContractCertificate {P : QECParams}
    (beta : BarrierSymbol P) (L : LogicalClassSymbol P) : Type where
  identity : SyntacticBarrierIdentityCertificate beta L
  logical : SyntacticBarrierLogicalCertificate beta L
  triangle : SyntacticBarrierTriangleCertificate beta
  aligned : SyntacticBarrierAlignedCertificate beta

namespace SyntacticBarrierContractCertificate

def size {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) : Nat :=
  1 + contract.identity.size + contract.logical.size +
    contract.triangle.size + contract.aligned.size

theorem size_eq_five {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    contract.size = 5 := by
  simp [size]

def formulaCertificate {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    SyntacticBarrierFormulaCertificate (barrierContractF beta L) :=
  .andIntro (.barrierIdentity beta L contract.identity)
    (.andIntro (.barrierLogical beta L contract.logical)
      (.andIntro (.barrierTriangle beta contract.triangle)
        (.barrierAligned beta contract.aligned)))

noncomputable def toChecked {P : QECParams}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    BarrierContractCertificate beta L where
  identity := contract.identity.toChecked
  logical := contract.logical.toChecked
  triangle := contract.triangle.toChecked
  aligned := contract.aligned.toChecked

def sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    (barrierContractF beta L).Valid :=
  contract.formulaCertificate.sound

theorem formulaCertificate_size_eq_seven {P : QECParams}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    contract.formulaCertificate.size = 7 := by
  simp [formulaCertificate, SyntacticBarrierFormulaCertificate.size]

def identity_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    beta.eval (ErrorVec.identity P.n) = L.distance :=
  contract.identity.sound

def logical_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    forall E : ErrorVec P.n, L.contains E -> beta.eval E = 0 :=
  contract.logical.sound

def triangle_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    forall E F : ErrorVec P.n,
      beta.eval E <= beta.eval (ErrorVec.mul F E) + ErrorVec.weight F :=
  contract.triangle.sound

def aligned_sound {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (contract : SyntacticBarrierContractCertificate beta L) :
    forall (i : Fin P.numStab) (e : ErrorVec P.n),
      e ∈ P.backActionSet i ->
      forall E : ErrorVec P.n,
        beta.eval E <= beta.eval (ErrorVec.mul e E) + 1 :=
  contract.aligned.sound

noncomputable def ofAlignedSpreadCodeSpec {d : Nat}
    (betaName geomName logicalName : String) (spec : AlignedCodeSpec d) :
    SyntacticBarrierContractCertificate
      (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec)
      (LogicalClassSymbol.ofAlignedBarZ logicalName spec) where
  identity := .alignedSpreadCodeSpec betaName geomName logicalName spec
  logical := .alignedSpreadCodeSpec betaName geomName logicalName spec
  triangle := .alignedSpreadCodeSpec betaName geomName spec
  aligned := .alignedSpreadCodeSpec betaName geomName spec

/-- Derive the corresponding aligned-spread barrier contract from an already
    checked aligned-code contract. The current compatibility constructor
    recognizes aligned-code contracts produced from `AlignedCodeSpec`; future
    recursive frontends should add new syntactic aligned-code constructors here
    rather than extending the Hoare logic with code-specific rules. -/
noncomputable def ofAlignedCodeData {P : QECParams} {d : Nat}
    (betaName logicalName : String) (A : AlignedCodeData P d)
    (aligned : SyntacticAlignedCodeContractCertificate betaName A) :
    SyntacticBarrierContractCertificate (A.barrier betaName) (A.logicalClass logicalName) :=
  match aligned.cutStabEquiv with
  | .ofAlignedCodeSpec codeName geomName spec =>
      SyntacticBarrierContractCertificate.ofAlignedSpreadCodeSpec
        betaName geomName logicalName spec

end SyntacticBarrierContractCertificate

/-- User-facing synonym for the barrier-contract assertion proof derivation.
    This is the fixed four-law derivation consumed by the Hoare barrier rule. -/
abbrev BarrierContractDerivation {P : QECParams}
    (beta : BarrierSymbol P) (L : LogicalClassSymbol P) : Type :=
  SyntacticBarrierContractCertificate beta L

namespace BarrierContractDerivation

def size {P : QECParams} {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (D : BarrierContractDerivation beta L) : Nat :=
  SyntacticBarrierContractCertificate.size D

/-- The barrier-contract derivation tree has constant shape for every code
    distance; all distance dependence lives in the symbols named by the leaves. -/
theorem size_eq_five {P : QECParams} {beta : BarrierSymbol P}
    {L : LogicalClassSymbol P}
    (D : BarrierContractDerivation beta L) :
    D.size = 5 :=
  SyntacticBarrierContractCertificate.size_eq_five D

theorem formulaDerivation_size_eq_seven {P : QECParams}
    {beta : BarrierSymbol P} {L : LogicalClassSymbol P}
    (D : BarrierContractDerivation beta L) :
    D.formulaCertificate.size = 7 :=
  SyntacticBarrierContractCertificate.formulaCertificate_size_eq_seven D

end BarrierContractDerivation

end QHL.AssertionLang
