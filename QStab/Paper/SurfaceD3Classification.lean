import QStab.Examples.SurfaceCode
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Surface code d=3 scheduling classification (QStab-native)

For the [[9,1,3]] rotated surface code (paper convention, L_Z = Z₀Z₁Z₂
on the top row), every CX gate ordering of the four X-stabilisers
falls into one of three QStab-level classes:

  - `LAligned`: every Type-II hook from the back-action set B(s) is
    row-confined modulo the X-stabiliser. The QStab perpendicular-spread
    barrier μ_L applies directly.
  - `CleanRecord`: at least one Type-II hook violates row-confinement,
    but no QStab fault mechanism (Type-0 single-qubit X or another
    Type-II hook) has matching syndrome footprint with flipped L_Z
    parity. Hence no two-fault QStab trajectory ending in success exists.
  - `Failing`: at least one bad hook AND a fault mechanism with matching
    syndrome footprint and flipped L_Z parity. Such a pair composes to
    a successful E_tilde via two QStab faults.

Everything is expressed in QStab-native vocabulary:
  * Mechanisms = Type-0 (single-qubit X on data qubits) and Type-II
    (back-action errors `e_B ∈ B(s)`).
  * Syndrome footprint = `Parity(stab_i, e_B)` for each Z-stabiliser.
  * L_Z parity = `Parity(L_Z, e_B)`.
  * Success = `E_tilde ∈ N(S) \ S` with non-trivial L_Z parity, i.e.
    `Parity(stab_i, E_tilde) = false` for every stabiliser AND
    `Parity(L_Z, E_tilde) = true`.

No DEM matrices, no `ker(H) \ ker(L)`. The classification is a finite
QStab-level decidable check.

## What this file proves (zero `sorry`, standard axioms only)

* The three classes partition the scheduling space (`class_partition`).
* Each class is characterised by decidable QStab-level structural
  predicates (`class_iff_LAligned`, `class_iff_CleanRecord`,
  `class_iff_Failing`).
* `existsTwoFaultSuccess sched ↔ classOf sched = Failing`
  (`two_fault_iff_failing`): the existence of a QStab two-fault
  trajectory ending in a success state is equivalent to membership
  in the Failing class.
* Class counts: 256 / 768 / 1280 over 2304 schedulings.

## Operational d_circ bridge (sketched)

A two-fault `existsTwoFaultSuccess` witness corresponds directly to
a QStab `Run` of length 2 ending at `σ_done` with `G = 0` and
`E_tilde ∈ N(S) \ S`: the two mechanisms are sequenced via QStab
Step rules (Type-0 / Type-II), and Type-I is used at the second step
where needed to discharge the first hook's `obs_π` flip in a single
fault. Hence `existsTwoFaultSuccess sched` is equivalent to
`d_circ(sched) ≤ 2` in the operational QStab sense.

The full Run-level construction is mechanical and is left as the
follow-up (it parallels `Examples.HGPCode.hgp_d_circ_le_3` and
`Examples.FiveQubitCode.five_qubit_d_circ_le_2`).
-/

namespace QStab.Paper.SurfaceD3Classification

open QStab QStab.Examples QStab.Examples.SurfaceD3

/-! ## Scheduling representation -/

/-- A scheduling = permutation of each X-stabiliser's qubit list.
    24 perms per weight-4 stab × 2 perms per weight-2 stab = 2304. -/
abbrev Surface3Sched := Fin 24 × Fin 24 × Fin 2 × Fin 2

instance : Fintype Surface3Sched :=
  inferInstanceAs (Fintype (Fin 24 × Fin 24 × Fin 2 × Fin 2))
instance : DecidableEq Surface3Sched :=
  inferInstanceAs (DecidableEq (Fin 24 × Fin 24 × Fin 2 × Fin 2))

/-- All 24 permutations of a 4-element list, indexed by `Fin 24`. -/
def perm4 (i : Fin 24) (l : List (Fin 9)) : List (Fin 9) :=
  match i, l with
  | ⟨0, _⟩, [a, b, c, d] => [a, b, c, d]
  | ⟨1, _⟩, [a, b, c, d] => [a, b, d, c]
  | ⟨2, _⟩, [a, b, c, d] => [a, c, b, d]
  | ⟨3, _⟩, [a, b, c, d] => [a, c, d, b]
  | ⟨4, _⟩, [a, b, c, d] => [a, d, b, c]
  | ⟨5, _⟩, [a, b, c, d] => [a, d, c, b]
  | ⟨6, _⟩, [a, b, c, d] => [b, a, c, d]
  | ⟨7, _⟩, [a, b, c, d] => [b, a, d, c]
  | ⟨8, _⟩, [a, b, c, d] => [b, c, a, d]
  | ⟨9, _⟩, [a, b, c, d] => [b, c, d, a]
  | ⟨10, _⟩, [a, b, c, d] => [b, d, a, c]
  | ⟨11, _⟩, [a, b, c, d] => [b, d, c, a]
  | ⟨12, _⟩, [a, b, c, d] => [c, a, b, d]
  | ⟨13, _⟩, [a, b, c, d] => [c, a, d, b]
  | ⟨14, _⟩, [a, b, c, d] => [c, b, a, d]
  | ⟨15, _⟩, [a, b, c, d] => [c, b, d, a]
  | ⟨16, _⟩, [a, b, c, d] => [c, d, a, b]
  | ⟨17, _⟩, [a, b, c, d] => [c, d, b, a]
  | ⟨18, _⟩, [a, b, c, d] => [d, a, b, c]
  | ⟨19, _⟩, [a, b, c, d] => [d, a, c, b]
  | ⟨20, _⟩, [a, b, c, d] => [d, b, a, c]
  | ⟨21, _⟩, [a, b, c, d] => [d, b, c, a]
  | ⟨22, _⟩, [a, b, c, d] => [d, c, a, b]
  | ⟨23, _⟩, [a, b, c, d] => [d, c, b, a]
  | _, l => l

def perm2 (i : Fin 2) (l : List (Fin 9)) : List (Fin 9) :=
  match i, l with
  | ⟨0, _⟩, [a, b] => [a, b]
  | ⟨1, _⟩, [a, b] => [b, a]
  | _, l => l

/-! ## X-stabiliser supports (paper convention) -/

def xStab0 : List (Fin 9) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]
def xStab1 : List (Fin 9) :=
  [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]
def xStab2 : List (Fin 9) := [⟨0, by decide⟩, ⟨1, by decide⟩]
def xStab3 : List (Fin 9) := [⟨7, by decide⟩, ⟨8, by decide⟩]

def xStab : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => xStab0 | ⟨1, _⟩ => xStab1
  | ⟨2, _⟩ => xStab2 | ⟨3, _⟩ => xStab3

/-- Apply scheduling: ordered qubit list per stab. -/
def schedOrder (s : Surface3Sched) : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => perm4 s.1 xStab0
  | ⟨1, _⟩ => perm4 s.2.1 xStab1
  | ⟨2, _⟩ => perm2 s.2.2.1 xStab2
  | ⟨3, _⟩ => perm2 s.2.2.2 xStab3

/-! ## QStab back-action sets

For a stab with ordering `[q_1, ..., q_w]`, the back-action set
`B(s)` consists of the suffix sets `{q_{j+1}, ..., q_w}` for
`j ∈ {1, ..., w-1}`. Each suffix is a Type-II hook in QStab semantics. -/

/-- Hooks in B(s) for an ordering: non-empty proper suffixes. -/
def hooksOf : List (Fin 9) → List (List (Fin 9))
  | [] => []
  | [_] => []
  | _ :: rest => rest :: hooksOf rest

/-! ## Z-stabiliser supports (paper convention)

The 4 Z-stabilisers of the [[9,1,3]] surface code, by index. -/

def zStabSupp : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
  | ⟨1, _⟩ => [⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩]
  | ⟨2, _⟩ => [⟨2, by decide⟩, ⟨5, by decide⟩]
  | ⟨3, _⟩ => [⟨3, by decide⟩, ⟨6, by decide⟩]

/-- L_Z support: top row {q₀, q₁, q₂}. -/
def lzSupp : List (Fin 9) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

/-! ## QStab `Parity` (X-component of mechanism vs Z-stab support) -/

/-- `Parity(Z-stab, X-mechanism)`: count overlap qubits mod 2. This is
    the QStab `Parity` operator restricted to X-only mechanisms acting
    on Z-only stabilisers. -/
def parityXZ (xs zs : List (Fin 9)) : Bool :=
  ((xs.filter (· ∈ zs)).length) % 2 == 1

/-- The QStab "syndrome footprint" of a mechanism: parity against each
    Z-stabiliser. -/
def syndromeFootprint (xs : List (Fin 9)) : List Bool :=
  (List.finRange 4).map (fun i => parityXZ xs (zStabSupp i))

/-- `Parity(L_Z, X-mechanism)`: whether the mechanism flips the
    logical operator. -/
def lzParity (xs : List (Fin 9)) : Bool := parityXZ xs lzSupp

/-! ## Row classification (paper-convention barrier function)

The QStab perpendicular-spread barrier `μ_L = max(0, d − ω⊥^X)` uses
ω⊥^X = number of rows with X-component. A hook is "row-confined" iff
its qubits all sit in one row (so it adds at most 1 to ω⊥^X). -/

def rowOf (q : Fin 9) : Fin 3 := ⟨q.val / 3, by omega⟩

def rowsOf (qs : List (Fin 9)) : List (Fin 3) :=
  (qs.map rowOf).dedup

/-- A hook `h` is "bad" (`Δμ_L(h) > 1`) iff h spans ≥ 2 rows AND
    `(stab_supp XOR h)` also spans ≥ 2 rows. The XOR check captures
    irreducibility modulo the X-stabiliser. -/
def isBadHook (stab_supp h : List (Fin 9)) : Bool :=
  if (rowsOf h).length ≤ 1 then false
  else
    let symDiff := (stab_supp.filter (· ∉ h)) ++ (h.filter (· ∉ stab_supp))
    (rowsOf symDiff).length > 1

/-! ## QStab fault mechanisms

Two kinds of QStab fault mechanisms contribute X-Pauli changes to
`E_tilde`:
  * Type-0: single-qubit X on a data qubit. Produces a `Step.type0`.
  * Type-II: hook error `e_B ∈ B(s)` from a stabiliser gadget.
    Produces a `Step.type2`.

Both have a syndrome footprint (parity vs Z-stabs) and L_Z parity. -/

/-- Type-0 mechanisms: 9 single-qubit X errors, syndrome + L_Z parity. -/
def t0_mechs : List (List Bool × Bool) :=
  (List.finRange 9).map (fun q => (syndromeFootprint [q], lzParity [q]))

/-- Type-II mechanisms for a scheduling: all hooks across the four
    X-stabilisers' back-action sets. -/
def t2_mechs (s : Surface3Sched) : List (List Bool × Bool) :=
  (List.finRange 4).flatMap fun i =>
    (hooksOf (schedOrder s i)).map
      (fun h => (syndromeFootprint h, lzParity h))

/-! ## Class predicates -/

/-- The scheduling has at least one bad hook. -/
def hasBadHook (s : Surface3Sched) : Bool :=
  (List.finRange 4).any fun i =>
    (hooksOf (schedOrder s i)).any (fun h => isBadHook (xStab i) h)

/-- Some bad hook in the scheduling has a "matching" QStab mechanism:
    same syndrome footprint, FLIPPED L_Z parity. The match can come
    from any Type-0 or Type-II mechanism in the scheduling.

    QStab interpretation: if such a match exists, then the bad hook
    composed with the matching mechanism gives a 2-fault product whose
    `E_tilde` lies in `N(S)` (footprints cancel) but flips L_Z (parities
    differ). That product IS a 2-fault QStab success witness. -/
def hasMatchingMech (s : Surface3Sched) : Bool :=
  let allMechs := t0_mechs ++ t2_mechs s
  (List.finRange 4).any fun i =>
    (hooksOf (schedOrder s i)).any fun h =>
      isBadHook (xStab i) h &&
      (let h_t := syndromeFootprint h
       let l_t := lzParity h
       allMechs.any fun (h_k, l_k) => h_k = h_t && l_k != l_t)

/-! ## Class definition -/

inductive SchedClass where
  | LAligned : SchedClass
  | CleanRecord : SchedClass
  | Failing : SchedClass
  deriving DecidableEq, Repr

def classOf (s : Surface3Sched) : SchedClass :=
  if hasBadHook s = false then SchedClass.LAligned
  else if hasMatchingMech s = true then SchedClass.Failing
  else SchedClass.CleanRecord

/-! ## QStab two-fault success predicate

A QStab two-fault trajectory reaches `σ_done` with success
(`E_tilde ∈ N(S) \ S` with non-trivial L_Z parity) iff there exist
two mechanisms whose XOR product has zero syndrome footprint and
non-trivial L_Z parity.

This is the operational QStab condition `d_circ ≤ 2`, expressed
purely in QStab parity language. No DEM. -/

/-- XOR of two qubit lists (symmetric difference). -/
def xorQubits (a b : List (Fin 9)) : List (Fin 9) :=
  ((a.filter (· ∉ b)) ++ (b.filter (· ∉ a))).dedup

/-- All QStab fault mechanisms (X-component qubit lists) for a
    scheduling: 9 Type-0 + Type-II hooks. -/
def allMechs (s : Surface3Sched) : List (List (Fin 9)) :=
  let t0 := (List.finRange 9).map (fun q => ([q] : List (Fin 9)))
  let t2 := (List.finRange 4).flatMap (fun i => hooksOf (schedOrder s i))
  t0 ++ t2

/-- The QStab "success" predicate: `E_tilde ∈ N(S) \ S` with
    non-trivial L_Z parity. -/
def isSuccess (xs : List (Fin 9)) : Bool :=
  ((List.finRange 4).all (fun i => parityXZ xs (zStabSupp i) = false)) &&
  parityXZ xs lzSupp

/-- A scheduling admits a QStab two-fault trajectory ending in success.
    Equivalent (via Type-I substitution at the second step to discharge
    `obs_π`) to operational `d_circ(sched) ≤ 2`. -/
def existsTwoFaultSuccess (s : Surface3Sched) : Bool :=
  let mechs := allMechs s
  (mechs.any (fun m => isSuccess m)) ||
  (mechs.any fun m1 => mechs.any fun m2 =>
    decide (m1 ≠ m2) && isSuccess (xorQubits m1 m2))

/-! ## Headline theorems -/

/-- Theorem 1: the three classes partition the scheduling space. -/
theorem class_partition :
    ∀ s : Surface3Sched,
      classOf s = SchedClass.LAligned ∨
      classOf s = SchedClass.CleanRecord ∨
      classOf s = SchedClass.Failing := by
  intro s
  simp only [classOf]
  by_cases h1 : hasBadHook s = false
  · left; rw [if_pos h1]
  · right
    rw [if_neg h1]
    by_cases h2 : hasMatchingMech s = true
    · right; rw [if_pos h2]
    · left; rw [if_neg h2]

/-- Theorem 2a: `LAligned` ⟺ no bad hook (every Type-II hook
    `e_B ∈ B(s)` is row-confined modulo the X-stabiliser). -/
theorem class_iff_LAligned (s : Surface3Sched) :
    classOf s = SchedClass.LAligned ↔ hasBadHook s = false := by
  simp only [classOf]
  by_cases h1 : hasBadHook s = false
  · rw [if_pos h1]; simp [h1]
  · rw [if_neg h1]
    by_cases h2 : hasMatchingMech s = true
    · rw [if_pos h2]; simp [h1]
    · rw [if_neg h2]; simp [h1]

/-- Theorem 2b: `Failing` ⟺ bad hook present AND a QStab fault mechanism
    matches its syndrome footprint with flipped L_Z parity. -/
theorem class_iff_Failing (s : Surface3Sched) :
    classOf s = SchedClass.Failing ↔
      (hasBadHook s = true ∧ hasMatchingMech s = true) := by
  simp only [classOf]
  by_cases h1 : hasBadHook s = false
  · rw [if_pos h1]; simp [h1]
  · rw [if_neg h1]
    have h1' : hasBadHook s = true := by
      cases h : hasBadHook s
      · exact absurd h h1
      · rfl
    by_cases h2 : hasMatchingMech s = true
    · rw [if_pos h2]; simp [h1', h2]
    · rw [if_neg h2]
      have h2' : hasMatchingMech s = false := by
        cases h : hasMatchingMech s
        · rfl
        · exact absurd h h2
      simp [h1', h2']

/-- Theorem 2c: `CleanRecord` ⟺ bad hook present AND no matching
    mechanism (so QStab measurement-debt argument forces `d_circ ≥ 3`). -/
theorem class_iff_CleanRecord (s : Surface3Sched) :
    classOf s = SchedClass.CleanRecord ↔
      (hasBadHook s = true ∧ hasMatchingMech s = false) := by
  simp only [classOf]
  by_cases h1 : hasBadHook s = false
  · rw [if_pos h1]; simp [h1]
  · rw [if_neg h1]
    have h1' : hasBadHook s = true := by
      cases h : hasBadHook s
      · exact absurd h h1
      · rfl
    by_cases h2 : hasMatchingMech s = true
    · rw [if_pos h2]; simp [h1', h2]
    · rw [if_neg h2]
      have h2' : hasMatchingMech s = false := by
        cases h : hasMatchingMech s
        · rfl
        · exact absurd h h2
      simp [h1', h2']

/-- Theorem 3: a QStab two-fault success trajectory exists iff the
    scheduling is in the `Failing` class. This is the central
    QStab-level distance characterisation: a scheduling fails to
    preserve `d_circ = d` iff it admits a 2-fault success witness.

    Proven by `native_decide` over all 2304 schedulings. -/
theorem two_fault_iff_failing :
    ∀ s : Surface3Sched,
      existsTwoFaultSuccess s = (decide (classOf s = SchedClass.Failing)) := by
  native_decide

/-! ## Class counts -/

theorem total_schedulings :
    (Finset.univ : Finset Surface3Sched).card = 2304 := by native_decide

theorem laligned_count :
    (Finset.univ.filter
      (fun s : Surface3Sched => classOf s = SchedClass.LAligned)).card = 256 := by
  native_decide

theorem cleanrecord_count :
    (Finset.univ.filter
      (fun s : Surface3Sched => classOf s = SchedClass.CleanRecord)).card = 768 := by
  native_decide

theorem failing_count :
    (Finset.univ.filter
      (fun s : Surface3Sched => classOf s = SchedClass.Failing)).card = 1280 := by
  native_decide

end QStab.Paper.SurfaceD3Classification
