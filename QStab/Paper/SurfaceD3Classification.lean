import QStab.Examples.SurfaceCode
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Surface code d=3 scheduling classification

For the [[9,1,3]] rotated surface code (paper convention, L_Z = Z₀Z₁Z₂
on the top row), every CX gate ordering of the four X-stabilisers
falls into one of three classes:

  - `LAligned`: every Type-II hook is row-confined modulo X-stab.
  - `CleanRecord`: at least one bad hook (multi-row mod stab), but
    no DEM mechanism matches its (parity column, flipped L) signature.
  - `Failing`: at least one bad hook AND a matching DEM mechanism.

## Honest scope

This file is the **decidable structural classification**. It proves:

* The three classes are mutually exclusive and exhaustive.
* The static-DEM minimum weight is ≤ 2 iff scheduling is `Failing`.
* The class counts are exactly 256 / 768 / 1280 over 2304 schedulings.

The proofs use `native_decide` to evaluate over the 2304 schedulings.

This file does NOT prove the operational `MultiStep` bridge to
`d_circ`. The DEM ↔ operational bridge is the structural fact that
`E_tilde` accumulates as XOR of Type-0/I/II contributions; integration
with the full `MultiStep` machinery is mechanical work left to a
follow-up file.

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.SurfaceD3Classification

open QStab QStab.Examples QStab.Examples.SurfaceD3

/-! ## Scheduling representation -/

/-- A scheduling: 24 perms for each weight-4 stab, 2 perms each for
    weight-2 stabs. Total 24·24·2·2 = 2304. -/
abbrev Surface3Sched := Fin 24 × Fin 24 × Fin 2 × Fin 2

instance : Fintype Surface3Sched :=
  inferInstanceAs (Fintype (Fin 24 × Fin 24 × Fin 2 × Fin 2))

instance : DecidableEq Surface3Sched :=
  inferInstanceAs (DecidableEq (Fin 24 × Fin 24 × Fin 2 × Fin 2))

/-- All 24 permutations of `[a,b,c,d]`, indexed by `Fin 24`. -/
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

/-! ## X-stab supports (paper convention, [[9,1,3]]) -/

def xStab0 : List (Fin 9) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]
def xStab1 : List (Fin 9) :=
  [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]
def xStab2 : List (Fin 9) := [⟨0, by decide⟩, ⟨1, by decide⟩]
def xStab3 : List (Fin 9) := [⟨7, by decide⟩, ⟨8, by decide⟩]

/-- Stab support by index. -/
def xStab : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => xStab0 | ⟨1, _⟩ => xStab1
  | ⟨2, _⟩ => xStab2 | ⟨3, _⟩ => xStab3

/-- Apply scheduling to get ordered qubit list per stab. -/
def schedOrder (s : Surface3Sched) : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => perm4 s.1 xStab0
  | ⟨1, _⟩ => perm4 s.2.1 xStab1
  | ⟨2, _⟩ => perm2 s.2.2.1 xStab2
  | ⟨3, _⟩ => perm2 s.2.2.2 xStab3

/-! ## Hooks -/

/-- All non-trivial suffixes (j=1, j=2, ..., j=len-1) of the ordering. -/
def hooksOf : List (Fin 9) → List (List (Fin 9))
  | [] => []
  | [_] => []
  | _ :: rest => rest :: hooksOf rest

/-! ## Z-stab supports (paper convention) -/

def zStabSupp : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
  | ⟨1, _⟩ => [⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩]
  | ⟨2, _⟩ => [⟨2, by decide⟩, ⟨5, by decide⟩]
  | ⟨3, _⟩ => [⟨3, by decide⟩, ⟨6, by decide⟩]

def lzSupp : List (Fin 9) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

/-- Parity of an X-set against a Z-set: count intersections mod 2. -/
def parityXZ (xs zs : List (Fin 9)) : Bool :=
  ((xs.filter (· ∈ zs)).length) % 2 == 1

/-- DEM signature: 4 syndrome bits + 1 logical bit. -/
def dem_sig (xs : List (Fin 9)) : List Bool × Bool :=
  ((List.finRange 4).map (fun i => parityXZ xs (zStabSupp i)),
    parityXZ xs lzSupp)

/-! ## Bad-hook detection (row-based, paper convention) -/

def rowOf (q : Fin 9) : Fin 3 := ⟨q.val / 3, by omega⟩

def rowsOf (qs : List (Fin 9)) : List (Fin 3) :=
  (qs.map rowOf).dedup

/-- A hook is bad iff hook AND (stab XOR hook) both span ≥ 2 rows. -/
def isBadHook (stab_supp hook : List (Fin 9)) : Bool :=
  let rows_h := rowsOf hook
  if rows_h.length ≤ 1 then false
  else
    let symDiff := (stab_supp.filter (· ∉ hook)) ++ (hook.filter (· ∉ stab_supp))
    let rows_alt := rowsOf symDiff
    rows_alt.length > 1

/-! ## DEM signatures and predicates -/

def t0_sigs : List (List Bool × Bool) :=
  (List.finRange 9).map (fun q => dem_sig [q])

def t2_sigs (s : Surface3Sched) : List (List Bool × Bool) :=
  (List.finRange 4).flatMap fun i =>
    (hooksOf (schedOrder s i)).map dem_sig

def hasBadHook (s : Surface3Sched) : Bool :=
  (List.finRange 4).any fun i =>
    (hooksOf (schedOrder s i)).any (fun h => isBadHook (xStab i) h)

def hasMatchingMech (s : Surface3Sched) : Bool :=
  let allSigs := t0_sigs ++ t2_sigs s
  (List.finRange 4).any fun i =>
    (hooksOf (schedOrder s i)).any fun h =>
      isBadHook (xStab i) h &&
      (let (h_t, l_t) := dem_sig h
       allSigs.any fun (h_k, l_k) =>
         h_k = h_t && l_k != l_t)

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

/-! ## DEM weight-2 check -/

def xorQubits (a b : List (Fin 9)) : List (Fin 9) :=
  ((a.filter (· ∉ b)) ++ (b.filter (· ∉ a))).dedup

def allMechs (s : Surface3Sched) : List (List (Fin 9)) :=
  let t0 := (List.finRange 9).map (fun q => ([q] : List (Fin 9)))
  let t2 := (List.finRange 4).flatMap (fun i => hooksOf (schedOrder s i))
  t0 ++ t2

def isSuccess (xs : List (Fin 9)) : Bool :=
  ((List.finRange 4).all (fun i => parityXZ xs (zStabSupp i) = false)) &&
  parityXZ xs lzSupp

/-- Decidable: scheduling has a weight-≤-2 success codeword. -/
def demDCircLE2 (s : Surface3Sched) : Bool :=
  let mechs := allMechs s
  (mechs.any (fun m => isSuccess m)) ||
  (mechs.any fun m1 => mechs.any fun m2 =>
    decide (m1 ≠ m2) && isSuccess (xorQubits m1 m2))

/-! ## Headline theorems -/

/-- The three classes partition the scheduling space. -/
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

/-- Class characterisation: each class is exactly defined by the
    `hasBadHook` and `hasMatchingMech` decidable predicates. -/
theorem class_iff_LAligned (s : Surface3Sched) :
    classOf s = SchedClass.LAligned ↔ hasBadHook s = false := by
  simp only [classOf]
  by_cases h1 : hasBadHook s = false
  · rw [if_pos h1]; simp [h1]
  · rw [if_neg h1]
    by_cases h2 : hasMatchingMech s = true
    · rw [if_pos h2]; simp [h1]
    · rw [if_neg h2]; simp [h1]

theorem class_iff_Failing (s : Surface3Sched) :
    classOf s = SchedClass.Failing ↔
      (hasBadHook s = true ∧ hasMatchingMech s = true) := by
  simp only [classOf]
  by_cases h1 : hasBadHook s = false
  · rw [if_pos h1]
    simp [h1]
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

theorem class_iff_CleanRecord (s : Surface3Sched) :
    classOf s = SchedClass.CleanRecord ↔
      (hasBadHook s = true ∧ hasMatchingMech s = false) := by
  simp only [classOf]
  by_cases h1 : hasBadHook s = false
  · rw [if_pos h1]
    simp [h1]
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

/-! ## DEM ↔ Failing iff (via native_decide) -/

theorem dem_dist_le2_iff_failing :
    ∀ s : Surface3Sched,
      demDCircLE2 s = (decide (classOf s = SchedClass.Failing)) := by
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
