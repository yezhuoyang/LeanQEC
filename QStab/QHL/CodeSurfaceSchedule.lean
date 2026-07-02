import QStab.Examples.SurfaceHookErrors
import QStab.QHL.CodeLang

/-!
# Milestone S: the NZ schedule as a syntactic object-language program

Goal: express the compiler's NZ schedule as **object-language programs** (a flat order
program `nzOrderProg : Term 3 .nat` and a length program `nzLenProg : Term 2 .nat`), so
that the compiler input becomes two object programs whose certified evaluation re-anchors
`surfaceXZProgram` (and hence every closed theorem on it) to a syntactically-generated
pipeline.

## Phase map
* **S1 (this file, in progress).**  Meta classifiers `nzOrderFlat` / `nzLenFlat` (landed
  here), then the object programs `nzOrderProg : Term 3 .nat` / `nzLenProg : Term 2 .nat`
  mirroring `classifyStab`'s `ltNat/div/mod/ite` cascade (no `recCall`; both `PureTerm`),
  and certified eval `nzOrderProg_eval` / `nzLenProg_eval` via the
  `gridRowZStripIndex_eval` recipe.  Qubit-level anchor to the existing `nzSchedule`
  (via `gridFin_val_of_lt` + `kindOrderRC_classify_in_bounds`).
* **S3.**  `xzProgramOfPrograms` generator + re-anchor
  `xzProgramOfPrograms Surface.code nzOrderProg nzLenProg d = surfaceXZProgram d hd`
  (leans on the existing `nzSchedule_kind_faithful` / `nzSchedule_support_iff` in
  `Compile/SurfaceNZScheduleAnchor.lean`).
* **S2.**  `nzScheduledPauli := .stabAt (.recCall (.var 2) (.var 1)) nzOrderProg`, certified
  to `surfaceCellPauli d k (nzOrderFlat d k j)` at odd distances.
* **S4.**  Finish `nz_ordered` + assemble `IsNZScheduleOf` (the spec/uniqueness layer
  already drafted in `Compile/SurfaceNZScheduleAnchor.lean`) against the generated
  schedule.

## S1 meta foundation (this file)

The two meta classifiers below are the *reference* values against which the object
programs are certified.  They are the flat (index-`j`) views of the already-fixed meta
schedule `kindOrderRC ∘ classifyStab`, so no new notion of order or kind is introduced —
`nzOrderFlat` is definitionally `gridIdx` of the `j`-th `kindOrderRC` coordinate.
-/

namespace QHL.CodeSurfaceSchedule

open QStab.Examples.SurfaceParametric

/-- Number of scheduled couplings of surface stabilizer `k` at distance `d`: the length
of the NZ coupling order `kindOrderRC (classifyStab d k)` (always `2` or `4`). -/
def nzLenFlat (d k : Nat) : Nat := (kindOrderRC d (classifyStab d k)).length

/-- Flat NZ-order classifier: the qubit index (`gridIdx d row col`) of the `j`-th
scheduled coupling of surface stabilizer `k` at distance `d`, with the out-of-range
sentinel `d * d` when `j ≥ nzLenFlat d k`.  This is the *reference* value the object
program `nzOrderProg` is certified against. -/
def nzOrderFlat (d k j : Nat) : Nat :=
  match (kindOrderRC d (classifyStab d k))[j]? with
  | some rc => gridIdx d rc.1 rc.2
  | none => d * d

/-- `nzLenFlat` is exactly the `kindOrderRC` length (definitional unfold). -/
theorem nzLenFlat_eq (d k : Nat) :
    nzLenFlat d k = (kindOrderRC d (classifyStab d k)).length := rfl

/-- Every surface stabilizer schedules a positive number of couplings (`2` or `4`). -/
theorem nzLenFlat_pos (d k : Nat) : 0 < nzLenFlat d k := by
  rw [nzLenFlat_eq]
  cases hk : classifyStab d k <;> simp [kindOrderRC]

/-- The NZ schedule length is `2` or `4`, by stabilizer kind. -/
theorem nzLenFlat_eq_two_or_four (d k : Nat) : nzLenFlat d k = 2 ∨ nzLenFlat d k = 4 := by
  rw [nzLenFlat_eq]
  cases hk : classifyStab d k <;> simp [kindOrderRC]

/-- In range (`j < nzLenFlat d k`), `nzOrderFlat` reads the `j`-th coordinate: it is
`gridIdx d rc.1 rc.2` for `rc = (kindOrderRC d (classifyStab d k))[j]`, never the
sentinel. -/
theorem nzOrderFlat_of_lt (d k j : Nat) (hj : j < nzLenFlat d k) :
    ∃ rc, (kindOrderRC d (classifyStab d k))[j]? = some rc ∧
      nzOrderFlat d k j = gridIdx d rc.1 rc.2 := by
  rw [nzLenFlat_eq] at hj
  have hsome : (kindOrderRC d (classifyStab d k))[j]? =
      some (kindOrderRC d (classifyStab d k))[j] := List.getElem?_eq_getElem hj
  refine ⟨_, hsome, ?_⟩
  unfold nzOrderFlat
  rw [hsome]

/-! ## S1 object programs

The NZ order and length as **object-language terms** — `classifyStab`'s cascade fused
with the `kindOrderRC` coordinate selection and `gridIdx`, expressed with the language's
`ltNat/eqNat/div/mod/ite` constructors.  Variable convention (environment
`Env.cons j (Env.code d k)`): `j = var 0`, `k = var 1`, `d = var 2`.  No `recCall`
anywhere, so evaluation is fuel- and codeBody-irrelevant. -/

open QHL.CodeLang

/-- **The NZ schedule as a syntactic object program**: `(d, k, j) ↦` the qubit index of
the `j`-th scheduled coupling (sentinel `d * d` out of range). -/
def nzOrderProg : Term 3 .nat :=
  let J : Term 3 .nat := .var 0
  let K : Term 3 .nat := .var 1
  let D : Term 3 .nat := .var 2
  let one : Term 3 .nat := .natLit 1
  let two : Term 3 .nat := .natLit 2
  let three : Term 3 .nat := .natLit 3
  let dm1 : Term 3 .nat := .sub D one
  let bulk : Term 3 .nat := .mul dm1 dm1
  let half : Term 3 .nat := .div dm1 two
  let b : Term 3 .nat := .sub K bulk
  let r : Term 3 .nat := .div K dm1
  let c : Term 3 .nat := .mod K dm1
  let qb : Term 3 .nat → Term 3 .nat → Term 3 .nat := fun row col => .add (.mul D row) col
  let sentinel : Term 3 .nat := .mul D D
  .ite (.ltNat K bulk)
    (.ite (.eqNat (.mod (.add r c) two) (.natLit 0))
      (.ite (.eqNat J (.natLit 0)) (qb r c)
        (.ite (.eqNat J one) (qb (.add r one) c)
          (.ite (.eqNat J two) (qb r (.add c one))
            (.ite (.eqNat J three) (qb (.add r one) (.add c one)) sentinel))))
      (.ite (.eqNat J (.natLit 0)) (qb r c)
        (.ite (.eqNat J one) (qb r (.add c one))
          (.ite (.eqNat J two) (qb (.add r one) c)
            (.ite (.eqNat J three) (qb (.add r one) (.add c one)) sentinel)))))
    (.ite (.ltNat b half)
      (.ite (.ltNat J two) (.add (.mul two b) J) sentinel)
      (.ite (.ltNat b (.mul two half))
        (.ite (.ltNat J two) (qb (.add (.mul two (.sub b half)) J) dm1) sentinel)
        (.ite (.ltNat b (.mul three half))
          (.ite (.ltNat J two)
            (.mul D (.add (.add (.mul two (.sub b (.mul two half))) one) J)) sentinel)
          (.ite (.ltNat J two)
            (.add (.mul D dm1) (.add (.add (.mul two (.sub b (.mul three half))) one) J))
            sentinel))))

/-- The NZ schedule length as an object program: `4` for bulk, `2` for boundary. -/
def nzLenProg : Term 2 .nat :=
  let K : Term 2 .nat := .var 0
  let D : Term 2 .nat := .var 1
  let dm1 : Term 2 .nat := .sub D (.natLit 1)
  .ite (.ltNat K (.mul dm1 dm1)) (.natLit 4) (.natLit 2)

private lemma env3_zero (j d k : Nat) : (Env.cons j (Env.code d k)) 0 = j := rfl
private lemma env3_one (j d k : Nat) : (Env.cons j (Env.code d k)) 1 = k := rfl
private lemma env3_two (j d k : Nat) : (Env.cons j (Env.code d k)) 2 = d := rfl
private lemma env2_zero (d k : Nat) : (Env.code d k) 0 = k := rfl
private lemma env2_one (d k : Nat) : (Env.code d k) 1 = d := rfl

/-- Meta mirror of `nzOrderProg`'s arithmetic — identical tree, identical condition
order, so certified evaluation is pure structural alignment. -/
def nzOrderArith (d k j : Nat) : Nat :=
  if k < (d - 1) * (d - 1) then
    if (k / (d - 1) + k % (d - 1)) % 2 = 0 then
      if j = 0 then d * (k / (d - 1)) + k % (d - 1)
      else if j = 1 then d * (k / (d - 1) + 1) + k % (d - 1)
      else if j = 2 then d * (k / (d - 1)) + (k % (d - 1) + 1)
      else if j = 3 then d * (k / (d - 1) + 1) + (k % (d - 1) + 1)
      else d * d
    else
      if j = 0 then d * (k / (d - 1)) + k % (d - 1)
      else if j = 1 then d * (k / (d - 1)) + (k % (d - 1) + 1)
      else if j = 2 then d * (k / (d - 1) + 1) + k % (d - 1)
      else if j = 3 then d * (k / (d - 1) + 1) + (k % (d - 1) + 1)
      else d * d
  else
    if k - (d - 1) * (d - 1) < (d - 1) / 2 then
      if j < 2 then 2 * (k - (d - 1) * (d - 1)) + j else d * d
    else if k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2) then
      if j < 2 then
        d * (2 * (k - (d - 1) * (d - 1) - (d - 1) / 2) + j) + (d - 1)
      else d * d
    else if k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2) then
      if j < 2 then
        d * (2 * (k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 1 + j)
      else d * d
    else
      if j < 2 then
        d * (d - 1) + (2 * (k - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1 + j)
      else d * d

theorem nzLenFlat_bulk (d k : Nat) (h : k < (d - 1) * (d - 1)) : nzLenFlat d k = 4 := by
  rw [nzLenFlat_eq]
  simp only [classifyStab, h, if_true]
  split_ifs <;> simp [kindOrderRC]

theorem nzLenFlat_boundary (d k : Nat) (h : ¬ k < (d - 1) * (d - 1)) : nzLenFlat d k = 2 := by
  rw [nzLenFlat_eq]
  simp only [classifyStab, h, if_false]
  split_ifs <;> simp [kindOrderRC]

/-! Certified evaluation (S1 remainder — see the milestone prompt): `nzLenProg_eval`
via a small `nzLenArith` mirror + the two branch helpers above, and
`nzOrderProg_eval_arith : Term.eval cb fuel nzOrderProg (Env.cons j (Env.code d k)) =
some (nzOrderArith d k j)` by `simp only [nzOrderProg, nzOrderArith, Term.eval,
env3_zero, env3_one, env3_two, Option.bind, decide_eq_true_eq]; split_ifs <;> rfl`
(this exact script elaborated successfully in a lean environment; it is heartbeat-
borderline in the full file — land it in a small downstream file if it times out
here), then `nzOrderFlat_eq_arith` reconciling the mirror with `nzOrderFlat`. -/

end QHL.CodeSurfaceSchedule
