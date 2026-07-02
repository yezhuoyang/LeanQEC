import QStab.QClifford.Compile.SurfaceNZSpecAlign

/-!
# F1 Stab-half: the `InStab` ↔ masked-product bridge (decide-free, parametric)

The `d = 3` route (`SurfaceD3.prodStab_surface`) closes `Stab ↔ InStab` by `decide +revert`
over the finite mask set — forbidden on the parametric path.  This file builds the genuine
bridge: `InStab P E ↔ ∃ mask, E = qecMaskProd P mask`, where `qecMaskProd` is the
`ErrorVec.mul`-fold of the masked generators.  The forward direction needs the abelian +
self-inverse structure of the Pauli group (the mask-combination lemma); the backward
direction is a fold invariant.

Stated at ONE spelling of the index type (`Fin P.numStab`); the compiled-spec transport (a
`Fin.cast` along `programNumStab_surfaceXZProgram`) is layered on top downstream.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford

/-! ## `ErrorVec.mul` is an abelian group with involutive elements -/

private theorem evmul_comm {n : Nat} (a b : ErrorVec n) : ErrorVec.mul a b = ErrorVec.mul b a := by
  funext q; simp only [ErrorVec.mul]; cases a q <;> cases b q <;> rfl

private theorem evmul_assoc {n : Nat} (a b c : ErrorVec n) :
    ErrorVec.mul (ErrorVec.mul a b) c = ErrorVec.mul a (ErrorVec.mul b c) := by
  funext q; simp only [ErrorVec.mul]; cases a q <;> cases b q <;> cases c q <;> rfl

private theorem evmul_self {n : Nat} (a : ErrorVec n) : ErrorVec.mul a a = ErrorVec.identity n := by
  funext q; simp only [ErrorVec.mul, ErrorVec.identity]; cases a q <;> rfl

private theorem evmul_id_right {n : Nat} (a : ErrorVec n) :
    ErrorVec.mul a (ErrorVec.identity n) = a := by
  funext q; simp only [ErrorVec.mul, ErrorVec.identity]; cases a q <;> rfl

private theorem evmul_id_left {n : Nat} (a : ErrorVec n) :
    ErrorVec.mul (ErrorVec.identity n) a = a := by
  funext q; simp only [ErrorVec.mul, ErrorVec.identity]; cases a q <;> rfl

/-! ## The masked product of a QEC param's generators -/

/-- The `ErrorVec.mul`-fold of the generators `P.stabilizers i` selected by `mask`. -/
def qecMaskProd (P : QECParams) (mask : Fin P.numStab → Bool) : ErrorVec P.n :=
  (List.finRange P.numStab).foldl
    (fun acc i => if mask i then ErrorVec.mul acc (P.stabilizers i) else acc)
    (ErrorVec.identity P.n)

/-- **Mask-combination** (the crux): the product of two masked folds is the masked fold of
the boolean-XOR mask.  Uses only `ErrorVec.mul` abelian + self-inverse. -/
private theorem foldl_maskStep_combine {P : QECParams} (m₁ m₂ : Fin P.numStab → Bool) :
    ∀ (l : List (Fin P.numStab)) (a b : ErrorVec P.n),
      ErrorVec.mul
        (l.foldl (fun acc i => if m₁ i then ErrorVec.mul acc (P.stabilizers i) else acc) a)
        (l.foldl (fun acc i => if m₂ i then ErrorVec.mul acc (P.stabilizers i) else acc) b) =
      l.foldl (fun acc i =>
          if xor (m₁ i) (m₂ i) then ErrorVec.mul acc (P.stabilizers i) else acc)
        (ErrorVec.mul a b) := by
  intro l
  induction l with
  | nil => intro a b; rfl
  | cons i rest ih =>
      intro a b
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      -- reconcile the head step: mul (step m₁ a i) (step m₂ b i) = step (m₁⊕m₂) (mul a b) i
      funext q
      simp only [ErrorVec.mul, apply_ite (f := fun e : ErrorVec P.n => e q)]
      cases m₁ i <;> cases m₂ i <;> cases a q <;> cases b q <;> cases P.stabilizers i q <;> rfl

/-- The all-`false` mask gives the identity. -/
private theorem qecMaskProd_false (P : QECParams) :
    qecMaskProd P (fun _ => false) = ErrorVec.identity P.n := by
  unfold qecMaskProd
  have : ∀ (l : List (Fin P.numStab)) (init : ErrorVec P.n),
      l.foldl (fun acc i => if (fun _ => false) i then ErrorVec.mul acc (P.stabilizers i) else acc)
        init = init := by
    intro l; induction l with
    | nil => intro init; rfl
    | cons _ rest ih => intro init; simp only [List.foldl_cons]; exact ih init
  exact this _ _

/-- Boolean-XOR of masks ↦ `ErrorVec.mul` of the folds. -/
private theorem qecMaskProd_combine (P : QECParams) (m₁ m₂ : Fin P.numStab → Bool) :
    ErrorVec.mul (qecMaskProd P m₁) (qecMaskProd P m₂) =
      qecMaskProd P (fun i => xor (m₁ i) (m₂ i)) := by
  unfold qecMaskProd
  rw [foldl_maskStep_combine m₁ m₂, evmul_id_right]

/-- A mask that misses `i` never touches `i`'s generator. -/
private theorem foldl_maskStep_miss (P : QECParams) (i : Fin P.numStab) :
    ∀ (l : List (Fin P.numStab)), i ∉ l → ∀ init : ErrorVec P.n,
      l.foldl (fun acc j => if decide (j = i) then ErrorVec.mul acc (P.stabilizers j) else acc)
        init = init := by
  intro l; induction l with
  | nil => intro _ init; rfl
  | cons h rest ih =>
      intro hmem init
      have hh : h ≠ i := fun heq => hmem (heq ▸ List.mem_cons_self ..)
      simp only [List.foldl_cons, if_neg (show ¬ (decide (h = i) = true) by simp [hh])]
      exact ih (fun hm => hmem (List.mem_cons_of_mem h hm)) init

/-- Selecting a single generator index `i` yields exactly `P.stabilizers i`. -/
private theorem foldl_maskStep_single (P : QECParams) (i : Fin P.numStab) :
    ∀ (l : List (Fin P.numStab)), l.Nodup → i ∈ l → ∀ init : ErrorVec P.n,
      l.foldl (fun acc j => if decide (j = i) then ErrorVec.mul acc (P.stabilizers j) else acc)
        init = ErrorVec.mul init (P.stabilizers i) := by
  intro l; induction l with
  | nil => intro _ hmem _; exact absurd hmem (by simp)
  | cons h rest ih =>
      intro hnd hmem init
      rw [List.nodup_cons] at hnd
      simp only [List.foldl_cons]
      by_cases hh : h = i
      · subst hh
        rw [if_pos (by simp)]
        exact foldl_maskStep_miss P h rest hnd.1 (ErrorVec.mul init (P.stabilizers h))
      · rw [if_neg (show ¬ (decide (h = i) = true) by simp [hh])]
        rcases List.mem_cons.mp hmem with h' | h'
        · exact absurd h'.symm hh
        · exact ih hnd.2 h' init

private theorem qecMaskProd_single (P : QECParams) (i : Fin P.numStab) :
    qecMaskProd P (fun j => decide (j = i)) = P.stabilizers i := by
  unfold qecMaskProd
  rw [foldl_maskStep_single P i _ (List.nodup_finRange _) (List.mem_finRange i), evmul_id_left]

/-- The fold over any mask lands in the stabilizer subgroup. -/
private theorem foldl_maskStep_InStab (P : QECParams) (mask : Fin P.numStab → Bool) :
    ∀ (l : List (Fin P.numStab)) (init : ErrorVec P.n), InStab P init →
      InStab P (l.foldl (fun acc i => if mask i then ErrorVec.mul acc (P.stabilizers i) else acc)
        init) := by
  intro l; induction l with
  | nil => intro init h; exact h
  | cons i rest ih =>
      intro init h
      simp only [List.foldl_cons]
      apply ih
      by_cases hm : mask i = true
      · rw [if_pos hm]; exact InStab.mul h (InStab.gen i)
      · rw [if_neg hm]; exact h

/-- **The bridge.**  `InStab P E` iff `E` is a masked product of `P`'s generators. -/
theorem InStab_iff_qecMaskProd (P : QECParams) (E : ErrorVec P.n) :
    InStab P E ↔ ∃ mask : Fin P.numStab → Bool, E = qecMaskProd P mask := by
  constructor
  · intro h
    induction h with
    | identity => exact ⟨fun _ => false, (qecMaskProd_false P).symm⟩
    | gen i => exact ⟨fun j => decide (j = i), (qecMaskProd_single P i).symm⟩
    | mul _ _ ih₁ ih₂ =>
        obtain ⟨m₁, rfl⟩ := ih₁
        obtain ⟨m₂, rfl⟩ := ih₂
        exact ⟨fun i => xor (m₁ i) (m₂ i), qecMaskProd_combine P m₁ m₂⟩
  · rintro ⟨mask, rfl⟩
    exact foldl_maskStep_InStab P mask _ _ InStab.identity

end QStab.QClifford.Compile
