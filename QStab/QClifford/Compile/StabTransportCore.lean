import QStab.QClifford.Compile.VCBridge
import QStab.Examples.SurfaceGeometry

/-!
# Program-agnostic fold lemmas for the `Stab ↔ InStab` transport

The generic engine behind the dimensional transport between a compiled PCC
spec's `Stab`/`prodStab` predicates (over `Fin (n + k)`, `pauliMul` folds) and
a source machine's `InStab`/`qecMaskProd` (over `Fin n`, `ErrorVec.mul`
folds):

* `foldl_ev_apply` / `qecMaskProd_apply` — pointwise evaluation of masked
  `ErrorVec.mul`-folds;
* `foldl_transport` — the index transport along a `Fin.cast` of the
  stabilizer count;
* `foldl_pauliMul_allI` — triviality of a fold whose generators vanish;
* `Fin_cast_forall_iff` — reindexing a `∀` along a `Fin.cast`.

Also home to the (formerly surface-filed) generic pieces: the
`InStab ↔ qecMaskProd` bridge and the `seqMeas` scheme alignment
(`measuresAtAux_seqMeas_map_scheme`).  Everything here is **public** and
program-agnostic; both the surface and HGP transports instantiate it.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC

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

/-- Evaluating an `ErrorVec.mul`-fold at a fixed coordinate `q` pushes through
to the kernel `pauliMul`-fold of the coordinate values. -/
theorem foldl_ev_apply {N : Nat} {ι : Type} (mask : ι → Bool) (stabs : ι → ErrorVec N) :
    ∀ (l : List ι) (init : ErrorVec N) (q : Fin N),
      (l.foldl (fun acc i => if mask i then ErrorVec.mul acc (stabs i) else acc) init) q =
        l.foldl (fun acc i => if mask i then pauliMul acc (stabs i q) else acc) (init q) := by
  intro l
  induction l with
  | nil => intro init q; rfl
  | cons a rest ih =>
      intro init q
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      simp only [apply_ite (f := fun e : ErrorVec N => e q), ErrorVec.mul, pauliMul_eq_mul]

/-- Pointwise `pauliMul`-fold form of `qecMaskProd`. -/
theorem qecMaskProd_apply (P : QECParams) (mask : Fin P.numStab → Bool) (q : Fin P.n) :
    qecMaskProd P mask q =
      (List.finRange P.numStab).foldl
        (fun acc i => if mask i then pauliMul acc (P.stabilizers i q) else acc) Pauli.I := by
  unfold qecMaskProd
  rw [foldl_ev_apply]
  rfl

/-- **Index transport.**  A `pauliMul`-fold over `finRange m` whose per-index
generator is `Fin.cast`-related to a source generator equals the source fold
over `finRange m'` (`m = m'`), the mask carried across by the inverse cast. -/
theorem foldl_transport {m m' : Nat} (hmm : m = m') (mask : Fin m → Bool)
    (specStab : Fin m → Pauli) (srcStab : Fin m' → Pauli)
    (hstab : ∀ i, specStab i = srcStab (Fin.cast hmm i)) (init : Pauli) :
    (List.finRange m).foldl
        (fun acc i => if mask i then pauliMul acc (specStab i) else acc) init =
      (List.finRange m').foldl
        (fun acc i' => if mask (Fin.cast hmm.symm i') then pauliMul acc (srcStab i') else acc)
        init := by
  have hstep : (fun acc (i : Fin m) => if mask i then pauliMul acc (specStab i) else acc)
      = (fun acc i => if mask i then pauliMul acc (srcStab (Fin.cast hmm i)) else acc) := by
    funext acc i; rw [hstab i]
  rw [hstep]
  cases hmm
  rfl

/-- If every selected generator is `I`, the `pauliMul`-fold is the initial
value. -/
theorem foldl_pauliMul_allI {ι : Type} (mask : ι → Bool) (g : ι → Pauli) :
    ∀ (l : List ι), (∀ i ∈ l, g i = Pauli.I) → ∀ (init : Pauli),
      l.foldl (fun acc i => if mask i then pauliMul acc (g i) else acc) init = init := by
  intro l
  induction l with
  | nil => intro _ init; rfl
  | cons a rest ih =>
      intro hg init
      simp only [List.foldl_cons]
      rw [ih (fun i hi => hg i (List.mem_cons.mpr (Or.inr hi)))]
      by_cases hm : mask a = true
      · rw [if_pos hm, hg a (List.mem_cons.mpr (Or.inl rfl)), pauliMul_I_right]
      · rw [if_neg hm]

/-- Reindex a `∀` over `Fin m` (with a `Fin.cast`) to a `∀` over `Fin m'`
(`m = m'`). -/
theorem Fin_cast_forall_iff {m m' : Nat} (h : m = m') (Q : Fin m' → Prop) :
    (∀ i : Fin m, Q (Fin.cast h i)) ↔ (∀ j : Fin m', Q j) := by
  constructor
  · intro H j
    have := H (Fin.cast h.symm j)
    rwa [show Fin.cast h (Fin.cast h.symm j) = j from Fin.ext rfl] at this
  · intro H i; exact H (Fin.cast h i)

/-- Mirror of `measuresAtAux_seqMeas_map_schedule` for the `.scheme` projection: every
measured block of a `seqMeas`-shaped program is `Scheme.NZ`. -/
theorem measuresAtAux_seqMeas_map_scheme {n th tf : Nat} {α : Type}
    (g : α → RuleSchedule n) :
    ∀ (L : List α) (hs ds : Nat)
      (fit : hs + programHelperCount
        (L.foldr (fun a acc => XZProgram.seq (.meas Scheme.NZ (g a)) acc) XZProgram.skip) ≤ th)
      (dfit : ds + programDetectorCount
        (L.foldr (fun a acc => XZProgram.seq (.meas Scheme.NZ (g a)) acc) XZProgram.skip) ≤ tf),
      ((programMeasuresAtAux (totalHelpers := th) (totalFlags := tf) hs ds
        (L.foldr (fun a acc => XZProgram.seq (.meas Scheme.NZ (g a)) acc) XZProgram.skip)
        fit dfit).map (·.scheme)) = L.map (fun _ => Scheme.NZ) := by
  intro L
  induction L with
  | nil => intro hs ds fit dfit; rfl
  | cons a rest ih =>
      intro hs ds fit dfit
      simp only [List.foldr_cons, programMeasuresAtAux, List.map_cons, List.singleton_append]
      exact congrArg (Scheme.NZ :: ·) (ih _ _ _ _)

-- Regression guards (axiom pins).
/-- info: 'QStab.QClifford.Compile.foldl_ev_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms foldl_ev_apply

/--
info: 'QStab.QClifford.Compile.qecMaskProd_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qecMaskProd_apply

/-- info: 'QStab.QClifford.Compile.foldl_transport' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms foldl_transport

/-- info: 'QStab.QClifford.Compile.foldl_pauliMul_allI' depends on axioms: [propext] -/
#guard_msgs in
#print axioms foldl_pauliMul_allI

/-- info: 'QStab.QClifford.Compile.Fin_cast_forall_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Fin_cast_forall_iff

end QStab.QClifford.Compile
