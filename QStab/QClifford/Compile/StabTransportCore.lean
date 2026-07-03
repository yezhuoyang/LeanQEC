import QStab.QClifford.Compile.SurfaceNZStabBridge

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

These are **public**: the surface transport (`SurfaceNZStabTransport`) proved
private copies, which was a confirmed reuse obstacle; new code instantiates
this file, and the surface file can be back-ported onto it.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC

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

end QStab.QClifford.Compile
