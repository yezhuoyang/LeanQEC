import QStab.QHL.CodeLang

/-!
# HGP(Rep(d), Rep(d)) schedule programs: order and length

The two object-language programs that drive the code-blind compiler front-end
(`xzProgramOfPrograms`) for the HGP family, plus their certified evaluations.

Order convention (pinned against `HGP13PCC.hookErrors`'s suffix structure):
**globally ascending qubit index** — the check's sector-1 qubits in ascending
order, then its sector-2 qubits in ascending order.  For the X-check
`(i, j) = (k/d, k%d)` that is rows `i, i+1` of column `j`, then row `i`'s
sector-2 columns `{j-1, j} ∩ [0, d-2]`; for the Z-check `(a, j)` (div/mod of
`k - (d-1)·d` by `d-1`) it is columns `j, j+1` of row `a`, then column `j`'s
sector-2 rows `{a-1, a} ∩ [0, d-2]`.  Schedule length is `3` for boundary
checks and `4` for interior ones (`len = 2 + |{c-1, c} ∩ [0, d-2]|`, `c` the
X-column resp. Z-row index).

* `hgpSupportList` / `hgpLenFlat` / `hgpOrderFlat` — the list-based reference.
* `hgpOrderProg : Term 3 .nat`, `hgpLenProg : Term 2 .nat` — the object
  programs (env `j = var 0, k = var 1, d = var 2` resp. `k = var 0,
  d = var 1`, as for `nzOrderProg`/`nzLenProg`; no `recCall`, so evaluation is
  fuel- and codeBody-irrelevant).
* `hgpOrderProg_eval` / `hgpLenProg_eval` — certified evaluation to the
  reference, via the arithmetic mirrors (identical tree, identical condition
  order) and the `split_ifs`-alignment recipe.
-/

namespace QHL.CodeHGPSchedule

open QHL.CodeLang

/-! ## The list-based reference -/

/-- The support of generator `k` in schedule order (ascending qubit index):
    two sector-1 qubits, then the one or two sector-2 qubits. -/
def hgpSupportList (d k : Nat) : List Nat :=
  if k < (d - 1) * d then
    [d * (k / d) + k % d, d * (k / d + 1) + k % d]
      ++ (if 1 ≤ k % d then [d * d + k / d * (d - 1) + (k % d - 1)] else [])
      ++ (if k % d ≤ d - 2 then [d * d + k / d * (d - 1) + k % d] else [])
  else
    [d * ((k - (d - 1) * d) / (d - 1)) + (k - (d - 1) * d) % (d - 1),
     d * ((k - (d - 1) * d) / (d - 1)) + ((k - (d - 1) * d) % (d - 1) + 1)]
      ++ (if 1 ≤ (k - (d - 1) * d) / (d - 1) then
            [d * d + ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1)
              + (k - (d - 1) * d) % (d - 1)]
          else [])
      ++ (if (k - (d - 1) * d) / (d - 1) ≤ d - 2 then
            [d * d + (k - (d - 1) * d) / (d - 1) * (d - 1)
              + (k - (d - 1) * d) % (d - 1)]
          else [])

/-- Reference schedule length: `3` on the boundary, `4` in the interior. -/
def hgpLenFlat (d k : Nat) : Nat := (hgpSupportList d k).length

/-- Reference order: the `j`-th scheduled qubit, sentinel `d² + (d-1)²`
    (the qubit count) out of range. -/
def hgpOrderFlat (d k j : Nat) : Nat :=
  (hgpSupportList d k)[j]?.getD (d * d + (d - 1) * (d - 1))

/-! ## The object programs -/

/-- HGP order program: `(d, k, j) ↦` the `j`-th scheduled qubit.
    Env: `j = var 0`, `k = var 1`, `d = var 2`.  No `recCall`. -/
def hgpOrderProg : Term 3 .nat :=
  let J : Term 3 .nat := .var 0
  let K : Term 3 .nat := .var 1
  let D : Term 3 .nat := .var 2
  let one : Term 3 .nat := .natLit 1
  let dm1 : Term 3 .nat := .sub D one
  let A : Term 3 .nat := .mul dm1 D
  let DD : Term 3 .nat := .mul D D
  let sentinel : Term 3 .nat := .add DD (.mul dm1 dm1)
  let I : Term 3 .nat := .div K D
  let Jc : Term 3 .nat := .mod K D
  let s2xBase : Term 3 .nat := .add DD (.mul I dm1)
  let T : Term 3 .nat := .sub K A
  let Za : Term 3 .nat := .div T dm1
  let Zj : Term 3 .nat := .mod T dm1
  let s2zBase : Term 3 .nat := .add DD (.mul Za dm1)
  let s2zBaseM : Term 3 .nat := .add DD (.mul (.sub Za one) dm1)
  .ite (.ltNat K A)
    (.ite (.eqNat J (.natLit 0)) (.add (.mul D I) Jc)
      (.ite (.eqNat J (.natLit 1)) (.add (.mul D (.add I one)) Jc)
        (.ite (.eqNat J (.natLit 2))
          (.ite (.eqNat Jc (.natLit 0)) (.add s2xBase Jc)
            (.add s2xBase (.sub Jc one)))
          (.ite (.eqNat J (.natLit 3))
            (.ite (.and (.leNat one Jc) (.leNat Jc (.sub D (.natLit 2))))
              (.add s2xBase Jc) sentinel)
            sentinel))))
    (.ite (.eqNat J (.natLit 0)) (.add (.mul D Za) Zj)
      (.ite (.eqNat J (.natLit 1)) (.add (.mul D Za) (.add Zj one))
        (.ite (.eqNat J (.natLit 2))
          (.ite (.eqNat Za (.natLit 0)) (.add s2zBase Zj) (.add s2zBaseM Zj))
          (.ite (.eqNat J (.natLit 3))
            (.ite (.and (.leNat one Za) (.leNat Za (.sub D (.natLit 2))))
              (.add s2zBase Zj) sentinel)
            sentinel))))

/-- HGP length program: `(d, k) ↦ 3` on the boundary, `4` in the interior.
    Env: `k = var 0`, `d = var 1`.  No `recCall`. -/
def hgpLenProg : Term 2 .nat :=
  let K : Term 2 .nat := .var 0
  let D : Term 2 .nat := .var 1
  let one : Term 2 .nat := .natLit 1
  let dm1 : Term 2 .nat := .sub D one
  let A : Term 2 .nat := .mul dm1 D
  let Za : Term 2 .nat := .div (.sub K A) dm1
  .ite (.ltNat K A)
    (.ite (.eqNat (.mod K D) (.natLit 0)) (.natLit 3)
      (.ite (.eqNat (.mod K D) dm1) (.natLit 3) (.natLit 4)))
    (.ite (.eqNat Za (.natLit 0)) (.natLit 3)
      (.ite (.eqNat Za dm1) (.natLit 3) (.natLit 4)))

/-! ## Pins at `d = 3` (the `[[13,1,3]]` order table, before any proof)

Cross-checked against `HGP13PCC.hookErrors`'s suffix convention: e.g. `k = 8`
order `[3, 4, 9, 11]` has proper suffixes `{4,9,11}, {9,11}, {11}` — exactly
its hook list. -/

/-- info: [3, 4, 3, 3, 4, 3, 3, 3, 4, 4, 3, 3] -/
#guard_msgs in
#eval (List.range 12).map (hgpLenFlat 3)

/-- info: true -/
#guard_msgs in
#eval (List.range 12).map (fun k => (List.range (hgpLenFlat 3 k)).map (hgpOrderFlat 3 k))
  == [[0, 3, 9], [1, 4, 9, 10], [2, 5, 10], [3, 6, 11], [4, 7, 11, 12], [5, 8, 12],
      [0, 1, 9], [1, 2, 10], [3, 4, 9, 11], [4, 5, 10, 12], [6, 7, 11], [7, 8, 12]]

-- The object programs agree with the reference at d = 3 (all checks, all slots
-- incl. out-of-range), under an arbitrary codeBody and fuel:
/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun k => (List.range 6).all fun j =>
  Term.eval (.stabLam (.pauliLit Pauli.I)) 0 hgpOrderProg
      (Env.cons j (Env.code 3 k)) == some (hgpOrderFlat 3 k j)
/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun k =>
  Term.eval (.stabLam (.pauliLit Pauli.I)) 0 hgpLenProg (Env.code 3 k)
    == some (hgpLenFlat 3 k)

/-! ## Certified evaluation -/

private lemma env3_zero (j d k : Nat) : (Env.cons j (Env.code d k)) 0 = j := rfl
private lemma env3_one (j d k : Nat) : (Env.cons j (Env.code d k)) 1 = k := rfl
private lemma env3_two (j d k : Nat) : (Env.cons j (Env.code d k)) 2 = d := rfl
private lemma env2_zero (d k : Nat) : (Env.code d k) 0 = k := rfl
private lemma env2_one (d k : Nat) : (Env.code d k) 1 = d := rfl

/-- Arithmetic mirror of `hgpOrderProg` — identical tree, identical condition
    order. -/
def hgpOrderArith (d k j : Nat) : Nat :=
  if k < (d - 1) * d then
    if j = 0 then d * (k / d) + k % d
    else if j = 1 then d * (k / d + 1) + k % d
    else if j = 2 then
      if k % d = 0 then d * d + k / d * (d - 1) + k % d
      else d * d + k / d * (d - 1) + (k % d - 1)
    else if j = 3 then
      if 1 ≤ k % d ∧ k % d ≤ d - 2 then d * d + k / d * (d - 1) + k % d
      else d * d + (d - 1) * (d - 1)
    else d * d + (d - 1) * (d - 1)
  else
    if j = 0 then d * ((k - (d - 1) * d) / (d - 1)) + (k - (d - 1) * d) % (d - 1)
    else if j = 1 then
      d * ((k - (d - 1) * d) / (d - 1)) + ((k - (d - 1) * d) % (d - 1) + 1)
    else if j = 2 then
      if (k - (d - 1) * d) / (d - 1) = 0 then
        d * d + (k - (d - 1) * d) / (d - 1) * (d - 1) + (k - (d - 1) * d) % (d - 1)
      else
        d * d + ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1) + (k - (d - 1) * d) % (d - 1)
    else if j = 3 then
      if 1 ≤ (k - (d - 1) * d) / (d - 1) ∧ (k - (d - 1) * d) / (d - 1) ≤ d - 2 then
        d * d + (k - (d - 1) * d) / (d - 1) * (d - 1) + (k - (d - 1) * d) % (d - 1)
      else d * d + (d - 1) * (d - 1)
    else d * d + (d - 1) * (d - 1)

/-- Arithmetic mirror of `hgpLenProg`. -/
def hgpLenArith (d k : Nat) : Nat :=
  if k < (d - 1) * d then
    if k % d = 0 then 3 else if k % d = d - 1 then 3 else 4
  else
    if (k - (d - 1) * d) / (d - 1) = 0 then 3
    else if (k - (d - 1) * d) / (d - 1) = d - 1 then 3 else 4

/-- **Certified evaluation of `hgpOrderProg`** to its arithmetic mirror.
    Fuel- and codeBody-irrelevant (no `recCall`). -/
theorem hgpOrderProg_eval_arith (cb : Term 2 .stab) (fuel : Nat) (d k j : Nat) :
    Term.eval cb fuel hgpOrderProg (Env.cons j (Env.code d k))
      = some (hgpOrderArith d k j) := by
  simp only [hgpOrderProg, hgpOrderArith, Term.eval, env3_zero, env3_one, env3_two,
    bind, Option.bind, decide_eq_true_eq]
  split_ifs <;> simp [*] <;> tauto

/-- **Certified evaluation of `hgpLenProg`** to its arithmetic mirror. -/
theorem hgpLenProg_eval_arith (cb : Term 2 .stab) (fuel : Nat) (d k : Nat) :
    Term.eval cb fuel hgpLenProg (Env.code d k) = some (hgpLenArith d k) := by
  simp only [hgpLenProg, hgpLenArith, Term.eval, env2_zero, env2_one,
    bind, Option.bind, decide_eq_true_eq]
  split_ifs <;> simp [*]

/-! ## Reconciliation with the list-based reference

Guarded by `2 ≤ d` and `k < 2·(d-1)·d` — the generator only ever evaluates
in-range generators of nondegenerate codes. -/

/-- The mirror lengths agree with the reference lengths. -/
theorem hgpLenFlat_eq_arith (d k : Nat) (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    hgpLenFlat d k = hgpLenArith d k := by
  unfold hgpLenFlat hgpSupportList hgpLenArith
  by_cases hx : k < (d - 1) * d
  · rw [if_pos hx, if_pos hx]
    have hj : k % d < d := Nat.mod_lt _ (by omega)
    by_cases hj0 : k % d = 0
    · rw [if_pos hj0]
      rw [if_neg (by omega), if_pos (by omega)]
      simp
    · rw [if_neg hj0]
      by_cases hjd : k % d = d - 1
      · rw [if_pos hjd, if_pos (by omega), if_neg (by omega)]
        simp
      · rw [if_neg hjd, if_pos (by omega), if_pos (by omega)]
        simp
  · rw [if_neg hx, if_neg hx]
    have hd1 : 0 < d - 1 := by omega
    have ht : k - (d - 1) * d < (d - 1) * d := by omega
    have ha : (k - (d - 1) * d) / (d - 1) < d :=
      (Nat.div_lt_iff_lt_mul hd1).mpr (by rw [Nat.mul_comm d (d - 1)]; exact ht)
    by_cases ha0 : (k - (d - 1) * d) / (d - 1) = 0
    · rw [if_pos ha0]
      simp [ha0]
    · rw [if_neg ha0]
      by_cases had : (k - (d - 1) * d) / (d - 1) = d - 1
      · have h1 : 1 ≤ (k - (d - 1) * d) / (d - 1) := Nat.one_le_iff_ne_zero.mpr ha0
        have h2 : ¬(k - (d - 1) * d) / (d - 1) ≤ d - 2 := by rw [had]; omega
        rw [if_pos had]
        simp [h1, h2]
      · have h1 : 1 ≤ (k - (d - 1) * d) / (d - 1) := Nat.one_le_iff_ne_zero.mpr ha0
        have h2 : (k - (d - 1) * d) / (d - 1) ≤ d - 2 :=
          Nat.sub_sub d 1 1 ▸
            Nat.le_pred_of_lt (Nat.lt_of_le_of_ne (Nat.le_pred_of_lt ha) had)
        rw [if_neg had]
        simp [h1, h2]

/-- The mirror orders agree with the reference orders. -/
theorem hgpOrderFlat_eq_arith (d k j : Nat) (hd : 2 ≤ d)
    (hk : k < 2 * ((d - 1) * d)) :
    hgpOrderFlat d k j = hgpOrderArith d k j := by
  unfold hgpOrderFlat hgpSupportList hgpOrderArith
  by_cases hx : k < (d - 1) * d
  · rw [if_pos hx, if_pos hx]
    have hj : k % d < d := Nat.mod_lt _ (by omega)
    by_cases hj0 : k % d = 0
    · have h1 : ¬1 ≤ k % d := by omega
      have h2 : k % d ≤ d - 2 := by omega
      have hg : ¬(1 ≤ k % d ∧ k % d ≤ d - 2) := by intro h; omega
      rcases j with _ | _ | _ | _ | j <;> simp [hj0]
    · by_cases hjd : k % d = d - 1
      · have h1 : 1 ≤ k % d := by omega
        have h2 : ¬k % d ≤ d - 2 := by omega
        rcases j with _ | _ | _ | _ | j <;> simp [hj0, h1, h2]
      · have h1 : 1 ≤ k % d := by omega
        have h2 : k % d ≤ d - 2 := by omega
        rcases j with _ | _ | _ | _ | j <;> simp [hj0, h1, h2]
  · rw [if_neg hx, if_neg hx]
    have hd1 : 0 < d - 1 := by omega
    have ht : k - (d - 1) * d < (d - 1) * d := by omega
    have ha : (k - (d - 1) * d) / (d - 1) < d :=
      (Nat.div_lt_iff_lt_mul hd1).mpr (by rw [Nat.mul_comm d (d - 1)]; exact ht)
    by_cases ha0 : (k - (d - 1) * d) / (d - 1) = 0
    · rcases j with _ | _ | _ | _ | j <;> simp [ha0]
    · by_cases had : (k - (d - 1) * d) / (d - 1) = d - 1
      · have h1 : 1 ≤ (k - (d - 1) * d) / (d - 1) := Nat.one_le_iff_ne_zero.mpr ha0
        have h2 : ¬(k - (d - 1) * d) / (d - 1) ≤ d - 2 := by rw [had]; omega
        rcases j with _ | _ | _ | _ | j <;> simp [ha0, h1, h2]
      · have h1 : 1 ≤ (k - (d - 1) * d) / (d - 1) := Nat.one_le_iff_ne_zero.mpr ha0
        have h2 : (k - (d - 1) * d) / (d - 1) ≤ d - 2 :=
          Nat.sub_sub d 1 1 ▸
            Nat.le_pred_of_lt (Nat.lt_of_le_of_ne (Nat.le_pred_of_lt ha) had)
        rcases j with _ | _ | _ | _ | j <;> simp [ha0, h1, h2]

/-- **`hgpOrderProg` evaluates to the reference order.** -/
theorem hgpOrderProg_eval (cb : Term 2 .stab) (fuel : Nat) (d k j : Nat)
    (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    Term.eval cb fuel hgpOrderProg (Env.cons j (Env.code d k))
      = some (hgpOrderFlat d k j) := by
  rw [hgpOrderProg_eval_arith, hgpOrderFlat_eq_arith d k j hd hk]

/-- **`hgpLenProg` evaluates to the reference length.** -/
theorem hgpLenProg_eval (cb : Term 2 .stab) (fuel : Nat) (d k : Nat)
    (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    Term.eval cb fuel hgpLenProg (Env.code d k) = some (hgpLenFlat d k) := by
  rw [hgpLenProg_eval_arith, hgpLenFlat_eq_arith d k hd hk]

#print axioms hgpOrderProg_eval
#print axioms hgpLenProg_eval

/-! ## Support-list facts for the compiled side

In-range, length window, and Nodup — the classification inputs the generic
per-gadget site classifiers consume. -/

/-- Every scheduled qubit is a real qubit: `q < d² + (d-1)²`. -/
theorem hgpSupportList_lt (d k : Nat) (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    ∀ q ∈ hgpSupportList d k, q < d * d + (d - 1) * (d - 1) := by
  intro q hq
  unfold hgpSupportList at hq
  by_cases hx : k < (d - 1) * d
  · rw [if_pos hx] at hq
    have hi : k / d < d - 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hx
    have hj : k % d < d := Nat.mod_lt _ (by omega)
    have hs1 : d * (k / d + 1) + k % d < d * d := by
      calc d * (k / d + 1) + k % d < d * (k / d + 1) + d := by omega
        _ = d * (k / d + 1 + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    have hs0 : d * (k / d) + k % d < d * d := by
      have hstep : d * (k / d) ≤ d * (k / d + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hrow : k / d * (d - 1) ≤ (d - 2) * (d - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hdd : (d - 2) * (d - 1) + (d - 1) = (d - 1) * (d - 1) := by
      have h21 : Nat.succ (d - 2) = d - 1 := by omega
      rw [Nat.mul_comm (d - 2) (d - 1), ← Nat.mul_succ, h21]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with ((rfl | rfl) | hq) | hq
    · omega
    · omega
    · by_cases hg : 1 ≤ k % d
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        omega
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim
    · by_cases hg : k % d ≤ d - 2
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        omega
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim
  · rw [if_neg hx] at hq
    have hd1 : 0 < d - 1 := by omega
    have ht : k - (d - 1) * d < (d - 1) * d := by omega
    have ha : (k - (d - 1) * d) / (d - 1) < d :=
      (Nat.div_lt_iff_lt_mul hd1).mpr (by rw [Nat.mul_comm d (d - 1)]; exact ht)
    have hjz : (k - (d - 1) * d) % (d - 1) < d - 1 := Nat.mod_lt _ hd1
    have hs1 : d * ((k - (d - 1) * d) / (d - 1))
        + ((k - (d - 1) * d) % (d - 1) + 1) < d * d := by
      calc d * ((k - (d - 1) * d) / (d - 1)) + ((k - (d - 1) * d) % (d - 1) + 1)
          < d * ((k - (d - 1) * d) / (d - 1)) + d := by omega
        _ = d * ((k - (d - 1) * d) / (d - 1) + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    have hdd : (d - 2) * (d - 1) + (d - 1) = (d - 1) * (d - 1) := by
      have h21 : Nat.succ (d - 2) = d - 1 := by omega
      rw [Nat.mul_comm (d - 2) (d - 1), ← Nat.mul_succ, h21]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with ((rfl | rfl) | hq) | hq
    · omega
    · omega
    · by_cases hg : 1 ≤ (k - (d - 1) * d) / (d - 1)
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have hrow : ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1)
            ≤ (d - 2) * (d - 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim
    · by_cases hg : (k - (d - 1) * d) / (d - 1) ≤ d - 2
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have hrow : (k - (d - 1) * d) / (d - 1) * (d - 1)
            ≤ (d - 2) * (d - 1) := Nat.mul_le_mul_right _ hg
        omega
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim

/-- The schedule length window: `3 ≤ len ≤ 4`. -/
theorem hgpLenFlat_window (d k : Nat) (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    3 ≤ hgpLenFlat d k ∧ hgpLenFlat d k ≤ 4 := by
  rw [hgpLenFlat_eq_arith d k hd hk]
  unfold hgpLenArith
  split_ifs <;> omega

/-- In range, the reference order is a support-list member. -/
theorem hgpOrderFlat_mem (d k j : Nat) (hj : j < hgpLenFlat d k) :
    hgpOrderFlat d k j ∈ hgpSupportList d k := by
  unfold hgpOrderFlat
  rw [List.getElem?_eq_getElem hj]
  exact List.getElem_mem _

/-- In range, the reference order is a genuine qubit index. -/
theorem hgpOrderFlat_lt_nQ (d k j : Nat) (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d))
    (hj : j < hgpLenFlat d k) :
    hgpOrderFlat d k j < d * d + (d - 1) * (d - 1) :=
  hgpSupportList_lt d k hd hk _ (hgpOrderFlat_mem d k j hj)

/-- No qubit is scheduled twice within a check. -/
theorem hgpSupportList_nodup (d k : Nat) (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    (hgpSupportList d k).Nodup := by
  unfold hgpSupportList
  by_cases hx : k < (d - 1) * d
  · rw [if_pos hx]
    have hi : k / d < d - 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hx
    have hj : k % d < d := Nat.mod_lt _ (by omega)
    have hs1 : d * (k / d + 1) + k % d < d * d := by
      calc d * (k / d + 1) + k % d < d * (k / d + 1) + d := by omega
        _ = d * (k / d + 1 + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    have hstep : d * (k / d) < d * (k / d + 1) := by
      rw [Nat.mul_succ]; omega
    split_ifs with h1 h2 h2 <;> simp <;> omega
  · rw [if_neg hx]
    have hd1 : 0 < d - 1 := by omega
    have ht : k - (d - 1) * d < (d - 1) * d := by omega
    have ha : (k - (d - 1) * d) / (d - 1) < d :=
      (Nat.div_lt_iff_lt_mul hd1).mpr (by rw [Nat.mul_comm d (d - 1)]; exact ht)
    have hjz : (k - (d - 1) * d) % (d - 1) < d - 1 := Nat.mod_lt _ hd1
    have hs1 : d * ((k - (d - 1) * d) / (d - 1))
        + ((k - (d - 1) * d) % (d - 1) + 1) < d * d := by
      calc d * ((k - (d - 1) * d) / (d - 1)) + ((k - (d - 1) * d) % (d - 1) + 1)
          < d * ((k - (d - 1) * d) / (d - 1)) + d := by omega
        _ = d * ((k - (d - 1) * d) / (d - 1) + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    have hrowlt : 1 ≤ (k - (d - 1) * d) / (d - 1) →
        ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1) + (k - (d - 1) * d) % (d - 1)
        < (k - (d - 1) * d) / (d - 1) * (d - 1) := by
      intro hA
      calc ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1)
            + (k - (d - 1) * d) % (d - 1)
          < ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1) + (d - 1) := by omega
        _ = ((k - (d - 1) * d) / (d - 1) - 1 + 1) * (d - 1) := (Nat.succ_mul _ _).symm
        _ ≤ (k - (d - 1) * d) / (d - 1) * (d - 1) :=
            Nat.mul_le_mul_right _ (Nat.le_of_eq (Nat.sub_add_cancel hA))
    -- name the div-products (and the div itself) so the final linear
    -- arithmetic sees only plain variables
    generalize hp0 : d * ((k - (d - 1) * d) / (d - 1)) = Q at hs1 ⊢
    generalize hp1 : ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1) = P1 at hrowlt ⊢
    generalize hp2 : (k - (d - 1) * d) / (d - 1) * (d - 1) = P2 at hrowlt ⊢
    generalize hpa : (k - (d - 1) * d) / (d - 1) = Av at hrowlt ⊢
    split_ifs with h1 h2 h2 <;> simp <;> omega

end QHL.CodeHGPSchedule
