import QStab.Examples.HGPCode
import QStab.Examples.SurfaceGeneral
import QStab.Examples.SurfaceRowEquiv
import QStab.QHL.Source.Examples.HGP

/-! # The HGP(Rep(d), Rep(d)) family: a parametric `HGPSpec d` for every `d ≥ 2`

Hypergraph product of two length-`d` repetition codes, the
`[[d² + (d-1)², 1, d]]` family — `[[13,1,3]]` at `d = 3` (`HGPCode.lean`).
This module replaces the fixed-`d` enumeration proofs of `HGP13PCC.lean`
(`fin_cases`/`decide` over 12 stabilizers × 13 qubits) with structural proofs
over the tensor formulas, valid at every distance.

Layout: sector 1 (bit-type) is the `d × d` block `q < d²` at `(q/d, q%d)`;
sector 2 (check-type) holds the remaining `(d-1)²` qubits at
`((q-d²)/(d-1), (q-d²)%(d-1))`.  Generators `k < (d-1)·d` are X-type at
`(i, j) = (k/d, k%d)`; the rest are Z-type at `(a, j)` by the same div/mod
split of `k - (d-1)·d`.  From `H_X = (H⊗I | I⊗Hᵀ)`, `H_Z = (I⊗H | Hᵀ⊗I)`:

* X-generator `(i, j)`: sector-1 `X` at rows `{i, i+1}` of **column `j`**
  (the hook-alignment fact), sector-2 `X` at columns `{j-1, j}` of row `i`.
* Z-generator `(a, j)`: sector-1 `Z` at columns `{j, j+1}` of row `a`,
  sector-2 `Z` at rows `{a-1, a}` of column `j`.

The back-action set is **schedule-independent**: every error pointwise
dominated by the generator (`e q ∈ {I, T_s q}`).  This contains the mid-CNOT
suffix hooks of *every* gate ordering as well as the generator itself, so the
`hook_in_column` proof below covers any extraction schedule — the reason HGP
codes preserve circuit distance unconditionally (Manes–Claes), unlike the
surface code's NZ requirement.

**Stage**: this is the *source-level* (pre-compiler) distance milestone, over
the QStab abstract machine.  The stabilizers here are the meta-level entry
formula `stabEntry`; the certified-evaluation anchor to the object-language
program `QHL.CodeLang.HGP.code` and the compiled-circuit statements
(schedule programs, `compileProgram`, site classification, VCGen slots) are
the subsequent pipeline stages, as for the surface code. -/

namespace QStab.Examples.HGPParametric

open QStab QStab.Examples QStab.Examples.SurfaceGeneral

/-! ## Parametric definitions -/

/-- Physical qubit count `d² + (d-1)²`. -/
def hgpN (d : Nat) : Nat := d * d + (d - 1) * (d - 1)

/-- Total generator count `2·(d-1)·d`; the first `(d-1)·d` are X-type. -/
def hgpNumStab (d : Nat) : Nat := 2 * ((d - 1) * d)

/-- Stabilizer entry `(d, k, q) ↦ Pauli`: the meta-level mirror of the
    object-language program `QHL.CodeLang.HGP.hgpEntryAST` (same branch tree,
    same condition order — the future certified-evaluation bridge aligns the
    two trees `if`-for-`ite`). -/
def stabEntry (d k q : Nat) : Pauli :=
  if k < 2 * ((d - 1) * d) ∧ q < d * d + (d - 1) * (d - 1) then
    if k < (d - 1) * d then
      if q < d * d then
        if q % d = k % d ∧ (q / d = k / d ∨ q / d = k / d + 1) then .X else .I
      else
        if (q - d * d) / (d - 1) = k / d ∧
            ((q - d * d) % (d - 1) = k % d ∨
             (q - d * d) % (d - 1) + 1 = k % d) then .X
        else .I
    else
      if q < d * d then
        if q / d = (k - (d - 1) * d) / (d - 1) ∧
            (q % d = (k - (d - 1) * d) % (d - 1) ∨
             q % d = (k - (d - 1) * d) % (d - 1) + 1) then .Z
        else .I
      else
        if (q - d * d) % (d - 1) = (k - (d - 1) * d) % (d - 1) ∧
            ((q - d * d) / (d - 1) = (k - (d - 1) * d) / (d - 1) ∨
             (q - d * d) / (d - 1) + 1 = (k - (d - 1) * d) / (d - 1)) then .Z
        else .I
  else .I

/-- The parametric generator family. -/
def mkHGPRepStabilizers (d : Nat) : Fin (hgpNumStab d) → ErrorVec (hgpN d) :=
  fun k q => stabEntry d k.val q.val

/-- Logical Z̄: `Z` on sector-1 column 0 (`{(a, 0) : a < d}`). -/
def mkHGPRepLogicalZ (d : Nat) : ErrorVec (hgpN d) :=
  fun q => if q.val < d * d ∧ q.val % d = 0 then .Z else .I

/-- Column map: sector-1 qubit `(a, b) ↦ some b`, sector-2 ↦ `none`. -/
def hgpCol (d : Nat) (hd : 0 < d) : Fin (hgpN d) → Option (Fin d) :=
  fun q => if q.val < d * d then some ⟨q.val % d, Nat.mod_lt _ hd⟩ else none

/-- Column-cut `Ẑ_j`: `Z` on sector-1 column `j`, `I` elsewhere. -/
def mkHGPRepCutOp (d : Nat) : Fin d → ErrorVec (hgpN d) :=
  fun j q => if q.val < d * d ∧ q.val % d = j.val then .Z else .I

/-- Schedule-independent back-action set: every error pointwise dominated by
    the generator.  Contains the mid-CNOT suffixes of every gate ordering and
    the generator itself (pre-first-CNOT ancilla fault). -/
def hgpBackAction (d : Nat) (k : Fin (hgpNumStab d)) : Set (ErrorVec (hgpN d)) :=
  { e | ∀ q, e q = Pauli.I ∨ e q = mkHGPRepStabilizers d k q }

/-! ## Entry classification and support -/

/-- X-generator entries are `I` or `X`. -/
theorem stabEntry_X_type (d k q : Nat) (hk : k < (d - 1) * d) :
    stabEntry d k q = .I ∨ stabEntry d k q = .X := by
  unfold stabEntry
  by_cases hg : k < 2 * ((d - 1) * d) ∧ q < d * d + (d - 1) * (d - 1)
  · rw [if_pos hg, if_pos hk]
    by_cases hs1 : q < d * d
    · rw [if_pos hs1]; split_ifs <;> simp
    · rw [if_neg hs1]; split_ifs <;> simp
  · rw [if_neg hg]; left; rfl

/-- Z-generator entries are `I` or `Z`. -/
theorem stabEntry_Z_type (d k q : Nat) (hk : (d - 1) * d ≤ k) :
    stabEntry d k q = .I ∨ stabEntry d k q = .Z := by
  unfold stabEntry
  by_cases hg : k < 2 * ((d - 1) * d) ∧ q < d * d + (d - 1) * (d - 1)
  · rw [if_pos hg, if_neg (Nat.not_lt.mpr hk)]
    by_cases hs1 : q < d * d
    · rw [if_pos hs1]; split_ifs <;> simp
    · rw [if_neg hs1]; split_ifs <;> simp
  · rw [if_neg hg]; left; rfl

/-- A supported sector-1 qubit of X-generator `k` lies in column `k % d`. -/
theorem stabEntry_X_s1_col (d k q : Nat) (hk : k < (d - 1) * d) (hq : q < d * d)
    (h : stabEntry d k q ≠ .I) : q % d = k % d := by
  unfold stabEntry at h
  by_cases hg : k < 2 * ((d - 1) * d) ∧ q < d * d + (d - 1) * (d - 1)
  · rw [if_pos hg, if_pos hk, if_pos hq] at h
    by_cases hm : q % d = k % d ∧ (q / d = k / d ∨ q / d = k / d + 1)
    · exact hm.1
    · rw [if_neg hm] at h; exact absurd rfl h
  · rw [if_neg hg] at h; exact absurd rfl h

/-- The support of X-generator `k` (four explicit candidates:
    sector-1 rows `{i, i+1}` of column `j`, sector-2 columns `{j, j-1}` of
    row `i`, for `(i, j) = (k/d, k%d)`). -/
theorem stabEntry_X_support (d k q : Nat) (hk : k < (d - 1) * d)
    (h : stabEntry d k q ≠ .I) :
    q = d * (k / d) + k % d ∨ q = d * (k / d + 1) + k % d ∨
    q = d * d + ((d - 1) * (k / d) + k % d) ∨
    q = d * d + ((d - 1) * (k / d) + (k % d - 1)) := by
  unfold stabEntry at h
  by_cases hg : k < 2 * ((d - 1) * d) ∧ q < d * d + (d - 1) * (d - 1)
  case neg => rw [if_neg hg] at h; exact absurd rfl h
  rw [if_pos hg, if_pos hk] at h
  by_cases hs1 : q < d * d
  · -- sector 1: q % d = k % d, q / d ∈ {k/d, k/d + 1}
    rw [if_pos hs1] at h
    by_cases hm : q % d = k % d ∧ (q / d = k / d ∨ q / d = k / d + 1)
    case neg => rw [if_neg hm] at h; exact absurd rfl h
    have hsplit := Nat.div_add_mod q d
    rcases hm.2 with hr | hr
    · left; rw [← hsplit, hr, hm.1]
    · right; left; rw [← hsplit, hr, hm.1]
  · -- sector 2: (q-d²)/(d-1) = k/d, (q-d²)%(d-1) ∈ {k%d, k%d - 1}
    rw [if_neg hs1] at h
    by_cases hm : (q - d * d) / (d - 1) = k / d ∧
        ((q - d * d) % (d - 1) = k % d ∨ (q - d * d) % (d - 1) + 1 = k % d)
    case neg => rw [if_neg hm] at h; exact absurd rfl h
    have hq2 : d * d ≤ q := Nat.le_of_not_lt hs1
    have hsplit := Nat.div_add_mod (q - d * d) (d - 1)
    rcases hm.2 with hc | hc
    · right; right; left
      have heq : (d - 1) * (k / d) + k % d = q - d * d := by rw [← hm.1, ← hc]; exact hsplit
      omega
    · right; right; right
      have hc' : (q - d * d) % (d - 1) = k % d - 1 := by omega
      have heq : (d - 1) * (k / d) + (k % d - 1) = q - d * d := by
        rw [← hm.1, ← hc']; exact hsplit
      omega

/-- The support of Z-generator `k` (four explicit candidates:
    sector-1 columns `{j, j+1}` of row `a`, sector-2 rows `{a, a-1}` of
    column `j`, for `(a, j)` the div/mod split of `t = k - (d-1)·d`). -/
theorem stabEntry_Z_support (d k q : Nat) (hk : (d - 1) * d ≤ k)
    (h : stabEntry d k q ≠ .I) :
    q = d * ((k - (d - 1) * d) / (d - 1)) + (k - (d - 1) * d) % (d - 1) ∨
    q = d * ((k - (d - 1) * d) / (d - 1)) + ((k - (d - 1) * d) % (d - 1) + 1) ∨
    q = d * d + ((d - 1) * ((k - (d - 1) * d) / (d - 1)) + (k - (d - 1) * d) % (d - 1)) ∨
    q = d * d + ((d - 1) * ((k - (d - 1) * d) / (d - 1) - 1) + (k - (d - 1) * d) % (d - 1)) := by
  unfold stabEntry at h
  by_cases hg : k < 2 * ((d - 1) * d) ∧ q < d * d + (d - 1) * (d - 1)
  case neg => rw [if_neg hg] at h; exact absurd rfl h
  rw [if_pos hg, if_neg (Nat.not_lt.mpr hk)] at h
  by_cases hs1 : q < d * d
  · -- sector 1: q / d = a, q % d ∈ {j, j+1}
    rw [if_pos hs1] at h
    by_cases hm : q / d = (k - (d - 1) * d) / (d - 1) ∧
        (q % d = (k - (d - 1) * d) % (d - 1) ∨ q % d = (k - (d - 1) * d) % (d - 1) + 1)
    case neg => rw [if_neg hm] at h; exact absurd rfl h
    have hsplit := Nat.div_add_mod q d
    rcases hm.2 with hc | hc
    · left; rw [← hsplit, hm.1, hc]
    · right; left; rw [← hsplit, hm.1, hc]
  · -- sector 2: (q-d²)%(d-1) = j, (q-d²)/(d-1) ∈ {a, a-1}
    rw [if_neg hs1] at h
    by_cases hm : (q - d * d) % (d - 1) = (k - (d - 1) * d) % (d - 1) ∧
        ((q - d * d) / (d - 1) = (k - (d - 1) * d) / (d - 1) ∨
         (q - d * d) / (d - 1) + 1 = (k - (d - 1) * d) / (d - 1))
    case neg => rw [if_neg hm] at h; exact absurd rfl h
    have hq2 : d * d ≤ q := Nat.le_of_not_lt hs1
    have hsplit := Nat.div_add_mod (q - d * d) (d - 1)
    rcases hm.2 with hr | hr
    · right; right; left
      have heq : (d - 1) * ((k - (d - 1) * d) / (d - 1)) + (k - (d - 1) * d) % (d - 1)
          = q - d * d := by rw [← hm.1, ← hr]; exact hsplit
      omega
    · right; right; right
      have hr' : (q - d * d) / (d - 1) = (k - (d - 1) * d) / (d - 1) - 1 :=
        Nat.eq_sub_of_add_eq hr
      have heq : (d - 1) * ((k - (d - 1) * d) / (d - 1) - 1) + (k - (d - 1) * d) % (d - 1)
          = q - d * d := by rw [← hm.1, ← hr']; exact hsplit
      omega

/-! ## Weight bound `r = 4` -/

private theorem weight_le_of_pointwise_dominated {n : Nat} {e f : ErrorVec n}
    (h : ∀ q, e q = Pauli.I ∨ e q = f q) : ErrorVec.weight e ≤ ErrorVec.weight f := by
  unfold ErrorVec.weight
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  rcases h q with h1 | h1
  · exact absurd h1 hq
  · exact h1 ▸ hq

private theorem card_quad_le {α : Type _} [DecidableEq α] (a b c e : α) :
    ({a, b, c, e} : Finset α).card ≤ 4 := by
  refine le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right ?_ 1)
  refine le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right ?_ 1)
  refine le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right ?_ 1)
  exact le_of_eq (Finset.card_singleton _)

/-- Every generator has weight at most 4 (two sector-1 and two sector-2
    candidates). -/
theorem weight_stab_le_four (d : Nat) (k : Fin (hgpNumStab d)) :
    ErrorVec.weight (mkHGPRepStabilizers d k) ≤ 4 := by
  unfold ErrorVec.weight
  rw [← Finset.card_image_of_injOn (f := Fin.val) (fun a _ b _ hab => Fin.ext hab)]
  rcases Nat.lt_or_ge k.val ((d - 1) * d) with hx | hz
  · refine le_trans (Finset.card_le_card ?_) (card_quad_le
        (d * (k.val / d) + k.val % d) (d * (k.val / d + 1) + k.val % d)
        (d * d + ((d - 1) * (k.val / d) + k.val % d))
        (d * d + ((d - 1) * (k.val / d) + (k.val % d - 1))))
    intro v hv
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨a, hane, rfl⟩ := hv
    have := stabEntry_X_support d k.val a.val hx hane
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine le_trans (Finset.card_le_card ?_) (card_quad_le
        (d * ((k.val - (d - 1) * d) / (d - 1)) + (k.val - (d - 1) * d) % (d - 1))
        (d * ((k.val - (d - 1) * d) / (d - 1)) + ((k.val - (d - 1) * d) % (d - 1) + 1))
        (d * d + ((d - 1) * ((k.val - (d - 1) * d) / (d - 1)) + (k.val - (d - 1) * d) % (d - 1)))
        (d * d + ((d - 1) * ((k.val - (d - 1) * d) / (d - 1) - 1)
          + (k.val - (d - 1) * d) % (d - 1))))
    intro v hv
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨a, hane, rfl⟩ := hv
    have := stabEntry_Z_support d k.val a.val hz hane
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-! ## The parametric `QECParams` family -/

/-- `QECParams` for HGP(Rep(d), Rep(d)), `d ≥ 2`: schedule-independent
    back-action, `r = 4`, budget `d - 1` (the largest budget below the
    distance, so the FT headline is the sharp `d-1`-fault statement). -/
def mkHGPRepQECParams (d : Nat) (hd : 2 ≤ d) : QECParams where
  n := hgpN d
  k := 1
  d := d
  R := 1
  numStab := hgpNumStab d
  stabilizers := mkHGPRepStabilizers d
  backActionSet := hgpBackAction d
  r := 4
  backAction_weight_bound := fun s e he =>
    le_trans (weight_le_of_pointwise_dominated he) (weight_stab_le_four d s)
  C_budget := d - 1
  hn := Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) (Nat.le_add_right _ _)
  hns := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  hR := Nat.one_pos

/-! ## Branch selection

The four live branches of `stabEntry`, exposed as `if`-normal forms so that
downstream proofs can rewrite once and case on the membership condition. -/

private theorem guard_of_X {d k q : Nat} (hk : k < (d - 1) * d)
    (hq : q < d * d + (d - 1) * (d - 1)) :
    k < 2 * ((d - 1) * d) ∧ q < d * d + (d - 1) * (d - 1) :=
  ⟨Nat.lt_of_lt_of_le hk (Nat.le_mul_of_pos_left _ (by omega)), hq⟩

theorem stabEntry_X_s1_eq (d k q : Nat) (hk : k < (d - 1) * d) (hq : q < d * d) :
    stabEntry d k q =
      if q % d = k % d ∧ (q / d = k / d ∨ q / d = k / d + 1) then .X else .I := by
  unfold stabEntry
  rw [if_pos (guard_of_X hk (Nat.lt_of_lt_of_le hq (Nat.le_add_right _ _))),
    if_pos hk, if_pos hq]

theorem stabEntry_X_s2_eq (d k q : Nat) (hk : k < (d - 1) * d)
    (hq1 : ¬q < d * d) (hq2 : q < d * d + (d - 1) * (d - 1)) :
    stabEntry d k q =
      if (q - d * d) / (d - 1) = k / d ∧
          ((q - d * d) % (d - 1) = k % d ∨ (q - d * d) % (d - 1) + 1 = k % d)
      then .X else .I := by
  unfold stabEntry
  rw [if_pos (guard_of_X hk hq2), if_pos hk, if_neg hq1]

theorem stabEntry_Z_s1_eq (d k q : Nat) (hzk : (d - 1) * d ≤ k)
    (hk2 : k < 2 * ((d - 1) * d)) (hq : q < d * d) :
    stabEntry d k q =
      if q / d = (k - (d - 1) * d) / (d - 1) ∧
          (q % d = (k - (d - 1) * d) % (d - 1) ∨
           q % d = (k - (d - 1) * d) % (d - 1) + 1)
      then .Z else .I := by
  unfold stabEntry
  rw [if_pos ⟨hk2, Nat.lt_of_lt_of_le hq (Nat.le_add_right _ _)⟩,
    if_neg (Nat.not_lt.mpr hzk), if_pos hq]

theorem stabEntry_Z_s2_eq (d k q : Nat) (hzk : (d - 1) * d ≤ k)
    (hk2 : k < 2 * ((d - 1) * d)) (hq1 : ¬q < d * d)
    (hq2 : q < d * d + (d - 1) * (d - 1)) :
    stabEntry d k q =
      if (q - d * d) % (d - 1) = (k - (d - 1) * d) % (d - 1) ∧
          ((q - d * d) / (d - 1) = (k - (d - 1) * d) / (d - 1) ∨
           (q - d * d) / (d - 1) + 1 = (k - (d - 1) * d) / (d - 1))
      then .Z else .I := by
  unfold stabEntry
  rw [if_pos ⟨hk2, hq2⟩, if_neg (Nat.not_lt.mpr hzk), if_neg hq1]

/-! ## Commutation

`parity` counts anticommuting positions.  For any pair of generators the
anticommuting set is empty (same CSS type) or an explicit two-element set
(one sector-1 and one sector-2 overlap point, which always co-occur) — even
either way.  No enumeration: the pair is produced by div/mod arithmetic. -/

private theorem div_mul_add (d a b : Nat) (hd : 0 < d) (hb : b < d) :
    (d * a + b) / d = a := by
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mod_mul_add (d a b : Nat) (hb : b < d) : (d * a + b) % d = b := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private theorem parity_false_of_pointwise {n : Nat} (S E : ErrorVec n)
    (h : ∀ q, ErrorVec.Pauli.anticommutes (S q) (E q) = false) :
    ErrorVec.parity S E = false := by
  unfold ErrorVec.parity
  have hempty : (Finset.univ.filter fun q : Fin n =>
      ErrorVec.Pauli.anticommutes (S q) (E q)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h q] at hq
    exact Bool.false_ne_true hq
  rw [hempty]
  rfl

private theorem parity_false_of_pair_or_empty {n : Nat} (S E : ErrorVec n)
    (h : (Finset.univ.filter fun q : Fin n =>
            ErrorVec.Pauli.anticommutes (S q) (E q)) = ∅ ∨
         ∃ q1 q2 : Fin n, q1 ≠ q2 ∧
           (Finset.univ.filter fun q : Fin n =>
             ErrorVec.Pauli.anticommutes (S q) (E q)) = {q1, q2}) :
    ErrorVec.parity S E = false := by
  unfold ErrorVec.parity
  rcases h with h | ⟨q1, q2, hne, h⟩
  · rw [h]; rfl
  · rw [h, Finset.card_insert_of_notMem (by simp [hne]),
      Finset.card_singleton]
    rfl

/-- The X-generator/Z-generator pair-or-empty argument: the anticommuting set
    of X-generator `ki = (i, j)` against Z-generator `kj = (a, jz)` is
    `{(a, j), d² + (i, jz)}` when `a ∈ {i, i+1}` and `j ∈ {jz, jz+1}`, and
    empty otherwise. -/
private theorem commute_XZ (d : Nat) (hd : 2 ≤ d) (ki kj : Nat)
    (hx : ki < (d - 1) * d) (hz : (d - 1) * d ≤ kj) (hk2 : kj < 2 * ((d - 1) * d)) :
    ErrorVec.parity (n := hgpN d)
      (fun q => stabEntry d ki q.val) (fun q => stabEntry d kj q.val) = false := by
  have hd0 : 0 < d := by omega
  have hd1 : 0 < d - 1 := by omega
  have hi : ki / d < d - 1 := (Nat.div_lt_iff_lt_mul hd0).mpr hx
  have hjc : ki % d < d := Nat.mod_lt _ hd0
  have ht : kj - (d - 1) * d < (d - 1) * d := by omega
  have ha : (kj - (d - 1) * d) / (d - 1) < d :=
    (Nat.div_lt_iff_lt_mul hd1).mpr (by rw [Nat.mul_comm d (d - 1)]; exact ht)
  have hjz : (kj - (d - 1) * d) % (d - 1) < d - 1 := Nat.mod_lt _ hd1
  -- the two candidate overlap points
  have hq1lt : d * ((kj - (d - 1) * d) / (d - 1)) + ki % d < d * d := by
    calc d * ((kj - (d - 1) * d) / (d - 1)) + ki % d
        < d * ((kj - (d - 1) * d) / (d - 1)) + d := by omega
      _ = d * ((kj - (d - 1) * d) / (d - 1) + 1) := (Nat.mul_succ _ _).symm
      _ ≤ d * d := Nat.mul_le_mul_left _ ha
  have hq2plt : (d - 1) * (ki / d) + (kj - (d - 1) * d) % (d - 1) < (d - 1) * (d - 1) := by
    calc (d - 1) * (ki / d) + (kj - (d - 1) * d) % (d - 1)
        < (d - 1) * (ki / d) + (d - 1) := by omega
      _ = (d - 1) * (ki / d + 1) := (Nat.mul_succ _ _).symm
      _ ≤ (d - 1) * (d - 1) := Nat.mul_le_mul_left _ hi
  refine parity_false_of_pair_or_empty _ _ ?_
  by_cases hC : ((kj - (d - 1) * d) / (d - 1) = ki / d ∨
                 (kj - (d - 1) * d) / (d - 1) = ki / d + 1) ∧
                (ki % d = (kj - (d - 1) * d) % (d - 1) ∨
                 ki % d = (kj - (d - 1) * d) % (d - 1) + 1)
  · right
    refine ⟨⟨d * ((kj - (d - 1) * d) / (d - 1)) + ki % d, by unfold hgpN; omega⟩,
            ⟨d * d + ((d - 1) * (ki / d) + (kj - (d - 1) * d) % (d - 1)),
             by unfold hgpN; omega⟩,
            by simp only [ne_eq, Fin.mk.injEq]; omega, ?_⟩
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    constructor
    · intro hanti
      by_cases hs1 : q.val < d * d
      · rw [stabEntry_X_s1_eq d ki q.val hx hs1,
            stabEntry_Z_s1_eq d kj q.val hz hk2 hs1] at hanti
        split_ifs at hanti with hm1 hm2
        · left
          have hsplit := Nat.div_add_mod q.val d
          rw [hm2.1, hm1.1] at hsplit
          omega
        · simp [ErrorVec.Pauli.anticommutes] at hanti
        · simp [ErrorVec.Pauli.anticommutes] at hanti
        · simp [ErrorVec.Pauli.anticommutes] at hanti
      · rw [stabEntry_X_s2_eq d ki q.val hx hs1 q.isLt,
            stabEntry_Z_s2_eq d kj q.val hz hk2 hs1 q.isLt] at hanti
        split_ifs at hanti with hm1 hm2
        · right
          have hsplit := Nat.div_add_mod (q.val - d * d) (d - 1)
          rw [hm1.1, hm2.1] at hsplit
          omega
        · simp [ErrorVec.Pauli.anticommutes] at hanti
        · simp [ErrorVec.Pauli.anticommutes] at hanti
        · simp [ErrorVec.Pauli.anticommutes] at hanti
    · rintro (hq | hq)
      · have hs1 : q.val < d * d := by omega
        rw [stabEntry_X_s1_eq d ki q.val hx hs1,
            stabEntry_Z_s1_eq d kj q.val hz hk2 hs1]
        have hdiv : q.val / d = (kj - (d - 1) * d) / (d - 1) := by
          rw [hq]; exact div_mul_add d _ _ hd0 hjc
        have hmod : q.val % d = ki % d := by
          rw [hq]; exact mod_mul_add d _ _ hjc
        rw [if_pos ⟨hmod, by rw [hdiv]; omega⟩, if_pos ⟨hdiv, by rw [hmod]; exact hC.2⟩]
        rfl
      · have hs1 : ¬q.val < d * d := by omega
        rw [stabEntry_X_s2_eq d ki q.val hx hs1 q.isLt,
            stabEntry_Z_s2_eq d kj q.val hz hk2 hs1 q.isLt]
        have hp : q.val - d * d = (d - 1) * (ki / d) + (kj - (d - 1) * d) % (d - 1) := by
          omega
        have hpdiv : (q.val - d * d) / (d - 1) = ki / d := by
          rw [hp]; exact div_mul_add _ _ _ hd1 hjz
        have hpmod : (q.val - d * d) % (d - 1) = (kj - (d - 1) * d) % (d - 1) := by
          rw [hp]; exact mod_mul_add _ _ _ hjz
        rw [if_pos ⟨hpdiv, by rw [hpmod]; omega⟩, if_pos ⟨hpmod, by rw [hpdiv]; omega⟩]
        rfl
  · left
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    apply hC
    by_cases hs1 : q.val < d * d
    · rw [stabEntry_X_s1_eq d ki q.val hx hs1,
          stabEntry_Z_s1_eq d kj q.val hz hk2 hs1] at hq
      split_ifs at hq with hm1 hm2
      · exact ⟨by omega, by omega⟩
      · simp [ErrorVec.Pauli.anticommutes] at hq
      · simp [ErrorVec.Pauli.anticommutes] at hq
      · simp [ErrorVec.Pauli.anticommutes] at hq
    · rw [stabEntry_X_s2_eq d ki q.val hx hs1 q.isLt,
          stabEntry_Z_s2_eq d kj q.val hz hk2 hs1 q.isLt] at hq
      split_ifs at hq with hm1 hm2
      · exact ⟨by omega, by omega⟩
      · simp [ErrorVec.Pauli.anticommutes] at hq
      · simp [ErrorVec.Pauli.anticommutes] at hq
      · simp [ErrorVec.Pauli.anticommutes] at hq

/-- All generator pairs commute, at every `d ≥ 2`. -/
theorem hgpRep_stab_commute (d : Nat) (hd : 2 ≤ d) (i j : Fin (hgpNumStab d)) :
    ErrorVec.parity (mkHGPRepStabilizers d i) (mkHGPRepStabilizers d j) = false := by
  have hib : i.val < 2 * ((d - 1) * d) := i.isLt
  have hjb : j.val < 2 * ((d - 1) * d) := j.isLt
  rcases Nat.lt_or_ge i.val ((d - 1) * d) with hxi | hzi
  · rcases Nat.lt_or_ge j.val ((d - 1) * d) with hxj | hzj
    · refine parity_false_of_pointwise _ _ fun q => ?_
      rcases stabEntry_X_type d i.val q.val hxi with h1 | h1 <;>
        rcases stabEntry_X_type d j.val q.val hxj with h2 | h2 <;>
        show ErrorVec.Pauli.anticommutes (stabEntry d i.val q.val)
          (stabEntry d j.val q.val) = false <;>
        rw [h1, h2] <;> rfl
    · exact commute_XZ d hd i.val j.val hxi hzj hjb
  · rcases Nat.lt_or_ge j.val ((d - 1) * d) with hxj | hzj
    · rw [ErrorVec.parity_symm]
      exact commute_XZ d hd j.val i.val hxj hzi hib
    · refine parity_false_of_pointwise _ _ fun q => ?_
      rcases stabEntry_Z_type d i.val q.val hzi with h1 | h1 <;>
        rcases stabEntry_Z_type d j.val q.val hzj with h2 | h2 <;>
        show ErrorVec.Pauli.anticommutes (stabEntry d i.val q.val)
          (stabEntry d j.val q.val) = false <;>
        rw [h1, h2] <;> rfl

/-! ## The logical operator is in the normalizer -/

private theorem logicalZ_type (d : Nat) (q : Fin (hgpN d)) :
    mkHGPRepLogicalZ d q = .I ∨ mkHGPRepLogicalZ d q = .Z := by
  unfold mkHGPRepLogicalZ
  split_ifs <;> simp

/-- Z̄ commutes with every generator: Z-generators are pure-Z; an X-generator
    meets column 0 in exactly the two sector-1 rows `{i, i+1}` when its own
    column is 0, and nowhere otherwise. -/
theorem hgpRep_logicalZ_normalizer (d : Nat) (hd : 2 ≤ d) (k : Fin (hgpNumStab d)) :
    ErrorVec.parity (mkHGPRepStabilizers d k) (mkHGPRepLogicalZ d) = false := by
  have hd0 : 0 < d := by omega
  rcases Nat.lt_or_ge k.val ((d - 1) * d) with hx | hz
  · -- X-generator: meets column 0 in rows {i, i+1} iff its own column is 0
    have hi : k.val / d < d - 1 := (Nat.div_lt_iff_lt_mul hd0).mpr hx
    have hrow2 : d * (k.val / d + 1) < d * d := by
      calc d * (k.val / d + 1) ≤ d * (d - 1) := Nat.mul_le_mul_left _ (by omega)
        _ < d * d := by
          have hdd : d * (d - 1) + d = d * d := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega
    have hstep : d * (k.val / d) < d * (k.val / d + 1) := by
      rw [Nat.mul_succ]; omega
    have hrow1 : d * (k.val / d) < d * d := lt_trans hstep hrow2
    refine parity_false_of_pair_or_empty _ _ ?_
    by_cases hj0 : k.val % d = 0
    · right
      refine ⟨⟨d * (k.val / d), by unfold hgpN; omega⟩,
              ⟨d * (k.val / d + 1), by unfold hgpN; omega⟩,
              by simp only [ne_eq, Fin.mk.injEq]; omega, ?_⟩
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      constructor
      · intro hanti
        by_cases hs1 : q.val < d * d
        · rw [show mkHGPRepStabilizers d k q = stabEntry d k.val q.val from rfl,
              stabEntry_X_s1_eq d k.val q.val hx hs1,
              show mkHGPRepLogicalZ d q =
                (if q.val < d * d ∧ q.val % d = 0 then Pauli.Z else Pauli.I) from rfl]
            at hanti
          split_ifs at hanti with hm1 hm2
          · have hsplit := Nat.div_add_mod q.val d
            rcases hm1.2 with hr | hr <;> rw [hr, hm2.2] at hsplit <;> omega
          · simp [ErrorVec.Pauli.anticommutes] at hanti
          · simp [ErrorVec.Pauli.anticommutes] at hanti
          · simp [ErrorVec.Pauli.anticommutes] at hanti
        · rw [show mkHGPRepLogicalZ d q =
              (if q.val < d * d ∧ q.val % d = 0 then Pauli.Z else Pauli.I) from rfl,
              if_neg (fun h => hs1 h.1)] at hanti
          rcases stabEntry_X_type d k.val q.val hx with h1 | h1 <;>
            rw [show mkHGPRepStabilizers d k q = stabEntry d k.val q.val from rfl, h1]
              at hanti <;>
            simp [ErrorVec.Pauli.anticommutes] at hanti
      · rintro (hq | hq)
        · have hs1 : q.val < d * d := by omega
          rw [show mkHGPRepStabilizers d k q = stabEntry d k.val q.val from rfl,
              stabEntry_X_s1_eq d k.val q.val hx hs1,
              show mkHGPRepLogicalZ d q =
                (if q.val < d * d ∧ q.val % d = 0 then Pauli.Z else Pauli.I) from rfl]
          have hdiv : q.val / d = k.val / d := by
            rw [hq]; exact Nat.mul_div_cancel_left _ hd0
          have hmod : q.val % d = 0 := by rw [hq]; exact Nat.mul_mod_right d _
          rw [if_pos ⟨by omega, Or.inl hdiv⟩, if_pos ⟨hs1, hmod⟩]
          rfl
        · have hs1 : q.val < d * d := by omega
          rw [show mkHGPRepStabilizers d k q = stabEntry d k.val q.val from rfl,
              stabEntry_X_s1_eq d k.val q.val hx hs1,
              show mkHGPRepLogicalZ d q =
                (if q.val < d * d ∧ q.val % d = 0 then Pauli.Z else Pauli.I) from rfl]
          have hdiv : q.val / d = k.val / d + 1 := by
            rw [hq]; exact Nat.mul_div_cancel_left _ hd0
          have hmod : q.val % d = 0 := by rw [hq]; exact Nat.mul_mod_right d _
          rw [if_pos ⟨by omega, Or.inr hdiv⟩, if_pos ⟨hs1, hmod⟩]
          rfl
    · left
      rw [Finset.eq_empty_iff_forall_notMem]
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      by_cases hs1 : q.val < d * d
      · rw [show mkHGPRepStabilizers d k q = stabEntry d k.val q.val from rfl,
            stabEntry_X_s1_eq d k.val q.val hx hs1,
            show mkHGPRepLogicalZ d q =
              (if q.val < d * d ∧ q.val % d = 0 then Pauli.Z else Pauli.I) from rfl] at hq
        split_ifs at hq with hm1 hm2
        · exact hj0 (by omega)
        · simp [ErrorVec.Pauli.anticommutes] at hq
        · simp [ErrorVec.Pauli.anticommutes] at hq
        · simp [ErrorVec.Pauli.anticommutes] at hq
      · rw [show mkHGPRepLogicalZ d q =
            (if q.val < d * d ∧ q.val % d = 0 then Pauli.Z else Pauli.I) from rfl,
            if_neg (fun h => hs1 h.1)] at hq
        rcases stabEntry_X_type d k.val q.val hx with h1 | h1 <;>
          rw [show mkHGPRepStabilizers d k q = stabEntry d k.val q.val from rfl, h1]
            at hq <;>
          simp [ErrorVec.Pauli.anticommutes] at hq
  · refine parity_false_of_pointwise _ _ fun q => ?_
    rcases stabEntry_Z_type d k.val q.val hz with h1 | h1 <;>
      rcases logicalZ_type d q with h2 | h2 <;>
      show ErrorVec.Pauli.anticommutes (stabEntry d k.val q.val)
        (mkHGPRepLogicalZ d q) = false <;>
      rw [h1, h2] <;> rfl

/-! ## Column-cut telescoping

`Ẑ_{j+1} = (∏_{a<d} Z-gen (a,j)) · Ẑ_j`: the Z-generators of column pair
`{j, j+1}` hit each sector-1 qubit of those columns once and each sector-2
qubit of column `j` twice (rows `a` and `a+1`), so the sector-2 contributions
cancel.  Iterating from `Ẑ_0 = Z̄` gives `cutOp_stabEquiv` — the parametric
analogue of `HGPCode.lean`'s `cut01/cut02_stabilizer_equiv` (`decide`). -/

/-- Index of the Z-generator `(t, j)` (sector-1 row `t`, columns `{j, j+1}`). -/
private def zColIdx (d t j : Nat) : Nat := (d - 1) * d + ((d - 1) * t + j)

private theorem zColIdx_lt_numStab (d t j : Nat) (ht : t < d) (hj : j < d - 1) :
    zColIdx d t j < hgpNumStab d := by
  unfold zColIdx hgpNumStab
  have h1 : (d - 1) * t + j < (d - 1) * d := by
    calc (d - 1) * t + j < (d - 1) * t + (d - 1) := by omega
      _ = (d - 1) * (t + 1) := (Nat.mul_succ _ _).symm
      _ ≤ (d - 1) * d := Nat.mul_le_mul_left _ ht
  omega

private theorem zColIdx_ge (d t j : Nat) : (d - 1) * d ≤ zColIdx d t j :=
  Nat.le_add_right _ _

private theorem zColIdx_div (d t j : Nat) (hd1 : 0 < d - 1) (hj : j < d - 1) :
    (zColIdx d t j - (d - 1) * d) / (d - 1) = t := by
  unfold zColIdx
  rw [Nat.add_sub_cancel_left]
  exact div_mul_add _ _ _ hd1 hj

private theorem zColIdx_mod (d t j : Nat) (hj : j < d - 1) :
    (zColIdx d t j - (d - 1) * d) % (d - 1) = j := by
  unfold zColIdx
  rw [Nat.add_sub_cancel_left]
  exact mod_mul_add _ _ _ hj

/-- Sector-1 value of the Z-generator `(t, j)`. -/
private theorem colStab_s1 (d t j : Nat) (hj : j < d - 1)
    (hlt : zColIdx d t j < hgpNumStab d) (q : Fin (hgpN d)) (hs1 : q.val < d * d) :
    mkHGPRepStabilizers d ⟨zColIdx d t j, hlt⟩ q =
      if q.val / d = t ∧ (q.val % d = j ∨ q.val % d = j + 1) then .Z else .I := by
  show stabEntry d (zColIdx d t j) q.val = _
  rw [stabEntry_Z_s1_eq d _ q.val (zColIdx_ge d t j) hlt hs1,
    zColIdx_div d t j (by omega) hj, zColIdx_mod d t j hj]

/-- Sector-2 value of the Z-generator `(t, j)`. -/
private theorem colStab_s2 (d t j : Nat) (hj : j < d - 1)
    (hlt : zColIdx d t j < hgpNumStab d) (q : Fin (hgpN d)) (hs1 : ¬q.val < d * d) :
    mkHGPRepStabilizers d ⟨zColIdx d t j, hlt⟩ q =
      if (q.val - d * d) % (d - 1) = j ∧
          ((q.val - d * d) / (d - 1) = t ∨ (q.val - d * d) / (d - 1) + 1 = t)
      then .Z else .I := by
  show stabEntry d (zColIdx d t j) q.val = _
  rw [stabEntry_Z_s2_eq d _ q.val (zColIdx_ge d t j) hlt hs1 q.isLt,
    zColIdx_div d t j (by omega) hj, zColIdx_mod d t j hj]

/-- Product of the column-`j` Z-generators over sector-1 rows `a < t`. -/
private def colProd (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1) :
    (t : Nat) → t ≤ d → ErrorVec (hgpN d)
  | 0, _ => ErrorVec.identity _
  | t + 1, ht =>
    ErrorVec.mul (colProd d hd j hj t (Nat.le_of_succ_le ht))
      (mkHGPRepStabilizers d ⟨zColIdx d t j, zColIdx_lt_numStab d t j (by omega) hj⟩)

private theorem colProd_inStab (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1) :
    ∀ (t : Nat) (ht : t ≤ d), InStab (mkHGPRepQECParams d hd) (colProd d hd j hj t ht) := by
  intro t
  induction t with
  | zero => intro ht; exact InStab.identity
  | succ t ih =>
    intro ht
    exact InStab.mul (ih (Nat.le_of_succ_le ht))
      (InStab.gen (P := mkHGPRepQECParams d hd)
        ⟨zColIdx d t j, zColIdx_lt_numStab d t j (by omega) hj⟩)

/-- Sector-1 running value: after `t` factors, a sector-1 qubit of columns
    `{j, j+1}` has seen exactly one `Z` iff its row is `< t`. -/
private theorem colProd_apply_s1 (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (q : Fin (hgpN d)) (hs1 : q.val < d * d) :
    ∀ (t : Nat) (ht : t ≤ d), colProd d hd j hj t ht q =
      if q.val / d < t ∧ (q.val % d = j ∨ q.val % d = j + 1) then .Z else .I := by
  intro t
  induction t with
  | zero =>
    intro ht
    rw [if_neg (fun hm => Nat.not_lt_zero _ hm.1)]
    rfl
  | succ t ih =>
    intro ht
    show ErrorVec.mul _ _ q = _
    have hmul : ErrorVec.mul (colProd d hd j hj t (Nat.le_of_succ_le ht))
        (mkHGPRepStabilizers d ⟨zColIdx d t j, zColIdx_lt_numStab d t j (by omega) hj⟩) q
        = Pauli.mul (colProd d hd j hj t (Nat.le_of_succ_le ht) q)
            (mkHGPRepStabilizers d
              ⟨zColIdx d t j, zColIdx_lt_numStab d t j (by omega) hj⟩ q) := rfl
    rw [hmul, ih (Nat.le_of_succ_le ht), colStab_s1 d t j hj _ q hs1]
    by_cases hc : q.val % d = j ∨ q.val % d = j + 1
    · rcases Nat.lt_trichotomy (q.val / d) t with h | h | h
      · rw [if_pos ⟨h, hc⟩, if_neg (fun hm => absurd hm.1 (Nat.ne_of_lt h)),
          if_pos ⟨by omega, hc⟩]
        rfl
      · rw [if_neg (fun hm => by omega), if_pos ⟨h, hc⟩, if_pos ⟨by omega, hc⟩]
        rfl
      · rw [if_neg (fun hm => by omega), if_neg (fun hm => by omega),
          if_neg (fun hm => by omega)]
        rfl
    · rw [if_neg (fun hm => hc hm.2), if_neg (fun hm => hc hm.2),
        if_neg (fun hm => hc hm.2)]
      rfl

/-- Sector-2 running value: a sector-2 qubit of column `j` at row `r` has odd
    `Z`-count iff exactly one of the two hitting factors `a ∈ {r, r+1}` has
    been multiplied, i.e. iff `t = r + 1`. -/
private theorem colProd_apply_s2 (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (q : Fin (hgpN d)) (hs1 : ¬q.val < d * d) :
    ∀ (t : Nat) (ht : t ≤ d), colProd d hd j hj t ht q =
      if (q.val - d * d) % (d - 1) = j ∧ t = (q.val - d * d) / (d - 1) + 1
      then .Z else .I := by
  intro t
  induction t with
  | zero =>
    intro ht
    rw [if_neg (fun hm => Nat.succ_ne_zero _ hm.2.symm)]
    rfl
  | succ t ih =>
    intro ht
    show ErrorVec.mul _ _ q = _
    have hmul : ErrorVec.mul (colProd d hd j hj t (Nat.le_of_succ_le ht))
        (mkHGPRepStabilizers d ⟨zColIdx d t j, zColIdx_lt_numStab d t j (by omega) hj⟩) q
        = Pauli.mul (colProd d hd j hj t (Nat.le_of_succ_le ht) q)
            (mkHGPRepStabilizers d
              ⟨zColIdx d t j, zColIdx_lt_numStab d t j (by omega) hj⟩ q) := rfl
    rw [hmul, ih (Nat.le_of_succ_le ht), colStab_s2 d t j hj _ q hs1]
    by_cases hcc : (q.val - d * d) % (d - 1) = j
    · rcases Nat.lt_trichotomy t ((q.val - d * d) / (d - 1)) with h | h | h
      · rw [if_neg (fun hm => by omega), if_neg (fun hm => by omega),
          if_neg (fun hm => by omega)]
        rfl
      · rw [if_neg (fun hm => by omega), if_pos ⟨hcc, Or.inl h.symm⟩,
          if_pos ⟨hcc, by omega⟩]
        rfl
      · by_cases h2 : t = (q.val - d * d) / (d - 1) + 1
        · rw [if_pos ⟨hcc, h2⟩, if_pos ⟨hcc, Or.inr (by omega)⟩,
            if_neg (fun hm => by omega)]
          rfl
        · rw [if_neg (fun hm => h2 hm.2), if_neg (fun hm => by omega),
            if_neg (fun hm => by omega)]
          rfl
    · rw [if_neg (fun hm => hcc hm.1), if_neg (fun hm => hcc hm.1),
        if_neg (fun hm => hcc hm.1)]
      rfl

/-- Base of the telescope: the column-0 cut **is** the logical Z̄. -/
private theorem cut_zero (d : Nat) (hj : 0 < d) :
    mkHGPRepCutOp d ⟨0, hj⟩ = mkHGPRepLogicalZ d := rfl

/-- Step of the telescope: `Ẑ_{j+1} = (∏_{a<d} Z-gen (a,j)) · Ẑ_j`. -/
private theorem cut_succ (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (hj1 : j + 1 < d) :
    mkHGPRepCutOp d ⟨j + 1, hj1⟩ =
      ErrorVec.mul (colProd d hd j hj d Nat.le.refl)
        (mkHGPRepCutOp d ⟨j, Nat.lt_of_succ_lt hj1⟩) := by
  funext q
  show _ = Pauli.mul (colProd d hd j hj d Nat.le.refl q) (mkHGPRepCutOp d ⟨j, _⟩ q)
  by_cases hs1 : q.val < d * d
  · rw [colProd_apply_s1 d hd j hj q hs1 d Nat.le.refl]
    have hqd : q.val / d < d := (Nat.div_lt_iff_lt_mul (by omega)).mpr hs1
    show (if q.val < d * d ∧ q.val % d = j + 1 then Pauli.Z else Pauli.I) =
      Pauli.mul _ (if q.val < d * d ∧ q.val % d = j then Pauli.Z else Pauli.I)
    by_cases hc1 : q.val % d = j
    · rw [if_neg (fun hm => by omega), if_pos ⟨hqd, Or.inl hc1⟩, if_pos ⟨hs1, hc1⟩]
      rfl
    · by_cases hc2 : q.val % d = j + 1
      · rw [if_pos ⟨hs1, hc2⟩, if_pos ⟨hqd, Or.inr hc2⟩, if_neg (fun hm => hc1 hm.2)]
        rfl
      · rw [if_neg (fun hm => hc2 hm.2), if_neg (fun hm => by omega),
          if_neg (fun hm => hc1 hm.2)]
        rfl
  · rw [colProd_apply_s2 d hd j hj q hs1 d Nat.le.refl]
    have hrr : (q.val - d * d) / (d - 1) < d - 1 := by
      have hp : q.val - d * d < (d - 1) * (d - 1) := by
        have := q.isLt
        unfold hgpN at this
        omega
      exact (Nat.div_lt_iff_lt_mul (by omega)).mpr
        (by rw [Nat.mul_comm (d - 1) (d - 1)] at hp; exact hp)
    have hne : d ≠ (q.val - d * d) / (d - 1) + 1 := by
      have h2 : (q.val - d * d) / (d - 1) + 1 < (d - 1) + 1 := Nat.succ_lt_succ hrr
      have h3 : (q.val - d * d) / (d - 1) + 1 < d :=
        Nat.lt_of_lt_of_le h2 (Nat.le_of_eq (by omega))
      exact ne_of_gt h3
    show (if q.val < d * d ∧ q.val % d = j + 1 then Pauli.Z else Pauli.I) =
      Pauli.mul _ (if q.val < d * d ∧ q.val % d = j then Pauli.Z else Pauli.I)
    rw [if_neg (fun hm => hs1 hm.1), if_neg (fun hm => hne hm.2),
      if_neg (fun hm => hs1 hm.1)]
    rfl

/-- **Column-cut equivalence**: every cut is a Z-generator product times Z̄ —
    at every `d ≥ 2`, by telescoping from column 0. -/
theorem hgpRep_cutOp_stabEquiv (d : Nat) (hd : 2 ≤ d) :
    ∀ (j : Nat) (hj : j < d),
      ∃ S, InStab (mkHGPRepQECParams d hd) S ∧
        mkHGPRepCutOp d ⟨j, hj⟩ = ErrorVec.mul S (mkHGPRepLogicalZ d) := by
  intro j
  induction j with
  | zero =>
    intro hj
    refine ⟨ErrorVec.identity _, InStab.identity, ?_⟩
    rw [ErrorVec.mul_identity_left]
    exact cut_zero d hj
  | succ j ih =>
    intro hj1
    have hj : j < d - 1 := by omega
    obtain ⟨S, hS, hEq⟩ := ih (Nat.lt_of_succ_lt hj1)
    refine ⟨ErrorVec.mul (colProd d hd j hj d Nat.le.refl) S,
            InStab.mul (colProd_inStab d hd j hj d Nat.le.refl) hS, ?_⟩
    rw [cut_succ d hd j hj hj1, hEq]
    exact (ErrorVec.mul_assoc _ _ _).symm

/-- The cut/column compatibility field of `HGPSpec`. -/
theorem hgpRep_cutOp_spec (d : Nat) (hd0 : 0 < d) (i : Fin d) (q : Fin (hgpN d)) :
    mkHGPRepCutOp d i q = if hgpCol d hd0 q = some i then .Z else .I := by
  unfold mkHGPRepCutOp hgpCol
  by_cases hs1 : q.val < d * d
  · rw [if_pos hs1]
    by_cases hc : q.val % d = i.val
    · rw [if_pos ⟨hs1, hc⟩, if_pos (congrArg some (Fin.ext hc))]
    · rw [if_neg (fun hm => hc hm.2),
        if_neg (fun h => hc (congrArg Fin.val (Option.some.inj h)))]
  · rw [if_neg hs1, if_neg (fun hm => hs1 hm.1)]
    simp

/-! ## Hook alignment for any schedule

The `hook_in_column` obligation, discharged **uniformly**: X-generator hooks
are pointwise dominated by the generator, whose sector-1 support lies in one
column, so multiplying a hook in can add at most that column to the X-pattern;
Z-generator hooks are pure-Z and change no X-pattern at all.  This replaces
the ~400-line `fin_cases` enumeration of `HGP13PCC.lean` and — because the
back-action set dominates the suffix hooks of *every* CNOT ordering — proves
the schedule-free claim directly. -/

private theorem hasX_eq_of_eB_I {n : Nat} (S_wit e_B E : ErrorVec n) (q : Fin n)
    (h_q : e_B q = .I) :
    Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
      = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
  show Pauli.hasXComponent (Pauli.mul (S_wit q) (Pauli.mul (e_B q) (E q)))
    = Pauli.hasXComponent (Pauli.mul (S_wit q) (E q))
  rw [h_q]
  cases S_wit q <;> cases E q <;> rfl

private theorem hasX_eq_of_eB_Z {n : Nat} (S_wit e_B E : ErrorVec n) (q : Fin n)
    (h_q : e_B q = .Z) :
    Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
      = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
  show Pauli.hasXComponent (Pauli.mul (S_wit q) (Pauli.mul (e_B q) (E q)))
    = Pauli.hasXComponent (Pauli.mul (S_wit q) (E q))
  rw [h_q]
  cases S_wit q <;> cases E q <;> rfl

/-- Counting bound: if every position either preserves the X-pattern or lives
    in column `j` (or has no column), the hit-column count grows by ≤ 1. -/
private theorem col_filter_bound {n d : Nat} (col : Fin n → Option (Fin d))
    (S_wit e_B E : ErrorVec n) (j : Fin d)
    (h : ∀ q : Fin n,
      Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
        = Pauli.hasXComponent (ErrorVec.mul S_wit E q)
      ∨ col q = some j ∨ col q = none) :
    (Finset.univ.filter fun g : Fin d => ∃ q, col q = some g ∧
      Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true).card
    ≤ (Finset.univ.filter fun g : Fin d => ∃ q, col q = some g ∧
      Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  have hsub : (Finset.univ.filter fun g : Fin d => ∃ q, col q = some g ∧
      Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true)
      ⊆ insert j (Finset.univ.filter fun g : Fin d => ∃ q, col q = some g ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨q, hcol, hX⟩ := hg
    rcases h q with hpres | hj | hnone
    · refine Finset.mem_insert_of_mem ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨q, hcol, hpres ▸ hX⟩
    · rw [hcol] at hj
      exact Finset.mem_insert.mpr (Or.inl (Option.some.inj hj))
    · rw [hcol] at hnone
      exact absurd hnone (Option.some_ne_none g)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

private theorem hgpCol_s1 (d : Nat) (hd0 : 0 < d) (q : Fin (hgpN d))
    (hs1 : q.val < d * d) :
    hgpCol d hd0 q = some ⟨q.val % d, Nat.mod_lt _ hd0⟩ := by
  unfold hgpCol
  rw [if_pos hs1]

private theorem hgpCol_s2 (d : Nat) (hd0 : 0 < d) (q : Fin (hgpN d))
    (hs1 : ¬q.val < d * d) :
    hgpCol d hd0 q = none := by
  unfold hgpCol
  rw [if_neg hs1]

/-- The `hook_in_column` field, for every generator and every dominated hook:
    the witness is unchanged in all cases. -/
theorem hgpRep_hook_in_column (d : Nat) (hd : 2 ≤ d) (hd0 : 0 < d) :
    ∀ (s_idx : Fin (hgpNumStab d)) (e_B : ErrorVec (hgpN d)),
      e_B ∈ hgpBackAction d s_idx →
      ∀ (E S_wit : ErrorVec (hgpN d)), InStab (mkHGPRepQECParams d hd) S_wit →
        ∃ S_wit', InStab (mkHGPRepQECParams d hd) S_wit' ∧
          (Finset.univ.filter fun g : Fin d => ∃ q, hgpCol d hd0 q = some g ∧
            Pauli.hasXComponent (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
          ≤ (Finset.univ.filter fun g : Fin d => ∃ q, hgpCol d hd0 q = some g ∧
            Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  intro s_idx e_B he E S_wit hS
  refine ⟨S_wit, hS, ?_⟩
  rcases Nat.lt_or_ge s_idx.val ((d - 1) * d) with hx | hz
  · -- X-generator: X-support lies in sector-1 column `s_idx % d` ∪ sector 2
    apply col_filter_bound (hgpCol d hd0) S_wit e_B E ⟨s_idx.val % d, Nat.mod_lt _ hd0⟩
    intro q
    rcases he q with hI | hstab
    · exact Or.inl (hasX_eq_of_eB_I _ _ _ _ hI)
    · by_cases hqI : mkHGPRepStabilizers d s_idx q = Pauli.I
      · exact Or.inl (hasX_eq_of_eB_I _ _ _ _ (hstab.trans hqI))
      · by_cases hs1 : q.val < d * d
        · right; left
          have hcolq : q.val % d = s_idx.val % d :=
            stabEntry_X_s1_col d s_idx.val q.val hx hs1 hqI
          rw [hgpCol_s1 d hd0 q hs1]
          exact congrArg some (Fin.ext hcolq)
        · right; right
          exact hgpCol_s2 d hd0 q hs1
  · -- Z-generator: pure-Z hook, X-pattern unchanged everywhere
    have heq : ∀ q, Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
        = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
      intro q
      rcases he q with hI | hstab
      · exact hasX_eq_of_eB_I _ _ _ _ hI
      · rcases stabEntry_Z_type d s_idx.val q.val hz with hI | hZ
        · exact hasX_eq_of_eB_I _ _ _ _ (hstab.trans hI)
        · exact hasX_eq_of_eB_Z _ _ _ _ (hstab.trans hZ)
    have hfilters : (Finset.univ.filter fun g : Fin d => ∃ q, hgpCol d hd0 q = some g ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true)
        = (Finset.univ.filter fun g : Fin d => ∃ q, hgpCol d hd0 q = some g ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true) :=
      Finset.filter_congr fun g _ =>
        exists_congr fun q => and_congr_right fun _ => by rw [heq q]
    exact le_trans (Nat.le_of_eq (congrArg Finset.card hfilters)) (Nat.le_succ _)

/-! ## The parametric spec and its headlines -/

/-- **The HGP(Rep(d), Rep(d)) family as an `HGPSpec d`, for every `d ≥ 2`** —
    all fields discharged structurally; no `fin_cases`, no `decide`, no
    `native_decide` anywhere in the construction. -/
def mkHGPRepSpec (d : Nat) (hd : 2 ≤ d) : HGPSpec d where
  params := mkHGPRepQECParams d hd
  hd_pos := by omega
  logicalZ := mkHGPRepLogicalZ d
  col := hgpCol d (by omega)
  cutOp := mkHGPRepCutOp d
  cutOp_stabEquiv := fun i => by
    obtain ⟨j, hj⟩ := i
    exact hgpRep_cutOp_stabEquiv d hd j hj
  cutOp_spec := fun i q => hgpRep_cutOp_spec d (by omega) i q
  logicalZ_normalizer := fun i => hgpRep_logicalZ_normalizer d hd i
  stab_commute := fun i j => hgpRep_stab_commute d hd i j
  hook_in_column := hgpRep_hook_in_column d hd (by omega)

/-- **HGP(Rep(d), Rep(d)) preserves circuit-level distance at every `d ≥ 2`,
    under any gate scheduling**: a reachable zero-syndrome state that flips Z̄
    has consumed at least `d` faults.  With the instance budget `d - 1` the
    conclusion is `Nat`-unsatisfiable, so (as in `HGP13PCC`) the content is
    that the hypotheses are jointly impossible — the usable form is
    `hgpRep_no_logical_error` below. -/
theorem hgpRep_distance_ge_d (d : Nat) (hd : 2 ≤ d)
    (s : State (mkHGPRepSpec d hd).params)
    (hreach : MultiStep (mkHGPRepSpec d hd).params
      (.active (State.init (mkHGPRepSpec d hd).params)) (.active s))
    (hSyn : ∀ i, ErrorVec.parity ((mkHGPRepSpec d hd).params.stabilizers i)
      s.E_tilde = false)
    (hLog : ErrorVec.parity (mkHGPRepSpec d hd).logicalZ s.E_tilde = true) :
    (mkHGPRepSpec d hd).params.C_budget - s.C ≥ d :=
  hgp_distance_ge_d (mkHGPRepSpec d hd) s hreach hSyn hLog

/-- With budget `d - 1`, no reachable zero-syndrome state flips the logical:
    the family tolerates `d - 1` faults. -/
theorem hgpRep_no_logical_error (d : Nat) (hd : 2 ≤ d)
    (s : State (mkHGPRepSpec d hd).params)
    (hreach : MultiStep (mkHGPRepSpec d hd).params
      (.active (State.init (mkHGPRepSpec d hd).params)) (.active s))
    (hSyn : ∀ i, ErrorVec.parity ((mkHGPRepSpec d hd).params.stabilizers i)
      s.E_tilde = false) :
    ErrorVec.parity (mkHGPRepSpec d hd).logicalZ s.E_tilde = false := by
  cases hLog : ErrorVec.parity (mkHGPRepSpec d hd).logicalZ s.E_tilde with
  | false => rfl
  | true =>
    exfalso
    have hge := hgpRep_distance_ge_d d hd s hreach hSyn hLog
    have hb : (mkHGPRepSpec d hd).params.C_budget = d - 1 := rfl
    rw [hb] at hge
    omega

/-- The Hoare-logic route: the same bound through the QHL syntactic
    invariant certificate (`hgp_invariant_derivation`), for a completed run of
    the row-major measurement program — the parametric analogue of
    `HGP13PCC.hgp13_FT`. -/
theorem hgpRep_FT (d : Nat) (hd : 2 ≤ d)
    (s : State (mkHGPRepSpec d hd).params)
    (hrun : Run (mkHGPRepSpec d hd).params (.done s))
    (h_in : (QStab.Paper.AlignedBarrier.barZClass
      (mkHGPRepSpec d hd).toAligned).contains s.E_tilde) :
    (mkHGPRepSpec d hd).params.C_budget - s.C ≥ d :=
  QHL.Source.Examples.HGP.hgp_dcirc_geq_d d (mkHGPRepSpec d hd) s hrun h_in

/-! ## Cross-validation against the fixed `[[13,1,3]]` instance

The `d = 3` member must reproduce `HGPCode.lean`'s hand-written table
entry-for-entry (the same anchor `CodeHGP.lean` checks the object-language
program against). -/

example : ∀ (k : Fin 12) (q : Fin 13),
    mkHGPRepStabilizers 3 k q = QStab.Examples.HGP13.stabilizers k q := by
  decide

example : mkHGPRepLogicalZ 3 = QStab.Examples.HGP13.logicalZ := by
  funext q; revert q; decide

example : ∀ i : Fin 3, mkHGPRepCutOp 3 i = QStab.Examples.HGP13.cutOp i := by
  intro i; funext q; revert q i; decide

#print axioms mkHGPRepSpec
#print axioms hgpRep_distance_ge_d
#print axioms hgpRep_no_logical_error
#print axioms hgpRep_FT

end QStab.Examples.HGPParametric
