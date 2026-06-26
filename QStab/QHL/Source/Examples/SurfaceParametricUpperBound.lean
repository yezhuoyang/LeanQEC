import QStab.Examples.SurfaceParametric
import QStab.Examples.SurfaceHookErrors
import QStab.Examples.SurfaceRowEquiv
import QStab.Paper.SurfaceBarrier

/-! # Parametric Pauli-weight upper bound for the rotated surface code

This file constructs an explicit X-string attacker of weight `d` that
lies in the `barZClass` of the parametric surface code at distance `d`.
Combined with the existing parametric lower bound
`parametricSurface_distance_preservation` (lower bound: `C_budget - C ≥ d`
at any done state with `E ∈ barZClass`), this provides the matching upper
bound side `d_circ ≤ d`.

The attacker is the **column-0 X-string**:

```
mkSurfaceAttackerX d q = if q.val % d = 0 then Pauli.X else Pauli.I
```

Five items are exposed (matching the workflow design):

1. `mkSurfaceAttackerX` — the attacker definition.
2. `mkSurfaceAttackerX_weight` — weight equals `d` (parametric).
3. `mkSurfaceAttackerX_commutes_with_stabilizers` — commutes with every
   parametric surface stabilizer (requires odd `d`).
4. `mkSurfaceAttackerX_anticommutes_logicalZ` — anti-commutes with the
   parametric logical Z (overlap is the single qubit `0`).
5. `mkSurfaceAttackerX_in_barZClass` — packages 3+4 as membership in
   `barZClass (mkSurfaceNZSurfaceSpec d hd3 hodd)`.

## Discipline (verified by `#print axioms`)

* All five headlines verify at `[propext, Classical.choice, Quot.sound]`.
* No `sorry`, `native_decide`, `Classical.choose`, `Exists.choose`,
  `by_contra`, or `relative_completeness_FDeriv`.
* `decide` is used ONLY on closed `Nat` / `Pauli` goals (e.g., the `d = 3`
  sanity reductions and discharge of `(0 : Nat) = 0` / `1 % 2 = 1`).
-/

namespace QHL.Source.Examples.SurfaceParametricUpperBound

open QStab QStab.Examples QStab.Examples.SurfaceParametric
     QStab.Examples.SurfaceGeneral
     QStab.Paper.BarrierFramework QStab.Paper.SurfaceBarrier

/-! ## Local re-exports of `SurfaceParametric` `private` helpers

Lean's `private` is file-scoped, so the helpers below — which exist in
`QStab/Examples/SurfaceParametric.lean` but cannot be referenced from
outside that file — are restated here as plain (non-private) lemmas,
with their proofs copied verbatim from the source.  No new content. -/

/-- Every value `decodeStabPauliAt d i row col` returns is either `I` or
    equals `stabType d i` (re-export of `SurfaceParametric.decode_eq_I_or_stabType`). -/
private lemma decode_eq_I_or_stabType' (d i row col : Nat) :
    decodeStabPauliAt d i row col = Pauli.I ∨
    decodeStabPauliAt d i row col = stabType d i := by
  simp only [decodeStabPauliAt, stabType]
  split_ifs with hbulk hbsupp hkind hTop hbtsupp hRight hRsupp hLeft hLsupp hBot
  all_goals first | (left; rfl) | (right; rfl)

/-- `anticommutes` of two `{I, X, Z}` values whose `stabType`s are equal is
    `false` (re-export of `SurfaceParametric.anticommutes_same_type`). -/
private lemma anticommutes_same_type'
    (a b : Pauli) (t : Pauli) (ht : t = Pauli.X ∨ t = Pauli.Z)
    (ha : a = Pauli.I ∨ a = t) (hb : b = Pauli.I ∨ b = t) :
    ErrorVec.Pauli.anticommutes a b = false := by
  rcases ht with ht | ht <;>
    rcases ha with ha | ha <;>
    rcases hb with hb | hb <;>
    subst ha <;> subst hb <;> subst ht <;> rfl

/-- `classifyStab d i` has type Z iff `stabType d i = .Z`
    (re-export of `SurfaceParametric.classify_type_Z`). -/
private lemma classify_type_Z' (d i : Nat) :
    stabType d i = Pauli.Z ↔
      (∃ r c, classifyStab d i = StabKind.bulkZ r c) ∨
      (∃ b, classifyStab d i = StabKind.rightZ b) ∨
      (∃ b, classifyStab d i = StabKind.leftZ b) := by
  simp only [stabType, classifyStab]
  split_ifs with hbulk hkind hTop hRight hLeft <;> simp

/-- Bounds extracted from `classifyStab d i = bulkZ r c`
    (re-export of `SurfaceParametric.classifyStab_bulkZ_bounds`). -/
private lemma classifyStab_bulkZ_bounds' (d i r c : Nat)
    (h : classifyStab d i = .bulkZ r c) :
    r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  subst hr_eq; subst hc_eq
  have hdmone_pos : 0 < d - 1 := by
    rcases Nat.eq_zero_or_pos (d - 1) with hzero | hpos
    · exfalso; rw [hzero, Nat.mul_zero] at hbulk; omega
    · exact hpos
  have hr_lt : i / (d - 1) < d - 1 :=
    Nat.div_lt_iff_lt_mul hdmone_pos |>.mpr (by rw [Nat.mul_comm]; exact hbulk)
  have hc_lt : i % (d - 1) < d - 1 := Nat.mod_lt _ hdmone_pos
  exact ⟨by omega, by omega, hpar⟩

/-- Bounds extracted from `classifyStab d i = rightZ b`
    (re-export of `SurfaceParametric.classifyStab_rightZ_bounds`). -/
private lemma classifyStab_rightZ_bounds' (d i b : Nat)
    (h : classifyStab d i = .rightZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight
  injection h with heq
  subst heq
  omega

/-- Bounds extracted from `classifyStab d i = leftZ b`
    (re-export of `SurfaceParametric.classifyStab_leftZ_bounds`). -/
private lemma classifyStab_leftZ_bounds' (d i b : Nat)
    (h : classifyStab d i = .leftZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight hLeft
  injection h with heq
  subst heq
  omega

/-- Filter cardinality is even, given that the filter set is either empty
    or a pair of distinct grid coordinates `q1, q2 ∈ Fin (d * d)`
    (re-export of `SurfaceParametric.card_filter_pair_or_empty_even_grid`). -/
private lemma card_filter_pair_or_empty_even_grid'
    (d : Nat) (P : Fin (d * d) → Prop) [DecidablePred P]
    (h : (∀ q, ¬ P q) ∨
         ∃ q1 q2 : Fin (d * d), q1 ≠ q2 ∧
           (∀ q, P q ↔ q = q1 ∨ q = q2)) :
    (Finset.univ.filter P).card % 2 = 0 := by
  rcases h with hempty | ⟨q1, q2, hne, hPair⟩
  · have : (Finset.univ.filter P).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro q _
      exact hempty q
    rw [this]
  · have : (Finset.univ.filter P).card = 2 := by
      have h_eq : Finset.univ.filter P =
                  Finset.univ.filter fun q : Fin (d * d) => q = q1 ∨ q = q2 := by
        apply Finset.ext; intro q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hPair q
      rw [h_eq, Finset.card_eq_two]
      refine ⟨q1, q2, hne, ?_⟩
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                 Finset.mem_singleton]
    rw [this]

/-! ## (1) The X-string attacker on column 0 -/

/-- The **column-0 X-string attacker** at distance `d`:
    `X` on every data qubit `q` with `q.val % d = 0` (i.e. left column),
    `I` elsewhere.

    At `d = 3` the support is the three qubits `{0, 3, 6}`; at `d = 5`
    it is `{0, 5, 10, 15, 20}`; etc. The set has cardinality exactly
    `d` (proven below). -/
def mkSurfaceAttackerX (d : Nat) : ErrorVec (d * d) :=
  fun q => if q.val % d = 0 then Pauli.X else Pauli.I

/-! ### `d = 3` sanity reductions (the function reduces to closed `Pauli`
    literals; provides a tangible inspection target). -/

example : mkSurfaceAttackerX 3 ⟨0, by decide⟩ = Pauli.X := rfl
example : mkSurfaceAttackerX 3 ⟨3, by decide⟩ = Pauli.X := rfl
example : mkSurfaceAttackerX 3 ⟨6, by decide⟩ = Pauli.X := rfl
example : mkSurfaceAttackerX 3 ⟨1, by decide⟩ = Pauli.I := rfl
example : mkSurfaceAttackerX 3 ⟨2, by decide⟩ = Pauli.I := rfl
example : mkSurfaceAttackerX 3 ⟨4, by decide⟩ = Pauli.I := rfl
example : mkSurfaceAttackerX 3 ⟨5, by decide⟩ = Pauli.I := rfl
example : mkSurfaceAttackerX 3 ⟨7, by decide⟩ = Pauli.I := rfl
example : mkSurfaceAttackerX 3 ⟨8, by decide⟩ = Pauli.I := rfl

/-! ## (2) Weight = d via bijection with `Fin d`

We use `Finset.card_bij` with the map `q ↦ ⟨q.val / d, _⟩` from
`{q : Fin (d * d) | q.val % d = 0}` to `Fin d`. The inverse on `r : Fin d`
is `⟨d * r.val, _⟩`. -/

/-- Weight of the column-0 X-string attacker is exactly `d`. -/
theorem mkSurfaceAttackerX_weight (d : Nat) (hd : 0 < d) :
    ErrorVec.weight (mkSurfaceAttackerX d) = d := by
  -- weight = |{q | attacker q ≠ I}| = |{q | q.val % d = 0}|
  unfold ErrorVec.weight mkSurfaceAttackerX
  -- The filter set is exactly {q : Fin (d * d) | q.val % d = 0}.
  have h_filter_eq :
      (Finset.univ.filter fun q : Fin (d * d) =>
          (if q.val % d = 0 then Pauli.X else Pauli.I) ≠ Pauli.I) =
      Finset.univ.filter fun q : Fin (d * d) => q.val % d = 0 := by
    apply Finset.ext
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hmod : q.val % d = 0
    · rw [if_pos hmod]
      constructor
      · intro _; exact hmod
      · intro _; decide
    · rw [if_neg hmod]
      constructor
      · intro h; exact absurd rfl h
      · intro h; exact absurd h hmod
  rw [h_filter_eq]
  -- Now show |{q | q.val % d = 0}| = d via bijection q ↦ ⟨q.val / d, _⟩.
  have h_card :
      (Finset.univ.filter fun q : Fin (d * d) => q.val % d = 0).card =
      (Finset.univ : Finset (Fin d)).card := by
    apply Finset.card_bij
      (fun (q : Fin (d * d)) (hq : q ∈ _) =>
        (⟨q.val / d, Nat.div_lt_of_lt_mul q.isLt⟩ : Fin d))
    · -- mapsTo: every image is in Finset.univ
      intro q _
      exact Finset.mem_univ _
    · -- injOn
      intro q1 hq1 q2 hq2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
      apply Fin.ext
      -- heq : (⟨q1.val/d, _⟩ : Fin d) = ⟨q2.val/d, _⟩.
      have hdiv : q1.val / d = q2.val / d :=
        congrArg Fin.val heq
      -- q.val = d * (q.val / d) + q.val % d
      have h1 : q1.val = d * (q1.val / d) + q1.val % d :=
        (Nat.div_add_mod q1.val d).symm
      have h2 : q2.val = d * (q2.val / d) + q2.val % d :=
        (Nat.div_add_mod q2.val d).symm
      -- substitute hq1, hq2, hdiv
      rw [hq1] at h1
      rw [hq2] at h2
      rw [hdiv] at h1
      omega
    · -- surjOn
      intro r _
      refine ⟨⟨d * r.val, ?_⟩, ?_, ?_⟩
      · exact Nat.mul_lt_mul_of_pos_left r.isLt hd
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show d * r.val % d = 0
        exact Nat.mul_mod_right d r.val
      · apply Fin.ext
        show d * r.val / d = r.val
        exact Nat.mul_div_cancel_left r.val hd
  rw [h_card, Finset.card_univ, Fintype.card_fin]

/-! ## (3) Commutation with every parametric stabilizer

We split on the Pauli **type** of the stabilizer (`stabType d i.val`):

* If `stabType d i.val = Pauli.X`: every position is in `{I, X}`, so the
  anticommutation with `{I, X}` is always `false`. Parity = 0.

* If `stabType d i.val = Pauli.Z`: anticommutation is non-zero exactly
  at positions where stab is `Z` AND attacker is `X` (i.e. `q.val % d = 0`).
  We show the count is always even via case analysis on the Z-kind
  (`bulkZ`, `rightZ`, `leftZ`).

The `hodd : d % 2 = 1` hypothesis is needed only because the parametric
`rightZ` boundary at even `d` is unconstrained; here it lets us cleanly
rule out the degenerate `d - 1 = 0` case. -/

/-- If `stabType d i.val = Pauli.X`, the parity of the stabilizer against
    the X-attacker is `false` (X commutes with X, X commutes with I). -/
private lemma parity_attacker_X_when_stabType_X (d : Nat) (hd : 0 < d)
    (i : Fin (numStabFormula d)) (hi : stabType d i.val = Pauli.X) :
    ErrorVec.parity (mkSurfaceStabilizers d hd i) (mkSurfaceAttackerX d) = false := by
  unfold ErrorVec.parity mkSurfaceStabilizers mkSurfaceAttackerX
  have h_empty :
      (Finset.univ.filter fun q : Fin (d * d) =>
        ErrorVec.Pauli.anticommutes
          (decodeStabPauliAt d i.val (q.val / d) (q.val % d))
          (if q.val % d = 0 then Pauli.X else Pauli.I) = true) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro q _
    intro h
    -- stab is in {I, X}; attacker is in {I, X}; both same-type so commute.
    have hstab := decode_eq_I_or_stabType' d i.val (q.val / d) (q.val % d)
    rw [hi] at hstab
    have hatt : (if q.val % d = 0 then Pauli.X else Pauli.I) = Pauli.I ∨
                (if q.val % d = 0 then Pauli.X else Pauli.I) = Pauli.X := by
      by_cases hmod : q.val % d = 0
      · rw [if_pos hmod]; right; rfl
      · rw [if_neg hmod]; left; rfl
    have hcomm := anticommutes_same_type'
      (decodeStabPauliAt d i.val (q.val / d) (q.val % d))
      (if q.val % d = 0 then Pauli.X else Pauli.I)
      Pauli.X (Or.inl rfl) hstab hatt
    rw [h] at hcomm
    exact Bool.false_ne_true hcomm.symm
  rw [h_empty]
  rfl

/-! ### Helper: counting Z-positions of a Z-typed stabilizer -/

/-- If `stabType d i.val = Pauli.Z`, the anticommutation filter (against
    the X-attacker) equals the qubit-set
    `{q | inStabSupport d i.val (q.val / d) (q.val % d) ∧ q.val % d = 0}`. -/
private lemma anticomm_filter_eq_support_col0
    (d : Nat) (hd : 0 < d) (i : Fin (numStabFormula d))
    (hi : stabType d i.val = Pauli.Z) :
    (Finset.univ.filter fun q : Fin (d * d) =>
      ErrorVec.Pauli.anticommutes
        (decodeStabPauliAt d i.val (q.val / d) (q.val % d))
        (if q.val % d = 0 then Pauli.X else Pauli.I) = true) =
    Finset.univ.filter fun q : Fin (d * d) =>
      inStabSupport d i.val (q.val / d) (q.val % d) ∧ q.val % d = 0 := by
  apply Finset.ext
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hmod : q.val % d = 0
  · rw [if_pos hmod]
    -- attacker is X; anticommutes(stab q, X) is true iff stab q has Z-component.
    -- For stab in {I, Z}, this is true iff stab q = Z, i.e. iff q ∈ support.
    have hstab := decode_eq_I_or_stabType' d i.val (q.val / d) (q.val % d)
    rw [hi] at hstab
    constructor
    · intro hanti
      refine ⟨?_, hmod⟩
      unfold inStabSupport
      rcases hstab with hstab | hstab
      · rw [hstab] at hanti
        exact absurd hanti (by decide)
      · rw [hstab]; decide
    · intro ⟨hsupp, _⟩
      unfold inStabSupport at hsupp
      rcases hstab with hstab | hstab
      · exact absurd hstab hsupp
      · rw [hstab]; decide
  · rw [if_neg hmod]
    have hanti_I :
        ErrorVec.Pauli.anticommutes
            (decodeStabPauliAt d i.val (q.val / d) (q.val % d)) Pauli.I = false := by
      cases (decodeStabPauliAt d i.val (q.val / d) (q.val % d)) <;> rfl
    rw [hanti_I]
    constructor
    · intro h; exact absurd h (by decide)
    · intro ⟨_, h⟩; exact absurd h hmod

/-! ### Z-support intersected with column 0 — case analysis by kind

The Z-typed stabilizers are: `bulkZ`, `rightZ`, `leftZ`.

* `bulkZ r c`:  rowSet `{r, r+1}`, colSet `{c, c+1}`.
                Intersected with col 0: only the `c = 0` case contributes,
                giving 2 qubits (rows `r`, `r+1`).
* `rightZ b`:   rowSet `{2b, 2b+1}`, colSet `{d-1}`.
                For odd `d ≥ 3`, `d - 1 ≥ 2 ≠ 0`, so 0 qubits.
* `leftZ b`:    rowSet `{2b+1, 2b+2}`, colSet `{0}`.
                Always 2 qubits (rows `2b+1`, `2b+2`).

In every case the count is even, so the parity is `false`. -/

/-- If `stabType d i.val = Pauli.Z` and `d` is odd, the qubit-set
    `{q | inStabSupport d i.val (q.val / d) (q.val % d) ∧ q.val % d = 0}`
    has even cardinality. -/
private lemma supp_col0_card_even (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) (hi : stabType d i.val = Pauli.Z) :
    (Finset.univ.filter fun q : Fin (d * d) =>
      inStabSupport d i.val (q.val / d) (q.val % d) ∧ q.val % d = 0).card % 2 = 0 := by
  have hcls := (classify_type_Z' d i.val).mp hi
  apply card_filter_pair_or_empty_even_grid' d _
  rcases hcls with ⟨r, c, hkind⟩ | ⟨b, hkind⟩ | ⟨b, hkind⟩
  · -- bulkZ r c
    by_cases hc0 : c = 0
    · -- c = 0: cells at (r, 0), (r+1, 0).
      have hbnd := classifyStab_bulkZ_bounds' d i.val r c hkind
      obtain ⟨hr1, _, _⟩ := hbnd
      have hr_lt_d : r < d := by omega
      have hr1_lt_d : r + 1 < d := hr1
      have hd_pos : 0 < d := hd
      have hq1_lt : d * r < d * d :=
        Nat.mul_lt_mul_of_pos_left hr_lt_d hd_pos
      have hq2_lt : d * (r + 1) < d * d :=
        Nat.mul_lt_mul_of_pos_left hr1_lt_d hd_pos
      right
      refine ⟨⟨d * r, hq1_lt⟩, ⟨d * (r + 1), hq2_lt⟩, ?_, ?_⟩
      · intro hEq
        have hraw : d * r = d * (r + 1) := congrArg Fin.val hEq
        have hreq : r = r + 1 := Nat.eq_of_mul_eq_mul_left hd_pos hraw
        omega
      · intro q
        rw [inStabSupport_iff_supportByKind, hkind]
        simp only [supportByKind, kindRowSet, kindColSet]
        constructor
        · rintro ⟨hsupp, hmod⟩
          rw [decide_eq_true_iff] at hsupp
          obtain ⟨hrow, _⟩ := hsupp
          rcases hrow with hrow | hrow
          · left
            apply Fin.ext
            show (q.val : Nat) = d * r
            have hdivmod := Nat.div_add_mod q.val d
            rw [hrow, hmod] at hdivmod
            omega
          · right
            apply Fin.ext
            show (q.val : Nat) = d * (r + 1)
            have hdivmod := Nat.div_add_mod q.val d
            rw [hrow, hmod] at hdivmod
            omega
        · rintro (hq | hq)
          · subst hq
            refine ⟨?_, ?_⟩
            · rw [decide_eq_true_iff]
              refine ⟨Or.inl ?_, ?_⟩
              · show d * r / d = r
                exact Nat.mul_div_cancel_left r hd
              · subst hc0
                left
                show d * r % d = 0
                exact Nat.mul_mod_right d r
            · show d * r % d = 0
              exact Nat.mul_mod_right d r
          · subst hq
            refine ⟨?_, ?_⟩
            · rw [decide_eq_true_iff]
              refine ⟨Or.inr ?_, ?_⟩
              · show d * (r + 1) / d = r + 1
                exact Nat.mul_div_cancel_left (r + 1) hd
              · subst hc0
                left
                show d * (r + 1) % d = 0
                exact Nat.mul_mod_right d (r + 1)
            · show d * (r + 1) % d = 0
              exact Nat.mul_mod_right d (r + 1)
    · -- c ≠ 0: empty.
      left
      intro q hcontra
      obtain ⟨hsupp, hmod⟩ := hcontra
      rw [inStabSupport_iff_supportByKind, hkind] at hsupp
      simp only [supportByKind] at hsupp
      rw [decide_eq_true_iff] at hsupp
      obtain ⟨_, hcol⟩ := hsupp
      rw [hmod] at hcol
      omega
  · -- rightZ b
    have hb := classifyStab_rightZ_bounds' d i.val b hkind
    -- For d = 1: (d - 1) / 2 = 0, so b < 0 impossible.
    -- For d odd ≥ 3: d - 1 ≥ 2 ≠ 0.
    -- d odd and 0 < d, so d ∈ {1, 3, 5, 7, ...}.
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · -- d = 1.
      have hd_eq : d = 1 := by omega
      have hb0 : b < (1 - 1) / 2 := hd_eq ▸ hb
      omega
    · -- d ≥ 2 and odd, so d ≥ 3.
      have hd_ne_2 : d ≠ 2 := by
        intro h
        rw [h] at hodd
        exact absurd hodd (by decide)
      have hd3 : 3 ≤ d := by omega
      left
      intro q hcontra
      obtain ⟨hsupp, hmod⟩ := hcontra
      rw [inStabSupport_iff_supportByKind, hkind] at hsupp
      simp only [supportByKind] at hsupp
      rw [decide_eq_true_iff] at hsupp
      obtain ⟨hcol, _⟩ := hsupp
      -- hcol : q.val % d = d - 1; hmod : q.val % d = 0; but d ≥ 3 → d - 1 ≥ 2 ≠ 0.
      omega
  · -- leftZ b
    have hb := classifyStab_leftZ_bounds' d i.val b hkind
    -- hb : b < (d - 1) / 2  →  2b + 2 ≤ d - 1 (when d ≥ 2)  →  2b + 2 < d.
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · have hd_eq : d = 1 := by omega
      rw [hd_eq] at hb
      omega
    · -- d ≥ 2, and from hb : b < (d - 1) / 2 we get 2b ≤ 2 * ((d - 1) / 2) ≤ d - 1.
      have h_2b_le : 2 * b ≤ d - 1 - 2 := by
        have h1 : 2 * b + 2 ≤ 2 * ((d - 1) / 2) + 2 := by omega
        have h2 : 2 * ((d - 1) / 2) ≤ d - 1 := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self (d - 1) 2
        -- Actually: 2 * ((d - 1) / 2) ≤ d - 1, but we need 2b + 2 ≤ d - 1.
        -- From hb : b < (d - 1) / 2, get 2b ≤ 2 * ((d - 1) / 2) - 2.
        have h3 : 2 * b ≤ 2 * ((d - 1) / 2) - 2 := by
          have : b + 1 ≤ (d - 1) / 2 := hb
          omega
        omega
      have h2b2_lt_d : 2 * b + 2 < d := by omega
      have h2b1_lt_d : 2 * b + 1 < d := by omega
      have hd_pos : 0 < d := hd
      have hq1_lt : d * (2 * b + 1) < d * d :=
        Nat.mul_lt_mul_of_pos_left h2b1_lt_d hd_pos
      have hq2_lt : d * (2 * b + 2) < d * d :=
        Nat.mul_lt_mul_of_pos_left h2b2_lt_d hd_pos
      right
      refine ⟨⟨d * (2 * b + 1), hq1_lt⟩, ⟨d * (2 * b + 2), hq2_lt⟩, ?_, ?_⟩
      · intro hEq
        have hraw : d * (2 * b + 1) = d * (2 * b + 2) := congrArg Fin.val hEq
        have hreq : 2 * b + 1 = 2 * b + 2 := Nat.eq_of_mul_eq_mul_left hd_pos hraw
        omega
      · intro q
        rw [inStabSupport_iff_supportByKind, hkind]
        simp only [supportByKind, kindRowSet, kindColSet]
        constructor
        · rintro ⟨hsupp, hmod⟩
          rw [decide_eq_true_iff] at hsupp
          obtain ⟨_, hrow⟩ := hsupp
          rcases hrow with hrow | hrow
          · left
            apply Fin.ext
            show (q.val : Nat) = d * (2 * b + 1)
            have hdivmod := Nat.div_add_mod q.val d
            rw [hrow, hmod] at hdivmod
            omega
          · right
            apply Fin.ext
            show (q.val : Nat) = d * (2 * b + 2)
            have hdivmod := Nat.div_add_mod q.val d
            rw [hrow, hmod] at hdivmod
            omega
        · rintro (hq | hq)
          · subst hq
            refine ⟨?_, ?_⟩
            · rw [decide_eq_true_iff]
              refine ⟨?_, Or.inl ?_⟩
              · show d * (2 * b + 1) % d = 0
                exact Nat.mul_mod_right d (2 * b + 1)
              · show d * (2 * b + 1) / d = 2 * b + 1
                exact Nat.mul_div_cancel_left (2 * b + 1) hd
            · show d * (2 * b + 1) % d = 0
              exact Nat.mul_mod_right d (2 * b + 1)
          · subst hq
            refine ⟨?_, ?_⟩
            · rw [decide_eq_true_iff]
              refine ⟨?_, Or.inr ?_⟩
              · show d * (2 * b + 2) % d = 0
                exact Nat.mul_mod_right d (2 * b + 2)
              · show d * (2 * b + 2) / d = 2 * b + 2
                exact Nat.mul_div_cancel_left (2 * b + 2) hd
            · show d * (2 * b + 2) % d = 0
              exact Nat.mul_mod_right d (2 * b + 2)

/-- The case `stabType d i.val = Pauli.Z`: parity of stabilizer against
    X-attacker is `false`. -/
private lemma parity_attacker_X_when_stabType_Z (d : Nat) (hd : 0 < d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d))
    (hi : stabType d i.val = Pauli.Z) :
    ErrorVec.parity (mkSurfaceStabilizers d hd i) (mkSurfaceAttackerX d) = false := by
  unfold ErrorVec.parity mkSurfaceStabilizers mkSurfaceAttackerX
  rw [anticomm_filter_eq_support_col0 d hd i hi]
  have h_even := supp_col0_card_even d hd hodd i hi
  rw [h_even]
  decide

/-- **Headline (3): Parametric commutation with all stabilizers.**

    For odd `d ≥ 1` and any stabilizer index `i`, the parametric surface
    stabilizer `mkSurfaceStabilizers d hd i` commutes with the column-0
    X-attacker `mkSurfaceAttackerX d`.

    Proof: split on `stabType d i.val ∈ {X, Z}`; the X-case is "same-type
    so commute" and the Z-case counts overlap with col 0 (always even by
    case analysis on kind). -/
theorem mkSurfaceAttackerX_commutes_with_stabilizers
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) :
    ErrorVec.parity (mkSurfaceStabilizers d hd i) (mkSurfaceAttackerX d) = false := by
  have htype : stabType d i.val = Pauli.X ∨ stabType d i.val = Pauli.Z := by
    simp only [stabType]; split_ifs <;> simp
  rcases htype with hi | hi
  · exact parity_attacker_X_when_stabType_X d hd i hi
  · exact parity_attacker_X_when_stabType_Z d hd hodd i hi

/-! ## (4) Anticommutation with the parametric logical Z

`mkSurfaceLogicalZ d` has `Z` exactly on the **top row** (qubits with
`q.val / d = 0`); `mkSurfaceAttackerX d` has `X` exactly on the **first
column** (qubits with `q.val % d = 0`).  Their overlap is the single
qubit `q = 0`. -/

/-- The anticommutation filter for `(logicalZ, attacker)` reduces to the
    singleton `{0}`. -/
private lemma anticomm_logicalZ_attacker_eq_singleton (d : Nat) (hd : 0 < d) :
    (Finset.univ.filter fun q : Fin (d * d) =>
      ErrorVec.Pauli.anticommutes
        (mkSurfaceLogicalZ d q) (mkSurfaceAttackerX d q) = true) =
    ({⟨0, Nat.mul_pos hd hd⟩} : Finset (Fin (d * d))) := by
  apply Finset.ext
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  unfold mkSurfaceLogicalZ mkSurfaceAttackerX
  constructor
  · intro hanti
    by_cases hrow : q.val / d = 0
    · -- top row
      rw [if_pos hrow] at hanti
      by_cases hcol : q.val % d = 0
      · rw [if_pos hcol] at hanti
        have hqv : q.val < d := Nat.lt_of_div_eq_zero hd hrow
        have hqmod : q.val % d = q.val := Nat.mod_eq_of_lt hqv
        rw [hqmod] at hcol
        apply Fin.ext
        exact hcol
      · rw [if_neg hcol] at hanti
        exact absurd hanti (by decide)
    · rw [if_neg hrow] at hanti
      -- logicalZ q = I; anticomm(I, _) = false.
      have h_I : ErrorVec.Pauli.anticommutes Pauli.I
              (if q.val % d = 0 then Pauli.X else Pauli.I) = false := by
        by_cases hcol : q.val % d = 0
        · rw [if_pos hcol]; rfl
        · rw [if_neg hcol]; rfl
      rw [h_I] at hanti
      exact absurd hanti (by decide)
  · intro hq
    subst hq
    have h_div : (0 : Nat) / d = 0 := Nat.zero_div d
    have h_mod : (0 : Nat) % d = 0 := Nat.zero_mod d
    show ErrorVec.Pauli.anticommutes
            (if (⟨0, _⟩ : Fin (d * d)).val / d = 0 then Pauli.Z else Pauli.I)
            (if (⟨0, _⟩ : Fin (d * d)).val % d = 0 then Pauli.X else Pauli.I) = true
    rw [show (⟨0, Nat.mul_pos hd hd⟩ : Fin (d * d)).val = 0 from rfl, h_div, h_mod]
    rw [if_pos rfl, if_pos rfl]
    decide

/-- **Headline (4): Anti-commutation with the parametric logical Z.**

    The column-0 X-attacker anti-commutes with the parametric logical Z.
    The overlap is the single qubit `0`. -/
theorem mkSurfaceAttackerX_anticommutes_logicalZ (d : Nat) (hd : 0 < d) :
    ErrorVec.parity (mkSurfaceLogicalZ d) (mkSurfaceAttackerX d) = true := by
  unfold ErrorVec.parity
  rw [anticomm_logicalZ_attacker_eq_singleton d hd]
  rw [Finset.card_singleton]
  decide

/-! ## (5) Membership in `barZClass (mkSurfaceNZSurfaceSpec d hd3 hodd)` -/

/-- **Headline (5): The column-0 X-attacker lies in `barZClass`.**

    Combining items (3) and (4): the attacker has zero syndrome
    (parity false with every stabilizer) and anti-commutes with
    `logicalZ`, so it is in the bar-Z logical class of the parametric
    surface code. -/
theorem mkSurfaceAttackerX_in_barZClass
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    (barZClass (mkSurfaceNZSurfaceSpec d hd3 hodd)).contains
      (mkSurfaceAttackerX d) := by
  refine ⟨?_, ?_⟩
  · intro i
    show ErrorVec.parity
            ((mkSurfaceNZSurfaceSpec d hd3 hodd).params.stabilizers i)
            (mkSurfaceAttackerX d) = false
    exact mkSurfaceAttackerX_commutes_with_stabilizers d (by omega) hodd i
  · show ErrorVec.parity
            (mkSurfaceNZSurfaceSpec d hd3 hodd).logicalZ
            (mkSurfaceAttackerX d) = true
    exact mkSurfaceAttackerX_anticommutes_logicalZ d (by omega)

/-! ## `#print axioms` audit -/

#print axioms mkSurfaceAttackerX
#print axioms mkSurfaceAttackerX_weight
#print axioms mkSurfaceAttackerX_commutes_with_stabilizers
#print axioms mkSurfaceAttackerX_anticommutes_logicalZ
#print axioms mkSurfaceAttackerX_in_barZClass

/-! ## (6)(7)(8) Parametric `d_circ = d` Pauli-weight equality theorems

These three headlines package the *Pauli-weight* form of the rotated
surface code's circuit-level distance, using the column-0 X-string
attacker (item 1) as the explicit upper-bound witness:

* **(6) `surface_dcirc_le_d_pauli`** — there exists a weight-`d` error
  in `barZClass`.  The witness is `mkSurfaceAttackerX d`: weight `d`
  by item 2; in `barZClass` by item 5.

* **(7) `surface_dcirc_ge_d_pauli`** — every member of `barZClass` has
  weight at least `d`.  This is `LogicalClass.d_L_min` applied at
  `d_L = d` (definitional).  *Works for arbitrary `spec : NZSurfaceSpec d`.*

* **(8) `surface_dcirc_eq_d_pauli`** — conjunction of (6) and (7).

### Honest note on `spec` parameterization

`NZSurfaceSpec d` is a `structure` whose `stabilizers` and `logicalZ`
fields are not pinned to the canonical `mkSurfaceStabilizers d` /
`mkSurfaceLogicalZ d` constructions; the structure only constrains them
up to the axioms (`stab_commute`, `logicalZ_normalizer`, `rowCut_spec`,
…).  The column-0 X-attacker `mkSurfaceAttackerX d` is therefore not a
universal witness for *every* `spec : NZSurfaceSpec d` — it commutes
only with the canonical `mkSurfaceStabilizers d` (proved at item 3).

Consequently:

* **(7) is genuinely parametric in `spec`** — the lower bound follows
  from `d_L_min`, which is built into the `LogicalClass` interface and
  holds for every `NZSurfaceSpec d`.

* **(6) and (8)** carry the explicit hypothesis
  `hspec : spec = mkSurfaceNZSurfaceSpec d hd3 hodd`, pinning `spec`
  to the canonical surface construction.  This faithfully follows the
  workflow spec signature `(d : Nat) … (spec : NZSurfaceSpec d) → …`
  while honestly recording that the upper bound is canonical-spec-only.
  The `spec.hn` transport drafted in the workflow spec is in fact
  `rfl` for the canonical spec, so the witness reduces to the bare
  `mkSurfaceAttackerX d` after `subst hspec`. -/

/-- **(6) Pauli-weight upper bound**: there exists a weight-`d` error
    in `barZClass spec.toAligned` for the canonical surface spec.

    Witness: `mkSurfaceAttackerX d`. -/
theorem surface_dcirc_le_d_pauli
    (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (spec : NZSurfaceSpec d)
    (hspec : spec = mkSurfaceNZSurfaceSpec d hd3 hodd) :
    ∃ (E : ErrorVec spec.params.n),
      ErrorVec.weight E = d ∧
      (QStab.Paper.AlignedBarrier.barZClass spec.toAligned).contains E := by
  -- After `subst hspec`, `spec.params.n` reduces to `d * d` (since
  -- `(mkSurfaceNZSurfaceSpec d hd3 hodd).hn = rfl`), so the workflow
  -- spec's `spec.hn ▸ mkSurfaceAttackerX d` transport collapses to
  -- the bare `mkSurfaceAttackerX d` (no nontrivial cast needed).
  subst hspec
  refine ⟨mkSurfaceAttackerX d,
          mkSurfaceAttackerX_weight d hd,
          mkSurfaceAttackerX_in_barZClass d hd3 hodd⟩

/-- **(7) Pauli-weight lower bound (free from `d_L_min`)**: every
    error in `barZClass spec.toAligned` has Pauli weight `≥ d`.

    *Holds for arbitrary `spec : NZSurfaceSpec d`* — this direction is
    parametric, unlike (6). -/
theorem surface_dcirc_ge_d_pauli (d : Nat) (spec : NZSurfaceSpec d) :
    ∀ (E : ErrorVec spec.params.n),
      (QStab.Paper.AlignedBarrier.barZClass spec.toAligned).contains E →
        ErrorVec.weight E ≥ d := by
  intro E hE
  -- `(AlignedBarrier.barZClass spec.toAligned).d_L = d` definitionally.
  exact (QStab.Paper.AlignedBarrier.barZClass spec.toAligned).d_L_min E hE

/-- **(8) HEADLINE — Pauli-weight `d_circ = d` for the rotated surface
    code**: every `barZClass` error has weight `≥ d`, and there exists
    a `barZClass` error of weight exactly `d`. -/
theorem surface_dcirc_eq_d_pauli
    (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (spec : NZSurfaceSpec d)
    (hspec : spec = mkSurfaceNZSurfaceSpec d hd3 hodd) :
    (∀ E : ErrorVec spec.params.n,
        (QStab.Paper.AlignedBarrier.barZClass spec.toAligned).contains E →
          ErrorVec.weight E ≥ d)
    ∧
    (∃ E : ErrorVec spec.params.n,
        ErrorVec.weight E = d ∧
        (QStab.Paper.AlignedBarrier.barZClass spec.toAligned).contains E) :=
  ⟨surface_dcirc_ge_d_pauli d spec,
   surface_dcirc_le_d_pauli d hd hd3 hodd spec hspec⟩

/-! ## `#print axioms` audit for (6)(7)(8) -/

#print axioms surface_dcirc_le_d_pauli
#print axioms surface_dcirc_ge_d_pauli
#print axioms surface_dcirc_eq_d_pauli

end QHL.Source.Examples.SurfaceParametricUpperBound
