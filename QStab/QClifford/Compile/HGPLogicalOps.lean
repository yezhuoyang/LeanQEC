import QStab.QClifford.Compile.HGPXDistance
import QStab.QClifford.Compile.CSSSplit
import QStab.Paper.LogicalCosets

/-!
# `LogicalOps` for the HGP union machine (chunk 4, route A)

The `(X̄, Z̄)` logical-operator system for `hgpUParams d hd`, with the
**maximal-isotropic** axiom proved by constructive cleaning (`k = 1`
exactness): every operator commuting with all stabilizer generators and
with both `X̄` and `Z̄` is an explicit product of stabilizer generators.

Structure (validated numerically in `notes/validate_hgp_maxiso.py`,
exhaustively for `d ≤ 4`):

* CSS split — X-type rows read only the Z-content of an error and vice
  versa, so the axiom splits into two classical statements;
* the Z-side is cleaned in three phases: **A1** sector-2 peel by a
  closed-form prefix-parity corrector, **A2** column-constancy (derived
  from the X-check constraints, no operations), **A3** adjacent-column
  pair-cleaners whose sector-2 part telescopes to zero;
* the X-side is the `Φ`-transport of the Z-side along the chunk-2/3
  duality machinery — no second cleaning proof.

All statements are over the real objects: `mkHGPRepStabilizers`,
`hgpUParams`, `mkHGPRepLogicalZ` / `mkHGPRepLogicalX`.  Stabilizer-product
witnesses are explicit lists of generators; no `decide` anywhere.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QStab.Examples.HGPParametric
open QStab.Paper.LogicalCosets
open QStab.Paper.LogicalCosets.General (listProd parity_listProd)
open QHL
open QHL.Source.Examples.HGPUnionSpec

/-! ## Small Pauli/Finset helpers -/

private theorem anticommutes_I_right (p : Pauli) :
    ErrorVec.Pauli.anticommutes p Pauli.I = false := by cases p <;> rfl

private theorem anticommutes_I_left (p : Pauli) :
    ErrorVec.Pauli.anticommutes Pauli.I p = false := rfl

/-- Cardinality of a filter whose predicate is concentrated on one point. -/
private theorem card_filter_single {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (q0 : Fin n) (h : ∀ q, P q → q = q0) :
    (Finset.univ.filter P).card = if P q0 then 1 else 0 := by
  by_cases h0 : P q0
  · rw [if_pos h0]
    apply Finset.card_eq_one.mpr
    refine ⟨q0, ?_⟩
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hP => h q hP, fun he => he.symm ▸ h0⟩
  · rw [if_neg h0]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q _ hP
    exact h0 ((h q hP) ▸ hP)

/-- Cardinality of a filter whose predicate is concentrated on two points. -/
private theorem card_filter_pair {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (q1 q2 : Fin n) (hne : q1 ≠ q2) (h : ∀ q, P q → q = q1 ∨ q = q2) :
    (Finset.univ.filter P).card
      = (if P q1 then 1 else 0) + (if P q2 then 1 else 0) := by
  have hsub : Finset.univ.filter P = ({q1, q2} : Finset (Fin n)).filter P := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨fun hP => ⟨h q hP, hP⟩, fun hP => hP.2⟩
  rw [hsub, Finset.filter_insert, Finset.filter_singleton]
  by_cases h1 : P q1 <;> by_cases h2 : P q2 <;>
    simp [h1, h2, Finset.card_insert_of_notMem, Finset.mem_singleton, hne]

/-! ## The side fields -/

/-- `X̄` commutes with every stabilizer generator: transported from
    `logicalZ_normalizer` through the duality (`X̄ = Φ Z̄`, `Φ`-image of a
    generator row is the dual check's row). -/
theorem hgp_Xbar_comm (d : Nat) (hd : 2 ≤ d) :
    ∀ s : Fin (hgpUParams d hd).numStab,
      ErrorVec.parity ((hgpUParams d hd).stabilizers s)
        (mkHGPRepLogicalX d hd) = false := by
  intro s
  show ErrorVec.parity (mkHGPRepStabilizers d s)
    (hgpPhi d hd (mkHGPRepLogicalZ d)) = false
  calc ErrorVec.parity (mkHGPRepStabilizers d s)
        (hgpPhi d hd (mkHGPRepLogicalZ d))
      = ErrorVec.parity (hgpPhi d hd (hgpPhi d hd (mkHGPRepStabilizers d s)))
          (hgpPhi d hd (mkHGPRepLogicalZ d)) :=
        (congrArg (fun S => ErrorVec.parity S (hgpPhi d hd (mkHGPRepLogicalZ d)))
          (hgpPhi_involutive d hd (mkHGPRepStabilizers d s))).symm
    _ = ErrorVec.parity (hgpPhi d hd (mkHGPRepStabilizers d s))
          (mkHGPRepLogicalZ d) :=
        parity_phi d hd (hgpPhi d hd (mkHGPRepStabilizers d s)) (mkHGPRepLogicalZ d)
    _ = false := by
        rw [mkHGPRepStabilizers_phi d hd s]
        exact (exactUnionHGPSpec d hd).logicalZ_normalizer _

/-- `X̄` and `Z̄` anticommute: the two representatives overlap exactly at
    the sector-1 corner qubit `(0, 0)`, with `X` against `Z`. -/
theorem hgp_Xbar_anticomm_Zbar (d : Nat) (hd : 2 ≤ d) :
    ErrorVec.parity (mkHGPRepLogicalX d hd) (mkHGPRepLogicalZ d) = true := by
  have hdd : 0 < d * d := Nat.mul_pos (by omega) (by omega)
  have h0lt : 0 < hgpN d :=
    Nat.lt_of_lt_of_le hdd (Nat.le_add_right _ _)
  unfold ErrorVec.parity
  rw [card_filter_single _ ⟨0, h0lt⟩ ?uniq]
  case uniq =>
    intro q hq
    by_cases hx : q.val < d * d ∧ q.val / d = 0
    · by_cases hz : q.val < d * d ∧ q.val % d = 0
      · apply Fin.ext
        show q.val = 0
        have hdm := Nat.div_add_mod q.val d
        rw [hx.2, hz.2, Nat.mul_zero, Nat.add_zero] at hdm
        exact hdm.symm
      · exfalso
        have hzv : mkHGPRepLogicalZ d q = Pauli.I := by
          unfold mkHGPRepLogicalZ
          rw [if_neg hz]
        rw [hzv, anticommutes_I_right] at hq
        exact Bool.noConfusion hq
    · exfalso
      have hxv : mkHGPRepLogicalX d hd q = Pauli.I := by
        rw [mkHGPRepLogicalX_spec, if_neg hx]
      rw [hxv, anticommutes_I_left] at hq
      exact Bool.noConfusion hq
  · have hP0 : ErrorVec.Pauli.anticommutes
        (mkHGPRepLogicalX d hd ⟨0, h0lt⟩) (mkHGPRepLogicalZ d ⟨0, h0lt⟩) = true := by
      have hxv : mkHGPRepLogicalX d hd ⟨0, h0lt⟩ = Pauli.X := by
        rw [mkHGPRepLogicalX_spec, if_pos ⟨hdd, Nat.zero_div d⟩]
      have hzv : mkHGPRepLogicalZ d ⟨0, h0lt⟩ = Pauli.Z := by
        unfold mkHGPRepLogicalZ
        rw [if_pos ⟨hdd, Nat.zero_mod d⟩]
      rw [hxv, hzv]
      rfl
    rw [if_pos hP0]
    rfl

/-! ## The xor-fold engine

Products of Z-type rows are governed by the parity of the per-position
live-factor count; the two concentration lemmas below evaluate that parity
when the live factors sit at one or two known list positions. -/

private def liveP : Pauli → Bool
  | Pauli.I => false
  | _ => true

private def xfold : List Bool → Bool
  | [] => false
  | b :: l => xor b (xfold l)

private theorem xfold_map_false {α : Type _} :
    ∀ (l : List α) (g : α → Bool), (∀ a ∈ l, g a = false) →
      xfold (l.map g) = false
  | [], _, _ => rfl
  | a :: l, g, h => by
    show xor (g a) (xfold (l.map g)) = false
    rw [h a (List.mem_cons.mpr (Or.inl rfl)),
      xfold_map_false l g (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))]
    rfl

private theorem xfold_map_one_point {α : Type _} :
    ∀ (l : List α), l.Nodup → ∀ (g : α → Bool) (c : α), c ∈ l →
      (∀ a ∈ l, g a = true → a = c) → xfold (l.map g) = g c
  | [], _, _, _, hc, _ => absurd hc (List.not_mem_nil)
  | a :: l, hnd, g, c, hc, hg => by
    have hnd' := List.nodup_cons.mp hnd
    show xor (g a) (xfold (l.map g)) = g c
    rcases List.mem_cons.mp hc with rfl | hcl
    · have hfalse : ∀ b ∈ l, g b = false := by
        intro b hb
        cases hgb : g b
        · rfl
        · exact absurd ((hg b (List.mem_cons.mpr (Or.inr hb)) hgb) ▸ hb) hnd'.1
      rw [xfold_map_false l g hfalse, Bool.xor_false]
    · have hga : g a = false := by
        cases hga : g a
        · rfl
        · have hac : a = c := hg a (List.mem_cons.mpr (Or.inl rfl)) hga
          exact absurd hcl (hac ▸ hnd'.1)
      rw [hga, xfold_map_one_point l hnd'.2 g c hcl
        (fun b hb hgb => hg b (List.mem_cons.mpr (Or.inr hb)) hgb), Bool.false_xor]

private theorem xfold_map_two_point {α : Type _} :
    ∀ (l : List α), l.Nodup → ∀ (g : α → Bool) (c1 c2 : α), c1 ≠ c2 →
      c1 ∈ l → c2 ∈ l → (∀ a ∈ l, g a = true → a = c1 ∨ a = c2) →
      xfold (l.map g) = xor (g c1) (g c2)
  | [], _, _, _, _, _, hc1, _, _ => absurd hc1 (List.not_mem_nil)
  | a :: l, hnd, g, c1, c2, hne, hc1, hc2, hg => by
    have hnd' := List.nodup_cons.mp hnd
    show xor (g a) (xfold (l.map g)) = xor (g c1) (g c2)
    rcases List.mem_cons.mp hc1 with rfl | hc1l
    · have hc2l : c2 ∈ l := by
        rcases List.mem_cons.mp hc2 with rfl | h
        · exact absurd rfl hne
        · exact h
      rw [xfold_map_one_point l hnd'.2 g c2 hc2l (fun b hb hgb => by
        rcases hg b (List.mem_cons.mpr (Or.inr hb)) hgb with h | h
        · exact absurd (h ▸ hb) hnd'.1
        · exact h)]
    · rcases List.mem_cons.mp hc2 with rfl | hc2l
      · rw [xfold_map_one_point l hnd'.2 g c1 hc1l (fun b hb hgb => by
          rcases hg b (List.mem_cons.mpr (Or.inr hb)) hgb with h | h
          · exact h
          · exact absurd (h ▸ hb) hnd'.1), Bool.xor_comm]
      · have hga : g a = false := by
          cases hga : g a
          · rfl
          · rcases hg a (List.mem_cons.mpr (Or.inl rfl)) hga with h | h
            · exact absurd hc1l (h ▸ hnd'.1)
            · exact absurd hc2l (h ▸ hnd'.1)
        rw [hga, xfold_map_two_point l hnd'.2 g c1 c2 hne hc1l hc2l
          (fun b hb hgb => hg b (List.mem_cons.mpr (Or.inr hb)) hgb),
          Bool.false_xor]

/-! ## `listProd` and multiplication helpers -/

private theorem listProd_ztype_at {n : Nat} :
    ∀ (l : List (ErrorVec n)),
      (∀ v ∈ l, ∀ q, v q = Pauli.Z ∨ v q = Pauli.I) → ∀ q : Fin n,
      listProd l q = cond (xfold (l.map fun v => liveP (v q))) Pauli.Z Pauli.I
  | [], _, q => rfl
  | v :: l, hl, q => by
    show Pauli.mul (v q) (listProd l q)
      = cond (xor (liveP (v q)) (xfold (l.map fun w => liveP (w q)))) Pauli.Z Pauli.I
    rw [listProd_ztype_at l (fun w hw => hl w (List.mem_cons.mpr (Or.inr hw))) q]
    rcases hl v (List.mem_cons.mpr (Or.inl rfl)) q with hv | hv <;> rw [hv] <;>
      cases xfold (l.map fun w => liveP (w q)) <;> rfl

private theorem instab_listProd {P : QECParams} :
    ∀ l : List (ErrorVec P.n), (∀ v ∈ l, InStab P v) → InStab P (listProd l)
  | [], _ => InStab.identity
  | v :: l, h =>
    InStab.mul (h v (List.mem_cons.mpr (Or.inl rfl)))
      (instab_listProd l fun w hw => h w (List.mem_cons.mpr (Or.inr hw)))

private theorem foldr_xor_false {n : Nat} (F : ErrorVec n) :
    ∀ l : List (ErrorVec n), (∀ v ∈ l, ErrorVec.parity F v = false) →
      l.foldr (fun G acc => xor (ErrorVec.parity F G) acc) false = false
  | [], _ => rfl
  | v :: l, h => by
    show xor (ErrorVec.parity F v) _ = false
    rw [h v (List.mem_cons.mpr (Or.inl rfl)),
      foldr_xor_false F l (fun w hw => h w (List.mem_cons.mpr (Or.inr hw)))]
    rfl

private theorem parity_listProd_false {n : Nat} (F : ErrorVec n)
    (l : List (ErrorVec n)) (h : ∀ v ∈ l, ErrorVec.parity F v = false) :
    ErrorVec.parity F (listProd l) = false := by
  rw [parity_listProd]
  exact foldr_xor_false F l h

private theorem ztype_mul {n : Nat} {v w : ErrorVec n}
    (hv : ∀ q, v q = Pauli.Z ∨ v q = Pauli.I)
    (hw : ∀ q, w q = Pauli.Z ∨ w q = Pauli.I) :
    ∀ q, ErrorVec.mul v w q = Pauli.Z ∨ ErrorVec.mul v w q = Pauli.I := by
  intro q
  show Pauli.mul (v q) (w q) = _ ∨ Pauli.mul (v q) (w q) = _
  rcases hv q with h1 | h1 <;> rcases hw q with h2 | h2 <;> rw [h1, h2] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl

private theorem mul_mul_cancel {n : Nat} (v E : ErrorVec n) :
    ErrorVec.mul v (ErrorVec.mul v E) = E := by
  funext q
  show Pauli.mul (v q) (Pauli.mul (v q) (E q)) = E q
  rw [← Pauli.mul_assoc, Pauli.mul_self, Pauli.I_mul]

/-! ## Local coordinate arithmetic -/

private theorem div_mul_add'' (m a b : Nat) (hm : 0 < m) (hb : b < m) :
    (a * m + b) / m = a := by
  rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mod_mul_add'' (m a b : Nat) (hb : b < m) : (a * m + b) % m = b := by
  rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private theorem mul_add_lt_gen (a b M m : Nat) (ha : a < M) (hb : b < m) :
    a * m + b < M * m := by
  calc a * m + b < a * m + m := by omega
    _ = (a + 1) * m := (Nat.succ_mul _ _).symm
    _ ≤ M * m := Nat.mul_le_mul_right _ ha

/-- Sector-2 cell `(a, b)` as an ambient qubit index. -/
private def s2Q (d a b : Nat) : Nat := d * d + (a * (d - 1) + b)

private theorem s2Q_lt (d a b : Nat) (ha : a < d - 1) (hb : b < d - 1) :
    s2Q d a b < hgpN d := by
  show d * d + (a * (d - 1) + b) < d * d + (d - 1) * (d - 1)
  exact Nat.add_lt_add_left (mul_add_lt_gen a b (d - 1) (d - 1) ha hb) _

/-! ## Z-check rows and the A1 sector-2 peel -/

/-- The Z-check generator row with schedule offset `kp = A·(d−1) + jz`. -/
private def zRow (d : Nat) (kp : Fin ((d - 1) * d)) : ErrorVec (hgpN d) :=
  mkHGPRepStabilizers d ⟨(d - 1) * d + kp.val, by
    show (d - 1) * d + kp.val < 2 * ((d - 1) * d); omega⟩

private theorem zRow_ztype (d : Nat) (hd : 2 ≤ d) (kp : Fin ((d - 1) * d)) :
    ∀ q, zRow d kp q = Pauli.Z ∨ zRow d kp q = Pauli.I := by
  intro q
  show QStab.Examples.HGPParametric.stabEntry d ((d - 1) * d + kp.val) q.val = Pauli.Z
    ∨ QStab.Examples.HGPParametric.stabEntry d ((d - 1) * d + kp.val) q.val = Pauli.I
  have hzk : (d - 1) * d ≤ (d - 1) * d + kp.val := Nat.le_add_right _ _
  have hk2 : (d - 1) * d + kp.val < 2 * ((d - 1) * d) := by omega
  by_cases hq : q.val < d * d
  · rw [stabEntry_Z_s1_eq d _ q.val hzk hk2 hq]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have hq2 : q.val < d * d + (d - 1) * (d - 1) := q.isLt
    rw [stabEntry_Z_s2_eq d _ q.val hzk hk2 hq hq2]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem zRow_instab (d : Nat) (hd : 2 ≤ d) (kp : Fin ((d - 1) * d)) :
    InStab (hgpUParams d hd) (zRow d kp) :=
  InStab.gen (P := hgpUParams d hd) ⟨(d - 1) * d + kp.val, by
    show (d - 1) * d + kp.val < 2 * ((d - 1) * d); omega⟩

/-- Value of a Z-check row at a sector-2 cell: `Z` exactly when the check is
    one of the two vertical neighbours in the cell's column. -/
private theorem zRow_s2 (d : Nat) (hd : 2 ≤ d) (kp : Fin ((d - 1) * d))
    (a b : Nat) (ha : a < d - 1) (hb : b < d - 1) (hq : s2Q d a b < hgpN d) :
    zRow d kp ⟨s2Q d a b, hq⟩
      = if kp.val = a * (d - 1) + b ∨ kp.val = (a + 1) * (d - 1) + b
        then Pauli.Z else Pauli.I := by
  have hd1 : 0 < d - 1 := by omega
  show QStab.Examples.HGPParametric.stabEntry d ((d - 1) * d + kp.val) (s2Q d a b) = _
  have hzk : (d - 1) * d ≤ (d - 1) * d + kp.val := Nat.le_add_right _ _
  have hk2 : (d - 1) * d + kp.val < 2 * ((d - 1) * d) := by omega
  have hq1 : ¬s2Q d a b < d * d :=
    Nat.not_lt.mpr (Nat.le_add_right _ _)
  have hq2 : s2Q d a b < d * d + (d - 1) * (d - 1) := hq
  have e1 : s2Q d a b - d * d = a * (d - 1) + b := Nat.add_sub_cancel_left _ _
  have e2 : (d - 1) * d + kp.val - (d - 1) * d = kp.val :=
    Nat.add_sub_cancel_left _ _
  rw [stabEntry_Z_s2_eq d _ _ hzk hk2 hq1 hq2, e1, e2,
    mod_mul_add'' (d - 1) a b hb, div_mul_add'' (d - 1) a b hd1 hb]
  by_cases hc : kp.val = a * (d - 1) + b ∨ kp.val = (a + 1) * (d - 1) + b
  · rw [if_pos hc]
    rcases hc with hc | hc
    · rw [if_pos ⟨by rw [hc, mod_mul_add'' (d - 1) a b hb],
        Or.inl (by rw [hc, div_mul_add'' (d - 1) a b hd1 hb])⟩]
    · rw [if_pos ⟨by rw [hc, mod_mul_add'' (d - 1) (a + 1) b hb],
        Or.inr (by rw [hc, div_mul_add'' (d - 1) (a + 1) b hd1 hb])⟩]
  · rw [if_neg hc, if_neg ?_]
    intro ⟨h1, h2⟩
    have hdm := Nat.div_add_mod kp.val (d - 1)
    rcases h2 with h2 | h2
    · exact hc (Or.inl (by rw [← hdm, ← h1, ← h2, Nat.mul_comm]))
    · exact hc (Or.inr (by rw [← hdm, ← h1, ← h2, Nat.mul_comm]))

/-- Prefix parity of column `b` of the sector-2 support of `E` below row `A` —
    the closed-form A1 corrector selector (validated in
    `notes/validate_hgp_maxiso.py`). -/
private def s2LiveB (d : Nat) (E : ErrorVec (hgpN d)) (a b : Nat) : Bool :=
  if h : s2Q d a b < hgpN d then liveP (E ⟨s2Q d a b, h⟩) else false

private def a1Pref (d : Nat) (E : ErrorVec (hgpN d)) (b : Nat) : Nat → Bool
  | 0 => false
  | A + 1 => xor (a1Pref d E b A) (s2LiveB d E A b)

/-- One corrector factor: the Z-check row when selected, identity otherwise. -/
private def a1Row (d : Nat) (E : ErrorVec (hgpN d)) (kp : Fin ((d - 1) * d)) :
    ErrorVec (hgpN d) :=
  cond (a1Pref d E (kp.val % (d - 1)) (kp.val / (d - 1)))
    (zRow d kp) (ErrorVec.identity (hgpN d))

/-- The A1 corrector. -/
private def a1List (d : Nat) (E : ErrorVec (hgpN d)) : List (ErrorVec (hgpN d)) :=
  (List.finRange ((d - 1) * d)).map (a1Row d E)

private theorem identity_ztype {n : Nat} :
    ∀ q : Fin n, ErrorVec.identity n q = Pauli.Z ∨ ErrorVec.identity n q = Pauli.I :=
  fun _ => Or.inr rfl

private theorem a1Row_ztype (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (kp : Fin ((d - 1) * d)) :
    ∀ q, a1Row d E kp q = Pauli.Z ∨ a1Row d E kp q = Pauli.I := by
  unfold a1Row
  cases a1Pref d E (kp.val % (d - 1)) (kp.val / (d - 1))
  · exact identity_ztype
  · exact zRow_ztype d hd kp

private theorem a1List_ztype (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d)) :
    ∀ v ∈ a1List d E, ∀ q, v q = Pauli.Z ∨ v q = Pauli.I := by
  intro v hv
  obtain ⟨kp, -, rfl⟩ := List.mem_map.mp hv
  exact a1Row_ztype d hd E kp

private theorem a1List_instab (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d)) :
    ∀ v ∈ a1List d E, InStab (hgpUParams d hd) v := by
  intro v hv
  obtain ⟨kp, -, rfl⟩ := List.mem_map.mp hv
  unfold a1Row
  cases a1Pref d E (kp.val % (d - 1)) (kp.val / (d - 1))
  · exact InStab.identity
  · exact zRow_instab d hd kp

private theorem liveP_a1Row (d : Nat) (E : ErrorVec (hgpN d))
    (kp : Fin ((d - 1) * d)) (q : Fin (hgpN d)) :
    liveP (a1Row d E kp q)
      = (a1Pref d E (kp.val % (d - 1)) (kp.val / (d - 1)) && liveP (zRow d kp q)) := by
  unfold a1Row
  cases a1Pref d E (kp.val % (d - 1)) (kp.val / (d - 1)) <;> rfl

/-- **A1 cancellation at one sector-2 cell**: the corrector's live-factor
    parity at cell `(a, b)` telescopes to the cell's own liveness. -/
private theorem a1_clean_cell (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (hZ : ∀ q, E q = Pauli.Z ∨ E q = Pauli.I)
    (a b : Nat) (ha : a < d - 1) (hb : b < d - 1) (hq : s2Q d a b < hgpN d) :
    ErrorVec.mul (listProd (a1List d E)) E ⟨s2Q d a b, hq⟩ = Pauli.I := by
  have hd1 : 0 < d - 1 := by omega
  have hc1lt : a * (d - 1) + b < (d - 1) * d := by
    rw [Nat.mul_comm (d - 1) d]
    exact mul_add_lt_gen a b d (d - 1) (by omega) hb
  have hc2lt : (a + 1) * (d - 1) + b < (d - 1) * d := by
    rw [Nat.mul_comm (d - 1) d]
    exact mul_add_lt_gen (a + 1) b d (d - 1) (by omega) hb
  have hne : (⟨a * (d - 1) + b, hc1lt⟩ : Fin ((d - 1) * d))
      ≠ ⟨(a + 1) * (d - 1) + b, hc2lt⟩ := by
    intro h
    have hv : a * (d - 1) + b = (a + 1) * (d - 1) + b := congrArg Fin.val h
    have hsm : (a + 1) * (d - 1) = a * (d - 1) + (d - 1) := Nat.succ_mul _ _
    rw [hsm] at hv
    omega
  show Pauli.mul (listProd (a1List d E) ⟨s2Q d a b, hq⟩) (E ⟨s2Q d a b, hq⟩)
    = Pauli.I
  rw [listProd_ztype_at (a1List d E) (a1List_ztype d hd E) ⟨s2Q d a b, hq⟩]
  have hxf : xfold ((a1List d E).map fun v => liveP (v ⟨s2Q d a b, hq⟩))
      = liveP (E ⟨s2Q d a b, hq⟩) := by
    unfold a1List
    rw [List.map_map]
    rw [xfold_map_two_point (List.finRange ((d - 1) * d)) (List.nodup_finRange _)
      ((fun v => liveP (v ⟨s2Q d a b, hq⟩)) ∘ a1Row d E)
      ⟨a * (d - 1) + b, hc1lt⟩ ⟨(a + 1) * (d - 1) + b, hc2lt⟩ hne
      (List.mem_finRange _) (List.mem_finRange _) ?conc]
    case conc =>
      intro kp _ hgkp
      have h1 : liveP (a1Row d E kp ⟨s2Q d a b, hq⟩) = true := hgkp
      rw [liveP_a1Row] at h1
      have h2 : liveP (zRow d kp ⟨s2Q d a b, hq⟩) = true := by
        cases h3 : liveP (zRow d kp ⟨s2Q d a b, hq⟩)
        · rw [h3, Bool.and_false] at h1
          exact Bool.noConfusion h1
        · rfl
      rw [zRow_s2 d hd kp a b ha hb hq] at h2
      by_cases hc : kp.val = a * (d - 1) + b ∨ kp.val = (a + 1) * (d - 1) + b
      · rcases hc with hc | hc
        · exact Or.inl (Fin.ext hc)
        · exact Or.inr (Fin.ext hc)
      · rw [if_neg hc] at h2
        exact Bool.noConfusion h2
    -- evaluate the two live points
    show xor (liveP (a1Row d E ⟨a * (d - 1) + b, hc1lt⟩ ⟨s2Q d a b, hq⟩))
      (liveP (a1Row d E ⟨(a + 1) * (d - 1) + b, hc2lt⟩ ⟨s2Q d a b, hq⟩)) = _
    rw [liveP_a1Row, liveP_a1Row,
      zRow_s2 d hd ⟨a * (d - 1) + b, hc1lt⟩ a b ha hb hq,
      zRow_s2 d hd ⟨(a + 1) * (d - 1) + b, hc2lt⟩ a b ha hb hq,
      if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
    show xor
      (a1Pref d E ((a * (d - 1) + b) % (d - 1)) ((a * (d - 1) + b) / (d - 1)) && true)
      (a1Pref d E (((a + 1) * (d - 1) + b) % (d - 1))
        (((a + 1) * (d - 1) + b) / (d - 1)) && true) = _
    rw [Bool.and_true, Bool.and_true,
      mod_mul_add'' (d - 1) a b hb, div_mul_add'' (d - 1) a b hd1 hb,
      mod_mul_add'' (d - 1) (a + 1) b hb, div_mul_add'' (d - 1) (a + 1) b hd1 hb]
    show xor (a1Pref d E b a) (xor (a1Pref d E b a) (s2LiveB d E a b)) = _
    rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    show (if h : s2Q d a b < hgpN d then liveP (E ⟨s2Q d a b, h⟩) else false) = _
    rw [dif_pos hq]
  rw [hxf]
  rcases hZ ⟨s2Q d a b, hq⟩ with h | h <;> rw [h] <;> rfl

/-- **A1**: the corrector clears the whole sector-2 block, unconditionally. -/
private theorem a1_clean (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (hZ : ∀ q, E q = Pauli.Z ∨ E q = Pauli.I) :
    ∀ q : Fin (hgpN d), d * d ≤ q.val →
      ErrorVec.mul (listProd (a1List d E)) E q = Pauli.I := by
  intro q hq
  have hqlt : q.val < d * d + (d - 1) * (d - 1) := q.isLt
  have hplt : q.val - d * d < (d - 1) * (d - 1) := by omega
  have ha : (q.val - d * d) / (d - 1) < d - 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr hplt
  have hb : (q.val - d * d) % (d - 1) < d - 1 := Nat.mod_lt _ (by omega)
  have hqe : q.val = s2Q d ((q.val - d * d) / (d - 1)) ((q.val - d * d) % (d - 1)) := by
    show q.val = d * d + ((q.val - d * d) / (d - 1) * (d - 1) + (q.val - d * d) % (d - 1))
    have hdm := Nat.div_add_mod (q.val - d * d) (d - 1)
    rw [Nat.mul_comm ((q.val - d * d) / (d - 1)) (d - 1)]
    omega
  have hcell : q = ⟨s2Q d ((q.val - d * d) / (d - 1)) ((q.val - d * d) % (d - 1)),
      hqe ▸ q.isLt⟩ := Fin.ext hqe
  rw [hcell]
  exact a1_clean_cell d hd E hZ _ _ ha hb _

/-! ## X-check rows and the A2 column-constancy -/

/-- The X-check generator row with check offset `kx = i·d + j`. -/
private def xRow (d : Nat) (kx : Fin ((d - 1) * d)) : ErrorVec (hgpN d) :=
  mkHGPRepStabilizers d ⟨kx.val, by
    show kx.val < 2 * ((d - 1) * d); omega⟩

private theorem xRow_xtype (d : Nat) (hd : 2 ≤ d) (kx : Fin ((d - 1) * d)) :
    ∀ q, xRow d kx q = Pauli.X ∨ xRow d kx q = Pauli.I := by
  intro q
  show QStab.Examples.HGPParametric.stabEntry d kx.val q.val = Pauli.X
    ∨ QStab.Examples.HGPParametric.stabEntry d kx.val q.val = Pauli.I
  by_cases hq : q.val < d * d
  · rw [stabEntry_X_s1_eq d kx.val q.val kx.isLt hq]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have hq2 : q.val < d * d + (d - 1) * (d - 1) := q.isLt
    rw [stabEntry_X_s2_eq d kx.val q.val kx.isLt hq hq2]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Value of an X-check row at a sector-1 cell (nat-indexed check offset). -/
private theorem xRow_s1' (d : Nat) (hd : 2 ≤ d) (kxv : Nat) (hkx : kxv < (d - 1) * d)
    (r c : Nat) (hr : r < d) (hc : c < d) (hq : r * d + c < hgpN d) :
    xRow d ⟨kxv, hkx⟩ ⟨r * d + c, hq⟩
      = if c = kxv % d ∧ (r = kxv / d ∨ r = kxv / d + 1)
        then Pauli.X else Pauli.I := by
  have hd0 : 0 < d := by omega
  have hq1 : r * d + c < d * d := mul_add_lt_gen r c d d hr hc
  show QStab.Examples.HGPParametric.stabEntry d kxv (r * d + c) = _
  rw [stabEntry_X_s1_eq d kxv (r * d + c) hkx hq1,
    mod_mul_add'' d r c hc, div_mul_add'' d r c hd0 hc]

/-- Two-point evaluation of a false parity: if the anticommutation predicate
    is concentrated on two positions, its values there agree. -/
private theorem parity_false_pair {n : Nat} (S E : ErrorVec n) (q1 q2 : Fin n)
    (hne : q1 ≠ q2)
    (hconc : ∀ q, ErrorVec.Pauli.anticommutes (S q) (E q) = true → q = q1 ∨ q = q2)
    (hpar : ErrorVec.parity S E = false) :
    ErrorVec.Pauli.anticommutes (S q1) (E q1)
      = ErrorVec.Pauli.anticommutes (S q2) (E q2) := by
  have hcard : (Finset.univ.filter fun i =>
        ErrorVec.Pauli.anticommutes (S i) (E i)).card
      = (if ErrorVec.Pauli.anticommutes (S q1) (E q1) then 1 else 0)
        + (if ErrorVec.Pauli.anticommutes (S q2) (E q2) then 1 else 0) :=
    card_filter_pair _ q1 q2 hne (fun q hq => hconc q hq)
  unfold ErrorVec.parity at hpar
  rw [hcard] at hpar
  cases h1 : ErrorVec.Pauli.anticommutes (S q1) (E q1) <;>
    cases h2 : ErrorVec.Pauli.anticommutes (S q2) (E q2) <;>
      rw [h1, h2] at hpar <;> simp at hpar <;> rfl

/-- **A2 step**: with sector 2 dead, a false X-check parity forces equal
    entries at the check's two sector-1 cells. -/
private theorem a2_step (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (hZ : ∀ q, E q = Pauli.Z ∨ E q = Pauli.I)
    (hs2 : ∀ q : Fin (hgpN d), d * d ≤ q.val → E q = Pauli.I)
    (i j : Nat) (hi : i < d - 1) (hj : j < d)
    (hkx : i * d + j < (d - 1) * d)
    (hpar : ErrorVec.parity (xRow d ⟨i * d + j, hkx⟩) E = false)
    (hq1 : i * d + j < hgpN d) (hq2 : (i + 1) * d + j < hgpN d) :
    E ⟨i * d + j, hq1⟩ = E ⟨(i + 1) * d + j, hq2⟩ := by
  have hd0 : 0 < d := by omega
  have hne : (⟨i * d + j, hq1⟩ : Fin (hgpN d)) ≠ ⟨(i + 1) * d + j, hq2⟩ := by
    intro h
    have hv : i * d + j = (i + 1) * d + j := congrArg Fin.val h
    have hsm : (i + 1) * d = i * d + d := Nat.succ_mul i d
    rw [hsm] at hv
    omega
  have hx1 : xRow d ⟨i * d + j, hkx⟩ ⟨i * d + j, hq1⟩ = Pauli.X := by
    rw [xRow_s1' d hd (i * d + j) hkx i j (by omega) hj hq1,
      if_pos ⟨(mod_mul_add'' d i j hj).symm,
        Or.inl (div_mul_add'' d i j hd0 hj).symm⟩]
  have hx2 : xRow d ⟨i * d + j, hkx⟩ ⟨(i + 1) * d + j, hq2⟩ = Pauli.X := by
    rw [xRow_s1' d hd (i * d + j) hkx (i + 1) j (by omega) hj hq2,
      if_pos ⟨(mod_mul_add'' d i j hj).symm,
        Or.inr (by rw [div_mul_add'' d i j hd0 hj])⟩]
  have hconc : ∀ q, ErrorVec.Pauli.anticommutes
      (xRow d ⟨i * d + j, hkx⟩ q) (E q) = true →
      q = ⟨i * d + j, hq1⟩ ∨ q = ⟨(i + 1) * d + j, hq2⟩ := by
    intro q hq
    by_cases hqd : q.val < d * d
    · have hrq : q.val / d < d := (Nat.div_lt_iff_lt_mul hd0).mpr hqd
      have hcq : q.val % d < d := Nat.mod_lt _ hd0
      have hqe : q = ⟨q.val / d * d + q.val % d, by
          rw [Nat.mul_comm (q.val / d) d, Nat.div_add_mod]; exact q.isLt⟩ :=
        Fin.ext (by
          show q.val = q.val / d * d + q.val % d
          rw [Nat.mul_comm (q.val / d) d, Nat.div_add_mod])
      rw [hqe, xRow_s1' d hd (i * d + j) hkx (q.val / d) (q.val % d) hrq hcq _] at hq
      by_cases hcond : q.val % d = (i * d + j) % d ∧
          (q.val / d = (i * d + j) / d ∨ q.val / d = (i * d + j) / d + 1)
      · obtain ⟨hcj, hri⟩ := hcond
        rw [mod_mul_add'' d i j hj] at hcj
        rw [div_mul_add'' d i j hd0 hj] at hri
        rcases hri with hri | hri
        · left
          exact Fin.ext (by
            show q.val = i * d + j
            rw [← hri, ← hcj, Nat.mul_comm (q.val / d) d, Nat.div_add_mod])
        · right
          exact Fin.ext (by
            show q.val = (i + 1) * d + j
            rw [← hri, ← hcj, Nat.mul_comm (q.val / d) d, Nat.div_add_mod])
      · rw [if_neg hcond, anticommutes_I_left] at hq
        exact Bool.noConfusion hq
    · rw [hs2 q (by omega), anticommutes_I_right] at hq
      exact Bool.noConfusion hq
  have hpp := parity_false_pair (xRow d ⟨i * d + j, hkx⟩) E _ _ hne hconc hpar
  rw [hx1, hx2] at hpp
  rcases hZ ⟨i * d + j, hq1⟩ with h1 | h1 <;>
    rcases hZ ⟨(i + 1) * d + j, hq2⟩ with h2 | h2 <;>
      rw [h1, h2] <;> rw [h1, h2] at hpp
  · exact Bool.noConfusion hpp
  · exact Bool.noConfusion hpp

/-- **A2**: with sector 2 dead and all X-check parities false, every sector-1
    column is constant. -/
private theorem a2_col_const (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (hZ : ∀ q, E q = Pauli.Z ∨ E q = Pauli.I)
    (hs2 : ∀ q : Fin (hgpN d), d * d ≤ q.val → E q = Pauli.I)
    (hcomm : ∀ kx : Fin ((d - 1) * d), ErrorVec.parity (xRow d kx) E = false) :
    ∀ (r c : Nat), r < d → c < d →
      ∀ (hq : r * d + c < hgpN d) (hq0 : c < hgpN d),
        E ⟨r * d + c, hq⟩ = E ⟨c, hq0⟩
  | 0, c, _, _, hq, hq0 => by
    have h0 : (⟨0 * d + c, hq⟩ : Fin (hgpN d)) = ⟨c, hq0⟩ :=
      Fin.ext (by show 0 * d + c = c; rw [Nat.zero_mul, Nat.zero_add])
    rw [h0]
  | r + 1, c, hr, hc, hq, hq0 => by
    have hr' : r < d := by omega
    have hsm : (r + 1) * d = r * d + d := Nat.succ_mul r d
    have hq' : r * d + c < hgpN d := by
      have h2 : (r + 1) * d + c < hgpN d := hq
      omega
    have hkx : r * d + c < (d - 1) * d :=
      mul_add_lt_gen r c (d - 1) d (by omega) hc
    have hstep := a2_step d hd E hZ hs2 r c (by omega) hc hkx
      (hcomm ⟨r * d + c, hkx⟩) hq' hq
    rw [← hstep]
    exact a2_col_const d hd E hZ hs2 hcomm r c hr' hc hq' hq0

/-! ## The A3 pair cleaner -/

private theorem parity_identity_right {n : Nat} (F : ErrorVec n) :
    ErrorVec.parity F (ErrorVec.identity n) = false := by
  unfold ErrorVec.parity
  have h : (Finset.univ.filter fun i : Fin n =>
      ErrorVec.Pauli.anticommutes (F i) (ErrorVec.identity n i)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q _ hP
    rw [show ErrorVec.identity n q = Pauli.I from rfl, anticommutes_I_right] at hP
    exact Bool.noConfusion hP
  rw [h]
  rfl

/-- Value of a Z-check row at a sector-1 cell (nat-indexed check offset). -/
private theorem zRow_s1' (d : Nat) (hd : 2 ≤ d) (kpv : Nat) (hkp : kpv < (d - 1) * d)
    (r c : Nat) (hr : r < d) (hc : c < d) (hq : r * d + c < hgpN d) :
    zRow d ⟨kpv, hkp⟩ ⟨r * d + c, hq⟩
      = if r = kpv / (d - 1) ∧ (c = kpv % (d - 1) ∨ c = kpv % (d - 1) + 1)
        then Pauli.Z else Pauli.I := by
  have hd0 : 0 < d := by omega
  have hq1 : r * d + c < d * d := mul_add_lt_gen r c d d hr hc
  show QStab.Examples.HGPParametric.stabEntry d ((d - 1) * d + kpv) (r * d + c) = _
  have hzk : (d - 1) * d ≤ (d - 1) * d + kpv := Nat.le_add_right _ _
  have hk2 : (d - 1) * d + kpv < 2 * ((d - 1) * d) := by omega
  have e2 : (d - 1) * d + kpv - (d - 1) * d = kpv := Nat.add_sub_cancel_left _ _
  rw [stabEntry_Z_s1_eq d _ _ hzk hk2 hq1, e2,
    mod_mul_add'' d r c hc, div_mul_add'' d r c hd0 hc]

/-- One vertical strip of Z-checks: check `(A, j)`. -/
private def pairRow (d : Nat) (j : Nat) (hj : j < d - 1) (A : Fin d) :
    ErrorVec (hgpN d) :=
  zRow d ⟨A.val * (d - 1) + j, by
    rw [Nat.mul_comm (d - 1) d]
    exact mul_add_lt_gen A.val j d (d - 1) A.isLt hj⟩

/-- The adjacent-column pair cleaner `Pair(j) = Π_A Zcheck(A, j)`. -/
private def pairList (d : Nat) (j : Nat) (hj : j < d - 1) :
    List (ErrorVec (hgpN d)) :=
  (List.finRange d).map (pairRow d j hj)

private theorem pairList_ztype (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1) :
    ∀ v ∈ pairList d j hj, ∀ q, v q = Pauli.Z ∨ v q = Pauli.I := by
  intro v hv
  obtain ⟨A, -, rfl⟩ := List.mem_map.mp hv
  exact zRow_ztype d hd _

private theorem pairList_instab (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1) :
    ∀ v ∈ pairList d j hj, InStab (hgpUParams d hd) v := by
  intro v hv
  obtain ⟨A, -, rfl⟩ := List.mem_map.mp hv
  exact zRow_instab d hd _

private theorem pairRow_s1 (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (A : Fin d) (r c : Nat) (hr : r < d) (hc : c < d) (hq : r * d + c < hgpN d) :
    pairRow d j hj A ⟨r * d + c, hq⟩
      = if r = A.val ∧ (c = j ∨ c = j + 1) then Pauli.Z else Pauli.I := by
  have hd1 : 0 < d - 1 := by omega
  unfold pairRow
  rw [zRow_s1' d hd (A.val * (d - 1) + j) _ r c hr hc hq,
    div_mul_add'' (d - 1) A.val j hd1 hj, mod_mul_add'' (d - 1) A.val j hj]

private theorem pairRow_s2 (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (A : Fin d) (a b : Nat) (ha : a < d - 1) (hb : b < d - 1)
    (hq : s2Q d a b < hgpN d) :
    pairRow d j hj A ⟨s2Q d a b, hq⟩
      = if b = j ∧ (A.val = a ∨ A.val = a + 1) then Pauli.Z else Pauli.I := by
  have hd1 : 0 < d - 1 := by omega
  unfold pairRow
  rw [zRow_s2 d hd ⟨A.val * (d - 1) + j, by
    rw [Nat.mul_comm (d - 1) d]
    exact mul_add_lt_gen A.val j d (d - 1) A.isLt hj⟩ a b ha hb hq]
  by_cases hc : b = j ∧ (A.val = a ∨ A.val = a + 1)
  · rw [if_pos hc]
    rcases hc with ⟨hbj, hAa | hAa⟩
    · rw [if_pos (Or.inl (show A.val * (d - 1) + j = a * (d - 1) + b by
        rw [hAa, hbj]))]
    · rw [if_pos (Or.inr (show A.val * (d - 1) + j = (a + 1) * (d - 1) + b by
        rw [hAa, hbj]))]
  · rw [if_neg hc, if_neg ?_]
    intro hor
    rcases hor with h | h
    · have h' : A.val * (d - 1) + j = a * (d - 1) + b := h
      have hj' : j = b := by
        have h1 : j = (A.val * (d - 1) + j) % (d - 1) :=
          (mod_mul_add'' (d - 1) A.val j hj).symm
        rw [h', mod_mul_add'' (d - 1) a b hb] at h1
        exact h1
      have hA' : A.val = a := by
        have h1 : A.val = (A.val * (d - 1) + j) / (d - 1) :=
          (div_mul_add'' (d - 1) A.val j hd1 hj).symm
        rw [h', div_mul_add'' (d - 1) a b hd1 hb] at h1
        exact h1
      exact hc ⟨hj'.symm, Or.inl hA'⟩
    · have h' : A.val * (d - 1) + j = (a + 1) * (d - 1) + b := h
      have hj' : j = b := by
        have h1 : j = (A.val * (d - 1) + j) % (d - 1) :=
          (mod_mul_add'' (d - 1) A.val j hj).symm
        rw [h', mod_mul_add'' (d - 1) (a + 1) b hb] at h1
        exact h1
      have hA' : A.val = a + 1 := by
        have h1 : A.val = (A.val * (d - 1) + j) / (d - 1) :=
          (div_mul_add'' (d - 1) A.val j hd1 hj).symm
        rw [h', div_mul_add'' (d - 1) (a + 1) b hd1 hb] at h1
        exact h1
      exact hc ⟨hj'.symm, Or.inr hA'⟩

/-- The pair cleaner on sector 1: `Z` exactly on the two full columns. -/
private theorem pairProd_s1 (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (r c : Nat) (hr : r < d) (hc : c < d) (hq : r * d + c < hgpN d) :
    listProd (pairList d j hj) ⟨r * d + c, hq⟩
      = if c = j ∨ c = j + 1 then Pauli.Z else Pauli.I := by
  rw [listProd_ztype_at (pairList d j hj) (pairList_ztype d hd j hj) _]
  by_cases hcj : c = j ∨ c = j + 1
  · rw [if_pos hcj]
    have hxf : xfold ((pairList d j hj).map
        fun v => liveP (v ⟨r * d + c, hq⟩)) = true := by
      unfold pairList
      rw [List.map_map]
      rw [xfold_map_one_point (List.finRange d) (List.nodup_finRange d)
        ((fun v => liveP (v ⟨r * d + c, hq⟩)) ∘ pairRow d j hj) ⟨r, hr⟩
        (List.mem_finRange _) ?conc]
      case conc =>
        intro A _ hA
        have h1 : liveP (pairRow d j hj A ⟨r * d + c, hq⟩) = true := hA
        rw [pairRow_s1 d hd j hj A r c hr hc hq] at h1
        by_cases hcnd : r = A.val ∧ (c = j ∨ c = j + 1)
        · exact Fin.ext hcnd.1.symm
        · rw [if_neg hcnd] at h1
          exact Bool.noConfusion h1
      show liveP (pairRow d j hj ⟨r, hr⟩ ⟨r * d + c, hq⟩) = true
      rw [pairRow_s1 d hd j hj ⟨r, hr⟩ r c hr hc hq, if_pos ⟨rfl, hcj⟩]
      rfl
    rw [hxf]
    rfl
  · rw [if_neg hcj]
    have hxf : xfold ((pairList d j hj).map
        fun v => liveP (v ⟨r * d + c, hq⟩)) = false := by
      unfold pairList
      rw [List.map_map]
      apply xfold_map_false
      intro A _
      show liveP (pairRow d j hj A ⟨r * d + c, hq⟩) = false
      rw [pairRow_s1 d hd j hj A r c hr hc hq,
        if_neg (fun hcnd => hcj hcnd.2)]
      rfl
    rw [hxf]
    rfl

/-- The pair cleaner at a row-0 cell. -/
private theorem pairProd_row0 (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (c : Nat) (hc : c < d) (hc0 : c < hgpN d) :
    listProd (pairList d j hj) ⟨c, hc0⟩
      = if c = j ∨ c = j + 1 then Pauli.Z else Pauli.I := by
  have h0c : (⟨c, hc0⟩ : Fin (hgpN d)) = ⟨0 * d + c, by
      rw [Nat.zero_mul, Nat.zero_add]; exact hc0⟩ :=
    Fin.ext (by show c = 0 * d + c; rw [Nat.zero_mul, Nat.zero_add])
  rw [h0c, pairProd_s1 d hd j hj 0 c (by omega) hc _]

private theorem pairProd_s2_cell (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (a b : Nat) (ha : a < d - 1) (hb : b < d - 1) (hq : s2Q d a b < hgpN d) :
    listProd (pairList d j hj) ⟨s2Q d a b, hq⟩ = Pauli.I := by
  rw [listProd_ztype_at (pairList d j hj) (pairList_ztype d hd j hj) _]
  have haD : a < d := by omega
  have ha1D : a + 1 < d := by omega
  have hxf : xfold ((pairList d j hj).map
      fun v => liveP (v ⟨s2Q d a b, hq⟩)) = false := by
    unfold pairList
    rw [List.map_map]
    by_cases hbj : b = j
    · subst hbj
      rw [xfold_map_two_point (List.finRange d) (List.nodup_finRange d)
        ((fun v => liveP (v ⟨s2Q d a b, hq⟩)) ∘ pairRow d b hj)
        ⟨a, haD⟩ ⟨a + 1, ha1D⟩ (Fin.ne_of_val_ne (show a ≠ a + 1 by omega))
        (List.mem_finRange _) (List.mem_finRange _) ?conc]
      case conc =>
        intro A _ hA
        have h1 : liveP (pairRow d b hj A ⟨s2Q d a b, hq⟩) = true := hA
        rw [pairRow_s2 d hd b hj A a b ha hb hq] at h1
        by_cases hcnd : b = b ∧ (A.val = a ∨ A.val = a + 1)
        · rcases hcnd.2 with h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Fin.ext h)
        · rw [if_neg hcnd] at h1
          exact Bool.noConfusion h1
      show xor (liveP (pairRow d b hj ⟨a, haD⟩ ⟨s2Q d a b, hq⟩))
        (liveP (pairRow d b hj ⟨a + 1, ha1D⟩ ⟨s2Q d a b, hq⟩)) = false
      rw [pairRow_s2 d hd b hj ⟨a, haD⟩ a b ha hb hq,
        pairRow_s2 d hd b hj ⟨a + 1, ha1D⟩ a b ha hb hq,
        if_pos ⟨rfl, Or.inl rfl⟩, if_pos ⟨rfl, Or.inr rfl⟩]
      rfl
    · apply xfold_map_false
      intro A _
      show liveP (pairRow d j hj A ⟨s2Q d a b, hq⟩) = false
      rw [pairRow_s2 d hd j hj A a b ha hb hq,
        if_neg (fun hcnd => hbj hcnd.1)]
      rfl
  rw [hxf]
  rfl

/-- **The telescope**: the pair cleaner is trivial on all of sector 2. -/
private theorem pairProd_s2 (d : Nat) (hd : 2 ≤ d) (j : Nat) (hj : j < d - 1)
    (q : Fin (hgpN d)) (hs2q : d * d ≤ q.val) :
    listProd (pairList d j hj) q = Pauli.I := by
  have hqlt : q.val < d * d + (d - 1) * (d - 1) := q.isLt
  have hplt : q.val - d * d < (d - 1) * (d - 1) := by omega
  have ha : (q.val - d * d) / (d - 1) < d - 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr hplt
  have hb : (q.val - d * d) % (d - 1) < d - 1 := Nat.mod_lt _ (by omega)
  have hqe : q.val = s2Q d ((q.val - d * d) / (d - 1)) ((q.val - d * d) % (d - 1)) := by
    show q.val = d * d + ((q.val - d * d) / (d - 1) * (d - 1) + (q.val - d * d) % (d - 1))
    have hdm := Nat.div_add_mod (q.val - d * d) (d - 1)
    rw [Nat.mul_comm ((q.val - d * d) / (d - 1)) (d - 1)]
    omega
  have hcell : q = ⟨s2Q d ((q.val - d * d) / (d - 1)) ((q.val - d * d) % (d - 1)),
      hqe ▸ q.isLt⟩ := Fin.ext hqe
  rw [hcell]
  exact pairProd_s2_cell d hd j hj _ _ ha hb _

/-! ## X̄-parity facts for the cleaners -/

private theorem parity_xbar_zRow (d : Nat) (hd : 2 ≤ d) (kp : Fin ((d - 1) * d)) :
    ErrorVec.parity (mkHGPRepLogicalX d hd) (zRow d kp) = false := by
  rw [parity_symm]
  exact hgp_Xbar_comm d hd ⟨(d - 1) * d + kp.val, by
    show (d - 1) * d + kp.val < 2 * ((d - 1) * d); omega⟩

private theorem parity_xbar_pairProd (d : Nat) (hd : 2 ≤ d) (j : Nat)
    (hj : j < d - 1) :
    ErrorVec.parity (mkHGPRepLogicalX d hd) (listProd (pairList d j hj)) = false := by
  apply parity_listProd_false
  intro v hv
  obtain ⟨A, -, rfl⟩ := List.mem_map.mp hv
  exact parity_xbar_zRow d hd _

private theorem parity_xbar_a1List (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d)) :
    ErrorVec.parity (mkHGPRepLogicalX d hd) (listProd (a1List d E)) = false := by
  apply parity_listProd_false
  intro v hv
  obtain ⟨kp, -, rfl⟩ := List.mem_map.mp hv
  unfold a1Row
  cases a1Pref d E (kp.val % (d - 1)) (kp.val / (d - 1))
  · exact parity_identity_right _
  · exact parity_xbar_zRow d hd kp

private theorem parity_xrow_a1List (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (kx : Fin ((d - 1) * d)) :
    ErrorVec.parity (xRow d kx) (listProd (a1List d E)) = false := by
  apply parity_listProd_false
  intro v hv
  obtain ⟨kp, -, rfl⟩ := List.mem_map.mp hv
  unfold a1Row
  cases a1Pref d E (kp.val % (d - 1)) (kp.val / (d - 1))
  · exact parity_identity_right _
  · exact hgpRep_stab_commute d hd
      ⟨kx.val, by show kx.val < 2 * ((d - 1) * d); omega⟩
      ⟨(d - 1) * d + kp.val, by show (d - 1) * d + kp.val < 2 * ((d - 1) * d); omega⟩

private theorem parity_xrow_pairProd (d : Nat) (hd : 2 ≤ d) (j : Nat)
    (hj : j < d - 1) (kx : Fin ((d - 1) * d)) :
    ErrorVec.parity (xRow d kx) (listProd (pairList d j hj)) = false := by
  apply parity_listProd_false
  intro v hv
  obtain ⟨A, -, rfl⟩ := List.mem_map.mp hv
  exact hgpRep_stab_commute d hd
    ⟨kx.val, by show kx.val < 2 * ((d - 1) * d); omega⟩
    ⟨(d - 1) * d + (A.val * (d - 1) + j), by
      show (d - 1) * d + (A.val * (d - 1) + j) < 2 * ((d - 1) * d)
      have := mul_add_lt_gen A.val j d (d - 1) A.isLt hj
      have h2 : d * (d - 1) = (d - 1) * d := Nat.mul_comm _ _
      omega⟩

/-- A single live row-0 cell (all others dead) makes the `X̄`-parity fire. -/
private theorem parity_xbar_single_live (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (hgpN d))
    (j : Nat) (hj : j < d) (hjn : j < hgpN d)
    (hdead : ∀ c, c < d → c ≠ j → ∀ hc0 : c < hgpN d, E ⟨c, hc0⟩ = Pauli.I)
    (hlive : E ⟨j, hjn⟩ = Pauli.Z) :
    ErrorVec.parity (mkHGPRepLogicalX d hd) E = true := by
  have hd0 : 0 < d := by omega
  unfold ErrorVec.parity
  rw [card_filter_single _ ⟨j, hjn⟩ ?uniq]
  case uniq =>
    intro q hq
    by_cases hx : q.val < d * d ∧ q.val / d = 0
    · have hqd : q.val < d := by
        have h1 := Nat.div_add_mod q.val d
        have h2 : q.val % d < d := Nat.mod_lt _ hd0
        rw [hx.2, Nat.mul_zero, Nat.zero_add] at h1
        omega
      by_cases hqj : q.val = j
      · exact Fin.ext hqj
      · exfalso
        have hEq : E q = Pauli.I := hdead q.val hqd hqj q.isLt
        rw [hEq, anticommutes_I_right] at hq
        exact Bool.noConfusion hq
    · exfalso
      have hxv : mkHGPRepLogicalX d hd q = Pauli.I := by
        rw [mkHGPRepLogicalX_spec, if_neg hx]
      rw [hxv, anticommutes_I_left] at hq
      exact Bool.noConfusion hq
  · have hxv : mkHGPRepLogicalX d hd ⟨j, hjn⟩ = Pauli.X := by
      rw [mkHGPRepLogicalX_spec,
        if_pos ⟨Nat.lt_of_lt_of_le hj (Nat.le_mul_of_pos_left d hd0),
          Nat.div_eq_of_lt hj⟩]
    have hP : ErrorVec.Pauli.anticommutes (mkHGPRepLogicalX d hd ⟨j, hjn⟩)
        (E ⟨j, hjn⟩) = true := by
      rw [hxv, hlive]
      rfl
    rw [if_pos hP]
    rfl

/-- **A3**: left-to-right sweep — with everything below column `j` dead,
    the invariant vector is a product of Z-check generators. -/
private theorem a3_descend (d : Nat) (hd : 2 ≤ d) :
    ∀ (m j : Nat), j + m = d →
    ∀ E : ErrorVec (hgpN d),
      (∀ q, E q = Pauli.Z ∨ E q = Pauli.I) →
      (∀ q : Fin (hgpN d), d * d ≤ q.val → E q = Pauli.I) →
      (∀ (r c : Nat), r < d → c < d →
        ∀ (hq : r * d + c < hgpN d) (hq0 : c < hgpN d),
          E ⟨r * d + c, hq⟩ = E ⟨c, hq0⟩) →
      (∀ c, c < j → ∀ hc0 : c < hgpN d, E ⟨c, hc0⟩ = Pauli.I) →
      ErrorVec.parity (mkHGPRepLogicalX d hd) E = false →
      InStab (hgpUParams d hd) E
  | 0, j, hjm, E, hZ, hs2, hconst, hdead, hxb => by
    have hEid : E = ErrorVec.identity (hgpN d) := by
      funext q
      by_cases hqd : q.val < d * d
      · have hr : q.val / d < d := (Nat.div_lt_iff_lt_mul (by omega)).mpr hqd
        have hc : q.val % d < d := Nat.mod_lt _ (by omega)
        have hqb : q.val / d * d + q.val % d < hgpN d := by
          rw [Nat.mul_comm (q.val / d) d, Nat.div_add_mod]
          exact q.isLt
        have hcb : q.val % d < hgpN d := by
          have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
          show q.val % d < d * d + (d - 1) * (d - 1)
          omega
        have hqe : q = ⟨q.val / d * d + q.val % d, hqb⟩ :=
          Fin.ext (by
            show q.val = q.val / d * d + q.val % d
            rw [Nat.mul_comm (q.val / d) d, Nat.div_add_mod])
        rw [hqe, hconst (q.val / d) (q.val % d) hr hc hqb hcb,
          hdead (q.val % d) (by omega) hcb]
        rfl
      · rw [hs2 q (by omega)]
        rfl
    rw [hEid]
    exact InStab.identity
  | m + 1, j, hjm, E, hZ, hs2, hconst, hdead, hxb => by
    have hjd : j < d := by omega
    have hddle : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
    have hjn : j < hgpN d := by
      show j < d * d + (d - 1) * (d - 1)
      omega
    rcases hZ ⟨j, hjn⟩ with hlive | hdeadj
    · by_cases hj1 : j < d - 1
      · -- pair-clean column j, recurse at j + 1
        have hZ2 : ∀ q, ErrorVec.mul (listProd (pairList d j hj1)) E q = Pauli.Z
            ∨ ErrorVec.mul (listProd (pairList d j hj1)) E q = Pauli.I :=
          ztype_mul (fun q => by
            rw [listProd_ztype_at (pairList d j hj1) (pairList_ztype d hd j hj1) q]
            cases xfold ((pairList d j hj1).map fun v => liveP (v q))
            · exact Or.inr rfl
            · exact Or.inl rfl) hZ
        have hs2' : ∀ q : Fin (hgpN d), d * d ≤ q.val →
            ErrorVec.mul (listProd (pairList d j hj1)) E q = Pauli.I := by
          intro q hq
          show Pauli.mul (listProd (pairList d j hj1) q) (E q) = Pauli.I
          rw [pairProd_s2 d hd j hj1 q hq, hs2 q hq]
          rfl
        have hconst2 : ∀ (r c : Nat), r < d → c < d →
            ∀ (hq : r * d + c < hgpN d) (hq0 : c < hgpN d),
            ErrorVec.mul (listProd (pairList d j hj1)) E ⟨r * d + c, hq⟩
              = ErrorVec.mul (listProd (pairList d j hj1)) E ⟨c, hq0⟩ := by
          intro r c hr hc hq hq0
          show Pauli.mul (listProd (pairList d j hj1) ⟨r * d + c, hq⟩)
              (E ⟨r * d + c, hq⟩)
            = Pauli.mul (listProd (pairList d j hj1) ⟨c, hq0⟩) (E ⟨c, hq0⟩)
          rw [pairProd_s1 d hd j hj1 r c hr hc hq, hconst r c hr hc hq hq0,
            pairProd_row0 d hd j hj1 c hc hq0]
        have hdead2 : ∀ c, c < j + 1 → ∀ hc0 : c < hgpN d,
            ErrorVec.mul (listProd (pairList d j hj1)) E ⟨c, hc0⟩ = Pauli.I := by
          intro c hc hc0
          have hcd : c < d := by omega
          show Pauli.mul (listProd (pairList d j hj1) ⟨c, hc0⟩) (E ⟨c, hc0⟩)
            = Pauli.I
          rw [pairProd_row0 d hd j hj1 c hcd hc0]
          rcases Nat.lt_or_ge c j with hcj | hcj
          · rw [if_neg (fun h => by rcases h with h | h <;> omega),
              hdead c hcj hc0]
            rfl
          · have hcj' : c = j := by omega
            subst hcj'
            rw [if_pos (Or.inl rfl),
              show E ⟨c, hc0⟩ = Pauli.Z from hlive]
            rfl
        have hxb2 : ErrorVec.parity (mkHGPRepLogicalX d hd)
            (ErrorVec.mul (listProd (pairList d j hj1)) E) = false := by
          rw [parity_mul_right, parity_xbar_pairProd d hd j hj1, hxb]
          rfl
        have hrec := a3_descend d hd m (j + 1) (by omega) _
          hZ2 hs2' hconst2 hdead2 hxb2
        have hEeq : E = ErrorVec.mul (listProd (pairList d j hj1))
            (ErrorVec.mul (listProd (pairList d j hj1)) E) :=
          (mul_mul_cancel _ E).symm
        rw [hEeq]
        exact InStab.mul (instab_listProd _ (pairList_instab d hd j hj1)) hrec
      · -- j = d - 1 and live: the X̄-parity fires — contradiction
        exfalso
        have hpar := parity_xbar_single_live d hd E j hjd hjn
          (fun c hcd hcj hc0 => hdead c (by omega) hc0) hlive
        rw [hxb] at hpar
        exact Bool.noConfusion hpar
    · -- column j dead: shift the window
      exact a3_descend d hd m (j + 1) (by omega) E hZ hs2 hconst
        (fun c hc hc0 => by
          rcases Nat.lt_or_ge c j with h | h
          · exact hdead c h hc0
          · have hcj : c = j := by omega
            subst hcj
            exact hdeadj)
        hxb

/-- **Leg (a)**: a Z-type operator commuting with every X-check and with `X̄`
    lies in the stabilizer subgroup — by A1 + A2 + A3. -/
private theorem hgp_zside (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (hZ : ∀ q, E q = Pauli.Z ∨ E q = Pauli.I)
    (hcomm : ∀ kx : Fin ((d - 1) * d), ErrorVec.parity (xRow d kx) E = false)
    (hxbar : ErrorVec.parity (mkHGPRepLogicalX d hd) E = false) :
    InStab (hgpUParams d hd) E := by
  have hZ1 : ∀ q, ErrorVec.mul (listProd (a1List d E)) E q = Pauli.Z
      ∨ ErrorVec.mul (listProd (a1List d E)) E q = Pauli.I :=
    ztype_mul (fun q => by
      rw [listProd_ztype_at (a1List d E) (a1List_ztype d hd E) q]
      cases xfold ((a1List d E).map fun v => liveP (v q))
      · exact Or.inr rfl
      · exact Or.inl rfl) hZ
  have hs21 := a1_clean d hd E hZ
  have hcomm1 : ∀ kx : Fin ((d - 1) * d),
      ErrorVec.parity (xRow d kx) (ErrorVec.mul (listProd (a1List d E)) E)
        = false := by
    intro kx
    rw [parity_mul_right, parity_xrow_a1List d hd E kx, hcomm kx]
    rfl
  have hxbar1 : ErrorVec.parity (mkHGPRepLogicalX d hd)
      (ErrorVec.mul (listProd (a1List d E)) E) = false := by
    rw [parity_mul_right, parity_xbar_a1List d hd E, hxbar]
    rfl
  have hconst1 := a2_col_const d hd _ hZ1 hs21 hcomm1
  have hrec := a3_descend d hd d 0 (by omega) _ hZ1 hs21 hconst1
    (fun c hc _ => absurd hc (Nat.not_lt_zero c)) hxbar1
  have hEeq : E = ErrorVec.mul (listProd (a1List d E))
      (ErrorVec.mul (listProd (a1List d E)) E) := (mul_mul_cancel _ E).symm
  rw [hEeq]
  exact InStab.mul (instab_listProd _ (a1List_instab d hd E)) hrec

/-! ## Leg (b) by `Φ`-transport — reuse, don't re-clean -/

private theorem hgpPhi_identity (d : Nat) (hd : 2 ≤ d) :
    hgpPhi d hd (ErrorVec.identity (hgpN d)) = ErrorVec.identity (hgpN d) := by
  funext q
  rfl

private theorem hgpPhi_mul (d : Nat) (hd : 2 ≤ d) (E₁ E₂ : ErrorVec (hgpN d)) :
    hgpPhi d hd (ErrorVec.mul E₁ E₂)
      = ErrorVec.mul (hgpPhi d hd E₁) (hgpPhi d hd E₂) := by
  funext q
  show hadamardAction (Pauli.mul
      (E₁ ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩)
      (E₂ ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩))
    = Pauli.mul
      (hadamardAction (E₁ ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩))
      (hadamardAction (E₂ ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩))
  cases E₁ ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩ <;>
    cases E₂ ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩ <;> rfl

/-- `InStab` is `Φ`-closed: identity maps to identity, generators to the dual
    check's generator, products to products. -/
private theorem instab_phi (d : Nat) (hd : 2 ≤ d)
    {E : ErrorVec (hgpUParams d hd).n}
    (h : InStab (hgpUParams d hd) E) :
    InStab (hgpUParams d hd) (hgpPhi d hd E) := by
  induction h with
  | identity =>
    show InStab (hgpUParams d hd) (hgpPhi d hd (ErrorVec.identity (hgpN d)))
    rw [hgpPhi_identity d hd]
    exact InStab.identity
  | gen i =>
    show InStab (hgpUParams d hd) (hgpPhi d hd (mkHGPRepStabilizers d i))
    rw [mkHGPRepStabilizers_phi d hd i]
    exact InStab.gen (P := hgpUParams d hd) _
  | @mul E₁ E₂ h1 h2 ih1 ih2 =>
    have hmul : hgpPhi d hd (ErrorVec.mul (n := (hgpUParams d hd).n) E₁ E₂)
        = ErrorVec.mul (n := (hgpUParams d hd).n)
            (hgpPhi d hd E₁) (hgpPhi d hd E₂) :=
      hgpPhi_mul d hd E₁ E₂
    rw [hmul]
    exact InStab.mul ih1 ih2

/-- **Leg (b)**: an X-type operator commuting with every Z-check and with
    `Z̄` lies in the stabilizer subgroup — the `Φ`-transport of leg (a). -/
private theorem hgp_xside (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpN d))
    (hX : ∀ q, E q = Pauli.X ∨ E q = Pauli.I)
    (hcomm : ∀ kz : Fin (hgpNumStab d), (d - 1) * d ≤ kz.val →
      ErrorVec.parity (mkHGPRepStabilizers d kz) E = false)
    (hzbar : ErrorVec.parity (mkHGPRepLogicalZ d) E = false) :
    InStab (hgpUParams d hd) E := by
  have hphi : InStab (hgpUParams d hd) (hgpPhi d hd E) := by
    apply hgp_zside d hd (hgpPhi d hd E)
    · intro q
      show hadamardAction
          (E ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩) = Pauli.Z
        ∨ hadamardAction
          (E ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩) = Pauli.I
      rcases hX ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩ with h | h <;>
        rw [h]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro kx
      have hkx2 : kx.val < 2 * ((d - 1) * d) := by omega
      show ErrorVec.parity (mkHGPRepStabilizers d ⟨kx.val, hkx2⟩)
        (hgpPhi d hd E) = false
      calc ErrorVec.parity (mkHGPRepStabilizers d ⟨kx.val, hkx2⟩) (hgpPhi d hd E)
          = ErrorVec.parity
              (hgpPhi d hd (hgpPhi d hd (mkHGPRepStabilizers d ⟨kx.val, hkx2⟩)))
              (hgpPhi d hd E) :=
            (congrArg (fun S => ErrorVec.parity S (hgpPhi d hd E))
              (hgpPhi_involutive d hd (mkHGPRepStabilizers d ⟨kx.val, hkx2⟩))).symm
        _ = ErrorVec.parity
              (hgpPhi d hd (mkHGPRepStabilizers d ⟨kx.val, hkx2⟩)) E :=
            parity_phi d hd _ E
        _ = false := by
            rw [mkHGPRepStabilizers_phi d hd ⟨kx.val, hkx2⟩]
            exact hcomm _ (hgpDualCheck_z d kx.val hd kx.isLt).1
    · show ErrorVec.parity (hgpPhi d hd (mkHGPRepLogicalZ d)) (hgpPhi d hd E)
        = false
      rw [parity_phi d hd (mkHGPRepLogicalZ d) E]
      exact hzbar
  have h2 := instab_phi d hd hphi
  rw [hgpPhi_involutive d hd E] at h2
  exact h2

/-! ## The CSS split and the maximal-isotropic headline -/

private theorem zbar_ztype (d : Nat) :
    ∀ q, mkHGPRepLogicalZ d q = Pauli.Z ∨ mkHGPRepLogicalZ d q = Pauli.I := by
  intro q
  unfold mkHGPRepLogicalZ
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem xbar_xtype (d : Nat) (hd : 2 ≤ d) :
    ∀ q, mkHGPRepLogicalX d hd q = Pauli.X ∨ mkHGPRepLogicalX d hd q = Pauli.I := by
  intro q
  rw [mkHGPRepLogicalX_spec]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Maximal isotropy of the HGP stabilizer** (`k = 1` exactness): every
    operator commuting with all stabilizer generators of the union machine
    and with both `X̄ = Φ Z̄` and `Z̄` is a product of stabilizer generators
    — by the CSS split, the three-phase Z-side cleaning, and the
    `Φ`-transport of the X-side. -/
theorem hgp_maximal_isotropic (d : Nat) (hd : 2 ≤ d) :
    ∀ E : ErrorVec (hgpUParams d hd).n,
      (∀ s, ErrorVec.parity ((hgpUParams d hd).stabilizers s) E = false) →
      ErrorVec.parity (mkHGPRepLogicalX d hd) E = false →
      ErrorVec.parity (mkHGPRepLogicalZ d) E = false →
      InStab (hgpUParams d hd) E := by
  intro E hstab hx hz
  have hsplit : E = ErrorVec.mul (xPartVec E) (zPartVec E) :=
    (xPart_mul_zPart E).symm
  rw [hsplit]
  refine InStab.mul ?_ ?_
  · -- X-part via leg (b)
    apply hgp_xside d hd (xPartVec E) (xPartVec_xtype E)
    · intro kz hkz
      have hzt : ∀ q : Fin (hgpN d), mkHGPRepStabilizers d kz q = Pauli.Z
          ∨ mkHGPRepStabilizers d kz q = Pauli.I := by
        intro q
        show QStab.Examples.HGPParametric.stabEntry d kz.val q.val = Pauli.Z
          ∨ QStab.Examples.HGPParametric.stabEntry d kz.val q.val = Pauli.I
        have hk2 : kz.val < 2 * ((d - 1) * d) := kz.isLt
        by_cases hq : q.val < d * d
        · rw [stabEntry_Z_s1_eq d kz.val q.val hkz hk2 hq]
          split
          · exact Or.inl rfl
          · exact Or.inr rfl
        · have hq2 : q.val < d * d + (d - 1) * (d - 1) := q.isLt
          rw [stabEntry_Z_s2_eq d kz.val q.val hkz hk2 hq hq2]
          split
          · exact Or.inl rfl
          · exact Or.inr rfl
      rw [← parity_ztype_xPart (mkHGPRepStabilizers d kz) E hzt]
      exact hstab kz
    · rw [← parity_ztype_xPart (mkHGPRepLogicalZ d) E (zbar_ztype d)]
      exact hz
  · -- Z-part via leg (a)
    apply hgp_zside d hd (zPartVec E) (zPartVec_ztype E)
    · intro kx
      rw [← parity_xtype_zPart (xRow d kx) E (xRow_xtype d hd kx)]
      exact hstab ⟨kx.val, by show kx.val < 2 * ((d - 1) * d); omega⟩
    · rw [← parity_xtype_zPart (mkHGPRepLogicalX d hd) E (xbar_xtype d hd)]
      exact hx

/-- **The logical-operator system of the compiled HGP machine**, over the
    real objects: `X̄ = mkHGPRepLogicalX`, `Z̄ = mkHGPRepLogicalZ`, with the
    maximal-isotropic axiom discharged constructively. -/
def hgpLogicalOps (d : Nat) (hd : 2 ≤ d) :
    QStab.Paper.LogicalCosets.LogicalOps (hgpUParams d hd) where
  Xbar := mkHGPRepLogicalX d hd
  Zbar := mkHGPRepLogicalZ d
  Xbar_comm := hgp_Xbar_comm d hd
  Zbar_comm := (exactUnionHGPSpec d hd).logicalZ_normalizer
  Xbar_anticomm_Zbar := hgp_Xbar_anticomm_Zbar d hd
  maximal_isotropic := hgp_maximal_isotropic d hd

/-- **Four-coset normalizer decomposition for the HGP union machine**: every
    operator commuting with all stabilizer generators lies in one of
    `S`, `X̄·S`, `Z̄·S`, `(X̄ Z̄)·S`. -/
theorem hgp_normalizer_decomposition (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (hgpUParams d hd).n)
    (hE : ∀ s, ErrorVec.parity ((hgpUParams d hd).stabilizers s) E = false) :
    InStab (hgpUParams d hd) E
    ∨ InStab (hgpUParams d hd) (ErrorVec.mul (mkHGPRepLogicalX d hd) E)
    ∨ InStab (hgpUParams d hd) (ErrorVec.mul (mkHGPRepLogicalZ d) E)
    ∨ InStab (hgpUParams d hd)
        (ErrorVec.mul (mkHGPRepLogicalX d hd)
          (ErrorVec.mul (mkHGPRepLogicalZ d) E)) :=
  QStab.Paper.LogicalCosets.normalizer_decomposition (hgpLogicalOps d hd) E hE

/-! ## `d = 3` fingerprints against the Python oracle

Kernel-checked cross-checks of the phase machinery's Lean form against
`notes/validate_hgp_maxiso.py`: the A1 prefix-parity selector, the A1
sector-2 cleaning, and the `Pair(0)` support table. -/

private def a1TestE : ErrorVec (hgpN 3) := fun q =>
  if q.val = 0 ∨ q.val = 9 ∨ q.val = 12 then Pauli.Z else Pauli.I

-- A1 selector on `E = Z{0, 9, 12}`: columns pick checks {2, 4} and {5}.
/-- info: [2, 4, 5] -/
#guard_msgs in
#eval ((List.finRange ((3 - 1) * 3)).filter
    (fun kp => a1Pref 3 a1TestE (kp.val % (3 - 1)) (kp.val / (3 - 1)))).map (·.val)

-- A1 cleaning leaves sector 2 empty on the test vector.
/-- info: true -/
#guard_msgs in
#eval (List.finRange (hgpN 3)).all fun q =>
  if 9 ≤ q.val then
    match ErrorVec.mul (listProd (a1List 3 a1TestE)) a1TestE q with
    | Pauli.I => true
    | _ => false
  else true

-- `Pair(0)` support: `Z` exactly on sector-1 columns {0, 1}; sector 2
-- telescopes away.
/--
info: [true, true, false, true, true, false, true, true, false, false, false, false, false]
-/
#guard_msgs in
#eval (List.finRange (hgpN 3)).map fun q =>
  match listProd (pairList 3 0 (by show (0:Nat) < 3 - 1; omega)) q with
  | Pauli.Z => true
  | _ => false

-- Regression guards (axiom pins) for the chunk-4 headliners.
/--
info: 'QStab.QClifford.Compile.hgp_maximal_isotropic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_maximal_isotropic

/--
info: 'QStab.QClifford.Compile.hgpLogicalOps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpLogicalOps

/--
info: 'QStab.QClifford.Compile.hgp_normalizer_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_normalizer_decomposition

end QStab.QClifford.Compile
