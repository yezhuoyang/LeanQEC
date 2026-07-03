import QStab.QClifford.Compile.HConjRelabel

/-!
# HGP self-duality: the workhorse (duality transport, chunk 2)

The parametric content behind the chunk-1 pins:

* `hgpDualNat` bounds and involutivity, proved structurally (no `decide`, no
  `%`-totalization) — giving the data-level and ambient permutations via
  `Function.Involutive.toPerm`.
* `hgpDualCheck` — the check map `σ` (X-check `(i,j) ↦` Z-check `(j,i)` and
  back), with bounds and involutivity.
* **The workhorse** `stabEntry_dual`:
  `stabEntry d (σ k) (π q) = hadamardAction (stabEntry d k q)`, for every
  `d ≥ 2` — all four sector legs are exact condition-transposes.
* **The Rule-3 corollary** `hgp_code_selfDual`: through the certified
  evaluation anchor, the self-duality is a statement about the actual
  object-language program `HGP.code` — the theorem the paper cites.
* The Φ layer: `hgpPhi` (H-conjugated pullback along `π`), Φ-closure of the
  domination back-action sets, parity Φ-equivariance, and the logical-X
  representative `mkHGPRepLogicalX := Φ Z̄` with its closed form and the
  parity-swap identity `parity(X̄, R) = parity(Z̄, Φ R)`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.Examples.HGPParametric

/-! ## Coordinate arithmetic for the dual map -/

private theorem div_mul_add' (m a b : Nat) (hm : 0 < m) (hb : b < m) :
    (a * m + b) / m = a := by
  rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mod_mul_add' (m a b : Nat) (hb : b < m) : (a * m + b) % m = b := by
  rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private theorem mul_add_lt (m a b : Nat) (ha : a < m) (hb : b < m) :
    a * m + b < m * m := by
  calc a * m + b < a * m + m := by omega
    _ = (a + 1) * m := (Nat.succ_mul _ _).symm
    _ ≤ m * m := Nat.mul_le_mul_right _ ha

/-- Sector-1 image bound. -/
private theorem dual_s1_lt (d q : Nat) (hd : 0 < d) (hq : q < d * d) :
    (q % d) * d + q / d < d * d :=
  mul_add_lt d (q % d) (q / d) (Nat.mod_lt _ hd)
    ((Nat.div_lt_iff_lt_mul hd).mpr hq)

/-- The dual map preserves the qubit range. -/
theorem hgpDualNat_lt (d q : Nat) (hd : 2 ≤ d)
    (hq : q < d * d + (d - 1) * (d - 1)) :
    hgpDualNat d q < d * d + (d - 1) * (d - 1) := by
  unfold hgpDualNat
  by_cases h1 : q < d * d
  · rw [if_pos h1]
    exact Nat.lt_of_lt_of_le (dual_s1_lt d q (by omega) h1) (Nat.le_add_right _ _)
  · rw [if_neg h1, if_pos hq]
    have hp : q - d * d < (d - 1) * (d - 1) := by omega
    have himgp := mul_add_lt (d - 1) ((q - d * d) % (d - 1)) ((q - d * d) / (d - 1))
      (Nat.mod_lt _ (by omega)) ((Nat.div_lt_iff_lt_mul (by omega)).mpr hp)
    have h' := Nat.add_lt_add_left himgp (d * d)
    rwa [← Nat.add_assoc] at h'

/-- Ambient bound: on `Fin nq` with `d² + (d-1)² ≤ nq` the dual map stays in
    range (identity above the data block). -/
theorem hgpDualNat_lt_ambient (d nq q : Nat) (hd : 2 ≤ d)
    (hn : d * d + (d - 1) * (d - 1) ≤ nq) (hq : q < nq) :
    hgpDualNat d q < nq := by
  by_cases h : q < d * d + (d - 1) * (d - 1)
  · exact Nat.lt_of_lt_of_le (hgpDualNat_lt d q hd h) hn
  · unfold hgpDualNat
    rw [if_neg (by omega), if_neg h]
    exact hq

/-- **Involutivity of the dual map**, structurally. -/
theorem hgpDualNat_involutive (d : Nat) (hd : 2 ≤ d) :
    Function.Involutive (hgpDualNat d) := by
  intro q
  by_cases h1 : q < d * d
  · have hd0 : 0 < d := by omega
    have hqd : q / d < d := (Nat.div_lt_iff_lt_mul hd0).mpr h1
    have hs1 : hgpDualNat d q = (q % d) * d + q / d := by
      unfold hgpDualNat; rw [if_pos h1]
    have himg : (q % d) * d + q / d < d * d :=
      dual_s1_lt d q hd0 h1
    rw [hs1]
    unfold hgpDualNat
    rw [if_pos himg, div_mul_add' d _ _ hd0 hqd, mod_mul_add' d _ _ hqd]
    rw [Nat.mul_comm (q / d) d]
    exact Nat.div_add_mod q d
  · by_cases h2 : q < d * d + (d - 1) * (d - 1)
    · have hd1 : 0 < d - 1 := by omega
      have hp : q - d * d < (d - 1) * (d - 1) := by omega
      have hpd : (q - d * d) / (d - 1) < d - 1 :=
        (Nat.div_lt_iff_lt_mul hd1).mpr hp
      have himgp : ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1)
          < (d - 1) * (d - 1) :=
        mul_add_lt (d - 1) _ _ (Nat.mod_lt _ hd1) hpd
      have hs2 : hgpDualNat d q
          = d * d + ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1) := by
        unfold hgpDualNat
        rw [if_neg h1, if_pos h2]
      have hgeI : ¬d * d + ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1)
          < d * d :=
        Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      have hltI : d * d + ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1)
          < d * d + (d - 1) * (d - 1) := by
        have h' := Nat.add_lt_add_left himgp (d * d)
        rwa [← Nat.add_assoc] at h'
      have hsub : d * d + ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1)
          - d * d = ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1) := by
        rw [Nat.add_assoc]
        exact Nat.add_sub_cancel_left _ _
      rw [hs2]
      unfold hgpDualNat
      rw [if_neg hgeI, if_pos hltI, hsub,
        div_mul_add' (d - 1) _ _ hd1 hpd, mod_mul_add' (d - 1) _ _ hpd,
        Nat.add_assoc, Nat.mul_comm ((q - d * d) / (d - 1)) (d - 1),
        Nat.div_add_mod]
      exact Nat.add_sub_cancel' (Nat.le_of_not_lt h1)
    · unfold hgpDualNat
      rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

/-- The data-level dual permutation (no `decide`, no `%`-wrap). -/
def hgpDualPermData (d : Nat) (hd : 2 ≤ d) :
    Equiv.Perm (Fin (d * d + (d - 1) * (d - 1))) :=
  Function.Involutive.toPerm
    (fun q => ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩)
    (fun q => Fin.ext (hgpDualNat_involutive d hd q.val))

/-- The ambient dual permutation (identity on helpers). -/
def hgpDualPermAmbient (d nq : Nat) (hd : 2 ≤ d)
    (hn : d * d + (d - 1) * (d - 1) ≤ nq) : Equiv.Perm (Fin nq) :=
  Function.Involutive.toPerm
    (fun q => ⟨hgpDualNat d q.val, hgpDualNat_lt_ambient d nq q.val hd hn q.isLt⟩)
    (fun q => Fin.ext (hgpDualNat_involutive d hd q.val))

/-! ## The check map `σ` -/

/-- X-check `(i, j) ↦` Z-check `(j, i)`; Z-check `(a, jz) ↦` X-check
    `(jz, a)`. -/
def hgpDualCheck (d k : Nat) : Nat :=
  if k < (d - 1) * d then
    (d - 1) * d + ((k % d) * (d - 1) + k / d)
  else
    ((k - (d - 1) * d) % (d - 1)) * d + (k - (d - 1) * d) / (d - 1)

/-- `σ` maps the X-block into the Z-block. -/
theorem hgpDualCheck_z (d k : Nat) (hd : 2 ≤ d) (hk : k < (d - 1) * d) :
    (d - 1) * d ≤ hgpDualCheck d k ∧ hgpDualCheck d k < 2 * ((d - 1) * d) := by
  unfold hgpDualCheck
  rw [if_pos hk]
  have hi : k / d < d - 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hk
  have hj : k % d < d := Nat.mod_lt _ (by omega)
  have h1 : (k % d) * (d - 1) + k / d < (d - 1) * d := by
    have h1' : (k % d) * (d - 1) + k / d < d * (d - 1) := by
      calc (k % d) * (d - 1) + k / d < (k % d) * (d - 1) + (d - 1) := by omega
        _ = (k % d + 1) * (d - 1) := (Nat.succ_mul _ _).symm
        _ ≤ d * (d - 1) := Nat.mul_le_mul_right _ hj
    rwa [Nat.mul_comm d (d - 1)] at h1'
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.two_mul]
  exact Nat.add_lt_add_left h1 _

/-- `σ` maps the Z-block into the X-block. -/
theorem hgpDualCheck_x (d k : Nat) (hd : 2 ≤ d)
    (hzk : (d - 1) * d ≤ k) (hk : k < 2 * ((d - 1) * d)) :
    hgpDualCheck d k < (d - 1) * d := by
  unfold hgpDualCheck
  rw [if_neg (by omega)]
  have ht : k - (d - 1) * d < (d - 1) * d := by omega
  have ha : (k - (d - 1) * d) / (d - 1) < d :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr
      (by rw [Nat.mul_comm d (d - 1)]; exact ht)
  have hjz : (k - (d - 1) * d) % (d - 1) < d - 1 := Nat.mod_lt _ (by omega)
  calc ((k - (d - 1) * d) % (d - 1)) * d + (k - (d - 1) * d) / (d - 1)
      < ((k - (d - 1) * d) % (d - 1)) * d + d := by omega
    _ = ((k - (d - 1) * d) % (d - 1) + 1) * d := (Nat.succ_mul _ _).symm
    _ ≤ (d - 1) * d := Nat.mul_le_mul_right _ hjz

/-- Coordinates of the X-leg image. -/
private theorem dualCheck_x_coords (d k : Nat) (hd : 2 ≤ d) (hk : k < (d - 1) * d) :
    (hgpDualCheck d k - (d - 1) * d) / (d - 1) = k % d ∧
    (hgpDualCheck d k - (d - 1) * d) % (d - 1) = k / d := by
  have hi : k / d < d - 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hk
  have hsub : hgpDualCheck d k - (d - 1) * d = (k % d) * (d - 1) + k / d := by
    unfold hgpDualCheck
    rw [if_pos hk]
    exact Nat.add_sub_cancel_left _ _
  rw [hsub, div_mul_add' (d - 1) _ _ (by omega) hi, mod_mul_add' (d - 1) _ _ hi]
  exact ⟨rfl, rfl⟩

/-- Coordinates of the Z-leg image. -/
private theorem dualCheck_z_coords (d k : Nat) (hd : 2 ≤ d)
    (hzk : (d - 1) * d ≤ k) (hk : k < 2 * ((d - 1) * d)) :
    hgpDualCheck d k / d = (k - (d - 1) * d) % (d - 1) ∧
    hgpDualCheck d k % d = (k - (d - 1) * d) / (d - 1) := by
  have ht : k - (d - 1) * d < (d - 1) * d := by omega
  have ha : (k - (d - 1) * d) / (d - 1) < d :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr
      (by rw [Nat.mul_comm d (d - 1)]; exact ht)
  have heq : hgpDualCheck d k
      = ((k - (d - 1) * d) % (d - 1)) * d + (k - (d - 1) * d) / (d - 1) := by
    unfold hgpDualCheck
    rw [if_neg (by omega)]
  rw [heq, div_mul_add' d _ _ (by omega) ha, mod_mul_add' d _ _ ha]
  exact ⟨rfl, rfl⟩

/-- Coordinates of the sector-1 qubit image. -/
private theorem dual_s1_coords (d q : Nat) (hd : 2 ≤ d) (hq : q < d * d) :
    hgpDualNat d q / d = q % d ∧ hgpDualNat d q % d = q / d := by
  have hqd : q / d < d := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have heq : hgpDualNat d q = (q % d) * d + q / d := by
    unfold hgpDualNat; rw [if_pos hq]
  rw [heq, div_mul_add' d _ _ (by omega) hqd, mod_mul_add' d _ _ hqd]
  exact ⟨rfl, rfl⟩

/-- Coordinates of the sector-2 qubit image. -/
private theorem dual_s2_coords (d q : Nat) (hd : 2 ≤ d)
    (h1 : ¬q < d * d) (h2 : q < d * d + (d - 1) * (d - 1)) :
    (hgpDualNat d q - d * d) / (d - 1) = (q - d * d) % (d - 1) ∧
    (hgpDualNat d q - d * d) % (d - 1) = (q - d * d) / (d - 1) := by
  have hp : q - d * d < (d - 1) * (d - 1) := by omega
  have hpd : (q - d * d) / (d - 1) < d - 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr hp
  have heq : hgpDualNat d q - d * d
      = ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1) := by
    unfold hgpDualNat
    rw [if_neg h1, if_pos h2, Nat.add_assoc]
    exact Nat.add_sub_cancel_left _ _
  rw [heq, div_mul_add' (d - 1) _ _ (by omega) hpd, mod_mul_add' (d - 1) _ _ hpd]
  exact ⟨rfl, rfl⟩

/-- The dual map preserves the sector split. -/
private theorem dual_sector (d q : Nat) (hd : 2 ≤ d) :
    (q < d * d → hgpDualNat d q < d * d) ∧
    (¬q < d * d → q < d * d + (d - 1) * (d - 1) → ¬hgpDualNat d q < d * d) := by
  constructor
  · intro h1
    have heq : hgpDualNat d q = (q % d) * d + q / d := by
      unfold hgpDualNat; rw [if_pos h1]
    rw [heq]
    exact dual_s1_lt d q (by omega) h1
  · intro h1 h2
    have heq : hgpDualNat d q
        = d * d + ((q - d * d) % (d - 1)) * (d - 1) + (q - d * d) / (d - 1) := by
      unfold hgpDualNat
      rw [if_neg h1, if_pos h2]
    rw [heq]
    exact Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

/-! ## The workhorse -/

private theorem stabEntry_out (d k q : Nat)
    (hq : ¬q < d * d + (d - 1) * (d - 1)) :
    QStab.Examples.HGPParametric.stabEntry d k q = Pauli.I := by
  unfold QStab.Examples.HGPParametric.stabEntry
  rw [if_neg (fun h => hq h.2)]

/-- **The workhorse: HGP(Rep(d), Rep(d)) self-duality**, every `d ≥ 2`,
    decide-free.  All four sector legs are exact condition-transposes of the
    entry formulas. -/
theorem stabEntry_dual (d k q : Nat) (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    QStab.Examples.HGPParametric.stabEntry d (hgpDualCheck d k) (hgpDualNat d q)
      = hadamardAction (QStab.Examples.HGPParametric.stabEntry d k q) := by
  by_cases hq2 : q < d * d + (d - 1) * (d - 1)
  case neg =>
    have hπ : hgpDualNat d q = q := by
      unfold hgpDualNat
      rw [if_neg (by omega), if_neg hq2]
    rw [hπ, stabEntry_out d _ q hq2, stabEntry_out d k q hq2]
    rfl
  rcases Nat.lt_or_ge k ((d - 1) * d) with hx | hz
  · -- X-check ↦ Z-check
    obtain ⟨hσge, hσlt⟩ := hgpDualCheck_z d k hd hx
    obtain ⟨hσdiv, hσmod⟩ := dualCheck_x_coords d k hd hx
    by_cases hs1 : q < d * d
    · have hπlt : hgpDualNat d q < d * d := (dual_sector d q hd).1 hs1
      obtain ⟨hπdiv, hπmod⟩ := dual_s1_coords d q hd hs1
      rw [QStab.Examples.HGPParametric.stabEntry_Z_s1_eq d _ _ hσge hσlt hπlt,
        QStab.Examples.HGPParametric.stabEntry_X_s1_eq d k q hx hs1,
        hπdiv, hπmod, hσdiv, hσmod]
      by_cases hC : q % d = k % d ∧ (q / d = k / d ∨ q / d = k / d + 1)
      · rw [if_pos hC, if_pos hC]; rfl
      · rw [if_neg hC, if_neg hC]; rfl
    · have hπge : ¬hgpDualNat d q < d * d := (dual_sector d q hd).2 hs1 hq2
      have hπlt2 : hgpDualNat d q < d * d + (d - 1) * (d - 1) :=
        hgpDualNat_lt d q hd hq2
      obtain ⟨hπdiv, hπmod⟩ := dual_s2_coords d q hd hs1 hq2
      rw [QStab.Examples.HGPParametric.stabEntry_Z_s2_eq d _ _ hσge hσlt hπge hπlt2,
        QStab.Examples.HGPParametric.stabEntry_X_s2_eq d k q hx hs1 hq2,
        hπdiv, hπmod, hσdiv, hσmod]
      by_cases hC : (q - d * d) / (d - 1) = k / d ∧
          ((q - d * d) % (d - 1) = k % d ∨ (q - d * d) % (d - 1) + 1 = k % d)
      · rw [if_pos ⟨hC.1, hC.2⟩, if_pos hC]; rfl
      · rw [if_neg (fun h => hC ⟨h.1, h.2⟩), if_neg hC]; rfl
  · -- Z-check ↦ X-check
    have hσx : hgpDualCheck d k < (d - 1) * d := hgpDualCheck_x d k hd hz hk
    obtain ⟨hσdiv, hσmod⟩ := dualCheck_z_coords d k hd hz hk
    by_cases hs1 : q < d * d
    · have hπlt : hgpDualNat d q < d * d := (dual_sector d q hd).1 hs1
      obtain ⟨hπdiv, hπmod⟩ := dual_s1_coords d q hd hs1
      rw [QStab.Examples.HGPParametric.stabEntry_X_s1_eq d _ _ hσx hπlt,
        QStab.Examples.HGPParametric.stabEntry_Z_s1_eq d k q hz hk hs1,
        hπdiv, hπmod, hσdiv, hσmod]
      by_cases hC : q / d = (k - (d - 1) * d) / (d - 1) ∧
          (q % d = (k - (d - 1) * d) % (d - 1) ∨
           q % d = (k - (d - 1) * d) % (d - 1) + 1)
      · rw [if_pos hC, if_pos hC]; rfl
      · rw [if_neg hC, if_neg hC]; rfl
    · have hπge : ¬hgpDualNat d q < d * d := (dual_sector d q hd).2 hs1 hq2
      have hπlt2 : hgpDualNat d q < d * d + (d - 1) * (d - 1) :=
        hgpDualNat_lt d q hd hq2
      obtain ⟨hπdiv, hπmod⟩ := dual_s2_coords d q hd hs1 hq2
      rw [QStab.Examples.HGPParametric.stabEntry_X_s2_eq d _ _ hσx hπge hπlt2,
        QStab.Examples.HGPParametric.stabEntry_Z_s2_eq d k q hz hk hs1 hq2,
        hπdiv, hπmod, hσdiv, hσmod]
      by_cases hC : (q - d * d) % (d - 1) = (k - (d - 1) * d) % (d - 1) ∧
          ((q - d * d) / (d - 1) = (k - (d - 1) * d) / (d - 1) ∨
           (q - d * d) / (d - 1) + 1 = (k - (d - 1) * d) / (d - 1))
      · rw [if_pos ⟨hC.1, hC.2⟩, if_pos hC]; rfl
      · rw [if_neg (fun h => hC ⟨h.1, h.2⟩), if_neg hC]; rfl

/-- **The Rule-3 corollary** (the paper-citable form): through the certified
    evaluation anchor, the self-duality is a statement about the actual
    object-language program `HGP.code`. -/
theorem hgp_code_selfDual (d k q : Nat) (hd : 2 ≤ d) (hk : k < 2 * ((d - 1) * d)) :
    QHL.CodeLang.HGP.code.evalAt? d (hgpDualCheck d k) (hgpDualNat d q)
      = (QHL.CodeLang.HGP.code.evalAt? d k q).map hadamardAction := by
  rw [QHL.CodeLang.HGP.code_evalAt?_eq_stabEntry,
    QHL.CodeLang.HGP.code_evalAt?_eq_stabEntry, stabEntry_dual d k q hd hk]
  rfl

/-! ## The Φ layer -/

/-- H-conjugated pullback along the dual permutation (data level). -/
def hgpPhi (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (d * d + (d - 1) * (d - 1))) :
    ErrorVec (d * d + (d - 1) * (d - 1)) :=
  fun q => hadamardAction (E ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩)

theorem hgpPhi_involutive (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (d * d + (d - 1) * (d - 1))) :
    hgpPhi d hd (hgpPhi d hd E) = E := by
  funext q
  unfold hgpPhi
  rw [hadamardAction_involutive]
  congr 1
  exact Fin.ext (hgpDualNat_involutive d hd q.val)

/-- **Φ-closure of the domination back-action sets**: the Φ-image of a
    dominated error is dominated by the dual check. -/
theorem hgpBackAction_phi (d : Nat) (hd : 2 ≤ d)
    (k : Fin (hgpNumStab d)) (e : ErrorVec (hgpN d))
    (he : e ∈ hgpBackAction d k) :
    hgpPhi d hd e ∈ hgpBackAction d
      ⟨hgpDualCheck d k.val, by
        rcases Nat.lt_or_ge k.val ((d - 1) * d) with hx | hz
        · exact (hgpDualCheck_z d k.val hd hx).2
        · exact Nat.lt_of_lt_of_le (hgpDualCheck_x d k.val hd hz k.isLt)
            (by omega)⟩ := by
  intro q
  rcases he ⟨hgpDualNat d q.val, hgpDualNat_lt d q.val hd q.isLt⟩ with hI | hstab
  · left
    exact (congrArg hadamardAction hI).trans rfl
  · right
    refine (congrArg hadamardAction hstab).trans ?_
    show hadamardAction
        (QStab.Examples.HGPParametric.stabEntry d k.val (hgpDualNat d q.val)) = _
    rw [← stabEntry_dual d k.val (hgpDualNat d q.val) hd k.isLt,
      hgpDualNat_involutive d hd q.val]
    rfl

/-! ## Parity Φ-equivariance -/

theorem anticommutes_hadamardAction (a b : Pauli) :
    ErrorVec.Pauli.anticommutes (hadamardAction a) (hadamardAction b)
      = ErrorVec.Pauli.anticommutes a b := by
  cases a <;> cases b <;> rfl

theorem parity_phi (d : Nat) (hd : 2 ≤ d)
    (S E : ErrorVec (d * d + (d - 1) * (d - 1))) :
    ErrorVec.parity (hgpPhi d hd S) (hgpPhi d hd E) = ErrorVec.parity S E := by
  have hpt : ∀ q : Fin (d * d + (d - 1) * (d - 1)),
      ErrorVec.Pauli.anticommutes (hgpPhi d hd S q) (hgpPhi d hd E q)
        = ErrorVec.Pauli.anticommutes (S ((hgpDualPermData d hd) q))
            (E ((hgpDualPermData d hd) q)) := fun q =>
    anticommutes_hadamardAction _ _
  unfold ErrorVec.parity
  have hcard : (Finset.univ.filter fun q =>
        ErrorVec.Pauli.anticommutes (hgpPhi d hd S q) (hgpPhi d hd E q)).card
      = (Finset.univ.filter fun q =>
        ErrorVec.Pauli.anticommutes (S q) (E q)).card := by
    apply Finset.card_equiv (hgpDualPermData d hd)
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpt]
  rw [hcard]

/-! ## The logical-X representative -/

/-- X̄ := Φ Z̄ — X on sector-1 row 0. -/
def mkHGPRepLogicalX (d : Nat) (hd : 2 ≤ d) : ErrorVec (hgpN d) :=
  hgpPhi d hd (mkHGPRepLogicalZ d)

/-- Closed form: `X` exactly on the sector-1 row-0 qubits. -/
theorem mkHGPRepLogicalX_spec (d : Nat) (hd : 2 ≤ d) (q : Fin (hgpN d)) :
    mkHGPRepLogicalX d hd q
      = if q.val < d * d ∧ q.val / d = 0 then Pauli.X else Pauli.I := by
  unfold mkHGPRepLogicalX hgpPhi mkHGPRepLogicalZ
  by_cases hs1 : q.val < d * d
  · obtain ⟨_, hπmod⟩ := dual_s1_coords d q.val hd hs1
    have hπlt : hgpDualNat d q.val < d * d := (dual_sector d q.val hd).1 hs1
    by_cases h0 : q.val / d = 0
    · rw [if_pos ⟨hπlt, by rw [hπmod]; exact h0⟩, if_pos ⟨hs1, h0⟩]
      rfl
    · rw [if_neg (fun h => h0 (by rw [← hπmod]; exact h.2)), if_neg (fun h => h0 h.2)]
      rfl
  · have hπge : ¬hgpDualNat d q.val < d * d :=
      (dual_sector d q.val hd).2 hs1 q.isLt
    rw [if_neg (fun h => hπge h.1), if_neg (fun h => hs1 h.1)]
    rfl

/-- **The parity-swap identity**: the X̄-parity of a residual is the Z̄-parity
    of its Φ-image — the closing move of the X-side floor. -/
theorem parity_logicalX_phi (d : Nat) (hd : 2 ≤ d) (R : ErrorVec (hgpN d)) :
    ErrorVec.parity (mkHGPRepLogicalX d hd) R
      = ErrorVec.parity (mkHGPRepLogicalZ d) (hgpPhi d hd R) := by
  have h := parity_phi d hd (mkHGPRepLogicalZ d) (hgpPhi d hd R)
  rw [hgpPhi_involutive d hd R] at h
  exact h

-- Regression guards (axiom pins) for the chunk-2 headliners.
/-- info: 'QStab.QClifford.Compile.stabEntry_dual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stabEntry_dual

/-- info: 'QStab.QClifford.Compile.hgp_code_selfDual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hgp_code_selfDual

/-- info: 'QStab.QClifford.Compile.hgpBackAction_phi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hgpBackAction_phi

/--
info: 'QStab.QClifford.Compile.parity_phi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parity_phi

/--
info: 'QStab.QClifford.Compile.parity_logicalX_phi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parity_logicalX_phi

end QStab.QClifford.Compile
