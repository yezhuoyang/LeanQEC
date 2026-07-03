import QStab.QClifford.Compile.SurfaceZLeg

/-!
# The surface ρ-duality permutation (order 4)

The X↔Z self-duality of the rotated surface code is the **90° lattice rotation**
`ρ : (r,c) ↦ (c, d−1−r)` (composed with the Hadamard swap in the functor).  Unlike
HGP's transpose duality, ρ is **order 4, not an involution** — the only full X↔Z
automorphisms of the rotated code with boundaries are rot90/rot270 (reflections
break the boundary bands).  So the `Equiv.Perm` is built from an **explicit
inverse** `ρ⁻¹ = rot270 : (r,c) ↦ (d−1−c, r)` (not `Function.Involutive.toPerm`);
`ρ⁴ = id` factors through `rho_leftInv`/`rho_rightInv`.

Both maps are the identity above the data block (`q ≥ d*d`), so they extend to any
ambient `Fin nq` with `d*d ≤ nq` (the compiler's helper qubits are fixed).  All
proofs are structural (no `%`-wrap, no `decide`), mirroring the `hgpDualNat`
pattern.
-/

namespace QStab.QClifford.Compile

open QStab QStab.Examples.SurfaceParametric

/-! ## Coordinate arithmetic helpers (mirrors `HGPDuality`) -/

private theorem div_mul_addρ (m a b : Nat) (hm : 0 < m) (hb : b < m) :
    (a * m + b) / m = a := by
  rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mod_mul_addρ (m a b : Nat) (hb : b < m) : (a * m + b) % m = b := by
  rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private theorem mul_add_ltρ (m a b : Nat) (ha : a < m) (hb : b < m) :
    a * m + b < m * m := by
  calc a * m + b < a * m + m := by omega
    _ = (a + 1) * m := (Nat.succ_mul _ _).symm
    _ ≤ m * m := Nat.mul_le_mul_right _ ha

/-! ## The maps -/

/-- The 90° rotation on data qubits `q = d·(q/d) + q%d ↦ d·(q%d) + (d−1−q/d)`,
    identity on helpers. -/
def rhoNat (d q : Nat) : Nat :=
  if q < d * d then d * (q % d) + (d - 1 - q / d) else q

/-- The inverse 270° rotation `q ↦ d·(d−1−q%d) + q/d`, identity on helpers. -/
def rhoInvNat (d q : Nat) : Nat :=
  if q < d * d then d * (d - 1 - q % d) + q / d else q

/-! ## Range bounds -/

theorem rhoNat_lt (d q : Nat) (hd : 0 < d) (hq : q < d * d) : rhoNat d q < d * d := by
  unfold rhoNat
  rw [if_pos hq, Nat.mul_comm d (q % d)]
  exact mul_add_ltρ d (q % d) (d - 1 - q / d) (Nat.mod_lt _ hd)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hd Nat.one_pos))

theorem rhoInvNat_lt (d q : Nat) (hd : 0 < d) (hq : q < d * d) : rhoInvNat d q < d * d := by
  unfold rhoInvNat
  rw [if_pos hq, Nat.mul_comm d (d - 1 - q % d)]
  have hc : q % d < d := Nat.mod_lt _ hd
  have hr : q / d < d := (Nat.div_lt_iff_lt_mul hd).mpr hq
  exact mul_add_ltρ d (d - 1 - q % d) (q / d)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hd Nat.one_pos)) hr

theorem rhoNat_lt_ambient (d nq q : Nat) (hd : 0 < d) (hn : d * d ≤ nq) (hq : q < nq) :
    rhoNat d q < nq := by
  by_cases h : q < d * d
  · exact Nat.lt_of_lt_of_le (rhoNat_lt d q hd h) hn
  · unfold rhoNat; rw [if_neg h]; exact hq

theorem rhoInvNat_lt_ambient (d nq q : Nat) (hd : 0 < d) (hn : d * d ≤ nq) (hq : q < nq) :
    rhoInvNat d q < nq := by
  by_cases h : q < d * d
  · exact Nat.lt_of_lt_of_le (rhoInvNat_lt d q hd h) hn
  · unfold rhoInvNat; rw [if_neg h]; exact hq

/-! ## The inverse laws (ρ⁻¹∘ρ = id and ρ∘ρ⁻¹ = id, structurally) -/

theorem rho_leftInv (d q : Nat) (hd : 0 < d) : rhoInvNat d (rhoNat d q) = q := by
  by_cases h : q < d * d
  · have hc : q % d < d := Nat.mod_lt _ hd
    have hr : q / d < d := (Nat.div_lt_iff_lt_mul hd).mpr h
    have hb : d - 1 - q / d < d :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hd Nat.one_pos)
    have himg : rhoNat d q = d * (q % d) + (d - 1 - q / d) := by unfold rhoNat; rw [if_pos h]
    have hlt : rhoNat d q < d * d := rhoNat_lt d q hd h
    -- q'/d and q'%d of the rotated image
    have hdiv : rhoNat d q / d = q % d := by
      rw [himg, Nat.mul_comm d (q % d), div_mul_addρ d (q % d) (d - 1 - q / d) hd hb]
    have hmod : rhoNat d q % d = d - 1 - q / d := by
      rw [himg, Nat.mul_comm d (q % d), mod_mul_addρ d (q % d) (d - 1 - q / d) hb]
    unfold rhoInvNat
    rw [if_pos hlt, hdiv, hmod, show d - 1 - (d - 1 - q / d) = q / d by omega]
    exact Nat.div_add_mod q d
  · have h1 : rhoNat d q = q := by unfold rhoNat; rw [if_neg h]
    rw [h1]; unfold rhoInvNat; rw [if_neg h]

theorem rho_rightInv (d q : Nat) (hd : 0 < d) : rhoNat d (rhoInvNat d q) = q := by
  by_cases h : q < d * d
  · have hc : q % d < d := Nat.mod_lt _ hd
    have hr : q / d < d := (Nat.div_lt_iff_lt_mul hd).mpr h
    have hb : d - 1 - q % d < d :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hd Nat.one_pos)
    have himg : rhoInvNat d q = d * (d - 1 - q % d) + q / d := by unfold rhoInvNat; rw [if_pos h]
    have hlt : rhoInvNat d q < d * d := rhoInvNat_lt d q hd h
    have hdiv : rhoInvNat d q / d = d - 1 - q % d := by
      rw [himg, Nat.mul_comm d (d - 1 - q % d), div_mul_addρ d (d - 1 - q % d) (q / d) hd hr]
    have hmod : rhoInvNat d q % d = q / d := by
      rw [himg, Nat.mul_comm d (d - 1 - q % d), mod_mul_addρ d (d - 1 - q % d) (q / d) hr]
    unfold rhoNat
    rw [if_pos hlt, hdiv, hmod, show d - 1 - (d - 1 - q % d) = q % d by omega]
    exact Nat.div_add_mod q d
  · have h1 : rhoInvNat d q = q := by unfold rhoInvNat; rw [if_neg h]
    rw [h1]; unfold rhoNat; rw [if_neg h]

/-! ## The ambient ρ-permutation (identity on helpers) -/

/-- The order-4 ρ-permutation on the compiled ambient layout: 90° rotation on the
    `d*d` data block, identity on the compiler's helper qubits.  Built from the
    explicit inverse `rhoInvNat` (ρ is **not** an involution). -/
def rhoPermAmbient (d nq : Nat) (hd : 0 < d) (hn : d * d ≤ nq) : Equiv.Perm (Fin nq) where
  toFun := fun q => ⟨rhoNat d q.val, rhoNat_lt_ambient d nq q.val hd hn q.isLt⟩
  invFun := fun q => ⟨rhoInvNat d q.val, rhoInvNat_lt_ambient d nq q.val hd hn q.isLt⟩
  left_inv := fun q => Fin.ext (rho_leftInv d q.val hd)
  right_inv := fun q => Fin.ext (rho_rightInv d q.val hd)

/-! ## Image div/mod of the inverse rotation -/

theorem rhoInvNat_div (d q : Nat) (hd : 0 < d) (hq : q < d * d) :
    rhoInvNat d q / d = d - 1 - q % d := by
  have hr : q / d < d := (Nat.div_lt_iff_lt_mul hd).mpr hq
  have himg : rhoInvNat d q = d * (d - 1 - q % d) + q / d := by
    unfold rhoInvNat; rw [if_pos hq]
  rw [himg, Nat.mul_comm d (d - 1 - q % d), div_mul_addρ d (d - 1 - q % d) (q / d) hd hr]

theorem rhoInvNat_mod (d q : Nat) (hd : 0 < d) (hq : q < d * d) :
    rhoInvNat d q % d = q / d := by
  have hr : q / d < d := (Nat.div_lt_iff_lt_mul hd).mpr hq
  have himg : rhoInvNat d q = d * (d - 1 - q % d) + q / d := by
    unfold rhoInvNat; rw [if_pos hq]
  rw [himg, Nat.mul_comm d (d - 1 - q % d), mod_mul_addρ d (d - 1 - q % d) (q / d) hr]

/-! ## The check permutation σρ

`ρ` maps each check's support block onto another check's block, swapping X↔Z:
bulk `(r,c) ↦ (c, d−2−r)` (parity flips since `d` is odd); `topX b ↦ rightZ b`;
`rightZ b ↦ bottomX (half−1−b)`; `leftZ b ↦ topX (half−1−b)`; `bottomX b ↦ leftZ b`
(`half = (d−1)/2`). -/

def rhoCheck (d k : Nat) : Nat :=
  if k < (d - 1) * (d - 1) then
    bulkIdx d (k % (d - 1)) (d - 2 - k / (d - 1))
  else if k < (d - 1) * (d - 1) + (d - 1) / 2 then
    rightZIdx d (k - (d - 1) * (d - 1))
  else if k < (d - 1) * (d - 1) + 2 * ((d - 1) / 2) then
    bottomXIdx d ((d - 1) / 2 - 1 - (k - ((d - 1) * (d - 1) + (d - 1) / 2)))
  else if k < (d - 1) * (d - 1) + 3 * ((d - 1) / 2) then
    topXIdx d ((d - 1) / 2 - 1 - (k - ((d - 1) * (d - 1) + 2 * ((d - 1) / 2))))
  else
    leftZIdx d (k - ((d - 1) * (d - 1) + 3 * ((d - 1) / 2)))

theorem rhoCheck_lt_numStab (d k : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hk : k < numStabFormula d) : rhoCheck d k < numStabFormula d := by
  have hk' : k < (d - 1) * (d - 1) + 2 * (d - 1) := by
    unfold numStabFormula at hk; omega
  have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
  unfold rhoCheck
  by_cases h1 : k < (d - 1) * (d - 1)
  · rw [if_pos h1]
    exact bulkIdx_lt_numStab d _ _ hd (Nat.mod_lt _ (by omega))
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega))
  · rw [if_neg h1]
    by_cases h2 : k < (d - 1) * (d - 1) + (d - 1) / 2
    · rw [if_pos h2]; exact rightZIdx_lt_numStab d _ hd (by omega)
    · rw [if_neg h2]
      by_cases h3 : k < (d - 1) * (d - 1) + 2 * ((d - 1) / 2)
      · rw [if_pos h3]; exact bottomXIdx_lt_numStab d _ hd hodd (by omega)
      · rw [if_neg h3]
        by_cases h4 : k < (d - 1) * (d - 1) + 3 * ((d - 1) / 2)
        · rw [if_pos h4]; exact topXIdx_lt_numStab d _ hd (by omega)
        · rw [if_neg h4]; exact leftZIdx_lt_numStab d _ hd (by omega)

/-! ## The data-level transport Φρ -/

/-- The `ρ`-transport on data errors: Hadamard ∘ pullback along `ρ⁻¹` (an image
    residual reads the original at the 270°-rotated coordinate).  Mirror of
    `hgpPhi`, with the explicit inverse in place of the involution. -/
def rhoPhi (d : Nat) (hd : 0 < d) (E : ErrorVec (d * d)) : ErrorVec (d * d) :=
  fun q => hadamardAction (E ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩)

/-! ## Per-kind decode transport (the six geometric cases) -/

private theorem decode_rho_bulkZ (d r c row col : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hr : r < d - 1) (hc : c < d - 1) (hpar : (r + c) % 2 = 0)
    (hrow : row < d) (hcol : col < d) :
    decodeStabPauliAt d (bulkIdx d c (d - 2 - r)) row col
      = hadamardAction (decodeStabPauliAt d (bulkIdx d r c) (d - 1 - col) row) := by
  rw [decode_bulkXIdx d c (d - 2 - r) row col hd hc (by omega) (by omega),
      decode_bulkZIdx d r c (d - 1 - col) row hd hr hc hpar]
  by_cases h : (d - 1 - col = r ∨ d - 1 - col = r + 1) ∧ (row = c ∨ row = c + 1)
  · rw [if_pos h, if_pos (show (row = c ∨ row = c + 1)
      ∧ (col = d - 2 - r ∨ col = d - 2 - r + 1) by omega)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (by omega))]
    rfl

private theorem decode_rho_bulkX (d r c row col : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hr : r < d - 1) (hc : c < d - 1) (hpar : (r + c) % 2 = 1)
    (hrow : row < d) (hcol : col < d) :
    decodeStabPauliAt d (bulkIdx d c (d - 2 - r)) row col
      = hadamardAction (decodeStabPauliAt d (bulkIdx d r c) (d - 1 - col) row) := by
  rw [decode_bulkZIdx d c (d - 2 - r) row col hd hc (by omega) (by omega),
      decode_bulkXIdx d r c (d - 1 - col) row hd hr hc hpar]
  by_cases h : (d - 1 - col = r ∨ d - 1 - col = r + 1) ∧ (row = c ∨ row = c + 1)
  · rw [if_pos h, if_pos (show (row = c ∨ row = c + 1)
      ∧ (col = d - 2 - r ∨ col = d - 2 - r + 1) by omega)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (by omega))]
    rfl

private theorem decode_rho_topX (d b row col : Nat) (hd : 1 < d)
    (hb : b < (d - 1) / 2) (hrow : row < d) (hcol : col < d) :
    decodeStabPauliAt d (rightZIdx d b) row col
      = hadamardAction (decodeStabPauliAt d (topXIdx d b) (d - 1 - col) row) := by
  rw [decode_rightZIdx d b row col hd hb, decode_topXIdx d b (d - 1 - col) row hd hb]
  by_cases h : d - 1 - col = 0 ∧ (row = 2 * b ∨ row = 2 * b + 1)
  · rw [if_pos h, if_pos (show col = d - 1 ∧ (row = 2 * b ∨ row = 2 * b + 1) by omega)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (by omega))]
    rfl

private theorem decode_rho_rightZ (d b row col : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hb : b < (d - 1) / 2) (hrow : row < d) (hcol : col < d) :
    decodeStabPauliAt d (bottomXIdx d ((d - 1) / 2 - 1 - b)) row col
      = hadamardAction (decodeStabPauliAt d (rightZIdx d b) (d - 1 - col) row) := by
  have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
  rw [decode_bottomXIdx d ((d - 1) / 2 - 1 - b) row col hd (by omega),
      decode_rightZIdx d b (d - 1 - col) row hd hb]
  by_cases h : row = d - 1 ∧ (d - 1 - col = 2 * b ∨ d - 1 - col = 2 * b + 1)
  · rw [if_pos h, if_pos (show row = d - 1 ∧ (col = 2 * ((d - 1) / 2 - 1 - b) + 1
      ∨ col = 2 * ((d - 1) / 2 - 1 - b) + 2) by omega)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (by omega))]
    rfl

private theorem decode_rho_leftZ (d b row col : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hb : b < (d - 1) / 2) (hrow : row < d) (hcol : col < d) :
    decodeStabPauliAt d (topXIdx d ((d - 1) / 2 - 1 - b)) row col
      = hadamardAction (decodeStabPauliAt d (leftZIdx d b) (d - 1 - col) row) := by
  have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
  rw [decode_topXIdx d ((d - 1) / 2 - 1 - b) row col hd (by omega),
      decode_leftZIdx d b (d - 1 - col) row hd hb]
  by_cases h : row = 0 ∧ (d - 1 - col = 2 * b + 1 ∨ d - 1 - col = 2 * b + 2)
  · rw [if_pos h, if_pos (show row = 0 ∧ (col = 2 * ((d - 1) / 2 - 1 - b)
      ∨ col = 2 * ((d - 1) / 2 - 1 - b) + 1) by omega)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (by omega))]
    rfl

private theorem decode_rho_bottomX (d b row col : Nat) (hd : 1 < d)
    (hb : b < (d - 1) / 2) (hrow : row < d) (hcol : col < d) :
    decodeStabPauliAt d (leftZIdx d b) row col
      = hadamardAction (decodeStabPauliAt d (bottomXIdx d b) (d - 1 - col) row) := by
  rw [decode_leftZIdx d b row col hd hb, decode_bottomXIdx d b (d - 1 - col) row hd hb]
  by_cases h : d - 1 - col = d - 1 ∧ (row = 2 * b + 1 ∨ row = 2 * b + 2)
  · rw [if_pos h, if_pos (show col = 0 ∧ (row = 2 * b + 1 ∨ row = 2 * b + 2) by omega)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (by omega))]
    rfl

/-! ## The stab-row transport -/

/-- **The stab-row transport** `swap ∘ stabRow ∘ ρ = stabRow ∘ σρ`: the
    `Φρ`-image of a stabilizer generator row is the `σρ`-image check's row —
    decide-free, for every odd `d > 1`, anchored to the real
    `mkSurfaceStabilizers`. -/
theorem mkSurfaceStabilizers_rho (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (hodd : d % 2 = 1)
    (k : Fin (numStabFormula d)) :
    rhoPhi d hd0 (mkSurfaceStabilizers d hd0 k)
      = mkSurfaceStabilizers d hd0
          ⟨rhoCheck d k.val, rhoCheck_lt_numStab d k.val hd hodd k.isLt⟩ := by
  funext q
  show hadamardAction (decodeStabPauliAt d k.val
      (rhoInvNat d q.val / d) (rhoInvNat d q.val % d))
    = decodeStabPauliAt d (rhoCheck d k.val) (q.val / d) (q.val % d)
  rw [rhoInvNat_div d q.val hd0 q.isLt, rhoInvNat_mod d q.val hd0 q.isLt]
  have hrow : q.val / d < d := Nat.div_lt_of_lt_mul q.isLt
  have hcol : q.val % d < d := Nat.mod_lt _ hd0
  obtain ⟨row, hrowdef⟩ : ∃ x, q.val / d = x := ⟨_, rfl⟩
  obtain ⟨col, hcoldef⟩ : ∃ x, q.val % d = x := ⟨_, rfl⟩
  rw [hrowdef, hcoldef]; rw [hrowdef] at hrow; rw [hcoldef] at hcol
  have hk' : k.val < (d - 1) * (d - 1) + 2 * (d - 1) := by
    have := k.isLt; unfold numStabFormula at this; omega
  have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
  by_cases h1 : k.val < (d - 1) * (d - 1)
  · -- bulk block: (r, c) ↦ (c, d − 2 − r)
    obtain ⟨r, hrdef⟩ : ∃ x, k.val / (d - 1) = x := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ x, k.val % (d - 1) = x := ⟨_, rfl⟩
    have hrlt : r < d - 1 := by rw [← hrdef]; exact Nat.div_lt_of_lt_mul h1
    have hclt : c < d - 1 := by rw [← hcdef]; exact Nat.mod_lt _ (by omega)
    have hrho : rhoCheck d k.val = bulkIdx d c (d - 2 - r) := by
      unfold rhoCheck; rw [if_pos h1, hrdef, hcdef]
    have hkval : k.val = bulkIdx d r c := by
      show k.val = r * (d - 1) + c
      rw [← hrdef, ← hcdef, Nat.mul_comm]
      exact (Nat.div_add_mod k.val (d - 1)).symm
    rw [hrho, hkval]
    by_cases hpar : (r + c) % 2 = 0
    · exact (decode_rho_bulkZ d r c row col hd hodd hrlt hclt hpar hrow hcol).symm
    · exact (decode_rho_bulkX d r c row col hd hodd hrlt hclt (by omega) hrow hcol).symm
  · by_cases h2 : k.val < (d - 1) * (d - 1) + (d - 1) / 2
    · -- topX b ↦ rightZ b
      obtain ⟨b, hbdef⟩ : ∃ x, k.val - (d - 1) * (d - 1) = x := ⟨_, rfl⟩
      have hblt : b < (d - 1) / 2 := by omega
      have hrho : rhoCheck d k.val = rightZIdx d b := by
        unfold rhoCheck; rw [if_neg h1, if_pos h2, hbdef]
      have hkval : k.val = topXIdx d b := by
        show k.val = (d - 1) * (d - 1) + b; omega
      rw [hrho, hkval]
      exact (decode_rho_topX d b row col hd hblt hrow hcol).symm
    · by_cases h3 : k.val < (d - 1) * (d - 1) + 2 * ((d - 1) / 2)
      · -- rightZ b ↦ bottomX (half − 1 − b)
        obtain ⟨b, hbdef⟩ : ∃ x, k.val - ((d - 1) * (d - 1) + (d - 1) / 2) = x := ⟨_, rfl⟩
        have hblt : b < (d - 1) / 2 := by omega
        have hrho : rhoCheck d k.val = bottomXIdx d ((d - 1) / 2 - 1 - b) := by
          unfold rhoCheck; rw [if_neg h1, if_neg h2, if_pos h3, hbdef]
        have hkval : k.val = rightZIdx d b := by
          show k.val = (d - 1) * (d - 1) + (d - 1) / 2 + b; omega
        rw [hrho, hkval]
        exact (decode_rho_rightZ d b row col hd hodd hblt hrow hcol).symm
      · by_cases h4 : k.val < (d - 1) * (d - 1) + 3 * ((d - 1) / 2)
        · -- leftZ b ↦ topX (half − 1 − b)
          obtain ⟨b, hbdef⟩ : ∃ x, k.val - ((d - 1) * (d - 1) + 2 * ((d - 1) / 2)) = x :=
            ⟨_, rfl⟩
          have hblt : b < (d - 1) / 2 := by omega
          have hrho : rhoCheck d k.val = topXIdx d ((d - 1) / 2 - 1 - b) := by
            unfold rhoCheck; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, hbdef]
          have hkval : k.val = leftZIdx d b := by
            show k.val = (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b; omega
          rw [hrho, hkval]
          exact (decode_rho_leftZ d b row col hd hodd hblt hrow hcol).symm
        · -- bottomX b ↦ leftZ b
          obtain ⟨b, hbdef⟩ : ∃ x, k.val - ((d - 1) * (d - 1) + 3 * ((d - 1) / 2)) = x :=
            ⟨_, rfl⟩
          have hblt : b < (d - 1) / 2 := by omega
          have hrho : rhoCheck d k.val = leftZIdx d b := by
            unfold rhoCheck; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, hbdef]
          have hkval : k.val = bottomXIdx d b := by
            show k.val = (d - 1) * (d - 1) + 3 * ((d - 1) / 2) + b; omega
          rw [hrho, hkval]
          exact (decode_rho_bottomX d b row col hd hblt hrow hcol).symm

end QStab.QClifford.Compile
