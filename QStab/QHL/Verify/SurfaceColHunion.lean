import QStab.QHL.Verify.SurfaceHunion

open QHL.CodeLang
open QHL.CodeLang.Surface.Verify
open QHL.CodeLang.StabBinder

set_option maxHeartbeats 1600000

/-! ## Column dual of the strip-tiling identity (X-plaquettes / columns). -/

/-- A fold with a unique `X` at index `j` (others `I`) at `q` is `X`. -/
theorem fold_unique_X (width j : Nat) (body : Nat → PartialStabilizer) (q : Nat)
    (hj : j < width) (hX : body j q = some Pauli.X)
    (hI : ∀ i < width, i ≠ j → body i q = some Pauli.I) :
    partialStabilizerFold width body q = some Pauli.X := by
  induction width with
  | zero => omega
  | succ n ih =>
      by_cases hjn : j = n
      · subst hjn
        have hrec : partialStabilizerFold j body q = some Pauli.I :=
          fold_all_I j body q (fun i hi => hI i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi))
        simp only [partialStabilizerFold, partialStabilizerMul, hrec, hX]; rfl
      · have hjlt : j < n := by omega
        have hrec : partialStabilizerFold n body q = some Pauli.X :=
          ih hjlt (fun i hi hne => hI i (Nat.lt_succ_of_lt hi) hne)
        have hn : body n q = some Pauli.I :=
          hI n (Nat.lt_succ_self n) (fun h => hjn h.symm)
        simp only [partialStabilizerFold, partialStabilizerMul, hrec, hn]; rfl

/-- Nat value of `gridColXStripIndex dist col slot` (CodeStabBinder:786). -/
def colStripIndexVal (dist col slot : Nat) : Nat :=
  let dm1 := dist - 1
  let bulkCount := dm1 * dm1
  let half := dm1 / 2
  let bulkRow := if col % 2 = 0 then 2 * slot + 1 else 2 * slot
  let bulk := bulkRow * dm1 + col
  let topBoundary := bulkCount + col / 2
  let bottomBoundary := bulkCount + (3 * half + (col - 1) / 2)
  if slot < half then bulk else (if col % 2 = 0 then topBoundary else bottomBoundary)

/-- Whether the column strip stabilizer `(col, iv)` carries `X` at qubit `q`. -/
def colStripCovered (d col iv q : Nat) : Bool :=
  let half := (d - 1) / 2
  (q % d = col || q % d = col + 1) &&
  (if iv < half then
      (if col % 2 = 0 then (q / d = 2 * iv + 1 || q / d = 2 * iv + 2)
       else (q / d = 2 * iv || q / d = 2 * iv + 1))
   else
      (if col % 2 = 0 then q / d = 0 else q / d = d - 1))

theorem colStripCellPauli_eq (d col iv half : Nat)
    (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hcol : col < d - 1) (hiv : iv ≤ half) (q : Nat) :
    surfaceCellPauli d (colStripIndexVal d col iv) q
      = if colStripCovered d col iv q then Pauli.X else Pauli.I := by
  have hhalf2 : (d - 1) / 2 = half := by omega
  by_cases hivb : iv < half
  · -- bulk plaquette (iv < half)
    have hd1pos : 0 < d - 1 := by omega
    set bulkRow := (if col % 2 = 0 then 2 * iv + 1 else 2 * iv) with hbrdef
    have hbr : bulkRow < d - 1 := by rw [hbrdef]; split <;> omega
    have hk : colStripIndexVal d col iv = col + (d - 1) * bulkRow := by
      unfold colStripIndexVal
      simp only [hhalf2, ← hbrdef, if_pos hivb]
      rw [Nat.mul_comm bulkRow (d - 1)]; omega
    have hcellR : cellR d (colStripIndexVal d col iv) = bulkRow := by
      unfold cellR
      rw [hk, Nat.add_mul_div_left _ _ hd1pos, Nat.div_eq_of_lt hcol, Nat.zero_add]
    have hcellC : cellC d (colStripIndexVal d col iv) = col := by
      unfold cellC
      rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
    have hklt : colStripIndexVal d col iv < (d - 1) * (d - 1) := by
      rw [hk]
      calc col + (d - 1) * bulkRow < (d - 1) + (d - 1) * bulkRow := by omega
        _ = (d - 1) * (bulkRow + 1) := by rw [Nat.mul_succ]; omega
        _ ≤ (d - 1) * (d - 1) := Nat.mul_le_mul (Nat.le_refl _) (by omega)
    simp only [surfaceCellPauli, if_pos hklt, inBulkBand, bulkKind, cellRow, cellCol,
      hcellR, hcellC]
    rw [decide_eq_true hklt, Bool.and_true,
      if_neg (show ¬ (bulkRow + col) % 2 = 0 by rw [hbrdef]; split <;> omega)]
    unfold colStripCovered
    simp only [hhalf2, if_pos hivb, hbrdef]
    rw [Bool.and_comm]
    congr 1
    by_cases hp : col % 2 = 0 <;> simp [hp]
  · -- boundary stabilizer (iv = half)
    have hivh : iv = half := by omega
    subst hivh
    by_cases hp : col % 2 = 0
    · -- even col → top-X boundary
      have hk : colStripIndexVal d col iv = (d - 1) * (d - 1) + col / 2 := by
        unfold colStripIndexVal; simp only [hhalf2, if_neg hivb, if_pos hp]
      have hb : colStripIndexVal d col iv - (d - 1) * (d - 1) = col / 2 := by rw [hk]; omega
      have hkge : ¬ colStripIndexVal d col iv < (d - 1) * (d - 1) := by rw [hk]; omega
      have hblt : col / 2 < iv := by omega
      have hkdd : colStripIndexVal d col iv < d * d - 1 := by
        rw [hk]
        have key : (d - 1) * (d - 1) + (d - 1) + (d - 1) + 1 = d * d := by
          obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          rw [Nat.mul_succ, Nat.succ_mul]; omega
        omega
      simp only [surfaceCellPauli, if_neg hkge, hb, hhalf2, cellRow, cellCol,
        if_pos hblt]
      rw [decide_eq_true hkdd, Bool.true_and]
      unfold colStripCovered
      simp only [hhalf2, if_neg hivb, if_pos hp]
      rw [show 2 * (col / 2) = col by omega]
      by_cases h1 : q / d = 0 <;> by_cases h2 : q % d = col <;>
        by_cases h3 : q % d = col + 1 <;> simp_all
    · -- odd col → bottom-X boundary
      have hk : colStripIndexVal d col iv = (d - 1) * (d - 1) + (3 * iv + (col - 1) / 2) := by
        unfold colStripIndexVal; simp only [hhalf2, if_neg hivb, if_neg hp]
      have hb : colStripIndexVal d col iv - (d - 1) * (d - 1) = 3 * iv + (col - 1) / 2 := by
        rw [hk]; omega
      have hkge : ¬ colStripIndexVal d col iv < (d - 1) * (d - 1) := by rw [hk]; omega
      simp only [surfaceCellPauli, if_neg hkge, hb, hhalf2, cellRow, cellCol,
        if_neg (show ¬ 3 * iv + (col - 1) / 2 < iv by omega),
        if_neg (show ¬ 3 * iv + (col - 1) / 2 < 2 * iv by omega),
        if_neg (show ¬ 3 * iv + (col - 1) / 2 < 3 * iv by omega)]
      rw [show 3 * iv + (col - 1) / 2 - 3 * iv = (col - 1) / 2 by omega]
      unfold colStripCovered
      simp only [hhalf2, if_neg hivb, if_neg hp]
      rw [show 2 * ((col - 1) / 2) + 1 = col by omega,
        show 2 * ((col - 1) / 2) + 2 = col + 1 by omega]
      by_cases h1 : q / d = d - 1 <;> by_cases h2 : q % d = col <;>
        by_cases h3 : q % d = col + 1 <;> simp_all

/-- The unique strip index `iv ≤ half` whose stabilizer carries `X` at an in-band `q`. -/
def colCoverIv (d col q : Nat) : Nat :=
  if col % 2 = 0 then (if q / d = 0 then (d - 1) / 2 else (q / d - 1) / 2)
  else (if q / d = d - 1 then (d - 1) / 2 else q / d / 2)

theorem colCoverIv_le_half (d col q half : Nat) (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hqd : q / d < d) : colCoverIv d col q ≤ half := by
  unfold colCoverIv
  have hh2 : (d - 1) / 2 = half := by omega
  split <;> split <;> omega

/-- `tCol` is `X` exactly on the two-column band. -/
theorem tCol_eq (d col q : Nat) :
    tCol d col q = if (q % d = col ∨ q % d = col + 1) then Pauli.X else Pauli.I := by
  unfold tCol colCutPauli
  by_cases h1 : q % d = col <;> by_cases h2 : q % d = col + 1 <;>
    simp_all (config := {decide := true})

/-- Out of band, every column strip stabilizer is `I` at `q`. -/
theorem colStripCovered_false_outBand (d col iv q : Nat)
    (hout : ¬ (q % d = col ∨ q % d = col + 1)) :
    colStripCovered d col iv q = false := by
  unfold colStripCovered
  simp only [Bool.and_eq_false_iff]
  left
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨fun h => hout (Or.inl h), fun h => hout (Or.inr h)⟩

/-- In band, the column strip stabilizer carries `X` exactly at the unique cover index. -/
theorem colStripCovered_eq_decide (d col iv half : Nat) (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hcol : col < d - 1) (hiv : iv ≤ half) (q : Nat)
    (hband : q % d = col ∨ q % d = col + 1) (hqd : q / d < d) :
    colStripCovered d col iv q = decide (iv = colCoverIv d col q) := by
  have hh2 : (d - 1) / 2 = half := by omega
  unfold colStripCovered colCoverIv
  have hbandtrue : (q % d = col || q % d = col + 1) = true := by
    rcases hband with h | h <;> simp [h]
  rw [hbandtrue, Bool.true_and, Bool.eq_iff_iff]
  -- abstract `q / d` to a plain opaque variable so omega handles the nested division cleanly
  set r := q / d with hr
  clear_value r
  by_cases hp : col % 2 = 0
  · simp only [if_pos hp, hh2]
    by_cases hqc : r = 0
    · simp only [if_pos hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega
    · simp only [if_neg hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega
  · simp only [if_neg hp, hh2]
    by_cases hqc : r = d - 1
    · simp only [if_pos hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega
    · simp only [if_neg hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega

/-- **The column strip-tiling identity (pure Nat form).** -/
theorem hunion_pure_col (d col q half : Nat) (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hcol : col < d - 1) (hqd : q / d < d) :
    partialStabilizerFold (half + 1)
        (fun iv q => some (surfaceCellPauli d (colStripIndexVal d col iv) q)) q
      = some (tCol d col q) := by
  have hbody : ∀ iv, iv ≤ half →
      some (surfaceCellPauli d (colStripIndexVal d col iv) q)
        = some (if colStripCovered d col iv q then Pauli.X else Pauli.I) := by
    intro iv hiv
    rw [colStripCellPauli_eq d col iv half hhalf hd3 hcol hiv]
  rw [tCol_eq]
  by_cases hband : q % d = col ∨ q % d = col + 1
  · rw [if_pos hband]
    have hcov : colCoverIv d col q ≤ half := colCoverIv_le_half d col q half hhalf hd3 hqd
    apply fold_unique_X (half + 1) (colCoverIv d col q) _ q (Nat.lt_succ_of_le hcov)
    · rw [hbody (colCoverIv d col q) hcov,
        colStripCovered_eq_decide d col (colCoverIv d col q) half hhalf hd3 hcol hcov q hband hqd]
      simp
    · intro i hi hne
      rw [hbody i (by omega),
        colStripCovered_eq_decide d col i half hhalf hd3 hcol (by omega) q hband hqd]
      simp [hne]
  · rw [if_neg hband]
    apply fold_all_I
    intro i hi
    rw [hbody i (by omega), colStripCovered_false_outBand d col i q hband]
    rfl

/-- `gridColXStripIndex` (a kernel Term) evaluates to the Nat `colStripIndexVal`. -/
theorem gridColXStripIndex_eval (dist : Nat) {arity : Nat} (colT slotT : Term arity .nat)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) {cv sv : Nat}
    (hcol : Term.eval cb fuel colT rho = some cv)
    (hslot : Term.eval cb fuel slotT rho = some sv) :
    Term.eval cb fuel (SFormula.gridColXStripIndex dist colT slotT) rho
      = some (colStripIndexVal dist cv sv) := by
  unfold SFormula.gridColXStripIndex colStripIndexVal
  simp only [Term.eval, hcol, hslot]
  split_ifs <;> simp_all
