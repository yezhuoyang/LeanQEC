import QStab.QHL.Verify.SurfaceRowCharacterizationKeystone
import QStab.QHL.Verify.SurfaceBridgeTotality
import QStab.QHL.CodeStabBinder

open QHL.CodeLang
open QHL.CodeLang.Surface.Verify
open QHL.CodeLang.StabBinder

set_option maxHeartbeats 1600000

/-! ## Generic fold lemmas: a fold of Z/I terms with at most one Z. -/

/-- A fold of all-`I` terms at `q` is `I`. -/
theorem fold_all_I (width : Nat) (body : Nat → PartialStabilizer) (q : Nat)
    (hI : ∀ i < width, body i q = some Pauli.I) :
    partialStabilizerFold width body q = some Pauli.I := by
  induction width with
  | zero => rfl
  | succ n ih =>
      have hn : body n q = some Pauli.I := hI n (Nat.lt_succ_self n)
      have hrec : partialStabilizerFold n body q = some Pauli.I :=
        ih (fun i hi => hI i (Nat.lt_succ_of_lt hi))
      simp only [partialStabilizerFold, partialStabilizerMul, hrec, hn]; rfl

/-- A fold with a unique `Z` at index `j` (others `I`) at `q` is `Z`. -/
theorem fold_unique_Z (width j : Nat) (body : Nat → PartialStabilizer) (q : Nat)
    (hj : j < width) (hZ : body j q = some Pauli.Z)
    (hI : ∀ i < width, i ≠ j → body i q = some Pauli.I) :
    partialStabilizerFold width body q = some Pauli.Z := by
  induction width with
  | zero => omega
  | succ n ih =>
      by_cases hjn : j = n
      · -- the Z is the top term; the prefix [0,n) is all I
        subst hjn
        have hrec : partialStabilizerFold j body q = some Pauli.I :=
          fold_all_I j body q (fun i hi => hI i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi))
        simp only [partialStabilizerFold, partialStabilizerMul, hrec, hZ]; rfl
      · -- the Z is in the prefix; the top term is I
        have hjlt : j < n := by omega
        have hrec : partialStabilizerFold n body q = some Pauli.Z :=
          ih hjlt (fun i hi hne => hI i (Nat.lt_succ_of_lt hi) hne)
        have hn : body n q = some Pauli.I :=
          hI n (Nat.lt_succ_self n) (fun h => hjn h.symm)
        simp only [partialStabilizerFold, partialStabilizerMul, hrec, hn]; rfl


/-! ## Per-cell value of the strip stabilizer. -/

/-- Nat value of `gridRowZStripIndex dist row slot` (CodeStabBinder:773). -/
def stripIndexVal (dist row slot : Nat) : Nat :=
  let dm1 := dist - 1
  let bulkCount := dm1 * dm1
  let half := dm1 / 2
  let bulkCol := if row % 2 = 0 then 2 * slot else 2 * slot + 1
  let bulk := row * dm1 + bulkCol
  let rightBoundary := bulkCount + (half + row / 2)
  let leftBoundary := bulkCount + (2 * half + (row - 1) / 2)
  if slot < half then bulk else (if row % 2 = 0 then rightBoundary else leftBoundary)

/-- Whether the strip stabilizer `(row, iv)` carries `Z` at qubit `q`. -/
def stripCovered (d row iv q : Nat) : Bool :=
  let half := (d - 1) / 2
  (q / d = row || q / d = row + 1) &&
  (if iv < half then
      (if row % 2 = 0 then (q % d = 2 * iv || q % d = 2 * iv + 1)
       else (q % d = 2 * iv + 1 || q % d = 2 * iv + 2))
   else
      (if row % 2 = 0 then q % d = d - 1 else q % d = 0))

theorem stripCellPauli_eq (d row iv half : Nat)
    (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hrow : row < d - 1) (hiv : iv ≤ half) (q : Nat) :
    surfaceCellPauli d (stripIndexVal d row iv) q
      = if stripCovered d row iv q then Pauli.Z else Pauli.I := by
  have hhalf2 : (d - 1) / 2 = half := by omega
  by_cases hivb : iv < half
  · -- bulk plaquette (iv < half)
    have hd1pos : 0 < d - 1 := by omega
    set bulkCol := (if row % 2 = 0 then 2 * iv else 2 * iv + 1) with hbcdef
    have hbc : bulkCol < d - 1 := by rw [hbcdef]; split <;> omega
    have hk : stripIndexVal d row iv = bulkCol + (d - 1) * row := by
      unfold stripIndexVal
      simp only [hhalf2, ← hbcdef, if_pos hivb]
      rw [Nat.mul_comm row (d - 1)]; omega
    have hcellR : cellR d (stripIndexVal d row iv) = row := by
      unfold cellR
      rw [hk, Nat.add_mul_div_left _ _ hd1pos, Nat.div_eq_of_lt hbc, Nat.zero_add]
    have hcellC : cellC d (stripIndexVal d row iv) = bulkCol := by
      unfold cellC
      rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbc]
    have hklt : stripIndexVal d row iv < (d - 1) * (d - 1) := by
      rw [hk]
      calc bulkCol + (d - 1) * row < (d - 1) + (d - 1) * row := by omega
        _ = (d - 1) * (row + 1) := by rw [Nat.mul_succ]; omega
        _ ≤ (d - 1) * (d - 1) := Nat.mul_le_mul (Nat.le_refl _) (by omega)
    simp only [surfaceCellPauli, if_pos hklt, inBulkBand, bulkKind, cellRow, cellCol,
      hcellR, hcellC]
    rw [decide_eq_true hklt, Bool.and_true,
      if_pos (show (row + bulkCol) % 2 = 0 by rw [hbcdef]; split <;> omega)]
    unfold stripCovered
    simp only [hhalf2, if_pos hivb, hbcdef]
    congr 1
    by_cases hp : row % 2 = 0 <;> simp [hp]
  · -- boundary stabilizer (iv = half)
    have hivh : iv = half := by omega
    subst hivh
    by_cases hp : row % 2 = 0
    · -- even row → right-Z boundary
      have hk : stripIndexVal d row iv = (d - 1) * (d - 1) + (iv + row / 2) := by
        unfold stripIndexVal; simp only [hhalf2, if_neg hivb, if_pos hp]
      have hb : stripIndexVal d row iv - (d - 1) * (d - 1) = iv + row / 2 := by rw [hk]; omega
      have hkge : ¬ stripIndexVal d row iv < (d - 1) * (d - 1) := by rw [hk]; omega
      simp only [surfaceCellPauli, if_neg hkge, hb, hhalf2, cellRow, cellCol,
        if_neg (show ¬ iv + row / 2 < iv by omega), if_pos (show iv + row / 2 < 2 * iv by omega)]
      unfold stripCovered
      simp only [hhalf2, if_neg hivb, if_pos hp]
      rw [show 2 * (iv + row / 2 - iv) = row by omega]
      by_cases h1 : q % d = d - 1 <;> by_cases h2 : q / d = row <;>
        by_cases h3 : q / d = row + 1 <;> simp_all
    · -- odd row → left-Z boundary
      have hk : stripIndexVal d row iv = (d - 1) * (d - 1) + (2 * iv + (row - 1) / 2) := by
        unfold stripIndexVal; simp only [hhalf2, if_neg hivb, if_neg hp]
      have hb : stripIndexVal d row iv - (d - 1) * (d - 1) = 2 * iv + (row - 1) / 2 := by
        rw [hk]; omega
      have hkge : ¬ stripIndexVal d row iv < (d - 1) * (d - 1) := by rw [hk]; omega
      simp only [surfaceCellPauli, if_neg hkge, hb, hhalf2, cellRow, cellCol,
        if_neg (show ¬ 2 * iv + (row - 1) / 2 < iv by omega),
        if_neg (show ¬ 2 * iv + (row - 1) / 2 < 2 * iv by omega),
        if_pos (show 2 * iv + (row - 1) / 2 < 3 * iv by omega)]
      unfold stripCovered
      simp only [hhalf2, if_neg hivb, if_neg hp]
      rw [show 2 * (2 * iv + (row - 1) / 2 - 2 * iv) + 1 = row by omega,
        show 2 * (2 * iv + (row - 1) / 2 - 2 * iv) + 2 = row + 1 by omega]
      by_cases h1 : q % d = 0 <;> by_cases h2 : q / d = row <;>
        by_cases h3 : q / d = row + 1 <;> simp_all


/-! ## Coverage: the unique covering strip index. -/

/-- The unique strip index `iv ≤ half` whose stabilizer carries `Z` at an in-band `q`. -/
def coverIv (d row q : Nat) : Nat :=
  if row % 2 = 0 then (if q % d = d - 1 then (d - 1) / 2 else q % d / 2)
  else (if q % d = 0 then (d - 1) / 2 else (q % d - 1) / 2)

theorem coverIv_le_half (d row q half : Nat) (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hqd : q % d < d) : coverIv d row q ≤ half := by
  unfold coverIv
  have hh2 : (d - 1) / 2 = half := by omega
  split <;> split <;> omega

/-- `tRow` is `Z` exactly on the two-row band. -/
theorem tRow_eq (d row q : Nat) :
    tRow d row q = if (q / d = row ∨ q / d = row + 1) then Pauli.Z else Pauli.I := by
  unfold tRow rowCutPauli
  by_cases h1 : q / d = row <;> by_cases h2 : q / d = row + 1 <;>
    simp_all (config := {decide := true})

/-- Out of band, every strip stabilizer is `I` at `q`. -/
theorem stripCovered_false_outBand (d row iv q : Nat)
    (hout : ¬ (q / d = row ∨ q / d = row + 1)) :
    stripCovered d row iv q = false := by
  unfold stripCovered
  simp only [Bool.and_eq_false_iff]
  left
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨fun h => hout (Or.inl h), fun h => hout (Or.inr h)⟩

/-- In band, the strip stabilizer carries `Z` exactly at the unique cover index. -/
theorem stripCovered_eq_decide (d row iv half : Nat) (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hrow : row < d - 1) (hiv : iv ≤ half) (q : Nat)
    (hband : q / d = row ∨ q / d = row + 1) (hqd : q % d < d) :
    stripCovered d row iv q = decide (iv = coverIv d row q) := by
  have hh2 : (d - 1) / 2 = half := by omega
  unfold stripCovered coverIv
  have hbandtrue : (q / d = row || q / d = row + 1) = true := by
    rcases hband with h | h <;> simp [h]
  rw [hbandtrue, Bool.true_and, Bool.eq_iff_iff]
  by_cases hp : row % 2 = 0
  · simp only [if_pos hp, hh2]
    by_cases hqc : q % d = d - 1
    · simp only [if_pos hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega
    · simp only [if_neg hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega
  · simp only [if_neg hp, hh2]
    by_cases hqc : q % d = 0
    · simp only [if_pos hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega
    · simp only [if_neg hqc]; split_ifs <;>
        simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega


/-! ## The pure-Nat hunion identity. -/

/-- **The strip-tiling identity (pure Nat form).** The product of the `half+1` strip
stabilizers equals the two-cut bridge `tRow`, at every qubit. -/
theorem hunion_pure (d row q half : Nat) (hhalf : d - 1 = 2 * half) (hd3 : 3 ≤ d)
    (hrow : row < d - 1) (hqd : q % d < d) :
    partialStabilizerFold (half + 1)
        (fun iv q => some (surfaceCellPauli d (stripIndexVal d row iv) q)) q
      = some (tRow d row q) := by
  have hbody : ∀ iv, iv ≤ half →
      some (surfaceCellPauli d (stripIndexVal d row iv) q)
        = some (if stripCovered d row iv q then Pauli.Z else Pauli.I) := by
    intro iv hiv
    rw [stripCellPauli_eq d row iv half hhalf hd3 hrow hiv]
  rw [tRow_eq]
  by_cases hband : q / d = row ∨ q / d = row + 1
  · -- in band: a unique strip stabilizer covers q
    rw [if_pos hband]
    have hcov : coverIv d row q ≤ half := coverIv_le_half d row q half hhalf hd3 hqd
    apply fold_unique_Z (half + 1) (coverIv d row q) _ q (Nat.lt_succ_of_le hcov)
    · rw [hbody (coverIv d row q) hcov,
        stripCovered_eq_decide d row (coverIv d row q) half hhalf hd3 hrow hcov q hband hqd]
      simp
    · intro i hi hne
      rw [hbody i (by omega),
        stripCovered_eq_decide d row i half hhalf hd3 hrow (by omega) q hband hqd]
      simp [hne]
  · -- out of band: every strip stabilizer is I
    rw [if_neg hband]
    apply fold_all_I
    intro i hi
    rw [hbody i (by omega), stripCovered_false_outBand d row i q hband]
    rfl


/-! ## Gateway bridges: index value + strip width. -/

/-- `gridRowZStripIndex` (a kernel Term) evaluates to the Nat `stripIndexVal`. -/
theorem gridRowZStripIndex_eval (dist : Nat) {arity : Nat} (rowT slotT : Term arity .nat)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) {rv sv : Nat}
    (hrow : Term.eval cb fuel rowT rho = some rv)
    (hslot : Term.eval cb fuel slotT rho = some sv) :
    Term.eval cb fuel (SFormula.gridRowZStripIndex dist rowT slotT) rho
      = some (stripIndexVal dist rv sv) := by
  unfold SFormula.gridRowZStripIndex stripIndexVal
  simp only [Term.eval, hrow, hslot]
  split_ifs <;> simp_all

/-- `gridStripWidth dist = (dist-1)/2 + 1`. -/
theorem gridStripWidth_eq (dist : Nat) :
    SFormula.gridStripWidth dist = (dist - 1) / 2 + 1 := rfl


/-! ## eqPauli extraction: pin the stabAt eval value. -/

/-- From `eqPauli a (closed (pauliLit p))` evaluating `true`, recover `a.eval = some p`. -/
theorem eqPauli_pauliLit_extract {arity : Nat} (a : STerm arity .pauli) (p : Pauli)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) (E : PartialStabilizer)
    (h : (SFormula.eqPauli a (SC.closed (Term.pauliLit p))).eval cb fuel rho E = some true) :
    STerm.eval cb fuel a rho E = some p := by
  simp only [SFormula.eval, SC.closed, STerm.eval, Term.eval] at h
  cases ha : STerm.eval cb fuel a rho E with
  | none => rw [ha] at h; simp at h
  | some av => rw [ha] at h; simp at h; exact congrArg some h
