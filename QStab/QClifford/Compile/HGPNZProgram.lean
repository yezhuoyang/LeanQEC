import QStab.QClifford.Compile.XZProgramOfPrograms
import QStab.QHL.CodeHGP
import QStab.QHL.CodeHGPEval
import QStab.QHL.CodeHGPSchedule

/-!
# The parametric HGP compiler-facing program and its re-anchor

`hgpXZProgram d` is **defined through the code-blind generator** — the object
program `HGP.code` and the two certified schedule programs are the only
inputs — and then re-anchored: each per-check schedule is exactly the pinned
reference (`hgpSupportList` order, CSS kind read from the code's content via
the certified-evaluation anchor `code_evalAt?_eq_stabEntry`).

* `hgpKind` / `hgpSchedule` — the reference schedule (uniform CSS kind over
  the support list, `%`-totalized into `Fin (d² + (d-1)²)`).
* `stabEntry_mem_supportList` — support-Pauli faithfulness: the code's entry
  at every scheduled qubit is the check's CSS Pauli (never `I`/`Y`), so the
  generator's `kindOfPauli` fallback is proved unreachable.
* `genSchedule_eq_hgpSchedule` — per-check schedule equality.
* `hgpXZProgram_eq_foldr` — the program-level anchor.
* `hgpCompiledProgram_eq` — the `d = 3` demo instance is the `d = 3` member.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford
open QHL.CodeLang
open QHL.CodeHGPSchedule

/-- CSS kind of HGP generator `k`: the first `(d-1)·d` are X-type. -/
def hgpKind (d k : Nat) : XZPauli :=
  if k < (d - 1) * d then XZPauli.X else XZPauli.Z

/-- The corresponding code Pauli. -/
def hgpKindPauli (d k : Nat) : Pauli :=
  if k < (d - 1) * d then Pauli.X else Pauli.Z

/-- Totalization of a qubit index into `Fin (d² + (d-1)²)` for `d ≥ 2`. -/
def hgpFin (d : Nat) (hd : 2 ≤ d) (q : Nat) : Fin (d * d + (d - 1) * (d - 1)) :=
  ⟨q % (d * d + (d - 1) * (d - 1)),
   Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega))
     (Nat.le_add_right _ _))⟩

/-- **The reference schedule** of HGP generator `i`: its CSS kind, uniformly,
    over the pinned support order. -/
def hgpSchedule (d : Nat) (hd : 2 ≤ d) (i : Fin (2 * ((d - 1) * d))) :
    RuleSchedule (d * d + (d - 1) * (d - 1)) :=
  RuleSchedule.uniform (hgpKind d i.val) ((hgpSupportList d i.val).map (hgpFin d hd))

-- Div/mod recomposition facts (as in `HGPParametric`, restated locally).
private theorem div_mul_add (d a b : Nat) (hd : 0 < d) (hb : b < d) :
    (d * a + b) / d = a := by
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mod_mul_add (d a b : Nat) (hb : b < d) : (d * a + b) % d = b := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

/-- **Support-Pauli faithfulness.**  The code's entry at every scheduled qubit
    of generator `k` is the generator's CSS Pauli — the tensor formulas put
    exactly `X` (resp. `Z`) on every support-list member. -/
theorem stabEntry_mem_supportList (d k q : Nat) (hd : 2 ≤ d)
    (hk : k < 2 * ((d - 1) * d)) (hq : q ∈ hgpSupportList d k) :
    QStab.Examples.HGPParametric.stabEntry d k q = hgpKindPauli d k := by
  have hqlt : q < d * d + (d - 1) * (d - 1) := hgpSupportList_lt d k hd hk q hq
  unfold hgpSupportList at hq
  unfold hgpKindPauli
  by_cases hx : k < (d - 1) * d
  · rw [if_pos hx] at hq
    rw [if_pos hx]
    have hi : k / d < d - 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hx
    have hj : k % d < d := Nat.mod_lt _ (by omega)
    have hs0 : d * (k / d) + k % d < d * d := by
      have hstep : d * (k / d) + k % d < d * (k / d) + d := by omega
      calc d * (k / d) + k % d < d * (k / d) + d := hstep
        _ = d * (k / d + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    have hs1 : d * (k / d + 1) + k % d < d * d := by
      calc d * (k / d + 1) + k % d < d * (k / d + 1) + d := by omega
        _ = d * (k / d + 1 + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with ((rfl | rfl) | hq) | hq
    · -- sector-1 row i
      rw [QStab.Examples.HGPParametric.stabEntry_X_s1_eq d k _ hx hs0,
        if_pos ⟨mod_mul_add d _ _ hj, Or.inl (div_mul_add d _ _ (by omega) hj)⟩]
    · -- sector-1 row i+1
      rw [QStab.Examples.HGPParametric.stabEntry_X_s1_eq d k _ hx hs1,
        if_pos ⟨mod_mul_add d _ _ hj, Or.inr (div_mul_add d _ _ (by omega) hj)⟩]
    · -- sector-2 left neighbour (guard `1 ≤ k % d`)
      by_cases hg : 1 ≤ k % d
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have hns1 : ¬d * d + k / d * (d - 1) + (k % d - 1) < d * d := by omega
        have hp : d * d + k / d * (d - 1) + (k % d - 1) - d * d
            = (d - 1) * (k / d) + (k % d - 1) := by
          rw [Nat.mul_comm (k / d) (d - 1)]
          omega
        have hc : k % d - 1 < d - 1 := by omega
        rw [QStab.Examples.HGPParametric.stabEntry_X_s2_eq d k _ hx hns1 hqlt,
          if_pos ⟨by rw [hp]; exact div_mul_add _ _ _ (by omega) hc,
            Or.inr (by rw [hp, mod_mul_add _ _ _ hc]; omega)⟩]
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim
    · -- sector-2 right neighbour (guard `k % d ≤ d - 2`)
      by_cases hg : k % d ≤ d - 2
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have hns1 : ¬d * d + k / d * (d - 1) + k % d < d * d := by omega
        have hp : d * d + k / d * (d - 1) + k % d - d * d
            = (d - 1) * (k / d) + k % d := by
          rw [Nat.mul_comm (k / d) (d - 1)]
          omega
        have hc : k % d < d - 1 := by omega
        rw [QStab.Examples.HGPParametric.stabEntry_X_s2_eq d k _ hx hns1 hqlt,
          if_pos ⟨by rw [hp]; exact div_mul_add _ _ _ (by omega) hc,
            Or.inl (by rw [hp]; exact mod_mul_add _ _ _ hc)⟩]
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim
  · rw [if_neg hx] at hq
    rw [if_neg hx]
    have hzk : (d - 1) * d ≤ k := Nat.le_of_not_lt hx
    have hd1 : 0 < d - 1 := by omega
    have ht : k - (d - 1) * d < (d - 1) * d := by omega
    have ha : (k - (d - 1) * d) / (d - 1) < d :=
      (Nat.div_lt_iff_lt_mul hd1).mpr (by rw [Nat.mul_comm d (d - 1)]; exact ht)
    have hjz : (k - (d - 1) * d) % (d - 1) < d - 1 := Nat.mod_lt _ hd1
    have hs0 : d * ((k - (d - 1) * d) / (d - 1)) + (k - (d - 1) * d) % (d - 1)
        < d * d := by
      calc d * ((k - (d - 1) * d) / (d - 1)) + (k - (d - 1) * d) % (d - 1)
          < d * ((k - (d - 1) * d) / (d - 1)) + d := by omega
        _ = d * ((k - (d - 1) * d) / (d - 1) + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    have hs1 : d * ((k - (d - 1) * d) / (d - 1)) + ((k - (d - 1) * d) % (d - 1) + 1)
        < d * d := by
      calc d * ((k - (d - 1) * d) / (d - 1)) + ((k - (d - 1) * d) % (d - 1) + 1)
          < d * ((k - (d - 1) * d) / (d - 1)) + d := by omega
        _ = d * ((k - (d - 1) * d) / (d - 1) + 1) := (Nat.mul_succ _ _).symm
        _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with ((rfl | rfl) | hq) | hq
    · -- sector-1 column j
      have hjzd : (k - (d - 1) * d) % (d - 1) < d := by omega
      rw [QStab.Examples.HGPParametric.stabEntry_Z_s1_eq d k _ hzk hk hs0,
        if_pos ⟨div_mul_add d _ _ (by omega) hjzd,
          Or.inl (mod_mul_add d _ _ hjzd)⟩]
    · -- sector-1 column j+1
      have hjz1 : (k - (d - 1) * d) % (d - 1) + 1 < d := by omega
      rw [QStab.Examples.HGPParametric.stabEntry_Z_s1_eq d k _ hzk hk hs1,
        if_pos ⟨div_mul_add d _ _ (by omega) hjz1,
          Or.inr (mod_mul_add d _ _ hjz1)⟩]
    · -- sector-2 row a-1 (guard `1 ≤ a`)
      by_cases hg : 1 ≤ (k - (d - 1) * d) / (d - 1)
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have hns1 : ¬d * d + ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1)
            + (k - (d - 1) * d) % (d - 1) < d * d := by omega
        have hp : d * d + ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1)
            + (k - (d - 1) * d) % (d - 1) - d * d
            = (d - 1) * ((k - (d - 1) * d) / (d - 1) - 1)
              + (k - (d - 1) * d) % (d - 1) := by
          rw [Nat.mul_comm ((k - (d - 1) * d) / (d - 1) - 1) (d - 1)]
          omega
        rw [QStab.Examples.HGPParametric.stabEntry_Z_s2_eq d k _ hzk hk hns1 hqlt,
          if_pos ⟨by rw [hp]; exact mod_mul_add _ _ _ hjz,
            Or.inr (by rw [hp, div_mul_add _ _ _ hd1 hjz]
                       exact Nat.sub_add_cancel hg)⟩]
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim
    · -- sector-2 row a (guard `a ≤ d - 2`)
      by_cases hg : (k - (d - 1) * d) / (d - 1) ≤ d - 2
      · rw [if_pos hg] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have hns1 : ¬d * d + (k - (d - 1) * d) / (d - 1) * (d - 1)
            + (k - (d - 1) * d) % (d - 1) < d * d := by omega
        have hp : d * d + (k - (d - 1) * d) / (d - 1) * (d - 1)
            + (k - (d - 1) * d) % (d - 1) - d * d
            = (d - 1) * ((k - (d - 1) * d) / (d - 1))
              + (k - (d - 1) * d) % (d - 1) := by
          rw [Nat.mul_comm ((k - (d - 1) * d) / (d - 1)) (d - 1)]
          omega
        rw [QStab.Examples.HGPParametric.stabEntry_Z_s2_eq d k _ hzk hk hns1 hqlt,
          if_pos ⟨by rw [hp]; exact mod_mul_add _ _ _ hjz,
            Or.inl (by rw [hp]; exact div_mul_add _ _ _ hd1 hjz)⟩]
      · rw [if_neg hg] at hq
        exact (List.not_mem_nil hq).elim

/-- **The code's evaluated Pauli at every scheduled qubit is the CSS kind** —
    stated over `HGP.code` via the certified-evaluation anchor. -/
theorem hgp_evalAt_supportList (d k q : Nat) (hd : 2 ≤ d)
    (hk : k < 2 * ((d - 1) * d)) (hq : q ∈ hgpSupportList d k) :
    QHL.CodeLang.HGP.code.evalAt? d k q = some (hgpKindPauli d k) := by
  rw [QHL.CodeLang.HGP.code_evalAt?_eq_stabEntry,
    stabEntry_mem_supportList d k q hd hk hq]

/-- **The kind default never fires**: reading the CSS Pauli back through
    `kindOfPauli` is faithful. -/
theorem kindOfPauli_hgpKindPauli (d k : Nat) :
    kindOfPauli (some (hgpKindPauli d k)) = hgpKind d k := by
  unfold hgpKindPauli hgpKind
  by_cases hx : k < (d - 1) * d
  · rw [if_pos hx, if_pos hx]
    rfl
  · rw [if_neg hx, if_neg hx]
    rfl

/-- **Per-check schedule equality.**  The generated schedule at `k = i.val`
    equals the reference `hgpSchedule` — kind via the certified-evaluation
    anchor and support-Pauli faithfulness, qubit via the certified order
    program. -/
theorem genSchedule_eq_hgpSchedule (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) :
    genSchedule QHL.CodeLang.HGP.code hgpOrderProg hgpLenProg
      (d * d + (d - 1) * (d - 1)) d i.val = hgpSchedule d hd i := by
  have hpos : 0 < d * d + (d - 1) * (d - 1) :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) (Nat.le_add_right _ _)
  have hlen : (Term.eval QHL.CodeLang.HGP.code.body (CodeFn.fuelForDistance d)
      hgpLenProg (Env.code d i.val)).getD 0 = hgpLenFlat d i.val := by
    rw [hgpLenProg_eval _ _ _ _ hd i.isLt]; rfl
  simp only [genSchedule, hlen, dif_pos hpos, hgpSchedule, RuleSchedule.uniform]
  congr 1
  apply List.ext_getElem
  · simp [hgpLenFlat]
  · intro j h1 _h2
    have hjlen : j < hgpLenFlat d i.val := by
      simpa [List.length_map, List.length_range] using h1
    have horder : (Term.eval QHL.CodeLang.HGP.code.body (CodeFn.fuelForDistance d)
        hgpOrderProg (Env.cons j (Env.code d i.val))).getD 0
        = hgpOrderFlat d i.val j := by
      rw [hgpOrderProg_eval _ _ _ _ _ hd i.isLt]; rfl
    have hget : (hgpSupportList d i.val)[j] = hgpOrderFlat d i.val j := by
      show _ = (hgpSupportList d i.val)[j]?.getD _
      rw [List.getElem?_eq_getElem hjlen]
      rfl
    simp only [List.getElem_map, List.getElem_range]
    congr 1
    · rw [horder,
        hgp_evalAt_supportList d i.val _ hd i.isLt (hgpOrderFlat_mem d i.val j hjlen),
        kindOfPauli_hgpKindPauli]
    · apply Fin.ext
      show (Term.eval QHL.CodeLang.HGP.code.body (CodeFn.fuelForDistance d)
        hgpOrderProg (Env.cons j (Env.code d i.val))).getD 0
        % (d * d + (d - 1) * (d - 1)) = _
      rw [horder]
      show _ = (hgpFin d hd (hgpSupportList d i.val)[j]).val
      rw [hget]
      rfl

/-- **The parametric compiler-facing HGP program** — defined through the
    code-blind generator from `HGP.code` and its two certified schedule
    programs. -/
def hgpXZProgram (d : Nat) : XZProgram (d * d + (d - 1) * (d - 1)) :=
  xzProgramOfPrograms QHL.CodeLang.HGP.code hgpOrderProg hgpLenProg
    (2 * ((d - 1) * d)) (d * d + (d - 1) * (d - 1)) d

private theorem range_eq_finRange_map (n : Nat) :
    List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2; simp

/-- **The program-level anchor**: `hgpXZProgram d` is the fold of the
    reference schedules, one `.meas .NZ` per generator in index order. -/
theorem hgpXZProgram_eq_foldr (d : Nat) (hd : 2 ≤ d) :
    hgpXZProgram d = (List.finRange (2 * ((d - 1) * d))).foldr
      (fun i acc => .seq (.meas .NZ (hgpSchedule d hd i)) acc) .skip := by
  unfold hgpXZProgram xzProgramOfPrograms
  rw [range_eq_finRange_map, List.foldr_map]
  congr 1
  funext i acc
  rw [genSchedule_eq_hgpSchedule d hd i]

#print axioms genSchedule_eq_hgpSchedule
#print axioms hgpXZProgram_eq_foldr

end QStab.QClifford.Compile
