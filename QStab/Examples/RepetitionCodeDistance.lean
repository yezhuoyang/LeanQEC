import QStab.Paper.CodeDistance
import QStab.QHL.CodeRepetition

/-!
# Code distance of the parametric repetition code, in the shared assertion vocabulary

The `Z_i Z_{i+1}` repetition family `[[d, 1, 1]]` for every `d ≥ 2`, in the shared
`CodeDistanceAtLeast` / `CodeDistanceExactly` framework — **parametric in `d`**, proved
structurally (decide-free).

Honest framing: the **quantum** code distance is `1` (the single-qubit `Z̄ = Z₀` is a nontrivial
logical of weight 1); the `X`/bit-flip logical has the larger distance `d`, proved separately in
the object language's own assertion logic (`QStab.QHL.CodeRepetition`).  This file gives the
quantum distance `= 1` in the code-agnostic framework, for all `d` at once.
-/

namespace QStab.Examples.RepetitionDistance

open QStab QStab.Paper.CodeDistance

/-- The `k`-th repetition generator `Z_k Z_{k+1}`. -/
def repStab (d : Nat) (i : Fin (d - 1)) : ErrorVec d :=
  fun q => if q.val = i.val ∨ q.val = i.val + 1 then Pauli.Z else Pauli.I

/-- Logical `X̄ = X…X`. -/
def repXbar (d : Nat) : ErrorVec d := fun _ => Pauli.X
/-- The weight-1 logical `Z̄ = Z₀`. -/
def repZ0 (d : Nat) : ErrorVec d := fun q => if q.val = 0 then Pauli.Z else Pauli.I

def repParams (d : Nat) (hd : 2 ≤ d) : QECParams where
  n := d; k := 1; d := 1; R := 1; numStab := d - 1
  stabilizers := repStab d
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := by intro s e he; exact he.elim
  C_budget := 1
  hn := by omega
  hns := by omega
  hR := by omega

/-- Every stabilizer generator is `Z`-type. -/
theorem repStab_Ztype (d : Nat) (i : Fin (d - 1)) (q : Fin d) :
    repStab d i q = Pauli.Z ∨ repStab d i q = Pauli.I := by
  simp only [repStab]; split <;> simp

/-- A `Z`-type operator commutes with any `Z`-type operator (both have only `Z`/`I`). -/
theorem parity_Ztype {n : Nat} (S T : ErrorVec n)
    (hS : ∀ q, S q = Pauli.Z ∨ S q = Pauli.I) (hT : ∀ q, T q = Pauli.Z ∨ T q = Pauli.I) :
    ErrorVec.parity S T = false := by
  unfold ErrorVec.parity
  have : (Finset.univ.filter fun q => ErrorVec.Pauli.anticommutes (S q) (T q)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q _
    rcases hS q with h | h <;> rcases hT q with h' | h' <;> rw [h, h'] <;> decide
  simp [this]

/-- `Z̄ = Z₀` is `Z`-type. -/
theorem repZ0_Ztype (d : Nat) (q : Fin d) : repZ0 d q = Pauli.Z ∨ repZ0 d q = Pauli.I := by
  simp only [repZ0]; split <;> simp

/-- Weight of a nonzero operator is at least 1. -/
theorem weight_pos {n : Nat} {E : ErrorVec n} (h : E ≠ ErrorVec.identity n) :
    1 ≤ ErrorVec.weight E := by
  by_contra hlt
  have h0 : ErrorVec.weight E = 0 := by omega
  apply h
  funext q
  by_contra hq
  have : q ∈ Finset.univ.filter fun i => E i ≠ Pauli.I := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hq
  have : 0 < (Finset.univ.filter fun i => E i ≠ Pauli.I).card :=
    Finset.card_pos.mpr ⟨q, this⟩
  unfold ErrorVec.weight at h0; omega

/-- **Quantum code distance ≥ 1** — every nontrivial logical has weight ≥ 1 (parametric in `d`). -/
theorem rep_codeDistanceAtLeast_1 (d : Nat) (hd : 2 ≤ d) :
    CodeDistanceAtLeast (repParams d hd) 1 := by
  intro E _ hnot
  apply weight_pos
  intro hE
  exact hnot (hE ▸ InStab.identity)

/-- `Z₀` has weight exactly 1 (support `{0}`). -/
theorem repZ0_weight (d : Nat) (hd : 2 ≤ d) : ErrorVec.weight (repZ0 d) = 1 := by
  have hmem : ∀ q : Fin d, (repZ0 d q ≠ Pauli.I) ↔ q.val = 0 := by
    intro q; simp only [repZ0]; constructor
    · intro h; by_contra hq; rw [if_neg hq] at h; exact h rfl
    · intro h; rw [if_pos h]; exact fun hc => by cases hc
  unfold ErrorVec.weight
  rw [show (Finset.univ.filter fun q : Fin d => repZ0 d q ≠ Pauli.I)
        = {(⟨0, by omega⟩ : Fin d)} from ?_]
  · exact Finset.card_singleton _
  · ext q
    rw [Finset.mem_filter, Finset.mem_singleton, Fin.ext_iff]
    simp only [Finset.mem_univ, true_and]; exact hmem q

/-- `X̄` anticommutes with `Z₀` (overlap exactly at qubit 0). -/
theorem repXbar_anti_repZ0 (d : Nat) (hd : 2 ≤ d) :
    ErrorVec.parity (repXbar d) (repZ0 d) = true := by
  have hmem : ∀ q : Fin d,
      (ErrorVec.Pauli.anticommutes (repXbar d q) (repZ0 d q) = true) ↔ q.val = 0 := by
    intro q; simp only [repXbar, repZ0]; constructor
    · intro h; by_contra hq; rw [if_neg hq] at h; exact absurd h (by decide)
    · intro h; rw [if_pos h]; decide
  unfold ErrorVec.parity
  rw [show (Finset.univ.filter fun q : Fin d =>
        ErrorVec.Pauli.anticommutes (repXbar d q) (repZ0 d q)) = {(⟨0, by omega⟩ : Fin d)} from ?_]
  · rw [Finset.card_singleton]; decide
  · ext q
    rw [Finset.mem_filter, Finset.mem_singleton, Fin.ext_iff]
    simp only [Finset.mem_univ, true_and]; exact hmem q

/-- `X̄` commutes with each generator `Z_k Z_{k+1}` (overlap `{k, k+1}` has even size 2). -/
theorem repXbar_comm_repStab (d : Nat) (hd : 2 ≤ d) (i : Fin (d - 1)) :
    ErrorVec.parity (repXbar d) (repStab d i) = false := by
  have hi1 : i.val + 1 < d := by have := i.isLt; omega
  have hi0 : i.val < d := by have := i.isLt; omega
  have hmem : ∀ q : Fin d,
      (ErrorVec.Pauli.anticommutes (repXbar d q) (repStab d i q) = true)
        ↔ (q.val = i.val ∨ q.val = i.val + 1) := by
    intro q; simp only [repXbar, repStab]; constructor
    · intro h; by_contra hq; rw [if_neg hq] at h; exact absurd h (by decide)
    · intro h; rw [if_pos h]; decide
  unfold ErrorVec.parity
  rw [show (Finset.univ.filter fun q : Fin d =>
        ErrorVec.Pauli.anticommutes (repXbar d q) (repStab d i q))
        = {(⟨i.val, hi0⟩ : Fin d), (⟨i.val + 1, hi1⟩ : Fin d)} from ?_]
  · rw [Finset.card_insert_of_notMem
        (by simp only [Finset.mem_singleton, Fin.ext_iff]; omega), Finset.card_singleton]
    decide
  · ext q
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    simp only [Finset.mem_univ, true_and]; exact hmem q

/-- The weight-1 logical witness. -/
def repWitness (d : Nat) (hd : 2 ≤ d) : LogicalWitness (repParams d hd) 1 where
  op := repZ0 d
  centralizes := fun i => parity_Ztype _ _ (repStab_Ztype d i) (repZ0_Ztype d)
  not_stab := by
    intro h
    have hcomm : ErrorVec.parity (repXbar d) (repZ0 d) = false :=
      parity_commutes_of_InStab (P := repParams d hd) (repXbar d)
        (fun i => repXbar_comm_repStab d hd i) h
    rw [repXbar_anti_repZ0 d hd] at hcomm; exact absurd hcomm (by decide)
  weight_eq := repZ0_weight d hd

/-- **Quantum code distance of the repetition code = 1, exactly**, for every `d ≥ 2` —
in the shared framework, fully parametric. -/
theorem rep_codeDistanceExactly_1 (d : Nat) (hd : 2 ≤ d) :
    CodeDistanceExactly (repParams d hd) 1 :=
  codeDistanceExactly_intro (rep_codeDistanceAtLeast_1 d hd) (repWitness d hd)

/-! ## Object-program anchor (Route B: recursive certified evaluation, axiom-clean) -/

/-- **Object-program anchor.**  The *recursive* OCaml-language repetition program
`QHL.CodeLang.Repetition.code`, evaluated at distance `d`, produces *exactly* the generators
`repStab d i` whose code distance we proved — via the recursive certified evaluation
`code_evalAt?_eq_arith` (axiom-clean, no `native_decide`).  So `rep_codeDistanceExactly_1` is
provably a statement about the object-language program, for every `d` at once — the parametric
counterpart of the five-qubit / Steane anchors, on a genuinely recursive `.recCall` program. -/
theorem rep_objectProgram_anchor (d : Nat) (hd : 2 ≤ d) (i : Fin (d - 1)) (q : Fin d) :
    QHL.CodeLang.Repetition.code.evalAt? d i.val q.val = some (repStab d i q) := by
  rw [QHL.CodeLang.Repetition.code_evalAt?_eq_arith d i.val q.val (by have := i.isLt; omega)]
  simp only [QHL.CodeLang.Repetition.repEntryArith, repStab]

end QStab.Examples.RepetitionDistance
