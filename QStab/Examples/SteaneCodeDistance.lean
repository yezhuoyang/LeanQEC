import QStab.Paper.CodeDistance
import QStab.QHL.CodeSteane
import Mathlib.Data.Fintype.Pi

set_option maxRecDepth 8192

/-!
# Code distance of the `[[7,1,3]]` Steane code, in the shared assertion vocabulary

Instantiates `CodeDistanceAtLeast` / `CodeDistanceExactly` (`QStab.Paper.CodeDistance`) for the
Steane code — a CSS code — and anchors the result to the OCaml-language object program
`QHL.CodeLang.Steane.code` via the certified evaluation `code_evalAt?_eq_arith` (Route B,
axiom-clean).  This file delivers **distance = 3** and the **object-program anchor**, all via shallow kernel
`decide` (axiom-clean, crash-safe) — the lower bound uses the CSS/Hamming factorization.
-/

namespace QStab.Examples.SteaneDistance

open QStab QStab.Paper.CodeDistance

instance : Fintype Pauli where
  elems := {Pauli.I, Pauli.X, Pauli.Y, Pauli.Z}
  complete := fun p => by cases p <;> decide

/-- Positional 7-qubit Pauli vector. -/
def v7 (a b c d e f g : Pauli) : ErrorVec 7 := fun q =>
  if q.val = 0 then a else if q.val = 1 then b else if q.val = 2 then c else if q.val = 3 then d
  else if q.val = 4 then e else if q.val = 5 then f else g

/-- The six Steane generators: three X-type + three Z-type Hamming rows. -/
def steaneStab : Fin 6 → ErrorVec 7
  | ⟨0, _⟩ => v7 .X .I .X .I .X .I .X   -- X{0,2,4,6}
  | ⟨1, _⟩ => v7 .I .X .X .I .I .X .X   -- X{1,2,5,6}
  | ⟨2, _⟩ => v7 .I .I .I .X .X .X .X   -- X{3,4,5,6}
  | ⟨3, _⟩ => v7 .Z .I .Z .I .Z .I .Z   -- Z{0,2,4,6}
  | ⟨4, _⟩ => v7 .I .Z .Z .I .I .Z .Z   -- Z{1,2,5,6}
  | ⟨5, _⟩ => v7 .I .I .I .Z .Z .Z .Z   -- Z{3,4,5,6}

/-- Logical `X̄ = XXXXXXX`. -/
def steaneXbar : ErrorVec 7 := v7 .X .X .X .X .X .X .X

def steaneParams : QECParams where
  n := 7; k := 1; d := 3; R := 1; numStab := 6
  stabilizers := steaneStab
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := by intro s e he; exact he.elim
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Lower bound via CSS/Hamming factorization (crash-safe: `2⁷` Bool decide) -/

/-- X-component mask: `true` where `E q` anticommutes with `Z` (`E q ∈ {X, Y}`). -/
def xMask (E : ErrorVec 7) : Fin 7 → Bool := fun q => ErrorVec.Pauli.anticommutes Pauli.Z (E q)
/-- Z-component mask: `true` where `E q` anticommutes with `X` (`E q ∈ {Y, Z}`). -/
def zMask (E : ErrorVec 7) : Fin 7 → Bool := fun q => ErrorVec.Pauli.anticommutes Pauli.X (E q)

def maskVecX (m : Fin 7 → Bool) : ErrorVec 7 := fun q => if m q then Pauli.X else Pauli.I
def maskVecZ (m : Fin 7 → Bool) : ErrorVec 7 := fun q => if m q then Pauli.Z else Pauli.I

/-- Parity depends only on the pointwise anticommutation pattern. -/
theorem parity_congr_anti {n : Nat} (S E F : ErrorVec n)
    (h : ∀ q, ErrorVec.Pauli.anticommutes (S q) (E q) = ErrorVec.Pauli.anticommutes (S q) (F q)) :
    ErrorVec.parity S E = ErrorVec.parity S F := by
  unfold ErrorVec.parity
  simp only [h]

theorem parity_xMask_bridge (E : ErrorVec 7) (i : Fin 6) (hi : 3 ≤ i.val) :
    ErrorVec.parity (steaneStab i) E = ErrorVec.parity (steaneStab i) (maskVecX (xMask E)) := by
  apply parity_congr_anti; intro q
  have hZ : steaneStab i q = Pauli.Z ∨ steaneStab i q = Pauli.I := by
    fin_cases i <;> simp_all <;> (fin_cases q <;> decide)
  have key : ∀ (pp ss : Pauli), (ss = Pauli.Z ∨ ss = Pauli.I) →
      ErrorVec.Pauli.anticommutes ss pp = ErrorVec.Pauli.anticommutes ss
        (if ErrorVec.Pauli.anticommutes Pauli.Z pp = true then Pauli.X else Pauli.I) := by
    intro pp ss hs; rcases hs with h | h <;> subst h <;> cases pp <;> decide
  simp only [maskVecX, xMask]
  exact key (E q) (steaneStab i q) hZ

theorem parity_zMask_bridge (E : ErrorVec 7) (i : Fin 6) (hi : i.val < 3) :
    ErrorVec.parity (steaneStab i) E = ErrorVec.parity (steaneStab i) (maskVecZ (zMask E)) := by
  apply parity_congr_anti; intro q
  have hX : steaneStab i q = Pauli.X ∨ steaneStab i q = Pauli.I := by
    fin_cases i <;> simp_all <;> (fin_cases q <;> decide)
  have key : ∀ (pp ss : Pauli), (ss = Pauli.X ∨ ss = Pauli.I) →
      ErrorVec.Pauli.anticommutes ss pp = ErrorVec.Pauli.anticommutes ss
        (if ErrorVec.Pauli.anticommutes Pauli.X pp = true then Pauli.Z else Pauli.I) := by
    intro pp ss hs; rcases hs with h | h <;> subst h <;> cases pp <;> decide
  simp only [maskVecZ, zMask]
  exact key (E q) (steaneStab i q) hX

/-- **Hamming distance-3 (X side)** over Bool masks — `2⁷ = 128` cases, shallow/safe. -/
theorem hamming_X_lb : ∀ (m : Fin 7 → Bool),
    (∀ i : Fin 6, 3 ≤ i.val → ErrorVec.parity (steaneStab i) (maskVecX m) = false) →
    (Finset.univ.filter (fun q => m q = true)).card ≤ 2 → ∀ q, m q = false := by decide

/-- **Hamming distance-3 (Z side)**. -/
theorem hamming_Z_lb : ∀ (m : Fin 7 → Bool),
    (∀ i : Fin 6, i.val < 3 → ErrorVec.parity (steaneStab i) (maskVecZ m) = false) →
    (Finset.univ.filter (fun q => m q = true)).card ≤ 2 → ∀ q, m q = false := by decide

theorem card_xMask_le_weight (E : ErrorVec 7) :
    (Finset.univ.filter (fun q => xMask E q = true)).card ≤ ErrorVec.weight E := by
  apply Finset.card_le_card; intro q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, xMask] at hq ⊢
  cases hE : E q <;> simp_all [ErrorVec.Pauli.anticommutes]

theorem card_zMask_le_weight (E : ErrorVec 7) :
    (Finset.univ.filter (fun q => zMask E q = true)).card ≤ ErrorVec.weight E := by
  apply Finset.card_le_card; intro q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, zMask] at hq ⊢
  cases hE : E q <;> simp_all [ErrorVec.Pauli.anticommutes]

theorem eq_identity_of_masks (E : ErrorVec 7)
    (hx : ∀ q, xMask E q = false) (hz : ∀ q, zMask E q = false) : E = ErrorVec.identity 7 := by
  funext q
  have h1 := hx q; have h2 := hz q
  simp only [xMask] at h1; simp only [zMask] at h2
  cases hE : E q <;> simp_all [ErrorVec.Pauli.anticommutes, ErrorVec.identity]

/-- **Code distance ≥ 3** — CSS/Hamming factorization (two `2⁷` Bool decides + mask bridges),
no `4⁷` enumeration. -/
theorem st_codeDistanceAtLeast_3 : CodeDistanceAtLeast steaneParams 3 := by
  intro E hcent hnot
  by_contra hlt
  have hw : ErrorVec.weight E ≤ 2 := by omega
  have hx0 : ∀ q, xMask E q = false := by
    refine hamming_X_lb (xMask E) (fun i hi => ?_) (le_trans (card_xMask_le_weight E) hw)
    rw [← parity_xMask_bridge E i hi]; exact hcent i
  have hz0 : ∀ q, zMask E q = false := by
    refine hamming_Z_lb (zMask E) (fun i hi => ?_) (le_trans (card_zMask_le_weight E) hw)
    rw [← parity_zMask_bridge E i hi]; exact hcent i
  exact hnot (by rw [eq_identity_of_masks E hx0 hz0]; exact InStab.identity)


/-- A weight-3 logical: `Z̄·(Z-check₀) = Z{1,3,5}` — centralizes every stabilizer,
anticommutes with `X̄`. -/
def steaneLogicalZ3 : ErrorVec 7 := v7 .I .Z .I .Z .I .Z .I

/-- The weight-3 logical witness certifying distance ≤ 3 (non-membership via `X̄`-anticommutation
through the generic `parity_commutes_of_InStab`). -/
def steaneWitness : LogicalWitness steaneParams 3 where
  op := steaneLogicalZ3
  centralizes := by decide
  not_stab := by
    intro h
    have hx : ErrorVec.parity steaneXbar steaneLogicalZ3 = false :=
      parity_commutes_of_InStab (P := steaneParams) steaneXbar (by decide) h
    revert hx; decide
  weight_eq := by decide

/-- **Steane code distance = 3, exactly** — the shared predicate, on a CSS code: lower bound
from the CSS/Hamming factorization, upper bound from a weight-3 logical witness. -/
theorem st_codeDistanceExactly_3 : CodeDistanceExactly steaneParams 3 :=
  codeDistanceExactly_intro st_codeDistanceAtLeast_3 steaneWitness

/-! ## Object-program anchor (Route B) -/

/-- The arithmetic mirror reconciles with the distance proof's generators. -/
theorem steaneEntryArith_eq_steaneStab (k : Fin 6) (q : Fin 7) :
    QHL.CodeLang.Steane.steaneEntryArith k.val q.val = steaneStab k q := by
  fin_cases k <;> fin_cases q <;> rfl

/-- **Object-program anchor.**  The OCaml-language Steane program evaluated at `d = 3` produces
exactly `steaneStab` — so `st_codeDistanceExactly_3` is about the object-language program. -/
theorem steane_objectProgram_anchor (k : Fin 6) (q : Fin 7) :
    QHL.CodeLang.Steane.code.evalAt? 3 k.val q.val = some (steaneStab k q) := by
  rw [QHL.CodeLang.Steane.code_evalAt?_eq_arith, steaneEntryArith_eq_steaneStab]

end QStab.Examples.SteaneDistance
