import QStab.Paper.LogicalCosets

/-!
# The CSS split of a Pauli error vector

Generic (code-agnostic) decomposition of an `ErrorVec` into its X-content and Z-content,
with the parity-restriction lemmas: X-type stabilizer rows read only the Z-content and
Z-type rows read only the X-content.  This is the entry point of every `maximal_isotropic`
cleaning proof (HGP chunk 4; the surface X-side campaign consumes it verbatim).
-/

namespace QStab.QClifford.Compile

/-- The Z-content of an error vector: `Z` where the entry has a Z-component, `I` elsewhere. -/
def zPartVec {n : Nat} (E : ErrorVec n) : ErrorVec n := fun q =>
  match E q with
  | Pauli.Z => Pauli.Z
  | Pauli.Y => Pauli.Z
  | _ => Pauli.I

/-- The X-content of an error vector: `X` where the entry has an X-component, `I` elsewhere. -/
def xPartVec {n : Nat} (E : ErrorVec n) : ErrorVec n := fun q =>
  match E q with
  | Pauli.X => Pauli.X
  | Pauli.Y => Pauli.X
  | _ => Pauli.I

/-- The split multiplies back: `E = xPart · zPart` (pointwise, phase-free). -/
theorem xPart_mul_zPart {n : Nat} (E : ErrorVec n) :
    ErrorVec.mul (xPartVec E) (zPartVec E) = E := by
  funext q
  show Pauli.mul (xPartVec E q) (zPartVec E q) = E q
  cases h : E q <;> simp only [xPartVec, zPartVec, h] <;> rfl

theorem zPartVec_ztype {n : Nat} (E : ErrorVec n) :
    ∀ q, zPartVec E q = Pauli.Z ∨ zPartVec E q = Pauli.I := by
  intro q
  unfold zPartVec
  cases E q
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem xPartVec_xtype {n : Nat} (E : ErrorVec n) :
    ∀ q, xPartVec E q = Pauli.X ∨ xPartVec E q = Pauli.I := by
  intro q
  unfold xPartVec
  cases E q
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- X-type rows read only the Z-content of an error. -/
theorem parity_xtype_zPart {n : Nat} (S E : ErrorVec n)
    (hS : ∀ q, S q = Pauli.X ∨ S q = Pauli.I) :
    ErrorVec.parity S E = ErrorVec.parity S (zPartVec E) := by
  unfold ErrorVec.parity
  have hcard : (Finset.univ.filter fun i =>
        ErrorVec.Pauli.anticommutes (S i) (E i)).card
      = (Finset.univ.filter fun i =>
        ErrorVec.Pauli.anticommutes (S i) (zPartVec E i)).card := by
    apply Finset.card_equiv (Equiv.refl _)
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.refl_apply]
    rcases hS q with h | h <;> cases hE : E q <;>
      simp [h, hE, zPartVec, ErrorVec.Pauli.anticommutes]
  rw [hcard]

/-- Z-type rows read only the X-content of an error. -/
theorem parity_ztype_xPart {n : Nat} (S E : ErrorVec n)
    (hS : ∀ q, S q = Pauli.Z ∨ S q = Pauli.I) :
    ErrorVec.parity S E = ErrorVec.parity S (xPartVec E) := by
  unfold ErrorVec.parity
  have hcard : (Finset.univ.filter fun i =>
        ErrorVec.Pauli.anticommutes (S i) (E i)).card
      = (Finset.univ.filter fun i =>
        ErrorVec.Pauli.anticommutes (S i) (xPartVec E i)).card := by
    apply Finset.card_equiv (Equiv.refl _)
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.refl_apply]
    rcases hS q with h | h <;> cases hE : E q <;>
      simp [h, hE, xPartVec, ErrorVec.Pauli.anticommutes]
  rw [hcard]

end QStab.QClifford.Compile
