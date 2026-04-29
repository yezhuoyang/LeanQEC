import QStab.Invariant
import QStab.MultiStep
import QStab.Examples.SurfaceGeometry

/-!
# Logical barrier potential framework (paper §6.5)

Formalisation of the invariant framework introduced in §6.5 of the paper:
the *logical barrier* μ_L(Ẽ) measures the Pauli distance from the
accumulated error Ẽ to the closest nontrivial logical operator of type L.
Under an "L-aligned" schedule, the quantity Φ_L(σ) := μ_L(Ẽ) +
(C_budget − C) is a QStab invariant lower-bounded by d_L, which directly
yields d_circ ≥ d.

Goals of this file:
1. Define the abstract logical-class structure and the barrier-function
   interface so the framework is code-agnostic.
2. Define L-alignment as a predicate on QStab programs.
3. Prove the main barrier invariant (Theorem `BarrierInv` in the paper)
   from the alignment hypothesis and the QStab transition rules. **Zero
   sorry in the proof.**
4. Derive the distance-preservation corollary at done states.

Definitions (clean-record alignment, measurement debt, the stronger
clean-record invariant) are stated; their full proofs are out of scope
for this file and are scheduled as a follow-up.
-/

namespace QStab.Paper.BarrierFramework

open QStab QECParams

/-! ## Logical classes and barrier functions -/

/-- A *logical class* is a set of Pauli error vectors that captures one
    coset of nontrivial logical operators of a given type (e.g.\ the
    coset $\overline{X}\cdot S$). -/
structure LogicalClass (P : QECParams) where
  /-- The membership predicate. -/
  contains : ErrorVec P.n → Prop
  /-- The minimum Pauli weight of any member. -/
  d_L : Nat
  /-- d_L is positive: the class contains no zero-weight elements (since
      L is disjoint from the stabilizer subgroup, and the only zero-weight
      Pauli vector is the identity, which is in S). -/
  d_L_pos : 0 < d_L
  /-- Every member has weight at least d_L. -/
  d_L_min : ∀ E, contains E → ErrorVec.weight E ≥ d_L

/-- A *barrier function* `μ` for logical class `L`. Bundles the
    quantity μ_L(Ẽ) := min{|F| : Ẽ · F ∈ L} together with the four
    properties that make it useful as an invariant.

    We do not construct `μ` from the `min` definition explicitly; we
    take it as an abstract input with its properties as axioms. A
    concrete instance is provided by code-specific witnesses (e.g.\ the
    perpendicular-spread function for the surface code). -/
structure BarrierFunction (P : QECParams) (L : LogicalClass P) where
  /-- The barrier value on each error. -/
  mu : ErrorVec P.n → Nat
  /-- Property (i): μ_L(I) = d_L. -/
  mu_identity : mu (ErrorVec.identity P.n) = L.d_L
  /-- Property (ii): μ_L(E) = 0 iff E ∈ L. -/
  mu_zero_iff : ∀ E, mu E = 0 ↔ L.contains E
  /-- Property (iii): triangle inequality.
      μ_L(E · F) ≥ μ_L(E) − |F|, equivalently μ_L(E · F) + |F| ≥ μ_L(E). -/
  mu_triangle : ∀ E F : ErrorVec P.n,
    mu (ErrorVec.mul F E) + ErrorVec.weight F ≥ mu E

/-! ## L-alignment of a schedule

    A schedule is L-aligned if every back-action error e_B in the
    back-action set of any gadget shifts the barrier by at most one. -/

/-- A barrier function `μ` is *L-aligned* if every back-action error in
    every gadget's back-action set drops μ by at most 1 from any input. -/
def IsLAligned {P : QECParams} {L : LogicalClass P} (μ : BarrierFunction P L) : Prop :=
  ∀ (s : Fin P.numStab) (e_B : ErrorVec P.n),
    e_B ∈ P.backActionSet s →
    ∀ (E : ErrorVec P.n),
      μ.mu (ErrorVec.mul e_B E) + 1 ≥ μ.mu E

/-! ## Helper: weight of `update identity i p` is at most 1 -/

private theorem weight_update_identity_le_one (n : Nat) (i : Fin n) (p : Pauli) :
    ErrorVec.weight (ErrorVec.update (ErrorVec.identity n) i p) ≤ 1 := by
  unfold ErrorVec.weight ErrorVec.update ErrorVec.identity
  have h_subset : (Finset.univ.filter
      fun j : Fin n => Function.update (fun _ => Pauli.I) i (Pauli.mul p Pauli.I) j ≠ Pauli.I) ⊆
        ({i} : Finset (Fin n)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_singleton]
    by_contra hji
    apply hj
    simp [Function.update, hji]
  calc (Finset.univ.filter
        fun j : Fin n => Function.update (fun _ => Pauli.I) i (Pauli.mul p Pauli.I) j ≠ Pauli.I).card
      ≤ ({i} : Finset (Fin n)).card := Finset.card_le_card h_subset
    _ = 1 := Finset.card_singleton i

/-! ## The logical barrier invariant (Theorem `BarrierInv` in §6.5) -/

/-- The barrier potential at a state: μ_L(Ẽ) + (C_budget − C). -/
def Phi {P : QECParams} {L : LogicalClass P} (μ : BarrierFunction P L) (s : State P) : Nat :=
  μ.mu s.E_tilde + (P.C_budget - s.C)

/-- The barrier invariant predicate: Φ_L(σ) ≥ d_L AND C ≤ C_budget.
    The second conjunct lets `omega` reason about `C_budget − C` arithmetic. -/
def BarrierInvPred {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L) (s : State P) : Prop :=
  Phi μ s ≥ L.d_L ∧ s.C ≤ P.C_budget

/-- Pauli I is a left identity for `Pauli.mul`. -/
private theorem Pauli_I_mul (p : Pauli) : Pauli.mul Pauli.I p = p := by
  cases p <;> rfl

/-- Pauli I is a right identity for `Pauli.mul`. -/
private theorem Pauli_mul_I (p : Pauli) : Pauli.mul p Pauli.I = p := by
  cases p <;> rfl

/-- A single-qubit `update` decomposes as multiplication by an
    `update identity i p` vector on the left. -/
private theorem update_eq_mul_update_identity (n : Nat) (E : ErrorVec n)
    (i : Fin n) (p : Pauli) :
    ErrorVec.update E i p =
      ErrorVec.mul (ErrorVec.update (ErrorVec.identity n) i p) E := by
  funext j
  unfold ErrorVec.update ErrorVec.mul ErrorVec.identity
  by_cases hij : j = i
  · subst hij
    simp only [Function.update_self]
    rw [Pauli_mul_I]
  · simp only [Function.update_of_ne hij]
    rw [Pauli_I_mul]

/-- **Main theorem (paper Theorem~`thm:BarrierInv`).** If the barrier
    function `μ` is L-aligned, then `Φ_L(σ) ≥ d_L` is an invariant. -/
def barrierInvariant {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L) (h_aligned : IsLAligned μ) : Invariant P where
  holds := BarrierInvPred μ
  -- Initial state: μ(I) = d_L, C = C_budget so RHS = 0.
  holds_init := by
    refine ⟨?_, ?_⟩
    · simp only [Phi, State.init, μ.mu_identity]
      omega
    · simp [State.init]
  -- Preservation: case analysis on the five transition rules.
  preservation := by
    intro a b ⟨ha_phi, ha_C⟩ step
    cases step with
    | type0 _ i p hp hC =>
      -- Type-0: E_tilde becomes update i p, C decreases by 1.
      refine ⟨?_, ?_⟩
      · -- Phi preservation: μ(update i p · E) + (C_budget - (C-1)) ≥ d_L.
        show μ.mu (ErrorVec.update a.E_tilde i p) + (P.C_budget - (a.C - 1)) ≥ L.d_L
        rw [update_eq_mul_update_identity]
        have h_wt := weight_update_identity_le_one P.n i p
        have h_tri := μ.mu_triangle a.E_tilde
          (ErrorVec.update (ErrorVec.identity P.n) i p)
        simp only [Phi] at ha_phi
        omega
      · -- C preservation: a.C - 1 ≤ C_budget.
        show a.C - 1 ≤ P.C_budget
        omega
    | type1 _ i p hp mflip hC =>
      refine ⟨?_, ?_⟩
      · show μ.mu (ErrorVec.update a.E_tilde i p) + (P.C_budget - (a.C - 1)) ≥ L.d_L
        rw [update_eq_mul_update_identity]
        have h_wt := weight_update_identity_le_one P.n i p
        have h_tri := μ.mu_triangle a.E_tilde
          (ErrorVec.update (ErrorVec.identity P.n) i p)
        simp only [Phi] at ha_phi
        omega
      · show a.C - 1 ≤ P.C_budget
        omega
    | type2 _ e he mflip hC =>
      refine ⟨?_, ?_⟩
      · show μ.mu (ErrorVec.mul e a.E_tilde) + (P.C_budget - (a.C - 1)) ≥ L.d_L
        have h_align := h_aligned a.coord.x e he a.E_tilde
        simp only [Phi] at ha_phi
        omega
      · show a.C - 1 ≤ P.C_budget
        omega
    | type3 _ hC =>
      refine ⟨?_, ?_⟩
      · show μ.mu a.E_tilde + (P.C_budget - (a.C - 1)) ≥ L.d_L
        simp only [Phi] at ha_phi
        omega
      · show a.C - 1 ≤ P.C_budget
        omega
    | measure _ nc hN =>
      refine ⟨?_, ?_⟩
      · show μ.mu (measureStep P a nc).E_tilde +
              (P.C_budget - (measureStep P a nc).C) ≥ L.d_L
        rw [measureStep_E_tilde, measureStep_C]
        simp only [Phi] at ha_phi
        exact ha_phi
      · show (measureStep P a nc).C ≤ P.C_budget
        rw [measureStep_C]
        exact ha_C

/-! ## Distance preservation corollary -/

/-- **Corollary `cor:LBDistance` (paper §6.5).** Under L-alignment, every
    state reachable from σ_init satisfies `μ(Ẽ) + (C_budget − C) ≥ d_L`.
    Specialised at done states with `Ẽ ∈ L` (i.e.\ `μ(Ẽ) = 0`), this
    yields `C_budget − C ≥ d_L`. -/
theorem distance_preservation
    {P : QECParams} {L : LogicalClass P} (μ : BarrierFunction P L)
    (h_aligned : IsLAligned μ)
    (s : State P) (hrun : Run P (.done s))
    (h_in_L : L.contains s.E_tilde) :
    P.C_budget - s.C ≥ L.d_L := by
  have h_inv : BarrierInvPred μ s :=
    (barrierInvariant μ h_aligned).holds_at_done s hrun
  obtain ⟨h_phi, _h_C⟩ := h_inv
  have h_mu_zero : μ.mu s.E_tilde = 0 := (μ.mu_zero_iff s.E_tilde).mpr h_in_L
  unfold Phi at h_phi
  rw [h_mu_zero] at h_phi
  omega

/-! ## Clean-record framework (definitions only)

    The clean-record machinery generalises L-alignment to permit hooks
    that drop the barrier by more than one, provided each extra unit
    creates a future syndrome flip the adversary must cancel. The full
    invariant proof requires tracking debt across rounds and is out of
    scope for this file. -/

/-- The local observation map: future syndrome coordinates a back-action
    `e_B` at coordinate `(x, y)` would flip if not subsequently masked. -/
def obsMap {P : QECParams} (e_B : ErrorVec P.n) (xy : Coord P) :
    Set (Coord P) :=
  { c | xy < c ∧ ErrorVec.parity (P.stabilizers c.x) e_B = true }

/-- A barrier function is *clean-record aligned* for L (relative to an
    abstract observation-count function `obsCount : ErrorVec → Coord → Nat`)
    if every back-action `e_B` at any coordinate satisfies
    Δμ_L(e_B) ≤ 1 + obsCount(e_B, (x, y)).
    Here `Δμ_L(e_B) := μ(E) − μ(e_B · E)` is the barrier drop, and
    `obsCount` represents `|obs_π(e_B, x, y)|`. We leave `obsCount` as a
    parameter so this file does not commit to a particular finiteness
    construction; instantiations supply a concrete count. -/
def IsCleanRecordAligned {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L)
    (obsCount : ErrorVec P.n → Coord P → Nat) : Prop :=
  ∀ (s : Fin P.numStab) (e_B : ErrorVec P.n),
    e_B ∈ P.backActionSet s →
    ∀ (E : ErrorVec P.n) (xy : Coord P),
      μ.mu (ErrorVec.mul e_B E) + 1 + obsCount e_B xy ≥ μ.mu E

end QStab.Paper.BarrierFramework
