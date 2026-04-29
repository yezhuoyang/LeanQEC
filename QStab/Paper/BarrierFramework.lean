import QStab.Invariant
import QStab.MultiStep
import QStab.Examples.SurfaceGeometry

/-!
# Logical barrier potential framework (paper §6.5)

Formalisation of the invariant framework introduced in §6.5 of the paper.
A *barrier function* β for logical class L is any nonneg-valued function
on Pauli errors satisfying the four properties of Definition
`def:GenericBarrier`: β(I) = d_L, β vanishes on L (one direction only),
the triangle inequality, and stabilizer-invariance.

Under an "L-aligned" schedule, the quantity Φ_L(σ) := β(Ẽ) +
(C_budget − C) is a QStab invariant lower-bounded by d_L, which directly
yields d_circ ≥ d.

The canonical barrier is μ_L(Ẽ) := min{|F| : Ẽ · F ∈ L} (Lemma
`lem:MuProperties`). Code-specific surrogates such as the perpendicular
spread `d − ω⊥^X` (surface code) and the column spread `d − ω_col`
(HGP code) are alternative instances tighter than μ_L for codes with
weight-≥ 2 hooks.

Goals of this file:
1. Define the abstract logical-class structure and the barrier-function
   interface (one-direction property (ii)) so the framework is code-agnostic.
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

/-- A *barrier function* `μ` for logical class `L`. Matches paper
    Definition `def:GenericBarrier` (§6.5).

    Property (ii) is the one-direction relaxation `E ∈ L → μ E = 0`,
    not the original biconditional `μ E = 0 ↔ E ∈ L`. The relaxation
    is essential for code-specific surrogates: e.g. the surface code's
    `β_Z̄ := max(0, d − ω⊥^X)` has `β_Z̄(E) = 0` whenever the
    perpendicular spread reaches `d`, even when `E` is not actually a
    logical operator. The full biconditional fails for such surrogates
    but is not required by either `barrierInvariant` or
    `distance_preservation` (only the `→` direction is used). -/
structure BarrierFunction (P : QECParams) (L : LogicalClass P) where
  /-- The barrier value on each error. -/
  mu : ErrorVec P.n → Nat
  /-- Property (i): μ_L(I) = d_L. -/
  mu_identity : mu (ErrorVec.identity P.n) = L.d_L
  /-- Property (ii) (one-direction): if `E` is in the logical class `L`,
      then the barrier vanishes. The converse is *not* required. -/
  mu_at_logical : ∀ E, L.contains E → mu E = 0
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
  have h_mu_zero : μ.mu s.E_tilde = 0 := μ.mu_at_logical s.E_tilde h_in_L
  unfold Phi at h_phi
  rw [h_mu_zero] at h_phi
  omega

/-! ## Clean-record framework

    The clean-record machinery generalises `L`-alignment: it permits a
    Type-II hook to drop the barrier by more than one, provided each
    extra unit creates a future syndrome flip the adversary must
    subsequently cancel. The framework tracks the unpaid syndrome flips
    via a *measurement debt* function `D : State → ℕ` and proves the
    invariant
    \[
        \mu_L(\Tilde E) + (C_{\text{budget}} - C) \geq d_L + D(\sigma)
    \]
    along every reachable state.

    The function `D` is supplied by the scheme verifier together with
    two axioms: it starts at zero, and it preserves the (Nat-truncated)
    quantity Φ_CR := μ + (C_b − C) − D along every transition. The
    first half of clean-record alignment (the per-back-action condition
    `Δμ_L ≤ 1 + |obs|`) discharges the preservation axiom for the
    Type-II case; the rest is per-transition bookkeeping the user
    proves about their concrete `D`. -/

/-- The local observation map: future syndrome coordinates a back-action
    `e_B` at coordinate `(x, y)` would flip if not subsequently masked. -/
def obsMap {P : QECParams} (e_B : ErrorVec P.n) (xy : Coord P) :
    Set (Coord P) :=
  { c | xy < c ∧ ErrorVec.parity (P.stabilizers c.x) e_B = true }

/-- A barrier function is *clean-record aligned* for `L` (relative to an
    abstract observation-count function `obsCount : ErrorVec → Coord → Nat`)
    if every back-action `e_B` at any coordinate satisfies
    Δμ_L(e_B) ≤ 1 + obsCount(e_B, (x, y)).
    Here `Δμ_L(e_B) := μ(E) − μ(e_B · E)` is the barrier drop, and
    `obsCount` represents `|obs_π(e_B, x, y)|`. We leave `obsCount` as a
    parameter so this file does not commit to a particular finiteness
    construction; concrete schemes supply their own count. -/
def IsCleanRecordAligned {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L)
    (obsCount : ErrorVec P.n → Coord P → Nat) : Prop :=
  ∀ (s : Fin P.numStab) (e_B : ErrorVec P.n),
    e_B ∈ P.backActionSet s →
    ∀ (E : ErrorVec P.n) (xy : Coord P),
      μ.mu (ErrorVec.mul e_B E) + 1 + obsCount e_B xy ≥ μ.mu E

/-- A *debt specification* for a barrier function `μ`: a state-valued
    debt function `D` together with two axioms that make the
    clean-record invariant work.

    The preservation axiom says that the (Nat-truncated) quantity
    `Φ_CR := μ + (C_budget − C) − D` is monotone non-decreasing along
    every Step transition; equivalently,
    `μ(E') + (C_budget − C') + D(s) ≥ μ(E) + (C_budget − C) + D(s')`,
    avoiding Nat truncation issues.

    Concrete schemes prove `preservation_step` by case analysis on
    the five transition rules: Type-0/I/III/Meas use that D doesn't grow
    enough to outpace the rise in `C_budget − C`; Type-II uses
    clean-record alignment to bound the increase in D against the drop
    in μ.

    The `D_done_clean` axiom captures that, at a done state with no
    unmasked syndromes, the debt is fully discharged. -/
structure DebtSpec {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L) where
  /-- The debt function. -/
  D : State P → Nat
  /-- D = 0 at the initial state. -/
  D_init : D (State.init P) = 0
  /-- The clean-record potential Φ_CR is monotone non-decreasing along
      Step transitions (stated without Nat subtraction). The
      `s.C ≤ P.C_budget` premise comes from the invariant we maintain. -/
  preservation_step : ∀ (s s' : State P),
    Step P (.active s) (.active s') → s.C ≤ P.C_budget →
    μ.mu s'.E_tilde + (P.C_budget - s'.C) + D s ≥
      μ.mu s.E_tilde + (P.C_budget - s.C) + D s'
  /-- C ≤ C_budget is preserved (used to manipulate Nat subtraction). -/
  C_le_budget_step : ∀ (s s' : State P),
    Step P (.active s) (.active s') → s.C ≤ P.C_budget → s'.C ≤ P.C_budget
  /-- At a done state with all syndrome bits zero, the debt is fully
      discharged. This is the clean-prefix premise lifted to the
      done state. -/
  D_done_clean : ∀ (s : State P),
    Run P (.done s) → (∀ x y, s.G x y = false) → D s = 0

/-- Predicate: the clean-record invariant holds at state `s`. -/
def CleanRecordInvPred {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L) (spec : DebtSpec μ) (s : State P) : Prop :=
  μ.mu s.E_tilde + (P.C_budget - s.C) ≥ L.d_L + spec.D s ∧ s.C ≤ P.C_budget

/-- **Theorem (paper Theorem~`thm:CleanRecordInv`).** The clean-record
    invariant `μ + (C_budget − C) ≥ d_L + D` holds at every reachable
    state, given the debt specification's preservation axioms. -/
def cleanRecordInvariant {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L) (spec : DebtSpec μ) : Invariant P where
  holds := CleanRecordInvPred μ spec
  holds_init := by
    refine ⟨?_, ?_⟩
    · -- μ(I) + 0 ≥ d_L + D(init), and D(init) = 0, μ(I) = d_L.
      have h_D := spec.D_init
      have h_mu : μ.mu (State.init P).E_tilde = L.d_L := by
        show μ.mu (ErrorVec.identity P.n) = L.d_L
        exact μ.mu_identity
      show μ.mu (State.init P).E_tilde + (P.C_budget - (State.init P).C) ≥
            L.d_L + spec.D (State.init P)
      rw [h_mu, h_D]
      show L.d_L + (P.C_budget - (State.init P).C) ≥ L.d_L + 0
      simp [State.init]
    · simp [State.init]
  preservation := by
    intro a b ⟨ha_phi, ha_C⟩ step
    have h_pres := spec.preservation_step a b step ha_C
    have h_C_b : b.C ≤ P.C_budget := spec.C_le_budget_step a b step ha_C
    refine ⟨?_, h_C_b⟩
    -- ha_phi : μ(E_a) + (C_b - a.C) ≥ d_L + D(a)
    -- h_pres : μ(E_b) + (C_b - b.C) + D(a) ≥ μ(E_a) + (C_b - a.C) + D(b)
    -- Combine: μ(E_b) + (C_b - b.C) + D(a) ≥ d_L + D(a) + D(b)
    --         hence μ(E_b) + (C_b - b.C) ≥ d_L + D(b)
    omega

/-- **Corollary (paper Cor.~`cor:RecordAware`).** Under a debt
    specification, every done-state execution with `G = 0` and
    accumulated error in some logical class `L` consumes at least
    `d_L` of the error budget. -/
theorem record_aware_distance_preservation
    {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L) (spec : DebtSpec μ)
    (s : State P) (hrun : Run P (.done s))
    (h_clean : ∀ x y, s.G x y = false)
    (h_in_L : L.contains s.E_tilde) :
    P.C_budget - s.C ≥ L.d_L := by
  have h_inv := (cleanRecordInvariant μ spec).holds_at_done s hrun
  obtain ⟨h_phi, _h_C⟩ := h_inv
  have h_D_zero : spec.D s = 0 := spec.D_done_clean s hrun h_clean
  have h_mu_zero : μ.mu s.E_tilde = 0 := μ.mu_at_logical s.E_tilde h_in_L
  rw [h_mu_zero, h_D_zero] at h_phi
  omega

/-! ## Recovering the L-alignment case

    `IsLAligned` is the special case of clean-record alignment with
    `obsCount = 0`. When the user's debt function `D` is identically
    zero, the clean-record invariant collapses to the ordinary barrier
    invariant of Theorem `barrierInvariant`. -/

/-- A trivial debt specification: `D ≡ 0`, with preservation following
    from L-alignment. This is what concrete L-aligned schemes (surface,
    HGP) instantiate. -/
def trivialDebtSpec {P : QECParams} {L : LogicalClass P}
    (μ : BarrierFunction P L) (h_aligned : IsLAligned μ) : DebtSpec μ where
  D := fun _ => 0
  D_init := rfl
  preservation_step := by
    intro a b step ha_C
    -- With D ≡ 0, this reduces to: μ(E_b) + (C_b - b.C) ≥ μ(E_a) + (C_b - a.C),
    -- which is `barrierInvariant`'s preservation step (combined with C_le_budget).
    -- We re-derive it here as a self-contained proof.
    cases step with
    | type0 _ i p hp hC =>
      show μ.mu (ErrorVec.update a.E_tilde i p) + (P.C_budget - (a.C - 1)) + 0 ≥
            μ.mu a.E_tilde + (P.C_budget - a.C) + 0
      rw [update_eq_mul_update_identity]
      have h_wt := weight_update_identity_le_one P.n i p
      have h_tri := μ.mu_triangle a.E_tilde
        (ErrorVec.update (ErrorVec.identity P.n) i p)
      omega
    | type1 _ i p hp mflip hC =>
      show μ.mu (ErrorVec.update a.E_tilde i p) + (P.C_budget - (a.C - 1)) + 0 ≥
            μ.mu a.E_tilde + (P.C_budget - a.C) + 0
      rw [update_eq_mul_update_identity]
      have h_wt := weight_update_identity_le_one P.n i p
      have h_tri := μ.mu_triangle a.E_tilde
        (ErrorVec.update (ErrorVec.identity P.n) i p)
      omega
    | type2 _ e he mflip hC =>
      show μ.mu (ErrorVec.mul e a.E_tilde) + (P.C_budget - (a.C - 1)) + 0 ≥
            μ.mu a.E_tilde + (P.C_budget - a.C) + 0
      have h_align := h_aligned a.coord.x e he a.E_tilde
      omega
    | type3 _ hC =>
      show μ.mu a.E_tilde + (P.C_budget - (a.C - 1)) + 0 ≥
            μ.mu a.E_tilde + (P.C_budget - a.C) + 0
      omega
    | measure _ nc hN =>
      show μ.mu (measureStep P a nc).E_tilde +
              (P.C_budget - (measureStep P a nc).C) + 0 ≥
            μ.mu a.E_tilde + (P.C_budget - a.C) + 0
      rw [measureStep_E_tilde, measureStep_C]
  C_le_budget_step := by
    intro a b step h_a
    cases step with
    | type0 _ i p hp hC =>
      show a.C - 1 ≤ P.C_budget
      omega
    | type1 _ i p hp mflip hC =>
      show a.C - 1 ≤ P.C_budget
      omega
    | type2 _ e he mflip hC =>
      show a.C - 1 ≤ P.C_budget
      omega
    | type3 _ hC =>
      show a.C - 1 ≤ P.C_budget
      omega
    | measure _ nc hN =>
      show (measureStep P a nc).C ≤ P.C_budget
      rw [measureStep_C]
      exact h_a
  D_done_clean := fun _ _ _ => rfl

end QStab.Paper.BarrierFramework
