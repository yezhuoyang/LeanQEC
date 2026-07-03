import QStab.QClifford.Compile.SurfaceRhoUnionSpec
import QStab.QClifford.Compile.HConjRelabel

/-!
# The ρ-image `hook_spread_bound` classification (F2, the StabAbsorb step)

The one genuinely-new proof of the X-floor transport: every `rhoPhi`-image of a
native NZ hook satisfies the `hook_spread_bound` obligation (row-X-count grows by
at most 1 after optimal stabilizer correction).  Per-kind classification, closed
by the **existing** absorption library (`hook_spread_bound_*`,
`SurfaceRowEquiv.lean`) — reused, not re-derived:

* X-stab hooks: the ρ-image is Z-type (`hadamardAction` swaps components), so the
  X-component pattern is untouched — `hook_spread_bound_Z_side`;
* Z-stab parent hooks: the ρ-image **is** the σρ-image generator
  (`mkSurfaceStabilizers_rho`, the F1 stab-row transport) —
  `hook_spread_bound_full_stab_absorb`;
* Z-stab proper suffixes: vertical/single-cell supports are column-confined, and ρ
  maps columns to rows, so the image is row-confined —
  `hook_spread_bound_xInRow_singleton`; the one 2-column case (bulkZ drop-1)
  absorbs its own parent (`hook_spread_bound_xInRows_via_absorption` with
  `T := rhoPhi (stab)`, residual = the single head cell) — exactly the validated
  single-generator absorption of the hook-set pin.

Assembled into `rhoNZSurfaceSpec` (the `NZSurfaceSpec` over the ρ-rotated union
machine) and `rhoSurfaceSpec` (retargeted to budget `d`).
-/

namespace QStab.QClifford.Compile

open QStab QStab.Examples QStab.Examples.SurfaceParametric QStab.Examples.SurfaceGeneral
open QHL.Source.Examples.SurfaceExactDistance QHL.Source.Examples.SurfaceUnionSpec

/-! ## Pauli micro-lemmas -/

/-- The Hadamard swap exchanges the X- and Z-component predicates. -/
private theorem hasXComponent_hadamardAction (p : Pauli) :
    Pauli.hasXComponent (hadamardAction p) = Pauli.hasZComponent p := by
  cases p <;> rfl

/-! ## `rhoPhi` transport lemmas -/

/-- `rhoPhi` is multiplicative (pointwise `hadamardAction` homomorphism). -/
theorem rhoPhi_mul (d : Nat) (hd : 0 < d) (E F : ErrorVec (d * d)) :
    rhoPhi d hd (ErrorVec.mul E F)
      = ErrorVec.mul (rhoPhi d hd E) (rhoPhi d hd F) := by
  funext q
  show hadamardAction (Pauli.mul (E _) (F _))
    = Pauli.mul (hadamardAction (E _)) (hadamardAction (F _))
  exact hadamardAction_pauliMul _ _

/-- **Column-to-row transport**: a column-confined support becomes a
row-confined X-component pattern under `rhoPhi` (ρ maps columns to rows). -/
theorem rhoPhi_col_to_row (d : Nat) (hd : 0 < d) (e : ErrorVec (d * d)) (c₀ : Nat)
    (hcol : ∀ p : Fin (d * d), e p ≠ Pauli.I → p.val % d = c₀) :
    ∀ q : Fin (d * d),
      Pauli.hasXComponent (rhoPhi d hd e q) = true → q.val / d = c₀ := by
  intro q hq
  have hne : e ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩ ≠ Pauli.I := by
    intro hI
    have hfalse : Pauli.hasXComponent (rhoPhi d hd e q) = false := by
      show Pauli.hasXComponent
        (hadamardAction (e ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd q.isLt⟩)) = false
    -- placeholder replaced below
      rw [hI]; rfl
    rw [hfalse] at hq
    exact Bool.noConfusion hq
  have h1 := hcol _ hne
  rwa [rhoInvNat_mod d q.val hd q.isLt] at h1

/-! ## Positive `suffixHook` evaluation (key membership ⇒ value) -/

private theorem lookup_map_const_snd_of_mem {α : Type _} (l : List α) (f : α → Nat)
    (cst : Pauli) (n : Nat) (h : ∃ a ∈ l, n = f a) :
    (l.map (fun a => (f a, cst))).lookup n = some cst := by
  induction l with
  | nil =>
      obtain ⟨a, ha, _⟩ := h
      exact absurd ha (List.not_mem_nil)
  | cons a as ih =>
      simp only [List.map_cons, List.lookup]
      by_cases hbeq : (n == f a) = true
      · rw [hbeq]
      · rw [Bool.not_eq_true] at hbeq
        rw [hbeq]
        simp only [cond_false]
        apply ih
        obtain ⟨x, hx, hnx⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx'
        · exfalso
          have hne : n ≠ f x := by
            intro he
            rw [he] at hbeq
            simp at hbeq
          exact hne hnx
        · exact ⟨x, hx', hnx⟩

/-- If `q.val` is a key of the `j`-th suffix, the hook value there is the kind
Pauli. -/
private theorem suffixHook_eq_kindPauli_of_key (d : Nat) (k : StabKind) (j : Nat)
    (q : Fin (d * d))
    (h : ∃ rc ∈ (kindOrderRC d k).drop j, q.val = gridIdx d rc.1 rc.2) :
    suffixHook d k j q = kindPauli k := by
  unfold suffixHook ofList suffixPairs
  rw [lookup_map_const_snd_of_mem _ _ _ _ h]
  rfl

/-! ## `gridIdx` coordinate recovery -/

private theorem gridIdx_div (d a bb : Nat) (hd : 0 < d) (hbb : bb < d) :
    gridIdx d a bb / d = a := by
  show (d * a + bb) / d = a
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hbb, Nat.add_zero]

private theorem gridIdx_mod (d a bb : Nat) (hbb : bb < d) :
    gridIdx d a bb % d = bb := by
  show (d * a + bb) % d = bb
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hbb]

/-! ## `classifyStab` inversions (Z-kinds) -/

private theorem classify_bulkZ_inv (d k : Nat) (hd : 1 < d)
    (r c : Nat) (hkind : classifyStab d k = .bulkZ r c) :
    k = bulkIdx d r c ∧ r < d - 1 ∧ c < d - 1 ∧ (r + c) % 2 = 0 := by
  unfold classifyStab at hkind
  by_cases h1 : k < (d - 1) * (d - 1)
  · rw [if_pos h1] at hkind
    by_cases hp : (k / (d - 1) + k % (d - 1)) % 2 = 0
    · rw [if_pos hp] at hkind
      injection hkind with h2 h3
      subst h2; subst h3
      refine ⟨?_, Nat.div_lt_of_lt_mul h1, Nat.mod_lt _ (by omega), hp⟩
      show k = k / (d - 1) * (d - 1) + k % (d - 1)
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod k (d - 1)).symm
    · rw [if_neg hp] at hkind
      exact nomatch hkind
  · rw [if_neg h1] at hkind
    by_cases h2 : k - (d - 1) * (d - 1) < (d - 1) / 2
    · rw [if_pos h2] at hkind; exact nomatch hkind
    · rw [if_neg h2] at hkind
      by_cases h3 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · rw [if_pos h3] at hkind; exact nomatch hkind
      · rw [if_neg h3] at hkind
        by_cases h4 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · rw [if_pos h4] at hkind; exact nomatch hkind
        · rw [if_neg h4] at hkind; exact nomatch hkind

private theorem classify_rightZ_inv (d k : Nat) (hd : 1 < d)
    (b : Nat) (hkind : classifyStab d k = .rightZ b) :
    k = rightZIdx d b ∧ b < (d - 1) / 2 := by
  unfold classifyStab at hkind
  by_cases h1 : k < (d - 1) * (d - 1)
  · rw [if_pos h1] at hkind
    by_cases hp : (k / (d - 1) + k % (d - 1)) % 2 = 0
    · rw [if_pos hp] at hkind; exact nomatch hkind
    · rw [if_neg hp] at hkind; exact nomatch hkind
  · rw [if_neg h1] at hkind
    by_cases h2 : k - (d - 1) * (d - 1) < (d - 1) / 2
    · rw [if_pos h2] at hkind; exact nomatch hkind
    · rw [if_neg h2] at hkind
      by_cases h3 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · rw [if_pos h3] at hkind
        injection hkind with hb
        constructor
        · show k = (d - 1) * (d - 1) + (d - 1) / 2 + b
          omega
        · omega
      · rw [if_neg h3] at hkind
        by_cases h4 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · rw [if_pos h4] at hkind; exact nomatch hkind
        · rw [if_neg h4] at hkind; exact nomatch hkind

private theorem classify_leftZ_inv (d k : Nat) (hd : 1 < d)
    (b : Nat) (hkind : classifyStab d k = .leftZ b) :
    k = leftZIdx d b ∧ b < (d - 1) / 2 := by
  unfold classifyStab at hkind
  by_cases h1 : k < (d - 1) * (d - 1)
  · rw [if_pos h1] at hkind
    by_cases hp : (k / (d - 1) + k % (d - 1)) % 2 = 0
    · rw [if_pos hp] at hkind; exact nomatch hkind
    · rw [if_neg hp] at hkind; exact nomatch hkind
  · rw [if_neg h1] at hkind
    by_cases h2 : k - (d - 1) * (d - 1) < (d - 1) / 2
    · rw [if_pos h2] at hkind; exact nomatch hkind
    · rw [if_neg h2] at hkind
      by_cases h3 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · rw [if_pos h3] at hkind; exact nomatch hkind
      · rw [if_neg h3] at hkind
        by_cases h4 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · rw [if_pos h4] at hkind
          injection hkind with hb
          constructor
          · show k = (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b
            omega
          · omega
        · rw [if_neg h4] at hkind; exact nomatch hkind

/-! ## The bulkZ drop-1 residual: parent product is head-column-confined -/

/-- Multiplying the bulkZ parent into its drop-1 suffix hook leaves support only
at the head cell `(r, c)` — column `c`. -/
private theorem mul_stab_suffixZ1_ne_I_col (d : Nat) (hd0 : 0 < d) (hd : 1 < d)
    (r c : Nat) (hr : r < d - 1) (hc : c < d - 1) (hpar : (r + c) % 2 = 0)
    (hlt : bulkIdx d r c < numStabFormula d)
    (p : Fin (d * d))
    (hne : ErrorVec.mul (mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, hlt⟩)
        (suffixHook d (.bulkZ r c) 1) p ≠ Pauli.I) :
    p.val % d = c := by
  have hstab : mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, hlt⟩ p
      = if (p.val / d = r ∨ p.val / d = r + 1) ∧ (p.val % d = c ∨ p.val % d = c + 1)
        then Pauli.Z else Pauli.I :=
    decode_bulkZIdx d r c (p.val / d) (p.val % d) hd hr hc hpar
  have hdrop : (kindOrderRC d (.bulkZ r c)).drop 1
      = [(r + 1, c), (r, c + 1), (r + 1, c + 1)] := rfl
  by_cases hcol : p.val % d = c
  · exact hcol
  exfalso
  apply hne
  show Pauli.mul (mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, hlt⟩ p)
      (suffixHook d (.bulkZ r c) 1 p) = Pauli.I
  by_cases hcol1 : p.val % d = c + 1
  · by_cases hrow : p.val / d = r ∨ p.val / d = r + 1
    · -- both factors are Z at this cell
      have hsfx : suffixHook d (.bulkZ r c) 1 p = kindPauli (.bulkZ r c) := by
        apply suffixHook_eq_kindPauli_of_key
        have hpv := Nat.div_add_mod p.val d
        rcases hrow with h | h
        · refine ⟨(r, c + 1), by rw [hdrop]; simp, ?_⟩
          show p.val = d * r + (c + 1)
          rw [h, hcol1] at hpv
          exact hpv.symm
        · refine ⟨(r + 1, c + 1), by rw [hdrop]; simp, ?_⟩
          show p.val = d * (r + 1) + (c + 1)
          rw [h, hcol1] at hpv
          exact hpv.symm
      rw [hstab, if_pos ⟨hrow, Or.inr hcol1⟩, hsfx]
      rfl
    · -- both factors are I at this cell
      have hsfx : suffixHook d (.bulkZ r c) 1 p = Pauli.I := by
        apply suffixHook_eq_I_of_idx_not_key
        intro rc hrc hpe
        rw [hdrop] at hrc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrc
        apply hrow
        rcases hrc with rfl | rfl | rfl
        · right
          rw [hpe]
          exact gridIdx_div d (r + 1) c hd0 (by omega)
        · left
          rw [hpe]
          exact gridIdx_div d r (c + 1) hd0 (by omega)
        · right
          rw [hpe]
          exact gridIdx_div d (r + 1) (c + 1) hd0 (by omega)
      rw [hstab, if_neg (fun hh => hrow hh.1), hsfx]
      rfl
  · -- column outside {c, c+1}: both factors are I
    have hsfx : suffixHook d (.bulkZ r c) 1 p = Pauli.I := by
      apply suffixHook_eq_I_of_idx_not_key
      intro rc hrc hpe
      rw [hdrop] at hrc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrc
      rcases hrc with rfl | rfl | rfl
      · exact hcol (by rw [hpe]; exact gridIdx_mod d (r + 1) c (by omega))
      · exact hcol1 (by rw [hpe]; exact gridIdx_mod d r (c + 1) (by omega))
      · exact hcol1 (by rw [hpe]; exact gridIdx_mod d (r + 1) (c + 1) (by omega))
    have hstabI : mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, hlt⟩ p = Pauli.I := by
      rw [hstab, if_neg]
      intro hh
      rcases hh.2 with h | h
      · exact hcol h
      · exact hcol1 h
    rw [hstabI, hsfx]
    rfl

/-! ## ★ The ρ-image `hook_spread_bound` (the StabAbsorb classification) ★ -/

/-- **The ρ-image spread bound**: every `rhoPhi`-image of a native NZ hook meets
the `hook_spread_bound` obligation.  Per-kind classification closed by the
existing absorption library; the only 2-column case (bulkZ drop-1) absorbs a
single generator — its ρ-transported parent — leaving a single-cell residual. -/
theorem hook_spread_bound_rhoImage
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d))
    (e₀ : ErrorVec (d * d))
    (he : e₀ ∈ mkSurfaceHookErrors d (by omega) hodd s)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul (rhoPhi d (by omega) e₀) E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  rcases isXStab_or_isZStab d s with hX | hZ
  · -- X-stab hooks: the ρ-image is Z-type — X-pattern untouched
    refine hook_spread_bound_Z_side d hd0 hodd s (rhoPhi d hd0 e₀) ?_ E S_wit hS
    intro q
    show Pauli.hasXComponent (hadamardAction
      (e₀ ⟨rhoInvNat d q.val, rhoInvNat_lt d q.val hd0 q.isLt⟩)) = false
    rw [hasXComponent_hadamardAction]
    exact mkSurfaceHookErrors_X_no_Z d hd0 hodd s hX e₀ he _
  · unfold mkSurfaceHookErrors at he
    rw [Finset.mem_union] at he
    rcases he with he_suff | he_full
    · rw [Finset.mem_image] at he_suff
      obtain ⟨j, hj_mem, hj_eq⟩ := he_suff
      cases hkind : classifyStab d s.val with
      | bulkX r c =>
          exfalso
          have hx : stabType d s.val = Pauli.X := by
            rw [← kindPauli_eq_stabType d s.val, hkind]; rfl
          rw [show stabType d s.val = Pauli.Z from hZ] at hx
          exact nomatch hx
      | topX b =>
          exfalso
          have hx : stabType d s.val = Pauli.X := by
            rw [← kindPauli_eq_stabType d s.val, hkind]; rfl
          rw [show stabType d s.val = Pauli.Z from hZ] at hx
          exact nomatch hx
      | bottomX b =>
          exfalso
          have hx : stabType d s.val = Pauli.X := by
            rw [← kindPauli_eq_stabType d s.val, hkind]; rfl
          rw [show stabType d s.val = Pauli.Z from hZ] at hx
          exact nomatch hx
      | bulkZ r c =>
          rw [hkind] at hj_eq hj_mem
          subst hj_eq
          obtain ⟨hval, hr, hc, hpar⟩ := classify_bulkZ_inv d s.val hd1 r c hkind
          have hj_range : j = 1 ∨ j = 2 ∨ j = 3 := by
            have h_eq : suffixIndices d (.bulkZ r c) = [1, 2, 3] := rfl
            rw [h_eq, List.mem_toFinset] at hj_mem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_mem
            exact hj_mem
          rcases hj_range with rfl | rfl | rfl
          · -- drop-1: absorb the ρ-transported parent, residual = head cell (row c)
            refine hook_spread_bound_xInRows_via_absorption d hd0 hodd s
              (rhoPhi d hd0 (suffixHook d (.bulkZ r c) 1))
              (rhoPhi d hd0 (mkSurfaceStabilizers d hd0 s))
              ?_ ⟨c, by omega⟩ ?_ E S_wit hS
            · rw [mkSurfaceStabilizers_rho d hd0 hd1 hodd s]
              exact InStab.gen _
            · intro q hq
              rw [show ErrorVec.mul (rhoPhi d hd0 (mkSurfaceStabilizers d hd0 s))
                    (rhoPhi d hd0 (suffixHook d (.bulkZ r c) 1))
                  = rhoPhi d hd0 (ErrorVec.mul (mkSurfaceStabilizers d hd0 s)
                      (suffixHook d (.bulkZ r c) 1))
                from (rhoPhi_mul d hd0 _ _).symm] at hq
              refine rhoPhi_col_to_row d hd0 _ c ?_ q hq
              intro p hp
              have hs_eq : s = ⟨bulkIdx d r c, hval ▸ s.isLt⟩ := Fin.ext hval
              rw [hs_eq] at hp
              exact mul_stab_suffixZ1_ne_I_col d hd0 hd1 r c hr hc hpar _ p hp
          · -- drop-2: single column c+1 → single image row c+1
            refine hook_spread_bound_xInRow_singleton d hd0 hodd
              ⟨c + 1, by omega⟩ s _ ?_ E S_wit hS
            intro q hq
            refine rhoPhi_col_to_row d hd0 _ (c + 1) ?_ q hq
            intro p hp
            obtain ⟨rc, hrc, hpe⟩ :=
              suffixHook_support_implies_kindOrderRC d hd0 _ 2 p hp
            have hdrop : (kindOrderRC d (.bulkZ r c)).drop 2
                = [(r, c + 1), (r + 1, c + 1)] := rfl
            rw [hdrop] at hrc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hrc
            rcases hrc with rfl | rfl
            · rw [hpe]; exact gridIdx_mod d r (c + 1) (by omega)
            · rw [hpe]; exact gridIdx_mod d (r + 1) (c + 1) (by omega)
          · -- drop-3: single cell (r+1, c+1) → single image row c+1
            refine hook_spread_bound_xInRow_singleton d hd0 hodd
              ⟨c + 1, by omega⟩ s _ ?_ E S_wit hS
            intro q hq
            refine rhoPhi_col_to_row d hd0 _ (c + 1) ?_ q hq
            intro p hp
            obtain ⟨rc, hrc, hpe⟩ :=
              suffixHook_support_implies_kindOrderRC d hd0 _ 3 p hp
            have hdrop : (kindOrderRC d (.bulkZ r c)).drop 3
                = [(r + 1, c + 1)] := rfl
            rw [hdrop] at hrc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hrc
            subst hrc
            rw [hpe]; exact gridIdx_mod d (r + 1) (c + 1) (by omega)
      | rightZ b =>
          rw [hkind] at hj_eq hj_mem
          subst hj_eq
          obtain ⟨hval, hb⟩ := classify_rightZ_inv d s.val hd1 b hkind
          have hj1 : j = 1 := by
            have h_eq : suffixIndices d (.rightZ b) = [1] := rfl
            rw [h_eq, List.mem_toFinset] at hj_mem
            simpa using hj_mem
          subst hj1
          refine hook_spread_bound_xInRow_singleton d hd0 hodd
            ⟨d - 1, by omega⟩ s _ ?_ E S_wit hS
          intro q hq
          refine rhoPhi_col_to_row d hd0 _ (d - 1) ?_ q hq
          intro p hp
          obtain ⟨rc, hrc, hpe⟩ :=
            suffixHook_support_implies_kindOrderRC d hd0 _ 1 p hp
          have hdrop : (kindOrderRC d (.rightZ b)).drop 1
              = [(2 * b + 1, d - 1)] := rfl
          rw [hdrop] at hrc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrc
          subst hrc
          rw [hpe]; exact gridIdx_mod d (2 * b + 1) (d - 1) (by omega)
      | leftZ b =>
          rw [hkind] at hj_eq hj_mem
          subst hj_eq
          obtain ⟨hval, hb⟩ := classify_leftZ_inv d s.val hd1 b hkind
          have hj1 : j = 1 := by
            have h_eq : suffixIndices d (.leftZ b) = [1] := rfl
            rw [h_eq, List.mem_toFinset] at hj_mem
            simpa using hj_mem
          subst hj1
          refine hook_spread_bound_xInRow_singleton d hd0 hodd
            ⟨0, by omega⟩ s _ ?_ E S_wit hS
          intro q hq
          refine rhoPhi_col_to_row d hd0 _ 0 ?_ q hq
          intro p hp
          obtain ⟨rc, hrc, hpe⟩ :=
            suffixHook_support_implies_kindOrderRC d hd0 _ 1 p hp
          have hdrop : (kindOrderRC d (.leftZ b)).drop 1
              = [(2 * b + 2, 0)] := rfl
          rw [hdrop] at hrc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrc
          subst hrc
          rw [hpe]; exact gridIdx_mod d (2 * b + 2) 0 (by omega)
    · -- parent stabilizer: the ρ-image is the σρ generator
      rw [Finset.mem_singleton] at he_full
      subst he_full
      rw [mkSurfaceStabilizers_rho d hd0 hd1 hodd s]
      exact hook_spread_bound_fullStab_dispatch d hd0 hodd _ E S_wit hS

/-! ## The `NZSurfaceSpec` over the ρ-rotated union machine -/

/-- The NZ Surface spec over the ρ-rotated union machine (mirror of
`unionNZSurfaceSpec` field-for-field; `hook_spread_bound` splits the rotated
union: native hooks delegate to the landed parametric bound, ρ-images to
`hook_spread_bound_rhoImage`). -/
def rhoNZSurfaceSpec (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : NZSurfaceSpec d where
  params := mkSurfaceQECParamsRho d (by omega) hodd
  hn := rfl
  hd_pos := by omega
  logicalZ := (mkSurfaceNZSurfaceSpec d hd3 hodd).logicalZ
  rowCut := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut
  rowCut_zero := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut_zero
  rowCut_succ := fun i hi => by
    obtain ⟨S, hS, hZ, hrow⟩ := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut_succ i hi
    exact ⟨S, inStabRho hS, hZ, hrow⟩
  logicalZ_normalizer := (mkSurfaceNZSurfaceSpec d hd3 hodd).logicalZ_normalizer
  rowCut_spec := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut_spec
  stab_commute := (mkSurfaceNZSurfaceSpec d hd3 hodd).stab_commute
  hook_spread_bound := fun _ e_B he E S_wit hS => by
    rcases he with ⟨s, hs⟩ | ⟨s, e₀, he₀, rfl⟩
    · obtain ⟨S', hS', hcard⟩ :=
        (mkSurfaceNZSurfaceSpec d hd3 hodd).hook_spread_bound s e_B hs E S_wit
          (inStabRestoreRho hS)
      exact ⟨S', inStabRho hS', hcard⟩
    · obtain ⟨S', hS', hcard⟩ :=
        hook_spread_bound_rhoImage d hd3 hodd s e₀ he₀ E S_wit (inStabRestoreRho hS)
      exact ⟨S', inStabRho hS', hcard⟩

/-- The ρ-rotated union machine retargeted to budget exactly `d`. -/
def rhoSurfaceSpec (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : NZSurfaceSpec d :=
  retargetSurfaceSpec (rhoNZSurfaceSpec d hd3 hodd) d

end QStab.QClifford.Compile
