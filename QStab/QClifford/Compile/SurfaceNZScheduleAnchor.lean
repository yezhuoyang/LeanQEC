import QStab.QClifford.Compile.SurfaceCodeAnchor
import QStab.QClifford.Compile.SurfaceHValid

/-!
# NZ-schedule anchor: the schedule is determined by `Surface.code` + the generic NZ rule

`SurfaceCodeAnchor.lean` proved the machine's stabilizer *content* is the certified
evaluation of the recursive object program `Surface.code`.  This file removes the
remaining definitional freedom from the *schedule*: `nzSchedule` (built from the
meta-level `kindOrderRC`) is proven to be **the** NZ ordering of that certified
content, where the NZ rule is one code-independent scheme definition:

* traverse an X-type check's support in **row-major** order (the "Z" shape),
* traverse a Z-type check's support in **column-major** order (the "N" shape).

`IsNZScheduleOf` pins the four defining properties — support-exactness against the
code content, kind-faithfulness, duplicate-freeness, and the NZ ordering.  A
duplicate-free, support-exact, key-sorted enumeration of a finite support is unique,
so once all four fields are proven the schedule has no surface-specific freedom left:
it is a function of `Surface.code` and the scheme rule alone.
-/

namespace QStab.QClifford.Compile

open QStab QStab.Examples.SurfaceParametric
open QStab.QClifford.PCC.SurfaceNZ
open QHL.CodeLang.Surface.Verify

/-- Column-major (transposed row-major) qubit key at distance `d`. -/
def colMajorKey (d q : Nat) : Nat := (q % d) * d + q / d

/-- The generic NZ ordering key: row-major (the qubit index itself) for X-type
schedules, column-major for Z-type.  A scheme definition — code-independent. -/
def nzKey (d : Nat) (kp : Pauli) (q : Nat) : Nat :=
  if kp = Pauli.X then q else colMajorKey d q

/-- **What "the NZ schedule of code content" means.**  Support-exact,
kind-faithful, duplicate-free, and NZ-ordered.  These four properties determine
the schedule uniquely from the content. -/
structure IsNZScheduleOf (d : Nat) (content : Nat → Pauli)
    (sched : RuleSchedule (d * d)) : Prop where
  support_iff : ∀ q : Fin (d * d),
    (∃ s ∈ sched.slots, s.qubit = q) ↔ content q.val ≠ Pauli.I
  kind_faithful : ∀ s ∈ sched.slots, s.kind.toPauli = content s.qubit.val
  nodup : (sched.slots.map (·.qubit)).Nodup
  nz_ordered : (sched.slots.map (fun s => nzKey d (scheduleKind sched) s.qubit.val)).Pairwise (· < ·)

/-- The surface stabilizer kinds are never `I`. -/
theorem kindPauli_ne_I (k : StabKind) : kindPauli k ≠ Pauli.I := by
  cases k <;> simp [kindPauli]

/-- **Support-exactness** of the NZ schedule against the certified code content:
the schedule visits exactly the support of `surfaceCellPauli d i` — which is the
proven evaluation of `Surface.code` (`recCall_eval_surfaceCellPauli`). -/
theorem nzSchedule_support_iff (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) (q : Fin (d * d)) :
    (∃ s ∈ (nzSchedule d hd i).slots, s.qubit = q) ↔
      surfaceCellPauli d i.val q.val ≠ Pauli.I := by
  have hanchor : mkSurfaceStabilizers d hd i q = surfaceCellPauli d i.val q.val :=
    mkSurfaceStabilizers_eq_surfaceCellPauli d hd (by omega) i q
  have hany := nzSchedule_drop_any_iff d hd hd3 hodd i 0 q
  simp only [List.drop_zero] at hany
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hmem : (nzSchedule d hd i).slots.any
        (fun slot => decide (slot.qubit = s.qubit)) = true :=
      List.any_eq_true.mpr ⟨s, hs, by simp⟩
    obtain ⟨rc, hrc, hval⟩ := hany.mp hmem
    obtain ⟨h1, h2⟩ := kindOrderRC_classify_in_bounds d hd3 hodd i rc hrc
    have hdiv : s.qubit.val / d = rc.1 := by
      rw [hval]
      show (d * rc.1 + rc.2) / d = rc.1
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt h2]
      omega
    have hmod : s.qubit.val % d = rc.2 := by
      rw [hval]
      show (d * rc.1 + rc.2) % d = rc.2
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt h2
    rw [← hanchor]
    show decodeStabPauliAt d i.val (s.qubit.val / d) (s.qubit.val % d) ≠ Pauli.I
    rw [hdiv, hmod,
      decode_eq_kindPauli_of_mem_kindOrderRC d i.val rc.1 rc.2 (by simpa using hrc)]
    exact kindPauli_ne_I _
  · intro hne
    have hne' : decodeStabPauliAt d i.val (q.val / d) (q.val % d) ≠ Pauli.I := by
      rw [show decodeStabPauliAt d i.val (q.val / d) (q.val % d) =
          mkSurfaceStabilizers d hd i q from rfl, hanchor]
      exact hne
    have hmem := decode_ne_I_implies_in_kindOrderRC d i.val (q.val / d) (q.val % d) hne'
    have hq_recon : q.val = gridIdx d (q.val / d) (q.val % d) :=
      (Nat.div_add_mod q.val d).symm
    have hex : ((nzSchedule d hd i).slots).any
        (fun slot => decide (slot.qubit = q)) = true :=
      hany.mpr ⟨(q.val / d, q.val % d), by simpa using hmem, hq_recon⟩
    obtain ⟨s, hs, hsq⟩ := List.any_eq_true.mp hex
    exact ⟨s, hs, by simpa using hsq⟩

/-- **Kind-faithfulness** of the NZ schedule against the certified code content:
every slot's CSS kind is the content's Pauli at the visited qubit. -/
theorem nzSchedule_kind_faithful (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (i : Fin (numStabFormula d)) :
    ∀ s ∈ (nzSchedule d hd i).slots,
      s.kind.toPauli = surfaceCellPauli d i.val s.qubit.val := by
  intro s hs
  rw [nzSchedule_kind_uniform d hd i s hs, kindXZ_toPauli_eq_kindPauli]
  have hmem : (nzSchedule d hd i).slots.any
      (fun slot => decide (slot.qubit = s.qubit)) = true :=
    List.any_eq_true.mpr ⟨s, hs, by simp⟩
  have hany := nzSchedule_drop_any_iff d hd hd3 hodd i 0 s.qubit
  simp only [List.drop_zero] at hany
  obtain ⟨rc, hrc, hval⟩ := hany.mp hmem
  obtain ⟨h1, h2⟩ := kindOrderRC_classify_in_bounds d hd3 hodd i rc hrc
  have hanchor : mkSurfaceStabilizers d hd i s.qubit =
      surfaceCellPauli d i.val s.qubit.val :=
    mkSurfaceStabilizers_eq_surfaceCellPauli d hd (by omega) i s.qubit
  have hdiv : s.qubit.val / d = rc.1 := by
    rw [hval]
    show (d * rc.1 + rc.2) / d = rc.1
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt h2]
    omega
  have hmod : s.qubit.val % d = rc.2 := by
    rw [hval]
    show (d * rc.1 + rc.2) % d = rc.2
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt h2
  rw [← hanchor]
  show kindPauli (classifyStab d i.val) =
    decodeStabPauliAt d i.val (s.qubit.val / d) (s.qubit.val % d)
  rw [hdiv, hmod,
    decode_eq_kindPauli_of_mem_kindOrderRC d i.val rc.1 rc.2 (by simpa using hrc)]

/-! ## S4a: the NZ ordering field

The transposed-index computation is the one genuinely new arithmetic step; the row/column
strict-order helpers are packaged so `omega` never sees a product of variables. -/

/-- **The transposed-index computation.**  The column-major key of a row-major grid index
`d*r + c` (in range) is `c*d + r` — the "N" traversal reads columns first. -/
theorem colMajorKey_rowIdx (d r c : Nat) (hd : 0 < d) (hc : c < d) :
    colMajorKey d (d * r + c) = c * d + r := by
  unfold colMajorKey
  have h1 : (d * r + c) % d = c := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hc
  have h2 : (d * r + c) / d = r := by rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hc]; omega
  rw [h1, h2]

/-- The column-major key of a scheduled qubit `gridFin (r,c)` (in range) is `c*d + r`. -/
private lemma colMajorKey_gridFin (d : Nat) (hd : 0 < d) (r c : Nat) (hr : r < d) (hc : c < d) :
    colMajorKey d (gridFin d hd (r, c)).val = c * d + r := by
  rw [gridFin_val_of_lt d hd hr hc, colMajorKey_rowIdx d r c hd hc]

/-- **The NZ ordering field.**  The schedule keys — row-major (`X`-type, the "Z" shape) or
column-major (`Z`-type, the "N" shape) — are strictly increasing.  Each kind's key list is
an explicit `≤4`-element list; the strict order follows from the transposed-index
computation plus one product-expansion `have` (so `omega` never reasons about the product
itself, only about its expanded form). -/
theorem nzSchedule_nz_ordered (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) :
    ((nzSchedule d hd i).slots.map
        (fun s => nzKey d (scheduleKind (nzSchedule d hd i)) s.qubit.val)).Pairwise (· < ·) := by
  rw [scheduleKind_nzSchedule d hd i]
  have hslots : (nzSchedule d hd i).slots.map
      (fun s => nzKey d (kindPauli (classifyStab d i.val)) s.qubit.val) =
      (kindOrderRC d (classifyStab d i.val)).map
        (fun rc => nzKey d (kindPauli (classifyStab d i.val)) (gridFin d hd rc).val) := by
    simp [nzSchedule, RuleSchedule.uniform, List.map_map, Function.comp]
  rw [hslots]
  have hb := kindOrderRC_classify_in_bounds d hd3 hodd i
  cases hcl : classifyStab d i.val with
  | bulkZ r c =>
      rw [hcl] at hb
      obtain ⟨hr1, hc1⟩ := hb (r + 1, c + 1) (by simp [kindOrderRC])
      have hexp : (c + 1) * d = c * d + d := by ring
      show ([colMajorKey d (gridFin d hd (r, c)).val,
        colMajorKey d (gridFin d hd (r + 1, c)).val,
        colMajorKey d (gridFin d hd (r, c + 1)).val,
        colMajorKey d (gridFin d hd (r + 1, c + 1)).val]).Pairwise (· < ·)
      rw [colMajorKey_gridFin d hd r c (by omega) (by omega),
          colMajorKey_gridFin d hd (r + 1) c (by omega) (by omega),
          colMajorKey_gridFin d hd r (c + 1) (by omega) (by omega),
          colMajorKey_gridFin d hd (r + 1) (c + 1) (by omega) (by omega)]
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        List.Pairwise.nil, or_false, forall_eq_or_imp, forall_eq, and_true, IsEmpty.forall_iff,
        forall_const]
      omega
  | bulkX r c =>
      rw [hcl] at hb
      obtain ⟨hr1, hc1⟩ := hb (r + 1, c + 1) (by simp [kindOrderRC])
      have hexp : d * (r + 1) = d * r + d := by ring
      show ([(gridFin d hd (r, c)).val, (gridFin d hd (r, c + 1)).val,
        (gridFin d hd (r + 1, c)).val, (gridFin d hd (r + 1, c + 1)).val]).Pairwise (· < ·)
      rw [gridFin_val_of_lt d hd (show r < d by omega) (show c < d by omega),
          gridFin_val_of_lt d hd (show r < d by omega) (show c + 1 < d by omega),
          gridFin_val_of_lt d hd (show r + 1 < d by omega) (show c < d by omega),
          gridFin_val_of_lt d hd (show r + 1 < d by omega) (show c + 1 < d by omega)]
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        List.Pairwise.nil, or_false, forall_eq_or_imp, forall_eq, and_true, IsEmpty.forall_iff,
        forall_const]
      omega
  | topX b =>
      rw [hcl] at hb
      obtain ⟨-, hb2⟩ := hb (0, 2 * b + 1) (by simp [kindOrderRC])
      show ([(gridFin d hd (0, 2 * b)).val, (gridFin d hd (0, 2 * b + 1)).val]).Pairwise (· < ·)
      rw [gridFin_val_of_lt d hd (show 0 < d by omega) (show 2 * b < d by omega),
          gridFin_val_of_lt d hd (show 0 < d by omega) (show 2 * b + 1 < d by omega)]
      simp only [List.pairwise_cons, List.mem_singleton, List.not_mem_nil, List.Pairwise.nil,
        forall_eq, false_implies, and_true, forall_const]
      omega
  | rightZ b =>
      rw [hcl] at hb
      obtain ⟨hb1, hb2⟩ := hb (2 * b + 1, d - 1) (by simp [kindOrderRC])
      show ([colMajorKey d (gridFin d hd (2 * b, d - 1)).val,
        colMajorKey d (gridFin d hd (2 * b + 1, d - 1)).val]).Pairwise (· < ·)
      rw [colMajorKey_gridFin d hd (2 * b) (d - 1) (by omega) (by omega),
          colMajorKey_gridFin d hd (2 * b + 1) (d - 1) (by omega) (by omega)]
      simp only [List.pairwise_cons, List.mem_singleton, List.not_mem_nil, List.Pairwise.nil,
        forall_eq, false_implies, and_true, forall_const]
      omega
  | leftZ b =>
      rw [hcl] at hb
      obtain ⟨hb1, -⟩ := hb (2 * b + 2, 0) (by simp [kindOrderRC])
      show ([colMajorKey d (gridFin d hd (2 * b + 1, 0)).val,
        colMajorKey d (gridFin d hd (2 * b + 2, 0)).val]).Pairwise (· < ·)
      rw [colMajorKey_gridFin d hd (2 * b + 1) 0 (by omega) (by omega),
          colMajorKey_gridFin d hd (2 * b + 2) 0 (by omega) (by omega)]
      simp only [List.pairwise_cons, List.mem_singleton, List.not_mem_nil, List.Pairwise.nil,
        forall_eq, false_implies, and_true, forall_const]
      omega
  | bottomX b =>
      rw [hcl] at hb
      obtain ⟨hb1, hb2⟩ := hb (d - 1, 2 * b + 2) (by simp [kindOrderRC])
      show ([(gridFin d hd (d - 1, 2 * b + 1)).val,
        (gridFin d hd (d - 1, 2 * b + 2)).val]).Pairwise (· < ·)
      rw [gridFin_val_of_lt d hd (show d - 1 < d by omega) (show 2 * b + 1 < d by omega),
          gridFin_val_of_lt d hd (show d - 1 < d by omega) (show 2 * b + 2 < d by omega)]
      simp only [List.pairwise_cons, List.mem_singleton, List.not_mem_nil, List.Pairwise.nil,
        forall_eq, false_implies, and_true, forall_const]
      omega

/-! ## S4b: assembly

All four `IsNZScheduleOf` fields hold for `nzSchedule` against the certified `Surface.code`
content, so the schedule has no surface-specific definitional freedom left — it is a
function of the code content and the code-independent NZ scheme rule alone. -/

/-- **The NZ schedule is the NZ schedule of `Surface.code`'s content.**  All four defining
properties — support-exactness, kind-faithfulness, duplicate-freeness, NZ-ordering — hold. -/
theorem nzSchedule_isNZScheduleOf (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) :
    IsNZScheduleOf d (surfaceCellPauli d i.val) (nzSchedule d hd i) where
  support_iff := nzSchedule_support_iff d hd hd3 hodd i
  kind_faithful := nzSchedule_kind_faithful d hd hd3 hodd i
  nodup := nzSchedule_support_nodup d hd hd3 hodd i
  nz_ordered := nzSchedule_nz_ordered d hd hd3 hodd i

/-! ## Uniqueness: "the NZ schedule of the content" is well-defined

A strictly-key-sorted list is determined by its member set, so two schedules
satisfying `IsNZScheduleOf` for the same content — keyed the same way (`scheduleKind`
agreement; automatic for kind-uniform content like every CSS check) — are equal.
With this, `nzSchedule`/the generated schedule is *the* NZ schedule of
`Surface.code`'s content, not merely *an* NZ-compatible one. -/

/-- `XZPauli.toPauli` is injective (`X ↦ X`, `Z ↦ Z`). -/
theorem XZPauli.toPauli_injective : Function.Injective XZPauli.toPauli := by
  intro a b h
  cases a <;> cases b <;> simp_all [XZPauli.toPauli]

/-- Strictly-key-sorted lists with the same members are equal. -/
private theorem sorted_ext {α : Type _} (key : α → Nat) :
    ∀ (l₁ l₂ : List α), (l₁.map key).Pairwise (· < ·) → (l₂.map key).Pairwise (· < ·) →
      (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ _ hmem
      cases l₂ with
      | nil => rfl
      | cons b t => exact absurd ((hmem b).mpr (List.mem_cons_self)) (List.not_mem_nil)
  | cons a t₁ ih =>
      intro l₂ h₁ h₂ hmem
      cases l₂ with
      | nil => exact absurd ((hmem a).mp (List.mem_cons_self)) (List.not_mem_nil)
      | cons b t₂ =>
          simp only [List.map_cons, List.pairwise_cons] at h₁ h₂
          have hlt₁ : ∀ x ∈ t₁, key a < key x := fun x hx =>
            h₁.1 (key x) (List.mem_map_of_mem hx)
          have hlt₂ : ∀ x ∈ t₂, key b < key x := fun x hx =>
            h₂.1 (key x) (List.mem_map_of_mem hx)
          have hab : a = b := by
            rcases List.mem_cons.mp ((hmem a).mp List.mem_cons_self) with h | h
            · exact h
            · rcases List.mem_cons.mp ((hmem b).mpr List.mem_cons_self) with h' | h'
              · exact h'.symm
              · exact absurd (hlt₂ a h) (by have := hlt₁ b h'; omega)
          subst hab
          have hmem' : ∀ x, x ∈ t₁ ↔ x ∈ t₂ := by
            intro x
            constructor
            · intro hx
              rcases List.mem_cons.mp ((hmem x).mp (List.mem_cons_of_mem a hx)) with h | h
              · subst h
                exact absurd (hlt₁ x hx) (Nat.lt_irrefl _)
              · exact h
            · intro hx
              rcases List.mem_cons.mp ((hmem x).mpr (List.mem_cons_of_mem a hx)) with h | h
              · subst h
                exact absurd (hlt₂ x hx) (Nat.lt_irrefl _)
              · exact h
          rw [ih t₂ h₁.2 h₂.2 hmem']

/-- **Uniqueness of the NZ schedule.**  Two `IsNZScheduleOf` schedules for the same
content, keyed the same way, are equal.  (The `scheduleKind` hypothesis is automatic
whenever the content is kind-uniform on its support — true of every CSS check.) -/
theorem IsNZScheduleOf.unique {d : Nat} {content : Nat → Pauli}
    {s₁ s₂ : RuleSchedule (d * d)}
    (h₁ : IsNZScheduleOf d content s₁) (h₂ : IsNZScheduleOf d content s₂)
    (hk : scheduleKind s₁ = scheduleKind s₂) : s₁ = s₂ := by
  have hslot : ∀ s, s ∈ s₁.slots ↔ s ∈ s₂.slots := by
    have half : ∀ (t₁ t₂ : RuleSchedule (d * d)), IsNZScheduleOf d content t₁ →
        IsNZScheduleOf d content t₂ → ∀ s, s ∈ t₁.slots → s ∈ t₂.slots := by
      intro t₁ t₂ g₁ g₂ s hs
      have hq : content s.qubit.val ≠ Pauli.I := (g₁.support_iff s.qubit).mp ⟨s, hs, rfl⟩
      obtain ⟨t, ht, htq⟩ := (g₂.support_iff s.qubit).mpr hq
      have hkind : s.kind = t.kind := by
        apply XZPauli.toPauli_injective
        rw [g₁.kind_faithful s hs, g₂.kind_faithful t ht, htq]
      have : s = t := by
        cases s; cases t
        simp_all
      rw [this]
      exact ht
    exact fun s => ⟨half s₁ s₂ h₁ h₂ s, half s₂ s₁ h₂ h₁ s⟩
  have hslots : s₁.slots = s₂.slots := by
    apply sorted_ext (fun s => nzKey d (scheduleKind s₁) s.qubit.val)
    · exact (List.pairwise_map).mpr ((List.pairwise_map).mp h₁.nz_ordered)
    · rw [hk]
      exact (List.pairwise_map).mpr ((List.pairwise_map).mp h₂.nz_ordered)
    · exact hslot
  cases s₁; cases s₂
  simp_all

end QStab.QClifford.Compile
