import QStab.Examples.HGPParametric
import QStab.QHL.Source.Examples.SurfaceExactDistance

/-!
# Union-machine HGP spec, retargeted to budget `d`

The source anchor for the HGP compiler-lowered bar-Z distance, mirroring
`SurfaceUnionSpec`:

* `mkHGPRepQECParamsU` — the parametric HGP machine with the **union**
  back-action set `{e | ∃ k, e ∈ hgpBackAction d k}` (every error pointwise
  dominated by *some* generator).  Sound because `hook_in_column` is
  coordinate-independent; needed so the compiler-lowering side condition
  (`hvalid`, a `∀ st'` membership at `currentStab`) is provable without a
  coordinate-advancing fold.
* `retargetHGPSpec` — the `HGPSpec`-level budget retarget
  (`retargetSurfaceSpec` pattern; only the two `InStab`-carrying fields need
  transport).
* `exactUnionHGPSpec d hd` — the union machine at budget exactly `d`, so the
  compiled-distance assembly's `hbudget` is `Nat.le_refl d`.
-/

namespace QHL.Source.Examples.HGPUnionSpec

open QStab QStab.Examples.SurfaceGeneral QStab.Examples.HGPParametric
open QHL.Source.Examples.SurfaceExactDistance

/-- HGP params with the **union** back-action set (additive over
`mkHGPRepQECParams`: only `backActionSet` changes; the weight bound is the
per-generator one, unpacked). -/
def mkHGPRepQECParamsU (d : Nat) (hd : 2 ≤ d) : QECParams :=
  { mkHGPRepQECParams d hd with
    backActionSet := fun _ => { e | ∃ k, e ∈ hgpBackAction d k }
    backAction_weight_bound := by
      intro _ e he
      obtain ⟨k, hk⟩ := he
      exact (mkHGPRepQECParams d hd).backAction_weight_bound k e hk }

/-- `InStab` is independent of `backActionSet`: transport to the union machine. -/
def inStabU {d : Nat} {hd : 2 ≤ d} {E : ErrorVec (mkHGPRepQECParams d hd).n} :
    InStab (mkHGPRepQECParams d hd) E → InStab (mkHGPRepQECParamsU d hd) E
  | .identity => .identity
  | .gen i => by
      simpa [mkHGPRepQECParamsU] using (InStab.gen (P := mkHGPRepQECParamsU d hd) i)
  | .mul h₁ h₂ => .mul (inStabU h₁) (inStabU h₂)

/-- The reverse transport. -/
def inStabRestoreU {d : Nat} {hd : 2 ≤ d} {E : ErrorVec (mkHGPRepQECParams d hd).n} :
    InStab (mkHGPRepQECParamsU d hd) E → InStab (mkHGPRepQECParams d hd) E
  | .identity => .identity
  | .gen i => by
      simpa [mkHGPRepQECParamsU] using (InStab.gen (P := mkHGPRepQECParams d hd) i)
  | .mul h₁ h₂ => .mul (inStabRestoreU h₁) (inStabRestoreU h₂)

/-- The parametric HGP spec over the union machine.  Fields are copied from
`mkHGPRepSpec`; the two `InStab`-carrying fields transport via `inStabU`, and
`hook_in_column` unpacks the union `∃ k` and applies the
(coordinate-independent) per-generator bound. -/
def unionHGPRepSpec (d : Nat) (hd : 2 ≤ d) : HGPSpec d where
  params := mkHGPRepQECParamsU d hd
  hd_pos := by omega
  logicalZ := (mkHGPRepSpec d hd).logicalZ
  col := (mkHGPRepSpec d hd).col
  cutOp := (mkHGPRepSpec d hd).cutOp
  cutOp_stabEquiv := fun i => by
    obtain ⟨S, hS, hEq⟩ := (mkHGPRepSpec d hd).cutOp_stabEquiv i
    exact ⟨S, inStabU hS, hEq⟩
  cutOp_spec := (mkHGPRepSpec d hd).cutOp_spec
  logicalZ_normalizer := (mkHGPRepSpec d hd).logicalZ_normalizer
  stab_commute := (mkHGPRepSpec d hd).stab_commute
  hook_in_column := fun _ e_B he E S_wit hS => by
    obtain ⟨k, hk⟩ := he
    obtain ⟨S', hS', hcard⟩ :=
      (mkHGPRepSpec d hd).hook_in_column k e_B hk E S_wit (inStabRestoreU hS)
    exact ⟨S', inStabU hS', hcard⟩

/-- Retarget an HGP specification to another execution budget without changing
its code, logical operator, column geometry, or back-action set. -/
abbrev retargetHGPSpec {d : Nat} (spec : HGPSpec d) (budget : Nat) : HGPSpec d where
  params := retargetParams spec.params budget
  hd_pos := spec.hd_pos
  logicalZ := spec.logicalZ
  col := spec.col
  cutOp := spec.cutOp
  cutOp_stabEquiv := fun i => by
    obtain ⟨S, hS, hEq⟩ := spec.cutOp_stabEquiv i
    exact ⟨S, inStabRetarget hS, hEq⟩
  cutOp_spec := spec.cutOp_spec
  logicalZ_normalizer := spec.logicalZ_normalizer
  stab_commute := spec.stab_commute
  hook_in_column := fun s_idx e_B he E S_wit hS => by
    obtain ⟨S', hS', hcard⟩ :=
      spec.hook_in_column s_idx e_B he E S_wit (inStabRestore hS)
    exact ⟨S', inStabRetarget hS', hcard⟩

/-- The union machine at budget exactly `d`. -/
abbrev exactUnionHGPSpec (d : Nat) (hd : 2 ≤ d) : HGPSpec d :=
  retargetHGPSpec (unionHGPRepSpec d hd) d

@[simp] theorem exactUnionHGPSpec_budget (d : Nat) (hd : 2 ≤ d) :
    (exactUnionHGPSpec d hd).params.C_budget = d :=
  rfl

#print axioms unionHGPRepSpec
#print axioms exactUnionHGPSpec

end QHL.Source.Examples.HGPUnionSpec
