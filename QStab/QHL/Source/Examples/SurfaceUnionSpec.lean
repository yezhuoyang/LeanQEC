import QStab.QHL.Source.Examples.SurfaceExactDistance

/-!
# Union-machine Surface/NZ spec (source anchor for the compiler-lowered bar-Z distance)

This module is the **source anchor** for the compiler-lowered distance bridge.  It is
identical to `mkSurfaceNZSurfaceSpec` except that `backActionSet` is the **union** over
all stabilizers,

  `{ e | ∃ s, e ∈ mkSurfaceHookErrors d hd hodd s }`,

rather than the per-stabilizer set.  This is **sound** because `hook_spread_bound` is
*coordinate-independent*: any hook, from any stabilizer, spreads the X-row count by at
most one, and the derivation never uses `s_idx` elsewhere.  The final compiled-distance
statement never mentions this machine (it is a statement purely about the compiled
circuit); the union is used only so that the compiler-lowering side condition
(`hvalid`, a `∀ st'` membership on `backActionSet (currentStab …)`) is provable without a
coordinate-advancing fold.
-/

namespace QHL.Source.Examples.SurfaceUnionSpec

open QStab QStab.Examples.SurfaceParametric QStab.Examples.SurfaceGeneral
open QHL.Source.Examples.SurfaceExactDistance

/-- Surface QEC params with the **union** back-action set (additive over
`mkSurfaceQECParams`: only `backActionSet` and its weight bound change). -/
def mkSurfaceQECParamsU (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) : QECParams :=
  { mkSurfaceQECParams d hd hodd with
    backActionSet := fun _ => { e | ∃ s, e ∈ mkSurfaceHookErrors d hd hodd s }
    backAction_weight_bound := by
      intro _ e he
      obtain ⟨s', hs'⟩ := he
      exact mkSurfaceHookErrors_weight_le d hd hodd s' e hs' }

/-- `InStab` is independent of `backActionSet`, so it transports to the union machine. -/
def inStabU {d : Nat} {hd : 0 < d} {hodd : d % 2 = 1}
    {E : ErrorVec (mkSurfaceQECParams d hd hodd).n} :
    InStab (mkSurfaceQECParams d hd hodd) E → InStab (mkSurfaceQECParamsU d hd hodd) E
  | .identity => .identity
  | .gen i => by
      simpa [mkSurfaceQECParamsU] using (InStab.gen (P := mkSurfaceQECParamsU d hd hodd) i)
  | .mul h₁ h₂ => .mul (inStabU h₁) (inStabU h₂)

/-- The reverse transport (union machine back to the per-stabilizer machine). -/
def inStabRestoreU {d : Nat} {hd : 0 < d} {hodd : d % 2 = 1}
    {E : ErrorVec (mkSurfaceQECParams d hd hodd).n} :
    InStab (mkSurfaceQECParamsU d hd hodd) E → InStab (mkSurfaceQECParams d hd hodd) E
  | .identity => .identity
  | .gen i => by
      simpa [mkSurfaceQECParamsU] using (InStab.gen (P := mkSurfaceQECParams d hd hodd) i)
  | .mul h₁ h₂ => .mul (inStabRestoreU h₁) (inStabRestoreU h₂)

/-- The NZ Surface spec over the union machine.  Fields are copied from
`mkSurfaceNZSurfaceSpec`; the two `InStab`-carrying fields transport via `inStabU`, and
`hook_spread_bound` unpacks the union `∃ s` and applies the (coordinate-independent)
per-index bound. -/
def unionNZSurfaceSpec (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : NZSurfaceSpec d where
  params := mkSurfaceQECParamsU d (by omega) hodd
  hn := rfl
  hd_pos := by omega
  logicalZ := (mkSurfaceNZSurfaceSpec d hd3 hodd).logicalZ
  rowCut := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut
  rowCut_zero := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut_zero
  rowCut_succ := fun i hi => by
    obtain ⟨S, hS, hZ, hrow⟩ := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut_succ i hi
    exact ⟨S, inStabU hS, hZ, hrow⟩
  logicalZ_normalizer := (mkSurfaceNZSurfaceSpec d hd3 hodd).logicalZ_normalizer
  rowCut_spec := (mkSurfaceNZSurfaceSpec d hd3 hodd).rowCut_spec
  stab_commute := (mkSurfaceNZSurfaceSpec d hd3 hodd).stab_commute
  hook_spread_bound := fun _ e_B he E S_wit hS => by
    obtain ⟨s, hs⟩ := he
    obtain ⟨S', hS', hcard⟩ :=
      (mkSurfaceNZSurfaceSpec d hd3 hodd).hook_spread_bound s e_B hs E S_wit (inStabRestoreU hS)
    exact ⟨S', inStabU hS', hcard⟩

/-- The union machine retargeted to budget exactly `d` (so `C_budget = d`, `rfl`). -/
def unionSurfaceSpec (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : NZSurfaceSpec d :=
  retargetSurfaceSpec (unionNZSurfaceSpec d hd3 hodd) d

end QHL.Source.Examples.SurfaceUnionSpec
