import QStab.QClifford.Compile.SurfaceRhoPerm
import QStab.QHL.Source.Examples.SurfaceUnionSpec

/-!
# The ρ-rotated union machine (F2 entry layer)

The corrected back-action swap for the surface X-floor transport: the full domination
closure is **refuted** (an X-type diagonal pair is dominated but not row-confinable — every
X-generator flips an even number of cells per row, so per-row X-parity is invariant
mod stabilizers), so the honest set is the minimal rotated closure

  `hookUnion ∪ ρ(hookUnion)`,

exactly what the transported hvalid produces: the ρ-image circuit's hooks are `rhoPhi`
images of the native hooks.  This file provides the machine (params + weight bound +
`InStab` transports); the ρ-image `hook_spread_bound` classification is the remaining
F2 content.
-/

namespace QStab.QClifford.Compile

open QStab QStab.Examples.SurfaceParametric QStab.Examples.SurfaceGeneral
open QHL.Source.Examples.SurfaceExactDistance QHL.Source.Examples.SurfaceUnionSpec

/-- `hadamardAction` preserves non-identity. -/
private theorem hadamardAction_ne_I_iff (p : Pauli) :
    hadamardAction p ≠ Pauli.I ↔ p ≠ Pauli.I := by
  cases p <;> simp [hadamardAction]

/-- **ρ-transport preserves weight**: `rhoPhi` permutes the support (positions move by
the rotation bijection, `hadamardAction` fixes `I`-ness). -/
theorem rhoPhi_weight (d : Nat) (hd : 0 < d) (E : ErrorVec (d * d)) :
    ErrorVec.weight (rhoPhi d hd E) = ErrorVec.weight E := by
  unfold ErrorVec.weight
  refine (Finset.card_equiv (rhoPermAmbient d (d * d) hd (Nat.le_refl _)) fun q => ?_).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have himg : rhoPhi d hd E ((rhoPermAmbient d (d * d) hd (Nat.le_refl _)) q)
      = hadamardAction (E q) := by
    show hadamardAction (E ⟨rhoInvNat d (rhoNat d q.val), _⟩) = hadamardAction (E q)
    congr 1
    exact congrArg E (Fin.ext (rho_leftInv d q.val hd))
  rw [himg, hadamardAction_ne_I_iff]

/-- **The ρ-rotated union machine**: back-action is the hook union together with the
ρ-images of the hook union — the minimal set the duality transport needs (the image
circuit's hooks are `rhoPhi`-images of native hooks).  Additive over
`mkSurfaceQECParams`: only `backActionSet` and its weight bound change. -/
def mkSurfaceQECParamsRho (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) : QECParams :=
  { mkSurfaceQECParams d hd hodd with
    backActionSet := fun _ =>
      { e | (∃ s, e ∈ mkSurfaceHookErrors d hd hodd s)
          ∨ (∃ s, ∃ e₀ ∈ mkSurfaceHookErrors d hd hodd s, e = rhoPhi d hd e₀) }
    backAction_weight_bound := by
      intro _ e he
      rcases he with ⟨s', hs'⟩ | ⟨s', e₀, he₀, rfl⟩
      · exact mkSurfaceHookErrors_weight_le d hd hodd s' e hs'
      · exact le_of_eq_of_le (rhoPhi_weight d hd e₀)
          (mkSurfaceHookErrors_weight_le d hd hodd s' e₀ he₀) }

/-- `InStab` is independent of `backActionSet`: transport into the ρ-machine. -/
def inStabRho {d : Nat} {hd : 0 < d} {hodd : d % 2 = 1}
    {E : ErrorVec (mkSurfaceQECParams d hd hodd).n} :
    InStab (mkSurfaceQECParams d hd hodd) E → InStab (mkSurfaceQECParamsRho d hd hodd) E
  | .identity => .identity
  | .gen i => by
      simpa [mkSurfaceQECParamsRho] using (InStab.gen (P := mkSurfaceQECParamsRho d hd hodd) i)
  | .mul h₁ h₂ => .mul (inStabRho h₁) (inStabRho h₂)

/-- The reverse transport (ρ-machine back to the per-stabilizer machine). -/
def inStabRestoreRho {d : Nat} {hd : 0 < d} {hodd : d % 2 = 1}
    {E : ErrorVec (mkSurfaceQECParams d hd hodd).n} :
    InStab (mkSurfaceQECParamsRho d hd hodd) E → InStab (mkSurfaceQECParams d hd hodd) E
  | .identity => .identity
  | .gen i => by
      simpa [mkSurfaceQECParamsRho] using (InStab.gen (P := mkSurfaceQECParams d hd hodd) i)
  | .mul h₁ h₂ => .mul (inStabRestoreRho h₁) (inStabRestoreRho h₂)

end QStab.QClifford.Compile
