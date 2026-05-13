import QStab.Verifier
import QStab.Examples.SurfaceGeneral

/-!
# HGP code X-side fault-tolerance bundle (parametric over HGPSpec d)

Packages the HGP-family X-side distance theorem
(`hgp_distance_ge_d`) as a `QStabFTBundle`, parametric over an
`HGPSpec d` with `params.C_budget < d`.

Unlike the BB72 / surface bundles, the HGP framework's distance
theorem has shape `success → C_budget - s.C ≥ d`. The bundle's
bridge contraposes: `C_budget < d` forbids `C_budget - s.C ≥ d` for
any s, so no reachable state can satisfy the success condition.

Uses `MultiStep`-reachability as the dynamic invariant (same pattern
as `SurfaceD3Joint`).
-/

namespace QStab.Verifier.HGPX

open QStab QStab.Verifier QStab.Examples.SurfaceGeneral

variable {d : Nat}

/-- MultiStep-reachability as a dynamic invariant. -/
private def reachableInv (spec : HGPSpec d) :
    Invariant spec.params where
  holds s := MultiStep spec.params
    (.active (State.init spec.params)) (.active s)
  holds_init := Relation.ReflTransGen.refl
  preservation := fun _ _ hms step => Relation.ReflTransGen.tail hms step

/-- HGP code X-side fault-tolerance bundle, parametric over an
    `HGPSpec d` with budget below `d`. Failure: zero syndromes AND
    nonzero logical-Z parity. -/
def hgp_X_bundle (spec : HGPSpec d) (h_budget : spec.params.C_budget < d) :
    QStabFTBundle where
  P       := spec.params
  failure := fun E =>
    (∀ i : Fin spec.params.numStab,
      ErrorVec.parity (spec.params.stabilizers i) E = false) ∧
    (ErrorVec.parity spec.logicalZ E = true)
  inv     := reachableInv spec
  static  := true
  bridge  := fun _ s hms hfail => by
    obtain ⟨hSyn, hLog⟩ := hfail
    have h := hgp_distance_ge_d spec s hms hSyn hLog
    -- h : C_budget - s.C ≥ d, but C_budget < d ⇒ C_budget - s.C < d, contradiction.
    omega

theorem hgp_X_verified (spec : HGPSpec d)
    (h_budget : spec.params.C_budget < d) :
    verifyQStab (hgp_X_bundle spec h_budget) = true := rfl

/-- X-side `d_circ ≥ d` for any HGP code with `C_budget < d`,
    derived from the bundle via the generic `verifyQStab_sound`. -/
theorem hgp_X_d_circ_via_bundle
    (spec : HGPSpec d) (h_budget : spec.params.C_budget < d) :
    ∀ s : State spec.params,
      MultiStep spec.params (.active (State.init spec.params)) (.active s) →
      ¬ ((∀ i : Fin spec.params.numStab,
            ErrorVec.parity (spec.params.stabilizers i) s.E_tilde = false) ∧
         (ErrorVec.parity spec.logicalZ s.E_tilde = true)) :=
  verifyQStab_sound (hgp_X_bundle spec h_budget)
    (hgp_X_verified spec h_budget)

end QStab.Verifier.HGPX
