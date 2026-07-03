import QStab.QClifford.Compile.HConjRelabel
import QStab.QClifford.Compile.HoarePreservation

/-!
# The generic compiled bar-X distance floor by a duality automorphism

`hgp_compiled_barX_distance` and `surface_compiled_barX_distance` are structurally
identical: both simulate the real run on the `hConjCircuit`-conjugated image
circuit (`qceval_hConj`, transporting paulis + λ only), observe that the residual
becomes a **bar-Z**-class residual under the data transport `Φ`, apply the image
bar-Z floor, and pull the fault-count bound back.

This file factors that pullback into ONE generic lemma
`compiled_barX_of_dualityAutomorphism`, parameterized by a `DualityAutomorphism`
bundle — the code automorphism data (`perm`, `Φ`, the σ-check-permutation
surjectivity, `Φ(X̄)=Z̄`, parity-Φ-equivariance) plus the image bar-Z floor.  A
self-dual code (HGP, `Φ` involutive) and a rotation-dual code (surface, `Φ` order
4) each become a ~10-line instantiation.

The functor (`hConjCircuit` / `qceval_hConj`) is reused verbatim — it is not
touched here.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford

/-- **The duality-automorphism bundle.**  Everything the generic bar-X pullback
consumes: the compiled code (`params` / `fc` / `Xbar` / `Zbar` / `d`), the
ambient permutation `perm` and data transport `Φ` with their coherence, the three
algebraic facts of a stabilizer automorphism (`parity_Φ`, stab surjectivity,
`Φ(X̄)=Z̄`), and the image bar-Z floor (produced per-code by the hvalid transport). -/
structure DualityAutomorphism where
  params  : QECParams
  helpers : Nat
  d       : Nat
  fc      : FCircuit (params.n + helpers)
  Xbar    : ErrorVec params.n
  Zbar    : ErrorVec params.n
  perm     : Equiv.Perm (Fin (params.n + helpers))
  Phi      : ErrorVec params.n → ErrorVec params.n
  dualData : Fin params.n → Fin params.n
  /-- `Φ` is Hadamard ∘ pullback along the data-index map `dualData`. -/
  Phi_def        : ∀ E q, Phi E q = hadamardAction (E (dualData q))
  /-- `perm` restricted to the data block inverts `dualData`. -/
  perm_freshData : ∀ q, perm (freshDataQ params.n helpers (dualData q))
                        = freshDataQ params.n helpers q
  /-- `Φ` preserves symplectic parity (it is a Clifford automorphism). -/
  parity_Phi : ∀ F E, ErrorVec.parity (Phi F) (Phi E) = ErrorVec.parity F E
  /-- Every stabilizer generator row is the `Φ`-image of some generator row
      (the σ-check-permutation is surjective). -/
  stab_surj  : ∀ i, ∃ j, Phi (params.stabilizers j) = params.stabilizers i
  /-- `Φ` sends the logical `X̄` to the logical `Z̄`. -/
  Phi_Xbar   : Phi Xbar = Zbar
  /-- The bar-Z distance floor on the conjugated image circuit. -/
  image_barZ_floor :
    ∀ tau : QCState (params.n + helpers),
      qceval (hConjCircuit perm fc) (QCState.clean (params.n + helpers)) tau →
      (∀ i, ErrorVec.parity (params.stabilizers i)
              (dataErrorOfQCState params helpers tau) = false) →
      ErrorVec.parity Zbar (dataErrorOfQCState params helpers tau) = true →
      d ≤ tau.lambda

/-- **The generic compiled bar-X distance floor.**  For any `DualityAutomorphism`,
every clean-start run of `fc` whose data residual commutes with every stabilizer
and anticommutes with `X̄` fired at least `d` faults.  Proved by transport: the run
is simulated on the conjugated image circuit (`qceval_hConj`), where its residual
is bar-Z-class (`stab_surj` + `Φ(X̄)=Z̄`, through `parity_Φ`) and the image floor
applies; `λ` agrees between the two runs. -/
theorem compiled_barX_of_dualityAutomorphism (A : DualityAutomorphism)
    (sigma : QCState (A.params.n + A.helpers))
    (hrun : qceval A.fc (QCState.clean (A.params.n + A.helpers)) sigma)
    (hcent : ∀ i, ErrorVec.parity (A.params.stabilizers i)
        (dataErrorOfQCState A.params A.helpers sigma) = false)
    (hx : ErrorVec.parity A.Xbar (dataErrorOfQCState A.params A.helpers sigma) = true) :
    A.d ≤ sigma.lambda := by
  obtain ⟨tau, hrunD, hlam, hpauli⟩ := qceval_hConj A.perm hrun (HRel_clean A.perm)
  have hdata : dataErrorOfQCState A.params A.helpers tau
      = A.Phi (dataErrorOfQCState A.params A.helpers sigma) := by
    funext q
    rw [A.Phi_def]
    show tau.es.paulis (freshDataQ A.params.n A.helpers q)
      = hadamardAction (sigma.es.paulis (freshDataQ A.params.n A.helpers (A.dualData q)))
    rw [show freshDataQ A.params.n A.helpers q
        = A.perm (freshDataQ A.params.n A.helpers (A.dualData q))
      from (A.perm_freshData q).symm]
    exact hpauli _
  have hfloor := A.image_barZ_floor tau hrunD
    (by
      intro i
      rw [hdata]
      obtain ⟨j, hj⟩ := A.stab_surj i
      rw [← hj, A.parity_Phi]
      exact hcent j)
    (by
      rw [hdata, ← A.Phi_Xbar, A.parity_Phi]
      exact hx)
  exact hlam ▸ hfloor

end QStab.QClifford.Compile
