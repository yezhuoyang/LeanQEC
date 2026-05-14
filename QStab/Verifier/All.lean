import QStab.Verifier
import QStab.Verifier.QCliffordCertificate
import QStab.Verifier.BB72NZJoint
import QStab.Verifier.BB72SEX
import QStab.Verifier.SurfaceD3X
import QStab.Verifier.SurfaceD3Joint
import QStab.Verifier.HGPX

/-!
# QStab.Verifier.All — aggregated entry point

A single import that pulls in the generic verifier core and every
concrete bundle. `lake build QStab.Verifier.All` exercises the
entire verifier suite in one command — useful for CI and the
workflow doc.

Importing this module gives any consumer access to:
  * The QStab-level structure and soundness (`QStab.Verifier`).
  * The gate-level structure and soundness
    (`QStab.Verifier.QCliffordCertificate`).
  * All packaged bundles:
      - `bb72_NZ_joint_certificate` (BB[[72,12,6]] NZ joint X+Z)
      - `bb72_SE_X_certificate` (BB72 SE scheduling, X-side)
      - `surface_d3_X_certificate` (surface d=3 X-side, parametric scheduling)
      - `surface_d3_joint_certificate` (surface d=3 joint, parametric)
      - `hgp_X_certificate` (HGP family, parametric over `HGPSpec d`)

See `QStab/Verifier/README.md` for the bundle-writing workflow.
-/
