import QStab.QHL.Source.Examples.HGP

namespace QHL.Source.Examples.HGP.Check

open QHL.Source.Examples.HGP

/-! ## Independent axiom-audit checkpoint for the HGP code

The parametric HGP headline `hgp_dcirc_geq_d` is built using:

  1. A fixed row-major `QStabProgram`.
  2. The demonic one-step `hgp_havoc_derivation`, whose premises cover every
     enabled nondeterministic QStab branch.
  3. `hgp_invariant_derivation.check_sound` to compose the one-step rule over
     `Run`.
  4. Syntactic aligned-barrier denotation plus arithmetic for the final
     distance bound.

ALL must have axiom footprint `[propext, Classical.choice, Quot.sound]`
or stricter.
-/

-- ─── Headlines ────────────────────────────────────────────────────────

#check @hgp_dcirc_geq_d
#check @hgp_no_logical_error

-- ─── Trusted-base check ───────────────────────────────────────────────

#print axioms hgp_dcirc_geq_d
#print axioms hgp_no_logical_error

-- ─── Nondeterministic branch derivation ──

#check @hgp_havoc_derivation
#check @hgp_invariant_derivation
#print axioms hgp_havoc_derivation
#print axioms hgp_invariant_derivation

end QHL.Source.Examples.HGP.Check
