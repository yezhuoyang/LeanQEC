/-!
# Scope notes: multi-scheme compiled classification and general HGP(H₁,H₂)

Docs-only (zero declarations).  Honest statement of what the compiled
pipeline proves today and what the two queued generalisations would need.

## What is proven

* Surface (odd `d ≥ 3`, NZ scheme): compiled bar-Z distance floor,
  `Stab`/`logicalFailure` transport, `reach` — 4/5 VCGen slots (`ftDistance`
  blocked on the X-side floor, milestone F3).
* HGP(Rep(d), Rep(d)) (`d ≥ 2`), **NZ scheme**: **all five slots** —
  `hgp_Safe` / `hgp_compiled_Safe`.  Both floors (bar-Z direct, bar-X by
  duality transport), `maximal_isotropic` coverage, row-0 reach script.
* HGP(Rep(d), Rep(d)) (`d ≥ 2`), **Shor / Knill / Flag schemes**: **both
  distance floors and the `ftDistance` VCGen slot** — 4/5 slots.
  `hgp{Shor,Knill,Flag}_compiled_barZ_distance` (via the `SchemeClassifier`
  framework), `hgp{Shor,Knill,Flag}_compiled_barX_distance` (via the *generic*
  `compiled_barX_of_dualityAutomorphism`, generalized over helper count / circuit
  / `HGPSchemeHValid` in `HGPSchemeXDistance.lean`), and
  `hgp{Shor,Knill,Flag}_ftDistance` / `_vcgen_ftDistanceD` (via the generic
  `hgp_coverage` + both floors + a scheme-generic `logicalFailure`-iff, in
  `HGPSchemeFtDistance.lean`).  Everything routes through `hgpSchemeCircuit
  scheme d` (`= compileProgram (hgpSchemeProgram scheme d)`); the bridge and the
  VCGen slot are instantiated, never widened.  Only `reach` (hence `Safe`) is
  **not yet** closed for these schemes (see below).

## G6 — multi-scheme compiled classification (DONE, `ftDistance`/`reach` open)

The compiler front-end emits Shor/Knill/Flag gadget blocks
(`compileGadgetBlock`), and the compiled per-scheme site classification is now
**landed** for all four schemes: `shor_gadget_site_classified`,
`knill_site_wle1`/`knill_SchemeClassifier`, and `zpsChain_site_classified` /
`flag_gadget_site_classified` (the last handles Flag's mixed X/Z couplings via
the kind-generic `kindTransform` / `propagate_zpsChain_anc` calculus, replacing
the kind-uniform `nzSuffixResidual` machinery).  Each closes `HGPSchemeHValid`
(via `hgpScheme_hvalid`), hence both compiled distance floors above.  Nothing in
the bridge (`etildeC_hoare_preservation` chain) was changed — it is
circuit-generic and instantiated.

What remains open for full `Safe` on the non-NZ schemes — **only `reach`**:

* **`ftDistance`: DONE** (`HGPSchemeFtDistance.lean`).  The spec transport lifted
  over `scheme` cleanly: the compiled program's measured schedules are the
  scheme-independent `hgpSchedule` family (`hgpSchemeProgram_map_schedule` via the
  tag-generalized `measuresAtAux_seqMeas_map_schedule_gen`), and every downstream
  faithfulness lemma (`scheduleRow_hgpSchedule_dataRestrict`/`_helperTrivial`,
  `stabEntry_eq_I_of_not_mem`, `hgp_scheduleParity_eq_vectorParity`) is already
  helper-count-generic, so `hgpScheme_Stab_iff_InStab_es` /
  `_centralizer_iff_es` / `_logicalFailure_iff` port by swapping the program.
* **`reach`: hard NZ-only gap** (the sole blocker for `Safe`).  `hgpReachScript`
  / `hgp_reach_run` / `hgp_reach_step` are hardwired to the Standard NZ gadget
  (`nzBlock`, row-0 `X` injection via `hgpInjs`, X-uniform parity blindness).
  Each scheme has a different gadget layout (cat states, transversal readout,
  flag interleaving) and needs its own fault-injection script + reach proof;
  there is no scheme-generic reach framework.  No `Safe` is claimed for
  Shor/Knill/Flag until it is closed.

## G7 — general HGP(H₁, H₂) (deferred)

What generalises directly: the code-blind generator (`xzProgramOfPrograms`),
the union back-action design (pointwise domination by the own generator is
tensor-structural), and the transport engine (`StabTransportCore`).

What is Rep×Rep-specific today:

* the duality transport uses the *self*-duality of HGP(H,H) under the sector
  transpose; HGP(H₁,H₂) with H₁ ≠ H₂ pairs with HGP(H₂ᵀ,H₁ᵀ)-style partners
  instead — the bar-X floor would need either that transposed-pair transport
  or a direct X-side cleaning;
* the three-phase `maximal_isotropic` cleaning uses the Rep-chain structure
  (vertical dominoes, adjacent-column pair cleaners); a general `H` needs
  the classical statement `ker H₁ / row-span H₂ᵀ` handled abstractly, and
  `k > 1` logical sectors need the general-`k` coset machinery
  (`LogicalCosets.General`, already mechanised) in place of the `k = 1`
  `LogicalOps`;
* the closed-form schedules (`hgpSupportList` with its boundary guards) are
  Rep-specific; a general `H` needs generator-support programs synthesised
  from `H`'s row supports.

Estimate: the floors and transports are a full campaign; the `ftDistance`
assembly pattern (floors + coverage contrapositive + iff-transport) carries
over unchanged once those exist.
-/
