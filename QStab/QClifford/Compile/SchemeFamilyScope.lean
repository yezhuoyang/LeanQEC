/-!
# Scope notes: multi-scheme compiled classification and general HGP(H₁,H₂)

Docs-only (zero declarations).  Honest statement of what the compiled
pipeline proves today and what the two queued generalisations would need.

## What is proven (both code families, NZ scheme)

* Surface (odd `d ≥ 3`): compiled bar-Z distance floor, `Stab`/`logicalFailure`
  transport, `reach` — 4/5 VCGen slots (`ftDistance` blocked on the X-side
  floor, milestone F3).
* HGP(Rep(d), Rep(d)) (`d ≥ 2`): **all five slots** — `hgp_Safe` /
  `hgp_compiled_Safe`.  Both floors (bar-Z direct, bar-X by duality
  transport), `maximal_isotropic` coverage, row-0 reach script.

Scope qualifier carried by every headline: the NZ extraction scheme with the
canonical per-check schedule; any *gate scheduling* of the couplings is
absorbed by the union back-action machine, but the *scheme* (ancilla
topology) is fixed.

## G6 — multi-scheme compiled classification (deferred)

The compiler front-end already emits Shor/Knill/Flag gadget blocks
(`compileGadgetBlock`), and the *source-level* scheme-correctness proofs
exist (`SchemeFamilies/`: Standard, KnillCSS, Flag2, Shor).  What is missing
for a compiled `hvalid` (hence compiled floors) per scheme:

* per-scheme site classification of the compiled blocks — the NZ
  classification (`nz_gadget_site_classified` and the `nzSuffixResidual`
  calculus) has no Shor/Knill/Flag analog; gadget shapes differ (cat states,
  transversal readout, flag interleaving);
* Flag blocks mix X- and Z-kind couplings inside one gadget, so the
  kind-uniform schedule machinery (`RuleSchedule.uniform`,
  `scheduleRow_eval_uniform`) does not apply as-is;
* Shor's standalone-vs-compiled bridge (the cat-preparation block is not a
  `zParitySlot` stream).

Estimate: one NZ-classification-sized campaign *per scheme*; nothing in the
bridge (`etildeC_hoare_preservation` chain) needs to change — it is
circuit-generic and would be instantiated, not widened.

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
