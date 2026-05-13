import QStab.Paper.GenericReachableBridge
import QStab.MultiStep
import QStab.Invariant
import QStab.PauliOps

/-!
# Applying the QStab framework to LDPC codes (LP, BB, etc.)

## Summary

The `Paper.GenericReachableBridge` framework is **CSS-generic**: it
gives an operational `d_circ ≥ d` proof for ANY QECParams, modulo a
per-scheduling finite check on `reachableE allHooks (d−1)`.

This file documents how to apply the framework to non-surface CSS
codes — specifically Lifted Product (LP) codes and Bivariate Bicycle
(BB) codes — and characterises what's tractable at scale.

## Recap: the generic theorem (already proved)

```lean
theorem nonSuccess_op_d_circ_ge_d (P : QECParams) (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks)
    (isSuccess : ErrorVec P.n → Bool)
    (h_finite_check : ∀ E ∈ reachableE allHooks P.C_budget, isSuccess E = false) :
    ∀ s, MultiStep ... → isSuccess s.E_tilde = false
```

This **doesn't depend on the code being surface**. Any CSS QECParams
with the right back-action structure plugs in.

## What changes for LDPC codes

### Bivariate Bicycle (BB) codes

Construction: from polynomials A(x,y), B(x,y) in F_2[x,y]/(x^l - 1, y^m - 1).
H_X = [A | B], H_Z = [B^T | A^T].

Smallest non-trivial: [[72, 12, 6]] with l=m=6, A=B=x^3+y+y^2.

Larger: [[144, 12, 12]], [[288, 12, 18]], etc.

**Stabiliser weight**: 6 (for the IBM family). All stabs same weight,
unlike surface code's mix of weight-4 bulk + weight-2 boundary.

**Topology**: torus (no boundaries). Translation invariance under l × m
shift group.

**Logicals**: k > 1 in general (k=12 for [[72,12,6]]). Multiple `L_Z`
basis vectors.

### Lifted Product (LP) codes

Construction: from "protograph" + lift via cyclic group of order ell.
H_X, H_Z are quasi-cyclic block matrices.

Smallest in the literature: [[544, 80, 12]], [[714, 100, 16]], etc.
Much bigger than BB.

## Tractability matrix

| Operation | Surface d=3 | Surface d=k | BB [[72,12,6]] | LP [[544,80,12]] |
|---|---|---|---|---|
| Build QECParams | ✓ trivial | ✓ trivial | ⚠ tedious matrix def | ✗ very large |
| Per-scheduling check (decide) | ✓ (≈10⁴ elts) | ✓ (≈10^{d-1}) | ⚠ ≈10⁷ elts | ✗ ≈10^{12+} |
| Per-scheduling via native_decide | ✓ fast | borderline | borderline | infeasible |
| Per-scheduling via codeDistance | ✓ fast | OK | OK (~minutes) | OK (~hours) |
| Full ensemble enumeration | ✓ 2304 schedulings | ✗ exponential | ✗ 720^36 ≈ 10^{114} | ✗ even worse |
| Universal (ν-only) classifier | ✓ at d=3,4 | ✗ disproved at d=5 | ✗ likely impossible | ✗ likely impossible |

## What our framework gives for BB/LP codes

**Strictly**: a Lean-verified per-scheduling, per-logical theorem template.
For each fixed BB/LP scheduling and each fixed logical operator, `d_circ ≥ d`
holds iff a specific finite check passes. The check is decidable and
the framework reduces it from "trajectory enumeration" to
"reachableE enumeration" (which is much smaller).

**It does NOT give**: a closed-form classifier of "good" schedulings at
this scale. The scheduling space is astronomically large
(720^36 ≈ 10^114 for [[72,12,6]]); no per-stab local rule has been
shown to capture FT preservation.

**Empirical analog**: the IBM paper provides specific scheduling
prescriptions for [[144,12,12]] etc. that achieve d_circ = d. These are
hand-designed, not derived from a per-stab local classifier.

## Concrete demonstration: framework instantiation skeleton

For a hypothetical small CSS code with given matrices H_X, H_Z:

```
def myCode_QECParams (sched : MyScheduling) : QECParams where
  n := <num qubits>
  k := <num logicals>
  d := <distance>
  R := 1
  numStab := <num stabilisers>
  stabilizers := myStabilisers
  backActionSet := myBackActionSet sched
  r := <max hook weight>
  backAction_weight_bound := <proof>
  C_budget := <distance - 1>
  hn := ...
  hns := ...
  hR := ...

-- Headline: theorem follows from GenericReachableBridge
theorem myCode_d_circ_ge
    (sched : MyScheduling)
    (h_finite_check : ∀ E ∈ reachableE (myAllHooks sched) <C_budget>,
                        myIsSuccess E = false) :
    ∀ s, MultiStep (myCode sched) ... →
         myIsSuccess s.E_tilde = false :=
  nonSuccess_op_d_circ_ge_d (myCode sched) (myAllHooks sched) ...
```

This is a TWENTY-LINE Lean file given the matrices. The hard part is
**building the matrices in Lean from a polynomial-ring construction**
(BB) or **from a protograph lift** (LP), which is mechanical but
tedious.

For [[72,12,6]] BB: 36 weight-6 stabs each requiring an `ofList [...]`
of 6 entries. A Lean instance is ~50-100 lines. Adding native_decide
checks for the per-scheduling finite-check would compute over a list
of ~10⁷ elements at depth 5 — borderline feasible.

For LP codes: scale-up tedious, no fundamental obstruction.

## Empirical findings on [[72, 12, 6]] BB code (`notes/bb_72_*.py`)

| Scheduling | d_circ | Wall-clock per logical |
|---|---|---|
| NZ (lex-sorted) | 6 (preserved) | ~0.1s |
| Random (sample of 30) | 3 or 4 (failed in 30/30 cases) | ~0.3s |

Key observations:

  * **BB codes are extremely schedule-sensitive.** 100% of random
    schedulings drop d_circ from 6 to 3-4 in the [[72,12,6]] code.
    This contrasts with surface code d=3 where ~44% (1024/2304)
    preserve.
  * **Per-scheduling d_circ check is fast** via codeDistance
    (sub-second). The framework's structural reduction is verified
    against this for surface code; same reduction applies for BB code,
    but full Lean enumeration is intractable.
  * **No default-safe scheduling.** Unlike surface code where NZ-style
    is "natural", BB codes need hand-designed schedulings (IBM's
    construction in arXiv:2308.07915 is one example).

## Honest contribution boundary

This file does **not** build a concrete BB or LP Lean instance. The
contribution is the **framework documentation**:

  1. The `GenericReachableBridge` template applies CSS-generically.
  2. Per-scheduling, per-logical FT analysis works for BB/LP.
  3. The combinatorial limit at scale is the per-scheduling finite check
     itself, not the framework. SAT/SMT integration in Lean would help.
  4. **No closed-form universal classifier** is known for BB/LP, and the
     d=5 surface code disproof of the "row-traversal" conjecture suggests
     none exists for LDPC codes either. This is a research conjecture.
  5. Empirical evidence (BB [[72,12,6]] sample): 100% of random
     schedulings fail. Schedule choice is critical and **must be checked
     per-instance**; this is exactly what the framework supports.

The d=3 surface code's complete characterisation
(`Paper/SurfaceD3FullCharacterization`) is a special case where the
finite check is small enough for `native_decide`. For general LDPC
codes, the framework provides the same proof structure, but the
ensemble verification is left to external tools.

**Zero `sorry`. Standard axioms only.** (This file proves no new theorem;
its content is documentation referring to existing
`GenericReachableBridge` proofs.)
-/

namespace QStab.Paper.LDPCFramework

open QStab.Paper.GenericReachableBridge

/-!
The following identities re-state existing theorems to make the
CSS-generic claim explicit. -/

/-- The framework's main theorem applies to any QECParams P (CSS or
    not), regardless of its origin (surface, BB, LP, ...). -/
theorem framework_applies_to_any_CSS
    (P : QECParams)
    (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks)
    (isSuccess : ErrorVec P.n → Bool)
    (h_finite_check :
      ∀ E ∈ reachableE allHooks P.C_budget, isSuccess E = false) :
    ∀ (s : State P),
      MultiStep P (.active (State.init P)) (.active s) →
      isSuccess s.E_tilde = false :=
  nonSuccess_op_d_circ_ge_d P allHooks h_bound isSuccess h_finite_check

end QStab.Paper.LDPCFramework
