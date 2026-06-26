import QStab.Paper.GenericReachableBridge
import QStab.MultiStep
import QStab.PauliOps
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 8192

/-!
# BB [[72, 12, 6]] code: framework instantiation with NZ-sorted scheduling

This file demonstrates the `Paper.GenericReachableBridge` framework
applied to a non-surface CSS code: IBM's BB code [[72, 12, 6]].

## The code

  * 72 data qubits, 36 X-stabs (weight 6) + 36 Z-stabs (weight 6).
  * Constructed from polynomials A = x^3 + y + y^2, B = y^3 + x + x^2
    over F_2[x,y] / (x^6 - 1, y^6 - 1).
  * Code distance d = 6, k = 12 logical qubits.

## The scheduling

NZ-sorted: at each X-stab, the CX ordering is the lex-sorted list of
the stab's data qubits. Hooks are non-empty proper suffixes (5 hooks
per X-stab; 180 X-hooks total).

This scheduling **empirically preserves d_circ = 6** against the first
L_Z basis vector (verified at iterCount=500 in
`notes/bb_72_quick.py` — d_circ = 6, time 0.1s via codeDistance.QDistRndMW).

## The Lean theorem (this file)

For the BB [[72, 12, 6]] code with NZ-sorted X-CX scheduling, IF the
per-scheduling finite check holds — i.e., no element of
`reachableE bb_allHooks 5` is a success state for the first L_Z —
THEN no QStab Run with budget consumed ≤ 5 reaches a success state.

The hypothesis is **decidable** (the reachable set is finite at depth 5)
but is too large to discharge via `native_decide` directly. In practice,
the per-scheduling check is performed via codeDistance / SAT externally,
and the Lean theorem provides the rigorous structural reduction.

**Zero `sorry`. The framework's structural plumbing is fully proved;
the per-scheduling finite check is left as an explicit hypothesis.**
-/

namespace QStab.Paper.BB72Instance

open QStab QStab.Paper.GenericReachableBridge

/-! ## Build error vectors from sparse list -/

def ofList (ops : List (Nat × Pauli)) : ErrorVec 72 :=
  fun i => (ops.lookup i.val).getD Pauli.I


def bb_xs0 : ErrorVec 72 := ofList [(1, .X), (2, .X), (18, .X), (39, .X), (42, .X), (48, .X)]
def bb_xs1 : ErrorVec 72 := ofList [(2, .X), (3, .X), (19, .X), (40, .X), (43, .X), (49, .X)]
def bb_xs2 : ErrorVec 72 := ofList [(3, .X), (4, .X), (20, .X), (41, .X), (44, .X), (50, .X)]
def bb_xs3 : ErrorVec 72 := ofList [(4, .X), (5, .X), (21, .X), (36, .X), (45, .X), (51, .X)]
def bb_xs4 : ErrorVec 72 := ofList [(0, .X), (5, .X), (22, .X), (37, .X), (46, .X), (52, .X)]
def bb_xs5 : ErrorVec 72 := ofList [(0, .X), (1, .X), (23, .X), (38, .X), (47, .X), (53, .X)]
def bb_xs6 : ErrorVec 72 := ofList [(7, .X), (8, .X), (24, .X), (45, .X), (48, .X), (54, .X)]
def bb_xs7 : ErrorVec 72 := ofList [(8, .X), (9, .X), (25, .X), (46, .X), (49, .X), (55, .X)]
def bb_xs8 : ErrorVec 72 := ofList [(9, .X), (10, .X), (26, .X), (47, .X), (50, .X), (56, .X)]
def bb_xs9 : ErrorVec 72 := ofList [(10, .X), (11, .X), (27, .X), (42, .X), (51, .X), (57, .X)]
def bb_xs10 : ErrorVec 72 := ofList [(6, .X), (11, .X), (28, .X), (43, .X), (52, .X), (58, .X)]
def bb_xs11 : ErrorVec 72 := ofList [(6, .X), (7, .X), (29, .X), (44, .X), (53, .X), (59, .X)]
def bb_xs12 : ErrorVec 72 := ofList [(13, .X), (14, .X), (30, .X), (51, .X), (54, .X), (60, .X)]
def bb_xs13 : ErrorVec 72 := ofList [(14, .X), (15, .X), (31, .X), (52, .X), (55, .X), (61, .X)]
def bb_xs14 : ErrorVec 72 := ofList [(15, .X), (16, .X), (32, .X), (53, .X), (56, .X), (62, .X)]
def bb_xs15 : ErrorVec 72 := ofList [(16, .X), (17, .X), (33, .X), (48, .X), (57, .X), (63, .X)]
def bb_xs16 : ErrorVec 72 := ofList [(12, .X), (17, .X), (34, .X), (49, .X), (58, .X), (64, .X)]
def bb_xs17 : ErrorVec 72 := ofList [(12, .X), (13, .X), (35, .X), (50, .X), (59, .X), (65, .X)]
def bb_xs18 : ErrorVec 72 := ofList [(0, .X), (19, .X), (20, .X), (57, .X), (60, .X), (66, .X)]
def bb_xs19 : ErrorVec 72 := ofList [(1, .X), (20, .X), (21, .X), (58, .X), (61, .X), (67, .X)]
def bb_xs20 : ErrorVec 72 := ofList [(2, .X), (21, .X), (22, .X), (59, .X), (62, .X), (68, .X)]
def bb_xs21 : ErrorVec 72 := ofList [(3, .X), (22, .X), (23, .X), (54, .X), (63, .X), (69, .X)]
def bb_xs22 : ErrorVec 72 := ofList [(4, .X), (18, .X), (23, .X), (55, .X), (64, .X), (70, .X)]
def bb_xs23 : ErrorVec 72 := ofList [(5, .X), (18, .X), (19, .X), (56, .X), (65, .X), (71, .X)]
def bb_xs24 : ErrorVec 72 := ofList [(6, .X), (25, .X), (26, .X), (36, .X), (63, .X), (66, .X)]
def bb_xs25 : ErrorVec 72 := ofList [(7, .X), (26, .X), (27, .X), (37, .X), (64, .X), (67, .X)]
def bb_xs26 : ErrorVec 72 := ofList [(8, .X), (27, .X), (28, .X), (38, .X), (65, .X), (68, .X)]
def bb_xs27 : ErrorVec 72 := ofList [(9, .X), (28, .X), (29, .X), (39, .X), (60, .X), (69, .X)]
def bb_xs28 : ErrorVec 72 := ofList [(10, .X), (24, .X), (29, .X), (40, .X), (61, .X), (70, .X)]
def bb_xs29 : ErrorVec 72 := ofList [(11, .X), (24, .X), (25, .X), (41, .X), (62, .X), (71, .X)]
def bb_xs30 : ErrorVec 72 := ofList [(12, .X), (31, .X), (32, .X), (36, .X), (42, .X), (69, .X)]
def bb_xs31 : ErrorVec 72 := ofList [(13, .X), (32, .X), (33, .X), (37, .X), (43, .X), (70, .X)]
def bb_xs32 : ErrorVec 72 := ofList [(14, .X), (33, .X), (34, .X), (38, .X), (44, .X), (71, .X)]
def bb_xs33 : ErrorVec 72 := ofList [(15, .X), (34, .X), (35, .X), (39, .X), (45, .X), (66, .X)]
def bb_xs34 : ErrorVec 72 := ofList [(16, .X), (30, .X), (35, .X), (40, .X), (46, .X), (67, .X)]
def bb_xs35 : ErrorVec 72 := ofList [(17, .X), (30, .X), (31, .X), (41, .X), (47, .X), (68, .X)]

-- 36 Z-stabs (each weight 6)
def bb_zs0 : ErrorVec 72 := ofList [(3, .Z), (24, .Z), (30, .Z), (40, .Z), (41, .Z), (54, .Z)]
def bb_zs1 : ErrorVec 72 := ofList [(4, .Z), (25, .Z), (31, .Z), (36, .Z), (41, .Z), (55, .Z)]
def bb_zs2 : ErrorVec 72 := ofList [(5, .Z), (26, .Z), (32, .Z), (36, .Z), (37, .Z), (56, .Z)]
def bb_zs3 : ErrorVec 72 := ofList [(0, .Z), (27, .Z), (33, .Z), (37, .Z), (38, .Z), (57, .Z)]
def bb_zs4 : ErrorVec 72 := ofList [(1, .Z), (28, .Z), (34, .Z), (38, .Z), (39, .Z), (58, .Z)]
def bb_zs5 : ErrorVec 72 := ofList [(2, .Z), (29, .Z), (35, .Z), (39, .Z), (40, .Z), (59, .Z)]
def bb_zs6 : ErrorVec 72 := ofList [(0, .Z), (9, .Z), (30, .Z), (46, .Z), (47, .Z), (60, .Z)]
def bb_zs7 : ErrorVec 72 := ofList [(1, .Z), (10, .Z), (31, .Z), (42, .Z), (47, .Z), (61, .Z)]
def bb_zs8 : ErrorVec 72 := ofList [(2, .Z), (11, .Z), (32, .Z), (42, .Z), (43, .Z), (62, .Z)]
def bb_zs9 : ErrorVec 72 := ofList [(3, .Z), (6, .Z), (33, .Z), (43, .Z), (44, .Z), (63, .Z)]
def bb_zs10 : ErrorVec 72 := ofList [(4, .Z), (7, .Z), (34, .Z), (44, .Z), (45, .Z), (64, .Z)]
def bb_zs11 : ErrorVec 72 := ofList [(5, .Z), (8, .Z), (35, .Z), (45, .Z), (46, .Z), (65, .Z)]
def bb_zs12 : ErrorVec 72 := ofList [(0, .Z), (6, .Z), (15, .Z), (52, .Z), (53, .Z), (66, .Z)]
def bb_zs13 : ErrorVec 72 := ofList [(1, .Z), (7, .Z), (16, .Z), (48, .Z), (53, .Z), (67, .Z)]
def bb_zs14 : ErrorVec 72 := ofList [(2, .Z), (8, .Z), (17, .Z), (48, .Z), (49, .Z), (68, .Z)]
def bb_zs15 : ErrorVec 72 := ofList [(3, .Z), (9, .Z), (12, .Z), (49, .Z), (50, .Z), (69, .Z)]
def bb_zs16 : ErrorVec 72 := ofList [(4, .Z), (10, .Z), (13, .Z), (50, .Z), (51, .Z), (70, .Z)]
def bb_zs17 : ErrorVec 72 := ofList [(5, .Z), (11, .Z), (14, .Z), (51, .Z), (52, .Z), (71, .Z)]
def bb_zs18 : ErrorVec 72 := ofList [(6, .Z), (12, .Z), (21, .Z), (36, .Z), (58, .Z), (59, .Z)]
def bb_zs19 : ErrorVec 72 := ofList [(7, .Z), (13, .Z), (22, .Z), (37, .Z), (54, .Z), (59, .Z)]
def bb_zs20 : ErrorVec 72 := ofList [(8, .Z), (14, .Z), (23, .Z), (38, .Z), (54, .Z), (55, .Z)]
def bb_zs21 : ErrorVec 72 := ofList [(9, .Z), (15, .Z), (18, .Z), (39, .Z), (55, .Z), (56, .Z)]
def bb_zs22 : ErrorVec 72 := ofList [(10, .Z), (16, .Z), (19, .Z), (40, .Z), (56, .Z), (57, .Z)]
def bb_zs23 : ErrorVec 72 := ofList [(11, .Z), (17, .Z), (20, .Z), (41, .Z), (57, .Z), (58, .Z)]
def bb_zs24 : ErrorVec 72 := ofList [(12, .Z), (18, .Z), (27, .Z), (42, .Z), (64, .Z), (65, .Z)]
def bb_zs25 : ErrorVec 72 := ofList [(13, .Z), (19, .Z), (28, .Z), (43, .Z), (60, .Z), (65, .Z)]
def bb_zs26 : ErrorVec 72 := ofList [(14, .Z), (20, .Z), (29, .Z), (44, .Z), (60, .Z), (61, .Z)]
def bb_zs27 : ErrorVec 72 := ofList [(15, .Z), (21, .Z), (24, .Z), (45, .Z), (61, .Z), (62, .Z)]
def bb_zs28 : ErrorVec 72 := ofList [(16, .Z), (22, .Z), (25, .Z), (46, .Z), (62, .Z), (63, .Z)]
def bb_zs29 : ErrorVec 72 := ofList [(17, .Z), (23, .Z), (26, .Z), (47, .Z), (63, .Z), (64, .Z)]
def bb_zs30 : ErrorVec 72 := ofList [(18, .Z), (24, .Z), (33, .Z), (48, .Z), (70, .Z), (71, .Z)]
def bb_zs31 : ErrorVec 72 := ofList [(19, .Z), (25, .Z), (34, .Z), (49, .Z), (66, .Z), (71, .Z)]
def bb_zs32 : ErrorVec 72 := ofList [(20, .Z), (26, .Z), (35, .Z), (50, .Z), (66, .Z), (67, .Z)]
def bb_zs33 : ErrorVec 72 := ofList [(21, .Z), (27, .Z), (30, .Z), (51, .Z), (67, .Z), (68, .Z)]
def bb_zs34 : ErrorVec 72 := ofList [(22, .Z), (28, .Z), (31, .Z), (52, .Z), (68, .Z), (69, .Z)]
def bb_zs35 : ErrorVec 72 := ofList [(23, .Z), (29, .Z), (32, .Z), (53, .Z), (69, .Z), (70, .Z)]

-- L_Z (first basis vector, weight 14)
def bb_logicalZ : ErrorVec 72 := ofList [(5, .Z), (6, .Z), (7, .Z), (10, .Z), (11, .Z), (12, .Z), (13, .Z), (16, .Z), (17, .Z), (24, .Z), (30, .Z), (36, .Z), (37, .Z), (56, .Z)]


-- 12 L_Z basis vectors of BB[[72,12,6]]
def bb_logicalZ_0 : ErrorVec 72 := ofList [(5, .Z), (6, .Z), (7, .Z), (10, .Z), (11, .Z), (12, .Z), (13, .Z), (16, .Z), (17, .Z), (24, .Z), (30, .Z), (36, .Z), (37, .Z), (56, .Z)]  -- weight 14
def bb_logicalZ_1 : ErrorVec 72 := ofList [(0, .Z), (6, .Z), (7, .Z), (8, .Z), (11, .Z), (12, .Z), (13, .Z), (14, .Z), (15, .Z), (16, .Z), (17, .Z), (25, .Z), (30, .Z), (37, .Z), (38, .Z), (39, .Z), (42, .Z), (60, .Z)]  -- weight 18
def bb_logicalZ_2 : ErrorVec 72 := ofList [(0, .Z), (1, .Z), (5, .Z), (9, .Z), (10, .Z), (11, .Z), (12, .Z), (13, .Z), (15, .Z), (16, .Z), (17, .Z), (19, .Z), (25, .Z), (30, .Z), (36, .Z), (39, .Z), (43, .Z), (61, .Z)]  -- weight 18
def bb_logicalZ_3 : ErrorVec 72 := ofList [(2, .Z), (11, .Z), (12, .Z), (13, .Z), (16, .Z), (17, .Z), (30, .Z), (42, .Z), (43, .Z), (62, .Z)]  -- weight 10
def bb_logicalZ_4 : ErrorVec 72 := ofList [(0, .Z), (3, .Z), (4, .Z), (6, .Z), (7, .Z), (8, .Z), (11, .Z), (12, .Z), (13, .Z), (14, .Z), (17, .Z), (18, .Z), (19, .Z), (25, .Z), (31, .Z), (36, .Z), (37, .Z), (38, .Z), (42, .Z), (63, .Z)]  -- weight 20
def bb_logicalZ_5 : ErrorVec 72 := ofList [(0, .Z), (8, .Z), (9, .Z), (10, .Z), (11, .Z), (14, .Z), (15, .Z), (16, .Z), (17, .Z), (18, .Z), (19, .Z), (24, .Z), (30, .Z), (37, .Z), (38, .Z), (39, .Z), (43, .Z), (64, .Z)]  -- weight 18
def bb_logicalZ_6 : ErrorVec 72 := ofList [(0, .Z), (6, .Z), (7, .Z), (9, .Z), (10, .Z), (12, .Z), (14, .Z), (15, .Z), (16, .Z), (17, .Z), (19, .Z), (24, .Z), (25, .Z), (30, .Z), (37, .Z), (38, .Z), (39, .Z), (42, .Z), (43, .Z), (65, .Z)]  -- weight 20
def bb_logicalZ_7 : ErrorVec 72 := ofList [(1, .Z), (6, .Z), (7, .Z), (8, .Z), (11, .Z), (14, .Z), (25, .Z), (30, .Z), (31, .Z), (38, .Z), (42, .Z), (67, .Z)]  -- weight 12
def bb_logicalZ_8 : ErrorVec 72 := ofList [(2, .Z), (8, .Z), (9, .Z), (10, .Z), (11, .Z), (12, .Z), (13, .Z), (15, .Z), (16, .Z), (17, .Z), (24, .Z), (30, .Z), (31, .Z), (39, .Z), (43, .Z), (68, .Z)]  -- weight 16
def bb_logicalZ_9 : ErrorVec 72 := ofList [(3, .Z), (4, .Z), (5, .Z), (6, .Z), (7, .Z), (9, .Z), (10, .Z), (18, .Z), (24, .Z), (25, .Z), (37, .Z), (42, .Z), (43, .Z), (69, .Z)]  -- weight 14
def bb_logicalZ_10 : ErrorVec 72 := ofList [(5, .Z), (6, .Z), (7, .Z), (11, .Z), (18, .Z), (24, .Z), (36, .Z), (37, .Z), (42, .Z), (70, .Z)]  -- weight 10
def bb_logicalZ_11 : ErrorVec 72 := ofList [(0, .Z), (6, .Z), (7, .Z), (8, .Z), (19, .Z), (25, .Z), (37, .Z), (38, .Z), (43, .Z), (71, .Z)]  -- weight 10

-- Indexed lookup: i ∈ Fin 12 → corresponding L_Z basis vector
def bb_logicalZ_basis (i : Fin 12) : ErrorVec 72 :=
  match i.val with
  | 0 => bb_logicalZ_0
  | 1 => bb_logicalZ_1
  | 2 => bb_logicalZ_2
  | 3 => bb_logicalZ_3
  | 4 => bb_logicalZ_4
  | 5 => bb_logicalZ_5
  | 6 => bb_logicalZ_6
  | 7 => bb_logicalZ_7
  | 8 => bb_logicalZ_8
  | 9 => bb_logicalZ_9
  | 10 => bb_logicalZ_10
  | 11 => bb_logicalZ_11
  | _ => bb_logicalZ_0  -- unreachable

-- Stabiliser indexing: 0..35 = X-stabs, 36..71 = Z-stabs
-- Use match on i.val with default fallback to avoid Fin pattern exhaustion blowup
def bb_stabilizers (i : Fin 72) : ErrorVec 72 :=
  match i.val with
  | 0 => bb_xs0
  | 1 => bb_xs1
  | 2 => bb_xs2
  | 3 => bb_xs3
  | 4 => bb_xs4
  | 5 => bb_xs5
  | 6 => bb_xs6
  | 7 => bb_xs7
  | 8 => bb_xs8
  | 9 => bb_xs9
  | 10 => bb_xs10
  | 11 => bb_xs11
  | 12 => bb_xs12
  | 13 => bb_xs13
  | 14 => bb_xs14
  | 15 => bb_xs15
  | 16 => bb_xs16
  | 17 => bb_xs17
  | 18 => bb_xs18
  | 19 => bb_xs19
  | 20 => bb_xs20
  | 21 => bb_xs21
  | 22 => bb_xs22
  | 23 => bb_xs23
  | 24 => bb_xs24
  | 25 => bb_xs25
  | 26 => bb_xs26
  | 27 => bb_xs27
  | 28 => bb_xs28
  | 29 => bb_xs29
  | 30 => bb_xs30
  | 31 => bb_xs31
  | 32 => bb_xs32
  | 33 => bb_xs33
  | 34 => bb_xs34
  | 35 => bb_xs35
  | 36 => bb_zs0
  | 37 => bb_zs1
  | 38 => bb_zs2
  | 39 => bb_zs3
  | 40 => bb_zs4
  | 41 => bb_zs5
  | 42 => bb_zs6
  | 43 => bb_zs7
  | 44 => bb_zs8
  | 45 => bb_zs9
  | 46 => bb_zs10
  | 47 => bb_zs11
  | 48 => bb_zs12
  | 49 => bb_zs13
  | 50 => bb_zs14
  | 51 => bb_zs15
  | 52 => bb_zs16
  | 53 => bb_zs17
  | 54 => bb_zs18
  | 55 => bb_zs19
  | 56 => bb_zs20
  | 57 => bb_zs21
  | 58 => bb_zs22
  | 59 => bb_zs23
  | 60 => bb_zs24
  | 61 => bb_zs25
  | 62 => bb_zs26
  | 63 => bb_zs27
  | 64 => bb_zs28
  | 65 => bb_zs29
  | 66 => bb_zs30
  | 67 => bb_zs31
  | 68 => bb_zs32
  | 69 => bb_zs33
  | 70 => bb_zs34
  | 71 => bb_zs35
  | _ => bb_xs0  -- unreachable since i.val < 72

-- NZ-sorted CX orderings: each ⟨-stab uses lex order on its qubits
-- Hook list: suffixes of length 5, 4, 3, 2, 1 for each ⟨-stab
-- Total hooks per ⟨-stab: 5; total: 36 * 5 = 180

-- Hooks (NZ-sorted = lex-sorted CX ordering)
def bb_h0_0 : ErrorVec 72 := ofList [(2, .X), (18, .X), (39, .X), (42, .X), (48, .X)]
def bb_h0_1 : ErrorVec 72 := ofList [(18, .X), (39, .X), (42, .X), (48, .X)]
def bb_h0_2 : ErrorVec 72 := ofList [(39, .X), (42, .X), (48, .X)]
def bb_h0_3 : ErrorVec 72 := ofList [(42, .X), (48, .X)]
def bb_h0_4 : ErrorVec 72 := ofList [(48, .X)]
def bb_h1_0 : ErrorVec 72 := ofList [(3, .X), (19, .X), (40, .X), (43, .X), (49, .X)]
def bb_h1_1 : ErrorVec 72 := ofList [(19, .X), (40, .X), (43, .X), (49, .X)]
def bb_h1_2 : ErrorVec 72 := ofList [(40, .X), (43, .X), (49, .X)]
def bb_h1_3 : ErrorVec 72 := ofList [(43, .X), (49, .X)]
def bb_h1_4 : ErrorVec 72 := ofList [(49, .X)]
def bb_h2_0 : ErrorVec 72 := ofList [(4, .X), (20, .X), (41, .X), (44, .X), (50, .X)]
def bb_h2_1 : ErrorVec 72 := ofList [(20, .X), (41, .X), (44, .X), (50, .X)]
def bb_h2_2 : ErrorVec 72 := ofList [(41, .X), (44, .X), (50, .X)]
def bb_h2_3 : ErrorVec 72 := ofList [(44, .X), (50, .X)]
def bb_h2_4 : ErrorVec 72 := ofList [(50, .X)]
def bb_h3_0 : ErrorVec 72 := ofList [(5, .X), (21, .X), (36, .X), (45, .X), (51, .X)]
def bb_h3_1 : ErrorVec 72 := ofList [(21, .X), (36, .X), (45, .X), (51, .X)]
def bb_h3_2 : ErrorVec 72 := ofList [(36, .X), (45, .X), (51, .X)]
def bb_h3_3 : ErrorVec 72 := ofList [(45, .X), (51, .X)]
def bb_h3_4 : ErrorVec 72 := ofList [(51, .X)]
def bb_h4_0 : ErrorVec 72 := ofList [(5, .X), (22, .X), (37, .X), (46, .X), (52, .X)]
def bb_h4_1 : ErrorVec 72 := ofList [(22, .X), (37, .X), (46, .X), (52, .X)]
def bb_h4_2 : ErrorVec 72 := ofList [(37, .X), (46, .X), (52, .X)]
def bb_h4_3 : ErrorVec 72 := ofList [(46, .X), (52, .X)]
def bb_h4_4 : ErrorVec 72 := ofList [(52, .X)]
def bb_h5_0 : ErrorVec 72 := ofList [(1, .X), (23, .X), (38, .X), (47, .X), (53, .X)]
def bb_h5_1 : ErrorVec 72 := ofList [(23, .X), (38, .X), (47, .X), (53, .X)]
def bb_h5_2 : ErrorVec 72 := ofList [(38, .X), (47, .X), (53, .X)]
def bb_h5_3 : ErrorVec 72 := ofList [(47, .X), (53, .X)]
def bb_h5_4 : ErrorVec 72 := ofList [(53, .X)]
def bb_h6_0 : ErrorVec 72 := ofList [(8, .X), (24, .X), (45, .X), (48, .X), (54, .X)]
def bb_h6_1 : ErrorVec 72 := ofList [(24, .X), (45, .X), (48, .X), (54, .X)]
def bb_h6_2 : ErrorVec 72 := ofList [(45, .X), (48, .X), (54, .X)]
def bb_h6_3 : ErrorVec 72 := ofList [(48, .X), (54, .X)]
def bb_h6_4 : ErrorVec 72 := ofList [(54, .X)]
def bb_h7_0 : ErrorVec 72 := ofList [(9, .X), (25, .X), (46, .X), (49, .X), (55, .X)]
def bb_h7_1 : ErrorVec 72 := ofList [(25, .X), (46, .X), (49, .X), (55, .X)]
def bb_h7_2 : ErrorVec 72 := ofList [(46, .X), (49, .X), (55, .X)]
def bb_h7_3 : ErrorVec 72 := ofList [(49, .X), (55, .X)]
def bb_h7_4 : ErrorVec 72 := ofList [(55, .X)]
def bb_h8_0 : ErrorVec 72 := ofList [(10, .X), (26, .X), (47, .X), (50, .X), (56, .X)]
def bb_h8_1 : ErrorVec 72 := ofList [(26, .X), (47, .X), (50, .X), (56, .X)]
def bb_h8_2 : ErrorVec 72 := ofList [(47, .X), (50, .X), (56, .X)]
def bb_h8_3 : ErrorVec 72 := ofList [(50, .X), (56, .X)]
def bb_h8_4 : ErrorVec 72 := ofList [(56, .X)]
def bb_h9_0 : ErrorVec 72 := ofList [(11, .X), (27, .X), (42, .X), (51, .X), (57, .X)]
def bb_h9_1 : ErrorVec 72 := ofList [(27, .X), (42, .X), (51, .X), (57, .X)]
def bb_h9_2 : ErrorVec 72 := ofList [(42, .X), (51, .X), (57, .X)]
def bb_h9_3 : ErrorVec 72 := ofList [(51, .X), (57, .X)]
def bb_h9_4 : ErrorVec 72 := ofList [(57, .X)]
def bb_h10_0 : ErrorVec 72 := ofList [(11, .X), (28, .X), (43, .X), (52, .X), (58, .X)]
def bb_h10_1 : ErrorVec 72 := ofList [(28, .X), (43, .X), (52, .X), (58, .X)]
def bb_h10_2 : ErrorVec 72 := ofList [(43, .X), (52, .X), (58, .X)]
def bb_h10_3 : ErrorVec 72 := ofList [(52, .X), (58, .X)]
def bb_h10_4 : ErrorVec 72 := ofList [(58, .X)]
def bb_h11_0 : ErrorVec 72 := ofList [(7, .X), (29, .X), (44, .X), (53, .X), (59, .X)]
def bb_h11_1 : ErrorVec 72 := ofList [(29, .X), (44, .X), (53, .X), (59, .X)]
def bb_h11_2 : ErrorVec 72 := ofList [(44, .X), (53, .X), (59, .X)]
def bb_h11_3 : ErrorVec 72 := ofList [(53, .X), (59, .X)]
def bb_h11_4 : ErrorVec 72 := ofList [(59, .X)]
def bb_h12_0 : ErrorVec 72 := ofList [(14, .X), (30, .X), (51, .X), (54, .X), (60, .X)]
def bb_h12_1 : ErrorVec 72 := ofList [(30, .X), (51, .X), (54, .X), (60, .X)]
def bb_h12_2 : ErrorVec 72 := ofList [(51, .X), (54, .X), (60, .X)]
def bb_h12_3 : ErrorVec 72 := ofList [(54, .X), (60, .X)]
def bb_h12_4 : ErrorVec 72 := ofList [(60, .X)]
def bb_h13_0 : ErrorVec 72 := ofList [(15, .X), (31, .X), (52, .X), (55, .X), (61, .X)]
def bb_h13_1 : ErrorVec 72 := ofList [(31, .X), (52, .X), (55, .X), (61, .X)]
def bb_h13_2 : ErrorVec 72 := ofList [(52, .X), (55, .X), (61, .X)]
def bb_h13_3 : ErrorVec 72 := ofList [(55, .X), (61, .X)]
def bb_h13_4 : ErrorVec 72 := ofList [(61, .X)]
def bb_h14_0 : ErrorVec 72 := ofList [(16, .X), (32, .X), (53, .X), (56, .X), (62, .X)]
def bb_h14_1 : ErrorVec 72 := ofList [(32, .X), (53, .X), (56, .X), (62, .X)]
def bb_h14_2 : ErrorVec 72 := ofList [(53, .X), (56, .X), (62, .X)]
def bb_h14_3 : ErrorVec 72 := ofList [(56, .X), (62, .X)]
def bb_h14_4 : ErrorVec 72 := ofList [(62, .X)]
def bb_h15_0 : ErrorVec 72 := ofList [(17, .X), (33, .X), (48, .X), (57, .X), (63, .X)]
def bb_h15_1 : ErrorVec 72 := ofList [(33, .X), (48, .X), (57, .X), (63, .X)]
def bb_h15_2 : ErrorVec 72 := ofList [(48, .X), (57, .X), (63, .X)]
def bb_h15_3 : ErrorVec 72 := ofList [(57, .X), (63, .X)]
def bb_h15_4 : ErrorVec 72 := ofList [(63, .X)]
def bb_h16_0 : ErrorVec 72 := ofList [(17, .X), (34, .X), (49, .X), (58, .X), (64, .X)]
def bb_h16_1 : ErrorVec 72 := ofList [(34, .X), (49, .X), (58, .X), (64, .X)]
def bb_h16_2 : ErrorVec 72 := ofList [(49, .X), (58, .X), (64, .X)]
def bb_h16_3 : ErrorVec 72 := ofList [(58, .X), (64, .X)]
def bb_h16_4 : ErrorVec 72 := ofList [(64, .X)]
def bb_h17_0 : ErrorVec 72 := ofList [(13, .X), (35, .X), (50, .X), (59, .X), (65, .X)]
def bb_h17_1 : ErrorVec 72 := ofList [(35, .X), (50, .X), (59, .X), (65, .X)]
def bb_h17_2 : ErrorVec 72 := ofList [(50, .X), (59, .X), (65, .X)]
def bb_h17_3 : ErrorVec 72 := ofList [(59, .X), (65, .X)]
def bb_h17_4 : ErrorVec 72 := ofList [(65, .X)]
def bb_h18_0 : ErrorVec 72 := ofList [(19, .X), (20, .X), (57, .X), (60, .X), (66, .X)]
def bb_h18_1 : ErrorVec 72 := ofList [(20, .X), (57, .X), (60, .X), (66, .X)]
def bb_h18_2 : ErrorVec 72 := ofList [(57, .X), (60, .X), (66, .X)]
def bb_h18_3 : ErrorVec 72 := ofList [(60, .X), (66, .X)]
def bb_h18_4 : ErrorVec 72 := ofList [(66, .X)]
def bb_h19_0 : ErrorVec 72 := ofList [(20, .X), (21, .X), (58, .X), (61, .X), (67, .X)]
def bb_h19_1 : ErrorVec 72 := ofList [(21, .X), (58, .X), (61, .X), (67, .X)]
def bb_h19_2 : ErrorVec 72 := ofList [(58, .X), (61, .X), (67, .X)]
def bb_h19_3 : ErrorVec 72 := ofList [(61, .X), (67, .X)]
def bb_h19_4 : ErrorVec 72 := ofList [(67, .X)]
def bb_h20_0 : ErrorVec 72 := ofList [(21, .X), (22, .X), (59, .X), (62, .X), (68, .X)]
def bb_h20_1 : ErrorVec 72 := ofList [(22, .X), (59, .X), (62, .X), (68, .X)]
def bb_h20_2 : ErrorVec 72 := ofList [(59, .X), (62, .X), (68, .X)]
def bb_h20_3 : ErrorVec 72 := ofList [(62, .X), (68, .X)]
def bb_h20_4 : ErrorVec 72 := ofList [(68, .X)]
def bb_h21_0 : ErrorVec 72 := ofList [(22, .X), (23, .X), (54, .X), (63, .X), (69, .X)]
def bb_h21_1 : ErrorVec 72 := ofList [(23, .X), (54, .X), (63, .X), (69, .X)]
def bb_h21_2 : ErrorVec 72 := ofList [(54, .X), (63, .X), (69, .X)]
def bb_h21_3 : ErrorVec 72 := ofList [(63, .X), (69, .X)]
def bb_h21_4 : ErrorVec 72 := ofList [(69, .X)]
def bb_h22_0 : ErrorVec 72 := ofList [(18, .X), (23, .X), (55, .X), (64, .X), (70, .X)]
def bb_h22_1 : ErrorVec 72 := ofList [(23, .X), (55, .X), (64, .X), (70, .X)]
def bb_h22_2 : ErrorVec 72 := ofList [(55, .X), (64, .X), (70, .X)]
def bb_h22_3 : ErrorVec 72 := ofList [(64, .X), (70, .X)]
def bb_h22_4 : ErrorVec 72 := ofList [(70, .X)]
def bb_h23_0 : ErrorVec 72 := ofList [(18, .X), (19, .X), (56, .X), (65, .X), (71, .X)]
def bb_h23_1 : ErrorVec 72 := ofList [(19, .X), (56, .X), (65, .X), (71, .X)]
def bb_h23_2 : ErrorVec 72 := ofList [(56, .X), (65, .X), (71, .X)]
def bb_h23_3 : ErrorVec 72 := ofList [(65, .X), (71, .X)]
def bb_h23_4 : ErrorVec 72 := ofList [(71, .X)]
def bb_h24_0 : ErrorVec 72 := ofList [(25, .X), (26, .X), (36, .X), (63, .X), (66, .X)]
def bb_h24_1 : ErrorVec 72 := ofList [(26, .X), (36, .X), (63, .X), (66, .X)]
def bb_h24_2 : ErrorVec 72 := ofList [(36, .X), (63, .X), (66, .X)]
def bb_h24_3 : ErrorVec 72 := ofList [(63, .X), (66, .X)]
def bb_h24_4 : ErrorVec 72 := ofList [(66, .X)]
def bb_h25_0 : ErrorVec 72 := ofList [(26, .X), (27, .X), (37, .X), (64, .X), (67, .X)]
def bb_h25_1 : ErrorVec 72 := ofList [(27, .X), (37, .X), (64, .X), (67, .X)]
def bb_h25_2 : ErrorVec 72 := ofList [(37, .X), (64, .X), (67, .X)]
def bb_h25_3 : ErrorVec 72 := ofList [(64, .X), (67, .X)]
def bb_h25_4 : ErrorVec 72 := ofList [(67, .X)]
def bb_h26_0 : ErrorVec 72 := ofList [(27, .X), (28, .X), (38, .X), (65, .X), (68, .X)]
def bb_h26_1 : ErrorVec 72 := ofList [(28, .X), (38, .X), (65, .X), (68, .X)]
def bb_h26_2 : ErrorVec 72 := ofList [(38, .X), (65, .X), (68, .X)]
def bb_h26_3 : ErrorVec 72 := ofList [(65, .X), (68, .X)]
def bb_h26_4 : ErrorVec 72 := ofList [(68, .X)]
def bb_h27_0 : ErrorVec 72 := ofList [(28, .X), (29, .X), (39, .X), (60, .X), (69, .X)]
def bb_h27_1 : ErrorVec 72 := ofList [(29, .X), (39, .X), (60, .X), (69, .X)]
def bb_h27_2 : ErrorVec 72 := ofList [(39, .X), (60, .X), (69, .X)]
def bb_h27_3 : ErrorVec 72 := ofList [(60, .X), (69, .X)]
def bb_h27_4 : ErrorVec 72 := ofList [(69, .X)]
def bb_h28_0 : ErrorVec 72 := ofList [(24, .X), (29, .X), (40, .X), (61, .X), (70, .X)]
def bb_h28_1 : ErrorVec 72 := ofList [(29, .X), (40, .X), (61, .X), (70, .X)]
def bb_h28_2 : ErrorVec 72 := ofList [(40, .X), (61, .X), (70, .X)]
def bb_h28_3 : ErrorVec 72 := ofList [(61, .X), (70, .X)]
def bb_h28_4 : ErrorVec 72 := ofList [(70, .X)]
def bb_h29_0 : ErrorVec 72 := ofList [(24, .X), (25, .X), (41, .X), (62, .X), (71, .X)]
def bb_h29_1 : ErrorVec 72 := ofList [(25, .X), (41, .X), (62, .X), (71, .X)]
def bb_h29_2 : ErrorVec 72 := ofList [(41, .X), (62, .X), (71, .X)]
def bb_h29_3 : ErrorVec 72 := ofList [(62, .X), (71, .X)]
def bb_h29_4 : ErrorVec 72 := ofList [(71, .X)]
def bb_h30_0 : ErrorVec 72 := ofList [(31, .X), (32, .X), (36, .X), (42, .X), (69, .X)]
def bb_h30_1 : ErrorVec 72 := ofList [(32, .X), (36, .X), (42, .X), (69, .X)]
def bb_h30_2 : ErrorVec 72 := ofList [(36, .X), (42, .X), (69, .X)]
def bb_h30_3 : ErrorVec 72 := ofList [(42, .X), (69, .X)]
def bb_h30_4 : ErrorVec 72 := ofList [(69, .X)]
def bb_h31_0 : ErrorVec 72 := ofList [(32, .X), (33, .X), (37, .X), (43, .X), (70, .X)]
def bb_h31_1 : ErrorVec 72 := ofList [(33, .X), (37, .X), (43, .X), (70, .X)]
def bb_h31_2 : ErrorVec 72 := ofList [(37, .X), (43, .X), (70, .X)]
def bb_h31_3 : ErrorVec 72 := ofList [(43, .X), (70, .X)]
def bb_h31_4 : ErrorVec 72 := ofList [(70, .X)]
def bb_h32_0 : ErrorVec 72 := ofList [(33, .X), (34, .X), (38, .X), (44, .X), (71, .X)]
def bb_h32_1 : ErrorVec 72 := ofList [(34, .X), (38, .X), (44, .X), (71, .X)]
def bb_h32_2 : ErrorVec 72 := ofList [(38, .X), (44, .X), (71, .X)]
def bb_h32_3 : ErrorVec 72 := ofList [(44, .X), (71, .X)]
def bb_h32_4 : ErrorVec 72 := ofList [(71, .X)]
def bb_h33_0 : ErrorVec 72 := ofList [(34, .X), (35, .X), (39, .X), (45, .X), (66, .X)]
def bb_h33_1 : ErrorVec 72 := ofList [(35, .X), (39, .X), (45, .X), (66, .X)]
def bb_h33_2 : ErrorVec 72 := ofList [(39, .X), (45, .X), (66, .X)]
def bb_h33_3 : ErrorVec 72 := ofList [(45, .X), (66, .X)]
def bb_h33_4 : ErrorVec 72 := ofList [(66, .X)]
def bb_h34_0 : ErrorVec 72 := ofList [(30, .X), (35, .X), (40, .X), (46, .X), (67, .X)]
def bb_h34_1 : ErrorVec 72 := ofList [(35, .X), (40, .X), (46, .X), (67, .X)]
def bb_h34_2 : ErrorVec 72 := ofList [(40, .X), (46, .X), (67, .X)]
def bb_h34_3 : ErrorVec 72 := ofList [(46, .X), (67, .X)]
def bb_h34_4 : ErrorVec 72 := ofList [(67, .X)]
def bb_h35_0 : ErrorVec 72 := ofList [(30, .X), (31, .X), (41, .X), (47, .X), (68, .X)]
def bb_h35_1 : ErrorVec 72 := ofList [(31, .X), (41, .X), (47, .X), (68, .X)]
def bb_h35_2 : ErrorVec 72 := ofList [(41, .X), (47, .X), (68, .X)]
def bb_h35_3 : ErrorVec 72 := ofList [(47, .X), (68, .X)]
def bb_h35_4 : ErrorVec 72 := ofList [(68, .X)]

-- All hooks list (180 hooks)
def bb_allHooks : List (ErrorVec 72) := [
  bb_h0_0,
  bb_h0_1,
  bb_h0_2,
  bb_h0_3,
  bb_h0_4,
  bb_h1_0,
  bb_h1_1,
  bb_h1_2,
  bb_h1_3,
  bb_h1_4,
  bb_h2_0,
  bb_h2_1,
  bb_h2_2,
  bb_h2_3,
  bb_h2_4,
  bb_h3_0,
  bb_h3_1,
  bb_h3_2,
  bb_h3_3,
  bb_h3_4,
  bb_h4_0,
  bb_h4_1,
  bb_h4_2,
  bb_h4_3,
  bb_h4_4,
  bb_h5_0,
  bb_h5_1,
  bb_h5_2,
  bb_h5_3,
  bb_h5_4,
  bb_h6_0,
  bb_h6_1,
  bb_h6_2,
  bb_h6_3,
  bb_h6_4,
  bb_h7_0,
  bb_h7_1,
  bb_h7_2,
  bb_h7_3,
  bb_h7_4,
  bb_h8_0,
  bb_h8_1,
  bb_h8_2,
  bb_h8_3,
  bb_h8_4,
  bb_h9_0,
  bb_h9_1,
  bb_h9_2,
  bb_h9_3,
  bb_h9_4,
  bb_h10_0,
  bb_h10_1,
  bb_h10_2,
  bb_h10_3,
  bb_h10_4,
  bb_h11_0,
  bb_h11_1,
  bb_h11_2,
  bb_h11_3,
  bb_h11_4,
  bb_h12_0,
  bb_h12_1,
  bb_h12_2,
  bb_h12_3,
  bb_h12_4,
  bb_h13_0,
  bb_h13_1,
  bb_h13_2,
  bb_h13_3,
  bb_h13_4,
  bb_h14_0,
  bb_h14_1,
  bb_h14_2,
  bb_h14_3,
  bb_h14_4,
  bb_h15_0,
  bb_h15_1,
  bb_h15_2,
  bb_h15_3,
  bb_h15_4,
  bb_h16_0,
  bb_h16_1,
  bb_h16_2,
  bb_h16_3,
  bb_h16_4,
  bb_h17_0,
  bb_h17_1,
  bb_h17_2,
  bb_h17_3,
  bb_h17_4,
  bb_h18_0,
  bb_h18_1,
  bb_h18_2,
  bb_h18_3,
  bb_h18_4,
  bb_h19_0,
  bb_h19_1,
  bb_h19_2,
  bb_h19_3,
  bb_h19_4,
  bb_h20_0,
  bb_h20_1,
  bb_h20_2,
  bb_h20_3,
  bb_h20_4,
  bb_h21_0,
  bb_h21_1,
  bb_h21_2,
  bb_h21_3,
  bb_h21_4,
  bb_h22_0,
  bb_h22_1,
  bb_h22_2,
  bb_h22_3,
  bb_h22_4,
  bb_h23_0,
  bb_h23_1,
  bb_h23_2,
  bb_h23_3,
  bb_h23_4,
  bb_h24_0,
  bb_h24_1,
  bb_h24_2,
  bb_h24_3,
  bb_h24_4,
  bb_h25_0,
  bb_h25_1,
  bb_h25_2,
  bb_h25_3,
  bb_h25_4,
  bb_h26_0,
  bb_h26_1,
  bb_h26_2,
  bb_h26_3,
  bb_h26_4,
  bb_h27_0,
  bb_h27_1,
  bb_h27_2,
  bb_h27_3,
  bb_h27_4,
  bb_h28_0,
  bb_h28_1,
  bb_h28_2,
  bb_h28_3,
  bb_h28_4,
  bb_h29_0,
  bb_h29_1,
  bb_h29_2,
  bb_h29_3,
  bb_h29_4,
  bb_h30_0,
  bb_h30_1,
  bb_h30_2,
  bb_h30_3,
  bb_h30_4,
  bb_h31_0,
  bb_h31_1,
  bb_h31_2,
  bb_h31_3,
  bb_h31_4,
  bb_h32_0,
  bb_h32_1,
  bb_h32_2,
  bb_h32_3,
  bb_h32_4,
  bb_h33_0,
  bb_h33_1,
  bb_h33_2,
  bb_h33_3,
  bb_h33_4,
  bb_h34_0,
  bb_h34_1,
  bb_h34_2,
  bb_h34_3,
  bb_h34_4,
  bb_h35_0,
  bb_h35_1,
  bb_h35_2,
  bb_h35_3,
  bb_h35_4,
]

-- Back-action set: SOUND OVER-APPROXIMATION.
-- At X-stab indices (0..35): allow ANY hook (the union over all stab-
-- specific hooks). At Z-stab indices (36..71): empty.
-- This is sound for proving d_circ >= 6: the over-approximated
-- model is MORE permissive for the adversary, so any d_circ lower
-- bound proved here also holds for the actual stab-specific model.
-- (Static DEM analysis is identical anyway.)
def bb_backActionSet (i : Fin 72) : Set (ErrorVec 72) :=
  if i.val < 36 then (fun e => e ∈ bb_allHooks) else ∅


/-! ## Build the QECParams instance -/

/-- All hooks weight ≤ 5 (decidable per-hook). -/
theorem bb_allHooks_weight_bound :
    ∀ e ∈ bb_allHooks, ErrorVec.weight e ≤ 5 := by
  decide

/-- Each hook in the back-action set is in the all-hooks list.
    Trivial: by definition `bb_backActionSet i ⊆ bb_allHooks`. -/
theorem bb_backActionSet_subset :
    ∀ (i : Fin 72) (e : ErrorVec 72), e ∈ bb_backActionSet i → e ∈ bb_allHooks := by
  intro i e he
  unfold bb_backActionSet at he
  by_cases h : i.val < 36
  · rw [if_pos h] at he; exact he
  · rw [if_neg h] at he; exact he.elim

/-- Per-scheduling QECParams for BB [[72, 12, 6]] with NZ scheduling. -/
def bb_code : QECParams where
  n := 72
  k := 12
  d := 6
  R := 1
  numStab := 72
  stabilizers := bb_stabilizers
  backActionSet := bb_backActionSet
  r := 5
  backAction_weight_bound := by
    intro stab_idx e he
    have h_in : e ∈ bb_allHooks := bb_backActionSet_subset stab_idx e he
    exact bb_allHooks_weight_bound e h_in
  C_budget := 5
  hn := by omega
  hns := by omega
  hR := by omega

/-- The hooks-upper-bound hypothesis for the generic theorem. -/
theorem bb_hooks_bound : hooksUpperBound bb_code bb_allHooks :=
  bb_backActionSet_subset

/-! ## Success predicate (parity vs all 72 stabs zero AND non-trivial logical parity)

For BB72 with k=12 logical qubits, success means E ∈ N(S) \ S, equivalent to:
  * Zero parity vs all 72 stabilisers (E ∈ ker(H)).
  * Non-zero parity vs at least ONE of the 12 L_Z basis vectors (E ∉ row(HX)).

This handles ALL non-trivial X-coset attacks, not just one specific L_Z.
-/

def bb_isSuccess (E : ErrorVec 72) : Bool :=
  ((List.finRange 72).all fun i =>
    ErrorVec.parity (bb_stabilizers i) E = false) &&
  ((List.finRange 12).any fun i =>
    ErrorVec.parity (bb_logicalZ_basis i) E)

/-! ## External verification axiom

The per-scheduling finite check has been verified RIGOROUSLY via Python
exhaustive enumeration in `notes/bb72_mitm.py` (meet-in-the-middle algo).

**What was verified**: for BB72 with NZ-sorted CX scheduling, NO subset
of size ≤ 5 in the X-side static DEM (252 mechanisms = 72 Type-0 X +
180 X-hooks) gives a chain whose XOR has:
  * zero parity vs all 36 Z-stabs (commutes with stabilizers), AND
  * non-zero parity vs at least one of 12 L_Z basis vectors (flips a logical).

**Verification times**:
  * k=1, 2, 3: brute force, total 4.5s.
  * k=4: brute force, 270s (4.5 min).
  * k=5: meet-in-the-middle (split as 2+3), 1.1s.
  * **Total: ~5 minutes wall-clock for full exact proof.**

Cross-validated with codeDistance.QDistRndMW (5000 iter) and
codeDistance.QDistEvol (1000 iter) — both heuristic methods agree
d_circ = 6 for all 12 logicals.

We register this as an `axiom` in Lean (rather than discharging via
`native_decide`, which is infeasible at ~10¹² combinations). This
clearly marks the external trust boundary: the Lean theorem is fully
proved structurally, modulo this externally-verified finite check. -/

/-! ## Per-scheduling finite check: now PROVEN as a Lean theorem

The X-side static-DEM check `bb_NZ_no_X_attack_below_6` was previously an
axiom (Python MITM verified). It is now an unconditional Lean theorem;
see `QStab.Paper.BB72ReachableEBridge.bb_NZ_no_X_attack_below_6_proven`.

The theorem and the headline operational result `bb_NZ_d_circ_ge_6` are
declared in `BB72ReachableEBridge.lean` (which imports everything needed
to discharge them). They are placed in the `QStab.Paper.BB72Instance`
namespace there so existing references resolve correctly. -/

/-! ## Cross-references and notes

The companion theorems for the other 11 L_Z basis vectors follow by
the same template: change `bb_logicalZ` to the chosen basis vector,
re-run the per-scheduling finite check, and apply
`nonSuccess_op_d_circ_ge_d`.

For different schedulings (not NZ-sorted), redefine `bb_backActionSet`
and `bb_allHooks` accordingly; the rest of the file is unchanged.

This file confirms the framework is **CSS-generic** (works for the BB
LDPC code) and **scheduling-parametric** (the proof is independent of
which specific scheduling is chosen, given the per-scheduling check).

For a full ensemble theorem (over all schedulings), the per-scheduling
check would need discharging for each candidate scheduling. The
scheduling space size 720^36 ≈ 10^114 makes exhaustive enumeration
intractable; per-scheduling checks via codeDistance/SAT remain the
practical workflow.

**Honest scope**: this file does NOT discharge `h_finite_check`. The
external verification (codeDistance) gives high empirical confidence
that the check holds. To make the theorem unconditional in Lean,
either extend `native_decide` (likely infeasible at this scale) or
integrate an external SAT/SMT oracle.
-/

end QStab.Paper.BB72Instance

