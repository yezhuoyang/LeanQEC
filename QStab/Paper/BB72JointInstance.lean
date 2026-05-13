import QStab.Paper.BB72Instance
import QStab.Paper.BB72ReachableEBridge
import QStab.Paper.SurfaceD3JointXZ
import QStab.Paper.GenericReachableBridge
import QStab.MultiStep
import QStab.Invariant
import Mathlib.Tactic.FinCases

/-!
# BB [[72, 12, 6]] joint X+Z theorem: full d_circ ≥ 6

Combines the X-side (`Paper.BB72Instance`) and Z-side (this file)
analyses for the IBM BB [[72, 12, 6]] code with NZ-sorted CX scheduling
on BOTH X-stabs and Z-stabs.

## What this file proves

For any QStab Run on the joint BB72 code (with both X-CX and Z-CX
NZ-sorted schedulings), no run with budget consumed ≤ 5 reaches a
success state on ANY logical operator (L_X̄, L_Z̄, or L_Ȳ = L_X̄ · L_Z̄).

Equivalently: **operational d_circ ≥ 6 for full BB72 with NZ scheduling**.

## How (united with the invariant-based framework)

1. **`Paper.GenericReachableBridge`** provides the generic bridge invariant
   (E_tilde ∈ reachableE, preserved under all Steps).

2. **xPart/zPart decomposition** (from `Paper.SurfaceD3JointXZ`): for any
   E_tilde, decompose into X-part (X-only) and Z-part (Z-only):
   - L_Z parity / Z-stab parity depend only on xPart.
   - L_X parity / X-stab parity depend only on zPart.

3. **X-side axiom** (`Paper.BB72Instance.bb_NZ_no_X_attack_below_6`):
   verified by Python exhaustive enumeration in `notes/bb72_mitm.py`.
   ~5 min wall-clock for full proof.

4. **Z-side axiom** (this file): analogous Z-side enumeration verified
   in `notes/bb72_zside_mitm.py`. Same ~5 min wall-clock.

5. **Joint headline** combines (1)+(2)+(3)+(4): no joint chain attack
   succeeds on any logical operator.

**Total external trust budget**: 2 axioms, each backed by exhaustive
Python verification (meet-in-the-middle for k=5). The structural
plumbing (bridge invariant, decomposition, parity reductions) is all
proved in Lean.

**Zero `sorry`. Two `axiom`s clearly marked.**
-/

namespace QStab.Paper.BB72JointInstance

open QStab QStab.Paper.GenericReachableBridge
     QStab.Paper.BB72Instance
     QStab.Paper.SurfaceD3JointXZ


-- Z-side: 180 Z-hooks (NZ-sorted)
def bb_zh0_0 : ErrorVec 72 := ofList [(24, .Z), (30, .Z), (40, .Z), (41, .Z), (54, .Z)]
def bb_zh0_1 : ErrorVec 72 := ofList [(30, .Z), (40, .Z), (41, .Z), (54, .Z)]
def bb_zh0_2 : ErrorVec 72 := ofList [(40, .Z), (41, .Z), (54, .Z)]
def bb_zh0_3 : ErrorVec 72 := ofList [(41, .Z), (54, .Z)]
def bb_zh0_4 : ErrorVec 72 := ofList [(54, .Z)]
def bb_zh1_0 : ErrorVec 72 := ofList [(25, .Z), (31, .Z), (36, .Z), (41, .Z), (55, .Z)]
def bb_zh1_1 : ErrorVec 72 := ofList [(31, .Z), (36, .Z), (41, .Z), (55, .Z)]
def bb_zh1_2 : ErrorVec 72 := ofList [(36, .Z), (41, .Z), (55, .Z)]
def bb_zh1_3 : ErrorVec 72 := ofList [(41, .Z), (55, .Z)]
def bb_zh1_4 : ErrorVec 72 := ofList [(55, .Z)]
def bb_zh2_0 : ErrorVec 72 := ofList [(26, .Z), (32, .Z), (36, .Z), (37, .Z), (56, .Z)]
def bb_zh2_1 : ErrorVec 72 := ofList [(32, .Z), (36, .Z), (37, .Z), (56, .Z)]
def bb_zh2_2 : ErrorVec 72 := ofList [(36, .Z), (37, .Z), (56, .Z)]
def bb_zh2_3 : ErrorVec 72 := ofList [(37, .Z), (56, .Z)]
def bb_zh2_4 : ErrorVec 72 := ofList [(56, .Z)]
def bb_zh3_0 : ErrorVec 72 := ofList [(27, .Z), (33, .Z), (37, .Z), (38, .Z), (57, .Z)]
def bb_zh3_1 : ErrorVec 72 := ofList [(33, .Z), (37, .Z), (38, .Z), (57, .Z)]
def bb_zh3_2 : ErrorVec 72 := ofList [(37, .Z), (38, .Z), (57, .Z)]
def bb_zh3_3 : ErrorVec 72 := ofList [(38, .Z), (57, .Z)]
def bb_zh3_4 : ErrorVec 72 := ofList [(57, .Z)]
def bb_zh4_0 : ErrorVec 72 := ofList [(28, .Z), (34, .Z), (38, .Z), (39, .Z), (58, .Z)]
def bb_zh4_1 : ErrorVec 72 := ofList [(34, .Z), (38, .Z), (39, .Z), (58, .Z)]
def bb_zh4_2 : ErrorVec 72 := ofList [(38, .Z), (39, .Z), (58, .Z)]
def bb_zh4_3 : ErrorVec 72 := ofList [(39, .Z), (58, .Z)]
def bb_zh4_4 : ErrorVec 72 := ofList [(58, .Z)]
def bb_zh5_0 : ErrorVec 72 := ofList [(29, .Z), (35, .Z), (39, .Z), (40, .Z), (59, .Z)]
def bb_zh5_1 : ErrorVec 72 := ofList [(35, .Z), (39, .Z), (40, .Z), (59, .Z)]
def bb_zh5_2 : ErrorVec 72 := ofList [(39, .Z), (40, .Z), (59, .Z)]
def bb_zh5_3 : ErrorVec 72 := ofList [(40, .Z), (59, .Z)]
def bb_zh5_4 : ErrorVec 72 := ofList [(59, .Z)]
def bb_zh6_0 : ErrorVec 72 := ofList [(9, .Z), (30, .Z), (46, .Z), (47, .Z), (60, .Z)]
def bb_zh6_1 : ErrorVec 72 := ofList [(30, .Z), (46, .Z), (47, .Z), (60, .Z)]
def bb_zh6_2 : ErrorVec 72 := ofList [(46, .Z), (47, .Z), (60, .Z)]
def bb_zh6_3 : ErrorVec 72 := ofList [(47, .Z), (60, .Z)]
def bb_zh6_4 : ErrorVec 72 := ofList [(60, .Z)]
def bb_zh7_0 : ErrorVec 72 := ofList [(10, .Z), (31, .Z), (42, .Z), (47, .Z), (61, .Z)]
def bb_zh7_1 : ErrorVec 72 := ofList [(31, .Z), (42, .Z), (47, .Z), (61, .Z)]
def bb_zh7_2 : ErrorVec 72 := ofList [(42, .Z), (47, .Z), (61, .Z)]
def bb_zh7_3 : ErrorVec 72 := ofList [(47, .Z), (61, .Z)]
def bb_zh7_4 : ErrorVec 72 := ofList [(61, .Z)]
def bb_zh8_0 : ErrorVec 72 := ofList [(11, .Z), (32, .Z), (42, .Z), (43, .Z), (62, .Z)]
def bb_zh8_1 : ErrorVec 72 := ofList [(32, .Z), (42, .Z), (43, .Z), (62, .Z)]
def bb_zh8_2 : ErrorVec 72 := ofList [(42, .Z), (43, .Z), (62, .Z)]
def bb_zh8_3 : ErrorVec 72 := ofList [(43, .Z), (62, .Z)]
def bb_zh8_4 : ErrorVec 72 := ofList [(62, .Z)]
def bb_zh9_0 : ErrorVec 72 := ofList [(6, .Z), (33, .Z), (43, .Z), (44, .Z), (63, .Z)]
def bb_zh9_1 : ErrorVec 72 := ofList [(33, .Z), (43, .Z), (44, .Z), (63, .Z)]
def bb_zh9_2 : ErrorVec 72 := ofList [(43, .Z), (44, .Z), (63, .Z)]
def bb_zh9_3 : ErrorVec 72 := ofList [(44, .Z), (63, .Z)]
def bb_zh9_4 : ErrorVec 72 := ofList [(63, .Z)]
def bb_zh10_0 : ErrorVec 72 := ofList [(7, .Z), (34, .Z), (44, .Z), (45, .Z), (64, .Z)]
def bb_zh10_1 : ErrorVec 72 := ofList [(34, .Z), (44, .Z), (45, .Z), (64, .Z)]
def bb_zh10_2 : ErrorVec 72 := ofList [(44, .Z), (45, .Z), (64, .Z)]
def bb_zh10_3 : ErrorVec 72 := ofList [(45, .Z), (64, .Z)]
def bb_zh10_4 : ErrorVec 72 := ofList [(64, .Z)]
def bb_zh11_0 : ErrorVec 72 := ofList [(8, .Z), (35, .Z), (45, .Z), (46, .Z), (65, .Z)]
def bb_zh11_1 : ErrorVec 72 := ofList [(35, .Z), (45, .Z), (46, .Z), (65, .Z)]
def bb_zh11_2 : ErrorVec 72 := ofList [(45, .Z), (46, .Z), (65, .Z)]
def bb_zh11_3 : ErrorVec 72 := ofList [(46, .Z), (65, .Z)]
def bb_zh11_4 : ErrorVec 72 := ofList [(65, .Z)]
def bb_zh12_0 : ErrorVec 72 := ofList [(6, .Z), (15, .Z), (52, .Z), (53, .Z), (66, .Z)]
def bb_zh12_1 : ErrorVec 72 := ofList [(15, .Z), (52, .Z), (53, .Z), (66, .Z)]
def bb_zh12_2 : ErrorVec 72 := ofList [(52, .Z), (53, .Z), (66, .Z)]
def bb_zh12_3 : ErrorVec 72 := ofList [(53, .Z), (66, .Z)]
def bb_zh12_4 : ErrorVec 72 := ofList [(66, .Z)]
def bb_zh13_0 : ErrorVec 72 := ofList [(7, .Z), (16, .Z), (48, .Z), (53, .Z), (67, .Z)]
def bb_zh13_1 : ErrorVec 72 := ofList [(16, .Z), (48, .Z), (53, .Z), (67, .Z)]
def bb_zh13_2 : ErrorVec 72 := ofList [(48, .Z), (53, .Z), (67, .Z)]
def bb_zh13_3 : ErrorVec 72 := ofList [(53, .Z), (67, .Z)]
def bb_zh13_4 : ErrorVec 72 := ofList [(67, .Z)]
def bb_zh14_0 : ErrorVec 72 := ofList [(8, .Z), (17, .Z), (48, .Z), (49, .Z), (68, .Z)]
def bb_zh14_1 : ErrorVec 72 := ofList [(17, .Z), (48, .Z), (49, .Z), (68, .Z)]
def bb_zh14_2 : ErrorVec 72 := ofList [(48, .Z), (49, .Z), (68, .Z)]
def bb_zh14_3 : ErrorVec 72 := ofList [(49, .Z), (68, .Z)]
def bb_zh14_4 : ErrorVec 72 := ofList [(68, .Z)]
def bb_zh15_0 : ErrorVec 72 := ofList [(9, .Z), (12, .Z), (49, .Z), (50, .Z), (69, .Z)]
def bb_zh15_1 : ErrorVec 72 := ofList [(12, .Z), (49, .Z), (50, .Z), (69, .Z)]
def bb_zh15_2 : ErrorVec 72 := ofList [(49, .Z), (50, .Z), (69, .Z)]
def bb_zh15_3 : ErrorVec 72 := ofList [(50, .Z), (69, .Z)]
def bb_zh15_4 : ErrorVec 72 := ofList [(69, .Z)]
def bb_zh16_0 : ErrorVec 72 := ofList [(10, .Z), (13, .Z), (50, .Z), (51, .Z), (70, .Z)]
def bb_zh16_1 : ErrorVec 72 := ofList [(13, .Z), (50, .Z), (51, .Z), (70, .Z)]
def bb_zh16_2 : ErrorVec 72 := ofList [(50, .Z), (51, .Z), (70, .Z)]
def bb_zh16_3 : ErrorVec 72 := ofList [(51, .Z), (70, .Z)]
def bb_zh16_4 : ErrorVec 72 := ofList [(70, .Z)]
def bb_zh17_0 : ErrorVec 72 := ofList [(11, .Z), (14, .Z), (51, .Z), (52, .Z), (71, .Z)]
def bb_zh17_1 : ErrorVec 72 := ofList [(14, .Z), (51, .Z), (52, .Z), (71, .Z)]
def bb_zh17_2 : ErrorVec 72 := ofList [(51, .Z), (52, .Z), (71, .Z)]
def bb_zh17_3 : ErrorVec 72 := ofList [(52, .Z), (71, .Z)]
def bb_zh17_4 : ErrorVec 72 := ofList [(71, .Z)]
def bb_zh18_0 : ErrorVec 72 := ofList [(12, .Z), (21, .Z), (36, .Z), (58, .Z), (59, .Z)]
def bb_zh18_1 : ErrorVec 72 := ofList [(21, .Z), (36, .Z), (58, .Z), (59, .Z)]
def bb_zh18_2 : ErrorVec 72 := ofList [(36, .Z), (58, .Z), (59, .Z)]
def bb_zh18_3 : ErrorVec 72 := ofList [(58, .Z), (59, .Z)]
def bb_zh18_4 : ErrorVec 72 := ofList [(59, .Z)]
def bb_zh19_0 : ErrorVec 72 := ofList [(13, .Z), (22, .Z), (37, .Z), (54, .Z), (59, .Z)]
def bb_zh19_1 : ErrorVec 72 := ofList [(22, .Z), (37, .Z), (54, .Z), (59, .Z)]
def bb_zh19_2 : ErrorVec 72 := ofList [(37, .Z), (54, .Z), (59, .Z)]
def bb_zh19_3 : ErrorVec 72 := ofList [(54, .Z), (59, .Z)]
def bb_zh19_4 : ErrorVec 72 := ofList [(59, .Z)]
def bb_zh20_0 : ErrorVec 72 := ofList [(14, .Z), (23, .Z), (38, .Z), (54, .Z), (55, .Z)]
def bb_zh20_1 : ErrorVec 72 := ofList [(23, .Z), (38, .Z), (54, .Z), (55, .Z)]
def bb_zh20_2 : ErrorVec 72 := ofList [(38, .Z), (54, .Z), (55, .Z)]
def bb_zh20_3 : ErrorVec 72 := ofList [(54, .Z), (55, .Z)]
def bb_zh20_4 : ErrorVec 72 := ofList [(55, .Z)]
def bb_zh21_0 : ErrorVec 72 := ofList [(15, .Z), (18, .Z), (39, .Z), (55, .Z), (56, .Z)]
def bb_zh21_1 : ErrorVec 72 := ofList [(18, .Z), (39, .Z), (55, .Z), (56, .Z)]
def bb_zh21_2 : ErrorVec 72 := ofList [(39, .Z), (55, .Z), (56, .Z)]
def bb_zh21_3 : ErrorVec 72 := ofList [(55, .Z), (56, .Z)]
def bb_zh21_4 : ErrorVec 72 := ofList [(56, .Z)]
def bb_zh22_0 : ErrorVec 72 := ofList [(16, .Z), (19, .Z), (40, .Z), (56, .Z), (57, .Z)]
def bb_zh22_1 : ErrorVec 72 := ofList [(19, .Z), (40, .Z), (56, .Z), (57, .Z)]
def bb_zh22_2 : ErrorVec 72 := ofList [(40, .Z), (56, .Z), (57, .Z)]
def bb_zh22_3 : ErrorVec 72 := ofList [(56, .Z), (57, .Z)]
def bb_zh22_4 : ErrorVec 72 := ofList [(57, .Z)]
def bb_zh23_0 : ErrorVec 72 := ofList [(17, .Z), (20, .Z), (41, .Z), (57, .Z), (58, .Z)]
def bb_zh23_1 : ErrorVec 72 := ofList [(20, .Z), (41, .Z), (57, .Z), (58, .Z)]
def bb_zh23_2 : ErrorVec 72 := ofList [(41, .Z), (57, .Z), (58, .Z)]
def bb_zh23_3 : ErrorVec 72 := ofList [(57, .Z), (58, .Z)]
def bb_zh23_4 : ErrorVec 72 := ofList [(58, .Z)]
def bb_zh24_0 : ErrorVec 72 := ofList [(18, .Z), (27, .Z), (42, .Z), (64, .Z), (65, .Z)]
def bb_zh24_1 : ErrorVec 72 := ofList [(27, .Z), (42, .Z), (64, .Z), (65, .Z)]
def bb_zh24_2 : ErrorVec 72 := ofList [(42, .Z), (64, .Z), (65, .Z)]
def bb_zh24_3 : ErrorVec 72 := ofList [(64, .Z), (65, .Z)]
def bb_zh24_4 : ErrorVec 72 := ofList [(65, .Z)]
def bb_zh25_0 : ErrorVec 72 := ofList [(19, .Z), (28, .Z), (43, .Z), (60, .Z), (65, .Z)]
def bb_zh25_1 : ErrorVec 72 := ofList [(28, .Z), (43, .Z), (60, .Z), (65, .Z)]
def bb_zh25_2 : ErrorVec 72 := ofList [(43, .Z), (60, .Z), (65, .Z)]
def bb_zh25_3 : ErrorVec 72 := ofList [(60, .Z), (65, .Z)]
def bb_zh25_4 : ErrorVec 72 := ofList [(65, .Z)]
def bb_zh26_0 : ErrorVec 72 := ofList [(20, .Z), (29, .Z), (44, .Z), (60, .Z), (61, .Z)]
def bb_zh26_1 : ErrorVec 72 := ofList [(29, .Z), (44, .Z), (60, .Z), (61, .Z)]
def bb_zh26_2 : ErrorVec 72 := ofList [(44, .Z), (60, .Z), (61, .Z)]
def bb_zh26_3 : ErrorVec 72 := ofList [(60, .Z), (61, .Z)]
def bb_zh26_4 : ErrorVec 72 := ofList [(61, .Z)]
def bb_zh27_0 : ErrorVec 72 := ofList [(21, .Z), (24, .Z), (45, .Z), (61, .Z), (62, .Z)]
def bb_zh27_1 : ErrorVec 72 := ofList [(24, .Z), (45, .Z), (61, .Z), (62, .Z)]
def bb_zh27_2 : ErrorVec 72 := ofList [(45, .Z), (61, .Z), (62, .Z)]
def bb_zh27_3 : ErrorVec 72 := ofList [(61, .Z), (62, .Z)]
def bb_zh27_4 : ErrorVec 72 := ofList [(62, .Z)]
def bb_zh28_0 : ErrorVec 72 := ofList [(22, .Z), (25, .Z), (46, .Z), (62, .Z), (63, .Z)]
def bb_zh28_1 : ErrorVec 72 := ofList [(25, .Z), (46, .Z), (62, .Z), (63, .Z)]
def bb_zh28_2 : ErrorVec 72 := ofList [(46, .Z), (62, .Z), (63, .Z)]
def bb_zh28_3 : ErrorVec 72 := ofList [(62, .Z), (63, .Z)]
def bb_zh28_4 : ErrorVec 72 := ofList [(63, .Z)]
def bb_zh29_0 : ErrorVec 72 := ofList [(23, .Z), (26, .Z), (47, .Z), (63, .Z), (64, .Z)]
def bb_zh29_1 : ErrorVec 72 := ofList [(26, .Z), (47, .Z), (63, .Z), (64, .Z)]
def bb_zh29_2 : ErrorVec 72 := ofList [(47, .Z), (63, .Z), (64, .Z)]
def bb_zh29_3 : ErrorVec 72 := ofList [(63, .Z), (64, .Z)]
def bb_zh29_4 : ErrorVec 72 := ofList [(64, .Z)]
def bb_zh30_0 : ErrorVec 72 := ofList [(24, .Z), (33, .Z), (48, .Z), (70, .Z), (71, .Z)]
def bb_zh30_1 : ErrorVec 72 := ofList [(33, .Z), (48, .Z), (70, .Z), (71, .Z)]
def bb_zh30_2 : ErrorVec 72 := ofList [(48, .Z), (70, .Z), (71, .Z)]
def bb_zh30_3 : ErrorVec 72 := ofList [(70, .Z), (71, .Z)]
def bb_zh30_4 : ErrorVec 72 := ofList [(71, .Z)]
def bb_zh31_0 : ErrorVec 72 := ofList [(25, .Z), (34, .Z), (49, .Z), (66, .Z), (71, .Z)]
def bb_zh31_1 : ErrorVec 72 := ofList [(34, .Z), (49, .Z), (66, .Z), (71, .Z)]
def bb_zh31_2 : ErrorVec 72 := ofList [(49, .Z), (66, .Z), (71, .Z)]
def bb_zh31_3 : ErrorVec 72 := ofList [(66, .Z), (71, .Z)]
def bb_zh31_4 : ErrorVec 72 := ofList [(71, .Z)]
def bb_zh32_0 : ErrorVec 72 := ofList [(26, .Z), (35, .Z), (50, .Z), (66, .Z), (67, .Z)]
def bb_zh32_1 : ErrorVec 72 := ofList [(35, .Z), (50, .Z), (66, .Z), (67, .Z)]
def bb_zh32_2 : ErrorVec 72 := ofList [(50, .Z), (66, .Z), (67, .Z)]
def bb_zh32_3 : ErrorVec 72 := ofList [(66, .Z), (67, .Z)]
def bb_zh32_4 : ErrorVec 72 := ofList [(67, .Z)]
def bb_zh33_0 : ErrorVec 72 := ofList [(27, .Z), (30, .Z), (51, .Z), (67, .Z), (68, .Z)]
def bb_zh33_1 : ErrorVec 72 := ofList [(30, .Z), (51, .Z), (67, .Z), (68, .Z)]
def bb_zh33_2 : ErrorVec 72 := ofList [(51, .Z), (67, .Z), (68, .Z)]
def bb_zh33_3 : ErrorVec 72 := ofList [(67, .Z), (68, .Z)]
def bb_zh33_4 : ErrorVec 72 := ofList [(68, .Z)]
def bb_zh34_0 : ErrorVec 72 := ofList [(28, .Z), (31, .Z), (52, .Z), (68, .Z), (69, .Z)]
def bb_zh34_1 : ErrorVec 72 := ofList [(31, .Z), (52, .Z), (68, .Z), (69, .Z)]
def bb_zh34_2 : ErrorVec 72 := ofList [(52, .Z), (68, .Z), (69, .Z)]
def bb_zh34_3 : ErrorVec 72 := ofList [(68, .Z), (69, .Z)]
def bb_zh34_4 : ErrorVec 72 := ofList [(69, .Z)]
def bb_zh35_0 : ErrorVec 72 := ofList [(29, .Z), (32, .Z), (53, .Z), (69, .Z), (70, .Z)]
def bb_zh35_1 : ErrorVec 72 := ofList [(32, .Z), (53, .Z), (69, .Z), (70, .Z)]
def bb_zh35_2 : ErrorVec 72 := ofList [(53, .Z), (69, .Z), (70, .Z)]
def bb_zh35_3 : ErrorVec 72 := ofList [(69, .Z), (70, .Z)]
def bb_zh35_4 : ErrorVec 72 := ofList [(70, .Z)]

-- All Z-hooks list (180 hooks)
def bb_allHooksZ : List (ErrorVec 72) := [
  bb_zh0_0,
  bb_zh0_1,
  bb_zh0_2,
  bb_zh0_3,
  bb_zh0_4,
  bb_zh1_0,
  bb_zh1_1,
  bb_zh1_2,
  bb_zh1_3,
  bb_zh1_4,
  bb_zh2_0,
  bb_zh2_1,
  bb_zh2_2,
  bb_zh2_3,
  bb_zh2_4,
  bb_zh3_0,
  bb_zh3_1,
  bb_zh3_2,
  bb_zh3_3,
  bb_zh3_4,
  bb_zh4_0,
  bb_zh4_1,
  bb_zh4_2,
  bb_zh4_3,
  bb_zh4_4,
  bb_zh5_0,
  bb_zh5_1,
  bb_zh5_2,
  bb_zh5_3,
  bb_zh5_4,
  bb_zh6_0,
  bb_zh6_1,
  bb_zh6_2,
  bb_zh6_3,
  bb_zh6_4,
  bb_zh7_0,
  bb_zh7_1,
  bb_zh7_2,
  bb_zh7_3,
  bb_zh7_4,
  bb_zh8_0,
  bb_zh8_1,
  bb_zh8_2,
  bb_zh8_3,
  bb_zh8_4,
  bb_zh9_0,
  bb_zh9_1,
  bb_zh9_2,
  bb_zh9_3,
  bb_zh9_4,
  bb_zh10_0,
  bb_zh10_1,
  bb_zh10_2,
  bb_zh10_3,
  bb_zh10_4,
  bb_zh11_0,
  bb_zh11_1,
  bb_zh11_2,
  bb_zh11_3,
  bb_zh11_4,
  bb_zh12_0,
  bb_zh12_1,
  bb_zh12_2,
  bb_zh12_3,
  bb_zh12_4,
  bb_zh13_0,
  bb_zh13_1,
  bb_zh13_2,
  bb_zh13_3,
  bb_zh13_4,
  bb_zh14_0,
  bb_zh14_1,
  bb_zh14_2,
  bb_zh14_3,
  bb_zh14_4,
  bb_zh15_0,
  bb_zh15_1,
  bb_zh15_2,
  bb_zh15_3,
  bb_zh15_4,
  bb_zh16_0,
  bb_zh16_1,
  bb_zh16_2,
  bb_zh16_3,
  bb_zh16_4,
  bb_zh17_0,
  bb_zh17_1,
  bb_zh17_2,
  bb_zh17_3,
  bb_zh17_4,
  bb_zh18_0,
  bb_zh18_1,
  bb_zh18_2,
  bb_zh18_3,
  bb_zh18_4,
  bb_zh19_0,
  bb_zh19_1,
  bb_zh19_2,
  bb_zh19_3,
  bb_zh19_4,
  bb_zh20_0,
  bb_zh20_1,
  bb_zh20_2,
  bb_zh20_3,
  bb_zh20_4,
  bb_zh21_0,
  bb_zh21_1,
  bb_zh21_2,
  bb_zh21_3,
  bb_zh21_4,
  bb_zh22_0,
  bb_zh22_1,
  bb_zh22_2,
  bb_zh22_3,
  bb_zh22_4,
  bb_zh23_0,
  bb_zh23_1,
  bb_zh23_2,
  bb_zh23_3,
  bb_zh23_4,
  bb_zh24_0,
  bb_zh24_1,
  bb_zh24_2,
  bb_zh24_3,
  bb_zh24_4,
  bb_zh25_0,
  bb_zh25_1,
  bb_zh25_2,
  bb_zh25_3,
  bb_zh25_4,
  bb_zh26_0,
  bb_zh26_1,
  bb_zh26_2,
  bb_zh26_3,
  bb_zh26_4,
  bb_zh27_0,
  bb_zh27_1,
  bb_zh27_2,
  bb_zh27_3,
  bb_zh27_4,
  bb_zh28_0,
  bb_zh28_1,
  bb_zh28_2,
  bb_zh28_3,
  bb_zh28_4,
  bb_zh29_0,
  bb_zh29_1,
  bb_zh29_2,
  bb_zh29_3,
  bb_zh29_4,
  bb_zh30_0,
  bb_zh30_1,
  bb_zh30_2,
  bb_zh30_3,
  bb_zh30_4,
  bb_zh31_0,
  bb_zh31_1,
  bb_zh31_2,
  bb_zh31_3,
  bb_zh31_4,
  bb_zh32_0,
  bb_zh32_1,
  bb_zh32_2,
  bb_zh32_3,
  bb_zh32_4,
  bb_zh33_0,
  bb_zh33_1,
  bb_zh33_2,
  bb_zh33_3,
  bb_zh33_4,
  bb_zh34_0,
  bb_zh34_1,
  bb_zh34_2,
  bb_zh34_3,
  bb_zh34_4,
  bb_zh35_0,
  bb_zh35_1,
  bb_zh35_2,
  bb_zh35_3,
  bb_zh35_4,
]

-- 12 L_X basis vectors of BB72
def bb_logicalX_0 : ErrorVec 72 := ofList [(20, .X), (23, .X), (26, .X), (29, .X), (40, .X), (41, .X), (55, .X), (56, .X)]  -- weight 8
def bb_logicalX_1 : ErrorVec 72 := ofList [(20, .X), (22, .X), (28, .X), (35, .X), (46, .X), (58, .X), (59, .X), (60, .X)]  -- weight 8
def bb_logicalX_2 : ErrorVec 72 := ofList [(21, .X), (22, .X), (23, .X), (33, .X), (34, .X), (35, .X), (40, .X), (44, .X), (46, .X), (47, .X), (48, .X), (49, .X), (50, .X), (51, .X), (52, .X), (53, .X), (54, .X), (57, .X), (58, .X), (61, .X)]  -- weight 20
def bb_logicalX_3 : ErrorVec 72 := ofList [(21, .X), (22, .X), (23, .X), (26, .X), (29, .X), (32, .X), (33, .X), (34, .X), (40, .X), (44, .X), (48, .X), (49, .X), (50, .X), (51, .X), (52, .X), (53, .X), (54, .X), (57, .X), (58, .X), (62, .X)]  -- weight 20
def bb_logicalX_4 : ErrorVec 72 := ofList [(21, .X), (22, .X), (23, .X), (33, .X), (34, .X), (35, .X), (40, .X), (45, .X), (48, .X), (49, .X), (50, .X), (51, .X), (52, .X), (53, .X), (54, .X), (57, .X), (58, .X), (63, .X)]  -- weight 18
def bb_logicalX_5 : ErrorVec 72 := ofList [(20, .X), (21, .X), (23, .X), (27, .X), (29, .X), (35, .X), (40, .X), (45, .X), (54, .X), (57, .X), (59, .X), (64, .X)]  -- weight 12
def bb_logicalX_6 : ErrorVec 72 := ofList [(27, .X), (28, .X), (29, .X), (33, .X), (34, .X), (35, .X), (44, .X), (48, .X), (49, .X), (50, .X), (51, .X), (52, .X), (53, .X), (65, .X)]  -- weight 14
def bb_logicalX_7 : ErrorVec 72 := ofList [(20, .X), (21, .X), (29, .X), (34, .X), (35, .X), (45, .X), (53, .X), (58, .X), (66, .X), (67, .X)]  -- weight 10
def bb_logicalX_8 : ErrorVec 72 := ofList [(49, .X), (50, .X), (51, .X), (52, .X), (66, .X), (68, .X)]  -- weight 6
def bb_logicalX_9 : ErrorVec 72 := ofList [(20, .X), (21, .X), (29, .X), (34, .X), (35, .X), (45, .X), (50, .X), (51, .X), (52, .X), (58, .X), (66, .X), (69, .X)]  -- weight 12
def bb_logicalX_10 : ErrorVec 72 := ofList [(48, .X), (49, .X), (50, .X), (53, .X), (66, .X), (70, .X)]  -- weight 6
def bb_logicalX_11 : ErrorVec 72 := ofList [(20, .X), (21, .X), (29, .X), (34, .X), (35, .X), (45, .X), (48, .X), (49, .X), (50, .X), (51, .X), (53, .X), (58, .X), (66, .X), (71, .X)]  -- weight 14

-- Indexed lookup for L_X basis
def bb_logicalX_basis (i : Fin 12) : ErrorVec 72 :=
  match i.val with
  | 0 => bb_logicalX_0
  | 1 => bb_logicalX_1
  | 2 => bb_logicalX_2
  | 3 => bb_logicalX_3
  | 4 => bb_logicalX_4
  | 5 => bb_logicalX_5
  | 6 => bb_logicalX_6
  | 7 => bb_logicalX_7
  | 8 => bb_logicalX_8
  | 9 => bb_logicalX_9
  | 10 => bb_logicalX_10
  | 11 => bb_logicalX_11
  | _ => bb_logicalX_0  -- unreachable


/-! ## Joint code: X-hooks at X-stab indices, Z-hooks at Z-stab indices -/

def bb_jointBackActionSet (i : Fin 72) : Set (ErrorVec 72) :=
  if i.val < 36 then (fun e => e ∈ bb_allHooks)       -- X-stab indices: X-hooks
  else (fun e => e ∈ bb_allHooksZ)                   -- Z-stab indices: Z-hooks

def bb_jointAllHooks : List (ErrorVec 72) := bb_allHooks ++ bb_allHooksZ

/-- Joint hook membership in joint allHooks. -/
theorem bb_joint_hooks_subset :
    ∀ (i : Fin 72) (e : ErrorVec 72),
      e ∈ bb_jointBackActionSet i → e ∈ bb_jointAllHooks := by
  intro i e he
  unfold bb_jointBackActionSet at he
  by_cases h : i.val < 36
  · rw [if_pos h] at he
    show e ∈ bb_allHooks ++ bb_allHooksZ
    exact List.mem_append.mpr (Or.inl he)
  · rw [if_neg h] at he
    show e ∈ bb_allHooks ++ bb_allHooksZ
    exact List.mem_append.mpr (Or.inr he)

/-- All Z-hooks weight ≤ 5 (decidable by `native_decide`). -/
theorem bb_allHooksZ_weight_bound :
    ∀ e ∈ bb_allHooksZ, ErrorVec.weight e ≤ 5 := by
  native_decide

/-- All joint hooks have weight ≤ 5 (each hook from either side). -/
theorem bb_jointAllHooks_weight_bound :
    ∀ e ∈ bb_jointAllHooks, ErrorVec.weight e ≤ 5 := by
  intro e he
  rcases List.mem_append.mp he with h_x | h_z
  · exact bb_allHooks_weight_bound e h_x
  · exact bb_allHooksZ_weight_bound e h_z

/-- Joint QECParams: full BB72 with NZ X-CX and NZ Z-CX scheduling. -/
def bb_jointCode : QECParams where
  n := 72; k := 12; d := 6; R := 1
  numStab := 72
  stabilizers := bb_stabilizers
  backActionSet := bb_jointBackActionSet
  r := 5
  backAction_weight_bound := by
    intro stab_idx e he
    have h_in : e ∈ bb_jointAllHooks := bb_joint_hooks_subset stab_idx e he
    exact bb_jointAllHooks_weight_bound e h_in
  C_budget := 5
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Z-side success predicate (analogous to bb_isSuccess) -/

/-- Success on L_X̄ side: zero parity vs all 72 stabs AND non-zero parity
    vs at least one of 12 L_X basis vectors. -/
def bb_isSuccessZside (E : ErrorVec 72) : Bool :=
  ((List.finRange 72).all fun i =>
    ErrorVec.parity (bb_stabilizers i) E = false) &&
  ((List.finRange 12).any fun i =>
    ErrorVec.parity (bb_logicalX_basis i) E)

/-! ## Per-scheduling Z-side check: PROVEN as a Lean theorem

The Z-side static-DEM check `bb_NZ_no_Z_attack_below_6` was previously an
axiom (Python MITM verified). It is now an unconditional Lean theorem;
see `QStab.Paper.BB72ReachableEBridgeZ.bb_NZ_no_Z_attack_below_6_proven`.

The theorem and the headline operational result `bb_NZ_joint_d_circ_ge_6`
are declared in `BB72ZAxiomsProven.lean`, which imports the proven Z-side
discharge. They live in this `QStab.Paper.BB72JointInstance` namespace
so existing references resolve correctly. -/

/-! ## Joint success predicate

  E reaches success on ANY logical operator iff:
    - E ∈ N(S) (zero parity vs all 72 stabs), AND
    - E flips at least one logical (any of 12 L_Z basis OR any of 12 L_X basis).

  Note: L_Y = L_X · L_Z is automatic — `parity(L_Y, E) = parity(L_X, E) ⊕
  parity(L_Z, E)`, so flipping L_Y means flipping at least one of L_X/L_Z.
-/

def bb_isSuccessJoint (E : ErrorVec 72) : Bool :=
  ((List.finRange 72).all fun i =>
    ErrorVec.parity (bb_stabilizers i) E = false) &&
  (((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalZ_basis i) E) ||
   ((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalX_basis i) E))

/-! ## Joint headline: full d_circ ≥ 6

The joint headline reduces to the X-side and Z-side axioms via:
  * If E flips some L_Z̄: xPart of E flips that L_Z̄. By X-side axiom,
    no X-only chain reaches such E. Contradicts E being in jointReachableE.
  * If E flips some L_X̄: zPart of E flips that L_X̄. By Z-side axiom,
    no Z-only chain reaches such E.
  * E in N(S) decomposes: xPart commutes with Z-stabs, zPart commutes with X-stabs.

The full decomposition lemmas are in `Paper.SurfaceD3JointXZ` (parametric
in n_qubits) and apply directly here. -/

/-! ## Hook X-only / Z-only membership (decided by `native_decide`) -/

/-- Every X-side hook is X-only (each entry is X or I). -/
theorem bb_allHooks_xOnly :
    ∀ e ∈ bb_allHooks, ∀ j : Fin 72, e j = .X ∨ e j = .I := by
  native_decide

/-- Every Z-side hook is Z-only (each entry is Z or I). -/
theorem bb_allHooksZ_zOnly :
    ∀ e ∈ bb_allHooksZ, ∀ j : Fin 72, e j = .Z ∨ e j = .I := by
  native_decide

/-! ## Per-stab X-only / Z-only (decided by `native_decide`) -/

/-- For X-stab indices (i.val < 36), the stabiliser is X-only. -/
theorem bb_stabilizers_xOnly_at_xStabIdx :
    ∀ i : Fin 72, i.val < 36 → isXOnly (bb_stabilizers i) := by
  intro i hi j
  have h_dec : ∀ i : Fin 72, i.val < 36 →
      ∀ j : Fin 72, (bb_stabilizers i) j = .X ∨ (bb_stabilizers i) j = .I := by
    native_decide
  exact h_dec i hi j

/-- For Z-stab indices (i.val ≥ 36), the stabiliser is Z-only. -/
theorem bb_stabilizers_zOnly_at_zStabIdx :
    ∀ i : Fin 72, i.val ≥ 36 → isZOnly (bb_stabilizers i) := by
  intro i hi j
  have h_dec : ∀ i : Fin 72, i.val ≥ 36 →
      ∀ j : Fin 72, (bb_stabilizers i) j = .Z ∨ (bb_stabilizers i) j = .I := by
    native_decide
  exact h_dec i hi j

/-! ## Joint bridge invariant: xPart in X-reachable, zPart in Z-reachable -/

def bb_jointBridgePred (s : State bb_jointCode) : Prop :=
  xPartE s.E_tilde ∈ reachableE bb_allHooks (bb_jointCode.C_budget - s.C) ∧
  zPartE s.E_tilde ∈ reachableE bb_allHooksZ (bb_jointCode.C_budget - s.C) ∧
  s.C ≤ bb_jointCode.C_budget

theorem bb_jointBridge_init :
    bb_jointBridgePred (State.init bb_jointCode) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (State.init bb_jointCode).E_tilde = ErrorVec.identity 72 := rfl
    have h2 : bb_jointCode.C_budget - (State.init bb_jointCode).C = 0 := by
      show bb_jointCode.C_budget - bb_jointCode.C_budget = 0; omega
    rw [h1, h2]
    show xPartE (ErrorVec.identity 72) ∈ reachableE bb_allHooks 0
    rw [xPartE_identity]
    simp [reachableE]
  · have h1 : (State.init bb_jointCode).E_tilde = ErrorVec.identity 72 := rfl
    have h2 : bb_jointCode.C_budget - (State.init bb_jointCode).C = 0 := by
      show bb_jointCode.C_budget - bb_jointCode.C_budget = 0; omega
    rw [h1, h2]
    show zPartE (ErrorVec.identity 72) ∈ reachableE bb_allHooksZ 0
    rw [zPartE_identity]
    simp [reachableE]
  · show (State.init bb_jointCode).C ≤ bb_jointCode.C_budget
    show bb_jointCode.C_budget ≤ bb_jointCode.C_budget; omega

theorem bb_jointBridge_preserve
    (s s' : State bb_jointCode)
    (h_inv : bb_jointBridgePred s)
    (hstep : Step bb_jointCode (.active s) (.active s')) :
    bb_jointBridgePred s' := by
  obtain ⟨h_in_x, h_in_z, h_C⟩ := h_inv
  set n := bb_jointCode.C_budget - s.C with h_n_def
  cases hstep with
  | type0 _ i p hp _ =>
    refine ⟨?_, ?_, ?_⟩
    · -- xPart: update by xPartL p
      have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show xPartE (ErrorVec.update s.E_tilde i p) ∈
            reachableE bb_allHooks (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n', xPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X => exact reachableE_t01 bb_allHooks n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Y => exact reachableE_t01 bb_allHooks n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Z =>
        show ErrorVec.update (xPartE s.E_tilde) i .I ∈ reachableE bb_allHooks (n + 1)
        have h_eq : ErrorVec.update (xPartE s.E_tilde) i .I = xPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact reachableE_mono bb_allHooks n (xPartE s.E_tilde) h_in_x
    · -- zPart symmetric
      have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show zPartE (ErrorVec.update s.E_tilde i p) ∈
            reachableE bb_allHooksZ (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n', zPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X =>
        show ErrorVec.update (zPartE s.E_tilde) i .I ∈ reachableE bb_allHooksZ (n + 1)
        have h_eq : ErrorVec.update (zPartE s.E_tilde) i .I = zPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact reachableE_mono bb_allHooksZ n (zPartE s.E_tilde) h_in_z
      | Y => exact reachableE_t01 bb_allHooksZ n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
      | Z => exact reachableE_t01 bb_allHooksZ n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
    · show s.C - 1 ≤ bb_jointCode.C_budget; omega
  | type1 _ i p hp _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show xPartE (ErrorVec.update s.E_tilde i p) ∈
            reachableE bb_allHooks (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n', xPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X => exact reachableE_t01 bb_allHooks n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Y => exact reachableE_t01 bb_allHooks n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Z =>
        show ErrorVec.update (xPartE s.E_tilde) i .I ∈ reachableE bb_allHooks (n + 1)
        have h_eq : ErrorVec.update (xPartE s.E_tilde) i .I = xPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact reachableE_mono bb_allHooks n (xPartE s.E_tilde) h_in_x
    · have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show zPartE (ErrorVec.update s.E_tilde i p) ∈
            reachableE bb_allHooksZ (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n', zPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X =>
        show ErrorVec.update (zPartE s.E_tilde) i .I ∈ reachableE bb_allHooksZ (n + 1)
        have h_eq : ErrorVec.update (zPartE s.E_tilde) i .I = zPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact reachableE_mono bb_allHooksZ n (zPartE s.E_tilde) h_in_z
      | Y => exact reachableE_t01 bb_allHooksZ n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
      | Z => exact reachableE_t01 bb_allHooksZ n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
    · show s.C - 1 ≤ bb_jointCode.C_budget; omega
  | type2 _ e he _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show xPartE (ErrorVec.mul e s.E_tilde) ∈
            reachableE bb_allHooks (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n', xPartE_mul]
      -- e ∈ bb_jointBackActionSet s.coord.x
      have h_e_in : e ∈ bb_jointBackActionSet s.coord.x := he
      unfold bb_jointBackActionSet at h_e_in
      by_cases h_idx : s.coord.x.val < 36
      · -- X-stab idx: e ∈ bb_allHooks (X-only)
        rw [if_pos h_idx] at h_e_in
        have h_xonly : ∀ j, e j = .X ∨ e j = .I := bb_allHooks_xOnly e h_e_in
        have h_xPart_eq : xPartE e = e := xOnly_implies_xPartE_self e h_xonly
        rw [h_xPart_eq]
        exact reachableE_t2 bb_allHooks n (xPartE s.E_tilde) e h_in_x h_e_in
      · -- Z-stab idx: e ∈ bb_allHooksZ (Z-only)
        rw [if_neg h_idx] at h_e_in
        have h_zonly : ∀ j, e j = .Z ∨ e j = .I := bb_allHooksZ_zOnly e h_e_in
        have h_xPart_eq : xPartE e = ErrorVec.identity 72 :=
          zOnly_implies_xPartE_identity e h_zonly
        rw [h_xPart_eq]
        show ErrorVec.mul (ErrorVec.identity 72) (xPartE s.E_tilde) ∈
              reachableE bb_allHooks (n + 1)
        have h_id_mul : ErrorVec.mul (ErrorVec.identity 72) (xPartE s.E_tilde) = xPartE s.E_tilde := by
          funext j
          show Pauli.mul Pauli.I (xPartE s.E_tilde j) = xPartE s.E_tilde j
          cases xPartE s.E_tilde j <;> rfl
        rw [h_id_mul]
        exact reachableE_mono bb_allHooks n (xPartE s.E_tilde) h_in_x
    · have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show zPartE (ErrorVec.mul e s.E_tilde) ∈
            reachableE bb_allHooksZ (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n', zPartE_mul]
      have h_e_in : e ∈ bb_jointBackActionSet s.coord.x := he
      unfold bb_jointBackActionSet at h_e_in
      by_cases h_idx : s.coord.x.val < 36
      · -- X-stab idx: e ∈ bb_allHooks (X-only) → zPart e = identity
        rw [if_pos h_idx] at h_e_in
        have h_xonly : ∀ j, e j = .X ∨ e j = .I := bb_allHooks_xOnly e h_e_in
        have h_zPart_eq : zPartE e = ErrorVec.identity 72 :=
          xOnly_implies_zPartE_identity e h_xonly
        rw [h_zPart_eq]
        show ErrorVec.mul (ErrorVec.identity 72) (zPartE s.E_tilde) ∈
              reachableE bb_allHooksZ (n + 1)
        have h_id_mul : ErrorVec.mul (ErrorVec.identity 72) (zPartE s.E_tilde) = zPartE s.E_tilde := by
          funext j
          show Pauli.mul Pauli.I (zPartE s.E_tilde j) = zPartE s.E_tilde j
          cases zPartE s.E_tilde j <;> rfl
        rw [h_id_mul]
        exact reachableE_mono bb_allHooksZ n (zPartE s.E_tilde) h_in_z
      · -- Z-stab idx: e ∈ bb_allHooksZ (Z-only) → zPart e = e
        rw [if_neg h_idx] at h_e_in
        have h_zonly : ∀ j, e j = .Z ∨ e j = .I := bb_allHooksZ_zOnly e h_e_in
        have h_zPart_eq : zPartE e = e := zOnly_implies_zPartE_self e h_zonly
        rw [h_zPart_eq]
        exact reachableE_t2 bb_allHooksZ n (zPartE s.E_tilde) e h_in_z h_e_in
    · show s.C - 1 ≤ bb_jointCode.C_budget; omega
  | type3 _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show xPartE s.E_tilde ∈ reachableE bb_allHooks (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n']
      exact reachableE_mono bb_allHooks n (xPartE s.E_tilde) h_in_x
    · have h_n' : bb_jointCode.C_budget - (s.C - 1) = n + 1 := by
        show bb_jointCode.C_budget - (s.C - 1) = (bb_jointCode.C_budget - s.C) + 1; omega
      show zPartE s.E_tilde ∈ reachableE bb_allHooksZ (bb_jointCode.C_budget - (s.C - 1))
      rw [h_n']
      exact reachableE_mono bb_allHooksZ n (zPartE s.E_tilde) h_in_z
    · show s.C - 1 ≤ bb_jointCode.C_budget; omega
  | measure _ nc _ =>
    refine ⟨?_, ?_, ?_⟩
    · show xPartE (measureStep bb_jointCode s nc).E_tilde ∈
            reachableE bb_allHooks
              (bb_jointCode.C_budget - (measureStep bb_jointCode s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in_x
    · show zPartE (measureStep bb_jointCode s nc).E_tilde ∈
            reachableE bb_allHooksZ
              (bb_jointCode.C_budget - (measureStep bb_jointCode s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in_z
    · show (measureStep bb_jointCode s nc).C ≤ bb_jointCode.C_budget
      rw [measureStep_C]; exact h_C

def bb_jointBridgeInv : Invariant bb_jointCode where
  holds := bb_jointBridgePred
  holds_init := bb_jointBridge_init
  preservation := bb_jointBridge_preserve

/-- Reachability of `xPart` in the X-side reachable set, for any joint state. -/
theorem bb_joint_xPart_in_X_reachable (s : State bb_jointCode)
    (hreach : MultiStep bb_jointCode (.active (State.init bb_jointCode)) (.active s)) :
    xPartE s.E_tilde ∈ reachableE bb_allHooks (bb_jointCode.C_budget - s.C) :=
  (bb_jointBridgeInv.holds_of_reachable s hreach).1

/-- Reachability of `zPart` in the Z-side reachable set, for any joint state. -/
theorem bb_joint_zPart_in_Z_reachable (s : State bb_jointCode)
    (hreach : MultiStep bb_jointCode (.active (State.init bb_jointCode)) (.active s)) :
    zPartE s.E_tilde ∈ reachableE bb_allHooksZ (bb_jointCode.C_budget - s.C) :=
  (bb_jointBridgeInv.holds_of_reachable s hreach).2.1

/-! ## Headline theorem: full d_circ ≥ 6

The headline `bb_NZ_joint_d_circ_ge_6` is now declared in
`BB72ZAxiomsProven.lean`, which can use the unconditional X-side and
Z-side proven theorems. -/

/-! ## Summary: what's proven and what's external

| Component | Status |
|---|---|
| GenericReachableBridge framework (universal) | ✅ Proved zero-sorry |
| xPart/zPart decomposition (parametric) | ✅ Proved (SurfaceD3JointXZ) |
| Joint bridge invariant for BB72 (xPart/zPart) | ✅ Proved zero-sorry (this file) |
| Per-stab X-only/Z-only at split index 36 | ✅ Proved via `native_decide` |
| Per-hook X-only/Z-only (180 + 180 hooks) | ✅ Proved via `native_decide` |
| L_Z̄ basis Z-only (12 vectors) | ✅ Proved via `native_decide` |
| L_X̄ basis X-only (12 vectors) | ✅ Proved via `native_decide` |
| X-side per-scheduling check (no ≤5 chain attacks) | 🌐 axiom (Python: ~5 min, MITM) |
| Z-side per-scheduling check (no ≤5 chain attacks) | 🌐 axiom (Python: ~5 min, MITM) |
| Joint d_circ ≥ 6 headline (united with invariant framework) | ✅ Proved (`bb_NZ_joint_d_circ_ge_6`) |

**Total external trust budget**: 2 axioms (X-side and Z-side static-DEM
exhaustive checks, both Python-verified by meet-in-the-middle).
**Total Python verification**: ~10 min wall-clock.
**Total Lean structural proof**: zero-sorry, ~330 lines combining the
GenericReachableBridge bridge invariant with the SurfaceD3JointXZ
xPart/zPart decomposition lemmas (both parametric in n_qubits and
hence reusable for BB72).

The headline `bb_NZ_joint_d_circ_ge_6` is the formal counterpart of
`SurfaceD3JointXZ.joint_nonFailing_op_d_circ_ge_3`, lifted from the
[[9, 1, 3]] surface code to the IBM BB [[72, 12, 6]] LDPC code. The
proof is fully united with the previous (invariant-based) framework:
* `bb_jointBridgeInv : Invariant bb_jointCode` is the joint bridge.
* `bb_joint_xPart_in_X_reachable` / `bb_joint_zPart_in_Z_reachable`
  extract the side-specific reachability from the joint invariant.
* The two axioms then discharge each side's finite check.
-/

end QStab.Paper.BB72JointInstance

