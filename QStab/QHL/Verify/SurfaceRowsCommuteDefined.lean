import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Leaves
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Dispatch
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.TypeClosers
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.BulkBulkCombos
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.BulkBoundaryCombos
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.NonAdjacentPins
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.NonAdjacentClosers
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.DispatcherPrereqs
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Dispatchers
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Router
import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Assembly

/-!
# Surface rows-commute definedness (module index)

Barrel over the small single-concern files under `SurfaceRowsCommuteDefined/`, built in
dependency order (leaves → dispatch → closers → overlap combos → non-adjacent → dispatchers
→ router → assembly).  Establishes `rowsCommuteSym_WF` (pairwise generated-row commutation is
computationally well-formed) and the `codeLevelDefined` assembly it feeds.
-/
