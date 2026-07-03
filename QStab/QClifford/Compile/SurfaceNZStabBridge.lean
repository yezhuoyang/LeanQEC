import QStab.QClifford.Compile.SurfaceNZSpecAlign
import QStab.QClifford.Compile.StabTransportCore

/-!
# (shim) F1 Stab-half: the `InStab` ↔ masked-product bridge

The generic content of this file (`qecMaskProd`, `InStab_iff_qecMaskProd`,
and the `ErrorVec.mul` group facts) moved to `StabTransportCore`, the
neutral transport home shared by the surface and HGP pipelines.  This file
remains as an import shim so existing consumers keep resolving.
-/
