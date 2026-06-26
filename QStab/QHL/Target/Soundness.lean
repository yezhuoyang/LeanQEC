import QStab.QHL.Target.Deriv

/-! # Soundness of the QClifford Hoare logic (Floyd-Hoare model-theoretic layerII)

`hoare_sound_c : DerivC nq Pre c Post → ⦃Pre⦄ c ⦃Post⦄_c` — every
derivable QClifford Hoare triple is valid in the model-theoretic sense.

Mirrors `QHL.Source.hoare_sound` for QStab. Proof: by recursion on `DerivC`,
dispatching to the per-rule lemmas in `Rules.lean`.

This theorem closes the Part-III layer at the QClifford level. The
proof compiler (in `QHL/Compile/`) targets `DerivC` and the surface/HGP
end-to-end certificate extracts the triple via `hoare_sound_c`.
-/

namespace QHL.Target

open QStab.QClifford

/-- **Soundness** at the QClifford level. -/
theorem hoare_sound_c {nq : Nat}
    {Pre Post : AssertionC nq} {c : Circuit nq}
    (d : DerivC nq Pre c Post) :
    ⦃Pre⦄ c ⦃Post⦄c := by
  induction d with
  | C_Nil P => exact hoare_nil_c P
  | C_Gate g Q => exact hoare_gate_c g Q
  | C_App _ _ ih1 ih2 => exact hoare_app_c ih1 ih2
  | C_Consequence _ h_pre h_post ih => exact hoare_consequence_c ih h_pre h_post

end QHL.Target
