/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological

/-!
# The zero section of the model blowup as a symplectic submanifold

For `n : ℕ` and `l : ℝ`, the real zero section `zeroSectionRealEmbedding n` of the model blowup
`BlowupModel n` (`Geometry/Manifold/Complex/Blowup/Tautological.lean`) pulls the form
`ω̃_l = blowupForm n l` back to `l² ω_FS`. So for `l ≠ 0` it has symplectic tangent images. Both
the neighbourhood theorem for the divisor (`Blowup/DivisorNeighborhood.lean`) and the blowup of
weight `l` (`Blowup/Weight/Basic.lean`) use this.

## Main results

* `SymplecticGeometry.BlowupModel.mpullback_zeroSectionRealEmbedding_blowupForm`: the real zero
  section pulls `ω̃_l` back to `l² ω_FS`, by `mpullback_zeroSection_blowupForm`.
* `SymplecticGeometry.BlowupModel.hasSymplecticTangentImages_zeroSectionRealEmbedding`: for
  `l ≠ 0`, it has symplectic tangent images for `ω̃_l`, by
  `hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open Projectivization TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace BlowupModel

variable {n : ℕ}

/-- The real zero section of the model blowup pulls `ω̃_l = blowupForm n l` back to `l² ω_FS`. -/
theorem mpullback_zeroSectionRealEmbedding_blowupForm (l : ℝ) :
    SmoothForm.mpullback (zeroSectionRealEmbedding n) (zeroSectionRealEmbedding n).contMDiff
        (blowupForm n l) =
      l ^ 2 • fubiniStudyForm n :=
  (SmoothForm.mpullback_congr _ _ (coe_zeroSectionRealEmbedding n) _).trans
    (mpullback_zeroSection_blowupForm l)

/-- For `l ≠ 0`, the zero section of the model blowup has symplectic tangent images for the
symplectic form `ω̃_l = blowupForm n l`. -/
theorem hasSymplecticTangentImages_zeroSectionRealEmbedding {l : ℝ} (hl : l ≠ 0) :
    (isSymplectic_blowupForm (n := n) hl).isNondegenerate.HasSymplecticTangentImages
      𝓘(ℝ, Fin n → ℂ) (zeroSectionRealEmbedding n) :=
  hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm _ _ hl
    (mpullback_zeroSectionRealEmbedding_blowupForm l)

end BlowupModel

end SymplecticGeometry

end
