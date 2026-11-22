/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Orientation.TopForm

/-!
# The outward-normal orientation of a sphere and its volume form

Tau Ceti orients the unit sphere of an oriented real inner product space `E` of dimension `n + 1`
by the outward normal (`Orientation.sphereOrientation`), and gives the sphere the nowhere-vanishing
top form `Orientation.sphereVolumeForm`, `vol(x, ·, …, ·)`. It does not expose the definition of
the orientation. This file proves that the two agree:

* `Orientation.sphereOrientation_eq_ofTopForm`: the outward-normal orientation is the orientation
  `Manifold.Orientation.ofTopForm` defined by `sphereVolumeForm`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (the outward-normal orientation of the sphere).
-/

public section

open Metric TauCeti
open scoped Manifold

namespace Orientation

/-- The outward-normal orientation of the unit sphere is the orientation of its volume form
`Orientation.sphereVolumeForm`. -/
theorem sphereOrientation_eq_ofTopForm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (o : Orientation ℝ E (Fin (n + 1))) :
    o.sphereOrientation = Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin
      o.sphereVolumeForm.val (o.sphereVolumeForm.isSmoothForm.of_le zero_le)
      o.sphereVolumeForm_apply_ne_zero := by
  ext u
  set o' := Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin o.sphereVolumeForm.val
    (o.sphereVolumeForm.isSmoothForm.of_le zero_le) o.sphereVolumeForm_apply_ne_zero
  let b := Module.finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) u)
    (finrank_euclideanSpace_fin (𝕜 := ℝ))
  -- A tangent basis is positive for both orientations exactly when `vol(u, b₁, …, bₙ) > 0`.
  have h : b.orientation = o.sphereOrientation.orientationAt u ↔
      b.orientation = o'.orientationAt u := by
    rw [o.orientation_eq_orientationAt_sphereOrientation_iff,
      Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff,
      Orientation.sphereVolumeForm_apply]
  have hcard (o'' : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) :=
    Nat.card_eq_fintype_card.trans (o''.finrank_tangentSpace_eq u).symm
  rcases b.orientation.eq_or_eq_neg (o.sphereOrientation.orientationAt u)
    (hcard o.sphereOrientation) with hb | hb
  · exact hb.symm.trans (h.1 hb)
  · rcases b.orientation.eq_or_eq_neg (o'.orientationAt u) (hcard o') with hb' | hb'
    · exact absurd (h.2 hb') (hb ▸ (Module.Ray.ne_neg_self _).symm)
    · exact neg_injective (hb.symm.trans hb')

end Orientation

end
