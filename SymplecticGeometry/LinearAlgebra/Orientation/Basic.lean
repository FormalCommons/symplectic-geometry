/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Orientation

/-!
# Orientations of an empty index type

For an empty index type `ι`, every module has the orientation `positiveOrientation`, given by the
constant alternating map `1`. Mathlib shows that a linear equivalence carries it to the positive
orientation of the target (`Orientation.map_positiveOrientation_of_isEmpty`). This file adds the
same for a change of the empty index type (`Orientation.reindex_positiveOrientation`), and the
resulting characterizations of the orientations that these maps carry to the positive one
(`Orientation.map_eq_positiveOrientation_iff`, `Orientation.reindex_eq_positiveOrientation_iff`).
-/

public section

namespace Orientation

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {ι ι' : Type*}

/-- A change of the empty index type carries the positive orientation to the positive
orientation. -/
@[simp]
theorem reindex_positiveOrientation [IsEmpty ι] [IsEmpty ι'] (e : ι ≃ ι') :
    reindex R M e positiveOrientation = positiveOrientation :=
  (reindex_apply R M e (AlternatingMap.constLinearEquivOfIsEmpty (1 : R))
    (AlternatingMap.constLinearEquivOfIsEmpty.injective.ne one_ne_zero)).trans (by congr 1)

/-- For empty index types, a reindexed orientation is positive if and only if the orientation
is. -/
theorem reindex_eq_positiveOrientation_iff [IsEmpty ι] [IsEmpty ι'] (e : ι ≃ ι')
    (o : Orientation R M ι) :
    reindex R M e o = positiveOrientation ↔ o = positiveOrientation := by
  rw [← reindex_positiveOrientation (M := M) e, (reindex R M e).injective.eq_iff]

/-- For an empty index type, the image of an orientation under a linear equivalence is positive
if and only if the orientation is. -/
theorem map_eq_positiveOrientation_iff [IsEmpty ι] (f : M ≃ₗ[R] N) (o : Orientation R M ι) :
    map ι f o = positiveOrientation ↔ o = positiveOrientation := by
  rw [← map_positiveOrientation_of_isEmpty (ι := ι) f, (map ι f).injective.eq_iff]

end Orientation

end
