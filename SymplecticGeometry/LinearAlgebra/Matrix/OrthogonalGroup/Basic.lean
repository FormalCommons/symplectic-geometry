/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The inclusion of the special orthogonal group into the orthogonal group

Tau Ceti's `Matrix.specialOrthogonalGroup.toOrthogonalGroup : SO(n) →* O(n)` keeps the underlying
matrix of a special orthogonal matrix. This file records that it is injective.

## Main results

* `Matrix.specialOrthogonalGroup.toOrthogonalGroup_injective`: the inclusion `SO(n) →* O(n)` is
  injective.
-/

public section

namespace Matrix.specialOrthogonalGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The inclusion `SO(n) →* O(n)` is injective. -/
theorem toOrthogonalGroup_injective :
    Function.Injective (toOrthogonalGroup (n := n) (R := R)) := fun A B h ↦
  Subtype.ext <| by simpa using congrArg Subtype.val h

end Matrix.specialOrthogonalGroup

end
