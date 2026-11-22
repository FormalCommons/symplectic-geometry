/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Separating duals along injective continuous linear maps

If a topological module `W` has a separating dual and `f : V →L[R] W` is injective, then `V`
has a separating dual too: a functional on `W` that does not vanish at `f x` gives, by
composition with `f`, a functional on `V` that does not vanish at `x`. In particular a separating
dual is carried along a continuous linear equivalence.

## Main results

* `SeparatingDual.of_injective`: a separating dual pulls back along an injective continuous
  linear map.
-/

public section

namespace SeparatingDual

variable {R V W : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup V] [TopologicalSpace V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [Module R W]

/-- A module that maps injectively and continuously linearly into a module with separating dual
has a separating dual. -/
theorem of_injective [SeparatingDual R W] (f : V →L[R] W) (hf : Function.Injective f) :
    SeparatingDual R V where
  exists_ne_zero' x hx := by
    obtain ⟨g, hg⟩ := exists_ne_zero (R := R) ((map_ne_zero_iff f hf).2 hx)
    exact ⟨g.comp f, hg⟩

end SeparatingDual

end
