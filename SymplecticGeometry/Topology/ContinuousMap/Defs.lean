/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Bundled continuous maps

A complement to Mathlib's `Mathlib/Topology/ContinuousMap/Defs.lean`.

## Main results

* `ContinuousMap.ofClass_eq_self`: the bundled continuous map `ContinuousMap.ofClass f` of a
  map `f` that is already a `C(X, Y)` is `f` itself, as a `simp` lemma. It lets `simp` close
  goals left by lemmas whose statements cast a map of any `ContinuousMapClass` to `C(X, Y)`,
  when they are used with a bundled continuous map.

This follows Mathlib's `OrderHom.coe_eq` for monotone maps.
-/

public section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The bundled continuous map of a bundled continuous map `f` is `f`. -/
@[simp]
theorem ofClass_eq_self (f : C(X, Y)) : ContinuousMap.ofClass f = f :=
  rfl

end ContinuousMap

end
