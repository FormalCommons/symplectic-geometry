/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Circle.Loop

/-!
# Powers of the standard quotient of the unit interval onto the circle

Tau Ceti's `TauCeti.unitToCircle : C(I, Circle)` sends `t` to `e^{2πit}`. This file computes its
integer powers pointwise.

## Main results

* `TauCeti.unitToCircle_zpow`: `unitToCircle t ^ k = e^{2πikt}`.
-/

public section

open unitInterval

namespace TauCeti

/-- The `k`-th power of the point `e^{2πit}` of the circle is `e^{2πikt}`. -/
theorem unitToCircle_zpow (k : ℤ) (t : I) :
    unitToCircle t ^ k = Circle.exp (2 * Real.pi * k * t) := by
  rw [unitToCircle_apply, ← Circle.exp_zsmul, zsmul_eq_mul]
  ring_nf

end TauCeti

end
