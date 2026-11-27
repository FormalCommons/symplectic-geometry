/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Order.OrderClosed

import SymplecticGeometry.Order.Interval.Set.Piecewise

/-!
# Gluing two functions at a point of an ordered space, near a point

For `c` in a linear order, `fun r ↦ if r ≤ c then f r else g r` is `f` up to `c` and `g` after
it. When `f` and `g` agree on an interval `(a, b)` around the cut, then in an order topology the
glued function is eventually equal to `f` near every point left of `b`, and to `g` near every
point right of `a`. The proofs apply `Set.EqOn.eqOn_ite_le_left` and
`Set.EqOn.eqOn_ite_le_right` on an open ray.

## Main results

* `Set.EqOn.eventuallyEq_ite_le_left`, `Set.EqOn.eventuallyEq_ite_le_right`: if `f` and `g`
  agree on `(a, b)` and `a ≤ c < b`, the glued function is eventually equal to `f` near every
  `x < b`, and to `g` near every `x > a`.
-/

public section

open Filter Topology

namespace Set

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] {f g : α → β} {a b c x : α}

/-- If `f` and `g` agree on `(a, b)` and `a ≤ c`, the function equal to `f` up to `c` and to `g`
after it is eventually equal to `f` near every `x < b`. -/
theorem EqOn.eventuallyEq_ite_le_left [ClosedIciTopology α] (h : EqOn f g (Ioo a b))
    (hac : a ≤ c) (hx : x < b) : (fun r ↦ if r ≤ c then f r else g r) =ᶠ[𝓝 x] f :=
  EqOn.eqOn_ite_le_left (s := Iio b) (h.mono fun _ hr ↦ mem_Ioo.2 ⟨hac.trans_lt hr.2, hr.1⟩)
    |>.eventuallyEq_of_mem (Iio_mem_nhds hx)

/-- If `f` and `g` agree on `(a, b)` and `c < b`, the function equal to `f` up to `c` and to `g`
after it is eventually equal to `g` near every `x > a`. -/
theorem EqOn.eventuallyEq_ite_le_right [ClosedIicTopology α] (h : EqOn f g (Ioo a b))
    (hcb : c < b) (hx : a < x) : (fun r ↦ if r ≤ c then f r else g r) =ᶠ[𝓝 x] g :=
  EqOn.eqOn_ite_le_right (s := Ioi a) (h.mono fun _ hr ↦ mem_Ioo.2 ⟨hr.1, hr.2.trans_lt hcb⟩)
    |>.eventuallyEq_of_mem (Ioi_mem_nhds hx)

end Set

end
