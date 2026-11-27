/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Order.OrderClosed

/-!
# Gluing two functions at a point of an ordered space

For `c` in a linear order, `fun r ↦ if r ≤ c then f r else g r` is `f` up to `c` and `g` after
it, as in Tau Ceti's `Set.eqOn_ite_le_Ici` and `Set.MapsTo.ite_le_Icc`. When `f` and `g` agree
on an interval around the cut, the glued function is `f` or `g` on larger sets, and, in an order
topology, near every point to the left or to the right of where they agree. The first two
results below are the two directions of Mathlib's `Set.eqOn_piecewise` for `Iic c`, written for
the `if` form that proofs build.

## Main results

* `Set.EqOn.eqOn_ite_le_left`, `Set.EqOn.eqOn_ite_le_right`: the glued function equals `f`
  on any set `s` on whose part to the right of `c` the functions `f` and `g` agree, and `g` on
  any set on whose part up to `c` they agree.
* `Set.EqOn.eventuallyEq_ite_le_left`, `Set.EqOn.eventuallyEq_ite_le_right`: if `f` and `g`
  agree on `(a, b)` and `a ≤ c < b`, the glued function is eventually equal to `f` near every
  `x < b`, and to `g` near every `x > a`.
-/

public section

open Filter Topology

namespace Set

variable {α β : Type*} [LinearOrder α] {f g : α → β} {s : Set α} {a b c : α}

/-- The function equal to `f` up to `c` and to `g` after it equals `f` on a set `s` if `f` and
`g` agree on the points of `s` greater than `c`. -/
theorem EqOn.eqOn_ite_le_left (h : EqOn f g (s ∩ Ioi c)) :
    EqOn (fun r ↦ if r ≤ c then f r else g r) f s := fun r hr ↦ by
  by_cases hrc : r ≤ c
  · simp [hrc]
  · simpa [hrc] using (h ⟨hr, not_le.1 hrc⟩).symm

/-- The function equal to `f` up to `c` and to `g` after it equals `g` on a set `s` if `f` and
`g` agree on the points of `s` at most `c`. -/
theorem EqOn.eqOn_ite_le_right (h : EqOn f g (s ∩ Iic c)) :
    EqOn (fun r ↦ if r ≤ c then f r else g r) g s := fun r hr ↦ by
  by_cases hrc : r ≤ c
  · simpa [hrc] using h ⟨hr, hrc⟩
  · simp [hrc]

variable [TopologicalSpace α] {x : α}

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
