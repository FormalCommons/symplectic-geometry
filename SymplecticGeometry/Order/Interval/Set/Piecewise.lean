/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Piecewise
import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Gluing two functions at a point of a linear order

For `c` in a linear order, `fun r ↦ if r ≤ c then f r else g r` is `f` up to `c` and `g` after
it, as in Tau Ceti's `Set.eqOn_ite_le_Ici` and `Set.MapsTo.ite_le_Icc`. It is
`(Iic c).piecewise f g`, so when `f` and `g` agree on a part of a set, it equals `f` or `g` on
the whole set. Both results below are the reverse implication of Mathlib's
`Set.eqOn_piecewise` for `Iic c`, with target `f` or `g`, written for the `if` form that proofs
build.

## Main results

* `Set.EqOn.eqOn_ite_le_left`, `Set.EqOn.eqOn_ite_le_right`: the glued function equals `f`
  on any set `s` on whose part to the right of `c` the functions `f` and `g` agree, and `g` on
  any set on whose part up to `c` they agree.
-/

public section

namespace Set

variable {α β : Type*} [LinearOrder α] {f g : α → β} {s : Set α} {c : α}

/-- The function equal to `f` up to `c` and to `g` after it equals `f` on a set `s` if `f` and
`g` agree on the points of `s` greater than `c`. -/
theorem EqOn.eqOn_ite_le_left (h : EqOn f g (s ∩ Ioi c)) :
    EqOn (fun r ↦ if r ≤ c then f r else g r) f s :=
  eqOn_piecewise (s := Iic c) |>.2 ⟨fun _ _ ↦ rfl, by simpa [compl_Iic] using h.symm⟩

/-- The function equal to `f` up to `c` and to `g` after it equals `g` on a set `s` if `f` and
`g` agree on the points of `s` at most `c`. -/
theorem EqOn.eqOn_ite_le_right (h : EqOn f g (s ∩ Iic c)) :
    EqOn (fun r ↦ if r ≤ c then f r else g r) g s :=
  eqOn_piecewise (s := Iic c) |>.2 ⟨h, fun _ _ ↦ rfl⟩

end Set

end
