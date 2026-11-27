/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Order.Interval.Set.OrderIso

/-!
# Images of intervals under strictly monotone surjections

A strictly monotone surjection `f` from a linear order maps each interval onto the interval with
the image endpoints. Mathlib states this for order isomorphisms (`OrderIso.image_Iic`,
`OrderIso.image_Ioc`), and for a strictly monotone map only as inclusions
(`StrictMono.image_Ioo_subset` and its neighbours); this file gives the equalities for a strictly
monotone surjection, through `StrictMono.orderIsoOfSurjective`.

## Main results

* `StrictMono.image_Iic_of_surjective`: `f '' Iic a = Iic (f a)`.
* `StrictMono.image_Ioc_of_surjective`: `f '' Ioc a b = Ioc (f a) (f b)`.
-/

public section

open Set

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β}

/-- A strictly monotone surjection maps `Iic a` onto `Iic (f a)`. -/
theorem StrictMono.image_Iic_of_surjective (hf : StrictMono f) (hs : Function.Surjective f)
    (a : α) : f '' Iic a = Iic (f a) := by
  rw [← StrictMono.coe_orderIsoOfSurjective f hf hs]
  exact OrderIso.image_Iic _ a

/-- A strictly monotone surjection maps `Ioc a b` onto `Ioc (f a) (f b)`. -/
theorem StrictMono.image_Ioc_of_surjective (hf : StrictMono f) (hs : Function.Surjective f)
    (a b : α) : f '' Ioc a b = Ioc (f a) (f b) := by
  rw [← StrictMono.coe_orderIsoOfSurjective f hf hs]
  exact OrderIso.image_Ioc _ a b

end
