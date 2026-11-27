/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd

/-!
# Slices of functions of two variables that agree near a point

If `f g : X → Y → Z` agree, as functions `Function.uncurry f`, `Function.uncurry g` on
`X × Y`, on a neighbourhood of `x`, then their slices through `x` agree on neighbourhoods of the
coordinates of `x`: `f x.1` and `g x.1` near `x.2`, and `fun a ↦ f a x.2` and `fun a ↦ g a x.2`
near `x.1`. These are the counterparts for `Filter.EventuallyEq` of Mathlib's
`Continuous.uncurry_left` and `Continuous.uncurry_right`.

## Main results

* `Filter.EventuallyEq.uncurry_left`: the slices in the second variable.
* `Filter.EventuallyEq.uncurry_right`: the slices in the first variable.
-/

public section

open Topology

namespace Filter.EventuallyEq

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : X → Y → Z}
  {x : X × Y}

/-- If `Function.uncurry f` and `Function.uncurry g` agree near `x`, then `f x.1` and `g x.1`
agree near `x.2`. -/
theorem uncurry_left (h : Function.uncurry f =ᶠ[𝓝 x] Function.uncurry g) :
    f x.1 =ᶠ[𝓝 x.2] g x.1 :=
  h.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto' x.2 x rfl)

/-- If `Function.uncurry f` and `Function.uncurry g` agree near `x`, then `fun a ↦ f a x.2` and
`fun a ↦ g a x.2` agree near `x.1`. -/
theorem uncurry_right (h : Function.uncurry f =ᶠ[𝓝 x] Function.uncurry g) :
    (fun a ↦ f a x.2) =ᶠ[𝓝 x.1] fun a ↦ g a x.2 :=
  h.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto' x.1 x rfl)

end Filter.EventuallyEq

end
