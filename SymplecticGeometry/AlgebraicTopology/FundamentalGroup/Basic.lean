/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# The class of a loop in the fundamental group

Mathlib's `FundamentalGroup.mapOfEq f h : π₁(X, x) →* π₁(Y, y)`, for `f : C(X, Y)` and
`h : f x = y`, sends the class of a loop `γ` at `x` to the class of the loop `f ∘ γ`, read at
`y` through `h`. This file states that on the class of a loop, as a rewrite rule, to go with
`FundamentalGroup.mapOfEq_apply`, which states it on an element of `π₁(X, x)` in the
fundamental groupoid. It also states how concatenation and reversal of loops, and the change
of base point along a path, read on their classes.

## Main results

* `FundamentalGroup.mapOfEq_fromPath_mk`: `mapOfEq f h` sends the class of `γ` to the class of
  `(γ.map f.continuous).cast h.symm h.symm`.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_fromPath_mk`: the change of base point
  along `γ`, read backwards, sends the class of a loop `g` to the class of `γ · g · γ⁻¹`.
* `FundamentalGroup.fromPath_trans`, `FundamentalGroup.fromPath_symm`: the class of a
  concatenation of loops is the product of their classes, in the reverse order, and the class of
  a reversed loop is the inverse.
-/

public section

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The map `π₁(X, x) → π₁(Y, y)` induced by `f : C(X, Y)` with `f x = y` sends the class of a
loop `γ` at `x` to the class of the loop `f ∘ γ`, cast to a loop at `y`. -/
theorem mapOfEq_fromPath_mk (f : C(X, Y)) (h : f x = y) (γ : Path x x) :
    mapOfEq f h (fromPath (Path.Homotopic.Quotient.mk γ)) =
      fromPath (Path.Homotopic.Quotient.mk ((γ.map f.continuous).cast h.symm h.symm)) := by
  rw [mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]

/-- The inverse of the change of base point along a path `γ` from `x₀` to `x₁` sends the class of
a loop `g` at `x₁` to the class of the loop `γ · g · γ⁻¹` at `x₀`. -/
theorem fundamentalGroupMulEquivOfPath_symm_fromPath_mk {x₀ x₁ : X} (γ : Path x₀ x₁)
    (g : Path x₁ x₁) :
    (fundamentalGroupMulEquivOfPath γ).symm (fromPath (Path.Homotopic.Quotient.mk g)) =
      fromPath (Path.Homotopic.Quotient.mk (γ.trans (g.trans γ.symm))) := by
  rw [fundamentalGroupMulEquivOfPath_symm_apply, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]

/-- The concatenation `γ · δ` of two classes of loops is their product in the fundamental group, in
the reverse order: in Mathlib's `FundamentalGroup`, `g * h` is `h` followed by `g`. -/
@[simp]
theorem fromPath_trans (γ δ : Path.Homotopic.Quotient x x) :
    fromPath (γ.trans δ) = fromPath δ * fromPath γ :=
  (rfl)

/-- The reversal of a class of loops is its inverse in the fundamental group. -/
@[simp]
theorem fromPath_symm (γ : Path.Homotopic.Quotient x x) :
    fromPath γ.symm = (fromPath γ)⁻¹ :=
  (rfl)

end FundamentalGroup

end
