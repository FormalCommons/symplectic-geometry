/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Monoid homomorphisms from a group into a monoid with zero

A monoid homomorphism `f` from a group `G` to a monoid with zero `M₀` sends every element to a
unit, so it sends inverses to ring inverses: `f a⁻¹ = Ring.inverse (f a)`
(`map_inv_eq_ringInverse`). This is the analogue for group sources of Mathlib's
`map_inv_eq_ringInverse_map`, whose source is a group with zero.

## Main results

* `map_inv_eq_ringInverse`: a monoid homomorphism from a group to a monoid with zero sends `a⁻¹`
  to `Ring.inverse (f a)`.
-/

public section

variable {F G M₀ : Type*} [Group G] [MonoidWithZero M₀] [FunLike F G M₀] [MonoidHomClass F G M₀]

/-- A monoid homomorphism from a group to a monoid with zero sends the inverse `a⁻¹` to the ring
inverse of `f a`. -/
theorem map_inv_eq_ringInverse (f : F) (a : G) : f a⁻¹ = Ring.inverse (f a) := by
  simpa using (Ring.inverse_unit (Units.map (MonoidHom.ofClass f) (toUnits a))).symm

end
