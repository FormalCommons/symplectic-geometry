/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Circle.FreeLoop

/-!
# Degrees of products of circle maps

The degree `ContinuousMap.circleDegree` of maps `S¹ → S¹`, from Tau Ceti, is additive under the
pointwise product: `deg (f * g) = deg f + deg g`. This is Tau Ceti's `Circle.degree_mul` for
based loops, read on the loops `t ↦ f (e^{2πit})` of the two maps.

## Main results

* `ContinuousMap.circleDegree_mul`: the degree of a pointwise product is the sum of the degrees.
* `ContinuousMap.circleDegree_inv`: the degree of the pointwise inverse is the negated degree.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.1.
-/

public section

namespace ContinuousMap

open Circle

/-- The degree of the pointwise product of two circle maps is the sum of their degrees. -/
@[simp]
theorem circleDegree_mul (f g : C(Circle, Circle)) :
    (f * g).circleDegree = f.circleDegree + g.circleDegree := by
  rw [← degree_toBasedLoop, ← degree_toBasedLoop, ← degree_toBasedLoop, ← degree_mul]
  exact degree_congr _ _ fun t ↦ by rw [toBasedLoop_apply]; simp [toBasedLoop_apply]

/-- The degree of the pointwise inverse of a circle map is the negated degree. -/
@[simp]
theorem circleDegree_inv (f : C(Circle, Circle)) : f⁻¹.circleDegree = -f.circleDegree := by
  rw [← degree_toBasedLoop, ← degree_toBasedLoop, ← degree_inv]
  exact degree_congr _ _ fun t ↦ by rw [toBasedLoop_apply]; simp [toBasedLoop_apply]

end ContinuousMap

end
