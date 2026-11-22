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
* `ContinuousMap.circleDegreeHom`: the degree as a group hom `C(S¹, S¹) →* Multiplicative ℤ`.
* `ContinuousMap.circleDegree_one`, `ContinuousMap.circleDegree_div`,
  `ContinuousMap.circleDegree_pow`, `ContinuousMap.circleDegree_zpow_eq_mul`: the degree of the
  constant map `1`, of pointwise quotients and of pointwise powers.

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

/-- The degree of circle maps as a group hom from the pointwise product of circle maps to the
integers, written multiplicatively. -/
noncomputable def circleDegreeHom : C(Circle, Circle) →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd f.circleDegree
  map_one' := by rw [← const_one, circleDegree_const, ofAdd_zero]
  map_mul' f g := by rw [circleDegree_mul, ofAdd_add]

/-- The degree hom sends a circle map to its degree, read in `Multiplicative ℤ`. -/
@[simp]
theorem circleDegreeHom_apply (f : C(Circle, Circle)) :
    circleDegreeHom f = Multiplicative.ofAdd f.circleDegree :=
  (rfl)

/-- The constant circle map `1` has degree `0`. -/
@[simp]
theorem circleDegree_one : (1 : C(Circle, Circle)).circleDegree = 0 := by
  simpa using map_one circleDegreeHom

/-- The degree of the pointwise inverse of a circle map is the negated degree. -/
@[simp]
theorem circleDegree_inv (f : C(Circle, Circle)) : f⁻¹.circleDegree = -f.circleDegree := by
  simpa [← ofAdd_neg] using map_inv circleDegreeHom f

/-- The degree of a pointwise quotient of circle maps is the difference of their degrees. -/
@[simp]
theorem circleDegree_div (f g : C(Circle, Circle)) :
    (f / g).circleDegree = f.circleDegree - g.circleDegree := by
  simpa [← ofAdd_sub] using map_div circleDegreeHom f g

/-- The degree of the pointwise `n`-th power of a circle map is `n` times its degree. -/
@[simp]
theorem circleDegree_pow (f : C(Circle, Circle)) (n : ℕ) :
    (f ^ n).circleDegree = n * f.circleDegree := by
  simpa [← ofAdd_nsmul] using map_pow circleDegreeHom f n

/-- The degree of the pointwise `n`-th power of a circle map, for an integer `n`, is `n` times its
degree. (Tau Ceti's `ContinuousMap.circleDegree_zpow` is about the map `ζ ↦ ζ ^ n` instead.) -/
@[simp]
theorem circleDegree_zpow_eq_mul (f : C(Circle, Circle)) (n : ℤ) :
    (f ^ n).circleDegree = n * f.circleDegree := by
  simpa [← ofAdd_zsmul] using map_zpow circleDegreeHom f n

end ContinuousMap

end
