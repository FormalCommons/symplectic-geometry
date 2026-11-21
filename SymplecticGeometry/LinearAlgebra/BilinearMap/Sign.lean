/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Linear and bilinear maps that agree up to sign

If two linear maps `f` and `g` agree up to sign at every point, `f x = g x ∨ f x = -g x`, then
the sign does not depend on the point: `f = g` or `f = -g`. Comparing `f` and `g` at `x`, `y`
and `x + y` shows that a point where `f x ≠ g x` and a point where `f y ≠ -g y` cannot both
exist.

Over a commutative ring without zero divisors this applies to linear functionals with the
same squares, and, applied twice, to bilinear maps with the same squares. The second form says
that a linear map `Ψ` with `ω (Ψ v) (Ψ w) ^ 2 = ω v w ^ 2` for all `v` and `w` pulls `ω` back to
`ω` or to `-ω`; it is the last step of the linear rigidity theorem of McDuff–Salamon,
Theorem 2.4.2.

## Main results

* `LinearMap.eq_or_eq_neg_of_forall_eq_or_eq_neg`: pointwise agreement up to sign is global.
* `LinearMap.eq_or_eq_neg_of_forall_sq_eq_sq`: linear functionals with the same squares agree up
  to sign, after Mathlib's `eq_or_eq_neg_of_sq_eq_sq`.
* `LinearMap.eq_or_eq_neg_of_forall_sq_eq_sq₂`: the same for bilinear maps.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
-/

public section

namespace LinearMap

section AddCommGroup

variable {R M N : Type*} [Semiring R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

/-- If two linear maps agree up to sign at every point, then they agree up to a sign that does
not depend on the point. -/
theorem eq_or_eq_neg_of_forall_eq_or_eq_neg {f g : M →ₗ[R] N}
    (h : ∀ x, f x = g x ∨ f x = -g x) : f = g ∨ f = -g := by
  by_contra! hfg
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 hfg.1
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 hfg.2
  rw [LinearMap.neg_apply] at hy
  have hx' : f x = -g x := (h x).resolve_left hx
  have hy' : f y = g y := (h y).resolve_right hy
  rcases h (x + y) with hxy | hxy
  · rw [map_add, map_add, hy', add_left_inj] at hxy
    exact hx hxy
  · rw [map_add, map_add, hx', neg_add, add_right_inj] at hxy
    exact hy hxy

end AddCommGroup

section CommRing

variable {R M N : Type*} [CommRing R] [NoZeroDivisors R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Two linear functionals with the same squares at every point agree up to sign. -/
theorem eq_or_eq_neg_of_forall_sq_eq_sq {f g : M →ₗ[R] R} (h : ∀ x, f x ^ 2 = g x ^ 2) :
    f = g ∨ f = -g :=
  eq_or_eq_neg_of_forall_eq_or_eq_neg fun x ↦ sq_eq_sq_iff_eq_or_eq_neg.1 (h x)

/-- Two bilinear maps with the same squares at every pair of points agree up to sign. -/
theorem eq_or_eq_neg_of_forall_sq_eq_sq₂ {B ω : M →ₗ[R] N →ₗ[R] R}
    (h : ∀ x y, B x y ^ 2 = ω x y ^ 2) : B = ω ∨ B = -ω :=
  eq_or_eq_neg_of_forall_eq_or_eq_neg fun x ↦ by
    simpa only [LinearMap.neg_apply, LinearMap.ext_iff] using eq_or_eq_neg_of_forall_sq_eq_sq (h x)

end CommRing

end LinearMap

end
