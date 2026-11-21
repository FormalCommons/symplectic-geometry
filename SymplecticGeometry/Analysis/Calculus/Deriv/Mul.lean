/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of paths whose square is locally constant

In a normed algebra over a nontrivially normed field, for instance the continuous endomorphisms
of a Banach space, if `J s * J s` is a constant `c` for `s` near `t`, then `deriv J t`
anticommutes with `J t`. This is the algebra analogue of Tau Ceti's
`TauCeti.fderiv_apply_apply_eq_neg_of_eventually_const`; the case `c = -1` concerns paths of
complex structures.

No differentiability is assumed: where the path is not differentiable its `deriv` is zero, and
the identity is trivial.

## Main results

* `SymplecticGeometry.deriv_mul_add_mul_deriv_eq_zero`: the derivative of a path whose square is
  locally constant anticommutes with the path.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  proof of Exercise 2.5.18, where this identity is used.
-/

public section

open Filter
open scoped Topology

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- If `J s * J s` is a constant for every `s` near `t`, then `deriv J t` anticommutes with
`J t`. -/
theorem deriv_mul_add_mul_deriv_eq_zero {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]
    {J : 𝕜 → B} {t : 𝕜} {c : B} (hsq : ∀ᶠ s in 𝓝 t, J s * J s = c) :
    deriv J t * J t + J t * deriv J t = 0 := by
  by_cases hJ : DifferentiableAt 𝕜 J t
  swap
  · simp [deriv_zero_of_not_differentiableAt hJ]
  exact (hJ.hasDerivAt.mul hJ.hasDerivAt).unique
    ((hasDerivAt_const t c).congr_of_eventuallyEq hsq)

end SymplecticGeometry

end
