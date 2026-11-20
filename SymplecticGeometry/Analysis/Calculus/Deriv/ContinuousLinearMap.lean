/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of paths of skew forms and of square roots of a constant

Two algebraic identities satisfied by the derivative of a path that obeys a pointwise constraint,
obtained by differentiating the constraint.

* If `ω s` is a skew-symmetric continuous bilinear map for every `s` near `t`, then so is
  `deriv ω t`. This is the skew analogue of Tau Ceti's `TauCeti.fderiv_apply_apply_comm`.
* If `J s * J s` is a constant `c` for `s` near `t`, in a normed algebra (for instance the
  continuous endomorphisms of a Banach space), then `deriv J t` anticommutes with `J t`. This is
  the algebra analogue of Tau Ceti's `TauCeti.fderiv_apply_apply_eq_neg_of_eventually_const`;
  the case `c = -1` concerns paths of complex structures.

Neither statement assumes differentiability: where the path is not differentiable its `deriv` is
zero, and both identities are trivial.

## Main results

* `SymplecticGeometry.deriv_apply_apply_eq_neg`: the derivative of a path of skew forms is skew.
* `SymplecticGeometry.deriv_mul_add_mul_deriv_eq_zero`: the derivative of a path whose square is
  locally constant anticommutes with the path.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  proofs of Corollary 2.5.14 and Exercise 2.5.18, where these identities are used.
-/

public section

open Filter
open scoped Topology

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- If `ω s` is skew-symmetric for every `s` near `t`, then so is `deriv ω t`. -/
theorem deriv_apply_apply_eq_neg {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {ω : 𝕜 → F →L[𝕜] F →L[𝕜] G} {t : 𝕜}
    (hskew : ∀ᶠ s in 𝓝 t, ∀ v w, ω s v w = -ω s w v) (v w : F) :
    deriv ω t v w = -deriv ω t w v := by
  by_cases hω : DifferentiableAt 𝕜 ω t
  swap
  · simp [deriv_zero_of_not_differentiableAt hω]
  have hev (a b : F) : HasDerivAt (fun s => ω s a b) (deriv ω t a b) t := by
    have h := HasDerivAt.clm_apply (c := ω) (u := fun _ => a) hω.hasDerivAt
      (hasDerivAt_const t a)
    simpa using HasDerivAt.clm_apply (c := fun s => ω s a) (u := fun _ => b) h
      (hasDerivAt_const t b)
  have h : (fun s => -ω s w v) =ᶠ[𝓝 t] fun s => ω s v w := hskew.mono fun s hs => (hs v w).symm
  exact (hev v w).unique (HasDerivAt.congr_of_eventuallyEq (f := fun s => -ω s w v)
    (hev w v).fun_neg h.symm)

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
