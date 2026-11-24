/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The product rule for functions with values in a normed algebra

Mathlib's `mvfderiv_mul` is the product rule for scalar functions on a manifold. This file gives
the product rule for functions with values in a normed algebra that need not be commutative, such
as the algebra `V →L[𝕜] V` of continuous endomorphisms: `mvfderiv_fun_mul_apply'`. Mathlib states
this rule for `HasMFDerivAt` as `HasMFDerivAt.mul'`
(`Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean`); the lemma here is its form for
`mvfderiv`, applied to a tangent vector.

It is Tau Ceti's Leibniz rule `TauCeti.mvfderiv_smul_algebra`, for the algebra acting on itself by
left multiplication, evaluated at a tangent vector.
-/

public section

namespace SymplecticGeometry

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedRing F] [NormedAlgebra 𝕜 F]

/-- The **product rule** for functions on a manifold with values in a normed algebra, which need
not be commutative: the derivative of `y ↦ p y * q y` along `v` is `p' v * q x + p x * q' v`. -/
theorem mvfderiv_fun_mul_apply' {p q : M → F} {x : M}
    (hp : MDifferentiableAt I 𝓘(𝕜, F) p x) (hq : MDifferentiableAt I 𝓘(𝕜, F) q x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ p y * q y) x v = mvfderiv I p x v * q x + p x * mvfderiv I q x v := by
  have h := congr($(TauCeti.mvfderiv_smul_algebra (𝕜' := F) hp hq) v)
  rw [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, smul_eq_mul, add_comm] at h
  exact h

end SymplecticGeometry
