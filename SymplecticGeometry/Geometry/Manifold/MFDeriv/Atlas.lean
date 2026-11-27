/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The derivative of a differentiable partial homeomorphism

For a partial homeomorphism `e` that is differentiable with differentiable inverse, Mathlib's
`OpenPartialHomeomorph.MDifferentiable.mfderiv` packages its derivative at a point `x` of its
source as a continuous linear equivalence. This file states what that equivalence and its inverse
are as maps: the derivative of `e` at `x`, and the derivative of `e.symm` at `e x`.

## Main results

* `OpenPartialHomeomorph.MDifferentiable.coe_mfderiv`: the equivalence is the derivative of `e`.
* `OpenPartialHomeomorph.MDifferentiable.coe_mfderiv_symm`: its inverse is the derivative of
  `e.symm`.
-/

public section

open scoped Manifold

namespace OpenPartialHomeomorph.MDifferentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I') {x : M} (hx : x ∈ e.source)

/-- The continuous linear equivalence `he.mfderiv hx` is the derivative of `e` at `x`. -/
@[simp]
theorem coe_mfderiv : ⇑(he.mfderiv hx) = mfderiv I I' e x := (rfl)

/-- The inverse of the continuous linear equivalence `he.mfderiv hx` is the derivative of
`e.symm` at `e x`. -/
@[simp]
theorem coe_mfderiv_symm : ⇑(he.mfderiv hx).symm = mfderiv I' I e.symm (e x) := (rfl)

end OpenPartialHomeomorph.MDifferentiable

end
