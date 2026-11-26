/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# The derivative of a partial homeomorphism differentiable in both directions

Let `f` be an open partial homeomorphism between normed spaces, differentiable at a point `x` of
its source, with inverse differentiable at `f x`. By the chain rule, the derivatives of `f` at `x`
and of `f.symm` at `f x` are mutually inverse (Tau Ceti's
`OpenPartialHomeomorph.fderiv_symm_comp_fderiv_of_mem_source` and
`OpenPartialHomeomorph.fderiv_comp_fderiv_symm_of_mem_source`), so together they form one
continuous linear equivalence.

## Main definitions

* `OpenPartialHomeomorph.fderivEquiv`: the derivative of `f` at `x`, as a continuous linear
  equivalence whose inverse is the derivative of `f.symm` at `f x`.
-/

public section

namespace OpenPartialHomeomorph

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : OpenPartialHomeomorph E F) {x : E}

/-- The derivative at `x ∈ f.source` of an open partial homeomorphism `f` that is differentiable
at `x` and whose inverse is differentiable at `f x`, as a continuous linear equivalence. Its
inverse is the derivative of `f.symm` at `f x`
(`OpenPartialHomeomorph.coe_fderivEquiv_symm`). -/
noncomputable def fderivEquiv (hx : x ∈ f.source) (hf : DifferentiableAt 𝕜 f x)
    (hf' : DifferentiableAt 𝕜 f.symm (f x)) : E ≃L[𝕜] F :=
  .ofContinuousLinearMap (fderiv 𝕜 f x) (fderiv 𝕜 f.symm (f x))
    (f.fderiv_comp_fderiv_symm_of_mem_source hx hf hf')
    (f.fderiv_symm_comp_fderiv_of_mem_source hx hf hf')

variable (hx : x ∈ f.source) (hf : DifferentiableAt 𝕜 f x)
  (hf' : DifferentiableAt 𝕜 f.symm (f x))

@[simp]
theorem coe_fderivEquiv : ⇑(f.fderivEquiv hx hf hf') = fderiv 𝕜 f x :=
  (rfl)

@[simp]
theorem coe_fderivEquiv_symm : ⇑(f.fderivEquiv hx hf hf').symm = fderiv 𝕜 f.symm (f x) :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_fderivEquiv :
    (f.fderivEquiv hx hf hf' : E →L[𝕜] F) = fderiv 𝕜 f x :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_fderivEquiv_symm :
    ((f.fderivEquiv hx hf hf').symm : F →L[𝕜] E) = fderiv 𝕜 f.symm (f x) :=
  (rfl)

end OpenPartialHomeomorph

end
