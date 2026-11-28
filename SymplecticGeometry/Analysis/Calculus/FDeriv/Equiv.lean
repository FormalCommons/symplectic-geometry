/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import TauCeti.Analysis.Calculus.FDeriv.Equiv

import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Derivatives and equivalences

Let `f` be an open partial homeomorphism between normed spaces, differentiable at a point `x` of
its source, with inverse differentiable at `f x`. By the chain rule, the derivatives of `f` at `x`
and of `f.symm` at `f x` are mutually inverse (Tau Ceti's
`OpenPartialHomeomorph.fderiv_symm_comp_fderiv_of_mem_source` and
`OpenPartialHomeomorph.fderiv_comp_fderiv_symm_of_mem_source`), so together they form one
continuous linear equivalence.

## Main definitions

* `OpenPartialHomeomorph.fderivEquiv`: the derivative of `f` at `x`, as a continuous linear
  equivalence whose inverse is the derivative of `f.symm` at `f x`.

## Main results

* `OpenPartialHomeomorph.fderiv_fderiv_symm_apply_fderiv_apply`: when `f` and `f.symm` are `C²`,
  the second derivative of the inverse is `D²f⁻¹(Df a, Df b) = -Df⁻¹(D²f(a, b))`, by the
  second-order chain rule `TauCeti.fderiv_fderiv_comp_apply` applied to `f.symm ∘ f`.
* `LinearIsometryEquiv.comp_right_fderiv`: the derivative of `f ∘ iso`, for a linear isometry
  equivalence `iso`, is that of `f` composed with `iso`; Mathlib's
  `LinearIsometryEquiv` API has only the left-composition form `comp_fderiv`.
-/

public section

open Filter Topology

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

include hx in
/-- The second derivative of the inverse of an open partial homeomorphism `f` at `f x`, on the
images `Df_x a` and `Df_x b`, is `-Df⁻¹(D²f_x(a, b))`, where `f` is `C²` at `x` and `f.symm` is
`C²` at `f x`. -/
theorem fderiv_fderiv_symm_apply_fderiv_apply (he : ContDiffAt 𝕜 2 f x)
    (hs : ContDiffAt 𝕜 2 f.symm (f x)) (a b : E) :
    fderiv 𝕜 (fderiv 𝕜 f.symm) (f x) (fderiv 𝕜 f x a) (fderiv 𝕜 f x b) =
      -fderiv 𝕜 f.symm (f x) (fderiv 𝕜 (fderiv 𝕜 f) x a b) := by
  have hcomp : fderiv 𝕜 (fderiv 𝕜 (f.symm ∘ f)) x = 0 := by
    have h : fderiv 𝕜 (f.symm ∘ f) =ᶠ[𝓝 x] fun _ ↦ ContinuousLinearMap.id 𝕜 E :=
      eventually_of_mem (f.open_source.mem_nhds hx) fun q hq ↦ by
        have h' : f.symm ∘ f =ᶠ[𝓝 q] id := f.eventually_left_inverse hq
        exact h'.fderiv_eq.trans fderiv_id
    rw [h.fderiv_eq]
    simp
  have h := TauCeti.fderiv_fderiv_comp_apply hs he a b
  rw [hcomp, _root_.zero_apply, _root_.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end OpenPartialHomeomorph

namespace LinearIsometryEquiv

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The derivative of `f ∘ iso` at `x`, for a linear isometry equivalence `iso`, is the
derivative of `f` at `iso x` composed with `iso`. -/
theorem comp_right_fderiv (iso : E ≃ₗᵢ[𝕜] F) {f : F → G} {x : E} :
    fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E →L[𝕜] F) :=
  iso.toContinuousLinearEquiv.comp_right_fderiv

end LinearIsometryEquiv

end
