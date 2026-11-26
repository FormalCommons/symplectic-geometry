/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle.Sections
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# The Cauchy–Riemann operator of the standard structure on `𝒪(1)`

Let `D_i = SymplecticGeometry.twistOneDelBar 𝒊` be the real Cauchy–Riemann operator on the line
bundle `𝒪(1) = OnePoint.twistCore 1` over the Riemann sphere for its standard complex structure
`𝒊`. This file identifies the space `twistOneKernel 𝒊` of its smooth zeros with the space
`OnePoint.holomorphicTwistSections 1` of holomorphic sections of `𝒪(1)`, which has complex
dimension two.

## Main results

* `SymplecticGeometry.twistOneDelBar_ofComplexManifold_eq_zero_iff`: at a point where a section
  of `𝒪(1)` is real differentiable, `D_i` vanishes exactly when the section is holomorphic there.
* `SymplecticGeometry.twistOneKernel_ofComplexManifold`: the smooth zeros of `D_i` are the
  holomorphic sections of `𝒪(1)`.
* `SymplecticGeometry.finrank_twistOneKernel_ofComplexManifold`: they form a complex vector space
  of dimension two.

## Proof

In the frame of the chart at a point `x`, the `(0,1)`-part of the connection for `𝒊` is `∂bar` of
the coordinate of the section (`SymplecticGeometry.twistOneConnection_zeroOnePart_eq`), and
that frame is an isomorphism at `x`. By Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_eq_zero_iff`, `∂bar` of the
coordinate vanishes at `x` exactly when the coordinate is holomorphic at `x`, that is, when the
section is holomorphic at `x`. A holomorphic section of `𝒪(1)` is analytic
(`OnePoint.contMDiff_section_twistCore_iff_mdifferentiable`), hence smooth for the underlying real
structure; and Tau Ceti's `OnePoint.finrank_holomorphicTwistSections` gives the dimension.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle TauCeti
open OnePoint (twistCore)
open scoped Manifold ContDiff VectorBundle.ComplexToReal

namespace SymplecticGeometry

/-- At a point where a section `s` of `𝒪(1)` is real differentiable, the Cauchy–Riemann operator
`D_i` of the standard complex structure of the sphere vanishes exactly when `s` is holomorphic
there. -/
theorem twistOneDelBar_ofComplexManifold_eq_zero_iff {s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x}
    {x : OnePoint ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    twistOneDelBar 𝒊 s x = 0 ↔ MDifferentiableAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x := by
  have hx : x ∈ ((twistCore (𝕜 := ℂ) 1).localTriv x).baseSet := by simp
  have hr := ((twistCore (𝕜 := ℂ) 1).localTriv x).mdifferentiableAt_section_iff 𝓘(ℝ, ℂ) s hx
    |>.1 hs
  rw [((twistCore (𝕜 := ℂ) 1).localTriv x).mdifferentiableAt_section_iff 𝓘(ℂ, ℂ) s hx,
    ← SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_eq_zero_iff hr,
    twistOneDelBar_def, twistOneConnection_zeroOnePart_eq (mem_chart_source ℂ x) hs]
  -- The frame of the chart at `x` is the identity at `x`.
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_,
    fun h ↦ by rw [h, ContinuousLinearMap.comp_zero]⟩
  have h' := congrArg (fun L ↦ L v) h
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at h'
  rw [OnePoint.twistCore_localTriv_symmL_apply (mem_chart_source ℂ x),
    OnePoint.twistTransition_self, one_mul] at h'
  -- The fibre of `𝒪(1)` at `x` is `ℂ`, in which `h'` is stated.
  rw [zero_apply]
  exact h'

/-- **The kernel of `D_i` is `H⁰(𝒪(1))`.** The smooth sections of `𝒪(1)` that the Cauchy–Riemann
operator of the standard complex structure of the sphere sends to zero are exactly the
holomorphic sections. -/
theorem twistOneKernel_ofComplexManifold :
    twistOneKernel 𝒊 = OnePoint.holomorphicTwistSections 1 := by
  ext s
  rw [mem_twistOneKernel_iff, OnePoint.mem_holomorphicTwistSections]
  refine ⟨fun ⟨hs, h0⟩ x ↦ (twistOneDelBar_ofComplexManifold_eq_zero_iff
    (hs.mdifferentiableAt (by simp))).1 (congrFun h0 x), fun h ↦ ?_⟩
  have hc := (OnePoint.contMDiff_section_twistCore_iff_mdifferentiable (m := ∞) 1 (by simp) s).2 h
  have hr : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) := by
    simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
      hc.restrictScalars ℝ
  exact ⟨hr, funext fun x ↦
    (twistOneDelBar_ofComplexManifold_eq_zero_iff (hr.mdifferentiableAt (by simp))).2 (h x)⟩

/-- The smooth zeros of the Cauchy–Riemann operator of the standard complex structure on `𝒪(1)`
form a complex vector space of dimension two. -/
theorem finrank_twistOneKernel_ofComplexManifold : Module.finrank ℂ (twistOneKernel 𝒊) = 2 := by
  rw [twistOneKernel_ofComplexManifold]
  exact OnePoint.finrank_holomorphicTwistSections 1

end SymplecticGeometry

end
