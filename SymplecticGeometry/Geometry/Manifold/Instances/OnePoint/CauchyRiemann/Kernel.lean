/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.TwistCore

import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.ComplexLinear

/-!
# Kernels of Cauchy–Riemann operators on `𝒪(1)` over the sphere

This file is about the kernels of the real Cauchy–Riemann operators `D_J` on the line bundle
`L = 𝒪(1)` (Tau Ceti's `OnePoint.twistCore 1`) over the Riemann sphere `OnePoint ℂ`.

## Main results

* `SymplecticGeometry.eulerNumber_twistCore_one`: the Euler number of `L` is `1`. The sphere is
  oriented by its complex structure (`SymplecticGeometry.complexManifoldHomologicalOrientation`)
  and `L` by the complex orientation of its fibres (`TauCeti.VectorBundleOrientation.complex`),
  and the Euler class (`TauCeti.VectorBundleOrientation.eulerClass`) is paired with the
  fundamental class, in the form of the left side of Tau Ceti's
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`.

## Proof

The section `z` of `L` (`OnePoint.identitySection`) is continuous and vanishes only at `0`
(`OnePoint.identitySection_eq_zero_iff`). By Tau Ceti's
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex` the Euler
number is its local index at `0`. In the affine chart and the trivialization
`(twistCore 1).localTriv 0` the section reads as the identity of `ℂ`, a complex-linear
isomorphism, so this index is `1`
(`SymplecticGeometry.sectionIndex_eq_one_of_complexLinear`). This is the argument of
`Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass` on the sphere.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class as a sum of indices of a section) and §14 (the canonical
  orientation of a complex vector bundle).
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 (the zeros of a section in the kernel of a real Cauchy–Riemann operator).
-/

public section

open Bundle Module TauCeti
open OnePoint (twistCore identitySection)
open scoped Manifold VectorBundle.ComplexToReal

namespace SymplecticGeometry

/-- **The Euler number of `𝒪(1)` on the Riemann sphere is one.** Orient the sphere `OnePoint ℂ`
by its complex structure and the line bundle `𝒪(1) = OnePoint.twistCore 1` by the complex
orientation of its fibres. Then the Euler class of `𝒪(1)`, paired with the fundamental class of
the sphere, is `1`. -/
theorem eulerNumber_twistCore_one :
    ((complexManifoldHomologicalOrientation ℂ (OnePoint ℂ) (finrank_self ℂ)).evalFundamentalClass
      (Complex.finrank_real_complex) (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id _)
      (((VectorBundleOrientation.complex ℂ (twistCore (𝕜 := ℂ) 1).Fiber).reindex
        (finCongr (by simp : 2 * finrank ℂ ℂ = 1 + 1))).eulerClass
          Complex.finrank_real_complex)).down = 1 := by
  set s : ∀ x, (twistCore (𝕜 := ℂ) 1).Fiber x := identitySection
  have hs : Continuous fun x ↦ TotalSpace.mk' ℂ x (s x) :=
    OnePoint.contMDiff_identitySection.continuous
  have hZ : {x | s x = 0} = {((0 : ℂ) : OnePoint ℂ)} :=
    Set.ext fun _ ↦ OnePoint.identitySection_eq_zero_iff (𝕜 := ℂ)
  have hfin : {x | s x = 0}.Finite := hZ ▸ Set.finite_singleton _
  rw [VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _ hs
    Complex.finrank_real_complex hfin, show hfin.toFinset = {((0 : ℂ) : OnePoint ℂ)} by simp [hZ],
    Finset.sum_singleton]
  -- In the affine chart and the trivialization at `0`, the section reads as the identity.
  have hA : HasFDerivAt (fun y ↦ ((twistCore (𝕜 := ℂ) 1).localTriv ((0 : ℂ) : OnePoint ℂ)
      ⟨(chartAt ℂ ((0 : ℂ) : OnePoint ℂ)).symm y,
        s ((chartAt ℂ ((0 : ℂ) : OnePoint ℂ)).symm y)⟩).2)
      (((ContinuousLinearEquiv.refl ℂ ℂ : ℂ ≃L[ℂ] ℂ) : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ)) := by
    convert ContinuousLinearMap.hasFDerivAt _ using 1
    funext y
    rw [OnePoint.twistCore_localTriv_apply, OnePoint.chartAt_coe, OnePoint.affineChart_symm_apply,
      OnePoint.twistTransition_coe_coe]
    simp
  exact sectionIndex_eq_one_of_complexLinear (finrank_self ℂ) hs
    ((OnePoint.identitySection_eq_zero_iff (𝕜 := ℂ)).2 rfl) _ (by simp) _ hA

end SymplecticGeometry

end
