/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation

import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.ComplexLinear
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.TwistCore
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.LocalForm
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Sobolev
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Standard
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.Hilbert
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Contractible
import SymplecticGeometry.Analysis.Normed.Operator.Fredholm
import TauCeti.Analysis.Fredholm.ContinuousFamily
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.HomologicalOrientation
import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Holomorphic
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

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
* `SymplecticGeometry.existsUnique_eq_zero_of_mem_twistOneKernel`: for `J` tamed together with
  `i` by a two-form, a nonzero element of the kernel `twistOneKernel J` of `D_J` vanishes at
  exactly one point of the sphere.
* `SymplecticGeometry.surjective_sectionLinearization_of_mem_twistOneKernel`: that zero is
  simple: the linearization `TauCeti.sectionLinearization` of the section there is onto.
* `SymplecticGeometry.isFredholm_twistOneDelBarSobolev` and
  `SymplecticGeometry.index_twistOneDelBarSobolev`: for such `J` and every order `k`, the Sobolev
  realization `twistOneDelBarSobolev J k` is Fredholm of real index `4`.
* `SymplecticGeometry.finrank_twistOneKernel`: `twistOneKernel J` has complex dimension `2`.
* `SymplecticGeometry.twistOneDelBarSobolev_surjective`: `twistOneDelBarSobolev J k` is onto.

## Proof

The section `z` of `L` (`OnePoint.identitySection`) is continuous and vanishes only at `0`
(`OnePoint.identitySection_eq_zero_iff`). By Tau Ceti's
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex` the Euler
number is its local index at `0`. In the affine chart and the trivialization
`(twistCore 1).localTriv 0` the section reads as the identity of `ℂ`, a complex-linear
isomorphism, so this index is `1`
(`SymplecticGeometry.sectionIndex_eq_one_of_complexLinear`). This is the argument of
`Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass` on the sphere.

For the zero count, let `s ≠ 0` lie in `twistOneKernel J`. Its zeros are finite
(`SymplecticGeometry.finite_setOfPred_eq_zero_of_mem_twistOneKernel`), and at each of them it is
complex analytic in an isothermal chart `ψ` and a rescaled frame of `L` that reads the orientation
of the fibres as that of `ℂ`
(`SymplecticGeometry.exists_trivialization_analyticAt_of_mem_twistOneKernel`);
taming makes `ψ` carry the complex orientation of the sphere to that of `ℂ`
(`SymplecticGeometry.localHomologyMap_sub_complexManifoldHomologicalOrientation_of_tames`). By
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt` the
orders of vanishing of `s` in these coordinates add up to the Euler number `1`, and each is
positive (`TauCeti.VectorBundleOrientation.sectionIndex_pos_of_analyticAt`), since the zeros are
isolated. So there is one zero, of order one. A holomorphic function with a zero of order one has
a nonzero derivative there (`AnalyticAt.analyticOrderAt_deriv_add_one`). In the trivialization
`(twistCore 1).localTriv z` the coordinate of `s` is that holomorphic reading, composed with `ψ`,
times a factor that is only continuous but nonzero at the zero; at a zero such a factor multiplies
the derivative and nothing more (`TauCeti.mvfderiv_eq_comp_of_eventuallyEq_clm_apply`), so the
derivative of the coordinate is invertible, and so is the linearization
(`TauCeti.surjective_sectionLinearization_iff`).

For the index, give the structures tamed by `σ` the `C^∞` topology in the preferred frames of the
endomorphism bundle of the tangent bundle. There they form a contractible space
(`TauCeti.SmoothTwoForm.IsNondegenerate.contractibleSpace_tames`), on which `J ↦ D_J` is
continuous into the operator norm (`SymplecticGeometry.continuous_twistOneDelBarSobolev_tames`).
Every `D_J` has closed range and finite-dimensional kernel
(`SymplecticGeometry.isClosed_range_twistOneDelBarSobolev`,
`SymplecticGeometry.finiteDimensional_ker_twistOneDelBarSobolev`), and `D_i` is Fredholm of index
`4` (`SymplecticGeometry.isFredholm_twistOneDelBarSobolev_ofComplexManifold`). The target is
isomorphic to a Hilbert space
(`TauCeti.exists_continuousLinearEquiv_innerProductSpace_zeroOneSobolevSections`), so
`ContinuousOn.isFredholm_of_isPreconnected_of_continuousLinearEquiv` makes every `D_J` Fredholm,
and `Continuous.index_eq_of_preconnectedSpace` gives them all index `4`. The kernel of `D_J` has
the real dimension of `twistOneKernel J` (`SymplecticGeometry.finrank_ker_twistOneDelBarSobolev`),
and evaluation at `0` and `∞` is injective on `twistOneKernel J`, since a nonzero element has a
single zero; so this real dimension is at most `4`. As the index is the dimension of the kernel
minus that of the cokernel, the kernel has real dimension exactly `4`, and a Fredholm operator
whose index is the dimension of its kernel is onto
(`ContinuousLinearMap.IsFredholm.surjective_of_index_eq_finrank_ker`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class as a sum of indices of a section) and §14 (the canonical
  orientation of a complex vector bundle).
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 (the zeros of a section in the kernel of a real Cauchy–Riemann operator).
-/

public section

open Bundle Module TauCeti MeasureTheory
open OnePoint (twistCore identitySection)
open scoped Manifold VectorBundle.ComplexToReal ContDiff Topology TauCeti.ComplexManifold

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

variable {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}

/-- At each zero of a nonzero kernel element, its coordinate in the frame and chart of
`exists_trivialization_analyticAt_of_mem_twistOneKernel` has order one, and there is one zero. -/
private theorem exists_analyticOrderNatAt_eq_one_of_mem_twistOneKernel
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {s : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J) (hs₀ : s ≠ 0) :
    ∃ z₀, {x | s x = 0} = {z₀} ∧
      ∃ (e : Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) 1).Fiber))
        (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ∞), z₀ ∈ e.baseSet ∧
        z₀ ∈ ψ.source ∧
        AnalyticAt ℂ (fun w ↦ (e (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber)
          (ψ.toOpenPartialHomeomorph.symm w) (s (ψ.toOpenPartialHomeomorph.symm w)))).2)
          (ψ.toOpenPartialHomeomorph z₀) ∧
        analyticOrderNatAt (fun w ↦ (e (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber)
          (ψ.toOpenPartialHomeomorph.symm w) (s (ψ.toOpenPartialHomeomorph.symm w)))).2)
          (ψ.toOpenPartialHomeomorph z₀) = 1 ∧
        ∃ c : OnePoint ℂ → ℂ, ContinuousAt c z₀ ∧ c z₀ ≠ 0 ∧
          ∀ x (v : (twistCore (𝕜 := ℂ) 1).Fiber x), (e (TotalSpace.mk' ℂ x v)).2 =
            c x * ((twistCore (𝕜 := ℂ) 1).localTriv z₀ (TotalSpace.mk' ℂ x v)).2 := by
  -- The zeros, with `s` read as a section of `𝒪(1)`, as Tau Ceti's zero count reads them.
  have hZ : {x | (s x : (twistCore (𝕜 := ℂ) 1).Fiber x) = 0}.Finite :=
    finite_setOfPred_eq_zero_of_mem_twistOneKernel hs hs₀
  choose e he ψ hze hzψ hψ hA ho c hc hc₀ hec using
    fun z ↦ exists_trivialization_analyticAt_of_mem_twistOneKernel hs z
  have hφ₀ := fun z ↦ localHomologyMap_sub_complexManifoldHomologicalOrientation_of_tames hJ hi
    (ψ z) (hzψ z) (hψ z z (hzψ z))
  simp only [OpenPartialHomeomorph.centeredSourceRestrict_def] at hφ₀
  have hcont : Continuous fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x) :=
    ((mem_twistOneKernel_iff J).1 hs).1.continuous
  have hsum := VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt
    ((VectorBundleOrientation.complex ℂ (twistCore (𝕜 := ℂ) 1).Fiber).reindex
      (finCongr (by simp : 2 * finrank ℂ ℂ = 1 + 1))) Complex.finrank_real_complex
    (complexManifoldHomologicalOrientation ℂ (OnePoint ℂ) (finrank_self ℂ)) hcont
    (fun z ↦ (ψ z).toOpenPartialHomeomorph) e
    (fun _ ↦ Orientation.reindex ℝ ℂ (finCongr (by simp : 2 * Module.finrank ℂ ℂ = 1 + 1))
      (complexOrientation ℂ)) (fun z _ ↦ hzψ z) hZ (fun z _ ↦ hze z)
    (fun z _ ↦ .of_forall (ho z))
    (fun z _ ↦ hφ₀ z) (fun z _ ↦ hA z)
  rw [eulerNumber_twistCore_one] at hsum
  -- Each zero has positive order, since it is an isolated zero.
  have hpos : ∀ z, s z = 0 → 0 < (analyticOrderNatAt (fun w ↦ (e z (TotalSpace.mk' ℂ
      ((ψ z).toOpenPartialHomeomorph.symm w) (s ((ψ z).toOpenPartialHomeomorph.symm w)))).2)
        ((ψ z).toOpenPartialHomeomorph z) : ℤ) := fun z hz ↦ by
    rw [← VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt _ _ _ hcont (e z) _ (hze z)
      (hzψ z) (.of_forall (ho z)) (hφ₀ z) (hA z)]
    exact VectorBundleOrientation.sectionIndex_pos_of_analyticAt _ _ _ hcont (e z) _ (hze z)
      (hzψ z) (.of_forall (ho z)) (hφ₀ z) (hA z) hz
      (eventually_ne_zero_of_mem_twistOneKernel hs hs₀ z)
  -- A sum of positive integers equal to `1` has one term, equal to `1`.
  have hone : ∀ (T : Finset (OnePoint ℂ)) (f : OnePoint ℂ → ℤ), (∀ z ∈ T, 0 < f z) →
      ∑ z ∈ T, f z = 1 → ∃ z₀, T = {z₀} ∧ f z₀ = 1 := fun T f hf h ↦ by
    have hcard : (T.card : ℤ) ≤ 1 := by
      rw [← h, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact Finset.sum_le_sum fun z hz ↦ by have := hf z hz; omega
    have hne : T.Nonempty := Finset.nonempty_of_sum_ne_zero (h ▸ one_ne_zero)
    obtain ⟨z₀, rfl⟩ := (Finset.card_eq_one (s := T)).1 (by have := hne.card_pos; omega)
    exact ⟨z₀, rfl, by simpa using h⟩
  obtain ⟨z₀, hz₀, h1⟩ := hone _ _ (fun z hz ↦ hpos z ((Set.Finite.mem_toFinset _).1 hz))
    hsum.symm
  refine ⟨z₀, Set.ext fun x ↦ ?_, e z₀, ψ z₀, hze z₀, hzψ z₀, hA z₀, by exact_mod_cast h1, c z₀,
    hc z₀, hc₀ z₀, hec z₀⟩
  exact ((Set.Finite.mem_toFinset _).symm.trans (Iff.of_eq (congrArg (x ∈ ·) hz₀))).trans
    Finset.mem_singleton

/-- **A nonzero kernel element on `𝒪(1)` has exactly one zero.** Let a two-form `σ` on the
sphere tame both `J` and the standard structure `i`, and let `s ≠ 0` be a smooth section of
`𝒪(1)` with `D_J s = 0`. Then `s` vanishes at exactly one point of the sphere. -/
theorem existsUnique_eq_zero_of_mem_twistOneKernel {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {s : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J)
    (hs₀ : s ≠ 0) : ∃! z, s z = 0 := by
  obtain ⟨z₀, hZ, -⟩ := exists_analyticOrderNatAt_eq_one_of_mem_twistOneKernel hJ hi hs hs₀
  exact ⟨z₀, (Set.ext_iff.1 hZ z₀).2 rfl, fun z hz ↦ (Set.ext_iff.1 hZ z).1 hz⟩

/-- **The zero of a nonzero kernel element on `𝒪(1)` is simple.** Let a two-form
`σ` on the sphere tame both `J` and the standard structure `i`, and let `s ≠ 0` be a smooth
section of `𝒪(1)` with `D_J s = 0`. At a zero `z` of `s`, the linearization of `s`
(`TauCeti.sectionLinearization`: the derivative of the reading of `s` in the chart and the
trivialization at `z`, carried back to the fibre) is onto the fibre at `z`. -/
theorem surjective_sectionLinearization_of_mem_twistOneKernel
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {s : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J) (hs₀ : s ≠ 0) {z : OnePoint ℂ}
    (hz : s z = 0) :
    Function.Surjective (sectionLinearization (F := ℂ) (E := (twistCore (𝕜 := ℂ) 1).Fiber)
      𝓘(ℝ, ℂ) id s z) := by
  obtain ⟨z₀, hZ, e, ψ, hze, hzψ, hA, hord, c, hc, hc₀, hec⟩ :=
    exists_analyticOrderNatAt_eq_one_of_mem_twistOneKernel hJ hi hs hs₀
  obtain rfl : z = z₀ := (Set.ext_iff.1 hZ z).1 hz
  set h : ℂ → ℂ := fun w ↦ (e (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber)
    (ψ.toOpenPartialHomeomorph.symm w) (s (ψ.toOpenPartialHomeomorph.symm w)))).2
  set e₀ := (twistCore (𝕜 := ℂ) 1).localTriv z
  -- The holomorphic reading `h` of `s` has order one at `ψ z`, so it vanishes there with a
  -- nonzero complex derivative.
  obtain ⟨h0', hd⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hA (n := 1)).1
    (by simpa using (ENat.toNat_eq_iff one_ne_zero).1 hord)
  have h0 : h (ψ.toOpenPartialHomeomorph z) = 0 := by simpa using h0' 0 one_pos
  replace hd : deriv h (ψ.toOpenPartialHomeomorph z) ≠ 0 := by simpa using hd
  -- Near `z`, the coordinate of `s` in `e₀` is `(c x)⁻¹ h (ψ x)`.
  set C : OnePoint ℂ → ℂ →L[ℝ] ℂ := fun x ↦ (c x)⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have hC : ContinuousAt C z := (hc.inv₀ hc₀).smul continuousAt_const
  have hu : (fun x ↦ C x ((h ∘ ψ.toOpenPartialHomeomorph) x)) =ᶠ[𝓝 z]
      fun x ↦ (e₀ (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) (id x) (s x))).2 := by
    filter_upwards [ψ.open_source.mem_nhds hzψ, hc.eventually_ne hc₀] with x hx hcx
    -- `ψ⁻¹ (ψ x) = x`, rewritten under the dependent pair through the map `p ↦ ⟨p, s p⟩`.
    have hx' : (h ∘ ψ.toOpenPartialHomeomorph) x =
        (e (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x))).2 :=
      congrArg (fun p ↦ (e (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p))).2)
        (ψ.toOpenPartialHomeomorph.left_inv hx)
    simp only [C, hx', smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, id]
    rw [inv_mul_eq_iff_eq_mul₀ hcx]
    exact hec x (s x)
  have hψd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.toOpenPartialHomeomorph z :=
    (ψ.isLocalDiffeomorphAt _ _ ∞ hzψ).mdifferentiableAt (by simp)
  have hhd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h (ψ.toOpenPartialHomeomorph z) :=
    (hA.differentiableAt.restrictScalars ℝ).mdifferentiableAt
  have hcomp := hhd.comp z hψd
  rw [surjective_sectionLinearization_iff (e := e₀) continuousAt_id
    (by simp [e₀, OnePoint.twistCore_localTriv_baseSet])
    (mdifferentiableAt_of_eventuallyEq_clm_apply hu hC hcomp h0) hz,
    mvfderiv_eq_comp_of_eventuallyEq_clm_apply hu hC hcomp h0, mvfderiv_comp z hhd hψd,
    mvfderiv_eq_fderiv,
    (hA.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  have hDs := ((ψ.isLocalDiffeomorphAt _ _ ∞ hzψ).isInvertible_mfderiv (by simp)).surjective
  have hCs : Function.Surjective (C z) := fun y ↦ ⟨c z * y, by simp [C, hc₀]⟩
  have hds : Function.Surjective ((ContinuousLinearMap.toSpanSingleton ℂ
      (deriv h (ψ.toOpenPartialHomeomorph z))).restrictScalars ℝ) :=
    fun y ↦ ⟨y / deriv h (ψ.toOpenPartialHomeomorph z), by simpa using div_mul_cancel₀ y hd⟩
  simp only [ContinuousLinearMap.coe_comp]
  exact hCs.comp ((hds.comp (NormedSpace.fromTangentSpace _).surjective).comp hDs)

/-! ### Index, dimension of the kernel and surjectivity -/

section Index

variable {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}

/-- **A connected family.** Let a two-form `σ` on the sphere tame the standard structure `i`. For
every order `k`, the almost complex structures tamed by `σ` carry a topology in which they form a
preconnected space and on which `J ↦ D_J` is continuous into the operator norm topology. -/
private theorem exists_preconnectedSpace_continuous_twistOneDelBarSobolev (hi : σ.Tames 𝒊)
    (k : ℕ) : ∃ _ : TopologicalSpace {J // σ.Tames J}, PreconnectedSpace {J // σ.Tames J} ∧
      Continuous fun J : {J // σ.Tames J} ↦ twistOneDelBarSobolev J.val k := by
  let e (x : OnePoint ℂ) := trivializationAt (ℂ →L[ℝ] ℂ)
    (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x) x
  let U (x : OnePoint ℂ) : TopologicalSpace.Opens (OnePoint ℂ) := ⟨_, (e x).open_baseSet⟩
  have hU : ∀ x, (U x : Set (OnePoint ℂ)) ⊆ (e x).baseSet := fun _ ↦ subset_rfl
  have hcover : ∀ x, ∃ y, x ∈ U y := fun x ↦ ⟨x, mem_baseSet_trivializationAt _ _ x⟩
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := hi.isNondegenerate.contractibleSpace_tames e U hU hcover
  exact ⟨_, inferInstance, continuous_twistOneDelBarSobolev_tames e U hU hcover σ k⟩

/-- **`D_J` is Fredholm.** Let a two-form `σ` on the sphere tame both `J` and the standard
structure `i`. For every order `k`, the operator
`D_J : W^{k+1,2}(𝒪(1)) → W^{k,2}(Λ^{0,1} ⊗ 𝒪(1))` is Fredholm. -/
theorem isFredholm_twistOneDelBarSobolev (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (k : ℕ) :
    (twistOneDelBarSobolev J k).IsFredholm := by
  obtain ⟨_, _, hD⟩ := exists_preconnectedSpace_continuous_twistOneDelBarSobolev hi k
  obtain ⟨H, _, _, _, ⟨φ⟩⟩ :=
    exists_continuousLinearEquiv_innerProductSpace_zeroOneSobolevSections (twistCoreAtlas 1)
      volume k
  exact hD.continuousOn.isFredholm_of_isPreconnected_of_continuousLinearEquiv φ (s := Set.univ)
    (fun J _ ↦ finiteDimensional_ker_twistOneDelBarSobolev J.val k J.property hi)
    (fun J _ ↦ isClosed_range_twistOneDelBarSobolev J.val k J.property hi)
    isPreconnected_univ (x₀ := ⟨𝒊, hi⟩) (Set.mem_univ _)
    (isFredholm_twistOneDelBarSobolev_ofComplexManifold k).1 (x := ⟨J, hJ⟩) (Set.mem_univ _)

/-- **`D_J` has index four.** Let a two-form `σ` on the sphere tame both `J` and the standard
structure `i`. For every order `k`, the real index of
`D_J : W^{k+1,2}(𝒪(1)) → W^{k,2}(Λ^{0,1} ⊗ 𝒪(1))` is `4`. -/
theorem index_twistOneDelBarSobolev (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (k : ℕ) :
    (twistOneDelBarSobolev J k).index = 4 := by
  obtain ⟨_, _, hD⟩ := exists_preconnectedSpace_continuous_twistOneDelBarSobolev hi k
  rw [Continuous.index_eq_of_preconnectedSpace hD
    (fun J ↦ isFredholm_twistOneDelBarSobolev J.property hi k) ⟨J, hJ⟩ ⟨𝒊, hi⟩]
  exact (isFredholm_twistOneDelBarSobolev_ofComplexManifold k).2

/-- Evaluation at `0` and at `∞` is injective on `twistOneKernel J`, when a two-form tames `J`
and `i`, since a nonzero element has only one zero; so its complex dimension is at most two. -/
private theorem finrank_twistOneKernel_le (hJ : σ.Tames J) (hi : σ.Tames 𝒊) :
    finrank ℂ (twistOneKernel J) ≤ 2 := by
  let ev : twistOneKernel J →ₗ[ℂ] ℂ × ℂ :=
    ((LinearMap.proj ((0 : ℂ) : OnePoint ℂ)).prod
      (LinearMap.proj (OnePoint.infty : OnePoint ℂ))).comp
      (twistOneKernel J).subtype
  have hev : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun s hs ↦ ?_
    by_contra hs₀
    have h0 : s.val ((0 : ℂ) : OnePoint ℂ) = 0 := congrArg Prod.fst hs
    have hinf : s.val OnePoint.infty = 0 := congrArg Prod.snd hs
    obtain ⟨z, -, hz⟩ := existsUnique_eq_zero_of_mem_twistOneKernel hJ hi s.property
      (fun h ↦ hs₀ (Subtype.ext h))
    exact OnePoint.coe_ne_infty _ ((hz _ h0).trans (hz _ hinf).symm)
  simpa using LinearMap.finrank_le_finrank_of_injective hev

/-- **The kernel of `D_J` is a complex plane.** Let a two-form `σ` on the sphere tame both `J` and
the standard structure `i`. Then the space `twistOneKernel J` of smooth sections `s` of `𝒪(1)`
with `D_J s = 0` has complex dimension two. -/
theorem finrank_twistOneKernel (hJ : σ.Tames J) (hi : σ.Tames 𝒊) :
    finrank ℂ (twistOneKernel J) = 2 := by
  have hind := index_twistOneDelBarSobolev hJ hi 0
  rw [ContinuousLinearMap.index_eq_finrank_sub, finrank_ker_twistOneDelBarSobolev hJ hi 0,
    finrank_real_of_complex] at hind
  have := finrank_twistOneKernel_le hJ hi
  omega

/-- **`D_J` is onto.** Let a two-form `σ` on the sphere tame both `J` and the standard structure
`i`. For every order `k`, every `W^{k,2}` `(0,1)`-form with values in `𝒪(1)` on the sphere is
`D_J w` for a `W^{k+1,2}` section `w` of `𝒪(1)`. -/
theorem twistOneDelBarSobolev_surjective (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (k : ℕ) :
    Function.Surjective (twistOneDelBarSobolev J k) := by
  refine (isFredholm_twistOneDelBarSobolev hJ hi k).surjective_of_index_eq_finrank_ker ?_
  rw [index_twistOneDelBarSobolev hJ hi k, finrank_ker_twistOneDelBarSobolev hJ hi k,
    finrank_real_of_complex, finrank_twistOneKernel hJ hi]
  norm_num

end Index

end SymplecticGeometry

end
