/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation

import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.ComplexLinear
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.TwistCore
import SymplecticGeometry.Topology.VectorBundle.ZeroSet
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.LocalForm
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.LowerOrder
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
public import TauCeti.Analysis.Normed.Operator.Splitting.Basic
import TauCeti.Analysis.Normed.Operator.Splitting.Family
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
import TauCeti.Topology.Algebra.Module.ComplexSmulI
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.FrameTopology
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.ContDiffBound
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic

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
* `SymplecticGeometry.isPseudoholomorphicOn_div_of_mem_twistOneKernel`: for `s, t` in
  `twistOneKernel J`, the quotient `s / t` is pseudoholomorphic from `J` to the standard structure
  of `ℂ` where `t ≠ 0` (`isPseudoholomorphicAt_div_of_mem_twistOneKernel` at a point).
* `SymplecticGeometry.isFredholm_twistOneDelBarSobolev` and
  `SymplecticGeometry.index_twistOneDelBarSobolev`: for such `J` and every order `k`, the Sobolev
  realization `twistOneDelBarSobolev J k` is Fredholm of real index `4`.
* `SymplecticGeometry.finrank_twistOneKernel`: `twistOneKernel J` has complex dimension `2`.
* `SymplecticGeometry.twistOneDelBarSobolev_surjective`: `twistOneDelBarSobolev J k` is onto.
* `SymplecticGeometry.twistOneKernelEval_bijective`: evaluation at `0` and `∞` identifies
  `twistOneKernel J` with `ℂ × ℂ`.
* `SymplecticGeometry.exists_mem_twistOneKernel_eq_zero`: every point is the zero of a nonzero
  element of `twistOneKernel J`; by `SymplecticGeometry.exists_smul_eq_of_mem_twistOneKernel` and
  `SymplecticGeometry.finrank_twistOneKernel_inf_ker_proj`, the elements vanishing there form a
  complex line.
* `SymplecticGeometry.twistOneKernelTransfer`: given a map `Q` to `ℂ × ℂ` that stabilizes `D_J`,
  the complex linear map from `twistOneKernel J₀` to `twistOneKernel J` sending `s` to the element
  on which `Q` is `(s 0, s ∞)`; it is bijective (`twistOneKernelTransfer_bijective`).
* `SymplecticGeometry.exists_twistOneKernelFamily`: near a structure `J₀` tamed by `σ`, complex
  linear maps `T J` from `twistOneKernel J₀` onto `twistOneKernel J`, the inclusion at `J₀`, such
  that `J ↦ T J s` is continuous at `J₀` into `W^{k+1,2}` for every order `k`.
* `SymplecticGeometry.exists_continuousAt_twistOneKernelFamily`: maps as in
  `exists_twistOneKernelFamily`, with `J ↦ T J s` continuous at `J₀` into the smooth sections of
  `𝒪(1)` with `ContMDiffSection.frameTopology`, for every frame system.

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

For the quotient `u = s / t` of two kernel elements near a point where `t ≠ 0`, `u` is the
quotient of the coordinates of `s` and `t` in the frame of the chart, hence differentiable
(`OnePoint.mdifferentiableAt_div_twistCore`), and `s = u • t` near the point, so that
`D_J (u • t) = D_J s = 0` there by locality
(`TauCeti.IsRealCauchyRiemannOperator.apply_eq_of_eventuallyEq`). As `D_J` is complex linear,
`t ≠ 0` and `D_J t = 0`, this is the pseudoholomorphy of `u`
(`TauCeti.IsRealCauchyRiemannOperator.apply_smul_eq_zero_iff_isPseudoholomorphicAt`, from the
Leibniz rule `TauCeti.IsRealCauchyRiemannOperator.leibniz_complex`). This adapts Tau Ceti's
`TauCeti.IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul` and
`TauCeti.IsRealCauchyRiemannOperator.apply_smul_eq_zero_iff`, stated over a complex manifold, to
an arbitrary structure `J` on the sphere.

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

For the family, fix `J₀`. A projection of `W^{1,2}` onto the finite-dimensional kernel of
`D_{J₀}`, read in `ℂ × ℂ` through `twistOneKernelEval J₀` and averaged with its conjugate by
multiplication by `i` (`SymplecticGeometry.twistOneSobolevSMulI`), gives a real linear map `P` that
is complex linear on smooth sections (`SymplecticGeometry.exists_twistOneKernelProjection`). As
`D_{J₀}` is onto at every order and its kernel is the same at every order, the pair of `D_{J₀}` on
`W^{k+1,2}` and `P` composed with the inclusion in `W^{1,2}` is invertible
(`SymplecticGeometry.isInvertible_twistOneDelBarSobolev_prod`), so it stays invertible for `J`
near `J₀` (`ContinuousLinearMap.exists_isOpen_isInvertible_prod`). Tau Ceti's
`ContinuousLinearMap.kerEquivOfProd` of this pair identifies `ℂ × ℂ` with the kernel of `D_J`
(`SymplecticGeometry.twistOneKernelEquivOfProd`); composed with evaluation at `0` and `∞`, it gives
the complex linear map `SymplecticGeometry.twistOneKernelTransfer`. Its values are the
`ContinuousLinearMap.kerSection` of the pair, the same smooth section at every order
(`SymplecticGeometry.kerSection_twistOneDelBarSobolev_toOrderOne`), which depends continuously on
`J` at each order (`ContinuousAt.kerSection`). For the `C^∞` topology, fix a chart of the atlas
`twistCoreAtlas 1` and an order `j`. Continuity into `W^{j+2,2}` makes the derivatives of order
`j` of the chart readings of continuous representatives converge locally uniformly on the chart
image (`TauCeti.SobolevSection.tendstoLocallyUniformlyOn_iteratedFDeriv_coord_toSection`), and
`TauCeti.FiniteBundleAtlas.tendsto_frameTopology_of_tendstoLocallyUniformlyOn` gives convergence
in the frame topology of every frame system.

The construction of `P` and the proof of `isInvertible_twistOneDelBarSobolev_prod` adapt Tau
Ceti's `ContinuousLinearMap.exists_isOpen_isInvertible_prod_coprod_of_surjective`, with its
averaging step from `Submodule.ClosedComplemented.of_restrictScalars`: a real projection onto the
kernel from `Submodule.ClosedComplemented.of_finiteDimensional`, made complex linear by averaging,
read in complex coordinates of the kernel; the pair is injective, and onto by adding to a preimage
the element of the kernel with the right value. Those declarations do not apply directly, since
they are about complex linear operators and complex submodules, and the Sobolev sections of `𝒪(1)`
carry no `Module ℂ` structure here: multiplication by `i` is the real linear map
`twistOneSobolevSMulI`.

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
        (finCongr Complex.two_mul_finrank_self)).eulerClass
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
      (finCongr Complex.two_mul_finrank_self)) Complex.finrank_real_complex
    (complexManifoldHomologicalOrientation ℂ (OnePoint ℂ) (finrank_self ℂ)) hcont
    (fun z ↦ (ψ z).toOpenPartialHomeomorph) e
    (fun _ ↦ Orientation.reindex ℝ ℂ (finCongr Complex.two_mul_finrank_self)
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

/-- **Two zeros of a nonzero kernel element on `𝒪(1)` coincide.** Let a two-form `σ` on the
sphere tame both `J` and the standard structure `i`, and let `s ≠ 0` be a smooth section of
`𝒪(1)` with `D_J s = 0`. If `s x = 0` and `s y = 0`, then `x = y`. -/
theorem eq_of_mem_twistOneKernel_of_eq_zero {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {s : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J)
    (hs₀ : s ≠ 0) {x y : OnePoint ℂ} (hx : s x = 0) (hy : s y = 0) : x = y :=
  (existsUnique_eq_zero_of_mem_twistOneKernel hJ hi hs hs₀).unique hx hy

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

/-! ### Quotients of kernel elements -/

/-- **The quotient of two kernel elements on `𝒪(1)` is `J`-holomorphic.** Let `s` and `t` be
smooth sections of `𝒪(1)` with `D_J s = D_J t = 0`. At a point `x` where `t x ≠ 0`, the
function `p ↦ s p / t p` is pseudoholomorphic from `J` to the standard complex structure of `ℂ`.
The quotient is well defined as a function, since `s p` and `t p` lie in the same fibre. -/
theorem isPseudoholomorphicAt_div_of_mem_twistOneKernel {s t : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (ht : t ∈ twistOneKernel J) {x : OnePoint ℂ} (hx : t x ≠ 0) :
    IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ)
      (fun p ↦ s p / t p) x := by
  obtain ⟨hs₁, hs₂⟩ := (mem_twistOneKernel_iff J).1 hs
  obtain ⟨ht₁, ht₂⟩ := (mem_twistOneKernel_iff J).1 ht
  have hsx := hs₁.mdifferentiableAt (x := x) (by simp)
  have htx := ht₁.mdifferentiableAt (x := x) (by simp)
  have hu := OnePoint.mdifferentiableAt_div_twistCore 1 hsx htx hx
  -- Near `x`, `s` is the quotient times `t`.
  let t' : Π p, (twistCore (𝕜 := ℂ) 1).Fiber p := t
  have hst : ∀ᶠ p in 𝓝 x, ((fun p ↦ s p / t p) • t') p = s p := by
    filter_upwards [VectorBundle.eventually_ne_zero ℝ (b := id)
      (E := (twistCore (𝕜 := ℂ) 1).Fiber) (s := t) htx.continuousAt hx] with p hp
    -- The fibres of `𝒪(1)` are `ℂ`, with its multiplication as scalar action.
    exact div_mul_cancel₀ (s p) hp
  have hD := isRealCauchyRiemannOperator_twistOneDelBar J
  rw [← (hD.apply_smul_eq_zero_iff_isPseudoholomorphicAt (isComplexLinearOperator_twistOneDelBar J)
    htx hx (congrFun ht₂ x) hu), hD.apply_eq_of_eventuallyEq hsx hst, congrFun hs₂ x,
    Pi.zero_apply]

/-- **The quotient of two kernel elements on `𝒪(1)` is `J`-holomorphic.** For smooth sections
`s` and `t` of `𝒪(1)` with `D_J s = D_J t = 0`, the function `p ↦ s p / t p` is
pseudoholomorphic from `J` to the standard complex structure of `ℂ` on the set where `t` does
not vanish. -/
theorem isPseudoholomorphicOn_div_of_mem_twistOneKernel {s t : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (ht : t ∈ twistOneKernel J) :
    IsPseudoholomorphicOn J (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ)
      (fun p ↦ s p / t p) {x | t x ≠ 0} :=
  isPseudoholomorphicOn_iff.2 fun _ hx ↦
  (isPseudoholomorphicAt_div_of_mem_twistOneKernel hs ht hx).isPseudoholomorphicWithinAt

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

/-- Evaluation at `0` and at `∞` on `twistOneKernel J`, as a complex linear map to `ℂ × ℂ`. -/
noncomputable def twistOneKernelEval (J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) :
    twistOneKernel J →ₗ[ℂ] ℂ × ℂ :=
  ((LinearMap.proj ((0 : ℂ) : OnePoint ℂ)).prod
    (LinearMap.proj (OnePoint.infty : OnePoint ℂ))).comp (twistOneKernel J).subtype

@[simp]
theorem twistOneKernelEval_apply (s : twistOneKernel J) :
    twistOneKernelEval J s = (s.val ((0 : ℂ) : OnePoint ℂ), s.val OnePoint.infty) :=
  (rfl)

/-- Evaluation at `0` and at `∞` is injective on `twistOneKernel J`, when a two-form tames `J`
and `i`, since a nonzero element has only one zero. -/
theorem twistOneKernelEval_injective (hJ : σ.Tames J) (hi : σ.Tames 𝒊) :
    Function.Injective (twistOneKernelEval J) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ?_
  by_contra hs₀
  have h0 : s.val ((0 : ℂ) : OnePoint ℂ) = 0 := congrArg Prod.fst hs
  have hinf : s.val OnePoint.infty = 0 := congrArg Prod.snd hs
  exact OnePoint.coe_ne_infty _ (eq_of_mem_twistOneKernel_of_eq_zero hJ hi s.property
    (fun h ↦ hs₀ (Subtype.ext h)) h0 hinf)

/-- The complex dimension of `twistOneKernel J` is at most two, by
`twistOneKernelEval_injective`. -/
private theorem finrank_twistOneKernel_le (hJ : σ.Tames J) (hi : σ.Tames 𝒊) :
    finrank ℂ (twistOneKernel J) ≤ 2 := by
  simpa using LinearMap.finrank_le_finrank_of_injective (twistOneKernelEval_injective hJ hi)

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

/-- `twistOneKernel J` is finite dimensional over `ℂ`, when a two-form tames `J` and `i`. -/
theorem finiteDimensional_twistOneKernel (hJ : σ.Tames J) (hi : σ.Tames 𝒊) :
    FiniteDimensional ℂ (twistOneKernel J) :=
  Module.finite_of_finrank_pos (by rw [finrank_twistOneKernel hJ hi]; norm_num)

/-- **`D_J` is onto.** Let a two-form `σ` on the sphere tame both `J` and the standard structure
`i`. For every order `k`, every `W^{k,2}` `(0,1)`-form with values in `𝒪(1)` on the sphere is
`D_J w` for a `W^{k+1,2}` section `w` of `𝒪(1)`. -/
theorem twistOneDelBarSobolev_surjective (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (k : ℕ) :
    Function.Surjective (twistOneDelBarSobolev J k) := by
  refine (isFredholm_twistOneDelBarSobolev hJ hi k).surjective_of_index_eq_finrank_ker ?_
  rw [index_twistOneDelBarSobolev hJ hi k, finrank_ker_twistOneDelBarSobolev hJ hi k,
    finrank_real_of_complex, finrank_twistOneKernel hJ hi]
  norm_num

/-- **Evaluation at `0` and `∞` identifies the kernel with `ℂ²`.** Let a two-form `σ` on the
sphere tame both `J` and the standard structure `i`. Then `s ↦ (s 0, s ∞)` is a bijection from
`twistOneKernel J` onto `ℂ × ℂ`. -/
theorem twistOneKernelEval_bijective (hJ : σ.Tames J) (hi : σ.Tames 𝒊) :
    Function.Bijective (twistOneKernelEval J) := by
  have := finiteDimensional_twistOneKernel hJ hi
  exact ⟨twistOneKernelEval_injective hJ hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [finrank_twistOneKernel hJ hi])).1 (twistOneKernelEval_injective hJ hi)⟩

/-- **Every point is the zero of a nonzero kernel element.** Let a two-form `σ` on the sphere
tame both `J` and the standard structure `i`. Then for every point `x` of the sphere, some nonzero
`s ∈ twistOneKernel J` vanishes at `x`. -/
theorem exists_mem_twistOneKernel_eq_zero (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (x : OnePoint ℂ) :
    ∃ s ∈ twistOneKernel J, s ≠ 0 ∧ s x = 0 := by
  have := finiteDimensional_twistOneKernel hJ hi
  -- Evaluation at `x` goes to a line, so its kernel in the plane `twistOneKernel J` is nonzero.
  set f : twistOneKernel J →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (twistOneKernel J).subtype
  obtain ⟨s, hs, hs₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by simp [finrank_twistOneKernel hJ hi]))
  refine ⟨s.val, s.property, fun h ↦ hs₀ (Subtype.ext h), ?_⟩
  simpa [f] using LinearMap.mem_ker.1 hs

/-- **Kernel elements with a common zero are proportional.** Let a two-form `σ` on the sphere tame
both `J` and the standard structure `i`, and let `s, t ∈ twistOneKernel J` vanish at a point `x`,
with `s ≠ 0`. Then `t` is a complex multiple of `s`. -/
theorem exists_smul_eq_of_mem_twistOneKernel (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {s t : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J) (ht : t ∈ twistOneKernel J)
    (hs₀ : s ≠ 0) {x : OnePoint ℂ} (hsx : s x = 0) (htx : t x = 0) :
    ∃ c : ℂ, c • s = t := by
  -- At a second point `y`, the section `s` does not vanish; match `t` there.
  obtain ⟨y, hyx⟩ : ∃ y : OnePoint ℂ, y ≠ x := exists_ne x
  have hsy : s y ≠ 0 := fun h ↦ hyx (eq_of_mem_twistOneKernel_of_eq_zero hJ hi hs hs₀ h hsx)
  refine ⟨t y / s y, ?_⟩
  by_contra hne
  have hu : t - (t y / s y) • s ∈ twistOneKernel J := sub_mem ht (Submodule.smul_mem _ _ hs)
  have hu₀ : t - (t y / s y) • s ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hux : (t - (t y / s y) • s) x = 0 := by simp [hsx, htx]
  have huy : (t - (t y / s y) • s) y = 0 := by simp [div_mul_cancel₀ _ hsy]
  exact hyx (eq_of_mem_twistOneKernel_of_eq_zero hJ hi hu hu₀ huy hux)

/-- **The kernel elements vanishing at a point form a complex line.** Let a two-form `σ` on the
sphere tame both `J` and the standard structure `i`. Then for every point `x` of the sphere, the
elements of `twistOneKernel J` that vanish at `x` form a subspace of complex dimension one. -/
theorem finrank_twistOneKernel_inf_ker_proj (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (x : OnePoint ℂ) :
    finrank ℂ ↥(twistOneKernel J ⊓
      LinearMap.ker (LinearMap.proj x : (OnePoint ℂ → ℂ) →ₗ[ℂ] ℂ)) = 1 := by
  obtain ⟨s, hs, hs₀, hsx⟩ := exists_mem_twistOneKernel_eq_zero hJ hi x
  refine (finrank_eq_one_iff_of_ne_zero' (⟨s, hs, hsx⟩ : ↥(twistOneKernel J ⊓
      LinearMap.ker (LinearMap.proj x : (OnePoint ℂ → ℂ) →ₗ[ℂ] ℂ)))
    fun h ↦ hs₀ (congrArg Subtype.val h)).2 fun ⟨t, ht, htx⟩ ↦ ?_
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_twistOneKernel hJ hi hs ht hs₀ hsx htx
  exact ⟨c, Subtype.ext hc⟩

end Index

/-! ### The kernels near a given structure -/

section Family

variable {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}

/-- Multiplication by `i` on the `W^{k,2}` sections of `𝒪(1)`: the action of the smooth section
`x ↦ i` of the endomorphism bundle (`TauCeti.contMDiff_smulIEquiv_bundle`). -/
noncomputable def twistOneSobolevSMulI (k : ℕ) :
    SobolevSection (twistCoreAtlas 1) volume 2 k →L[ℝ]
      SobolevSection (twistCoreAtlas 1) volume 2 k :=
  SobolevSection.bundleMapL (twistCoreAtlas 1) (twistCoreAtlas 1).closure_dom_subset_baseSet
    (TauCeti.contMDiff_smulIEquiv_bundle (n := ∞)) volume 2 k

theorem twistOneSobolevSMulI_def (k : ℕ) :
    twistOneSobolevSMulI k = SobolevSection.bundleMapL (twistCoreAtlas 1)
      (twistCoreAtlas 1).closure_dom_subset_baseSet
      (TauCeti.contMDiff_smulIEquiv_bundle (n := ∞)) volume 2 k :=
  (rfl)

/-- On the Sobolev section of an element `s` of `twistOneKernel J`, multiplication by `i` gives
the Sobolev section of `i • s`. -/
theorem twistOneSobolevSMulI_twistOneKernelSobolev (k : ℕ) (s : twistOneKernel J) :
    twistOneSobolevSMulI (k + 1) (twistOneKernelSobolev J k s) =
      twistOneKernelSobolev J k (Complex.I • s) := by
  rw [twistOneSobolevSMulI_def, twistOneKernelSobolev_apply, twistOneKernelSobolev_apply]
  refine (SobolevSection.bundleMapL_ofContMDiffSection _).trans ?_
  exact congrArg _ (ContMDiffSection.ext fun x ↦ by
    simp only [ContMDiffSection.coeFn_mk, coe_twistOneKernelToContMDiffSection, Submodule.coe_smul,
      Pi.smul_apply]
    exact Complex.smulIEquiv_apply (s.val x))

/-- Lowering the order of the Sobolev section of an element of `twistOneKernel J` gives its Sobolev
section of order one. -/
theorem toOrderOne_twistOneKernelSobolev (k : ℕ) (s : twistOneKernel J) :
    (twistCoreAtlas 1).sectionChartData.toOrderOne volume 2 k (twistOneKernelSobolev J k s) =
      twistOneKernelSobolev J 0 s := by
  refine SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_
  rw [SectionChartData.chartValueL_toOrderOne, twistOneKernelSobolev_apply,
    twistOneKernelSobolev_apply]
  have h₁ := SobolevSection.chartValueL_ofContMDiffSection_ae (twistCoreAtlas 1) volume 2 (k + 1)
    (twistOneKernelToContMDiffSection J k s) i
  have h₀ := SobolevSection.chartValueL_ofContMDiffSection_ae (twistCoreAtlas 1) volume 2 (0 + 1)
    (twistOneKernelToContMDiffSection J 0 s) i
  rw [coe_twistOneKernelToContMDiffSection] at h₁ h₀
  exact h₁.trans h₀.symm

/-- Multiplication by `i` twice is `-1` on the Sobolev sections of elements of `twistOneKernel J`.
-/
private theorem twistOneSobolevSMulI_twistOneSobolevSMulI (s : twistOneKernel J) :
    twistOneSobolevSMulI 1 (twistOneSobolevSMulI 1 (twistOneKernelSobolev J 0 s)) =
      -twistOneKernelSobolev J 0 s := by
  rw [twistOneSobolevSMulI_twistOneKernelSobolev, twistOneSobolevSMulI_twistOneKernelSobolev,
    smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]

/-- **A complex projection onto the kernel at `J₀`.** Let a two-form `σ` tame both `J₀` and the
standard structure `i`. There is a continuous real linear map `P` from `W^{1,2}(𝒪(1))` to `ℂ × ℂ`
that is evaluation at `0` and `∞` on the elements of `twistOneKernel J₀`, and that commutes with
multiplication by `i` on the elements of `twistOneKernel J` for every `J`. -/
theorem exists_twistOneKernelProjection {J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ₀ : σ.Tames J₀) (hi : σ.Tames 𝒊) :
    ∃ P : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ,
      (∀ s : twistOneKernel J₀, P (twistOneKernelSobolev J₀ 0 s) = twistOneKernelEval J₀ s) ∧
      ∀ (J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) (s : twistOneKernel J),
        P (twistOneSobolevSMulI 1 (twistOneKernelSobolev J 0 s)) =
          Complex.I • P (twistOneKernelSobolev J 0 s) := by
  set K := (twistOneDelBarSobolev J₀ 0).ker
  have : FiniteDimensional ℝ K := finiteDimensional_ker_twistOneDelBarSobolev J₀ 0 hJ₀ hi
  obtain ⟨P₁, hP₁⟩ := Submodule.ClosedComplemented.of_finiteDimensional K
  let e := twistOneKernelSobolevEquiv hJ₀ hi 0
  -- A real projection, read in `ℂ × ℂ`, then averaged with its conjugate by `i`.
  let Q : K →L[ℝ] ℂ × ℂ := ⟨((twistOneKernelEval J₀).restrictScalars ℝ).comp e.symm.toLinearMap,
    LinearMap.continuous_of_finiteDimensional (E := K) _⟩
  let P₂ := Q.comp P₁
  have hP₂ (s : twistOneKernel J₀) :
      P₂ (twistOneKernelSobolev J₀ 0 s) = twistOneKernelEval J₀ s := by
    have : P₁ (twistOneKernelSobolev J₀ 0 s) = e s := by
      rw [← coe_twistOneKernelSobolevEquiv_apply hJ₀ hi]; exact hP₁ (e s)
    simp [P₂, Q, this]
  refine ⟨(2⁻¹ : ℝ) • (P₂ - (Complex.I • ContinuousLinearMap.id ℝ (ℂ × ℂ)).comp
    (P₂.comp (twistOneSobolevSMulI 1))), fun s ↦ ?_, fun J s ↦ ?_⟩
  · have h₁ := twistOneSobolevSMulI_twistOneKernelSobolev 0 s
    simp only [FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
      Pi.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, h₁, hP₂, map_smul]
    match_scalars
    simp [Complex.ext_iff]
    norm_num
  · have h₂ := twistOneSobolevSMulI_twistOneSobolevSMulI s
    simp only [FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
      Pi.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, h₂, map_neg]
    match_scalars <;> simp [Complex.ext_iff]

/-- **The stabilized operator is invertible at `J₀`.** Let a two-form `σ` tame both `J₀` and the
standard structure `i`, and let `P` from `W^{1,2}(𝒪(1))` to `ℂ × ℂ` be evaluation at `0` and `∞`
on the elements of `twistOneKernel J₀`. For every order `k`, the pair of `D_{J₀}` on `W^{k+1,2}`
and `P` composed with the inclusion of `W^{k+1,2}` in `W^{1,2}` is invertible. -/
theorem isInvertible_twistOneDelBarSobolev_prod
    {J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ₀ : σ.Tames J₀) (hi : σ.Tames 𝒊)
    {P : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (hP : ∀ s : twistOneKernel J₀, P (twistOneKernelSobolev J₀ 0 s) = twistOneKernelEval J₀ s)
    (k : ℕ) :
    ((twistOneDelBarSobolev J₀ k).prod
      (P.comp ((twistCoreAtlas 1).sectionChartData.toOrderOne volume 2 k))).IsInvertible := by
  set Q := P.comp ((twistCoreAtlas 1).sectionChartData.toOrderOne volume 2 k)
  have hQ (s : twistOneKernel J₀) : Q (twistOneKernelSobolev J₀ k s) = twistOneKernelEval J₀ s := by
    rw [ContinuousLinearMap.comp_apply, toOrderOne_twistOneKernelSobolev, hP]
  have hker := range_twistOneKernelSobolev hJ₀ hi k
  have hinj : ((twistOneDelBarSobolev J₀ k).prod Q).ker = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have hx₁ : x ∈ (twistOneDelBarSobolev J₀ k).ker := congrArg Prod.fst hx
    rw [← hker] at hx₁
    obtain ⟨s, rfl⟩ := hx₁
    have hs : twistOneKernelEval J₀ s = 0 := (hQ s).symm.trans (congrArg Prod.snd hx)
    rw [(twistOneKernelEval_injective hJ₀ hi) (hs.trans (map_zero _).symm), map_zero]
  have hsurj : ((twistOneDelBarSobolev J₀ k).prod Q).range = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun ⟨y, v⟩ ↦ ?_
    obtain ⟨x, rfl⟩ := twistOneDelBarSobolev_surjective hJ₀ hi k y
    obtain ⟨s, hs⟩ := (twistOneKernelEval_bijective hJ₀ hi).2 (v - Q x)
    have hDs : twistOneDelBarSobolev J₀ k (twistOneKernelSobolev J₀ k s) = 0 :=
      LinearMap.mem_ker.1 (hker ▸ LinearMap.mem_range_self _ s)
    refine ⟨x + twistOneKernelSobolev J₀ k s, ?_⟩
    simp [hDs, hQ, hs]
  exact ⟨ContinuousLinearEquiv.ofBijective _ hinj hsurj, rfl⟩

/-- **The kernel section at order `k` is the smooth solution.** Let a two-form `σ` tame both `J`
and the standard structure `i`, and let `Q` from `W^{1,2}(𝒪(1))` to `ℂ × ℂ` be such that the pair
of `D_J` on `W^{k+1,2}` and `Q` composed with the inclusion in `W^{1,2}` is invertible. If `Q` takes
the value `v` on the element `t` of `twistOneKernel J`, then the kernel section of the pair sends
`v` to the Sobolev section of `t`. -/
theorem kerSection_twistOneDelBarSobolev_toOrderOne (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {k : ℕ}
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J k).prod
      (Q.comp ((twistCoreAtlas 1).sectionChartData.toOrderOne volume 2 k))).IsInvertible)
    {v : ℂ × ℂ} {t : twistOneKernel J} (ht : Q (twistOneKernelSobolev J 0 t) = v) :
    (twistOneDelBarSobolev J k).kerSection
        (Q.comp ((twistCoreAtlas 1).sectionChartData.toOrderOne volume 2 k)) v =
      twistOneKernelSobolev J k t := by
  rw [← ht, ← toOrderOne_twistOneKernelSobolev k t, ← ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.kerSection_apply_of_mem_ker h
    (by rw [← range_twistOneKernelSobolev hJ hi k]; exact LinearMap.mem_range_self _ t)

/-- The element of `twistOneKernel J` with prescribed values of a stabilizing map. Let a two-form
`σ` tame both `J` and the standard structure `i`, and let `Q` from `W^{1,2}(𝒪(1))` to `ℂ × ℂ` be
such that the pair of `D_J` and `Q` is invertible. This is the real linear isomorphism from `ℂ × ℂ`
onto `twistOneKernel J` that sends `v` to the element on which `Q` takes the value `v`: Tau Ceti's
`ContinuousLinearMap.kerEquivOfProd`, read through `twistOneKernelSobolevEquiv`. -/
noncomputable def twistOneKernelEquivOfProd (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible) : (ℂ × ℂ) ≃ₗ[ℝ] twistOneKernel J :=
  (ContinuousLinearMap.kerEquivOfProd _ Q h).toLinearEquiv.trans
    (twistOneKernelSobolevEquiv hJ hi 0).symm

theorem twistOneKernelEquivOfProd_def (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible) :
    twistOneKernelEquivOfProd hJ hi h =
      (ContinuousLinearMap.kerEquivOfProd _ Q h).toLinearEquiv.trans
        (twistOneKernelSobolevEquiv hJ hi 0).symm :=
  (rfl)

/-- The Sobolev section of `twistOneKernelEquivOfProd hJ hi h v` is the kernel section of the
pair at `v`. -/
@[simp]
theorem twistOneKernelSobolev_twistOneKernelEquivOfProd (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible) (v : ℂ × ℂ) :
    twistOneKernelSobolev J 0 (twistOneKernelEquivOfProd hJ hi h v) =
      (twistOneDelBarSobolev J 0).kerSection Q v := by
  rw [twistOneKernelEquivOfProd_def, LinearEquiv.trans_apply,
    twistOneKernelSobolev_twistOneKernelSobolevEquiv_symm_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearMap.coe_kerEquivOfProd_apply]

/-- The inverse of `twistOneKernelEquivOfProd hJ hi h` is `Q` on Sobolev sections. -/
@[simp]
theorem twistOneKernelEquivOfProd_symm_apply (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible) (t : twistOneKernel J) :
    (twistOneKernelEquivOfProd hJ hi h).symm t = Q (twistOneKernelSobolev J 0 t) := by
  rw [twistOneKernelEquivOfProd_def, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    ContinuousLinearEquiv.coe_symm_toLinearEquiv, ContinuousLinearMap.kerEquivOfProd_symm_apply,
    coe_twistOneKernelSobolevEquiv_apply]

/-- `twistOneKernelEquivOfProd hJ hi h` sends `v` to the element on which `Q` is `v`. -/
theorem apply_twistOneKernelSobolev_twistOneKernelEquivOfProd (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible) (v : ℂ × ℂ) :
    Q (twistOneKernelSobolev J 0 (twistOneKernelEquivOfProd hJ hi h v)) = v := by
  rw [← twistOneKernelEquivOfProd_symm_apply hJ hi h, LinearEquiv.symm_apply_apply]

/-- If `Q` commutes with multiplication by `i` on the Sobolev sections of `twistOneKernel J`, then
`twistOneKernelEquivOfProd hJ hi h` is complex linear. -/
theorem twistOneKernelEquivOfProd_I_smul (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible)
    (hQ : ∀ t : twistOneKernel J, Q (twistOneSobolevSMulI 1 (twistOneKernelSobolev J 0 t)) =
      Complex.I • Q (twistOneKernelSobolev J 0 t)) (v : ℂ × ℂ) :
    twistOneKernelEquivOfProd hJ hi h (Complex.I • v) =
      Complex.I • twistOneKernelEquivOfProd hJ hi h v := by
  apply (twistOneKernelEquivOfProd hJ hi h).symm.injective
  rw [LinearEquiv.symm_apply_apply, twistOneKernelEquivOfProd_symm_apply,
    ← twistOneSobolevSMulI_twistOneKernelSobolev, hQ,
    apply_twistOneKernelSobolev_twistOneKernelEquivOfProd]

/-- **Transport of the kernel at `J₀` to the kernel at `J`.** Let a two-form `σ` tame both `J` and
the standard structure `i`, let `Q` from `W^{1,2}(𝒪(1))` to `ℂ × ℂ` commute with multiplication by
`i` on the Sobolev sections of `twistOneKernel J`, and let the pair of `D_J` and `Q` be invertible.
This complex linear map sends `s ∈ twistOneKernel J₀` to the element of `twistOneKernel J` on
which `Q` takes the value `(s 0, s ∞)`. -/
noncomputable def twistOneKernelTransfer (J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ))
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible)
    (hQ : ∀ t : twistOneKernel J, Q (twistOneSobolevSMulI 1 (twistOneKernelSobolev J 0 t)) =
      Complex.I • Q (twistOneKernelSobolev J 0 t)) :
    twistOneKernel J₀ →ₗ[ℂ] twistOneKernel J :=
  ((twistOneKernelEquivOfProd hJ hi h).toLinearMap.complexOfMapISmul
    (twistOneKernelEquivOfProd_I_smul hJ hi h hQ)).comp (twistOneKernelEval J₀)

@[simp]
theorem twistOneKernelTransfer_apply (J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ))
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible)
    (hQ : ∀ t : twistOneKernel J, Q (twistOneSobolevSMulI 1 (twistOneKernelSobolev J 0 t)) =
      Complex.I • Q (twistOneKernelSobolev J 0 t)) (s : twistOneKernel J₀) :
    twistOneKernelTransfer J₀ hJ hi h hQ s =
      twistOneKernelEquivOfProd hJ hi h (twistOneKernelEval J₀ s) := by
  rw [twistOneKernelTransfer, LinearMap.comp_apply, LinearMap.coe_complexOfMapISmul,
    LinearEquiv.coe_coe]

/-- When a two-form tames `J₀`, `J` and `i`, `twistOneKernelTransfer J₀ hJ hi h hQ` is bijective. -/
theorem twistOneKernelTransfer_bijective
    {J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ₀ : σ.Tames J₀)
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J 0).prod Q).IsInvertible)
    (hQ : ∀ t : twistOneKernel J, Q (twistOneSobolevSMulI 1 (twistOneKernelSobolev J 0 t)) =
      Complex.I • Q (twistOneKernelSobolev J 0 t)) :
    Function.Bijective (twistOneKernelTransfer J₀ hJ hi h hQ) := by
  have : ⇑(twistOneKernelTransfer J₀ hJ hi h hQ) =
      twistOneKernelEquivOfProd hJ hi h ∘ twistOneKernelEval J₀ :=
    funext (twistOneKernelTransfer_apply J₀ hJ hi h hQ)
  rw [this]
  exact (twistOneKernelEquivOfProd hJ hi h).bijective.comp (twistOneKernelEval_bijective hJ₀ hi)

/-- If `Q` is evaluation at `0` and `∞` on the elements of `twistOneKernel J₀`, then
`twistOneKernelTransfer J₀ hJ₀ hi h hQ` is the identity. -/
theorem twistOneKernelTransfer_self {J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ₀ : σ.Tames J₀) (hi : σ.Tames 𝒊)
    {Q : SobolevSection (twistCoreAtlas 1) volume 2 (0 + 1) →L[ℝ] ℂ × ℂ}
    (h : ((twistOneDelBarSobolev J₀ 0).prod Q).IsInvertible)
    (hQ : ∀ t : twistOneKernel J₀, Q (twistOneSobolevSMulI 1 (twistOneKernelSobolev J₀ 0 t)) =
      Complex.I • Q (twistOneKernelSobolev J₀ 0 t))
    (hQ₀ : ∀ s : twistOneKernel J₀, Q (twistOneKernelSobolev J₀ 0 s) = twistOneKernelEval J₀ s)
    (s : twistOneKernel J₀) :
    twistOneKernelTransfer J₀ hJ₀ hi h hQ s = s := by
  rw [twistOneKernelTransfer_apply, ← hQ₀, ← twistOneKernelEquivOfProd_symm_apply hJ₀ hi h,
    LinearEquiv.apply_symm_apply]

variable {ι : Type*}
  (e : ι → Trivialization (ℂ →L[ℝ] ℂ) (π (ℂ →L[ℝ] ℂ) (fun x : OnePoint ℂ ↦
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
  [∀ i, MemTrivializationAtlas (e i)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
  (hU : ∀ i, (U i : Set (OnePoint ℂ)) ⊆ (e i).baseSet)

/-- **The kernels of `D_J` near `J₀`.** Let a two-form `σ` on the sphere tame both `J₀` and the
standard structure `i`, and give the structures tamed by `σ` the subspace topology of
`SmoothAlmostComplexStructure.frameTopology e U hU`, for frames whose domains cover the sphere.
There are complex linear maps `T J : twistOneKernel J₀ → (OnePoint ℂ → ℂ)` such that:
* for `J` near `J₀`, `T J` is injective with range `twistOneKernel J`;
* `T J₀` is the inclusion;
* for every order `k` and every `s`, there is a family of `W^{k+1,2}` sections of `𝒪(1)`,
  continuous at `J₀`, whose continuous representatives are `T J s` for `J` near `J₀`.

`T J s` is read off the inverse of the operator `D_J` stabilized by a projection onto the kernel
at `J₀` (Tau Ceti's `ContinuousLinearMap.kerSection`). -/
theorem exists_twistOneKernelFamily (hcover : ∀ x, ∃ i, x ∈ U i)
    {J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ₀ : σ.Tames J₀)
    (hi : σ.Tames 𝒊) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    ∃ T : {J // σ.Tames J} → twistOneKernel J₀ →ₗ[ℂ] (OnePoint ℂ → ℂ),
      (∀ᶠ J in 𝓝 ⟨J₀, hJ₀⟩, Function.Injective (T J) ∧
        LinearMap.range (T J) = twistOneKernel J.val) ∧
      (∀ s, T ⟨J₀, hJ₀⟩ s = s) ∧
      ∀ (k : ℕ) (s : twistOneKernel J₀), ∃ w : {J // σ.Tames J} →
          SobolevSection (twistCoreAtlas 1) volume 2 (k + 1),
        ContinuousAt w ⟨J₀, hJ₀⟩ ∧
          ∀ᶠ J in 𝓝 ⟨J₀, hJ₀⟩, SobolevSection.toSection (w J) = T J s := by
  intro _
  obtain ⟨P, hP₀, hPI⟩ := exists_twistOneKernelProjection hJ₀ hi
  -- The projection at order `k`, through the inclusion of `W^{k+1,2}` in `W^{1,2}`.
  let Q (k : ℕ) := P.comp ((twistCoreAtlas 1).sectionChartData.toOrderOne volume 2 k)
  have hQ (k : ℕ) {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}
      (t : twistOneKernel J) :
      Q k (twistOneKernelSobolev J k t) = P (twistOneKernelSobolev J 0 t) := by
    rw [ContinuousLinearMap.comp_apply, toOrderOne_twistOneKernelSobolev]
  have hQI (J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) (t : twistOneKernel J) :
      Q 0 (twistOneSobolevSMulI 1 (twistOneKernelSobolev J 0 t)) =
        Complex.I • Q 0 (twistOneKernelSobolev J 0 t) := by
    rw [twistOneSobolevSMulI_twistOneKernelSobolev, hQ, hQ,
      ← twistOneSobolevSMulI_twistOneKernelSobolev, hPI]
  have hD (k : ℕ) : Continuous fun J : {J // σ.Tames J} ↦ twistOneDelBarSobolev J.val k :=
    continuous_twistOneDelBarSobolev_tames e U hU hcover σ k
  have hinv₀ (k : ℕ) : ((twistOneDelBarSobolev (⟨J₀, hJ₀⟩ : {J // σ.Tames J}).val k).prod
      (Q k)).IsInvertible :=
    isInvertible_twistOneDelBarSobolev_prod hJ₀ hi hP₀ k
  have hev (k : ℕ) : ∀ᶠ J in 𝓝 (⟨J₀, hJ₀⟩ : {J // σ.Tames J}),
      ((twistOneDelBarSobolev J.val k).prod (Q k)).IsInvertible := by
    obtain ⟨V, hV, hJV, hVinv⟩ :=
      ContinuousLinearMap.exists_isOpen_isInvertible_prod (hD k).continuousAt (hinv₀ k)
    exact Filter.mem_of_superset (hV.mem_nhds hJV) hVinv
  classical
  refine ⟨fun J ↦ if h : ((twistOneDelBarSobolev J.val 0).prod (Q 0)).IsInvertible then
    (twistOneKernel J.val).subtype ∘ₗ twistOneKernelTransfer J₀ J.property hi h (hQI J.val)
    else 0, ?_, fun s ↦ ?_, fun k s ↦ ?_⟩
  · filter_upwards [hev 0] with J h
    have hb := twistOneKernelTransfer_bijective hJ₀ J.property hi h (hQI J.val)
    simp only [h, ↓reduceDIte]
    rw [LinearMap.coe_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 hb.2), Submodule.range_subtype]
    exact ⟨(Submodule.injective_subtype _).comp hb.1, rfl⟩
  · have h := hinv₀ 0
    simp only [h, ↓reduceDIte]
    rw [LinearMap.comp_apply, Submodule.subtype_apply,
      twistOneKernelTransfer_self hJ₀ hi _ _ fun s ↦ (hQ 0 s).trans (hP₀ s)]
  · refine ⟨fun J ↦ (twistOneDelBarSobolev J.val k).kerSection (Q k) (twistOneKernelEval J₀ s),
      (((hD k).continuousAt.kerSection continuousAt_const (hinv₀ k)).clm_apply
        continuousAt_const), ?_⟩
    filter_upwards [hev 0, hev k] with J h₀ hk
    simp only [h₀, ↓reduceDIte]
    rw [LinearMap.comp_apply, Submodule.subtype_apply, twistOneKernelTransfer_apply,
      kerSection_twistOneDelBarSobolev_toOrderOne J.property hi hk
        ((hQ 0 _).symm.trans (apply_twistOneKernelSobolev_twistOneKernelEquivOfProd _ hi h₀ _)),
      toSection_twistOneKernelSobolev]

/-- **The kernels of `D_J` near `J₀`, continuous in the `C^∞` topology.** Let a two-form `σ` on
the sphere tame both `J₀` and the standard structure `i`, and give the structures tamed by `σ`
the subspace topology of `SmoothAlmostComplexStructure.frameTopology e U hU`, for frames whose
domains cover the sphere. There are complex linear maps
`T J : twistOneKernel J₀ → (OnePoint ℂ → ℂ)` such that:
* for `J` near `J₀`, `T J` is injective with range `twistOneKernel J`;
* `T J₀` is the inclusion;
* for every `s`, there is a family `S` of smooth sections of `𝒪(1)` with `S J = T J s` for `J`
  near `J₀`, continuous at `J₀` for `ContMDiffSection.frameTopology e' U' hU'`, for every frame
  system `(e', U')` of `𝒪(1)`. -/
theorem exists_continuousAt_twistOneKernelFamily (hcover : ∀ x, ∃ i, x ∈ U i)
    {J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ₀ : σ.Tames J₀)
    (hi : σ.Tames 𝒊) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    ∃ T : {J // σ.Tames J} → twistOneKernel J₀ →ₗ[ℂ] (OnePoint ℂ → ℂ),
      (∀ᶠ J in 𝓝 ⟨J₀, hJ₀⟩, Function.Injective (T J) ∧
        LinearMap.range (T J) = twistOneKernel J.val) ∧
      (∀ s, T ⟨J₀, hJ₀⟩ s = s) ∧
      ∀ s : twistOneKernel J₀, ∃ S : {J // σ.Tames J} →
          Cₛ^∞⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯,
        (∀ᶠ J in 𝓝 ⟨J₀, hJ₀⟩, ⇑(S J) = T J s) ∧
        ∀ {κ : Type*} (e' : κ → Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) 1).Fiber))
          [∀ i, MemTrivializationAtlas (e' i)] (U' : κ → TopologicalSpace.Opens (OnePoint ℂ))
          (hU' : ∀ i, (U' i : Set (OnePoint ℂ)) ⊆ (e' i).baseSet),
          letI := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := ∞) e' U' hU'
          ContinuousAt S ⟨J₀, hJ₀⟩ := by
  intro _
  obtain ⟨T, hT, hT₀, hw⟩ := exists_twistOneKernelFamily e U hU hcover hJ₀ hi
  refine ⟨T, hT, hT₀, fun s ↦ ?_⟩
  classical
  let S (J : {J // σ.Tames J}) : Cₛ^∞⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ :=
    if h : T J s ∈ twistOneKernel J.val then ⟨T J s, ((mem_twistOneKernel_iff J.val).1 h).1⟩
    else 0
  have hS : ∀ᶠ J in 𝓝 ⟨J₀, hJ₀⟩, ⇑(S J) = T J s := by
    filter_upwards [hT] with J hJ
    have h : T J s ∈ twistOneKernel J.val := hJ.2 ▸ LinearMap.mem_range_self _ s
    simp only [S, h, ↓reduceDIte]
    exact ContMDiffSection.coeFn_mk _ _
  refine ⟨S, hS, fun e' _ U' hU' ↦ ?_⟩
  let := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := ∞) e' U' hU'
  let A := twistCoreAtlas 1
  refine FiniteBundleAtlas.tendsto_frameTopology_of_tendstoLocallyUniformlyOn A
    fun i j _ ↦ ?_
  -- At order `j + 1`, convergence in `W^{j+2,2}` makes the derivatives of order `j` of the chart
  -- readings converge locally uniformly.
  have hk : finrank ℝ ℂ + j ≤ j + 1 + 1 := by rw [Complex.finrank_real_complex]; omega
  obtain ⟨w, hwc, hwS⟩ := hw (j + 1) s
  have hSw : ∀ᶠ J in 𝓝 ⟨J₀, hJ₀⟩, ⇑(S J) = SobolevSection.toSection (w J) := by
    filter_upwards [hS, hwS] with J h₁ h₂
    rw [h₁, h₂]
  rw [hSw.self_of_nhds]
  refine (SobolevSection.tendstoLocallyUniformlyOn_iteratedFDeriv_coord_toSection hk i
    hwc).congr_inseparable ?_
  filter_upwards [hSw] with J hJ y _
  exact .of_eq (by rw [hJ])

end Family

end SymplecticGeometry

end
