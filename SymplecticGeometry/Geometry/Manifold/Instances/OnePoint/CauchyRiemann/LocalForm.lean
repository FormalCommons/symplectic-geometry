/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.DbarFunction
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Sobolev
import SymplecticGeometry.Geometry.Manifold.Complex.Isothermal
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ZeroOnePart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Tames
import SymplecticGeometry.Topology.VectorBundle.Basic
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Basic
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Basic
import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Holomorphic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Topology.FiberBundle.Trivialization
public import TauCeti.Analysis.Complex.Wirtinger.Weak
import SymplecticGeometry.Analysis.Complex.Wirtinger.Similarity.Weak
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import SymplecticGeometry.Topology.Connected.Clopen
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.MeasureTheory.Function.Jacobian
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffRepresentative
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.LowerOrder
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey

/-!
# Local form of the kernel of `D_J` on `𝒪(1)`, and its zeros

This file reads the Cauchy–Riemann equation on `𝒪(1)` over the sphere `OnePoint ℂ` in charts:
first for Sobolev sections in the charts of `twistCoreAtlas 1`, then for smooth sections in an
isothermal chart, and last for Sobolev sections in an isothermal chart. From the smooth
equation it also derives unique continuation and the isolation of the zeros of a nonzero smooth
kernel element, and from the last reading the regularity of the kernel of `D_J` on Sobolev
sections of every order.

## The Sobolev equation in the charts of `twistCoreAtlas 1`

The first part reads the equation `D_J w = 0` in the charts of the atlas `twistCoreAtlas 1`, for
an almost complex structure `J` on the sphere and the Cauchy–Riemann operator
`D_J = twistOneDelBarSobolev J 0 : W^{1,2}(𝒪(1)) → W^{0,2}(Λ^{0,1} ⊗ 𝒪(1))` of
`SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Sobolev`.

In chart `i`, let `u` be the chart data of `w`, `Du` a weak derivative of `u` on the chart image,
`Γ` the zeroth-order term `chartZeroOrder` of the connection `twistOneConnection`, and
`K = J.inChart (twistCoreAtlas 1).center i` the reading of `J`. The chart data of `∇w` are the
one-forms `L y = Du y + Γ y (u y)` (`IsCovariantDerivativeOn.chartValueL_sobolevL_ae`). When a
two-form tames both `J` and the standard structure `i` of the sphere, `D_J w = 0` holds exactly
when, in every chart, `L y` is complex linear for `K y` at almost every point of the chart image:
`L y (K y v) = i L y v` (`SymplecticGeometry.twistOneDelBarSobolev_eq_zero_iff`).

The proof reads each factor of `D_J = π^{0,1}_i ∘ Φ_J ∘ ∇` in the chart. The chart data of
`Φ_J ∇w` are the chart reading of the field `zeroOnePartL J` applied to `L`
(`TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_self`). Tau Ceti's
`TauCeti.zeroOnePartSobolevL_eq_zero_iff` says that `D_J w = 0` exactly when these data are
complex linear almost everywhere in every chart. Taming gives `K 1 ≠ -i`
(`TauCeti.SmoothAlmostComplexStructure.inChart_apply_one_ne_neg_I_of_tames`), and then the
reading of `zeroOnePartL J` sends `L` to a complex-linear map exactly when `L ∘ K = i L`
(`TauCeti.FiniteBundleAtlas.coord_hom_zeroOnePartL_apply_I_smul_iff`).

## The smooth equation in an isothermal chart

Let `J` be a smooth almost complex structure on the sphere and `D_J` the real Cauchy–Riemann
operator `SymplecticGeometry.twistOneDelBar J` on `𝒪(1)`. The second part reads `D_J s = 0` in
a chart `ψ : OnePoint ℂ → ℂ` whose derivative carries `J` to multiplication by `i` (such charts
come from
`TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph`), with the section
written in the frame of the trivialization `(twistCore 1).localTriv y` of `𝒪(1)` at any point
`y` of the sphere. The result is a planar equation `∂v/∂w̄ = a v` with `a` smooth, which is the
form that Tau Ceti's
`TauCeti.exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul` takes.

The argument has two steps. In the frame of a chart, the local frame formula
`TauCeti.IsRealCauchyRiemannOperator.eq_frameCauchyRiemannOperator_add_sum` and the complex
linearity of `D_J` write `D_J s` as `∂bar_J` of the coordinate of `s` plus the coordinate times
`D_J` of the first frame section. Then, along an isothermal chart, `∂bar_J` evaluated on the
preimage of `1` is the conjugate Wirtinger derivative `∂/∂w̄` of the function read in the chart
(`TauCeti.SmoothAlmostComplexStructure.dbarFunction_apply_mfderiv_symm_eq_conjWirtingerDeriv`).

The similarity principle then writes the coordinate of a kernel element as `e^{-g} h` near `ψ x`,
with `g` smooth and `h` holomorphic. Restricting the trivialization to the source of `ψ` and
multiplying its fibre coordinate by `exp (-g ∘ ψ)` (Tau Ceti's gauge transform
`Bundle.Trivialization.transFiberwiseLinear`) gives a trivialization in which the section reads as
`h`. This scalar gauge, with the lemmas that give it and its inverse as multiplication by a
scalar and its continuity, adapts Tau Ceti's `TauCeti.expReGauge` and
`TauCeti.expReTrivialization`. Multiplication by a nonzero complex number is complex linear, so
this trivialization still reads the canonical orientation of the fibres
(`TauCeti.VectorBundleOrientation.complex`) as that of `ℂ`
(`TauCeti.VectorBundleOrientation.mapOrientation_complex_of_isLinear`). These are the local
hypotheses of
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`
at a zero of the section, apart from the orientation of the chart.

## Zeros of smooth kernel elements

From this equation the zeros of a smooth kernel element are understood. In the rescaled
trivialization above, its coordinate is complex analytic, so near each point the section either
vanishes identically or has no zero on a punctured neighbourhood, by Tau Ceti's
`Bundle.Trivialization.eventually_eq_zero_or_eventually_ne_zero_of_eventually_eq_mul` (with the
constant factor `1`). Since the sphere is connected, this dichotomy gives unique continuation
(`PreconnectedSpace.eq_zero_of_eventually_eq_zero`); since it is also compact, Tau Ceti's
`TauCeti.finite_setOf_eq_zero_of_forall_eventually` turns it into the finiteness of the zeros of
a nonzero kernel element.

## Sobolev kernel elements in an isothermal chart

The last part combines the two readings. Let `w` be a `W^{1,2}` section of `𝒪(1)` with
`D_J w = 0`, for `J` tamed together with `i`, let `u` be its chart data in chart `i` with chart map
`φ`, and let `ψ` be a chart that carries `J` to `i`. Read through the transition `T = φ ∘ ψ⁻¹`,
the function `v = u ∘ T` has the weak derivative `Du (T z) ∘ dT z`, by Tau Ceti's change of
variables `TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`. Since `dT z` carries `i` to the reading
of `J` (`TauCeti.SmoothAlmostComplexStructure.fderiv_extChartAt_comp_apply_eq_inChart`), the kernel
equation in the chart makes `Du (T z) ∘ dT z + Γ (u (T z)) ∘ dT z` complex linear, and since the
zeroth-order term `Γ` is complex linear (`chartZeroOrder_twistOneConnection_apply`),
the weak conjugate Wirtinger derivative of `v` is `a v` for a smooth `a`. The weak similarity
principle `TauCeti.HasWeakConjWirtingerDerivOn.exists_contDiffOn_differentiableOn_ae_eq_exp_neg_mul`
then writes `v` as `exp (-g) h`. Pulling this back along `T⁻¹` gives smooth representatives of the
chart data near every point.

## Regularity of the kernel

Let `w` be a `W^{k+1,2}` section of `𝒪(1)` with `D_J w = 0`. Whether `D_J w = 0` holds depends only
on the chart data of `w`, through a weak derivative of them, so forgetting the higher derivatives
of `w` (`TauCeti.SectionChartData.toOrderOne`) gives a `W^{1,2}` section in the kernel of `D_J` at
order zero. Its chart data have smooth representatives near every point, so `w` is represented by
a smooth section (`TauCeti.SobolevSection.exists_contMDiff_ae_eq_coord_of_locally`), which is the
continuous representative `TauCeti.SobolevSection.toSection w`. On a smooth section the chart
data of the Sobolev operator are the readings of the `(0,1)`-part for `i` of `D_J s`, and taming
makes that projection injective on the `(0,1)`-forms for `J`
(`TauCeti.SmoothAlmostComplexStructure.injOn_zeroOnePart_of_tames`). So the kernel of the Sobolev
operator is the space `twistOneKernel J` of smooth solutions.

## Main results

* `SymplecticGeometry.twistOneDelBarSobolev_eq_zero_iff`: for `J` tamed together with `i` by a
  two-form, a `W^{1,2}` section `w` of `𝒪(1)` satisfies `D_J w = 0` exactly when, in every chart
  of `twistCoreAtlas 1`, the chart data of `∇w` are complex linear for `J` almost everywhere.
* `SymplecticGeometry.twistOneDelBar_eq_symmL_comp_dbarFunction_add_smul`: `D_J` in the frame of
  the chart at `y`.
* `SymplecticGeometry.contDiffOn_twistOneDelBar_localFrame_apply_mfderiv_symm`: the zeroth-order
  coefficient read through `ψ` is smooth.
* `SymplecticGeometry.exists_conjWirtingerDeriv_apply_one_eq_mul_of_mem_twistOneKernel`: the
  coordinate of a smooth element of the kernel of `D_J`, read through `ψ`, satisfies
  `∂v/∂w̄ = a v` near `ψ x`, with `a` smooth.
* `SymplecticGeometry.exists_trivialization_analyticAt_of_mem_twistOneKernel`: at every point, a
  smooth element of the kernel of `D_J` is complex analytic in an isothermal chart and a real
  linear trivialization of `𝒪(1)` that reads the canonical orientation of the fibres as that of
  `ℂ`.
* `SymplecticGeometry.eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel`: near
  each point, a smooth kernel element vanishes identically or has no zero on a punctured
  neighbourhood.
* `SymplecticGeometry.eq_zero_of_eventually_eq_zero_of_mem_twistOneKernel`: unique
  continuation.
* `SymplecticGeometry.eventually_ne_zero_of_mem_twistOneKernel`: the zeros of a nonzero smooth
  kernel element are isolated.
* `SymplecticGeometry.exists_hasWeakConjWirtingerDerivOn_mul_of_twistOneDelBarSobolev_eq_zero`:
  the chart data of a Sobolev element of the kernel of `D_J`, read through an isothermal chart,
  satisfy the weak equation `∂v/∂w̄ = a v` with `a` smooth.
* `SymplecticGeometry.exists_ae_eq_exp_neg_mul_of_twistOneDelBarSobolev_eq_zero`: the chart data of
  a Sobolev element of the kernel of `D_J`, read through an isothermal chart, are almost everywhere
  `exp (-g) h` with `g` smooth and `h` holomorphic.
* `SymplecticGeometry.exists_contDiffOn_ae_eq_chartValueL_of_twistOneDelBarSobolev_eq_zero`: the
  chart data of such an element agree almost everywhere near each point with a smooth function.
* `SymplecticGeometry.twistOneDelBarSobolev_eq_zero_iff_of_chartValueL_ae_eq`: the kernel equation
  of `D_J` on Sobolev sections depends only on the chart data, at any order.
* `SymplecticGeometry.twistOneDelBarSobolev_ofContMDiffSection_eq_zero_iff`: on a `C^{k+1}` section
  `s`, the Sobolev equation `D_J s = 0` is the equation `twistOneDelBar J s = 0`.
* `SymplecticGeometry.exists_contMDiff_ae_eq_coord_of_twistOneDelBarSobolev_eq_zero` and
  `SymplecticGeometry.contMDiff_of_twistOneDelBarSobolev_eq_zero`: a Sobolev element of the kernel
  of `D_J`, at any order, is represented by a smooth section, its continuous representative.
* `SymplecticGeometry.ker_twistOneDelBarSobolev_eq`: the kernel of `D_J` on `W^{k+1,2}` sections is
  the image of `twistOneKernel J`.
* `SymplecticGeometry.twistOneKernelToContMDiffSection` and
  `SymplecticGeometry.finrank_ker_twistOneDelBarSobolev`: the elements of `twistOneKernel J`, as
  `C^{k+1}` sections, map injectively onto that kernel, which so has the same real dimension.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 and C.2.
-/

public section

open Bundle Filter MeasureTheory Set TauCeti TauCeti.Manifold
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff ENNReal Topology TauCeti.ComplexManifold
  VectorBundle.ComplexToReal

noncomputable section

namespace SymplecticGeometry

variable {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}

/-- **The kernel equation of `D_J` in the charts.** Let a two-form `σ` tame both `J` and the
standard structure `i` of the sphere, and let `w` be a `W^{1,2}` section of `𝒪(1)`. Then
`D_J w = 0` exactly when, for every chart `i` of `twistCoreAtlas 1` and every weak derivative
`Du` of the chart data `u` of `w` on the chart image, the one-form `L y = Du y + Γ y (u y)`, for
the zeroth-order term `Γ` of the connection in chart `i`, is complex linear for the reading
`K = J.inChart (twistCoreAtlas 1).center i` of `J` at almost every point `y` of the chart image:
`L y (K y v) = i L y v` for all `v`. -/
theorem twistOneDelBarSobolev_eq_zero_iff {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {w : SobolevSection (twistCoreAtlas 1) volume 2 1} :
    twistOneDelBarSobolev J 0 w = 0 ↔
      ∀ (i : Fin (twistCoreAtlas 1).n) {Du : ℂ → ℂ →L[ℝ] ℂ},
        HasWeakFDerivOn volume ((twistCoreAtlas 1).image i)
          ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w) Du →
        ∀ᵐ y ∂volume.restrict ((twistCoreAtlas 1).image i), ∀ v : ℂ,
          (Du y + (twistCoreAtlas 1).chartZeroOrder twistOneConnection i y
              ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w y))
              (J.inChart ((twistCoreAtlas 1).center i) y v) =
            Complex.I • (Du y + (twistCoreAtlas 1).chartZeroOrder twistOneConnection i y
              ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w y)) v := by
  -- Taming gives `K 1 ≠ -i` for the reading `K` of `J` on each chart image.
  have hK1 (i : Fin (twistCoreAtlas 1).n) {y : ℂ} (hy : y ∈ (twistCoreAtlas 1).image i) :
      J.inChart ((twistCoreAtlas 1).center i) y 1 ≠ -Complex.I :=
    SmoothAlmostComplexStructure.inChart_apply_one_ne_neg_I_of_tames hJ hi _ <| by
      simpa using ((twistCoreAtlas 1).image_subset_target_inter_preimage_baseSet i hy).1
  -- The chart data of `Φ_J ∇w` are the reading of `Φ_J` applied to those of `∇w`, which are
  -- `Du + Γ u` for any weak derivative `Du`.
  have hΦ (i : Fin (twistCoreAtlas 1).n) := by
    have := SobolevSection.chartValueL_contMDiffHomMulL_ae_self
      (A := (twistCoreAtlas 1).tangentHom) (J.contMDiff_zeroOnePartL le_rfl)
      (isCovariantDerivativeOn_twistOneConnection.sobolevL (twistCoreAtlas 1)
        (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 0 w) i
    rwa [FiniteBundleAtlas.image_tangentHom] at this
  have hcov (i : Fin (twistCoreAtlas 1).n) {Du : ℂ → ℂ →L[ℝ] ℂ}
      (hDu : HasWeakFDerivOn volume ((twistCoreAtlas 1).image i)
        ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w) Du) :=
    isCovariantDerivativeOn_twistOneConnection.chartValueL_sobolevL_ae (twistCoreAtlas 1)
      (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 0 w hDu
  rw [twistOneDelBarSobolev_apply]
  refine zeroOnePartSobolevL_eq_zero_iff.trans ⟨fun h i Du hDu ↦ ?_, fun h i ↦ ?_⟩
  · filter_upwards [(FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).1 (h i),
      hΦ i, hcov i hDu, ae_restrict_mem ((twistCoreAtlas 1).image i).isOpen.measurableSet]
      with y hy1 hy2 hy3 hy
    rw [hy2, hy3] at hy1
    exact (FiniteBundleAtlas.coord_hom_zeroOnePartL_apply_I_smul_iff _ J hy (hK1 i hy) _).1 hy1
  · have hDu := (twistCoreAtlas 1).sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL
      volume 2 0 i w
    refine (FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).2 ?_
    filter_upwards [h i hDu, hΦ i, hcov i hDu,
      ae_restrict_mem ((twistCoreAtlas 1).image i).isOpen.measurableSet] with y hy1 hy2 hy3 hy
    rw [hy2, hy3]
    exact (FiniteBundleAtlas.coord_hom_zeroOnePartL_apply_I_smul_iff _ J hy (hK1 i hy) _).2 hy1

/-- **`D_J` in the frame of a chart.** Let `e = (twistCore 1).localTriv y` be the trivialization
of `𝒪(1)` at `y`, `φ p = (e ⟨p, s p⟩).2` the coordinate of a section `s` in it, and `e₀` the frame
section reading as `1`. At a point `x` of the chart at `y` where `s` is differentiable,
`D_J s x = ∂bar_J φ x + φ x • D_J e₀ x`, the first term carried to the fibre by `e.symmL`. -/
theorem twistOneDelBar_eq_symmL_comp_dbarFunction_add_smul {y x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    twistOneDelBar J s x =
      (((twistCore 1).localTriv y).symmL ℝ x).comp
          (J.dbarFunction (fun p ↦ ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨p, s p⟩).2) x) +
        ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨x, s x⟩).2 •
          twistOneDelBar J (((twistCore (𝕜 := ℂ) 1).localTriv y).localFrame Complex.basisOneI 0)
            x := by
  have hb : x ∈ ((twistCore (𝕜 := ℂ) 1).localTriv y).baseSet := by simpa using hx
  have hframe := ((((twistCore (𝕜 := ℂ) 1).localTriv y).contMDiffOn_localFrame_baseSet
    (I := 𝓘(ℝ, ℂ)) 1 Complex.basisOneI 0).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (((twistCore (𝕜 := ℂ) 1).localTriv y).open_baseSet.mem_nhds hb)
  have hc (i : Fin 2) := ((twistCore (𝕜 := ℂ) 1).localTriv y).localFrameCoeff_eq_coeff
    (I := 𝓘(ℝ, ℂ)) (b := Complex.basisOneI) (s := (s : Π p, (twistCore (𝕜 := ℂ) 1).Fiber p))
    (i := i) hb
  rw [(isRealCauchyRiemannOperator_twistOneDelBar J).eq_frameCauchyRiemannOperator_add_sum
    Complex.basisOneI hb hs, OnePoint.frameCauchyRiemannOperator_twistCore_localTriv hx hs,
    Fin.sum_univ_two, OnePoint.twistCore_localTriv_localFrame_basisOneI_one,
    twistOneDelBar_const_smul J _ hframe,
    hc 0, hc 1]
  congr 1
  · simp only [OnePoint.twistCore_localTriv_apply]
  · simp only [Complex.coe_basisOneI_repr, OnePoint.twistCore_localTriv_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_rhs => rw [← Complex.re_add_im (twistTransition 1 x y x * s x)]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- **The zeroth-order term through a chart is smooth.** Let `e = (twistCore 1).localTriv y` and
let `e₀` be its frame section reading as `1`. For a smooth partial diffeomorphism `ψ` from the
sphere to `ℂ`, the coordinate in `e` of `D_J e₀` at `ψ.symm w`, evaluated on `dψ⁻¹ 1`, is a smooth
function of `w` on the points of the target of `ψ` that `ψ.symm` sends into the chart at `y`. -/
theorem contDiffOn_twistOneDelBar_localFrame_apply_mfderiv_symm (J) (y : OnePoint ℂ)
    (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ∞) :
    ContDiffOn ℝ ∞ (fun w ↦ ((twistCore (𝕜 := ℂ) 1).localTriv y
      ⟨ψ.symm w, twistOneDelBar J
        (((twistCore (𝕜 := ℂ) 1).localTriv y).localFrame Complex.basisOneI 0) (ψ.symm w)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm w (1 : ℂ))⟩).2)
      (ψ.target ∩ ψ.symm ⁻¹' (chartAt ℂ y).source) := by
  set e := (twistCore (𝕜 := ℂ) 1).localTriv y
  set U := ψ.target ∩ ψ.symm ⁻¹' (chartAt ℂ y).source
  have hsource : (chartAt ℂ y).source = e.baseSet := (OnePoint.twistCore_localTriv_baseSet 1 y).symm
  have hDa : ContMDiffCovariantDerivativeOn ℂ ∞ (twistOneDelBar J) e.baseSet :=
    (isRealCauchyRiemannOperator_twistOneDelBar J).contMDiffCovariantDerivativeOn_mono_of_isOpen
      (contMDiffCovariantDerivativeOn_twistOneDelBar J ⊤) e.open_baseSet (subset_univ _)
  have hω := hDa.contMDiff ((e.contMDiffOn_localFrame_baseSet (I := 𝓘(ℝ, ℂ)) _
    Complex.basisOneI 0))
  have hψs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ.symm U := ψ.symm.contMDiffOn.mono inter_subset_left
  have hΦ := hω.comp hψs fun w hw ↦ hsource ▸ hw.2
  have hU : IsOpen U :=
    ψ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm (chartAt ℂ y).open_source
  have hv := hψs.contMDiffOn_totalSpaceMk_mfderiv_apply (m := ∞) (by simp) hU 1
  have h := hΦ.clm_bundle_apply hv
  rw [← contMDiffOn_iff_contDiffOn]
  exact ((e.contMDiffOn_iff fun w hw ↦ e.mem_source.2 (hsource ▸ hw.2)).1 h).2

/-- **The similarity equation of a smooth kernel element.** Let `ψ` be a smooth partial
diffeomorphism from the sphere to `ℂ` whose derivative carries `J` to multiplication by `i` on
its source, let `x` lie in the source of `ψ` and in the chart at `y`, and let `s` be a smooth
section of `𝒪(1)` with `D_J s = 0`. Then the coordinate
`v w = ((twistCore 1).localTriv y ⟨ψ.symm w, s (ψ.symm w)⟩).2` of `s` read through `ψ` is
real differentiable on an open set `U ∋ ψ x` and satisfies `∂v/∂w̄ = a v` there, for a function
`a` smooth on `U`. -/
theorem exists_conjWirtingerDeriv_apply_one_eq_mul_of_mem_twistOneKernel
    {ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ∞}
    (hψ : ∀ p ∈ ψ.source,
      IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) ψ p)
    {x y : OnePoint ℂ} (hx : x ∈ ψ.source) (hxy : x ∈ (chartAt ℂ y).source)
    {s : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J) :
    ∃ U : Set ℂ, IsOpen U ∧ ψ x ∈ U ∧ ∃ a : ℂ → ℂ, ContDiffOn ℝ ∞ a U ∧
      DifferentiableOn ℝ
        (fun w ↦ ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨ψ.symm w, s (ψ.symm w)⟩).2) U ∧
      ∀ w ∈ U, conjWirtingerDeriv
          (fun w ↦ ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨ψ.symm w, s (ψ.symm w)⟩).2) w 1 =
        a w * ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨ψ.symm w, s (ψ.symm w)⟩).2 := by
  set e := (twistCore (𝕜 := ℂ) 1).localTriv y
  set U := ψ.target ∩ ψ.symm ⁻¹' (chartAt ℂ y).source
  have hsource : (chartAt ℂ y).source = e.baseSet := (OnePoint.twistCore_localTriv_baseSet 1 y).symm
  have hU : IsOpen U :=
    ψ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm (chartAt ℂ y).open_source
  have hxU : ψ x ∈ U := ⟨ψ.map_source hx, by simpa [ψ.left_inv hx] using hxy⟩
  have hsm := (mem_twistOneKernel_iff J).1 hs
  set φ : OnePoint ℂ → ℂ := fun p ↦ (e ⟨p, s p⟩).2
  have hφ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ φ (chartAt ℂ y).source :=
    ((e.contMDiffOn_iff fun p hp ↦ e.mem_source.2 (hsource ▸ hp)).1 hsm.1.contMDiffOn).2
  have hψs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ.symm U := ψ.symm.contMDiffOn.mono inter_subset_left
  have hv : ContDiffOn ℝ ∞ (φ ∘ ψ.symm) U :=
    contMDiffOn_iff_contDiffOn.1 (hφ.comp hψs fun w hw ↦ hw.2)
  refine ⟨U, hU, hxU, fun w ↦ -(e ⟨ψ.symm w, twistOneDelBar J
      (e.localFrame Complex.basisOneI 0) (ψ.symm w)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm w (1 : ℂ))⟩).2,
    (contDiffOn_twistOneDelBar_localFrame_apply_mfderiv_symm J y ψ).neg,
    hv.differentiableOn (by simp), fun w hw ↦ ?_⟩
  set p := ψ.symm w
  set u := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm w (1 : ℂ)
  have hpd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ p :=
    (hφ.contMDiffAt ((chartAt ℂ y).open_source.mem_nhds hw.2)).mdifferentiableAt (by simp)
  have h0 := congrArg (fun L ↦ L u) (congrFun hsm.2 p)
  beta_reduce at h0
  rw [twistOneDelBar_eq_symmL_comp_dbarFunction_add_smul hw.2
    (hsm.1.mdifferentiableAt (by simp))] at h0
  have hcoord (v : ℂ) : (e ⟨p, v⟩).2 = twistTransition 1 p y p * v :=
    OnePoint.twistCore_localTriv_apply 1 y (fun _ ↦ v) p
  have htt : twistTransition 1 p y p * twistTransition 1 y p p = 1 := by
    rw [OnePoint.twistTransition_mul_twistTransition 1 hw.2 (mem_chart_source ℂ p) hw.2,
      OnePoint.twistTransition_self]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, Pi.zero_apply, zero_apply] at h0
  rw [OnePoint.twistCore_localTriv_symmL_apply hw.2, hcoord] at h0
  have hB := SmoothAlmostComplexStructure.dbarFunction_apply_mfderiv_symm_eq_conjWirtingerDeriv
    J hψ hw.1 hpd 1
  simp only [φ, Function.comp_def] at hB
  set d : ℂ := J.dbarFunction (fun p ↦ (e ⟨p, s p⟩).2) p u
  set D : ℂ := twistOneDelBar J (e.localFrame Complex.basisOneI 0) p u
  -- The fibres of `𝒪(1)` are `ℂ`, and its scalar action is multiplication.
  have h0' : twistTransition 1 y p p * d + (twistTransition 1 p y p * s p) * D = 0 := h0
  have hD : (e ⟨p, D⟩).2 = twistTransition 1 p y p * D := hcoord D
  rw [← hB]
  beta_reduce
  rw [hD, hcoord (s p)]
  linear_combination (twistTransition 1 p y p) * h0' - d * htt

/-- **A rescaled frame in which a smooth kernel element is holomorphic.** For a smooth element `s`
of the kernel of `D_J` on `𝒪(1)` and a point `z` of the sphere, there are a real linear
trivialization `e` of `𝒪(1)` over a neighbourhood of `z` and a smooth partial diffeomorphism
`ψ : OnePoint ℂ → ℂ` with `z` in its source, whose derivative carries `J` to multiplication by `i`
at every point of its source, such that the coordinate `w ↦ (e ⟨ψ⁻¹ w, s (ψ⁻¹ w)⟩).2` of `s` is
complex analytic at `ψ z`, and
`e` reads the canonical orientation `TauCeti.VectorBundleOrientation.complex` of every fibre over
its base set as the canonical orientation of `ℂ`, both indexed by `Fin (1 + 1)`. -/
theorem exists_trivialization_analyticAt_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (z : OnePoint ℂ) :
    ∃ (e : Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) 1).Fiber)) (_ : e.IsLinear ℝ)
      (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ∞), z ∈ e.baseSet ∧ z ∈ ψ.source ∧
      (∀ p ∈ ψ.source,
        IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) ψ p) ∧
      AnalyticAt ℂ (fun w ↦ (e (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber)
        (ψ.toOpenPartialHomeomorph.symm w) (s (ψ.toOpenPartialHomeomorph.symm w)))).2)
        (ψ.toOpenPartialHomeomorph z) ∧
      ∀ x (hx : x ∈ e.baseSet), e.mapOrientation (Fin (1 + 1)) hx
          (VectorBundleOrientation.reindex (finCongr (by simp : 2 * Module.finrank ℂ ℂ = 1 + 1))
            (VectorBundleOrientation.complex ℂ (twistCore (𝕜 := ℂ) 1).Fiber) x) =
        Orientation.reindex ℝ ℂ (finCongr (by simp : 2 * Module.finrank ℂ ℂ = 1 + 1))
          (complexOrientation ℂ) := by
  obtain ⟨ψ, hzψ, hψ⟩ := J.exists_isothermal_partialDiffeomorph (by simp) z
  obtain ⟨U, hU, hzU, a, ha, hv, heq⟩ :=
    exists_conjWirtingerDeriv_apply_one_eq_mul_of_mem_twistOneKernel hψ hzψ
      (mem_chart_source ℂ z) hs
  obtain ⟨g, hg, hA⟩ :=
    exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul
      (k := ⊤) le_top hU ha hv heq hzU
  -- The rescaling factor `c = exp (-g ∘ ψ)`, continuous on the source of `ψ` and nowhere zero.
  set c : OnePoint ℂ → ℂ := fun x ↦ Complex.exp (-g (ψ x))
  have hc : ContinuousOn c ψ.source :=
    Complex.continuous_exp.comp_continuousOn
      ((hg.continuous.comp_continuousOn ψ.contMDiffOn.continuousOn).neg)
  set m : OnePoint ℂ → ℂ ≃L[ℂ] ℂ := fun x ↦
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (c x) (Complex.exp_ne_zero _))
  have hm (x : OnePoint ℂ) : (m x : ℂ →L[ℂ] ℂ) = c x • ContinuousLinearMap.id ℂ ℂ := by
    ext; simp [m, mul_comm]
  have hm' (x : OnePoint ℂ) :
      ((m x).symm : ℂ →L[ℂ] ℂ) = (c x)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
    ext; simp [m, mul_comm]
  have hmc : ContinuousOn (fun x ↦ (m x : ℂ →L[ℂ] ℂ)) ψ.source := by
    simp only [hm]; exact hc.smul continuousOn_const
  have hmc' : ContinuousOn (fun x ↦ ((m x).symm : ℂ →L[ℂ] ℂ)) ψ.source := by
    simp only [hm']
    exact (hc.inv₀ fun _ _ ↦ Complex.exp_ne_zero _).smul continuousOn_const
  set e₀ := (twistCore (𝕜 := ℂ) 1).localTriv z
  set e₁ := e₀.restrOpen ψ.source ψ.open_source
  set e := e₁.transFiberwiseLinear m (hmc.mono inter_subset_right) (hmc'.mono inter_subset_right)
  have : e.IsLinear ℝ := Trivialization.isLinear_restrictScalars ℝ ℂ e
  have hze : z ∈ e.baseSet := by
    rw [Trivialization.baseSet_transFiberwiseLinear, Trivialization.restrOpen_baseSet]
    exact ⟨by simp [e₀, OnePoint.twistCore_localTriv_baseSet], hzψ⟩
  refine ⟨e, this, ψ, hze, hzψ, hψ, ?_, fun x hx ↦ ?_⟩
  · -- Over the target of `ψ`, the coordinate of `s` in `e` is `exp (-g)` times the one in `e₀`.
    refine hA.congr ?_
    filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hzψ)] with w hw
    rw [PartialDiffeomorph.coe_toOpenPartialHomeomorph_symm,
      Trivialization.transFiberwiseLinear_apply]
    simp only [e₁, e₀, Trivialization.coe_restrOpen, m, c,
      ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0]
    -- The base point of `e₀ ⟨p, v⟩` is `p` by definition of `FiberBundleCore.localTriv`; the
    -- `change` exposes it, since `twistOneKernel` types sections as maps into `ℂ` while `e₀`
    -- sees them in the fibres of `twistCore 1`.
    change _ = _ * Complex.exp (-g (ψ (ψ.symm w)))
    have hr : ψ.toPartialEquiv (ψ.symm.toPartialEquiv w) = w := ψ.toPartialEquiv.right_inv hw
    rw [hr, mul_comm]
  · rw [VectorBundleOrientation.reindex_apply, Trivialization.mapOrientation_reindex,
      VectorBundleOrientation.mapOrientation_complex_of_isLinear e hx]

/-- **Zeros of a smooth kernel element are isolated or interior.** Let `s` be a smooth section
of `𝒪(1)` with `D_J s = 0`. At each point `z` of the sphere, either `s` vanishes on a
neighbourhood of `z`, or `s` has no zero on a punctured neighbourhood of `z`. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (z : OnePoint ℂ) :
    (∀ᶠ y in 𝓝 z, s y = 0) ∨ ∀ᶠ y in 𝓝[≠] z, s y ≠ 0 := by
  obtain ⟨e, _, ψ, hze, hzψ, -, hA, -⟩ :=
    exists_trivialization_analyticAt_of_mem_twistOneKernel hs z
  exact e.eventually_eq_zero_or_eventually_ne_zero_of_eventually_eq_mul ψ.toOpenPartialHomeomorph
    (s := s) hze hzψ continuousAt_const one_ne_zero hA (.of_forall fun _ ↦ (one_mul _).symm)

/-- **Unique continuation for `D_J` on `𝒪(1)`.** A smooth section `s` of `𝒪(1)` with
`D_J s = 0` that vanishes on a neighbourhood of one point of the sphere is zero. -/
theorem eq_zero_of_eventually_eq_zero_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) {z : OnePoint ℂ} (hz : ∀ᶠ y in 𝓝 z, s y = 0) : s = 0 :=
  PreconnectedSpace.eq_zero_of_eventually_eq_zero
    (eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel hs) hz

/-- **Zeros of a nonzero smooth kernel element are isolated.** If `s ≠ 0` is a smooth section
of `𝒪(1)` with `D_J s = 0`, then `s` has no zero on some punctured neighbourhood of any point. -/
theorem eventually_ne_zero_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (hs₀ : s ≠ 0) (z : OnePoint ℂ) :
    ∀ᶠ y in 𝓝[≠] z, s y ≠ 0 :=
  (eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel hs z).resolve_left
    fun h ↦ hs₀ (eq_zero_of_eventually_eq_zero_of_mem_twistOneKernel hs h)

/-- The coefficient of the weak equation in an isothermal chart is smooth: for a map `T` smooth on
an open set `Ω` with values in the image of chart `i`, and the zeroth-order term `Γ` of the
connection in that chart, `z ↦ -(Γ (T z) 1 (dT z 1) + i Γ (T z) 1 (dT z i)) / 2` is smooth on
`Ω`. -/
private theorem contDiffOn_chartZeroOrder_comp_fderiv (i : Fin (twistCoreAtlas 1).n)
    {T : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hT : ContDiffOn ℝ ∞ T Ω)
    (hmaps : MapsTo T Ω ((twistCoreAtlas 1).image i)) :
    ContDiffOn ℝ ∞ (fun z ↦ -(2 : ℂ)⁻¹ *
      ((twistCoreAtlas 1).chartZeroOrder twistOneConnection i (T z) 1 (fderiv ℝ T z 1) +
        Complex.I * (twistCoreAtlas 1).chartZeroOrder twistOneConnection i (T z) 1
          (fderiv ℝ T z Complex.I))) Ω := by
  have hGT := (contDiffOn_chartZeroOrder_twistOneConnection_apply_one (twistCoreAtlas 1) i).comp
    hT fun z hz ↦ (twistCoreAtlas 1).image_subset_target_inter_preimage_baseSet i (hmaps hz)
  have hM : ContDiffOn ℝ ∞ (fderiv ℝ T) Ω := hT.fderiv_of_isOpen hΩ (by simp)
  exact contDiffOn_const.mul ((hGT.clm_apply (hM.clm_apply contDiffOn_const)).add
    (contDiffOn_const.mul (hGT.clm_apply (hM.clm_apply contDiffOn_const))))

/-- **The weak Cauchy–Riemann equation of a Sobolev kernel element in an isothermal chart.** Let a
two-form `σ` tame both `J` and the standard structure `i` of the sphere, let `w` be a `W^{1,2}`
section of `𝒪(1)` with `D_J w = 0`, and let `ψ` be a smooth partial diffeomorphism from the sphere
to `ℂ` whose derivative carries `J` to multiplication by `i` on its source. For every chart `i` of
`twistCoreAtlas 1`, with chart map `φ` and chart data `u` of `w`, and every open set `Ω` inside
`ψ.target ∩ ψ.symm ⁻¹' dom i`, there is a function `a` smooth on `Ω` such that
`v z = u (φ (ψ.symm z))` has the weak conjugate Wirtinger derivative `a v` on `Ω`. -/
theorem exists_hasWeakConjWirtingerDerivOn_mul_of_twistOneDelBarSobolev_eq_zero
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {w : SobolevSection (twistCoreAtlas 1) volume 2 1} (hw : twistOneDelBarSobolev J 0 w = 0)
    {ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ∞}
    (hψ : ∀ p ∈ ψ.source,
      IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) ψ p)
    (i : Fin (twistCoreAtlas 1).n) {Ω : TopologicalSpace.Opens ℂ}
    (hΩ : (Ω : Set ℂ) ⊆ ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) :
    ∃ a : ℂ → ℂ, ContDiffOn ℝ ∞ a Ω ∧
      HasWeakConjWirtingerDerivOn volume Ω
        (fun z ↦ (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w
          ((twistCoreAtlas 1).chart i (ψ.symm z)))
        (fun z ↦ a z * (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w
          ((twistCoreAtlas 1).chart i (ψ.symm z))) := by
  -- The transition `T = φ ∘ ψ⁻¹` from the isothermal coordinate to the chart coordinate.
  set T : OpenPartialHomeomorph ℂ ℂ :=
    ψ.toOpenPartialHomeomorph.symm.trans ((twistCoreAtlas 1).chart i)
  have hTcoe : (T : ℂ → ℂ) = extChartAt 𝓘(ℝ, ℂ) ((twistCoreAtlas 1).center i) ∘ ψ.symm := by
    ext z; simp [T]
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hΩT : (Ω : Set ℂ) ⊆ T.source := fun z hz ↦ by
    simpa [T] using ⟨(hΩ hz).1, (twistCoreAtlas 1).dom_subset_chart_source i (hΩ hz).2⟩
  have hT : ContDiffOn ℝ ∞ T Ω :=
    (ψ.contDiffOn_symm_trans_chartAt ((twistCoreAtlas 1).center i)).mono hΩT
  have hdet (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) : (fderiv ℝ T z).det ≠ 0 :=
    ψ.det_fderiv_symm_trans_chartAt_ne_zero hn ((twistCoreAtlas 1).center i) (hΩT hz)
  have hinj : InjOn T Ω := T.injOn.mono hΩT
  have hmaps : MapsTo T Ω ((twistCoreAtlas 1).image i) := fun z hz ↦ by
    rw [hTcoe]
    exact (twistCoreAtlas 1).mem_image.2 ⟨ψ.symm z, (hΩ hz).2, by simp⟩
  -- The derivative of `T` carries `i` to the reading `K` of `J` in chart `i`.
  have hTK (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) (v : ℂ) :
      fderiv ℝ T z (Complex.I • v) =
        J.inChart ((twistCoreAtlas 1).center i) (T z) (fderiv ℝ T z v) := by
    rw [hTcoe]
    exact J.fderiv_extChartAt_comp_apply_eq_inChart ((twistCoreAtlas 1).center i)
      (ψ.toOpenPartialHomeomorph.continuousAt_symm (hΩ hz).1)
      (by simpa using (twistCoreAtlas 1).dom_subset_chart_source i (hΩ hz).2)
      -- `ψ⁻¹` is pseudoholomorphic from `i` to `J`.
      ((SmoothAlmostComplexStructure.ofComplexManifold_apply (E := ℂ) z v).symm ▸
        ((ψ.toOpenPartialHomeomorph_mdifferentiable hn).isPseudoholomorphicAt_symm (hΩ hz).1
          (hψ _ (ψ.map_target (hΩ hz).1))).mfderiv_apply_commute v :)
  -- The kernel equation in chart `i`, pulled back along `T`, and the weak derivative of `u ∘ T`.
  have hDu :=
    (twistCoreAtlas 1).sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL volume 2 0 i w
  have hk := MeasureTheory.ae_restrict_comp_of_differentiableOn (μ := volume) Ω.isOpen
    (hT.differentiableOn hn) hinj hdet hmaps
    ((twistOneDelBarSobolev_eq_zero_iff hJ hi).1 hw i hDu)
  have hv := (hDu.comp_contDiffOn_diffeo (U := Ω) (hT.of_le (by simp)) hdet
    hmaps).hasWeakConjWirtingerDerivOn
  -- Since `Γ c = c • Γ 1`, the kernel equation reads `∂̄(u ∘ T) = a (u ∘ T)`.
  refine ⟨_, contDiffOn_chartZeroOrder_comp_fderiv i Ω.isOpen hT hmaps, hv.congr_ae_deriv ?_⟩
  filter_upwards [hk, ae_restrict_mem Ω.isOpen.measurableSet] with z hz hzΩ
  have hΓ := chartZeroOrder_twistOneConnection_apply (twistCoreAtlas 1) (hmaps hzΩ)
    ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w (T z))
  have hI : fderiv ℝ T z Complex.I =
      J.inChart ((twistCoreAtlas 1).center i) (T z) (fderiv ℝ T z 1) := by
    simpa using hTK z hzΩ 1
  have h1 := hz (fderiv ℝ T z 1)
  rw [hΓ, ← hI] at h1
  simp only [add_apply, smul_apply, smul_eq_mul] at h1
  have hTz : (twistCoreAtlas 1).chart i (ψ.symm z) = T z := by simp [T]
  simp only [ContinuousLinearMap.comp_apply, smul_eq_mul, hTz]
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
    (2⁻¹ * Complex.I) * h1

/-- **The local form of a Sobolev kernel element of `D_J`.** Let a two-form `σ` tame both `J` and
the standard structure `i` of the sphere, let `w` be a `W^{1,2}` section of `𝒪(1)` with
`D_J w = 0`, and let `ψ` be a smooth partial diffeomorphism from the sphere to `ℂ` whose derivative
carries `J` to multiplication by `i` on its source. For every chart `i` of `twistCoreAtlas 1`, with
chart map `φ` and chart data `u` of `w`, there are a function `g` smooth and a function `h`
holomorphic on `Ω = ψ.target ∩ ψ.symm ⁻¹' dom i` such that `u (φ (ψ.symm z)) = exp (-g z) * h z`
for almost every `z ∈ Ω`. -/
theorem exists_ae_eq_exp_neg_mul_of_twistOneDelBarSobolev_eq_zero
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {w : SobolevSection (twistCoreAtlas 1) volume 2 1} (hw : twistOneDelBarSobolev J 0 w = 0)
    {ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ∞}
    (hψ : ∀ p ∈ ψ.source,
      IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) ψ p)
    (i : Fin (twistCoreAtlas 1).n) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) ∧
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) ∧
        (fun z ↦ (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w
            ((twistCoreAtlas 1).chart i (ψ.symm z))) =ᵐ[volume.restrict
              (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i)]
          fun z ↦ Complex.exp (-g z) * h z := by
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) := by
    simpa [ψ.toOpenPartialHomeomorph_target] using
      ψ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm ((twistCoreAtlas 1).isOpen_dom i)
  obtain ⟨a, ha, hv⟩ := exists_hasWeakConjWirtingerDerivOn_mul_of_twistOneDelBarSobolev_eq_zero
    hJ hi hw hψ i (Ω := ⟨_, hO⟩) subset_rfl
  obtain ⟨g, hg, -, h, hh, hae⟩ := hv.exists_contDiffOn_differentiableOn_ae_eq_exp_neg_mul ha
  exact ⟨g, hg, h, hh, hae⟩

/-- **Sobolev kernel elements of `D_J` are smooth in the charts.** Let a two-form `σ` tame both `J`
and the standard structure `i` of the sphere, and let `w` be a `W^{1,2}` section of `𝒪(1)` with
`D_J w = 0`. For every chart `i` of `twistCoreAtlas 1`, each point `y` of the chart image has an
open neighbourhood `U` in the chart image on which the chart data of `w` agree almost everywhere
with a function smooth on `U`. -/
theorem exists_contDiffOn_ae_eq_chartValueL_of_twistOneDelBarSobolev_eq_zero
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {w : SobolevSection (twistCoreAtlas 1) volume 2 1} (hw : twistOneDelBarSobolev J 0 w = 0)
    (i : Fin (twistCoreAtlas 1).n) {y : ℂ} (hy : y ∈ (twistCoreAtlas 1).image i) :
    ∃ U : Set ℂ, IsOpen U ∧ y ∈ U ∧ U ⊆ (twistCoreAtlas 1).image i ∧
      ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f U ∧
        (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w =ᵐ[volume.restrict U] f := by
  set φ := (twistCoreAtlas 1).chart i
  have hx := (twistCoreAtlas 1).symm_mem_dom hy
  obtain ⟨ψ, hxψ, hψ⟩ := J.exists_isothermal_partialDiffeomorph Complex.finrank_real_complex
    (φ.symm y)
  obtain ⟨g, hg, h, hh, hae⟩ :=
    exists_ae_eq_exp_neg_mul_of_twistOneDelBarSobolev_eq_zero hJ hi hw hψ i
  -- The transition `S = ψ ∘ φ⁻¹` back to the isothermal coordinate, on the open set `U ∋ y`.
  set S : OpenPartialHomeomorph ℂ ℂ := φ.symm.trans ψ.toOpenPartialHomeomorph
  set U := φ.target ∩ φ.symm ⁻¹' (ψ.source ∩ (twistCoreAtlas 1).dom i)
  have hU : IsOpen U :=
    φ.isOpen_inter_preimage_symm (ψ.open_source.inter ((twistCoreAtlas 1).isOpen_dom i))
  have hUS : U ⊆ S.source := fun z hz ↦ by simpa [S] using ⟨hz.1, hz.2.1⟩
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hS : ContDiffOn ℝ ∞ S U :=
    (ψ.contDiffOn_chartAt_symm_trans ((twistCoreAtlas 1).center i)).mono hUS
  have hmaps : MapsTo S U (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) := fun z hz ↦ by
    simpa [S, ψ.left_inv hz.2.1] using ⟨ψ.map_source hz.2.1, hz.2.2⟩
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) := by
    simpa [ψ.toOpenPartialHomeomorph_target] using
      ψ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm ((twistCoreAtlas 1).isOpen_dom i)
  have hF : ContDiffOn ℝ ∞ (fun z ↦ Complex.exp (-g z) * h z)
      (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) :=
    hg.neg.cexp.mul ((hh.contDiffOn hO).restrict_scalars ℝ)
  obtain ⟨p, hp, hpy⟩ := (twistCoreAtlas 1).mem_image.1 hy
  refine ⟨U, hU,
    ⟨hpy ▸ φ.map_source ((twistCoreAtlas 1).dom_subset_chart_source i hp),
      by simpa using ⟨hxψ, hx⟩⟩,
    fun z hz ↦ (twistCoreAtlas 1).mem_image.2 ⟨φ.symm z, hz.2.2, φ.right_inv hz.1⟩, _,
    hF.comp hS hmaps, ?_⟩
  -- Pull the local form back along `S`, which has invertible derivative on `U`.
  have hae' := MeasureTheory.ae_restrict_comp_of_differentiableOn (μ := volume) hU
    (hS.differentiableOn hn) (S.injOn.mono hUS)
    (fun z hz ↦ ψ.det_fderiv_chartAt_symm_trans_ne_zero hn ((twistCoreAtlas 1).center i) (hUS hz))
    hmaps hae
  filter_upwards [hae', ae_restrict_mem hU.measurableSet] with z hz hzU
  have hφz : φ (ψ.symm (S z)) = z := by
    simp [S, ψ.left_inv hzU.2.1, φ.right_inv hzU.1]
  rwa [hφz] at hz

/-! ### Regularity of the kernel on Sobolev sections -/

/-- **The kernel equation depends only on the chart data.** If a section `w` in `W^{k+1,2}` and
a section `w'` in `W^{k'+1,2}` of `𝒪(1)` have the same chart data almost everywhere in every chart
of `twistCoreAtlas 1`, then `D_J w = 0` at order `k` exactly when `D_J w' = 0` at order `k'`. -/
theorem twistOneDelBarSobolev_eq_zero_iff_of_chartValueL_ae_eq {k k' : ℕ}
    {w : SobolevSection (twistCoreAtlas 1) volume 2 (k + 1)}
    {w' : SobolevSection (twistCoreAtlas 1) volume 2 (k' + 1)}
    (h : ∀ i, (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 (k + 1) i w
      =ᵐ[volume.restrict ((twistCoreAtlas 1).image i)]
        (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 (k' + 1) i w') :
    twistOneDelBarSobolev J k w = 0 ↔ twistOneDelBarSobolev J k' w' = 0 := by
  -- In every chart, the chart data of `Φ_J ∇w` and of `Φ_J ∇w'` are both the reading of
  -- `Φ_J` applied to `Du + Γ u`, for the chart data `u` of `w` and a weak derivative `Du` of them.
  have hΦ {l : ℕ} (v : SobolevSection (twistCoreAtlas 1) volume 2 (l + 1))
      (i : Fin (twistCoreAtlas 1).n) := by
    have := SobolevSection.chartValueL_contMDiffHomMulL_ae_self
      (A := (twistCoreAtlas 1).tangentHom) (J.contMDiff_zeroOnePartL le_rfl)
      (isCovariantDerivativeOn_twistOneConnection.sobolevL (twistCoreAtlas 1)
        (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 l v) i
    rwa [FiniteBundleAtlas.image_tangentHom] at this
  rw [twistOneDelBarSobolev_apply, twistOneDelBarSobolev_apply]
  refine zeroOnePartSobolevL_eq_zero_iff.trans
    (Iff.trans (forall_congr' fun i ↦ ?_) zeroOnePartSobolevL_eq_zero_iff.symm)
  have hDu := (twistCoreAtlas 1).sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL
    volume 2 k i w
  have hcov := isCovariantDerivativeOn_twistOneConnection.chartValueL_sobolevL_ae
    (twistCoreAtlas 1) (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 k w hDu
  have hcov' := isCovariantDerivativeOn_twistOneConnection.chartValueL_sobolevL_ae
    (twistCoreAtlas 1) (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 k' w'
    (hDu.congr_ae (h i))
  have hA {P : ℂ → Prop} :=
    FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i (P := P)
  constructor <;> intro hi <;> refine hA.2 ?_ <;>
    filter_upwards [hA.1 hi, hΦ w i, hΦ w' i, hcov, hcov', h i] with y hy h1 h2 h3 h4 h5
  · rwa [h1, h3, h5, ← h4, ← h2] at hy
  · rwa [h2, h4, ← h5, ← h3, ← h1] at hy

/-- **The kernel equation on smooth sections.** Let a two-form `σ` tame both `J` and the standard
structure `i` of the sphere. A `C^{k+1}` section `s` of `𝒪(1)`, as a Sobolev section, lies in the
kernel of `twistOneDelBarSobolev J k` exactly when `twistOneDelBar J s = 0`. -/
theorem twistOneDelBarSobolev_ofContMDiffSection_eq_zero_iff
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {k : ℕ}
    (s : Cₛ^((k + 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯) :
    twistOneDelBarSobolev J k
        (SobolevSection.ofContMDiffSection (twistCoreAtlas 1) volume 2 (k + 1) s) = 0 ↔
      twistOneDelBar J s = 0 := by
  have hae := chartValueL_twistOneDelBarSobolev_ofContMDiffSection_ae_coord J k s
  constructor
  · intro h
    -- The `(0,1)`-part for `i` of `D_J s` is a continuous one-form with chart readings zero
    -- almost everywhere, hence zero.
    have hcont : Continuous fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] ℂ)
        (E := fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x) x
        (𝒊.zeroOnePart (twistOneDelBar J s x)) := by
      have := (𝒊.contMDiff_totalSpace_zeroOnePart (n := ((k : ℕ∞) : WithTop ℕ∞))
        (by exact_mod_cast le_top)).comp_contMDiffOn
        ((contMDiffCovariantDerivativeOn_twistOneDelBar J k).contMDiff
          (s.contMDiff.contMDiffOn (s := univ)))
      exact contMDiff_zero_iff.1 (contMDiffOn_univ.1 (this.of_le (by simp)))
    have h0 := (twistCoreAtlas 1).tangentHom.eq_of_continuous_of_coord_ae_eq (μ := volume) hcont
      (t := 0) (contMDiff_zeroSection ℝ (fun x : OnePoint ℂ ↦
        TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x) (IB := 𝓘(ℝ, ℂ))
        (n := 0)).continuous fun i ↦ ?_
    · funext x
      refine SmoothAlmostComplexStructure.injOn_zeroOnePart_of_tames hJ hi x ?_ ?_
        ((congrFun h0 x).trans
          (by rw [Pi.zero_apply, SmoothAlmostComplexStructure.zeroOnePart_zero]))
      · rw [twistOneDelBar_def]
        exact J.isZeroOneForm_zeroOnePart _
      · have := J.isZeroOneForm_zeroOnePart
          (0 : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x)
        rwa [SmoothAlmostComplexStructure.zeroOnePart_zero] at this
    · simp only [h, ZeroMemClass.coe_zero, map_zero] at hae
      have hI : ((twistCoreAtlas 1).tangentHom.image i : Set ℂ) = (twistCoreAtlas 1).image i :=
        congrArg SetLike.coe (FiniteBundleAtlas.image_tangentHom (twistCoreAtlas 1) i)
      rw [hI]
      filter_upwards [hae i,
        (FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).1
          (AEEqFun.coeFn_zero (β := ℂ →L[ℝ] ℂ)),
        ae_restrict_mem ((twistCoreAtlas 1).image i).isOpen.measurableSet] with y hy h0 hyU
      exact hy.symm.trans (h0.trans ((twistCoreAtlas 1).tangentHom.coord_zero i
        (by rw [← SetLike.mem_coe, hI]; exact hyU)).symm)
  · intro h
    refine Subtype.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).2 ?_)
    simp only [ZeroMemClass.coe_zero, map_zero]
    filter_upwards [hae i,
      (FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).1
        (AEEqFun.coeFn_zero (β := ℂ →L[ℝ] ℂ)),
      ae_restrict_mem ((twistCoreAtlas 1).image i).isOpen.measurableSet] with y hy h0 hyU
    rw [hy]
    refine Eq.trans ?_ h0.symm
    rw [Pi.zero_apply, h]
    simp only [Pi.zero_apply, SmoothAlmostComplexStructure.zeroOnePart_zero]
    exact (twistCoreAtlas 1).tangentHom.coord_zero i
      (by rwa [FiniteBundleAtlas.image_tangentHom (twistCoreAtlas 1) i])

/-- **Sobolev kernel elements have smooth representatives.** Let a two-form `σ` tame both `J` and
the standard structure `i` of the sphere, and let `w` be a `W^{k+1,2}` section of `𝒪(1)` with
`D_J w = 0`. Then there is a smooth section `t` of `𝒪(1)` whose chart readings agree almost
everywhere with the chart data of `w` on every chart image of `twistCoreAtlas 1`. -/
theorem exists_contMDiff_ae_eq_coord_of_twistOneDelBarSobolev_eq_zero
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {k : ℕ}
    {w : SobolevSection (twistCoreAtlas 1) volume 2 (k + 1)}
    (hw : twistOneDelBarSobolev J k w = 0) :
    ∃ t : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (fun x ↦ TotalSpace.mk' ℂ x (t x)) ∧
        ∀ i, (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 (k + 1) i w
          =ᵐ[volume.restrict ((twistCoreAtlas 1).image i)] (twistCoreAtlas 1).coord i t := by
  -- Forgetting the higher derivatives gives an element of order one, in the kernel at order zero.
  have hw0 : twistOneDelBarSobolev J 0
      ((twistCoreAtlas 1).sectionChartData.toOrderOne volume 2 k w) = 0 :=
    (twistOneDelBarSobolev_eq_zero_iff_of_chartValueL_ae_eq fun i ↦ by
      rw [SectionChartData.chartValueL_toOrderOne]).1 hw
  refine SobolevSection.exists_contMDiff_ae_eq_coord_of_locally fun i y hy ↦ ?_
  obtain ⟨U, hU, hyU, -, f, hf, hae⟩ :=
    exists_contDiffOn_ae_eq_chartValueL_of_twistOneDelBarSobolev_eq_zero hJ hi hw0 i hy
  exact ⟨U, hU.mem_nhds hyU, f, hf,
    by rwa [SectionChartData.chartValueL_toOrderOne _ volume 2 k w i] at hae⟩

/-- **Regularity of the kernel of `D_J`.** Let a two-form `σ` tame both `J` and the standard
structure `i` of the sphere. For every order `k`, the continuous representative
`SobolevSection.toSection w` of a `W^{k+1,2}` section `w` of `𝒪(1)` with `D_J w = 0` is a smooth
section. -/
theorem contMDiff_of_twistOneDelBarSobolev_eq_zero
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {k : ℕ}
    {w : SobolevSection (twistCoreAtlas 1) volume 2 (k + 1)}
    (hw : twistOneDelBarSobolev J k w = 0) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x
        (SobolevSection.toSection w x) := by
  obtain ⟨t, ht, htw⟩ := exists_contMDiff_ae_eq_coord_of_twistOneDelBarSobolev_eq_zero hJ hi hw
  rw [← SobolevSection.eq_toSection ht.continuous htw]
  exact ht

/-- **The kernel of `D_J` on Sobolev sections.** Let a two-form `σ` tame both `J` and the standard
structure `i` of the sphere. For every order `k`, the kernel of `twistOneDelBarSobolev J k` is the
image under `SobolevSection.ofContMDiffSection` of the `C^{k+1}` sections of `𝒪(1)` that lie in
`twistOneKernel J`, the smooth sections `s` with `D_J s = 0`. -/
theorem ker_twistOneDelBarSobolev_eq
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (k : ℕ) :
    SetLike.coe (twistOneDelBarSobolev J k).ker =
      SobolevSection.ofContMDiffSection (twistCoreAtlas 1) volume 2 (k + 1) ''
        {s | ⇑s ∈ twistOneKernel J} := by
  ext w
  simp only [SetLike.mem_coe, LinearMap.mem_ker, mem_image, mem_ofPred_eq]
  constructor
  · intro hw
    obtain ⟨t, ht, htw⟩ := exists_contMDiff_ae_eq_coord_of_twistOneDelBarSobolev_eq_zero hJ hi hw
    let s : Cₛ^((k + 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ :=
      ⟨t, ht.of_le (by exact_mod_cast le_top)⟩
    have hsw : SobolevSection.ofContMDiffSection (twistCoreAtlas 1) volume 2 (k + 1) s = w :=
      SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
        (SobolevSection.chartValueL_ofContMDiffSection_ae _ _ _ _ s i).trans (htw i).symm
    refine ⟨s, (mem_twistOneKernel_iff J).2 ⟨ht, ?_⟩, hsw⟩
    rw [← twistOneDelBarSobolev_ofContMDiffSection_eq_zero_iff hJ hi, hsw]
    exact hw
  · rintro ⟨s, hs, rfl⟩
    exact (twistOneDelBarSobolev_ofContMDiffSection_eq_zero_iff hJ hi s).2
      ((mem_twistOneKernel_iff J).1 hs).2

/-- The smooth zeros of `D_J` as `C^{k+1}` sections of `𝒪(1)`: the real linear map sending an
element of `twistOneKernel J` to itself, as a section of class `C^{k+1}`. -/
def twistOneKernelToContMDiffSection (J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ))
    (k : ℕ) :
    twistOneKernel J →ₗ[ℝ]
      Cₛ^((k + 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ where
  toFun s := ⟨s.val, ((mem_twistOneKernel_iff J).1 s.property).1.of_le (by exact_mod_cast le_top)⟩
  -- The operations on `twistOneKernel J` and on sections are both pointwise; the fibres of
  -- `𝒪(1)` are `ℂ` by definition, which `rfl` sees through.
  map_add' s t := by ext x; rw [ContMDiffSection.coe_add]; rfl
  map_smul' c s := by ext x; rw [ContMDiffSection.coe_smul]; rfl

/-- The section `twistOneKernelToContMDiffSection J k s` is `s`. -/
@[simp]
theorem coe_twistOneKernelToContMDiffSection (k : ℕ) (s : twistOneKernel J) :
    ⇑(twistOneKernelToContMDiffSection J k s) = s.val :=
  ContMDiffSection.coeFn_mk _ _

/-- **The kernel of `D_J` on Sobolev sections, as a space.** Let a two-form `σ` tame both `J` and
the standard structure `i` of the sphere. For every order `k`, the kernel of
`twistOneDelBarSobolev J k` has the same real dimension as `twistOneKernel J`. -/
theorem finrank_ker_twistOneDelBarSobolev
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (k : ℕ) :
    Module.finrank ℝ (twistOneDelBarSobolev J k).ker = Module.finrank ℝ (twistOneKernel J) := by
  set f := (SobolevSection.ofContMDiffSection (twistCoreAtlas 1) volume 2 (k + 1)).comp
    (twistOneKernelToContMDiffSection J k)
  have hrange : LinearMap.range f = (twistOneDelBarSobolev J k).ker := by
    refine SetLike.coe_injective ?_
    rw [ker_twistOneDelBarSobolev_eq hJ hi k, LinearMap.coe_range]
    ext w
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨twistOneKernelToContMDiffSection J k s, ?_, rfl⟩
      rw [mem_ofPred_eq, coe_twistOneKernelToContMDiffSection]
      exact s.property
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, congrArg _ (ContMDiffSection.ext fun x ↦ by
        rw [coe_twistOneKernelToContMDiffSection])⟩
  have hinj : Function.Injective f :=
    (SobolevSection.ofContMDiffSection_injective _ _ _ _).comp fun s t h ↦ Subtype.ext <| by
      rw [← coe_twistOneKernelToContMDiffSection k s, ← coe_twistOneKernelToContMDiffSection k t,
        h]
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]

end SymplecticGeometry

end
