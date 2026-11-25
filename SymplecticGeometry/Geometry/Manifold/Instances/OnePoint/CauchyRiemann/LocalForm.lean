/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.DbarFunction
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Sobolev
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
public import TauCeti.Analysis.Complex.Wirtinger.Weak
import SymplecticGeometry.Analysis.Complex.Wirtinger.Similarity.Weak
import SymplecticGeometry.Geometry.Manifold.Complex.Isothermal
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ZeroOnePart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Tames
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Local form of the kernel of `D_J` on `𝒪(1)`

This file reads the Cauchy–Riemann equation on `𝒪(1)` over the sphere `OnePoint ℂ` in charts:
first for Sobolev sections in the charts of `twistCoreAtlas 1`, then for smooth sections in an
isothermal chart, and last for Sobolev sections in an isothermal chart.

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
(`TauCeti.SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames`), and then the
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

## Sobolev kernel elements in an isothermal chart

The third part combines the two readings. Let `w` be a `W^{1,2}` section of `𝒪(1)` with
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
* `SymplecticGeometry.exists_hasWeakConjWirtingerDerivOn_mul_of_twistOneDelBarSobolev_eq_zero`:
  the chart data of a Sobolev element of the kernel of `D_J`, read through an isothermal chart,
  satisfy the weak equation `∂v/∂w̄ = a v` with `a` smooth.
* `SymplecticGeometry.exists_ae_eq_exp_neg_mul_of_twistOneDelBarSobolev_eq_zero`: the chart data of
  a Sobolev element of the kernel of `D_J`, read through an isothermal chart, are almost everywhere
  `exp (-g) h` with `g` smooth and `h` holomorphic.
* `SymplecticGeometry.exists_contDiffOn_ae_eq_chartValueL_of_twistOneDelBarSobolev_eq_zero`: the
  chart data of such an element agree almost everywhere near each point with a smooth function.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 and C.2.
-/

public section

open Bundle MeasureTheory Set TauCeti TauCeti.Manifold
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff ENNReal Topology TauCeti.ComplexManifold
  VectorBundle.ComplexToReal

noncomputable section

namespace SymplecticGeometry

/-- The standard complex structure of the Riemann sphere. -/
local notation "𝒊" => SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)

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
      J.inChart ((twistCoreAtlas 1).center i) y 1 ≠ -Complex.I := fun h ↦ by
    have hyt : y ∈ (extChartAt 𝓘(ℝ, ℂ) ((twistCoreAtlas 1).center i)).target := by
      simpa using ((twistCoreAtlas 1).chart_image_closure_dom_subset i
        ((twistCoreAtlas 1).image_subset_chart_image_closure_dom i hy)).1
    have := SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames hJ hi _ hyt
    rw [h] at this
    norm_num at this
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
  have hU : IsOpen U := ψ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage ψ.open_target
    (chartAt ℂ y).open_source
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
    (hψ : ∀ p ∈ ψ.source, ∀ v : TangentSpace 𝓘(ℝ, ℂ) p,
      mvfderiv 𝓘(ℝ, ℂ) ψ p (J p v) = Complex.I * mvfderiv 𝓘(ℝ, ℂ) ψ p v)
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
  have hU : IsOpen U := ψ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage ψ.open_target
    (chartAt ℂ y).open_source
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
    hT fun z hz ↦ ((twistCoreAtlas 1).closure_image_subset_chart_image_closure_dom i).trans
      ((twistCoreAtlas 1).chart_image_closure_dom_subset i) (subset_closure (hmaps hz))
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
    (hψ : ∀ p ∈ ψ.source, ∀ v : TangentSpace 𝓘(ℝ, ℂ) p,
      mvfderiv 𝓘(ℝ, ℂ) ψ p (J p v) = Complex.I * mvfderiv 𝓘(ℝ, ℂ) ψ p v)
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
  have hTs := (ψ.contDiffOn_symm_trans_chartAt hn ((twistCoreAtlas 1).center i)).1
  have hT : ContDiffOn ℝ ∞ T Ω := hTs.1.mono hΩT
  have hdet (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) : (fderiv ℝ T z).det ≠ 0 := hTs.2 z (hΩT hz)
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
      (ψ.symm.contMDiffOn.continuousOn.continuousAt (ψ.open_target.mem_nhds (hΩ hz).1))
      (by simpa using (twistCoreAtlas 1).dom_subset_chart_source i (hΩ hz).2)
      (J.mfderiv_symm_apply_I_smul hψ (hΩ hz).1 v)
  -- The kernel equation in chart `i`, pulled back along `T`, and the weak derivative of `u ∘ T`.
  have hDu :=
    (twistCoreAtlas 1).sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL volume 2 0 i w
  have hk := MeasureTheory.ae_restrict_comp_of_differentiableOn (μ := volume) Ω.isOpen
    (hT.differentiableOn hn) hinj hdet hmaps
    ((twistOneDelBarSobolev_eq_zero_iff hJ hi).1 hw i hDu)
  have hv := (hDu.comp_contDiffOn_diffeo (U := Ω) (hT.of_le (by simp)) hinj hdet
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
    (hψ : ∀ p ∈ ψ.source, ∀ v : TangentSpace 𝓘(ℝ, ℂ) p,
      mvfderiv 𝓘(ℝ, ℂ) ψ p (J p v) = Complex.I * mvfderiv 𝓘(ℝ, ℂ) ψ p v)
    (i : Fin (twistCoreAtlas 1).n) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) ∧
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) ∧
        (fun z ↦ (twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w
            ((twistCoreAtlas 1).chart i (ψ.symm z))) =ᵐ[volume.restrict
              (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i)]
          fun z ↦ Complex.exp (-g z) * h z := by
  obtain ⟨a, ha, hv⟩ := exists_hasWeakConjWirtingerDerivOn_mul_of_twistOneDelBarSobolev_eq_zero
    hJ hi hw hψ i (Ω := ⟨_, ψ.isOpen_inter_preimage_symm ((twistCoreAtlas 1).isOpen_dom i)⟩)
    subset_rfl
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
  have hSs := (ψ.contDiffOn_symm_trans_chartAt hn ((twistCoreAtlas 1).center i)).2
  have hS : ContDiffOn ℝ ∞ S U := hSs.1.mono hUS
  have hmaps : MapsTo S U (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) := fun z hz ↦ by
    simpa [S, ψ.left_inv hz.2.1] using ⟨ψ.map_source hz.2.1, hz.2.2⟩
  have hF : ContDiffOn ℝ ∞ (fun z ↦ Complex.exp (-g z) * h z)
      (ψ.target ∩ ψ.symm ⁻¹' (twistCoreAtlas 1).dom i) :=
    hg.neg.cexp.mul ((hh.contDiffOn
      (ψ.isOpen_inter_preimage_symm ((twistCoreAtlas 1).isOpen_dom i))).restrict_scalars ℝ)
  obtain ⟨p, hp, hpy⟩ := (twistCoreAtlas 1).mem_image.1 hy
  refine ⟨U, hU,
    ⟨hpy ▸ φ.map_source ((twistCoreAtlas 1).dom_subset_chart_source i hp),
      by simpa using ⟨hxψ, hx⟩⟩,
    fun z hz ↦ (twistCoreAtlas 1).mem_image.2 ⟨φ.symm z, hz.2.2, φ.right_inv hz.1⟩, _,
    hF.comp hS hmaps, ?_⟩
  -- Pull the local form back along `S`, which has invertible derivative on `U`.
  have hae' := MeasureTheory.ae_restrict_comp_of_differentiableOn (μ := volume) hU
    (hS.differentiableOn hn) (S.injOn.mono hUS)
    (fun z hz ↦ hSs.2 z (hUS hz)) hmaps hae
  filter_upwards [hae', ae_restrict_mem hU.measurableSet] with z hz hzU
  have hφz : φ (ψ.symm (S z)) = z := by
    simp [S, ψ.left_inv hzU.2.1, φ.right_inv hzU.1]
  rwa [hφz] at hz

end SymplecticGeometry

end
