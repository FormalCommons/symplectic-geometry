/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.DbarFunction
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.Isothermal
import SymplecticGeometry.Topology.VectorBundle.RestrOpen
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Topology.FiberBundle.Trivialization
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The local equation of `D_J` on `𝒪(1)` in an isothermal chart

Let `J` be a smooth almost complex structure on the sphere and `D_J` the real Cauchy–Riemann
operator `SymplecticGeometry.twistOneDelBar J` on `𝒪(1)`. This file reads `D_J s = 0` in a chart
`ψ : OnePoint ℂ → ℂ` whose derivative carries `J` to multiplication by `i` (such charts come from
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
`h`. Multiplication by a nonzero complex number is complex linear, so this
trivialization still reads the canonical orientation of the fibres
(`TauCeti.VectorBundleOrientation.complex`) as that of `ℂ`
(`Bundle.Trivialization.mapOrientation_complexOrientation`). These are the local hypotheses of
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`
at a zero of the section, apart from the orientation of the chart.

## Main results

* `SymplecticGeometry.twistOneDelBar_eq_symmL_comp_dbarFunction_add_smul`: `D_J` in the frame of
  the chart at `y`.
* `SymplecticGeometry.contDiffOn_twistOneDelBar_localFrame_apply_mfderiv_symm`: the zeroth-order
  coefficient read through `ψ` is smooth.
* `SymplecticGeometry.exists_conjWirtingerDeriv_apply_one_eq_mul_of_mem_twistOneKernel`: the
  coordinate of a smooth element of the kernel of `D_J`, read through `ψ`, satisfies
  `∂v/∂w̄ = a v` near `ψ x`, with `a` smooth.
* `SymplecticGeometry.exists_trivialization_analyticAt_of_mem_twistOneKernel`: at every point, a
  smooth element of the kernel of `D_J` is complex analytic in a chart and a real linear
  trivialization of `𝒪(1)` that reads the canonical orientation of the fibres as that of `ℂ`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle Set TauCeti TauCeti.Manifold
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold VectorBundle.ComplexToReal

noncomputable section

namespace SymplecticGeometry

variable {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}

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

/-- **A rescaled frame in which a smooth kernel element is holomorphic.** For a smooth element `s`
of the kernel of `D_J` on `𝒪(1)` and a point `z` of the sphere, there are a real linear
trivialization `e` of `𝒪(1)` over a neighbourhood of `z` and a chart `φ : OnePoint ℂ → ℂ` at `z`
such that the coordinate `w ↦ (e ⟨φ⁻¹ w, s (φ⁻¹ w)⟩).2` of `s` is complex analytic at `φ z`, and
`e` reads the canonical orientation `TauCeti.VectorBundleOrientation.complex` of every fibre over
its base set as the canonical orientation of `ℂ`, both indexed by `Fin (1 + 1)`. -/
theorem exists_trivialization_analyticAt_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (z : OnePoint ℂ) :
    ∃ (e : Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) 1).Fiber)) (_ : e.IsLinear ℝ)
      (φ : OpenPartialHomeomorph (OnePoint ℂ) ℂ), z ∈ e.baseSet ∧ z ∈ φ.source ∧
      AnalyticAt ℂ (fun w ↦ (e (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) (φ.symm w)
        (s (φ.symm w)))).2) (φ z) ∧
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
  refine ⟨e, this, ψ.toOpenPartialHomeomorph, hze,
    ψ.toOpenPartialHomeomorph_source.symm ▸ hzψ, ?_, fun x hx ↦ ?_⟩
  · -- Over the target of `ψ`, the coordinate of `s` in `e` is `exp (-g)` times the one in `e₀`.
    refine hA.congr ?_
    filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hzψ)] with w hw
    rw [PartialDiffeomorph.coe_toOpenPartialHomeomorph_symm,
      Trivialization.transFiberwiseLinear_apply]
    simp only [e₁, e₀, Trivialization.coe_restrOpen, m, c,
      ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0]
    -- The base point of `e₀ ⟨p, v⟩` is `p` by definition of `FiberBundleCore.localTriv`.
    change _ = _ * Complex.exp (-g (ψ (ψ.symm w)))
    have hr : ψ.toPartialEquiv (ψ.symm.toPartialEquiv w) = w := ψ.toPartialEquiv.right_inv hw
    rw [hr, mul_comm]
  · have := VectorBundle.finiteDimensional ℂ ℂ (twistCore (𝕜 := ℂ) 1).Fiber x
    rw [VectorBundleOrientation.reindex_apply, Trivialization.mapOrientation_reindex,
      VectorBundleOrientation.complex_apply,
      Trivialization.mapOrientation_complexOrientation e hx _ rfl, finCongr_refl,
      Orientation.reindex_refl, Equiv.refl_apply]

end SymplecticGeometry
