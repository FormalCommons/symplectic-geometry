/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOneForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.TwistCore
import SymplecticGeometry.Analysis.Complex.Beltrami.Orientation
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Tames
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Cauchy–Riemann operators on `𝒪(1)` over the sphere

Let `L = 𝒪(1)` be Tau Ceti's line bundle `OnePoint.twistCore 1` on the Riemann sphere
`OnePoint ℂ`, viewed as a smooth complex line bundle over the underlying real surface. Its
sections are functions `OnePoint ℂ → ℂ`: the value at a finite point is the coordinate in the
affine frame, the value at `∞` the coordinate in the inverted frame. This file fixes a complex
linear connection `∇` on `L` and defines, for every almost complex structure `J` on the sphere,
the real Cauchy–Riemann operator `D_J s = (∇ s)^{0,1}` and the space `E_J` of its smooth zeros.

The connection is Tau Ceti's `CovariantDerivative.ofPartitionOfUnity`: it glues, along a smooth
partition of unity subordinate to the two chart domains, the flat connections
`TauCeti.Manifold.frameCovariantDerivative` of the frames of the trivializations of `L`. The
real bundle structure of `L` that this uses is in
`SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.TwistCore`. In the frame of a chart
the flat connection differentiates the coordinate of a section, so its `(0,1)`-part for the
standard complex structure `i` is `∂bar` of the coordinate. Since the transition functions of
`L` are holomorphic, these readings agree on the overlap of the charts, and so the `(0,1)`-part
of `∇` for `i` is `∂bar` of the coordinate in either frame.

## Main definitions and results

* `OnePoint.isCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv` and
  `OnePoint.contMDiffCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv`: the
  flat connection of the frame of the chart at `y` is a smooth covariant derivative over that
  chart, for `𝒪(k)`.
* `OnePoint.frameCovariantDerivative_twistCore_localTriv` and
  `OnePoint.frameCauchyRiemannOperator_twistCore_localTriv`: in the frame of the chart at `y`,
  the flat connection of `𝒪(k)` is the differential of the coordinate, and its `(0,1)`-part for
  `i` is `∂bar` of the coordinate; `OnePoint.symmL_comp_dbarFunction_twistCore_localTriv_eq`:
  the latter does not depend on the chart.
* `SymplecticGeometry.twistOneConnection`: the connection on `𝒪(1)`, with
  `isCovariantDerivativeOn_twistOneConnection`, the instance
  `contMDiffCovariantDerivative_twistOneConnection`,
  `contMDiffCovariantDerivativeOn_twistOneConnection` and its complex linearity
  `twistOneConnection_const_smul`.
* `SymplecticGeometry.twistOneConnection_zeroOnePart_eq`: in the frame of either chart, its
  `(0,1)`-part for `i` is `∂bar` of the coordinate.
* `SymplecticGeometry.twistOneDelBar J`: the operator `D_J`, with `twistOneDelBar_zero`,
  `twistOneDelBar_const_smul`, `isRealCauchyRiemannOperator_twistOneDelBar`,
  `isComplexLinearOperator_twistOneDelBar` and `contMDiffCovariantDerivativeOn_twistOneDelBar`.
* `SymplecticGeometry.twistOneKernel J`: the complex vector space of smooth sections `s` with
  `D_J s = 0`, with `mem_twistOneKernel_iff`.
* `SymplecticGeometry.norm_beltrami_lt_one_of_tames`: if a two-form tames `J` and `i`, then in
  every chart `chartAt ℂ y` of the sphere the Beltrami coefficient `ν` of `J` has `‖ν‖ < 1`,
  and so has the coefficient `μ = -ν` of `∂bar + μ ∂`. A form taming `i` and `J` makes `J`, read
  in the chart, induce the standard orientation of `ℂ`
  (`TauCeti.SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames`); the bound is then
  `TauCeti.Beltrami.norm_beltrami_lt_one_of_im_pos`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle Set TauCeti TauCeti.Manifold
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold VectorBundle.ComplexToReal

noncomputable section

/-- The standard complex structure of the Riemann sphere. -/
local notation "𝒊" => SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)

namespace OnePoint

variable {k : ℤ}

/-- The flat connection of the frame of the trivialization of `𝒪(k)` at `y` is a covariant
derivative over the chart at `y`. -/
theorem isCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv (k : ℤ)
    (y : OnePoint ℂ) :
    IsCovariantDerivativeOn ℂ
      (frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore k).localTriv y))
      (chartAt ℂ y).source := by
  rw [← twistCore_localTriv_baseSet k y]
  exact isCovariantDerivativeOn_frameCovariantDerivative Complex.basisOneI

/-- The flat connection of the frame of the trivialization of `𝒪(k)` at `y` sends `C^(n + 1)`
sections to `C^n` one-forms over the chart at `y`. -/
theorem contMDiffCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv (k : ℤ)
    (y : OnePoint ℂ) (n : ℕ∞) :
    ContMDiffCovariantDerivativeOn ℂ n
      (frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore k).localTriv y))
      (chartAt ℂ y).source := by
  rw [← twistCore_localTriv_baseSet k y]
  exact contMDiffCovariantDerivativeOn_frameCovariantDerivative (m := ω) (k := ω)
    Complex.basisOneI le_top le_top

/-- In the frame of the chart at `y`, the flat connection of `𝒪(k)` differentiates the coordinate
`p ↦ twistTransition k p y p * s p` of a section `s` differentiable at a point of the chart. -/
theorem frameCovariantDerivative_twistCore_localTriv {y x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x) :
    frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore k).localTriv y) s x =
      (((twistCore k).localTriv y).symmL ℝ x).comp
        (mvfderiv 𝓘(ℝ, ℂ) (fun p ↦ twistTransition k p y p * s p) x) := by
  have hg := ((twistCore (𝕜 := ℂ) k).localTriv y).mdifferentiableAt_section_iff 𝓘(ℝ, ℂ) s
    (by simpa using hx) |>.1 hs
  simp only [twistCore_localTriv_apply] at hg
  -- `mvfderiv` is `mfderiv` read in the model space `ℂ` through the identity `fromTangentSpace`.
  have hA : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun p ↦ twistTransition k p y p * s p) x
      (mvfderiv 𝓘(ℝ, ℂ) (fun p ↦ twistTransition k p y p * s p) x) := hg.hasMFDerivAt
  refine frameCovariantDerivative_eq_symmL_comp Complex.basisOneI hA (fun i ↦ ?_)
    (by simpa using hx)
  filter_upwards [((chartAt ℂ y).open_source.mem_nhds hx)] with z hz
  have h := ((twistCore (𝕜 := ℂ) k).localTriv y).localFrameCoeff_eq_coeff (I := 𝓘(ℝ, ℂ))
    (b := Complex.basisOneI) (s := (s : Π p, (twistCore (𝕜 := ℂ) k).Fiber p)) (i := i)
    (by simpa using hz)
  rw [Module.Basis.coord_apply]
  rwa [twistCore_localTriv_apply] at h

/-- In the frame of the chart at `y`, the flat Cauchy–Riemann operator of `𝒪(k)` for the standard
complex structure is `∂bar` of the coordinate `p ↦ twistTransition k p y p * s p` of a section
`s` differentiable at a point of the chart. -/
theorem frameCauchyRiemannOperator_twistCore_localTriv {y x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x) :
    frameCauchyRiemannOperator 𝒊 Complex.basisOneI ((twistCore k).localTriv y) s x =
      (((twistCore k).localTriv y).symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ twistTransition k p y p * s p) x) := by
  refine (frameCauchyRiemannOperator_apply Complex.basisOneI).trans ?_
  rw [frameCovariantDerivative_twistCore_localTriv hx hs]
  ext v
  simp only [SmoothAlmostComplexStructure.zeroOnePart_apply,
    SmoothAlmostComplexStructure.dbarFunction_apply, ContinuousLinearMap.comp_apply, map_add,
    map_smul]
  rw [twistCore_localTriv_symmL_smul]

/-- The reading of `∂bar` of a section of `𝒪(k)` through the frame of a chart does not depend on
the chart: the transition functions of `𝒪(k)` are holomorphic. -/
theorem symmL_comp_dbarFunction_twistCore_localTriv_eq {y y' x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) (hx' : x ∈ (chartAt ℂ y').source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x) :
    (((twistCore k).localTriv y).symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ twistTransition k p y p * s p) x) =
      (((twistCore k).localTriv y').symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ twistTransition k p y' p * s p) x) := by
  have hg := ((twistCore (𝕜 := ℂ) k).localTriv y).mdifferentiableAt_section_iff 𝓘(ℝ, ℂ) s
    (by simpa using hx) |>.1 hs
  simp only [twistCore_localTriv_apply] at hg
  have hU : (chartAt ℂ y).source ∩ (chartAt ℂ y').source ∈ 𝓝 x :=
    ((chartAt ℂ y).open_source.inter (chartAt ℂ y').open_source).mem_nhds ⟨hx, hx'⟩
  have ht : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (twistTransition k y y') x :=
    ((contMDiffOn_twistTransition k y y').contMDiffAt hU).mdifferentiableAt (by simp)
  have ht' := MDifferentiableAt.restrictScalars ℝ ht
  have hcoord : (fun p ↦ twistTransition k p y' p * s p) =ᶠ[𝓝 x]
      twistTransition k y y' • fun p ↦ twistTransition k p y p * s p := by
    filter_upwards [hU] with p hp
    rw [Pi.smul_apply', smul_eq_mul, ← mul_assoc,
      twistTransition_mul_twistTransition k (mem_chart_source ℂ p) hp.1 hp.2]
  have hdbar : 𝒊.dbarFunction (fun p ↦ twistTransition k p y' p * s p) x =
      twistTransition k y y' x • 𝒊.dbarFunction (fun p ↦ twistTransition k p y p * s p) x := by
    rw [SmoothAlmostComplexStructure.dbarFunction_eq_zeroOnePart, hcoord.mvfderiv_eq,
      ← SmoothAlmostComplexStructure.dbarFunction_eq_zeroOnePart,
      SmoothAlmostComplexStructure.dbarFunction_smul _ ht' hg,
      (SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_eq_zero_iff ht').2 ht]
    simp
  rw [hdbar]
  ext v
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply]
  rw [twistCore_localTriv_symmL_apply hx, twistCore_localTriv_symmL_apply hx', smul_eq_mul,
    ← mul_assoc, twistTransition_mul_twistTransition k hx hx' (mem_chart_source ℂ x)]

end OnePoint

namespace SymplecticGeometry

/-! ### The connection -/

/-- A smooth partition of unity on the sphere subordinate to the domains of its two charts. -/
def onePointChartPartition : SmoothPartitionOfUnity (OnePoint ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, ℂ) (OnePoint ℂ)).choose

/-- The partition of unity `onePointChartPartition` is subordinate to the chart domains. -/
theorem onePointChartPartition_isSubordinate :
    onePointChartPartition.IsSubordinate fun y : OnePoint ℂ ↦ (chartAt ℂ y).source :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, ℂ) (OnePoint ℂ)).choose_spec

/-- The partition function of the chart at `y` vanishes off the chart domain. -/
theorem onePointChartPartition_eq_zero_of_notMem {y x : OnePoint ℂ}
    (hx : x ∉ (chartAt ℂ y).source) : onePointChartPartition y x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (onePointChartPartition_isSubordinate y h)

/-- The connection on `𝒪(1)` glued from the flat connections of the affine and of the inverted
frame by a partition of unity subordinate to the two charts. -/
def twistOneConnection : CovariantDerivative 𝓘(ℝ, ℂ) ℂ (twistCore (𝕜 := ℂ) 1).Fiber :=
  CovariantDerivative.ofPartitionOfUnity onePointChartPartition.toPartitionOfUnity
    onePointChartPartition_isSubordinate.toPartitionOfUnity
    (OnePoint.isCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv 1)

theorem twistOneConnection_def :
    twistOneConnection = CovariantDerivative.ofPartitionOfUnity
      onePointChartPartition.toPartitionOfUnity
      onePointChartPartition_isSubordinate.toPartitionOfUnity
      (OnePoint.isCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv 1) :=
  (rfl)

/-- The connection on `𝒪(1)` is a covariant derivative. -/
theorem isCovariantDerivativeOn_twistOneConnection :
    IsCovariantDerivativeOn ℂ twistOneConnection univ :=
  twistOneConnection.isCovariantDerivativeOn

/-- The connection on `𝒪(1)` is `C^n` for every finite or infinite order `n ≤ ∞`: it sends
`C^(n + 1)` sections to `C^n` one-forms. -/
instance contMDiffCovariantDerivative_twistOneConnection {n : ℕ∞ω} [ENat.LEInfty n] :
    CovariantDerivative.ContMDiffCovariantDerivative twistOneConnection n := by
  lift n to ℕ∞ using ENat.LEInfty.ne_top n
  exact CovariantDerivative.contMDiffCovariantDerivative_ofPartitionOfUnity
    onePointChartPartition_isSubordinate (fun y ↦ (chartAt ℂ y).open_source)
    (OnePoint.isCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv 1)
    fun y ↦
      OnePoint.contMDiffCovariantDerivativeOn_frameCovariantDerivative_twistCore_localTriv 1 y n

/-- The connection on `𝒪(1)` is smooth: it sends `C^(n + 1)` sections to `C^n` one-forms. -/
theorem contMDiffCovariantDerivativeOn_twistOneConnection (n : ℕ∞) :
    ContMDiffCovariantDerivativeOn ℂ n twistOneConnection univ :=
  (inferInstance : CovariantDerivative.ContMDiffCovariantDerivative twistOneConnection n).contMDiff

/-- The connection on `𝒪(1)` is complex linear. -/
theorem twistOneConnection_const_smul (c : ℂ) {s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x}
    {x : OnePoint ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    twistOneConnection (c • s) x = c • twistOneConnection s x := by
  rw [twistOneConnection_def, CovariantDerivative.ofPartitionOfUnity_apply,
    CovariantDerivative.ofPartitionOfUnity_apply, smul_finsum]
  simp only [SmoothPartitionOfUnity.toPartitionOfUnity_toFun_apply]
  refine finsum_congr fun y ↦ ?_
  by_cases hy : x ∈ (chartAt ℂ y).source
  · have hcs := hs.const_smul_section c
    have h := OnePoint.frameCovariantDerivative_twistCore_localTriv hy hcs
    rw [smul_comm, h, OnePoint.frameCovariantDerivative_twistCore_localTriv hy hs]
    -- The sections of `𝒪(1)` are complex valued functions, and its scalar action on the fibres
    -- is multiplication in `ℂ`; `s'` is `s` as a complex valued function.
    let s' : OnePoint ℂ → ℂ := s
    change onePointChartPartition y x • (((twistCore 1).localTriv y).symmL ℝ x).comp
        (mvfderiv 𝓘(ℝ, ℂ) (fun p ↦ twistTransition 1 p y p * (c • s') p) x) = _
    have hfun : (fun p ↦ twistTransition 1 p y p * (c • s') p) =
        c • fun p ↦ twistTransition 1 p y p * s' p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, mvfderiv_const_smul_field]
    congr 1
    ext v
    exact OnePoint.twistCore_localTriv_symmL_smul y x c _
  · simp [onePointChartPartition_eq_zero_of_notMem hy]

/-- In the frame of the chart at `y`, the `(0,1)`-part of the connection on `𝒪(1)` for the
standard complex structure is `∂bar` of the coordinate of the section. -/
theorem twistOneConnection_zeroOnePart_eq {y x : OnePoint ℂ} (hx : x ∈ (chartAt ℂ y).source)
    {s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    𝒊.zeroOnePart (twistOneConnection s x) =
      (((twistCore 1).localTriv y).symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨p, s p⟩).2) x) := by
  -- `s'` is `s` as a complex valued function, in which the coordinates are products.
  let s' : OnePoint ℂ → ℂ := s
  have hcoord (z : OnePoint ℂ) :
      (fun p ↦ ((twistCore (𝕜 := ℂ) 1).localTriv z ⟨p, s p⟩).2) =
        fun p ↦ twistTransition 1 p z p * s' p :=
    funext fun p ↦ OnePoint.twistCore_localTriv_apply 1 z s' p
  have hfin : (Function.support fun z ↦ onePointChartPartition z x •
      frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore 1).localTriv z) s x).Finite :=
    (onePointChartPartition.locallyFinite.point_finite x).subset fun z hz ↦
      left_ne_zero_of_smul hz
  rw [hcoord, twistOneConnection_def, CovariantDerivative.ofPartitionOfUnity_apply]
  simp only [SmoothPartitionOfUnity.toPartitionOfUnity_toFun_apply]
  rw [← SmoothAlmostComplexStructure.zeroOnePartLinearMap_apply, map_finsum _ hfin]
  calc ∑ᶠ z, _ = ∑ᶠ z, onePointChartPartition z x • (((twistCore 1).localTriv y).symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ twistTransition 1 p y p * s' p) x) := by
        refine finsum_congr fun z ↦ ?_
        rw [SmoothAlmostComplexStructure.zeroOnePartLinearMap_apply,
          SmoothAlmostComplexStructure.zeroOnePart_smul]
        by_cases hz : x ∈ (chartAt ℂ z).source
        · rw [← frameCauchyRiemannOperator_apply,
            OnePoint.frameCauchyRiemannOperator_twistCore_localTriv (s := s') hz hs,
            OnePoint.symmL_comp_dbarFunction_twistCore_localTriv_eq hz hx hs]
        · simp [onePointChartPartition_eq_zero_of_notMem hz]
    _ = _ := by rw [← finsum_smul, onePointChartPartition.sum_eq_one (mem_univ x), one_smul]

/-! ### The operators `D_J` -/

variable (J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ))

/-- The real Cauchy–Riemann operator `D_J s = (∇ s)^{0,1}` on `𝒪(1)` for an almost complex
structure `J` on the sphere: the `(0,1)`-part for `J` of the connection `twistOneConnection`. -/
def twistOneDelBar (s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) (x : OnePoint ℂ) :
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x :=
  J.zeroOnePart (twistOneConnection s x)

theorem twistOneDelBar_def (s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) (x : OnePoint ℂ) :
    twistOneDelBar J s x = J.zeroOnePart (twistOneConnection s x) :=
  (rfl)

/-- `D_J` sends the zero section to zero. -/
@[simp]
theorem twistOneDelBar_zero : twistOneDelBar J 0 = 0 := by
  funext x
  rw [twistOneDelBar_def, twistOneConnection.zero, Pi.zero_apply,
    SmoothAlmostComplexStructure.zeroOnePart_zero]

/-- `D_J` commutes with complex scalars at a point where the section is differentiable. -/
theorem twistOneDelBar_const_smul (c : ℂ) {s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x}
    {x : OnePoint ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    twistOneDelBar J (c • s) x = c • twistOneDelBar J s x := by
  rw [twistOneDelBar_def, twistOneDelBar_def, twistOneConnection_const_smul c hs,
    SmoothAlmostComplexStructure.zeroOnePart_complex_smul]

/-- `D_J` is a real Cauchy–Riemann operator for `J`. -/
theorem isRealCauchyRiemannOperator_twistOneDelBar :
    IsRealCauchyRiemannOperator ℂ J (twistOneDelBar J) :=
  isCovariantDerivativeOn_twistOneConnection.isRealCauchyRiemannOperator_zeroOnePart J

/-- `D_J` is complex linear. -/
theorem isComplexLinearOperator_twistOneDelBar :
    IsComplexLinearOperator ℂ (twistOneDelBar J) :=
  isCovariantDerivativeOn_twistOneConnection.isComplexLinearOperator_zeroOnePart J
    fun _ _ hσ ↦ twistOneConnection_const_smul Complex.I hσ

/-- `D_J` is smooth: it sends `C^(n + 1)` sections to `C^n` one-forms. -/
theorem contMDiffCovariantDerivativeOn_twistOneDelBar (n : ℕ∞) :
    ContMDiffCovariantDerivativeOn ℂ n (twistOneDelBar J) univ where
  contMDiff hσ := (J.contMDiff_totalSpace_zeroOnePart (by exact_mod_cast le_top)).comp_contMDiffOn
    ((contMDiffCovariantDerivativeOn_twistOneConnection n).contMDiff hσ)

/-! ### The kernel -/

/-- The space `E_J` of smooth sections `s` of `𝒪(1)` with `D_J s = 0`. -/
def twistOneKernel : Submodule ℂ (OnePoint ℂ → ℂ) where
  carrier := {s | ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x)) ∧
    twistOneDelBar J s = 0}
  add_mem' {s t} hs ht := by
    refine ⟨hs.1.add_section ht.1, funext fun x ↦ ?_⟩
    exact ((isRealCauchyRiemannOperator_twistOneDelBar J).add
      (hs.1.mdifferentiableAt (by simp)) (ht.1.mdifferentiableAt (by simp))).trans
      (by rw [congrFun hs.2 x, congrFun ht.2 x, Pi.zero_apply, add_zero])
  zero_mem' := ⟨contMDiff_zeroSection ℝ _, twistOneDelBar_zero J⟩
  smul_mem' c s hs := by
    refine ⟨(contMDiff_const (c := c)).smul_totalSpace hs.1, funext fun x ↦ ?_⟩
    -- The scalar action on sections of `𝒪(1)` is that on functions `OnePoint ℂ → ℂ`.
    exact (twistOneDelBar_const_smul J c (s := s) (hs.1.mdifferentiableAt (by simp))).trans
      (by rw [congrFun hs.2 x, Pi.zero_apply, smul_zero])

/-- A section lies in `E_J` exactly when it is smooth and `D_J` sends it to zero. -/
theorem mem_twistOneKernel_iff {s : OnePoint ℂ → ℂ} :
    s ∈ twistOneKernel J ↔ ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x)) ∧
        twistOneDelBar J s = 0 :=
  Iff.rfl

/-! ### The Beltrami coefficient in the charts -/

/-- Let a two-form `σ` on the sphere tame both `J` and the standard structure `i`. Read `J` in
the chart `chartAt ℂ y` of the sphere, at a point `z` of the chart target, as the real-linear
structure `K = J.inChart y z` on `ℂ`. Then the Beltrami coefficient
`ν = (i - K 1) / (conj (K 1) - i)` of `K` has norm less than one, and so has the coefficient
`μ = -ν` of the operator `∂bar + μ ∂` of `K`. This holds in the chart at `∞`, the inversion
`z ↦ 1 / z`, as well as in the affine chart. -/
theorem norm_beltrami_lt_one_of_tames {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (y : OnePoint ℂ) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) y).target) :
    ‖(Complex.I - J.inChart y z 1) / (starRingEnd ℂ (J.inChart y z 1) - Complex.I)‖ < 1 :=
  Beltrami.norm_beltrami_lt_one_of_im_pos
    (SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames hJ hi y hz)

end SymplecticGeometry
