/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOneForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Cauchy–Riemann operators on `𝒪(1)` over the sphere

Let `L = 𝒪(1)` be Tau Ceti's line bundle `OnePoint.twistCore 1` on the Riemann sphere
`OnePoint ℂ`, viewed as a smooth complex line bundle over the underlying real surface. Its
sections are functions `OnePoint ℂ → ℂ`: the value at a finite point is the coordinate in the
affine frame, the value at `∞` the coordinate in the inverted frame. This file fixes a complex
linear connection `∇` on `L` and defines, for every almost complex structure `J` on the sphere,
the real Cauchy–Riemann operator `D_J s = (∇ s)^{0,1}` and the space `E_J` of its smooth zeros.

The connection is glued, by a smooth partition of unity subordinate to the two chart domains,
from the flat connections `TauCeti.Manifold.frameCovariantDerivative` of the frames of the
trivializations of `L` (the gluing is Tau Ceti's
`PartitionOfUnity.IsSubordinate.isCovariantDerivativeOn_finsum_smul`). In the frame of a chart
the flat connection differentiates the coordinate of a section, so its `(0,1)`-part for the
standard complex structure `i` is `∂bar` of the coordinate. Since the transition functions of
`L` are holomorphic, these readings agree on the overlap of the charts, and so the `(0,1)`-part
of `∇` for `i` is `∂bar` of the coordinate in either frame.

## Main definitions and results

* `OnePoint.frameCovariantDerivative_twistCore_localTriv` and
  `OnePoint.frameCauchyRiemannOperator_twistCore_localTriv`: in the frame of the chart at `y`,
  the flat connection of `𝒪(k)` is the differential of the coordinate, and its `(0,1)`-part for
  `i` is `∂bar` of the coordinate; `OnePoint.symmL_comp_dbarFunction_twistCore_localTriv_eq`:
  the latter does not depend on the chart.
* `SymplecticGeometry.twistOneConnection`: the connection on `𝒪(1)`, with
  `isCovariantDerivativeOn_twistOneConnection`,
  `contMDiffCovariantDerivativeOn_twistOneConnection` and its complex linearity
  `twistOneConnection_const_smul`.
* `SymplecticGeometry.twistOneConnection_zeroOnePart_eq`: in the frame of either chart, its
  `(0,1)`-part for `i` is `∂bar` of the coordinate.
* `SymplecticGeometry.twistOneDelBar J`: the operator `D_J`, with
  `isRealCauchyRiemannOperator_twistOneDelBar`, `isComplexLinearOperator_twistOneDelBar` and
  `contMDiffCovariantDerivativeOn_twistOneDelBar`.
* `SymplecticGeometry.twistOneKernel J`: the complex vector space of smooth sections `s` with
  `D_J s = 0`, with `mem_twistOneKernel_iff`.

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

/-- The fibres of `𝒪(k)` on the Riemann sphere carry the topology of `ℂ`, for which multiplication
by real scalars is continuous. -/
instance (k : ℤ) (x : OnePoint ℂ) : ContinuousSMul ℝ ((twistCore (𝕜 := ℂ) k).Fiber x) :=
  inferInstanceAs (ContinuousSMul ℝ ℂ)

/-- `𝒪(k)` on the Riemann sphere is a `C^n` real vector bundle over the underlying real
surface, for every `n`. -/
instance (k : ℤ) {n : ℕ∞ω} : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℝ, ℂ) :=
  have : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℂ, ℂ) :=
    ContMDiffVectorBundle.of_le le_top
  ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this

/-- The local trivializations of `𝒪(k)` belong to its trivialization atlas. -/
instance (k : ℤ) (y : OnePoint ℂ) :
    MemTrivializationAtlas ((twistCore (𝕜 := ℂ) k).localTriv y) :=
  ⟨⟨y, rfl⟩⟩

/-- Over the chart at `y`, the frame of the trivialization of `𝒪(k)` at `y` is multiplication by
the transition function from the chart at `y` to the chart at the point. -/
theorem twistCore_localTriv_symmL_apply {y x : OnePoint ℂ} (hx : x ∈ (chartAt ℂ y).source)
    (v : ℂ) :
    ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x v = twistTransition k y x x * v := by
  have hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet := by simpa using hx
  rw [Trivialization.symmL_apply _ hb]
  have h := (twistCore (𝕜 := ℂ) k).localTriv_symm_apply y hb v
  rwa [twistCore_indexAt, twistCore_coordChange_apply] at h

/-- The real frame of a trivialization of `𝒪(k)` commutes with complex scalars. -/
theorem twistCore_localTriv_symmL_smul {y x : OnePoint ℂ} (hx : x ∈ (chartAt ℂ y).source)
    (c w : ℂ) :
    ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x (c • w) =
      c • ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x w := by
  have hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet := by simpa using hx
  rw [Trivialization.symmL_apply _ hb, Trivialization.symmL_apply _ hb,
    ← Trivialization.symmL_apply (R := ℂ) _ hb, ← Trivialization.symmL_apply (R := ℂ) _ hb,
    map_smul]

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
  rw [twistCore_localTriv_symmL_smul hx]

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
def twistOneConnection (s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) (x : OnePoint ℂ) :
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x :=
  ∑ᶠ y, onePointChartPartition y x •
    frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore 1).localTriv y) s x

theorem twistOneConnection_def (s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) (x : OnePoint ℂ) :
    twistOneConnection s x = ∑ᶠ y, onePointChartPartition y x •
      frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore 1).localTriv y) s x :=
  (rfl)

/-- The connection on `𝒪(1)` is a covariant derivative. -/
theorem isCovariantDerivativeOn_twistOneConnection :
    IsCovariantDerivativeOn ℂ twistOneConnection univ :=
  onePointChartPartition_isSubordinate.toPartitionOfUnity.isCovariantDerivativeOn_finsum_smul
    fun y ↦ by
      rw [← OnePoint.twistCore_localTriv_baseSet 1 y]
      exact isCovariantDerivativeOn_frameCovariantDerivative Complex.basisOneI

/-- The connection on `𝒪(1)` is smooth: it sends `C^(n + 1)` sections to `C^n` one-forms. -/
theorem contMDiffCovariantDerivativeOn_twistOneConnection (n : ℕ∞) :
    ContMDiffCovariantDerivativeOn ℂ n twistOneConnection univ :=
  onePointChartPartition_isSubordinate.contMDiffCovariantDerivativeOn_finsum_smul
    (fun y ↦ (chartAt ℂ y).open_source) fun y ↦ by
      rw [← OnePoint.twistCore_localTriv_baseSet 1 y]
      exact contMDiffCovariantDerivativeOn_frameCovariantDerivative (m := ω) (k := ω)
        Complex.basisOneI le_top le_top

/-- The connection on `𝒪(1)` is complex linear. -/
theorem twistOneConnection_const_smul (c : ℂ) {s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x}
    {x : OnePoint ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    twistOneConnection (c • s) x = c • twistOneConnection s x := by
  rw [twistOneConnection_def, twistOneConnection_def, smul_finsum]
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
    exact OnePoint.twistCore_localTriv_symmL_smul hy c _
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
  rw [hcoord, twistOneConnection_def, ← SmoothAlmostComplexStructure.zeroOnePartLinearMap_apply,
    map_finsum _ hfin]
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
  zero_mem' := by
    have h0 : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
        (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x
          ((0 : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) x)) :=
      contMDiff_zeroSection ℝ _
    refine ⟨h0, funext fun x ↦ ?_⟩
    have h := (isRealCauchyRiemannOperator_twistOneDelBar J).add (x := x)
      (h0.mdifferentiableAt (by simp)) (h0.mdifferentiableAt (by simp))
    rw [add_zero] at h
    exact left_eq_add.mp h
  smul_mem' c s hs := by
    refine ⟨(contMDiff_const (c := c)).smul_totalSpace hs.1, funext fun x ↦ ?_⟩
    have h := (twistOneConnection_const_smul c (s := s) (x := x)
      (hs.1.mdifferentiableAt (by simp)))
    have h2 := congrArg J.zeroOnePart h
    rw [SmoothAlmostComplexStructure.zeroOnePart_complex_smul] at h2
    refine h2.trans ?_
    have h3 : J.zeroOnePart (twistOneConnection s x) = 0 := congrFun hs.2 x
    exact (congrArg (c • ·) h3).trans (smul_zero c)


/-- A section lies in `E_J` exactly when it is smooth and `D_J` sends it to zero. -/
theorem mem_twistOneKernel_iff {s : OnePoint ℂ → ℂ} :
    s ∈ twistOneKernel J ↔ ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x)) ∧
        twistOneDelBar J s = 0 :=
  Iff.rfl

end SymplecticGeometry
