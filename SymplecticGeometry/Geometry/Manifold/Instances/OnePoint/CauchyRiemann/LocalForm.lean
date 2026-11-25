/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.DbarFunction
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
import Mathlib.Topology.DiscreteSubset
import SymplecticGeometry.Geometry.Manifold.Complex.Isothermal
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The local equation of `D_J` on `𝒪(1)` in an isothermal chart, and its zeros

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

From this equation the zeros of a smooth kernel element are understood. Near each point,
Tau Ceti's `TauCeti.eventually_ne_zero_of_conjWirtingerDeriv_apply_one_eq_mul` shows that the
coordinate either vanishes identically or has an isolated zero, and a section vanishes exactly
where its coordinate does. Since the sphere is connected, the set of points near which `s`
vanishes is either empty or everything; since it is compact, a nonzero kernel element has
finitely many zeros. The connectedness argument follows the proof of
`TauCeti.not_eventually_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul`.

## Main results

* `SymplecticGeometry.twistOneDelBar_eq_symmL_comp_dbarFunction_add_smul`: `D_J` in the frame of
  the chart at `y`.
* `SymplecticGeometry.contDiffOn_twistOneDelBar_localFrame_apply_mfderiv_symm`: the zeroth-order
  coefficient read through `ψ` is smooth.
* `SymplecticGeometry.exists_conjWirtingerDeriv_apply_one_eq_mul_of_mem_twistOneKernel`: the
  coordinate of a smooth element of the kernel of `D_J`, read through `ψ`, satisfies
  `∂v/∂w̄ = a v` near `ψ x`, with `a` smooth.
* `SymplecticGeometry.eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel`: near
  each point, a smooth kernel element vanishes identically or has no zero on a punctured
  neighbourhood.
* `SymplecticGeometry.eq_zero_of_eventually_eq_zero_of_mem_twistOneKernel`: unique
  continuation.
* `SymplecticGeometry.eventually_ne_zero_of_mem_twistOneKernel` and
  `SymplecticGeometry.finite_setOf_eq_zero_of_mem_twistOneKernel`: the zeros of a nonzero smooth
  kernel element are isolated, and finitely many.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle Filter Set TauCeti TauCeti.Manifold
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
/-- **Zeros of a smooth kernel element are isolated or interior.** Let `s` be a smooth section
of `𝒪(1)` with `D_J s = 0`. At each point `z` of the sphere, either `s` vanishes on a
neighbourhood of `z`, or `s` has no zero on a punctured neighbourhood of `z`. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (z : OnePoint ℂ) :
    (∀ᶠ y in 𝓝 z, s y = 0) ∨ ∀ᶠ y in 𝓝[≠] z, s y ≠ 0 := by
  obtain ⟨ψ, hzψ, hψ⟩ := J.exists_isothermal_partialDiffeomorph Complex.finrank_real_complex z
  obtain ⟨U, hU, hzU, a, ha, hv, heq⟩ :=
    exists_conjWirtingerDeriv_apply_one_eq_mul_of_mem_twistOneKernel hψ hzψ
      (mem_chart_source ℂ z) hs
  set e := (twistCore (𝕜 := ℂ) 1).localTriv z
  -- On the chart at `z`, the coordinate of a vector of `𝒪(1)` vanishes only if the vector does.
  have hcoord (p : OnePoint ℂ) (hp : p ∈ (chartAt ℂ z).source) (v : ℂ) :
      (e ⟨p, v⟩).2 = 0 ↔ v = 0 := by
    have htt : twistTransition 1 p z p * twistTransition 1 z p p = 1 := by
      rw [OnePoint.twistTransition_mul_twistTransition 1 hp (mem_chart_source ℂ p) hp,
        OnePoint.twistTransition_self]
    rw [OnePoint.twistCore_localTriv_apply 1 z (fun _ ↦ v) p]
    simp [left_ne_zero_of_mul_eq_one htt]
  set φ := ψ.toOpenPartialHomeomorph
  have hφ : ⇑φ = ψ := PartialDiffeomorph.toFun'_toOpenPartialHomeomorph ψ
  have hW : ∀ᶠ p in 𝓝 z, p ∈ (chartAt ℂ z).source ∧ ψ.symm (ψ p) = p :=
    ((chartAt ℂ z).open_source.eventually_mem (mem_chart_source ℂ z)).and
      (hφ ▸ φ.eventually_left_inverse hzψ)
  have hc : ContinuousAt ψ z := hφ ▸ φ.continuousAt hzψ
  by_cases h : ∀ᶠ w in 𝓝 (ψ z), (e ⟨ψ.symm w, s (ψ.symm w)⟩).2 = 0
  · refine .inl ?_
    filter_upwards [hW, hc.eventually h] with p ⟨hp, hpp⟩ hp0
    rwa [hpp, hcoord p hp] at hp0
  · refine .inr ?_
    have ht : Tendsto ψ (𝓝[≠] z) (𝓝[≠] (ψ z)) :=
      tendsto_nhdsWithin_iff.2 ⟨hc.tendsto.mono_left nhdsWithin_le_nhds,
        hφ ▸ φ.eventually_ne_nhdsWithin hzψ⟩
    filter_upwards [ht.eventually (eventually_ne_zero_of_conjWirtingerDeriv_apply_one_eq_mul
      (k := 1) le_rfl hU (ha.of_le (by simp)) hv heq hzU h), nhdsWithin_le_nhds hW]
      with p hp0 ⟨hp, hpp⟩
    rwa [hpp, Ne, hcoord p hp] at hp0

/-- **Unique continuation for `D_J` on `𝒪(1)`.** A smooth section `s` of `𝒪(1)` with
`D_J s = 0` that vanishes on a neighbourhood of one point of the sphere is zero. -/
theorem eq_zero_of_eventually_eq_zero_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) {z : OnePoint ℂ} (hz : ∀ᶠ y in 𝓝 z, s y = 0) : s = 0 := by
  set S := {x | ∀ᶠ y in 𝓝 x, s y = 0}
  have hS : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx ↦ ?_),
      isOpen_setOfPred_eventually_nhds⟩
    have hx' := (eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel hs x).resolve_left
      hx
    filter_upwards [eventually_nhdsWithin_iff.1 hx'] with y hy hyS
    obtain rfl | hyx := eq_or_ne y x
    · exact hx hyS
    · exact hy hyx hyS.self_of_nhds
  have hSu := (isClopen_iff.1 hS).resolve_left (Set.nonempty_of_mem (x := z) hz).ne_empty
  exact funext fun x ↦ (hSu ▸ mem_univ x : x ∈ S).self_of_nhds

/-- **Zeros of a nonzero smooth kernel element are isolated.** If `s ≠ 0` is a smooth section
of `𝒪(1)` with `D_J s = 0`, then `s` has no zero on some punctured neighbourhood of any point. -/
theorem eventually_ne_zero_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (hs₀ : s ≠ 0) (z : OnePoint ℂ) :
    ∀ᶠ y in 𝓝[≠] z, s y ≠ 0 :=
  (eventually_eq_zero_or_eventually_ne_zero_of_mem_twistOneKernel hs z).resolve_left
    fun h ↦ hs₀ (eq_zero_of_eventually_eq_zero_of_mem_twistOneKernel hs h)

/-- **A nonzero smooth kernel element has finitely many zeros.** If `s ≠ 0` is a smooth section
of `𝒪(1)` with `D_J s = 0`, then the zero set of `s` on the sphere is finite. -/
theorem finite_setOf_eq_zero_of_mem_twistOneKernel {s : OnePoint ℂ → ℂ}
    (hs : s ∈ twistOneKernel J) (hs₀ : s ≠ 0) : {y | s y = 0}.Finite := by
  have hc : {y | s y ≠ 0} ∈ codiscrete (OnePoint ℂ) :=
    mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun z _ ↦
      mem_of_superset (eventually_ne_zero_of_mem_twistOneKernel hs hs₀ z) subset_union_left
  simpa [compl_ofPred] using cofinite_le_codiscrete hc

end SymplecticGeometry
