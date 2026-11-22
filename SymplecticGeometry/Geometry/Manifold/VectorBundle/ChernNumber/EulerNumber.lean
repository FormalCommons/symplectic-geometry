/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmoothZero
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree

/-!
# The first Chern number as a count of zeros

Over a compact oriented surface, the first Chern number of a complex line bundle `L` is the number
of zeros of a section of `L`, counted with signs.

* `chernNumber_eq_sum_sectionIndex`, the topological form: for a continuous section with finitely
  many zeros of a complex line bundle over a compact homologically oriented surface, not
  necessarily connected, `chernNumber` is the sum over the zeros of Tau Ceti's local index
  `TauCeti.VectorBundleOrientation.sectionIndex`, for the orientation of `L` as a complex line.
  For a line bundle the first Chern class is the Euler class of the bundle
  (`firstChernClass_eq_complexEulerClass`), and Tau Ceti evaluates the Euler class on the
  fundamental class as the sum of the local indices
  (`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`).
* `chernNumber_eq_sum_sign_of_transverse`, the smooth form: let `M` be a closed `C¹` surface with
  an orientation `o`, `V` a real `C¹` vector bundle of rank two over `M` with a continuous complex
  structure `J`, so that `J.Fiber` is a complex line bundle, and `s` a `C¹` section of `V`
  transverse to the zero section: its linearization `TauCeti.sectionLinearization` is onto at
  every zero. Then `s` has finitely many zeros (`TauCeti.finite_sectionZero_of_contMDiff`), and
  the first Chern number of `J.Fiber` is the sum over the zeros of `1` where the linearization
  carries the orientation of the tangent plane to the complex orientation of the fibre and `-1`
  where it does not.

At a zero `z`, the local index is computed by Tau Ceti's
`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt` as the sign of the
Jacobian of the section read in a chart of `M` with values in `ℂ` and in a trivialization of
`J.Fiber`. The chart is the preferred chart at `z` followed by a linear identification of the
model with `ℂ` that matches the orientations, so that it selects the local orientation of `M` at
`z`, by
`TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`,
and the chart translated so that `z` goes to the origin carries it to the local orientation of
`ℂ`, by `OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart` for the
identity of `ℂ`. The
trivialization of `J.Fiber` is that of `V` followed by a family of linear maps that is only
continuous; since the section vanishes at `z`, the Jacobian is still the linearization of `s`
followed by the value of that family at `z` (`TauCeti.mvfderiv_eq_comp_of_eventuallyEq_clm_apply`).

## Implementation notes

The complex structure is Tau Ceti's continuous one, `TauCeti.Bundle.ContinuousComplexStructure`;
a `C^n` complex structure `SymplecticGeometry.Bundle.ContMDiffComplexStructure` gives one through
`toContinuousComplexStructure`. The fibres of `J.Fiber` are those of `V`, and a section `s` of `V`
is read as the section `x ↦ (J.fiberEquiv x).symm (s x)` of `J.Fiber`. The sign at a zero is
stated directly, as `1` or `-1` according as a continuous linear equivalence equal to the
linearization carries the orientation `o.orientationAt z` to the canonical orientation of the
fibre (`TauCeti.VectorBundleOrientation.complex`), with no new definition.

This form of the sign, and the case split on it in the private `sign_det_eq_ite` (an orientation
of a plane is the given one or its negative), follow Tau Ceti's
`TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_ite` and
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sign`, in
`TauCeti/Geometry/Manifold/VectorBundle/Section/EulerNumber.lean` of Tau Ceti's main branch at
commit 55525ca, which the pinned version of Tau Ceti does not have. Those state the sign for an
oriented real bundle and a chart with values in an inner product space; here the bundle is
`J.Fiber` with its complex orientation, and the chart takes values in `ℂ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  Theorem 2.7.5.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §11 (the Euler
  class as a count of zeros of a section).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§11 and 14.
-/

public section

open Bundle Module Set TauCeti TauCeti.Bundle
open scoped Manifold

namespace SymplecticGeometry

namespace Bundle

section Topological

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] (o : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {L : M → Type} [TopologicalSpace (TotalSpace G L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle G L] [VectorBundle ℂ G L]

local instance : VectorBundle ℝ G L := VectorBundle.restrictScalars ℝ ℂ G L

/-- **The first Chern number as a sum of local indices.** Let `L` be a complex line bundle, with
model `G` of complex dimension one, over a compact surface `M` with a homological orientation `o`,
and let `s` be a continuous section of `L` with finitely many zeros. Then the first Chern number
of `L` is the sum over the zeros of `s` of the local index of `s`, for the orientation of `L` as a
complex line. -/
theorem chernNumber_eq_sum_sectionIndex (hG : finrank ℂ G = 1) {s : ∀ x, L x}
    (hs : Continuous fun x ↦ TotalSpace.mk' G x (s x)) (hZ : {x | s x = 0}.Finite) :
    chernNumber o hn G L = ∑ z ∈ hZ.toFinset,
      (VectorBundleOrientation.reindex (finCongr (by rw [hG]))
        (VectorBundleOrientation.complex G L)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hG]) o hs z := by
  rw [chernNumber_def, firstChernClass_eq_complexEulerClass L (hG.trans (zero_add 1).symm),
    complexEulerClass_def]
  exact VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ o hs hn hZ

end Topological
section Smooth

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] [IsManifold 𝓘(ℝ, EM) 1 M] (hn : finrank ℝ EM = 2)
  (o : Manifold.Orientation 𝓘(ℝ, EM) M (Fin 2))
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V 𝓘(ℝ, EM)]
  (J : ContinuousComplexStructure F V) [Fact (finrank ℝ F = 2 * finrank ℂ ℂ)]

local instance (x : M) : ContinuousSMul ℝ (J.Fiber x) := IsScalarTower.continuousSMul ℂ

local instance : VectorBundle ℝ ℂ J.Fiber := VectorBundle.restrictScalars ℝ ℂ ℂ J.Fiber

omit [T2Space M] [CompactSpace M] [FiniteDimensional ℝ EM] [IsManifold 𝓘(ℝ, EM) 1 M]
  [ContMDiffVectorBundle 1 F V 𝓘(ℝ, EM)] in
/-- At a zero `z` of a `C¹` section `s`, the section read in the chart
`(chartAt EM z).transHomeomorph D` of `M` and in the trivialization of `J.Fiber` at `z` has a
derivative `A` with `A (D v) = e (Lz v)`, for `Lz` the linearization of `s` at `z` and `e` the
fibre map of the trivialization at `z`. -/
private theorem exists_hasFDerivAt_trivializationAt {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, F)) 1 fun x ↦ TotalSpace.mk' F x (s x))
    {z : M} (hz : s z = 0) (D : EM ≃L[ℝ] ℂ) :
    ∃ A : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun y ↦ (trivializationAt ℂ J.Fiber z (TotalSpace.mk' ℂ
        (((chartAt EM z).transHomeomorph D.toHomeomorph).symm y)
        ((J.fiberEquiv _).symm (s (((chartAt EM z).transHomeomorph D.toHomeomorph).symm y))))).2)
        A (D (chartAt EM z z)) ∧
      ∀ v : TangentSpace 𝓘(ℝ, EM) z, A (D v) =
        (trivializationAt ℂ J.Fiber z).linearEquivAt ℝ z (mem_baseSet_trivializationAt ℂ J.Fiber z)
          ((J.fiberEquiv z).symm (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z v)) := by
  set e := trivializationAt ℂ J.Fiber z
  set eV := trivializationAt F V z
  have hzV : z ∈ eV.baseSet := mem_baseSet_trivializationAt F V z
  have hzu : z ∈ J.unitSet z := J.mem_unitSet_self z
  -- The section read in `e` is `c x (h x)`, its reading `h` in the trivialization `eV` of `V`
  -- followed by a family `c` of linear maps continuous at `z`.
  set h : M → F := fun x ↦ (eV ⟨x, s x⟩).2 with hh
  set c : M → F →L[ℝ] ℂ := fun x ↦
    ((J.modelEquiv ℂ z).symm : F →L[ℝ] ℂ).comp (Ring.inverse (J.complexLinearPart z x))
  set fM : M → ℂ := fun x ↦ (e ⟨x, (J.fiberEquiv x).symm (s x)⟩).2
  have hfMc : (fun x ↦ c x (h x)) =ᶠ[nhds z] fM := by
    filter_upwards [(J.isOpen_unitSet z).mem_nhds hzu] with x hx
    exact (J.trivializationAt_fiberEquiv_symm_apply_snd ℂ hx (s x)).symm
  have hcz : ContinuousAt c z := continuousAt_const.clm_comp
    ((J.continuousOn_inverse_complexLinearPart z).continuousAt ((J.isOpen_unitSet z).mem_nhds hzu))
  have hhd : MDifferentiableAt 𝓘(ℝ, EM) 𝓘(ℝ, F) h z :=
    ((contMDiffAt_totalSpace_iff.mp (hs z)).2).mdifferentiableAt one_ne_zero
  have hh0 : h z = 0 := by
    simp only [hh, hz]
    exact congrArg Prod.snd (eV.zeroSection ℝ hzV)
  have hfMd := mvfderiv_eq_comp_of_eventuallyEq_clm_apply hfMc hcz hhd hh0
  have hLzh : sectionLinearization (F := F) 𝓘(ℝ, EM) id s z =
      (eV.symmL ℝ z).comp (mvfderiv 𝓘(ℝ, EM) h z) := sectionLinearization_def
  have hfMf : HasFDerivAt (fM ∘ (extChartAt 𝓘(ℝ, EM) z).symm) (mvfderiv 𝓘(ℝ, EM) fM z)
      (D.symm (D (chartAt EM z z))) := by
    rw [D.symm_apply_apply, TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm]
    exact (TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.1
      (mdifferentiableAt_of_eventuallyEq_clm_apply hfMc hcz hhd hh0)).hasFDerivAt
  let D' : TangentSpace 𝓘(ℝ, EM) z ≃L[ℝ] ℂ := D
  refine ⟨(mvfderiv 𝓘(ℝ, EM) fM z).comp (D'.symm : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, EM) z),
    (hfMf.comp _ D.symm.hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ ?_), fun v ↦ ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_symm_apply]
    rfl
  · have h₁ : (mvfderiv 𝓘(ℝ, EM) fM z).comp (D'.symm : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, EM) z) (D v) =
        mvfderiv 𝓘(ℝ, EM) fM z v :=
      congrArg (mvfderiv 𝓘(ℝ, EM) fM z) (D.symm_apply_apply v)
    rw [h₁, hfMd, Trivialization.linearEquivAt_apply,
      J.trivializationAt_fiberEquiv_symm_apply_snd ℂ hzu, hLzh,
      ContinuousLinearMap.comp_apply (eV.symmL ℝ z), Trivialization.symmL_apply _ hzV,
      eV.apply_mk_symm hzV]
    rfl

omit [T2Space M] [CompactSpace M] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, EM)] in
include hn in
open scoped Classical in
/-- At a zero `z` where the linearization `Lz` of `s` is onto, a linear map `A` of `ℂ` with
`A (D v) = e (Lz v)` as in `exists_hasFDerivAt_trivializationAt`, for `D` carrying the tangent
orientation at `z` to the orientation that `e` reads from the complex orientation, is invertible,
and the sign of its determinant is `1` or `-1` according as `Lz` preserves orientations or not. -/
private theorem sign_det_eq_ite {s : ∀ x, V x} {z : M}
    (hsurj : Function.Surjective (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z))
    {D : EM ≃L[ℝ] ℂ}
    (hD : (o.orientationAt z).map (Fin 2) D.toLinearEquiv =
      (trivializationAt ℂ J.Fiber z).mapOrientation (Fin 2)
        (mem_baseSet_trivializationAt ℂ J.Fiber z)
        (VectorBundleOrientation.reindex (finCongr (by simp))
          (VectorBundleOrientation.complex ℂ J.Fiber) z))
    {A : ℂ →L[ℝ] ℂ}
    (hA : ∀ v : TangentSpace 𝓘(ℝ, EM) z, A (D v) =
      (trivializationAt ℂ J.Fiber z).linearEquivAt ℝ z (mem_baseSet_trivializationAt ℂ J.Fiber z)
        ((J.fiberEquiv z).symm (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z v))) :
    A.det ≠ 0 ∧ (SignType.sign A.det : ℤ) =
      if ∃ e : TangentSpace 𝓘(ℝ, EM) z ≃L[ℝ] J.Fiber z,
          (e : TangentSpace 𝓘(ℝ, EM) z →L[ℝ] J.Fiber z) =
            ((J.fiberEquiv z).symm : V z →L[ℝ] J.Fiber z).comp
              (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z) ∧
          (o.orientationAt z).map (Fin 2) e.toLinearEquiv =
            VectorBundleOrientation.reindex (finCongr (by simp))
              (VectorBundleOrientation.complex ℂ J.Fiber) z
      then 1 else -1 := by
  set oE : VectorBundleOrientation ℂ J.Fiber (Fin 2) :=
    VectorBundleOrientation.reindex (finCongr (by simp))
      (VectorBundleOrientation.complex ℂ J.Fiber)
  set e := trivializationAt ℂ J.Fiber z
  have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt ℂ J.Fiber z
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, EM) z) := inferInstanceAs (FiniteDimensional ℝ EM)
  have : FiniteDimensional ℝ (J.Fiber z) := VectorBundle.finiteDimensional ℝ ℂ J.Fiber z
  have hrank : finrank ℝ (TangentSpace 𝓘(ℝ, EM) z) = finrank ℝ (J.Fiber z) := by
    rw [VectorBundle.finrank_eq ℝ ℂ J.Fiber z, Complex.finrank_real_complex]
    exact hn
  -- The linearization, as a linear equivalence `Leq` onto the fibre of `J.Fiber`, and `A` as the
  -- linear equivalence `Aeq = e ∘ Leq ∘ D⁻¹`.
  set L₁ : TangentSpace 𝓘(ℝ, EM) z →ₗ[ℝ] J.Fiber z :=
    ((((J.fiberEquiv z).symm : V z →L[ℝ] J.Fiber z).comp
      (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z) :
      TangentSpace 𝓘(ℝ, EM) z →L[ℝ] J.Fiber z) : TangentSpace 𝓘(ℝ, EM) z →ₗ[ℝ] J.Fiber z)
    with hL₁
  have hL₁s : Function.Surjective L₁ := (J.fiberEquiv z).symm.surjective.comp hsurj
  set Leq : TangentSpace 𝓘(ℝ, EM) z ≃ₗ[ℝ] J.Fiber z := LinearEquiv.ofBijective L₁
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).2 hL₁s, hL₁s⟩ with hLeq
  let D' : TangentSpace 𝓘(ℝ, EM) z ≃L[ℝ] ℂ := D
  set Aeq : ℂ ≃ₗ[ℝ] ℂ := (D'.symm.toLinearEquiv.trans Leq).trans (e.linearEquivAt ℝ z hze)
    with hAeq
  have hdetA : A.det = LinearMap.det (Aeq : ℂ →ₗ[ℝ] ℂ) := by
    refine congrArg LinearMap.det (LinearMap.ext fun u ↦ ?_)
    obtain ⟨v, rfl⟩ := D'.surjective u
    rw [ContinuousLinearMap.coe_coe]
    refine (hA v).trans ?_
    simp only [hAeq, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.symm_apply_apply, hLeq, LinearEquiv.ofBijective_apply, hL₁,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    rfl
  have hcard : Fintype.card (Fin 2) = finrank ℝ ℂ := by simp
  -- `Aeq` carries the orientation `ω` of `ℂ` that `e` reads to the image of the tangent
  -- orientation under `Leq`, read in `e`.
  set ω := e.mapOrientation (Fin 2) hze (oE z)
  have hωA : Orientation.map (Fin 2) Aeq ω =
      e.mapOrientation (Fin 2) hze (Orientation.map (Fin 2) Leq (o.orientationAt z)) := by
    rw [hAeq, Orientation.map_trans, Orientation.map_trans, Trivialization.mapOrientation_apply,
      ← hD]
    congr 2
    exact Orientation.map_symm_map D.toLinearEquiv (o.orientationAt z)
  refine ⟨hdetA ▸ (LinearEquiv.isUnit_det' Aeq).ne_zero, ?_⟩
  split_ifs with hP
  · obtain ⟨e', he', hor⟩ := hP
    have hLe : Orientation.map (Fin 2) Leq (o.orientationAt z) = oE z := by
      have h : Leq = e'.toLinearEquiv := LinearEquiv.ext fun v ↦
        (congrArg (fun f : TangentSpace 𝓘(ℝ, EM) z →L[ℝ] J.Fiber z ↦ f v) he').symm
      rw [h, ← hor]
    have hpos : 0 < A.det := by
      rw [hdetA, ← Orientation.map_eq_iff_det_pos ω Aeq hcard, hωA, hLe]
    rw [sign_pos hpos, SignType.coe_one]
  · have hLe : Orientation.map (Fin 2) Leq (o.orientationAt z) = -oE z := by
      refine ((Orientation.map (Fin 2) Leq (o.orientationAt z)).eq_or_eq_neg (oE z)
        (by rw [← hrank]; simp [hn])).resolve_left fun h ↦ hP ?_
      have : T2Space (J.Fiber z) := FiberBundle.t2Space ℂ J.Fiber z
      exact ⟨Leq.toContinuousLinearEquiv, by ext v; rfl, h⟩
    have hneg : A.det < 0 := by
      rw [hdetA, ← Orientation.map_eq_neg_iff_det_neg ω Aeq hcard, hωA, hLe,
        Trivialization.mapOrientation_neg]
    rw [sign_neg hneg, SignType.coe_neg_one]

omit [CompactSpace M] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, EM)] in
open scoped Classical in
/-- **The local index at a transverse zero.** At a zero `z` of a `C¹` section `s` with finitely
many zeros, where the linearization of `s` is onto, the local index of `s` for the complex
orientation of `J.Fiber` is `1` or `-1` according as the linearization carries the orientation of
the tangent plane to the complex orientation of the fibre or not. -/
private theorem sectionIndex_eq_ite {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, F)) 1 fun x ↦ TotalSpace.mk' F x (s x))
    (hs' : Continuous fun x ↦ TotalSpace.mk' ℂ x ((J.fiberEquiv x).symm (s x)))
    (hZ : {x | s x = 0}.Finite) {z : M} (hz : s z = 0)
    (hsurj : Function.Surjective (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z)) :
    (VectorBundleOrientation.reindex (finCongr (by simp))
        (VectorBundleOrientation.complex ℂ J.Fiber)).sectionIndex (n := 1)
        Complex.finrank_real_complex (o.toHomologicalOrientation hn) hs' z =
      if ∃ e : TangentSpace 𝓘(ℝ, EM) z ≃L[ℝ] J.Fiber z,
          (e : TangentSpace 𝓘(ℝ, EM) z →L[ℝ] J.Fiber z) =
            ((J.fiberEquiv z).symm : V z →L[ℝ] J.Fiber z).comp
              (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z) ∧
          (o.orientationAt z).map (Fin 2) e.toLinearEquiv =
            VectorBundleOrientation.reindex (finCongr (by simp))
              (VectorBundleOrientation.complex ℂ J.Fiber) z
      then 1 else -1 := by
  set oE : VectorBundleOrientation ℂ J.Fiber (Fin (1 + 1)) :=
    VectorBundleOrientation.reindex (finCongr (by simp))
      (VectorBundleOrientation.complex ℂ J.Fiber)
  set e := trivializationAt ℂ J.Fiber z
  have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt ℂ J.Fiber z
  -- The trivialization `e` reads every fibre orientation as one orientation `ω` of `ℂ`.
  set ω := e.mapOrientation (Fin (1 + 1)) hze (oE z)
  have ho : ∀ x (hx : x ∈ e.baseSet), e.mapOrientation (Fin (1 + 1)) hx (oE x) = ω := by
    intro x hx
    simp only [ω, oE, VectorBundleOrientation.reindex_apply, Trivialization.mapOrientation_reindex,
      VectorBundleOrientation.mapOrientation_complex]
  -- A linear identification `D` of the model with `ℂ` that carries the orientation of the tangent
  -- space at `z` to `ω`, and the chart `φ` of `M` at `z` with values in `ℂ` that it gives.
  obtain ⟨D, hD⟩ : ∃ D : EM ≃L[ℝ] ℂ, (o.orientationAt z).map (Fin 2) D.toLinearEquiv = ω := by
    let b₁ : Basis (Fin 2) ℝ EM :=
      (Module.finBasisOfFinrankEq ℝ EM hn).adjustToOrientation (o.orientationAt z)
    let b₂ : Basis (Fin 2) ℝ ℂ :=
      (Module.finBasisOfFinrankEq ℝ ℂ Complex.finrank_real_complex).adjustToOrientation ω
    have hb₁ : b₁.orientation = o.orientationAt z := Basis.orientation_adjustToOrientation _ _
    have hb₂ : b₂.orientation = ω := Basis.orientation_adjustToOrientation _ _
    refine ⟨(b₁.equiv b₂ (Equiv.refl _)).toContinuousLinearEquiv, ?_⟩
    rw [← hb₁, ← hb₂, ← Basis.orientation_map]
    exact congrArg Basis.orientation ((b₁.map_equiv b₂ (Equiv.refl _)).trans b₂.reindex_refl)
  set φ : OpenPartialHomeomorph M ℂ := (chartAt EM z).transHomeomorph D.toHomeomorph with hφ
  have hzφ : z ∈ φ.source := by
    rw [hφ, OpenPartialHomeomorph.transHomeomorph_source]
    exact mem_chart_source EM z
  -- The orientation of `M` at `z` is the one selected by `φ` and `ω`, so that `φ`, translated,
  -- carries it to the local orientation of `ℂ` selected by `ω`.
  have hoM : o.toHomologicalOrientation hn z =
      φ.localOrientationOfOrientedChart hzφ ω Complex.finrank_real_complex := by
    refine Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart
      hn o Complex.finrank_real_complex φ hzφ D ?_ hD
    refine D.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, EM)) z] with y hy
    have h := (extChartAt 𝓘(ℝ, EM) z).right_inv hy
    simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, OpenPartialHomeomorph.toFun_eq_coe] at h
    simpa [φ] using h
  -- The centred chart is the case `L = id` of the chart map of
  -- `OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart`.
  have hσ : (⟨fun x : φ.source ↦ φ x - φ z,
      φ.continuousOn.domRestrict.sub continuous_const⟩ : C(φ.source, ℂ)) =
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ →L[ℝ] ℂ) : C(ℂ, ℂ)).comp
        ((⟨fun y ↦ y - φ z, by fun_prop⟩ : C(ℂ, ℂ)).comp φ.sourceRestrict) :=
    ContinuousMap.ext fun x ↦ by
      -- The topologies on `ℂ` in the type of `φ` and in `C(φ.source, ℂ)` agree only up to
      -- unfolding instances, so `rw` does not match `ContinuousMap.coe_mk`.
      erw [ContinuousMap.coe_mk]
      simp
  have hφl := φ.localHomologyMap_chart_localOrientationOfOrientedChart hzφ
    (ContinuousLinearEquiv.refl ℝ ℂ) ω Complex.finrank_real_complex Complex.finrank_real_complex
    (by
      rw [← hσ]
      exact fun x hx ↦ Subtype.ext (φ.injOn x.property hzφ (sub_eq_zero.1 hx)))
  have hrefl : (ContinuousLinearEquiv.refl ℝ ℂ).toLinearEquiv = LinearEquiv.refl ℝ ℂ := by
    ext x
    simp
  simp only [← hσ, hrefl, Orientation.map_refl, Equiv.refl_apply] at hφl
  rw [← hoM] at hφl
  -- An open neighbourhood `U` of `z` in which `z` is the only zero of `s`.
  set U := e.baseSet ∩ φ.source ∩ ({x | s x = 0} \ {z})ᶜ
  have hUo : IsOpen U :=
    (e.open_baseSet.inter φ.open_source).inter (hZ.sdiff (t := {z})).isClosed.isOpen_compl
  have hzU : z ∈ U := ⟨⟨hze, hzφ⟩, fun h ↦ h.2 rfl⟩
  have hUz : ∀ x ∈ U, (J.fiberEquiv x).symm (s x) = 0 → x = z := fun x hx h0 ↦
    by_contra fun hxz ↦ hx.2 ⟨(J.fiberEquiv x).symm.map_eq_zero_iff.1 h0, hxz⟩
  have hsz : (J.fiberEquiv z).symm (s z) = 0 := by rw [hz, map_zero]
  obtain ⟨A, hAd, hA⟩ := exists_hasFDerivAt_trivializationAt J hs hz D
  obtain ⟨hdet, hsign⟩ := sign_det_eq_ite hn o J hsurj hD hA
  rw [VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt oE
    Complex.finrank_real_complex (o.toHomologicalOrientation hn) hs' e φ hUo hzU hUz hsz
    (fun x hx ↦ hx.1.1) (fun x hx ↦ hx.1.2) (fun x hx ↦ ho x _) hφl hAd hdet, hsign]

open scoped Classical in
/-- **The first Chern number counts the zeros of a transverse section.** Let `M` be a closed `C¹`
surface with an orientation `o`, `V` a real `C¹` vector bundle of rank two over `M` with a
continuous complex structure `J`, and `s` a `C¹` section of `V` transverse to the zero section:
at every zero `z`, the linearization `Lz : T_z M → V_z` of `s` is onto. Then `s` has finitely many
zeros, and the first Chern number of the complex line bundle `J.Fiber` is the sum over the zeros
of `s` of `1` where `Lz` carries the orientation of `T_z M` to the complex orientation of the
fibre, and of `-1` where it does not.

Milestone: *First Chern number as an Euler number*. -/
theorem chernNumber_eq_sum_sign_of_transverse {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, F)) 1 fun x ↦ TotalSpace.mk' F x (s x))
    (htr : ∀ z, s z = 0 → Function.Surjective (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z)) :
    {z | s z = 0}.Finite ∧
      chernNumber (o.toHomologicalOrientation hn) hn ℂ J.Fiber =
        ∑ᶠ z ∈ {z | s z = 0},
          if ∃ e : TangentSpace 𝓘(ℝ, EM) z ≃L[ℝ] J.Fiber z,
              (e : TangentSpace 𝓘(ℝ, EM) z →L[ℝ] J.Fiber z) =
                ((J.fiberEquiv z).symm : V z →L[ℝ] J.Fiber z).comp
                  (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z) ∧
              (o.orientationAt z).map (Fin 2) e.toLinearEquiv =
                VectorBundleOrientation.reindex (finCongr (by simp))
                  (VectorBundleOrientation.complex ℂ J.Fiber) z
          then 1 else -1 := by
  have hF : finrank ℝ F = 2 := (Fact.out : finrank ℝ F = 2 * finrank ℂ ℂ).trans (by simp)
  have : ∀ x, T2Space (V x) := FiberBundle.t2Space F V
  have : ∀ x, FiniteDimensional ℝ (V x) := fun x ↦ VectorBundle.finiteDimensional ℝ F V x
  have hZ : {z | s z = 0}.Finite :=
    finite_sectionZero_of_contMDiff (b := id) one_ne_zero hs
      (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _) htr
      (fun _ _ ↦ by rw [index_sectionLinearization_of_finiteDimensional, hn, hF, sub_self])
  refine ⟨hZ, ?_⟩
  have hs' : Continuous fun x ↦ TotalSpace.mk' ℂ x ((J.fiberEquiv x).symm (s x)) :=
    ((J.totalSpaceHomeomorph ℂ).symm.continuous.comp hs.continuous).congr fun x ↦ by simp
  have hset : {x | (J.fiberEquiv x).symm (s x) = 0} = {x | s x = 0} := by
    ext x
    exact (J.fiberEquiv x).symm.map_eq_zero_iff
  rw [chernNumber_eq_sum_sectionIndex _ hn (finrank_self ℂ) hs' (hset ▸ hZ),
    finsum_mem_eq_finite_toFinset_sum _ hZ]
  refine Finset.sum_congr (by simp) fun z hz ↦ ?_
  have hz' : s z = 0 := hZ.mem_toFinset.1 (by simpa [hset] using hz)
  exact sectionIndex_eq_ite hn o J hs hs' hZ hz' (htr z hz')

end Smooth

end Bundle

end SymplecticGeometry
