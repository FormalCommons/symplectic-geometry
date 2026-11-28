/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
public import SymplecticGeometry.Topology.Algebra.Module.Equiv.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Derivative
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmoothZero
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.ComplexStructure
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank

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
`J.Fiber`, in the form
`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually`, which
finds the neighbourhood isolating `z` from the invertibility of the Jacobian. The chart is the
preferred chart at `z` followed by a linear identification `D` of
the model with `ℂ` that matches the orientations; translated so that `z` goes to the origin, it
carries the local orientation of `M` at `z` to the local orientation of `ℂ` selected by the image
of the tangent orientation under `D`
(`TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph`).
The trivialization of `J.Fiber` is that of `V` followed by a family of linear maps that is only
continuous; since the section vanishes at `z`, the linearization at `z` of `s` seen as a section
of `J.Fiber` is still that of `s` followed by `(J.fiberEquiv z).symm`
(`TauCeti.Bundle.ContinuousComplexStructure.sectionLinearization_fiberEquiv_symm`), and the
derivative along the chart of `M` comes from Tau Ceti's
`TauCeti.hasFDerivAt_comp_chartAt_symm_sectionLinearization`.

## Implementation notes

The complex structure is Tau Ceti's continuous one, `TauCeti.Bundle.ContinuousComplexStructure`;
a `C^n` complex structure `SymplecticGeometry.Bundle.ContMDiffComplexStructure` gives one through
`toContinuousComplexStructure`. The fibres of `J.Fiber` are those of `V`, and a section `s` of `V`
is read as the section `x ↦ (J.fiberEquiv x).symm (s x)` of `J.Fiber`. The sign at a zero is
stated directly, as `1` or `-1` according as a continuous linear equivalence equal to the
linearization carries the orientation `o.orientationAt z` to the canonical orientation of the
fibre (`TauCeti.VectorBundleOrientation.complex`), with no new definition. At a transverse zero the
linearization is a linear isomorphism by Tau Ceti's
`TauCeti.exists_continuousLinearEquiv_eq_sectionLinearization_of_surjective`.

This form of the sign, and the case split on it in the private `sign_det_eq_ite` (an orientation
of a plane is the given one or its negative), follow Tau Ceti's
`TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_ite` and
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sign`, in Tau Ceti's
`TauCeti/Geometry/Manifold/VectorBundle/Section/EulerNumber.lean`. Those state the sign for an
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

open Bundle Filter Module Set TauCeti TauCeti.Bundle
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

open scoped VectorBundle.ComplexToReal

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

open scoped VectorBundle.ComplexToReal

omit [T2Space M] [CompactSpace M] [FiniteDimensional ℝ EM] [IsManifold 𝓘(ℝ, EM) 1 M]
  [ContMDiffVectorBundle 1 F V 𝓘(ℝ, EM)] in
/-- At a zero `z` of a `C¹` section `s`, the section read in the chart
`(chartAt EM z).transHomeomorph (𝓘(ℝ, EM).toHomeomorph.trans D)` of `M` and in the trivialization
of `J.Fiber` at `z` has a derivative `A` with `A (D v) = e (Lz v)`, for `Lz` the linearization of
`s` at `z` and `e` the fibre map of the trivialization at `z`. -/
private theorem exists_hasFDerivAt_trivializationAt {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, F)) 1 fun x ↦ TotalSpace.mk' F x (s x))
    {z : M} (hz : s z = 0) (D : EM ≃L[ℝ] ℂ) :
    ∃ A : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun y ↦ (trivializationAt ℂ J.Fiber z (TotalSpace.mk' ℂ
        (((chartAt EM z).transHomeomorph (𝓘(ℝ, EM).toHomeomorph.trans D.toHomeomorph)).symm y)
        ((J.fiberEquiv _).symm (s (((chartAt EM z).transHomeomorph
          (𝓘(ℝ, EM).toHomeomorph.trans D.toHomeomorph)).symm y))))).2)
        A (D (chartAt EM z z)) ∧
      ∀ v : TangentSpace 𝓘(ℝ, EM) z, A (D v) =
        (trivializationAt ℂ J.Fiber z).linearEquivAt ℝ z (mem_baseSet_trivializationAt ℂ J.Fiber z)
          ((J.fiberEquiv z).symm (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z v)) := by
  set e := trivializationAt ℂ J.Fiber z
  have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt ℂ J.Fiber z
  have hhd : MDifferentiableAt 𝓘(ℝ, EM) 𝓘(ℝ, F) (fun x ↦ (trivializationAt F V z ⟨x, s x⟩).2) z :=
    ((contMDiffAt_totalSpace_iff.mp (hs z)).2).mdifferentiableAt one_ne_zero
  have hfMf := hasFDerivAt_comp_chartAt_symm_sectionLinearization (e := e) (b := id)
    (s := fun x ↦ (J.fiberEquiv (id x)).symm (s x)) continuousAt_id hze
    (J.mdifferentiableAt_trivializationAt_fiberEquiv_symm ℂ (b := id) continuousAt_id hhd hz)
    (by simp [hz])
  rw [← D.symm_apply_apply (chartAt EM z z),
    J.sectionLinearization_fiberEquiv_symm ℂ (b := id) continuousAt_id hhd hz] at hfMf
  let D' : TangentSpace 𝓘(ℝ, EM) z ≃L[ℝ] ℂ := D
  refine ⟨((e.continuousLinearMapAt ℝ z).comp (((J.fiberEquiv z).symm : V z →L[ℝ] J.Fiber z).comp
      (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z))).comp
      (D'.symm : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, EM) z),
    (hfMf.comp _ D.symm.hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ ?_), fun v ↦ ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_symm_apply]
    rfl
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    have hv : D'.symm (D v) = v := D.symm_apply_apply v
    rw [hv, Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (hb := hze),
      Trivialization.linearEquivAt_apply]

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
        (VectorBundleOrientation.reindex (finCongr Complex.two_mul_finrank_self)
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
            VectorBundleOrientation.reindex (finCongr Complex.two_mul_finrank_self)
              (VectorBundleOrientation.complex ℂ J.Fiber) z
      then 1 else -1 := by
  set oE : VectorBundleOrientation ℂ J.Fiber (Fin 2) :=
    VectorBundleOrientation.reindex (finCongr Complex.two_mul_finrank_self)
      (VectorBundleOrientation.complex ℂ J.Fiber)
  set e := trivializationAt ℂ J.Fiber z
  have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt ℂ J.Fiber z
  have : FiniteDimensional ℝ (J.Fiber z) := VectorBundle.finiteDimensional ℝ ℂ J.Fiber z
  have hrank : finrank ℝ (TangentSpace 𝓘(ℝ, EM) z) = finrank ℝ (J.Fiber z) := by
    rw [VectorBundle.finrank_eq ℝ ℂ J.Fiber z, Complex.finrank_real_complex]
    exact hn
  -- The linearization, as a linear equivalence `Leq` onto the fibre of `J.Fiber`, and `A` as the
  -- linear equivalence `Aeq = e ∘ Leq ∘ D⁻¹`.
  have hF : finrank ℝ F = 2 := (Fact.out : finrank ℝ F = 2 * finrank ℂ ℂ).trans
    Complex.two_mul_finrank_self
  obtain ⟨L, hL⟩ :=
    exists_continuousLinearEquiv_eq_sectionLinearization_of_surjective (hn.trans hF.symm) hsurj
  set Leq : TangentSpace 𝓘(ℝ, EM) z ≃ₗ[ℝ] J.Fiber z :=
    (L.trans (J.fiberEquiv z).symm).toLinearEquiv with hLeq
  have hLeq_apply (v : TangentSpace 𝓘(ℝ, EM) z) :
      Leq v = (J.fiberEquiv z).symm (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z v) := by
    rw [hLeq, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.trans_apply, ← hL,
      ContinuousLinearEquiv.coe_coe]
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
      ContinuousLinearEquiv.symm_apply_apply, hLeq_apply]
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
      have h : Leq = e'.toLinearEquiv := LinearEquiv.ext fun v ↦ (hLeq_apply v).trans
        (congrArg (fun f : TangentSpace 𝓘(ℝ, EM) z →L[ℝ] J.Fiber z ↦ f v) he').symm
      rw [h, ← hor]
    have hpos : 0 < A.det := by
      rw [hdetA, ← Orientation.map_eq_iff_det_pos ω Aeq hcard, hωA, hLe]
    rw [sign_pos hpos, SignType.coe_one]
  · have hLe : Orientation.map (Fin 2) Leq (o.orientationAt z) = -oE z := by
      refine ((Orientation.map (Fin 2) Leq (o.orientationAt z)).eq_or_eq_neg (oE z)
        (by rw [← hrank]; simp [hn])).resolve_left fun h ↦ hP ?_
      exact ⟨L.trans (J.fiberEquiv z).symm, by ext v; exact hLeq_apply v, h⟩
    have hneg : A.det < 0 := by
      rw [hdetA, ← Orientation.map_eq_neg_iff_det_neg ω Aeq hcard, hωA, hLe,
        Trivialization.mapOrientation_neg]
    rw [sign_neg hneg, SignType.coe_neg_one]

omit [CompactSpace M] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, EM)] in
open scoped Classical in
/-- **The local index at a transverse zero.** At a zero `z` of a `C¹` section `s` where the
linearization of `s` is onto, the local index of `s` for the complex orientation of `J.Fiber`
is `1` or `-1` according as the linearization carries the orientation of the tangent plane to
the complex orientation of the fibre or not. -/
private theorem sectionIndex_eq_ite {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, F)) 1 fun x ↦ TotalSpace.mk' F x (s x))
    (hs' : Continuous fun x ↦ TotalSpace.mk' ℂ x ((J.fiberEquiv x).symm (s x))) {z : M}
    (hz : s z = 0)
    (hsurj : Function.Surjective (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z)) :
    (VectorBundleOrientation.reindex (finCongr Complex.two_mul_finrank_self)
        (VectorBundleOrientation.complex ℂ J.Fiber)).sectionIndex (n := 1)
        Complex.finrank_real_complex (o.toHomologicalOrientation hn) hs' z =
      if ∃ e : TangentSpace 𝓘(ℝ, EM) z ≃L[ℝ] J.Fiber z,
          (e : TangentSpace 𝓘(ℝ, EM) z →L[ℝ] J.Fiber z) =
            ((J.fiberEquiv z).symm : V z →L[ℝ] J.Fiber z).comp
              (sectionLinearization (F := F) 𝓘(ℝ, EM) id s z) ∧
          (o.orientationAt z).map (Fin 2) e.toLinearEquiv =
            VectorBundleOrientation.reindex (finCongr Complex.two_mul_finrank_self)
              (VectorBundleOrientation.complex ℂ J.Fiber) z
      then 1 else -1 := by
  set oE : VectorBundleOrientation ℂ J.Fiber (Fin (1 + 1)) :=
    VectorBundleOrientation.reindex (finCongr Complex.two_mul_finrank_self)
      (VectorBundleOrientation.complex ℂ J.Fiber)
  set e := trivializationAt ℂ J.Fiber z
  have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt ℂ J.Fiber z
  -- The trivialization `e` reads every fibre orientation as one orientation `ω` of `ℂ`.
  set ω := e.mapOrientation (Fin (1 + 1)) hze (oE z)
  have ho : ∀ x (hx : x ∈ e.baseSet), e.mapOrientation (Fin (1 + 1)) hx (oE x) = ω := by
    intro x hx
    simp only [ω, oE, VectorBundleOrientation.mapOrientation_reindex_complex]
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
  -- The chart `φ` of `M` at `z` with values in `ℂ`, the preferred chart followed by `D`;
  -- translated, it carries the orientation of `M` at `z` to the local orientation selected by `ω`.
  set φ : OpenPartialHomeomorph M ℂ :=
    (chartAt EM z).transHomeomorph (𝓘(ℝ, EM).toHomeomorph.trans D.toHomeomorph)
  have hzφ : z ∈ φ.source := by simp [φ]
  have hφl := Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph
    hn o Complex.finrank_real_complex D z
  rw [hD] at hφl
  have hsz : (J.fiberEquiv z).symm (s z) = 0 := by rw [hz, map_zero]
  obtain ⟨A, hAd, hA⟩ := exists_hasFDerivAt_trivializationAt J hs hz D
  obtain ⟨hdet, hsign⟩ := sign_det_eq_ite hn o J hsurj hD hA
  rw [VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually oE
    Complex.finrank_real_complex (o.toHomologicalOrientation hn) hs' e φ hsz hze hzφ
    (Eventually.of_forall ho) hφl hAd hdet, hsign]

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
                VectorBundleOrientation.reindex (finCongr Complex.two_mul_finrank_self)
                  (VectorBundleOrientation.complex ℂ J.Fiber) z
          then 1 else -1 := by
  have hF : finrank ℝ F = 2 := (Fact.out : finrank ℝ F = 2 * finrank ℂ ℂ).trans
    Complex.two_mul_finrank_self
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
  exact sectionIndex_eq_ite hn o J hs hs' hz' (htr z hz')

end Smooth

end Bundle

end SymplecticGeometry
