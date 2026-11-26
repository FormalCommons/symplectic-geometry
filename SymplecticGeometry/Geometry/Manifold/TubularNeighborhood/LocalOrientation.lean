/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import TauCeti.LinearAlgebra.Orientation.Prod
public import SymplecticGeometry.Geometry.Manifold.Orientation.NormalOrientation
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Normalized
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.ExtChartAt
public import SymplecticGeometry.Topology.VectorBundle.Thom.LocalChart
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Point
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Sign
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# A normalized tube read in a chart, and the orientation it carries

Let `f : Z → X` be a smooth embedding between manifolds over boundaryless models, with normal
bundle `ν` of model fibre `P`, and let `Φ` be a normalized tube of `f`
(`TauCeti.SmoothEmbedding.IsNormalizedTube`), a diffeomorphism of the total space of `ν` onto an
open set `W` of `X`. Fix `z : Z` and let `e` be the preferred trivialization of `ν` at `z`.
Reading the inverse of `Φ` in the preferred chart of the total space at `0_z`, which is `e`
followed by the chart of `Z` at `z` on the base, and putting the normal coordinate first, gives a
chart `normalTubeChart Φ z : X → P × E` of `X` around `f z`. Its inverse applies `Φ` to the
inverse of the chart of the total space at `0_z` (`normalTubeChart_symm_apply`), and its source
and target are described by `mem_normalTubeChart_source_iff` and `normalTubeChart_target`.

Read in the chart of `X` at `f z`, this chart has derivative `normalTubeChartDeriv Φ z` at `f z`
(`hasFDerivAt_normalTubeChart`): the inverse of the differential of `Φ` at `0_z`, with the
factors exchanged, by Mathlib's `HasFDerivAt.of_local_left_inverse` applied to `Φ` read in the
two charts. Its inverse is block triangular: it sends a tangent vector `(0, u)` of `Z` to
the differential of `f` at `z` applied to `u`
(`normalTubeChartDeriv_symm_apply_zero_left`, from
`TauCeti.SmoothEmbedding.mfderiv_zeroSection_apply_horizontal_of_apply_zeroSection`), and the
normal class of the image of `(w, u)` is the vector of `ν_z` with coordinate `w` in `e`
(`normalClassL_normalTubeChartDeriv_symm_apply`, from
`TauCeti.SmoothEmbedding.IsNormalizedTube.normalClassL_mfderiv_zeroSection`).

Hence this derivative carries the orientation of `X` at `f z` to the product of the orientation
of `Z` at `z` and the normal orientation `normalOrientation f hn hdim oX oZ` at `z` read in `e`,
tangent factor first, moved to `P × E` by the exchange of factors
(`map_orientationAt_normalTubeChartDeriv`). This is the characterization
`TauCeti.SmoothEmbedding.ofExact_normalOrientation` of the normal orientation, through Tau Ceti's
splitting lemma `Orientation.ofExact_eq_map_prod` and `Orientation.map_prod`. No sign appears, in
any dimension and codimension, including zero.

In positive dimensions, the local orientation of `X` at `f z` is then read in the chart, translated
so that `f z` goes to the origin: it is the cross product `TauCeti.LocalOrientation.cross` of the
local orientation of the normal fibre and that of `Z`, normal factor first, with no sign
(`localHomologyMap_sub_normalTubeChart_toHomologicalOrientation`). The chart is first followed by
a linear identification of `P × E` with a Euclidean space, in which the library's
`TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`
reads the local orientation of `X` through the derivative, and Tau Ceti's
`OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart` carries it back to
`P × E`; this is the argument of the library's
`TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph`, for
a chart that is not a preferred one. The derivative carries the orientation of `X` to the
product orientation tangent factor first, exchanged; the cross product normal first is the local
orientation of that same orientation, by the library's
`TauCeti.LocalOrientation.cross_eq_map_prodComm_prod` and Tau Ceti's
`TauCeti.LocalOrientation.prod_localOrientation` and `Orientation.localOrientation_map`.

The same class is then read from the total space of the normal bundle, through the chart
`Bundle.Trivialization.localChart` built from `e` and the chart `c` of `Z` at `z` translated so
that `z` goes to `0` (`localHomologyMap_localChartLocalHomologyIso_hom_cross`): the isomorphism
`Bundle.Trivialization.localChartLocalHomologyIso` sends the cross product to a local class of
the total space at `0_z`, and `Φ` sends that class to the local orientation of `X` at `f z`. Up
to the translation by the coordinate of `z`, the chart `normalTubeChart Φ z` undoes `Φ` after
that chart of the total space (`tube_localChart_mem_normalTubeChart_source`,
`normalTubeChart_apply_tube_localChart`); as both maps of local homology are induced by open
embeddings, the statement follows from the one for the chart by functoriality of
`TauCeti.localHomologyMap` and excision.

## Main definitions

* `TauCeti.SmoothEmbedding.normalTubeChart`: the chart of `X` at `f z` given by the inverse of a
  tube read in the preferred chart of the normal bundle at `0_z`, normal coordinate first.
* `TauCeti.SmoothEmbedding.normalTubeChartDeriv`: its derivative at `f z`, read in the chart of
  `X` at `f z`.

## Main results

* `TauCeti.SmoothEmbedding.hasFDerivAt_normalTubeChart`: the chart read in the chart of `X` at
  `f z` has derivative `normalTubeChartDeriv Φ z` there.
* `TauCeti.SmoothEmbedding.normalTubeChartDeriv_symm_apply_zero_left`,
  `TauCeti.SmoothEmbedding.normalClassL_normalTubeChartDeriv_symm_apply`: the inverse of the
  derivative is block triangular.
* `TauCeti.SmoothEmbedding.map_orientationAt_normalTubeChartDeriv`: the derivative carries the
  orientation of `X` to the exchanged product of the orientation of `Z` and the normal
  orientation.
* `TauCeti.SmoothEmbedding.localHomologyMap_sub_normalTubeChart_toHomologicalOrientation`: in
  positive dimensions, the chart carries the local orientation of `X` at `f z` to the cross
  product of the local orientations of the normal fibre and of `Z`, normal factor first.
* `TauCeti.SmoothEmbedding.localHomologyMap_localChartLocalHomologyIso_hom_cross`: in positive
  dimensions, the tube carries the cross product, read in the total space at `0_z` through
  `Bundle.Trivialization.localChartLocalHomologyIso`, to the local orientation of `X` at `f z`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Manifold Topology ContDiff TensorProduct

namespace TauCeti.SmoothEmbedding

variable {E V P H G Z X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]
  {f : SmoothEmbedding I J ∞ Z X} {hn : (∞ : ℕ∞ω) ≠ 0}
  {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E} {W : TopologicalSpace.Opens X}

/-- The tube `Φ` as an open partial homeomorphism from the total space of the normal bundle to
`X`, with source everything and target `W`. -/
private def tubeOPH
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z) :
    letI := f.normalSpaceFiberBundle hn hdim
    OpenPartialHomeomorph (TotalSpace P (fun x ↦ f.NormalSpace x hn)) X :=
  letI := f.normalSpaceFiberBundle hn hdim
  Φ.toHomeomorph.toOpenPartialHomeomorph.trans
    (W.openPartialHomeomorphSubtypeCoe ⟨Φ (zeroSection P _ z)⟩)

/-- **The chart of a tube at a point of the submanifold.** For a tube `Φ` of `f` onto `W` and
`z : Z`, the chart of `X`, with source inside `W`, that reads `Φ⁻¹ x` in the preferred chart of
the total space of the normal bundle at `0_z` and puts the normal coordinate first: `x` goes to
`(w, u)`, where `(b, w)` is the image of `Φ⁻¹ x` under the preferred trivialization at `z` and
`u` is the coordinate of `b` in the chart of `Z` at `z` (`normalTubeChart_apply_eq`). For a
normalized tube its source contains `f z` (`mem_normalTubeChart_source`). -/
def normalTubeChart
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z) :
    OpenPartialHomeomorph X (P × E) :=
  letI := f.normalSpaceFiberBundle hn hdim
  ((tubeOPH Φ z).symm.trans (chartAt (ModelProd H P) (zeroSection P _ z))).trans
    (((I.prod 𝓘(ℝ, P)).toHomeomorph.trans (Homeomorph.prodComm E P)).toOpenPartialHomeomorph)

variable (Φ : letI := f.normalSpaceFiberBundle hn hdim
  TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z)

omit [J.Boundaryless] in
/-- The chart of the tube at `z` is the inverse of `Φ`, as an open partial homeomorphism onto
`W`, followed by the chart of the total space at `0_z`, the model embedding of `I.prod 𝓘(ℝ, P)`
and the exchange of factors. -/
theorem normalTubeChart_def :
    letI := f.normalSpaceFiberBundle hn hdim
    normalTubeChart Φ z =
      ((Φ.toHomeomorph.toOpenPartialHomeomorph.trans
        (W.openPartialHomeomorphSubtypeCoe ⟨Φ (zeroSection P _ z)⟩)).symm.trans
          (chartAt (ModelProd H P) (zeroSection P _ z))).trans
        (((I.prod 𝓘(ℝ, P)).toHomeomorph.trans
          (Homeomorph.prodComm E P)).toOpenPartialHomeomorph) :=
  (rfl)

omit [I.Boundaryless] [J.Boundaryless] in
private theorem tubeOPH_symm_apply {x : X} (hx : x ∈ W) :
    letI := f.normalSpaceFiberBundle hn hdim
    (tubeOPH Φ z).symm x = Φ.symm ⟨x, hx⟩ := by
  let := f.normalSpaceFiberBundle hn hdim
  have hT : tubeOPH Φ z (Φ.symm ⟨x, hx⟩) = x := by simp [tubeOPH]
  nth_rw 1 [← hT]
  exact (tubeOPH Φ z).left_inv (by simp [tubeOPH])

omit [J.Boundaryless] in
/-- The inverse of the chart of the tube at `z` reads a point of `P × E`, factors exchanged, in
the inverse of the extended chart of the total space at `0_z`, and applies `Φ`. -/
theorem normalTubeChart_symm_apply (y : P × E) :
    letI := f.normalSpaceFiberBundle hn hdim
    (normalTubeChart Φ z).symm y =
      Φ ((extChartAt (I.prod 𝓘(ℝ, P)) (zeroSection P _ z)).symm y.swap) := by
  let := f.normalSpaceFiberBundle hn hdim
  simp only [normalTubeChart_def, extChartAt_coe_symm]
  simp

omit [J.Boundaryless] in
/-- A point `x` of `X` is in the source of the chart of the tube at `z` if and only if it lies in
`W` and `Φ⁻¹ x` lies in the source of the extended chart of the total space at `0_z`. -/
theorem mem_normalTubeChart_source_iff {x : X} :
    letI := f.normalSpaceFiberBundle hn hdim
    x ∈ (normalTubeChart Φ z).source ↔
      ∃ hx : x ∈ W, Φ.symm ⟨x, hx⟩ ∈ (extChartAt (I.prod 𝓘(ℝ, P)) (zeroSection P _ z)).source := by
  let := f.normalSpaceFiberBundle hn hdim
  have hT : (tubeOPH Φ z).target = W := by ext; simp [tubeOPH]
  simp only [normalTubeChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    hT, mem_inter_iff, mem_preimage, Homeomorph.toOpenPartialHomeomorph_source, extChartAt_source,
    mem_univ, and_true]
  exact ⟨fun ⟨hx, h⟩ ↦ ⟨hx, tubeOPH_symm_apply Φ z hx ▸ h⟩,
    fun ⟨hx, h⟩ ↦ ⟨hx, (tubeOPH_symm_apply Φ z hx).symm ▸ h⟩⟩

omit [J.Boundaryless] in
/-- The target of the chart of the tube at `z` is the target of the extended chart of the total
space at `0_z`, factors exchanged. -/
theorem normalTubeChart_target :
    letI := f.normalSpaceFiberBundle hn hdim
    (normalTubeChart Φ z).target =
      Prod.swap ⁻¹'
        (extChartAt (I.prod 𝓘(ℝ, P)) (zeroSection P (fun x ↦ f.NormalSpace x hn) z)).target := by
  let := f.normalSpaceFiberBundle hn hdim
  ext y
  simp only [normalTubeChart_def, extChartAt_target, ModelWithCorners.range_eq_univ, inter_univ]
  simp

omit [J.Boundaryless] in
/-- On `W`, the chart of the tube at `z` reads `Φ⁻¹` in the extended chart of the total space at
`0_z`, with the two factors exchanged. -/
theorem normalTubeChart_apply {x : X} (hx : x ∈ W) :
    letI := f.normalSpaceFiberBundle hn hdim
    normalTubeChart Φ z x =
      (extChartAt (I.prod 𝓘(ℝ, P)) (zeroSection P _ z) (Φ.symm ⟨x, hx⟩)).swap := by
  let := f.normalSpaceFiberBundle hn hdim
  refine Prod.ext ?_ ?_ <;> simp [normalTubeChart, tubeOPH_symm_apply Φ z hx]

omit [J.Boundaryless] in
/-- On `W`, the chart of the tube at `z` is `Φ⁻¹`, followed by the preferred trivialization `e`
of the normal bundle at `z` and the chart of `Z` at `z` on the base, the normal coordinate
first. -/
theorem normalTubeChart_apply_eq {x : X} (hx : x ∈ W) :
    letI := f.normalSpaceFiberBundle hn hdim
    normalTubeChart Φ z x =
      ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z (Φ.symm ⟨x, hx⟩)).2,
        extChartAt I z (trivializationAt P (fun x ↦ f.NormalSpace x hn) z (Φ.symm ⟨x, hx⟩)).1) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [normalTubeChart_apply Φ z hx, FiberBundle.extChartAt]
  simp

omit [J.Boundaryless] in
/-- The source of the chart of a normalized tube at `z` contains `f z`. -/
theorem mem_normalTubeChart_source (hΦ : f.IsNormalizedTube hn hdim Φ) :
    f z ∈ (normalTubeChart Φ z).source := by
  let := f.normalSpaceFiberBundle hn hdim
  have hz := range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection (mem_range_self z)
  refine (mem_normalTubeChart_source_iff Φ z).2 ⟨hz, ?_⟩
  rw [symm_apply_eq_zeroSection_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection z hz]
  exact mem_extChartAt_source _

omit [J.Boundaryless] in
/-- The chart of a normalized tube at `z` sends `f z` to `(0, u)`, where `u` is the coordinate of
`z` in its chart. -/
theorem normalTubeChart_self (hΦ : f.IsNormalizedTube hn hdim Φ) :
    normalTubeChart Φ z (f z) = (0, extChartAt I z z) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  have hz := range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection (mem_range_self z)
  rw [normalTubeChart_apply_eq Φ z hz,
    symm_apply_eq_zeroSection_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection z hz,
    (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).zeroSection ℝ
      (mem_baseSet_trivializationAt P _ z)]

/-- The derivative of the chart of the tube at `z`, read in the chart of `X` at `f z`: the inverse
of the differential of `Φ` at `0_z`, the factors of `E × P` exchanged
(`normalTubeChartDeriv_symm_apply`, `hasFDerivAt_normalTubeChart`). -/
def normalTubeChartDeriv : V ≃L[ℝ] P × E :=
  letI := f.normalSpaceFiberBundle hn hdim
  ((ContinuousLinearEquiv.prodComm ℝ P E).trans
    ((Φ.isLocalDiffeomorph_subtypeVal_comp (zeroSection P _ z)).mfderivToContinuousLinearEquiv
      hn)).symm

omit [I.Boundaryless] [J.Boundaryless] in
/-- The inverse of the derivative of the chart of the tube at `z` sends `(w, u)` to the
differential of `Φ` at `0_z` applied to `(u, w)`. -/
theorem normalTubeChartDeriv_symm_apply (w : P) (u : E) :
    letI := f.normalSpaceFiberBundle hn hdim
    (normalTubeChartDeriv Φ z).symm (w, u) =
      mfderiv (I.prod 𝓘(ℝ, P)) J (fun p ↦ (Φ p : X)) (zeroSection P _ z) (u, w) := by
  (rfl)

omit [I.Boundaryless] [J.Boundaryless] in
/-- The inverse of the derivative of the chart of a normalized tube at `z` sends the tangent
vector `(0, u)` to the differential of `f` at `z` applied to `u`. -/
theorem normalTubeChartDeriv_symm_apply_zero_left (hΦ : f.IsNormalizedTube hn hdim Φ) (u : E) :
    (normalTubeChartDeriv Φ z).symm (0, u) = mfderiv I J f z u := by
  rw [normalTubeChartDeriv_symm_apply]
  exact mfderiv_zeroSection_apply_horizontal_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection
    z u

omit [I.Boundaryless] [J.Boundaryless] in
/-- The inverse of the derivative of the chart of a normalized tube at `z` sends `(w, u)` to a
vector whose normal class is the vector of `ν_z` with coordinate `w` in the preferred
trivialization at `z`. -/
theorem normalClassL_normalTubeChartDeriv_symm_apply (hΦ : f.IsNormalizedTube hn hdim Φ)
    (w : P) (u : E) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    f.normalClassL z hn ((normalTubeChartDeriv Φ z).symm (w, u)) =
      (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).symmL ℝ z w := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalTubeChartDeriv_symm_apply]
  exact hΦ.normalClassL_mfderiv_zeroSection z (u, w)

/-- **The derivative of a normalized tube in a chart.** Read in the chart of `X` at `f z`, the
chart `normalTubeChart Φ z` of a normalized tube has derivative `normalTubeChartDeriv Φ z` at
`f z`. -/
theorem hasFDerivAt_normalTubeChart (hΦ : f.IsNormalizedTube hn hdim Φ) :
    HasFDerivAt (normalTubeChart Φ z ∘ (extChartAt J (f z)).symm)
      (normalTubeChartDeriv Φ z : V →L[ℝ] P × E) (extChartAt J (f z) (f z)) := by
  let := f.normalSpaceFiberBundle hn hdim
  set p₀ := zeroSection P (fun x ↦ f.NormalSpace x hn) z
  set ψ := normalTubeChart Φ z
  have hz : (Φ p₀ : X) = f z := hΦ.apply_zeroSection z
  have hsrc := mem_normalTubeChart_source Φ z hΦ
  -- The tube read in the charts at `0_z` and `f z` has derivative its differential at `0_z`.
  have h1 : HasFDerivAt (writtenInExtChartAt (I.prod 𝓘(ℝ, P)) J p₀ (fun p ↦ (Φ p : X)))
      (((normalTubeChartDeriv Φ z).symm : P × E →L[ℝ] V).comp
        (ContinuousLinearEquiv.prodComm ℝ E P : E × P →L[ℝ] P × E))
      (extChartAt (I.prod 𝓘(ℝ, P)) p₀ p₀) := by
    have h :=
      ((Φ.isLocalDiffeomorph_subtypeVal_comp p₀).mdifferentiableAt (by simp)).hasMFDerivAt.2
    rw [ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ] at h
    convert h using 1
    refine ContinuousLinearMap.ext fun ⟨u, w⟩ ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk]
    rw [normalTubeChartDeriv_symm_apply]
    -- Mathlib's `HasMFDerivAt` casts the tangent spaces to the model spaces by
    -- `tangentSpaceCastModel`, which is the identity by definition and has no lemma saying so.
    rfl
  have hψ : ContinuousLinearEquiv.prodComm ℝ P E (ψ (f z)) =
      extChartAt (I.prod 𝓘(ℝ, P)) p₀ p₀ := by
    have hzW :=
      range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection (mem_range_self z)
    rw [normalTubeChart_apply Φ z hzW,
      symm_apply_eq_zeroSection_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection z hzW]
    simp [p₀]
  rw [← hψ] at h1
  have h2 : HasFDerivAt (writtenInExtChartAt (I.prod 𝓘(ℝ, P)) J p₀ (fun p ↦ (Φ p : X)) ∘
      (ContinuousLinearEquiv.prodComm ℝ P E)) ((normalTubeChartDeriv Φ z).symm : P × E →L[ℝ] V)
      (ψ (f z)) := by
    have := h1.comp (ψ (f z)) (ContinuousLinearEquiv.prodComm ℝ P E).hasFDerivAt
    convert this using 1
    exact ContinuousLinearMap.ext fun q ↦ by simp
  have h3 : (ψ ∘ (extChartAt J (f z)).symm) (extChartAt J (f z) (f z)) = ψ (f z) := by simp
  have key := HasFDerivAt.of_local_left_inverse
    ((ψ.continuousAt hsrc).comp_of_eq (continuousAt_extChartAt_symm (f z))
      (extChartAt_to_inv (f z))) (h3 ▸ h2) ?_
  · rwa [ContinuousLinearEquiv.symm_symm] at key
  filter_upwards [extChartAt_target_mem_nhds (I := J) (f z),
    (continuousAt_extChartAt_symm (I := J) (f z)).preimage_mem_nhds
      (by rw [extChartAt_to_inv]; exact ψ.open_source.mem_nhds hsrc)] with y hy hy'
  simp only [Function.comp_apply, writtenInExtChartAt, ContinuousLinearEquiv.prodComm_apply]
  rw [← normalTubeChart_symm_apply, ψ.left_inv hy', hz]
  exact (extChartAt J (f z)).right_inv hy

omit [I.Boundaryless] [J.Boundaryless] in
/-- **The orientation carried by a normalized tube.** Let `oX` and `oZ` orient `X` and `Z`, and
let `e` be the preferred trivialization of the normal bundle at `z`. The derivative of the chart
of a normalized tube at `z` carries the orientation of `X` at `f z` to the product of the
orientation of `Z` at `z` and the normal orientation `normalOrientation f hn hdim oX oZ` at `z`
read in `e`, tangent factor first, moved to `P × E` by the exchange of factors. -/
theorem map_orientationAt_normalTubeChartDeriv (hΦ : f.IsNormalizedTube hn hdim Φ) {m : ℕ}
    (oX : Manifold.Orientation J X (Fin (m + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin m)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    Orientation.map _ (normalTubeChartDeriv Φ z).toLinearEquiv (oX.orientationAt (f z)) =
      Orientation.map _ (LinearEquiv.prodComm ℝ (TangentSpace I z) P)
        (Orientation.prod (oZ.orientationAt z)
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation (Fin (finrank ℝ P))
            (mem_baseSet_trivializationAt P _ z) (normalOrientation f hn hdim oX oZ z))
          (by simpa using oZ.finrank_tangentSpace_eq z) rfl) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) z
  have hz : z ∈ e.baseSet := mem_baseSet_trivializationAt P _ z
  have hm : finrank ℝ (TangentSpace I z) = m := by simpa using oZ.finrank_tangentSpace_eq z
  have hr := f.finrank_normalSpace_eq hn hdim z
  -- The splitting `(u, v) ↦ D⁻¹ (e v, u)` of the tangent sequence at `z`.
  let L : (TangentSpace I z × f.NormalSpace z hn) ≃ₗ[ℝ] (TangentSpace I z × P) :=
    (LinearEquiv.refl ℝ (TangentSpace I z)).prodCongr (e.linearEquivAt ℝ z hz)
  let S : (TangentSpace I z × f.NormalSpace z hn) ≃ₗ[ℝ] TangentSpace J (f z) :=
    L.trans ((LinearEquiv.prodComm ℝ (TangentSpace I z) P).trans
      (normalTubeChartDeriv Φ z).symm.toLinearEquiv)
  have hS (u : TangentSpace I z) (v : f.NormalSpace z hn) :
      S (u, v) = (normalTubeChartDeriv Φ z).symm ((e.linearEquivAt ℝ z hz) v, u) := rfl
  have hX := (Orientation.ofExact_eq_map_prod (f.isImmersion.mfderiv_injective hn z)
    (f.exact_mfderiv_normalClass z hn) (f.normalClass_surjective z hn)
    (LinearEquiv.refl ℝ (TangentSpace I z)) S
    (fun u ↦ by
      rw [LinearEquiv.refl_apply, hS, map_zero]
      exact normalTubeChartDeriv_symm_apply_zero_left Φ z hΦ u)
    (fun ⟨u, v⟩ ↦ by
      have h := normalClassL_normalTubeChartDeriv_symm_apply Φ z hΦ (e.linearEquivAt ℝ z hz v) u
      have h2 : e.symmL ℝ z (e.linearEquivAt ℝ z hz v) = v := by
        rw [Trivialization.linearEquivAt_apply, Trivialization.symmL_apply,
          e.symm_apply_apply_mk hz]
        exact hz
      rw [hS]
      exact (normalClassL_apply _ _ _ _).symm.trans (h.trans h2))
    (oZ.orientationAt z) (normalOrientation f hn hdim oX oZ z) hm hr).symm.trans
    (ofExact_normalOrientation f hn hdim oX oZ z hm hr)
  have hSD : S.trans (normalTubeChartDeriv Φ z).toLinearEquiv =
      L.trans (LinearEquiv.prodComm ℝ (TangentSpace I z) P) :=
    LinearEquiv.ext fun _ ↦ (normalTubeChartDeriv Φ z).apply_symm_apply _
  rw [← hX]
  refine (Orientation.map_trans S (normalTubeChartDeriv Φ z).toLinearEquiv _).symm.trans ?_
  rw [hSD]
  refine (Orientation.map_trans L (LinearEquiv.prodComm ℝ (TangentSpace I z) P) _).trans ?_
  congr 1
  refine (Orientation.map_prod _ _ _ _ _ _).trans ?_
  simp only [Orientation.map_refl, Equiv.refl_apply, Trivialization.mapOrientation_apply, e]

end TauCeti.SmoothEmbedding

namespace TauCeti.SmoothEmbedding

variable {E V P X : Type} {H G Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [T2Space X] [ChartedSpace G X] [ChartedSpace V X] [IsManifold J ∞ X]
  {f : SmoothEmbedding I J ∞ Z X} {hn : (∞ : ℕ∞ω) ≠ 0}
  {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E} {W : TopologicalSpace.Opens X}

/-- **The local orientation of the ambient manifold through a normalized tube, as an
orientation.** Let `oX` and `oZ` orient `X` and `Z`, where `Z` has dimension `k` and `X`
dimension `d + 1`, and let `e` be the preferred trivialization of the normal bundle at `z`. The
chart `normalTubeChart Φ z` of a normalized tube `Φ`, translated so that `f z` goes to the
origin, carries the local orientation of `X` at `f z` to the local orientation of `P × E`
selected by the product of the orientation of `Z` at `z` and the normal orientation
`normalOrientation f hn hdim oX oZ` at `z` read in `e`, tangent factor first, moved to `P × E` by
the exchange of factors. This holds for any dimension of the normal fibre, zero included. -/
theorem localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_eq_localOrientation
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z)
    (hΦ : f.IsNormalizedTube hn hdim Φ) {k d : ℕ} (hE : finrank ℝ E = k)
    (hV : finrank ℝ V = d + 1) (hk : k + finrank ℝ P = d + 1)
    (oX : Manifold.Orientation J X (Fin (k + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin k)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (normalTubeChart Φ z).source ↦ normalTubeChart Φ z x - normalTubeChart Φ z (f z),
          (normalTubeChart Φ z).continuousOn.domRestrict.sub continuous_const⟩ :
          C((normalTubeChart Φ z).source, P × E))
        (S := {⟨f z, mem_normalTubeChart_source Φ z hΦ⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((normalTubeChart Φ z).injOn x.property
            (mem_normalTubeChart_source Φ z hΦ) (sub_eq_zero.1 hx)))
        (d + 1)
        (((normalTubeChart Φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv
          ⟨f z, mem_normalTubeChart_source Φ z hΦ⟩ (d + 1)).symm
          ((oX.reindex (finCongr hk)).toHomologicalOrientation hV (f z))).val =
      ((Orientation.reindex ℝ (P × E) (finCongr hk)
        (Orientation.map _ (LinearEquiv.prodComm ℝ E P)
          (Orientation.prod (oZ.orientationAt z)
            ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation
              (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
              (normalOrientation f hn hdim oX oZ z)) hE rfl))).localOrientation
        (by rw [Module.finrank_prod, hE]; omega)).val := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have hx := mem_normalTubeChart_source Φ z hΦ
  have hF : finrank ℝ (P × E) = d + 1 := by rw [Module.finrank_prod, hE]; omega
  set ψ := normalTubeChart Φ z
  set D := normalTubeChartDeriv Φ z
  -- Read `ψ` in a Euclidean space through a linear identification `L`.
  have hEuc : finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1 := finrank_euclideanSpace_fin
  let L : (P × E) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (hF.trans hEuc.symm)
  let ψ' := ψ.transHomeomorph L.toHomeomorph
  have hx' : f z ∈ ψ'.source := by rwa [OpenPartialHomeomorph.transHomeomorph_source]
  have hD' : HasFDerivAt (ψ' ∘ (extChartAt J (f z)).symm) ((D.trans L : V ≃L[ℝ] _) : V →L[ℝ] _)
      (extChartAt J (f z) (f z)) := by
    rw [OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      ← ContinuousLinearEquiv.comp_coe, Function.comp_assoc]
    exact L.hasFDerivAt.comp _ (hasFDerivAt_normalTubeChart Φ z hΦ)
  have h₁ := Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart
    hV (oX.reindex (finCongr hk)) hEuc ψ' hx' (D.trans L) hD' rfl
  have h₂ := ψ'.localHomologyMap_chart_localOrientationOfOrientedChart hx' L.symm
    (((oX.reindex (finCongr hk)).orientationAt (f z)).map (Fin (d + 1)) (D.trans L).toLinearEquiv)
    hEuc hF (by
      rintro x hx
      exact Subtype.ext (ψ'.injOn x.property hx'
        (sub_eq_zero.1 (L.symm.map_eq_zero_iff.1 (by simpa using hx)))))
  rw [← h₁] at h₂
  refine Eq.trans ?_ (h₂.trans ?_)
  · congr 3
    refine ContinuousMap.ext fun x ↦ ?_
    -- The sources of `ψ` and `ψ'` are the same set only after unfolding `transHomeomorph`, so
    -- `rw` does not match the application lemmas, nor `ContinuousMap.coe_mk` on the left.
    erw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, ψ'.sourceRestrict_apply]
    simp [ψ', ψ]
    rfl
  · have hω (o : Orientation ℝ V (Fin (d + 1))) :
        (o.map (Fin (d + 1)) (D.trans L).toLinearEquiv).map (Fin (d + 1)) L.symm.toLinearEquiv =
          o.map _ D.toLinearEquiv := by
      rw [ContinuousLinearEquiv.trans_toLinearEquiv, Orientation.map_trans]
      exact Orientation.map_symm_map L.toLinearEquiv _
    have hO := map_orientationAt_normalTubeChartDeriv Φ z hΦ oX oZ
    -- The tangent space of `X` at `f z` is `V`, and that of `Z` at `z` is `E`, only by
    -- definition, so `rw` does not match these lemmas.
    erw [hω]
    rw [Manifold.Orientation.orientationAt_reindex]
    erw [Orientation.map_reindex, hO]
    -- The two exchanges of factors agree only after unfolding `TangentSpace I z` to `E`.
    rfl

/-- **The local orientation of the ambient manifold through a normalized tube.** Let `oX` and
`oZ` orient `X` and `Z`, where `Z` has dimension `m + 1`, the normal fibre `P` dimension
`r + 1` and `X` dimension `d + 1`, and let `e` be the preferred trivialization of the normal
bundle at `z`. The chart `normalTubeChart Φ z` of a normalized tube `Φ`, translated so that `f z`
goes to the origin, carries the local orientation of `X` at `f z` to the cross product
`TauCeti.LocalOrientation.cross`, normal factor first, of the local orientation of `P` selected by
the normal orientation `normalOrientation f hn hdim oX oZ` at `z` read in `e` with the local
orientation of `E` selected by the orientation of `Z` at `z`. No sign appears. -/
theorem localHomologyMap_sub_normalTubeChart_toHomologicalOrientation
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z)
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m r d : ℕ} (hE : finrank ℝ E = m + 1)
    (hP : finrank ℝ P = r + 1) (hV : finrank ℝ V = d + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (normalTubeChart Φ z).source ↦ normalTubeChart Φ z x - normalTubeChart Φ z (f z),
          (normalTubeChart Φ z).continuousOn.domRestrict.sub continuous_const⟩ :
          C((normalTubeChart Φ z).source, P × E))
        (S := {⟨f z, mem_normalTubeChart_source Φ z hΦ⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((normalTubeChart Φ z).injOn x.property
            (mem_normalTubeChart_source Φ z hΦ) (sub_eq_zero.1 hx)))
        (d + 1)
        (((normalTubeChart Φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv
          ⟨f z, mem_normalTubeChart_source Φ z hΦ⟩ (d + 1)).symm
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z))).val =
      (LocalOrientation.cross hP hE (by omega)
        ((Orientation.reindex ℝ P (finCongr hP)
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation (Fin (finrank ℝ P))
            (mem_baseSet_trivializationAt P _ z)
            (normalOrientation f hn hdim oX oZ z))).localOrientation hP)
        (Orientation.localOrientation (F := E) (oZ.orientationAt z) hE)).val := by
  have hd : r + 1 + (m + 1) = d + 1 := by omega
  have hd' : m + 1 + (r + 1) = d + 1 := by omega
  have hdX : m + 1 + finrank ℝ P = d + 1 := by omega
  have hF : finrank ℝ (P × E) = d + 1 := by rw [Module.finrank_prod, hP, hE]; omega
  -- The linear algebra, for orientations `o` of `E` and `p` of `P`.
  have hlin (o : Orientation ℝ E (Fin (m + 1))) (p : Orientation ℝ P (Fin (finrank ℝ P))) :
      Orientation.reindex ℝ (P × E) (finCongr hdX)
          (Orientation.map _ (LinearEquiv.prodComm ℝ E P) (o.prod p hE rfl)) =
        (Orientation.reindex ℝ (E × P) (finCongr hd')
          (o.prod (Orientation.reindex ℝ P (finCongr hP) p) hE hP)).map (Fin (d + 1))
          (ContinuousLinearEquiv.prodComm ℝ E P).toLinearEquiv := by
    rw [Orientation.prod_reindex_finCongr_right, ← Orientation.reindex_trans,
      Orientation.map_reindex, ContinuousLinearEquiv.prodComm_toLinearEquiv]
    congr 1
  have hcross (o : Orientation ℝ E (Fin (m + 1))) (p : Orientation ℝ P (Fin (r + 1))) :
      (((Orientation.reindex ℝ (E × P) (finCongr hd') (o.prod p hE hP)).map (Fin (d + 1))
        (ContinuousLinearEquiv.prodComm ℝ E P).toLinearEquiv).localOrientation hF) =
        LocalOrientation.cross hP hE hd (p.localOrientation hP) (o.localOrientation hE) := by
    rw [Orientation.localOrientation_map _ _ (finrank_prod_eq_succ hE hP hd'),
      ← LocalOrientation.prod_localOrientation,
      ← LocalOrientation.cross_eq_map_prodComm_prod hP hE hd hd']
  refine (localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_eq_localOrientation Φ z hΦ
    hE hV hdX oX oZ).trans ?_
  -- The tangent space of `Z` at `z` is `E` only by definition, so `rw` does not match `hlin`.
  erw [hlin]
  exact congrArg Subtype.val (hcross _ _)

open Classical in
/-- **The local orientation of the ambient manifold through a normalized tube, when the normal
fibre is a point.** Let `oX` and `oZ` orient `X` and `Z`, where `Z` and `X` have dimension
`m + 1` and the normal fibre `P` dimension zero, and let `e` be the preferred trivialization of
the normal bundle at `z`. The chart `normalTubeChart Φ z` of a normalized tube `Φ`, translated so
that `f z` goes to the origin, carries the local orientation of `X` at `f z` to the cross product
`SymplecticGeometry.localHomologyCross` of the class of the origin of `P` with the local
orientation of `E` selected by the orientation of `Z` at `z`, if the normal orientation
`normalOrientation f hn hdim oX oZ` at `z` read in `e` is the positive orientation of `P`, and to
its negative otherwise. -/
theorem localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_eq_zero
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z)
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m : ℕ} (hE : finrank ℝ E = m + 1)
    (hP : finrank ℝ P = 0) (hV : finrank ℝ V = m + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (normalTubeChart Φ z).source ↦ normalTubeChart Φ z x - normalTubeChart Φ z (f z),
          (normalTubeChart Φ z).continuousOn.domRestrict.sub continuous_const⟩ :
          C((normalTubeChart Φ z).source, P × E))
        (S := {⟨f z, mem_normalTubeChart_source Φ z hΦ⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((normalTubeChart Φ z).injOn x.property
            (mem_normalTubeChart_source Φ z hΦ) (sub_eq_zero.1 hx)))
        (m + 1)
        (((normalTubeChart Φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv
          ⟨f z, mem_normalTubeChart_source Φ z hΦ⟩ (m + 1)).symm
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z))).val =
      if Orientation.reindex ℝ P (finCongr hP)
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation (Fin (finrank ℝ P))
            (mem_baseSet_trivializationAt P _ z) (normalOrientation f hn hdim oX oZ z)) =
          positiveOrientation then
        (SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 (m + 1) (m + 1) (zero_add _)).hom
          ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
            (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ
            (Orientation.localOrientation (F := E) (oZ.orientationAt z) hE).val)
      else
        -(SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 (m + 1) (m + 1) (zero_add _)).hom
          ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
            (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ
            (Orientation.localOrientation (F := E) (oZ.orientationAt z) hE).val) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have hdX : m + 1 + finrank ℝ P = m + 1 := by omega
  -- The linear algebra, for orientations `o` of `E` and `p` of `P`.
  have hlin (o : Orientation ℝ E (Fin (m + 1))) (p : Orientation ℝ P (Fin (finrank ℝ P))) :
      Orientation.reindex ℝ (P × E) (finCongr hdX)
          (Orientation.map _ (LinearEquiv.prodComm ℝ E P) (o.prod p hE rfl)) =
        (o.prod (Orientation.reindex ℝ P (finCongr hP) p) hE hP).map (Fin (m + 1))
          (LinearEquiv.prodComm ℝ E P) := by
    rw [Orientation.prod_reindex_finCongr_right, Orientation.map_reindex]
  refine (localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_eq_localOrientation Φ z hΦ
    hE hV hdX oX oZ).trans ?_
  -- The tangent space of `Z` at `z` is `E` only by definition, so `rw` does not match these.
  erw [Orientation.localHomologyCross_localOrientationOfZeroDimChart_tmul_localOrientation hP hE
    (Orientation.reindex ℝ P (finCongr hP)
      ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation (Fin (finrank ℝ P))
        (mem_baseSet_trivializationAt P _ z) (normalOrientation f hn hdim oX oZ z)))
    (oZ.orientationAt z), hlin]
  split_ifs
  · rfl
  · rw [neg_neg]

end TauCeti.SmoothEmbedding

namespace TauCeti.SmoothEmbedding

variable {E V P Z X : Type} {H G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [T2Space X] [ChartedSpace G X] [ChartedSpace V X] [IsManifold J ∞ X]
  {f : SmoothEmbedding I J ∞ Z X} {hn : (∞ : ℕ∞ω) ≠ 0}
  {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E} {W : TopologicalSpace.Opens X}

variable (Φ : letI := f.normalSpaceFiberBundle hn hdim
  TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z) {S : Set E}

omit [T2Space X] [J.Boundaryless] [ChartedSpace V X] in
/-- Let `c` be the chart of `Z` at `z` read in `E` and translated so that `z` goes to `0`, and
`S` a set of its target that `c⁻¹` carries into the base set of the preferred trivialization `e`
of the normal bundle at `z`. The tube `Φ` carries the image of `P × S` under the chart
`Bundle.Trivialization.localChart` of `e` and `c` into the source of `normalTubeChart Φ z`. -/
theorem tube_localChart_mem_normalTubeChart_source
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (y : (univ ×ˢ S : Set (P × E))) :
    letI := f.normalSpaceFiberBundle hn hdim
    (Φ ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).localChart
      ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))) S y) : X) ∈
        (normalTubeChart Φ z).source := by
  let := f.normalSpaceFiberBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) z
  set c := (chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))
  obtain ⟨⟨w, q⟩, -, hq⟩ := y
  have hqe : c.symm q ∈ e.baseSet := hSe hq
  refine (mem_normalTubeChart_source_iff Φ z).2 ⟨(Φ _).property, ?_⟩
  rw [Diffeomorph.symm_apply_apply, Trivialization.localChart_def]
  simp only [extChartAt_source, FiberBundle.chartedSpace_chartAt, zeroSection_proj]
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨e.toOpenPartialHomeomorph.map_target (e.mk_mem_target.2 hqe), ?_⟩
  rw [mem_preimage, Trivialization.coe_coe, e.apply_symm_apply (e.mk_mem_target.2 hqe)]
  exact ⟨by simpa [c] using c.map_target (hSc hq), mem_univ _⟩

omit [T2Space X] [J.Boundaryless] [ChartedSpace V X] in
/-- In the setting of `tube_localChart_mem_normalTubeChart_source`, the chart
`normalTubeChart Φ z` reads the image of `(w, q)` under the tube after the chart of the total
space as `(w, q + u)`, where `u` is the coordinate of `z` in its chart: up to this translation,
the chart of the tube undoes the tube after the chart of the total space. -/
theorem normalTubeChart_apply_tube_localChart
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (y : (univ ×ˢ S : Set (P × E))) :
    letI := f.normalSpaceFiberBundle hn hdim
    normalTubeChart Φ z (Φ ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).localChart
      ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))) S y)) =
        (y.val.1, y.val.2 + extChartAt I z z) := by
  let := f.normalSpaceFiberBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) z
  set c := (chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))
  have hq : y.val.2 ∈ S := y.property.2
  have hqt : I.symm (y.val.2 + I (chartAt H z z)) ∈ (chartAt H z).target := by
    simpa [c] using hSc hq
  have hcq : c.symm y.val.2 = (chartAt H z).symm (I.symm (y.val.2 + I (chartAt H z z))) := by
    simp [c]
  rw [normalTubeChart_apply_eq Φ z (Φ _).property, Diffeomorph.symm_apply_apply,
    Trivialization.localChart_def, e.apply_symm_apply (e.mk_mem_target.2 (hSe hq)), hcq,
    extChartAt_coe]
  ext
  · rfl
  · dsimp only [Function.comp_apply]
    rw [(chartAt H z).right_inv hqt, I.right_inv (I.range_eq_univ ▸ mem_univ _)]

/-- **A normalized tube undoes its chart on local orientations.** Let `c` be the chart of `Z` at
`z` read in `E` and translated so that `z` goes to `0`, and `S` an open set of its target
containing `0` that `c⁻¹` carries into the base set of the preferred trivialization `e` of the
normal bundle at `z`. For a local orientation `o` of `X` at `f z`, read it in the chart
`normalTubeChart Φ z`, translated so that `f z` goes to the origin, carry the class to the total
space at `0_z` by the isomorphism `Bundle.Trivialization.localChartLocalHomologyIso` of `e` and
`c`, and push it to `X` by the tube `Φ`: the result is `o`. -/
theorem localHomologyMap_localChartLocalHomologyIso_hom_localHomologyMap_sub_normalTubeChart
    (hΦ : f.IsNormalizedTube hn hdim Φ) {n : ℕ} (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) (o : LocalOrientation X (f z) n) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
          C(TotalSpace P (fun x ↦ f.NormalSpace x hn), X))
        (S := {zeroSection P _ z}) (T := {f z})
        (by
          rintro p hp
          exact Φ.injective (Subtype.ext (hp.trans (hΦ.apply_zeroSection z).symm)))
        n
        ((Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
          (by simp) (by simp) h0 n).hom
          (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
            (⟨fun x : (normalTubeChart Φ z).source ↦
                normalTubeChart Φ z x - normalTubeChart Φ z (f z),
              (normalTubeChart Φ z).continuousOn.domRestrict.sub continuous_const⟩ :
              C((normalTubeChart Φ z).source, P × E))
            (S := {⟨f z, mem_normalTubeChart_source Φ z hΦ⟩}) (T := {0})
            (by
              rintro x hx
              exact Subtype.ext ((normalTubeChart Φ z).injOn x.property
                (mem_normalTubeChart_source Φ z hΦ) (sub_eq_zero.1 hx)))
            n
            (((normalTubeChart Φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv
              ⟨f z, mem_normalTubeChart_source Φ z hΦ⟩ n).symm o).val)) =
      o.val := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) := Φ.toHomeomorph.isEmbedding.t1Space
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) z
  set c := (chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))
  set ψ := normalTubeChart Φ z
  have hb : z ∈ c.source := by simp [c]
  have hcb : c z = 0 := by simp [c]
  have hx := mem_normalTubeChart_source Φ z hΦ
  have hι := Trivialization.isOpenEmbedding_localChart (e := e) hS hSc hSe
  -- The tube after the chart of the total space at `0_z` is the inverse of `ψ`, translated.
  have hψ (y : (univ ×ˢ S : Set (P × E))) : ψ (Φ (e.localChart c S y)) - ψ (f z) = y.val := by
    rw [normalTubeChart_apply_tube_localChart Φ z hSc hSe, normalTubeChart_self Φ z hΦ,
      Prod.mk_sub_mk, sub_zero, add_sub_cancel_right]
  let κ : C((univ ×ˢ S : Set (P × E)), ψ.source) :=
    ⟨fun y ↦ ⟨Φ (e.localChart c S y), tube_localChart_mem_normalTubeChart_source Φ z hSc hSe y⟩,
      ((continuous_subtypeVal.comp Φ.continuous).comp hι.continuous).subtype_mk _⟩
  have hpt : e.localChart c S ⁻¹' {zeroSection P _ z} ⊆
      {⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩} := fun y hy ↦
    hι.injective (hy.trans (Trivialization.localChart_zero hSe hb hcb h0).symm)
  -- `ψ`, translated so that `f z` goes to the origin, is an open embedding of its source.
  let x₀ : ψ.source := ⟨f z, hx⟩
  let τ : C(ψ.source, P × E) :=
    ⟨fun x ↦ ψ x - ψ (f z), ψ.continuousOn.domRestrict.sub continuous_const⟩
  have hτ0 : τ ⁻¹' {0} = {x₀} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    refine ⟨fun h ↦ Subtype.ext (ψ.injOn x.property hx (sub_eq_zero.1 h)), ?_⟩
    rintro rfl
    exact sub_self _
  have hτ : Topology.IsOpenEmbedding τ :=
    (Homeomorph.subRight (ψ (f z))).isOpenEmbedding.comp ψ.isOpenEmbedding_restrict
  have : CategoryTheory.IsIso
      (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) τ hτ0.subset n) :=
    isIso_localHomologyMap _ τ hτ hτ0 isClosed_singleton
      (singleton_subset_iff.2 ⟨x₀, sub_self _⟩) n
  have hinj : Function.Injective
      (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) τ hτ0.subset n) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hκ0 : κ ⁻¹' {x₀} ⊆ {⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩} := fun y hy ↦ by
    have h := hψ y
    rw [show (Φ (e.localChart c S y) : X) = f z from congrArg Subtype.val hy, sub_self] at h
    exact Subtype.ext h.symm
  -- `κ`, then `τ`, is the inclusion of `P × S`.
  have hτκ : τ.comp κ = ⟨Subtype.val, continuous_subtypeVal⟩ :=
    ContinuousMap.ext fun y ↦ hψ y
  have hκs : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) κ hκ0 n
      ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
        ((isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × E))
        ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ n).inv
        (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) τ hτ0.subset n
          ((ψ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv x₀ n).symm o).val)) =
      ((ψ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv x₀ n).symm o).val := by
    refine hinj ?_
    rw [← CategoryTheory.ConcreteCategory.comp_apply, localHomologyMap_comp,
      localHomologyMap_congr _ hτκ, ← localHomologyIsoOfIsOpenEmbedding_hom]
    exact CategoryTheory.Iso.inv_hom_id_apply _ _
  rw [Trivialization.localChartLocalHomologyIso_hom _ _ _ _ _ _ _ hpt,
    CategoryTheory.ConcreteCategory.comp_apply,
    ← CategoryTheory.ConcreteCategory.comp_apply, localHomologyMap_comp]
  -- The tube after the chart of the total space is `κ` followed by the inclusion of the source.
  have hval : ((⟨Subtype.val, ψ.open_source.isOpenEmbedding_subtypeVal.continuous⟩ :
      C(ψ.source, X)) ⁻¹' {f z}) ⊆ {x₀} := fun x hx ↦ Subtype.ext hx
  have hcomp : (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
        C(TotalSpace P (fun x ↦ f.NormalSpace x hn), X)).comp
        ⟨e.localChart c S, hι.continuous⟩ =
      (⟨Subtype.val, ψ.open_source.isOpenEmbedding_subtypeVal.continuous⟩ :
        C(ψ.source, X)).comp κ :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [localHomologyMap_congr _ hcomp, ← localHomologyMap_comp _ κ _ hκ0 hval,
    CategoryTheory.ConcreteCategory.comp_apply, hκs]
  exact ψ.open_source.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm x₀ _
    hval

/-- **The local orientation of the ambient manifold through a normalized tube, from the total
space.** In the setting of `localHomologyMap_sub_normalTubeChart_toHomologicalOrientation`, let
`c` be the chart of `Z` at `z` read in `E` and translated so that `z` goes to `0`, and `S` an
open set of its target containing `0` that `c⁻¹` carries into the base set of the preferred
trivialization `e` of the normal bundle at `z`. The isomorphism
`Bundle.Trivialization.localChartLocalHomologyIso` of `e` and `c` carries the cross product,
normal factor first, of the local orientation of `P` selected by the normal orientation at `z`
read in `e` with the local orientation of `E` selected by the orientation of `Z` at `z`, to a
local class of the total space at `0_z`; the tube `Φ` carries that class to the local
orientation of `X` at `f z`. No sign appears. -/
theorem localHomologyMap_localChartLocalHomologyIso_hom_cross
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m r d : ℕ} (hE : finrank ℝ E = m + 1)
    (hP : finrank ℝ P = r + 1) (hV : finrank ℝ V = d + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
          C(TotalSpace P (fun x ↦ f.NormalSpace x hn), X))
        (S := {zeroSection P _ z}) (T := {f z})
        (by
          rintro p hp
          exact Φ.injective (Subtype.ext (hp.trans (hΦ.apply_zeroSection z).symm)))
        (d + 1)
        ((Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
          (by simp) (by simp) h0 (d + 1)).hom
          (LocalOrientation.cross hP hE (by omega)
            ((Orientation.reindex ℝ P (finCongr hP)
              ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation
                (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
                (normalOrientation f hn hdim oX oZ z))).localOrientation hP)
            (Orientation.localOrientation (F := E) (oZ.orientationAt z) hE)).val) =
      ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z)).val := by
  rw [← localHomologyMap_sub_normalTubeChart_toHomologicalOrientation Φ z hΦ hE hP hV oX oZ]
  exact localHomologyMap_localChartLocalHomologyIso_hom_localHomologyMap_sub_normalTubeChart Φ z hΦ
    hS hSc hSe h0 _

open Classical in
/-- **The local orientation of the ambient manifold through a normalized tube, from the total
space, when the normal fibre is a point.** In the setting of
`localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_eq_zero`, let `c` be the
chart of `Z` at `z` read in `E` and translated so that `z` goes to `0`, and `S` an open set of its
target containing `0` that `c⁻¹` carries into the base set of the preferred trivialization `e`
of the normal bundle at `z`. The isomorphism `Bundle.Trivialization.localChartLocalHomologyIso`
of `e` and `c` carries the cross product `SymplecticGeometry.localHomologyCross` of the class of
the origin of `P` with the local orientation of `E` selected by the orientation of `Z` at `z` to
a local class of the total space at `0_z`. The tube `Φ` carries that class to the local
orientation of `X` at `f z` if the normal orientation at `z` read in `e` is the positive
orientation of `P`, and to its negative otherwise. -/
theorem localHomologyMap_localChartLocalHomologyIso_hom_localHomologyCross_of_finrank_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m : ℕ} (hE : finrank ℝ E = m + 1)
    (hP : finrank ℝ P = 0) (hV : finrank ℝ V = m + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
          C(TotalSpace P (fun x ↦ f.NormalSpace x hn), X))
        (S := {zeroSection P _ z}) (T := {f z})
        (by
          rintro p hp
          exact Φ.injective (Subtype.ext (hp.trans (hΦ.apply_zeroSection z).symm)))
        (m + 1)
        ((Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
          (by simp) (by simp) h0 (m + 1)).hom
          ((SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 (m + 1) (m + 1)
            (zero_add _)).hom
            ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
              (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ
              (Orientation.localOrientation (F := E) (oZ.orientationAt z) hE).val))) =
      if Orientation.reindex ℝ P (finCongr hP)
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation (Fin (finrank ℝ P))
            (mem_baseSet_trivializationAt P _ z) (normalOrientation f hn hdim oX oZ z)) =
          positiveOrientation then
        ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z)).val
      else
        -((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z)).val := by
  have h := localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_eq_zero Φ z hΦ
    hE hP hV oX oZ
  have hG := localHomologyMap_localChartLocalHomologyIso_hom_localHomologyMap_sub_normalTubeChart
    Φ z hΦ hS hSc hSe h0 ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z))
  split_ifs with hc
  · rw [if_pos hc] at h
    rwa [← h]
  · rw [if_neg hc] at h
    rw [← neg_eq_iff_eq_neg.2 h, map_neg, map_neg, hG]

end TauCeti.SmoothEmbedding

end
