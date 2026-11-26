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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection

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
(`normalTubeChartDeriv_symm_apply_zero_left`), and the normal class of the image of `(w, u)` is
the vector of `ν_z` with coordinate `w` in `e`
(`normalClassL_normalTubeChartDeriv_symm_apply`, from
`TauCeti.SmoothEmbedding.IsNormalizedTube.normalClassL_mfderiv_zeroSection`).

Hence this derivative carries the orientation of `X` at `f z` to the product of the orientation
of `Z` at `z` and the normal orientation `normalOrientation f hn hdim oX oZ` at `z` read in `e`,
tangent factor first, moved to `P × E` by the exchange of factors
(`map_orientationAt_normalTubeChartDeriv`). This is the characterization
`TauCeti.SmoothEmbedding.ofExact_normalOrientation` of the normal orientation, through Tau Ceti's
splitting lemma `Orientation.ofExact_eq_map_prod` and `Orientation.map_prod`. No sign appears, in
any dimension and codimension, including zero.

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

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Manifold Topology ContDiff

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

omit [I.Boundaryless] [J.Boundaryless] in
/-- A normalized tube takes the value `f z` at `0_z`, so `f z ∈ W`. -/
private theorem mem_of_isNormalizedTube (hΦ : f.IsNormalizedTube hn hdim Φ) : f z ∈ W := by
  let := f.normalSpaceFiberBundle hn hdim
  exact hΦ.apply_zeroSection z ▸ (Φ (zeroSection P _ z)).property

omit [I.Boundaryless] [J.Boundaryless] in
private theorem symm_eq_zeroSection (hΦ : f.IsNormalizedTube hn hdim Φ) :
    letI := f.normalSpaceFiberBundle hn hdim
    Φ.symm ⟨f z, mem_of_isNormalizedTube Φ z hΦ⟩ = zeroSection P _ z := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [← Φ.symm_apply_apply (zeroSection P _ z)]
  exact congrArg Φ.symm (Subtype.ext (hΦ.apply_zeroSection z).symm)

omit [J.Boundaryless] in
/-- The source of the chart of a normalized tube at `z` contains `f z`. -/
theorem mem_normalTubeChart_source (hΦ : f.IsNormalizedTube hn hdim Φ) :
    f z ∈ (normalTubeChart Φ z).source := by
  let := f.normalSpaceFiberBundle hn hdim
  refine (mem_normalTubeChart_source_iff Φ z).2 ⟨mem_of_isNormalizedTube Φ z hΦ, ?_⟩
  rw [symm_eq_zeroSection Φ z hΦ]
  exact mem_extChartAt_source _

omit [J.Boundaryless] in
/-- The chart of a normalized tube at `z` sends `f z` to `(0, u)`, where `u` is the coordinate of
`z` in its chart. -/
theorem normalTubeChart_self (hΦ : f.IsNormalizedTube hn hdim Φ) :
    normalTubeChart Φ z (f z) = (0, extChartAt I z z) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalTubeChart_apply_eq Φ z (mem_of_isNormalizedTube Φ z hΦ), symm_eq_zeroSection Φ z hΦ,
    (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).zeroSection ℝ
      (mem_baseSet_trivializationAt P _ z)]

omit [I.Boundaryless] [J.Boundaryless] in
/-- The tube is a local diffeomorphism into `X` at each point. -/
private theorem isLocalDiffeomorphAt_tube
    (p : letI := f.normalSpaceFiberBundle hn hdim; TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ (fun p ↦ (Φ p : X)) p :=
  letI := f.normalSpaceFiberBundle hn hdim
  (Φ.isLocalDiffeomorph _).comp (hg := isLocalDiffeomorph_subtype_val (U := W) _)

/-- The derivative of the chart of the tube at `z`, read in the chart of `X` at `f z`: the inverse
of the differential of `Φ` at `0_z`, the factors of `E × P` exchanged
(`normalTubeChartDeriv_symm_apply`, `hasFDerivAt_normalTubeChart`). -/
def normalTubeChartDeriv : V ≃L[ℝ] P × E :=
  letI := f.normalSpaceFiberBundle hn hdim
  ((ContinuousLinearEquiv.prodComm ℝ P E).trans
    ((isLocalDiffeomorphAt_tube Φ (zeroSection P _ z)).mfderivToContinuousLinearEquiv hn)).symm

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
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalTubeChartDeriv_symm_apply]
  have hb := Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl
    ((isLocalDiffeomorphAt_tube Φ (zeroSection P _ z)).mdifferentiableAt (by simp))
    (g := f) (Filter.Eventually.of_forall hΦ.apply_zeroSection) u
  rw [Bundle.zeroSectionTangentEquiv_symm_apply, map_zero] at hb
  exact hb

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
    have h := ((isLocalDiffeomorphAt_tube Φ p₀).mdifferentiableAt (by simp)).hasMFDerivAt.2
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
    rw [normalTubeChart_apply Φ z (mem_of_isNormalizedTube Φ z hΦ), symm_eq_zeroSection Φ z hΦ]
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

end
