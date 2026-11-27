/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.LocalClass
public import SymplecticGeometry.Topology.VectorBundle.Thom.LocalCap
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.CategoryTheory.Monoidal.Preadditive
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.ZeroDimChart
import SymplecticGeometry.Topology.VectorBundle.Thom.FundamentalClass

/-!
# The cap product of the Thom class with the tube's fundamental class

Let `f : Z → X` be a smooth embedding of a compact manifold `Z` into a manifold `X`, with normal
bundle `π : ν → Z`, orientations `oX` of `X` and `oZ` of `Z`, and let `Φ` be a normalized tube of
`f`. Write `u` for the canonical Thom class of the induced normal orientation
`normalOrientation f hn hdim oX oZ`, and `μ_Φ ∈ Hₙ(ν, ν ∖ 0)` for the fundamental class of the
tube (`TauCeti.SmoothEmbedding.tubeFundamentalClass`), for the homological orientation of `oX`.
This file proves

`π_*(u ⌢ μ_Φ) = [Z]` in `H_m(Z; ℤ)`, `m = dim Z`,

in each case of the dimensions: `Z` of positive dimension or a set of points (with the
zero-dimensional homological orientation `toHomologicalOrientationOfZeroDim`), and normal rank
positive or zero. Together with
`TauCeti.SmoothEmbedding.exists_isNormalizedTube_singularCap_dualClassOf_fundamentalClass`
(`DualClass/Cap.lean`), this computes the cap product of the dual class of `Z` with the
fundamental class of `X`.

The proof is local on `Z`. By the library's criterion
`TauCeti.HomologicalOrientation.map_singularCap_eq_fundamentalClass`, a class of `H_m(Z)` is the
fundamental class once its image in `H_m(Z, Z ∖ z)` is the local orientation at each `z`; for a
push-forward along `π` of a cap product, that image is computed from the local class of `μ_Φ` at
`0_z`. Read in the centred chart of `Z` at `z` (which detects classes of local homology at `z`,
`OpenPartialHomeomorph.injective_localHomologyMap_sourceRestrict`), this gives the pointwise
criterion
`HomologicalOrientation.map_proj_singularCap_eq_fundamentalClass_of_centeredExtChartAt`
(`Topology/VectorBundle/Thom/FundamentalClass.lean`), and its form
`HomologicalOrientation.map_proj_singularCap_eq_fundamentalClass_of_nhds` checks it on an open
contractible set `S ∋ 0` of that chart whose image lies over a trivializing set. On such an `S`:

* `DualClass/LocalClass.lean` reads the local class of `μ_Φ` in the chart of the total space as a
  cross product, normal factor first, of the local orientation of the normal fibre with that of
  `Z` at `z`;
* `Topology/VectorBundle/Thom/LocalCap.lean` evaluates the cap product of such a class with the
  canonical Thom class: it is the factor of `Z`. In rank zero the sign of the normal orientation
  enters both the local class and the cap product, and the two signs cancel;
* `OrientedChart.lean` and `Orientation/ZeroDimChart.lean` identify that factor with the local
  orientation of `oZ` at `z`, read in the same chart.

The normal orientation is indexed by `Fin (finrank ℝ P)`. The local cap computations take an
orientation indexed by any `Fin r` together with an equation `r = k + 1` or `r = 0`, so they
apply to it directly.

## Main results

* `TauCeti.SmoothEmbedding.map_proj_singularCap_tubeFundamentalClass`,
  `…_of_finrank_fiber_eq_zero`, `…_of_finrank_eq_zero` and
  `…_of_finrank_eq_zero_of_finrank_fiber_eq_zero`: `π_*(u ⌢ μ_Φ) = [Z]` when `Z` and the normal
  fibre have positive dimension, when the normal fibre is a point, when `Z` has dimension zero,
  and when both are.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the Poincaré
  dual of a closed submanifold through the Thom class of its normal bundle).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products, local orientations and the fundamental class, Lemma 3.27).
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory Module Set AlgebraicTopology
open scoped Manifold ContDiff

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry VectorBundleOrientation

variable {H G : Type*} {E V P Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z] [ChartedSpace E Z] [CompactSpace Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X] [T2Space X] [ChartedSpace V X]
  {f : SmoothEmbedding I J ∞ Z X} {hn : (∞ : ℕ∞ω) ≠ 0}
  {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E} {W : TopologicalSpace.Opens X}
  (Φ : letI := f.normalSpaceFiberBundle hn hdim
    TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
  (hK : IsCompact (Subtype.val ⁻¹' range f : Set W))

/-- **The projection carries the cap product of the Thom class with the tube's class to the
fundamental class of the submanifold.** Let `f : Z → X` be a smooth embedding of a compact
manifold `Z` of dimension `m + 1`, with normal fibre `P` of dimension `r + 1`, orientations `oX`
of `X` and `oZ` of `Z`, and a normalized tube `Φ`. The push-forward along `π : ν → Z` of the
cap product of the canonical Thom class of the normal orientation
`normalOrientation f hn hdim oX oZ` with the fundamental class `tubeFundamentalClass` of `Φ`, for
the homological orientation of `oX`, is the fundamental class of `Z` for the homological
orientation of `oZ`. -/
theorem map_proj_singularCap_tubeFundamentalClass
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m r d : ℕ}
    (hE : finrank ℝ E = m + 1) (hP : finrank ℝ P = r + 1) (hV : finrank ℝ V = d + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T2Space Z := f.isEmbedding.t2Space
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨π P _, FiberBundle.continuous_proj P _⟩)
      (((thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCap ℤ (ρ_ _).inv
          (ρ_ _).hom (finrank ℝ P) (m + 1) (d + 1) (by omega)
          ((normalOrientation f hn hdim oX oZ).canonicalThomClass rfl)).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV) hV hK)) =
      (oZ.toHomologicalOrientation hE).fundamentalClass hE := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T2Space Z := f.isEmbedding.t2Space
  have : T1Space (TotalSpace P fun x ↦ f.isImmersion.NormalSpace x hn) :=
    Φ.toHomeomorph.isEmbedding.t1Space
  refine HomologicalOrientation.map_proj_singularCap_eq_fundamentalClass_of_nhds (I := I) _ hE
    _ _ _ (fun z ↦ (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).open_baseSet
      |>.mem_nhds (mem_baseSet_trivializationAt P _ z)) fun z S _ hS hSc hSe h0 ↦ ?_
  rw [Manifold.Orientation.localHomologyMap_centeredExtChartAt_toHomologicalOrientation hE oZ z]
  exact localHomologyMap_singularRelativeCap_canonicalThomClass_of_localOrientation
    _ rfl hP (trivializationAt P _ z) hS hSc hSe
    (mem_centeredExtChartAt_source I z) (centeredExtChartAt_self I z) h0
    _ _ _
    (localChartLocalHomologyIso_inv_tubeFundamentalClass Φ hK z hΦ hE hP hV oX oZ
      hS hSc hSe h0)

/-- **The projection carries the cap product of the Thom class with the tube's class to the
fundamental class of the submanifold**, in codimension zero. In the setting of
`map_proj_singularCap_tubeFundamentalClass`, with the normal fibre `P` of dimension zero, the
push-forward along `π` of the cap product of the canonical Thom class of the normal orientation
with the fundamental class of `Φ` is the fundamental class of `Z`. -/
theorem map_proj_singularCap_tubeFundamentalClass_of_finrank_fiber_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m : ℕ}
    (hE : finrank ℝ E = m + 1) (hP : finrank ℝ P = 0) (hV : finrank ℝ V = m + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T2Space Z := f.isEmbedding.t2Space
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨π P _, FiberBundle.continuous_proj P _⟩)
      (((thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCap ℤ (ρ_ _).inv
          (ρ_ _).hom (finrank ℝ P) (m + 1) (m + 1) (by omega)
          ((normalOrientation f hn hdim oX oZ).canonicalThomClass rfl)).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV) hV hK)) =
      (oZ.toHomologicalOrientation hE).fundamentalClass hE := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T2Space Z := f.isEmbedding.t2Space
  have : T1Space (TotalSpace P fun x ↦ f.isImmersion.NormalSpace x hn) :=
    Φ.toHomeomorph.isEmbedding.t1Space
  refine HomologicalOrientation.map_proj_singularCap_eq_fundamentalClass_of_nhds (I := I) _ hE
    _ _ _ (fun z ↦ (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).open_baseSet
      |>.mem_nhds (mem_baseSet_trivializationAt P _ z)) fun z S _ hS hSc hSe h0 ↦ ?_
  rw [Manifold.Orientation.localHomologyMap_centeredExtChartAt_toHomologicalOrientation hE oZ z]
  exact localHomologyMap_singularRelativeCap_canonicalThomClass_of_finrank_eq_zero
    _ rfl hP (trivializationAt P _ z) hS hSc hSe
    (mem_centeredExtChartAt_source I z) (centeredExtChartAt_self I z) h0
    _ _ _
    (localChartLocalHomologyIso_inv_tubeFundamentalClass_of_finrank_fiber_eq_zero Φ hK z hΦ hE hP
      hV oX oZ hS hSc hSe h0)

/-- **The projection carries the cap product of the Thom class with the tube's class to the
fundamental class of the submanifold**, for `Z` of dimension zero. In the setting of
`map_proj_singularCap_tubeFundamentalClass`, with `Z` of dimension zero and the normal fibre `P`
of dimension `r + 1`, the push-forward along `π` of the cap product of the canonical Thom class
of the normal orientation with the fundamental class of `Φ` is the fundamental class of the
zero-dimensional homological orientation `toHomologicalOrientationOfZeroDim` of `oZ`. -/
theorem map_proj_singularCap_tubeFundamentalClass_of_finrank_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) {r : ℕ}
    (hE : finrank ℝ E = 0) (hP : finrank ℝ P = r + 1) (hV : finrank ℝ V = r + 1)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T2Space Z := f.isEmbedding.t2Space
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨π P _, FiberBundle.continuous_proj P _⟩)
      (((thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCap ℤ (ρ_ _).inv
          (ρ_ _).hom (finrank ℝ P) 0 (r + 1) (by omega)
          ((normalOrientation f hn hdim oX oZ).canonicalThomClass rfl)).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV) hV hK)) =
      oZ.toHomologicalOrientationOfZeroDim.fundamentalClass hE := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T2Space Z := f.isEmbedding.t2Space
  have : T1Space (TotalSpace P fun x ↦ f.isImmersion.NormalSpace x hn) :=
    Φ.toHomeomorph.isEmbedding.t1Space
  refine HomologicalOrientation.map_proj_singularCap_eq_fundamentalClass_of_nhds (I := I) _ hE
    _ _ _ (fun z ↦ (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).open_baseSet
      |>.mem_nhds (mem_baseSet_trivializationAt P _ z)) fun z S _ hS hSc hSe h0 ↦ ?_
  rw [Manifold.Orientation.localHomologyMap_sourceRestrict_toHomologicalOrientationOfZeroDim oZ
      (centeredExtChartAt I z) (mem_centeredExtChartAt_source I z) (centeredExtChartAt_self I z)]
  exact localHomologyMap_singularRelativeCap_canonicalThomClass_of_localOrientation
    _ rfl hP (trivializationAt P _ z) hS hSc hSe
    (mem_centeredExtChartAt_source I z) (centeredExtChartAt_self I z) h0
    _ _ _
    (localChartLocalHomologyIso_inv_tubeFundamentalClass_of_finrank_eq_zero Φ hK z hΦ hE hP hV oX
      oZ hS hSc hSe h0)

omit [J.Boundaryless] in
/-- **The projection carries the cap product of the Thom class with the tube's class to the
fundamental class of the submanifold**, in dimension zero. In the setting of
`map_proj_singularCap_tubeFundamentalClass`, with `Z` and the normal fibre `P` both of dimension
zero, so that `X` has dimension zero too, the push-forward along `π` of the cap product of the
canonical Thom class of the normal orientation with the fundamental class of `Φ`, for the
zero-dimensional homological orientation of `oX`, is the fundamental class of the
zero-dimensional homological orientation of `oZ`. -/
theorem
    map_proj_singularCap_tubeFundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) (hE : finrank ℝ E = 0) (hP : finrank ℝ P = 0)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T2Space Z := f.isEmbedding.t2Space
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨π P _, FiberBundle.continuous_proj P _⟩)
      (((thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCap ℤ (ρ_ _).inv
          (ρ_ _).hom (finrank ℝ P) 0 0 (by omega)
          ((normalOrientation f hn hdim oX oZ).canonicalThomClass rfl)).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr ((zero_add _).trans hP))).toHomologicalOrientationOfZeroDim)
          (by omega) hK)) =
      oZ.toHomologicalOrientationOfZeroDim.fundamentalClass hE := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T2Space Z := f.isEmbedding.t2Space
  have : T1Space (TotalSpace P fun x ↦ f.isImmersion.NormalSpace x hn) :=
    Φ.toHomeomorph.isEmbedding.t1Space
  refine HomologicalOrientation.map_proj_singularCap_eq_fundamentalClass_of_nhds (I := I) _ hE
    _ _ _ (fun z ↦ (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).open_baseSet
      |>.mem_nhds (mem_baseSet_trivializationAt P _ z)) fun z S _ hS hSc hSe h0 ↦ ?_
  rw [Manifold.Orientation.localHomologyMap_sourceRestrict_toHomologicalOrientationOfZeroDim oZ
      (centeredExtChartAt I z) (mem_centeredExtChartAt_source I z) (centeredExtChartAt_self I z)]
  exact localHomologyMap_singularRelativeCap_canonicalThomClass_of_finrank_eq_zero
    _ rfl hP (trivializationAt P _ z) hS hSc hSe
    (mem_centeredExtChartAt_source I z) (centeredExtChartAt_self I z) h0
    _ _ _
    (localChartLocalHomologyIso_inv_tubeFundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero
      Φ hK z hΦ hE hP oX oZ hS hSc hSe h0)

end TauCeti.SmoothEmbedding

end
