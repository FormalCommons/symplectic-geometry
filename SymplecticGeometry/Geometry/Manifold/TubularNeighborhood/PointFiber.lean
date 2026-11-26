/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.LocalOrientation

/-!
# The local orientation through a normalized tube when the normal fibre is a point

Let `f : Z → X` be a smooth embedding with normal bundle of model fibre `P`, and `Φ` a normalized
tube of `f`, as in `SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.LocalOrientation`.
This file treats the case where `P` has dimension zero and `Z`, hence `X`, has positive dimension
`m + 1`. The cross product `TauCeti.LocalOrientation.cross` of the local orientations of the
normal fibre and of `Z`, which describes the positive-dimensional case, is replaced by the cross
product `SymplecticGeometry.localHomologyCross` of the class of the origin of `P` with the local
orientation of `E` selected by the orientation of `Z` at `z`. The normal orientation at `z`, read
in the preferred trivialization of the normal bundle, is an orientation of `P` indexed by `Fin 0`,
so it is the positive orientation or its negative, and it gives the sign.

The chart form
(`localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_fiber_eq_zero`)
follows from `localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_eq_localOrientation`
and the library's unit law
`Orientation.localHomologyCross_localOrientationOfZeroDimChart_tmul_localOrientation`. The form
read from the total space of the normal bundle
(`localHomologyMap_localChartLocalHomologyIso_hom_localHomologyCross_of_finrank_fiber_eq_zero`)
then follows by
`TauCeti.SmoothEmbedding.localHomologyMap_localChartLocalHomologyIso_hom_of_normalTubeChart`.

## Main results

* `localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_fiber_eq_zero`:
  the chart `normalTubeChart Φ z`, translated so that `f z` goes to the origin, carries the local
  orientation of `X` at `f z` to the cross product of the class of the origin of `P` with the
  local orientation of `Z`, with the sign of the normal orientation.
* `localHomologyMap_localChartLocalHomologyIso_hom_localHomologyCross_of_finrank_fiber_eq_zero`:
  the tube carries that cross product, read in the total space at `0_z` through
  `Bundle.Trivialization.localChartLocalHomologyIso`, to the local orientation of `X` at `f z`,
  with the same sign.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations).
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

section ChartForm

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
theorem localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_fiber_eq_zero
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z)
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
          ((trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).mapOrientation
            (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
            (normalOrientation f hn hdim oX oZ z)) =
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
      ((trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).mapOrientation
        (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
        (normalOrientation f hn hdim oX oZ z)))
    (oZ.orientationAt z), hlin]
  split_ifs
  · rfl
  · rw [neg_neg]

end ChartForm

section TotalSpaceForm

/- `localHomologyMap_localChartLocalHomologyIso_hom_of_normalTubeChart` takes `Z : Type`. -/
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
  TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) (z : Z)
  {S : Set E}

open Classical in
/-- **The local orientation of the ambient manifold through a normalized tube, from the total
space, when the normal fibre is a point.** In the setting of
`localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_fiber_eq_zero`, let
`c` be the chart of `Z` at `z` read in `E` and translated so that `z` goes to `0`, and `S` an
open set of its target containing `0` that `c⁻¹` carries into the base set of the preferred
trivialization `e` of the normal bundle at `z`. The isomorphism
`Bundle.Trivialization.localChartLocalHomologyIso` of `e` and `c` carries the cross product
`SymplecticGeometry.localHomologyCross` of the class of the origin of `P` with the local
orientation of `E` selected by the orientation of `Z` at `z` to a local class of the total space
at `0_z`. The tube `Φ` carries that class to the local orientation of `X` at `f z` if the normal
orientation at `z` read in `e` is the positive orientation of `P`, and to its negative
otherwise. -/
theorem
    localHomologyMap_localChartLocalHomologyIso_hom_localHomologyCross_of_finrank_fiber_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m : ℕ} (hE : finrank ℝ E = m + 1)
    (hP : finrank ℝ P = 0) (hV : finrank ℝ V = m + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.isImmersion.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
          C(TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn), X))
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
          ((trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).mapOrientation
            (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
            (normalOrientation f hn hdim oX oZ z)) =
          positiveOrientation then
        ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z)).val
      else
        -((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV (f z)).val := by
  have h := localHomologyMap_sub_normalTubeChart_toHomologicalOrientation_of_finrank_fiber_eq_zero
    Φ z hΦ hE hP hV oX oZ
  split_ifs with hc
  · rw [ite_eq_left hc] at h
    exact localHomologyMap_localChartLocalHomologyIso_hom_of_normalTubeChart Φ z hΦ
      hS hSc hSe h0 _ _ h
  · rw [ite_eq_right hc] at h
    have hG := localHomologyMap_localChartLocalHomologyIso_hom_of_normalTubeChart Φ z hΦ
      hS hSc hSe h0 _ _ h
    rw [map_neg, map_neg] at hG
    rw [← hG, neg_neg]

end TotalSpaceForm

end TauCeti.SmoothEmbedding

end
