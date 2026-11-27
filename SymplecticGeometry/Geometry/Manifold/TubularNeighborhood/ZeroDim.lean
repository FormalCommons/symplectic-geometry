/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.LocalOrientation
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.ZeroDim.Basic
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Point
import SymplecticGeometry.LinearAlgebra.Orientation.Basic
import SymplecticGeometry.LinearAlgebra.Orientation.Prod

/-!
# The local orientation through a normalized tube in dimension zero

Let `f : Z → X` be a smooth embedding with normal bundle of model fibre `P`, and `Φ` a normalized
tube of `f`, as in `SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.LocalOrientation`.
When `Z` and the normal fibre both have dimension zero, so does `X`. This file gives, in that
case, the statement that
`TauCeti.SmoothEmbedding.localHomologyMap_localChartLocalHomologyIso_hom_cross` gives in positive
dimensions: the tube, read through the chart `Bundle.Trivialization.localChartLocalHomologyIso`
of the total space at `0_z`, carries the cross product of a local class of `P` and one of `E` to
the local orientation of `X` at `f z`
(`localHomologyMap_localChartLocalHomologyIso_hom_cross_of_finrank_eq_zero`).

Here every class involved is the class of a point with a sign. The cross product of the classes of
two points is the class of the pair
(`SymplecticGeometry.localHomologyCross_tmul_localHomologyPointClass` and Tau Ceti's
`TauCeti.localHomologyPointClass_map`), and the chart of the total space and the tube carry the
class of a point to that of its image. The local orientation of `X` at `f z` is Tau Ceti's
`TauCeti.Manifold.Orientation.toHomologicalOrientationOfZeroDim`, the class of `f z` with the
sign of the orientation of `X` there. That sign is the product of the other two: in dimension
zero, `TauCeti.SmoothEmbedding.map_orientationAt_normalTubeChartDeriv` says that the orientation
of `X` is positive exactly when the orientation of `Z` and the normal orientation have the same
sign (`Orientation.prod_eq_positiveOrientation_iff`).

## Main results

* `localHomologyMap_localChartLocalHomologyIso_hom_cross_of_finrank_eq_zero`:
  the tube carries the cross product of the signed classes of the origins of `P` and `E` to the
  local orientation of `X` at `f z`.

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

open SymplecticGeometry

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

omit [T2Space X] [I.Boundaryless] [J.Boundaryless] [ChartedSpace V X] in
/-- In dimension zero, the orientation of `X` at `f z` is positive exactly when the normal
orientation at `z` read in the preferred trivialization and the orientation of `Z` at `z` have the
same sign. -/
private theorem orientationAt_reindex_eq_positiveOrientation_iff
    (hΦ : f.IsNormalizedTube hn hdim Φ) (hP : finrank ℝ P = 0)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (oX.reindex (finCongr ((zero_add _).trans hP))).orientationAt (f z) = positiveOrientation ↔
      (Orientation.reindex ℝ P (finCongr hP)
          ((trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).mapOrientation
              (Fin (finrank ℝ P))
            (mem_baseSet_trivializationAt P _ z) (normalOrientation f hn hdim oX oZ z)) =
          positiveOrientation ↔ oZ.orientationAt z = positiveOrientation) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : IsEmpty (Fin (finrank ℝ P)) := ⟨fun i ↦ (finCongr hP i).elim0⟩
  have : IsEmpty (Fin (0 + finrank ℝ P)) := ⟨fun i ↦ (finCongr ((zero_add _).trans hP) i).elim0⟩
  rw [Manifold.Orientation.orientationAt_reindex, Orientation.reindex_eq_positiveOrientation_iff]
  refine (Orientation.map_eq_positiveOrientation_iff
    (normalTubeChartDeriv Φ z).toLinearEquiv _).symm.trans ?_
  rw [map_orientationAt_normalTubeChartDeriv Φ z hΦ oX oZ]
  refine (Orientation.map_eq_positiveOrientation_iff _ _).trans ?_
  rw [Orientation.prod_eq_positiveOrientation_iff, Orientation.reindex_eq_positiveOrientation_iff]
  exact Iff.comm

omit [J.Boundaryless] in
open Classical in
/-- **The local orientation of the ambient manifold through a normalized tube, in dimension
zero.** In the setting of `localHomologyMap_localChartLocalHomologyIso_hom_cross`, let the normal
fibre `P` and the model `E` of `Z` have dimension zero, so that `X` has dimension zero too. Take
the class of the origin in `H₀(P, P ∖ {0}; ℤ)`, with the sign of the normal orientation at `z`
read in the preferred trivialization `e`, and the class of the origin in `H₀(E, E ∖ {0}; ℤ)`,
with the sign of the orientation of `Z` at `z`. The isomorphism
`Bundle.Trivialization.localChartLocalHomologyIso` carries their cross product to a class of the
total space at `0_z`, and the tube `Φ` carries that class to the zero-dimensional local
orientation `toHomologicalOrientationOfZeroDim` of `X` at `f z`. -/
theorem localHomologyMap_localChartLocalHomologyIso_hom_cross_of_finrank_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) (hE : finrank ℝ E = 0) (hP : finrank ℝ P = 0)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) (hS : IsOpen S)
    (hSc : S ⊆ (centeredExtChartAt I z).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo (centeredExtChartAt I z).symm S
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
        0
        ((Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
          (mem_centeredExtChartAt_source I z) (centeredExtChartAt_self I z) h0 0).hom
          ((SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 0 0 rfl).hom
            ((if Orientation.reindex ℝ P (finCongr hP)
                  ((trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z).mapOrientation
                    (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
                    (normalOrientation f hn hdim oX oZ z)) = positiveOrientation then
                (localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
                  (OpenPartialHomeomorph.mem_refl_source _) hP).val
              else -(localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
                  (OpenPartialHomeomorph.mem_refl_source _) hP).val) ⊗ₜ
              (if oZ.orientationAt z = positiveOrientation then
                (localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
                  (OpenPartialHomeomorph.mem_refl_source _) hE).val
              else -(localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
                  (OpenPartialHomeomorph.mem_refl_source _) hE).val)))) =
      ((oX.reindex (finCongr ((zero_add _).trans hP))).toHomologicalOrientationOfZeroDim
        (f z)).val := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T1Space (TotalSpace P fun x ↦ f.isImmersion.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
  set e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) z
  set c := centeredExtChartAt I z
  have hb : z ∈ c.source := mem_centeredExtChartAt_source I z
  have hcb : c z = 0 := centeredExtChartAt_self I z
  -- The cross product of the two point classes is carried to the point class of `f z`.
  have key : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
          C(TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn), X))
        (S := {zeroSection P _ z}) (T := {f z})
        (by
          rintro p hp
          exact Φ.injective (Subtype.ext (hp.trans (hΦ.apply_zeroSection z).symm)))
        0
        ((Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
          hb hcb h0 0).hom
          ((SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 0 0 rfl).hom
            (localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) {(0 : P)} 0 1 ⊗ₜ
              localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) {(0 : E)} 0 1))) =
      localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) {f z} (f z) 1 := by
    have h1 : (SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 0 0 rfl).hom
        (localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) {(0 : P)} 0 1 ⊗ₜ
          localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) {(0 : E)} 0 1) =
        localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) {((0, 0) : P × E)} (0, 0) 1 :=
      (SymplecticGeometry.localHomologyCross_tmul_localHomologyPointClass _ _ 0 _).trans
        (localHomologyPointClass_map_apply _ _ _ _ _)
    rw [h1, Trivialization.localHomologyPointClass_comp_localChartLocalHomologyIso_hom_apply]
    exact (localHomologyPointClass_map_apply _ _ _ _ _).trans
      (congrArg (fun y ↦ localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) {f z} y 1)
        (hΦ.apply_zeroSection z))
  rw [Manifold.Orientation.toHomologicalOrientationOfZeroDim_apply,
    Manifold.Orientation.localOrientationOfZeroDim_coe,
    orientationAt_reindex_eq_positiveOrientation_iff Φ z hΦ hP oX oZ]
  simp only [localOrientationOfZeroDimChart_coe]
  split_ifs <;> first
    | (exfalso; tauto)
    | simp only [TensorProduct.neg_tmul, TensorProduct.tmul_neg, map_neg, neg_neg, key]

end TauCeti.SmoothEmbedding

end
