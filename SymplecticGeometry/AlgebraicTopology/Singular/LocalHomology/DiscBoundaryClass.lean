/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Circle
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import SymplecticGeometry.Analysis.Complex.RadialProjection
public import SymplecticGeometry.Analysis.Normed.Module.Ball.Collar
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# The closed unit disc and the local orientation of `ℂ`

Let `D = closedBall (0 : ℂ) 1` be the closed unit disc. Its interior, the open unit disc, is an
open subset of `ℂ` and carries the orientation `TauCeti.complexHomologicalOrientation`; its
boundary is the unit circle. This file puts `D` in the setting of Tau Ceti's relative fundamental
class (`TauCeti.HomologicalOrientation.fundamentalClassRel`), and gives the two facts from which
`SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryDegree` computes the sign of
the boundary class of `D` (`SymplecticGeometry.singularHomologyOneIso_map_boundaryClass_closedBall`
there).

The hypotheses of `fundamentalClassRel` hold for the closed unit ball of any real normed space:
the inclusion of the open unit ball into the closed one is an open embedding
(`Topology.IsOpenEmbedding.inclusion`), its range is the complement of the unit sphere
(`Metric.range_inclusion_ball_eq_compl`), and the unit sphere is collared
(`Metric.isCollared_inclusion_sphere_closedBall`); both are proved in
`SymplecticGeometry.Analysis.Normed.Module.Ball.Collar`. The boundary is read in `Circle` by
`SymplecticGeometry.closedBallComplToCircle`.

The inclusion of `D` into `ℂ` is a map of pairs `(D, S¹) ⟶ (ℂ, ℂ ∖ {0})`, and it carries
`[D, S¹]` to the local orientation of `ℂ` at `0`: restrict to the centre of the disc, where
`[D, S¹]` is the local orientation of the open disc, and that is the pull-back of the local
orientation of `ℂ` (`TauCeti.comap_subtypeVal_complexHomologicalOrientation`). The local
orientation of `ℂ` at `0` is the one of the identity chart
(`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`), so the connecting morphism of
`(ℂ, ℂ ∖ {0})` followed by radial projection (`Circle.radialProjection`) sends it to the generator
of the unit circle selected by `Complex.orientation`
(`OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`),
which is the generator of `Circle.singularHomologyOneIso`
(`Circle.singularHomologyOneIso_inv_eq_complexOrientation`).

## Main results

* `TauCeti.complexHomologicalOrientation_apply_zero`: the local orientation of `ℂ` at the origin is
  the one selected by `Complex.orientation`.
* `SymplecticGeometry.localHomologyMap_fundamentalClassRel_closedBall`: the inclusion of the
  closed unit disc into `ℂ` sends its relative fundamental class to that local orientation.
* `SymplecticGeometry.singularHomologyOneIso_singularHomologyδ_localOrientation_complexOrientation`:
  the connecting morphism of `(ℂ, ℂ ∖ {0})`, followed by radial projection onto `Circle`, sends the
  local orientation selected by `Complex.orientation` to `1` in `H₁(Circle; ℤ) ≅ ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: local
  orientations and the fundamental class of a compact manifold with boundary.
-/

public section

noncomputable section

open CategoryTheory Limits Metric TauCeti AlgebraicTopology

/-- The local orientation of `ℂ`, as a complex manifold, at the origin is the one selected by
`Complex.orientation`. -/
theorem TauCeti.complexHomologicalOrientation_apply_zero :
    complexHomologicalOrientation ℂ 0 =
      Complex.orientation.localOrientation Complex.finrank_real_complex := by
  have h0 : (0 : ℂ) ∈ (OpenPartialHomeomorph.refl ℂ).source := by simp
  -- The preferred chart of `ℂ` is the identity.
  have hrefl :
      OpenPartialHomeomorph.refl ℂ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 ℂ := by
    simpa using IsManifold.chart_mem_maximalAtlas (I := modelWithCornersSelf ℂ ℂ) (n := 1) (0 : ℂ)
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas hrefl h0,
    Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl]

namespace SymplecticGeometry

open Set Topology

section Disc

open TopologicalSpace

/-- The open unit disc of `ℂ`, as an open set. -/
private abbrev openDisc : Opens ℂ := ⟨ball (0 : ℂ) 1, isOpen_ball⟩

/-- The inclusion of the open unit disc into the closed unit disc. -/
private abbrev ι : openDisc → closedBall (0 : ℂ) 1 := inclusion ball_subset_closedBall

private lemma isOpenEmbedding_ι : IsOpenEmbedding ι :=
  .inclusion _ (isOpen_ball.preimage continuous_subtypeVal)

/-- The complement of the open unit disc in the closed unit disc, read in `Circle`. -/
def closedBallComplToCircle :
    C(↥((range (inclusion (ball_subset_closedBall : ball (0 : ℂ) 1 ⊆ closedBall 0 1)))ᶜ),
      Circle) :=
  (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)).comp
    ⟨fun w ↦ ⟨w.val, by
      have h : w.val ∈ range (inclusion (sphere_subset_closedBall : sphere (0 : ℂ) 1 ⊆ _)) := by
        rw [← compl_compl (range _), ← range_inclusion_ball_eq_compl]
        exact w.property
      obtain ⟨z, hz⟩ := h
      rw [← hz]
      exact z.property⟩, by fun_prop⟩

@[simp]
theorem coe_closedBallComplToCircle_apply
    (w : ↥((range (inclusion (ball_subset_closedBall : ball (0 : ℂ) 1 ⊆ closedBall 0 1)))ᶜ)) :
    (closedBallComplToCircle w : ℂ) = w.val := by
  simp [closedBallComplToCircle]

/-- The integer coefficients of Tau Ceti's local homology. -/
private abbrev R : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ULift.{0} ℤ)

/-- The inclusion of the closed unit disc into `ℂ`. -/
private abbrev discVal : C(closedBall (0 : ℂ) 1, ℂ) := ⟨Subtype.val, continuous_subtypeVal⟩

private abbrev discCenter : openDisc := ⟨0, mem_ball_self one_pos⟩

private lemma preimage_discVal_subset : discVal ⁻¹' {0} ⊆ {ι discCenter} :=
  fun _ hw ↦ Subtype.ext hw

/-- **The fundamental class of the closed unit disc in `ℂ`.** Orient the open unit disc as an
open subset of `ℂ` (`TauCeti.complexHomologicalOrientation`). The inclusion of the closed unit
disc into `ℂ`, a map of pairs from the disc relative to its boundary circle to `(ℂ, ℂ ∖ {0})`,
sends the relative fundamental class of the disc to the local orientation of `ℂ` at the origin
selected by `Complex.orientation`. -/
theorem localHomologyMap_fundamentalClassRel_closedBall
    (h : (⟨Subtype.val, continuous_subtypeVal⟩ : C(closedBall (0 : ℂ) 1, ℂ)) ⁻¹' {0} ⊆
      range (inclusion (ball_subset_closedBall : ball (0 : ℂ) 1 ⊆ closedBall 0 1))) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨Subtype.val, continuous_subtypeVal⟩ : C(closedBall (0 : ℂ) 1, ℂ)) h 2
        ((complexHomologicalOrientation
            (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)).fundamentalClassRel
          Complex.finrank_real_complex
          (.inclusion _ (isOpen_ball.preimage continuous_subtypeVal))
          (range_inclusion_ball_eq_compl 0 1) isCollared_inclusion_sphere_closedBall) =
      (Complex.orientation.localOrientation Complex.finrank_real_complex).val := by
  have hval : IsOpenEmbedding (Subtype.val : openDisc → ℂ) :=
    openDisc.isOpen.isOpenEmbedding_subtypeVal
  have h1 : localHomologyMap R discVal h 2 =
      localHomologyRestriction R (singleton_subset_iff.2 (mem_range_self discCenter)) 2 ≫
        localHomologyMap R discVal preimage_discVal_subset 2 :=
    (localHomologyRestriction_comp_localHomologyMap R discVal _ preimage_discVal_subset 2).symm
  rw [h1, ConcreteCategory.comp_apply,
    HomologicalOrientation.localHomologyRestriction_fundamentalClassRel,
    localHomologyIsoOfIsOpenEmbedding_hom, ← ConcreteCategory.comp_apply, localHomologyMap_comp,
    ← complexHomologicalOrientation_apply_zero,
    ← comap_subtypeVal_complexHomologicalOrientation hval, HomologicalOrientation.comap_apply,
    IsOpenEmbedding.coe_localOrientationEquiv_symm]
  rw [localHomologyMap_congr R (j₁ := discVal.comp ⟨ι, isOpenEmbedding_ι.continuous⟩)
    (j₂ := ⟨Subtype.val, hval.continuous⟩) rfl]
  exact localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap_apply R hval discCenter _ 2 _

end Disc

/-- **The local orientation of `ℂ` generates `H₁(S¹)`.** The connecting morphism of the pair
`(ℂ, ℂ ∖ {0})`, followed by radial projection `z ↦ z / |z|` onto `Circle`
(`Circle.radialProjection`), sends the local orientation of `ℂ` at the origin selected by
`Complex.orientation` to the class that is `1` in `H₁(Circle; ℤ) ≅ ℤ`
(`Circle.singularHomologyOneIso`). -/
theorem singularHomologyOneIso_singularHomologyδ_localOrientation_complexOrientation :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom Circle.radialProjection)
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 1 rfl
          (Complex.orientation.localOrientation Complex.finrank_real_complex).val)) = 1 := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  set Q := TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))
  set H := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R
  set e := TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))
  set c := TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : ℂ)).toFun
  set x := (Complex.orientation.localOrientation Complex.finrank_real_complex).val
  have key : H.map (c ≫ e) (Q.singularHomologyδ R 2 1 rfl x) =
      (Circle.singularHomologyOneIso R).inv 1 := calc
    _ = H.map e (H.map c ((reducedSingularHomologyι R 1).app _
          (Q.reducedSingularHomologyδ R 1 x))) :=
        (ConcreteCategory.congr_hom (H.map_comp c e) _).trans
          ((ConcreteCategory.comp_apply _ _ _).trans (congrArg _ (congrArg _
            (ConcreteCategory.congr_hom (TopPair.reducedSingularHomologyδ_comp_ι Q R 1) x).symm)))
    _ = H.map e ((reducedSingularHomologyι R 1).app _
          ((reducedSingularHomologyFunctor R 1).map c (Q.reducedSingularHomologyδ R 1 x))) :=
        congrArg _ (ConcreteCategory.congr_hom ((reducedSingularHomologyι R 1).naturality c) _).symm
    _ = H.map e ((reducedSingularHomologyι R 1).app _
          ((reducedSingularHomologySphereIsoOfOrientation R Complex.orientation
            Complex.finrank_real_complex).inv 1)) := by
        have h :=
          OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl
            (p := (0 : ℂ)) (by simp) Complex.orientation Complex.finrank_real_complex
        rw [← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl] at h
        exact congrArg _ (congrArg _ h)
    _ = (Circle.singularHomologyOneIso R).inv 1 := by
        rw [Circle.singularHomologyOneIso_inv_eq_complexOrientation, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply]
  rw [Circle.radialProjection_def, TopCat.ofHom_comp, key, Iso.inv_hom_id_apply]

end SymplecticGeometry
