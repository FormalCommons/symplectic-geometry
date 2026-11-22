/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Circle
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryClass
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
public import SymplecticGeometry.Analysis.Normed.Module.Ball.Collar
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# The boundary class of the closed unit disc

Let `D = closedBall (0 : ℂ) 1` be the closed unit disc. Its interior, the open unit disc, is an
open subset of `ℂ` and carries the orientation `TauCeti.complexHomologicalOrientation`; its
boundary is the unit circle. This file puts `D` in the setting of Tau Ceti's relative fundamental
class (`TauCeti.HomologicalOrientation.fundamentalClassRel`) and computes the sign of its boundary
class `∂[D, S¹] ∈ H₁(S¹; ℤ)` (`TauCeti.HomologicalOrientation.boundaryClass`), the image of
`[D, S¹]` under the connecting morphism of the pair.

The hypotheses of `fundamentalClassRel` hold for the closed unit ball of any real normed space:
the inclusion of the open unit ball into the closed one is an open embedding
(`Topology.IsOpenEmbedding.inclusion`), its range is the complement of the unit sphere
(`Metric.range_inclusion_ball_eq_compl`), and the unit sphere is collared
(`Metric.isCollared_inclusion_sphere_closedBall`); both are proved in
`SymplecticGeometry.Analysis.Normed.Module.Ball.Collar`.

The sign is `+1`: read in `Circle` (`SymplecticGeometry.closedBallComplToCircle`) and in `ℤ`
through `Circle.singularHomologyOneIso`, the boundary class is `1`
(`SymplecticGeometry.singularHomologyOneIso_map_boundaryClass_closedBall`).
So the boundary class of the disc is the generator of `H₁(Circle; ℤ)` that Tau Ceti fixes.

## Proof

The inclusion of `D` into `ℂ` is a map of pairs `(D, S¹) ⟶ (ℂ, ℂ ∖ {0})`. It carries `[D, S¹]` to
the local orientation of `ℂ` at `0`: restrict to the centre of the disc, where `[D, S¹]` is the
local orientation of the open disc, and that is the pull-back of the local orientation of `ℂ`
(`TauCeti.comap_subtypeVal_complexHomologicalOrientation`). By naturality of the connecting
morphism, and since radial projection is the identity on the unit circle, the boundary class is
the image of that local orientation under the connecting morphism of `(ℂ, ℂ ∖ {0})` followed by
radial projection onto the unit circle. The local orientation of `ℂ` at `0` is the one of the
identity chart (`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`), so this image
is the generator of the unit circle selected by `Complex.orientation`
(`OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`),
which is the generator of `Circle.singularHomologyOneIso`
(`Circle.singularHomologyOneIso_inv_eq_complexOrientation`).

The naturality step follows Tau Ceti's
`TauCeti.localHomologyMap_translate_comp_reducedSingularHomologyδ` and
`TauCeti.snd_ofSubsetMap_translate_comp_complSingletonHomotopyEquivSphere`, which compare the
connecting morphisms and radial projections of the model at two points along a translation; here
the map is the inclusion of the disc.

## Main results

* `SymplecticGeometry.singularHomologyOneIso_map_boundaryClass_closedBall`:
  the boundary class of the closed unit disc is `1` in `H₁(Circle; ℤ) ≅ ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: local
  orientations and the fundamental class of a compact manifold with boundary.
-/

public section

noncomputable section

open CategoryTheory Limits Metric TauCeti AlgebraicTopology

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

private lemma preimage_discVal_subset_range : discVal ⁻¹' {0} ⊆ range ι :=
  preimage_discVal_subset.trans (singleton_subset_iff.2 (mem_range_self discCenter))

/-- The relative fundamental class of the closed unit disc, pushed into `ℂ`, is the local
orientation of `ℂ` at `0`. -/
private lemma localHomologyMap_fundamentalClassRel :
    localHomologyMap R discVal preimage_discVal_subset_range 2
        ((complexHomologicalOrientation openDisc).fundamentalClassRel Complex.finrank_real_complex
          isOpenEmbedding_ι (range_inclusion_ball_eq_compl 0 1)
          isCollared_inclusion_sphere_closedBall) =
      (complexHomologicalOrientation ℂ 0).val := by
  have hval : IsOpenEmbedding (Subtype.val : openDisc → ℂ) :=
    openDisc.isOpen.isOpenEmbedding_subtypeVal
  have h1 : localHomologyMap R discVal preimage_discVal_subset_range 2 =
      localHomologyRestriction R (singleton_subset_iff.2 (mem_range_self discCenter)) 2 ≫
        localHomologyMap R discVal preimage_discVal_subset 2 :=
    (localHomologyRestriction_comp_localHomologyMap R discVal _ preimage_discVal_subset 2).symm
  rw [h1, ConcreteCategory.comp_apply,
    HomologicalOrientation.localHomologyRestriction_fundamentalClassRel,
    localHomologyIsoOfIsOpenEmbedding_hom, ← ConcreteCategory.comp_apply, localHomologyMap_comp,
    ← comap_subtypeVal_complexHomologicalOrientation hval, HomologicalOrientation.comap_apply,
    IsOpenEmbedding.coe_localOrientationEquiv_symm]
  rw [localHomologyMap_congr R (j₁ := discVal.comp ⟨ι, isOpenEmbedding_ι.continuous⟩)
    (j₂ := ⟨Subtype.val, hval.continuous⟩) rfl]
  exact localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap_apply R hval discCenter _ 2 _

/-- On the boundary circle, radial projection about `0` is the identity. -/
private lemma snd_ofSubsetMap_comp_radial :
    TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of (closedBall (0 : ℂ) 1))
        (Y := TopCat.of ℂ) (B := (range ι)ᶜ) (B' := {0}ᶜ) (TopCat.ofHom discVal)
        ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 preimage_discVal_subset_range))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : ℂ)).toFun ≫
        TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)) =
      TopCat.ofHom closedBallComplToCircle := by
  ext z
  -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine (Circle.coe_homeomorphSphere_symm_apply _).trans
    ((coe_complSingletonHomotopyEquivSphere_apply 0 _).trans ?_)
  erw [TopPair.ofSubsetMap_snd_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, sub_zero]
  have h : (closedBallComplToCircle z : ℂ) = z.val := coe_closedBallComplToCircle_apply z
  rw [show ‖((z.val : closedBall (0 : ℂ) 1) : ℂ)‖ = 1 from h ▸ Circle.norm_coe _, inv_one, one_smul]
  exact h.symm

/-- The connecting morphism of the closed unit disc relative to its boundary circle, read in
`Circle`, factors through the local homology of `ℂ` at `0`, its connecting morphism and radial
projection. -/
@[reassoc]
private lemma reducedSingularHomologyδ_comp_closedBallComplToCircle :
    TopPair.reducedSingularHomologyδ
        (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of (closedBall (0 : ℂ) 1)))) R 1 ≫
      (reducedSingularHomologyFunctor R 1).map (TopCat.ofHom closedBallComplToCircle) =
      localHomologyMap R discVal preimage_discVal_subset_range 2 ≫
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))).reducedSingularHomologyδ R 1 ≫
          (reducedSingularHomologyFunctor R 1).map
            (TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : ℂ)).toFun) ≫
          (reducedSingularHomologyFunctor R 1).map
            (TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))) := by
  rw [localHomologyMap_def, ← TopPair.reducedSingularHomologyδ_naturality_assoc]
  congr 1
  -- The composite is only type-correct after unfolding the subspace of the pair.
  erw [← Functor.map_comp, ← Functor.map_comp, snd_ofSubsetMap_comp_radial]

/-- The local orientation of `ℂ` at `0` is the class whose connecting morphism, followed by radial
projection, is the generator of the unit circle selected by `Complex.orientation`. -/
private lemma reducedSingularHomologyδ_complexHomologicalOrientation :
    (reducedSingularHomologyFunctor R 1).map
        (TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : ℂ)).toFun)
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))).reducedSingularHomologyδ R 1
        (complexHomologicalOrientation ℂ 0).val) =
      (reducedSingularHomologySphereIsoOfOrientation R Complex.orientation
        Complex.finrank_real_complex).inv 1 := by
  have h0 : (0 : ℂ) ∈ (OpenPartialHomeomorph.refl ℂ).source := by simp
  -- The preferred chart of `ℂ` is the identity.
  have hrefl :
      OpenPartialHomeomorph.refl ℂ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 ℂ := by
    simpa using IsManifold.chart_mem_maximalAtlas (I := modelWithCornersSelf ℂ ℂ) (n := 1) (0 : ℂ)
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas hrefl h0]
  exact OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl
    h0 Complex.orientation Complex.finrank_real_complex

/-- **The boundary class of the closed unit disc.** Orient the open unit disc as an open subset
of `ℂ` (`TauCeti.complexHomologicalOrientation`). The boundary class of the closed unit disc
relative to the unit circle (`TauCeti.HomologicalOrientation.boundaryClass`), the image of its
relative fundamental class under the connecting morphism, is the class of `H₁(S¹; ℤ)` that, read
in `Circle` and through `Circle.singularHomologyOneIso`, is `1`: the generator of `H₁(Circle)`
that Tau Ceti fixes. -/
theorem singularHomologyOneIso_map_boundaryClass_closedBall :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom closedBallComplToCircle)
        ((complexHomologicalOrientation
            (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)).boundaryClass
          Complex.finrank_real_complex
          (.inclusion _ (isOpen_ball.preimage continuous_subtypeVal))
          (range_inclusion_ball_eq_compl 0 1) isCollared_inclusion_sphere_closedBall)) = 1 := by
  rw [HomologicalOrientation.boundaryClass_def]
  set γ := (complexHomologicalOrientation openDisc).fundamentalClassRel Complex.finrank_real_complex
    isOpenEmbedding_ι (range_inclusion_ball_eq_compl 0 1) isCollared_inclusion_sphere_closedBall
  set P := TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of (closedBall (0 : ℂ) 1)))
  set Q := TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))
  set H := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R
  set H' := reducedSingularHomologyFunctor R 1
  set e := TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))
  set c := TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : ℂ)).toFun
  set s := reducedSingularHomologySphereIsoOfOrientation R Complex.orientation
    Complex.finrank_real_complex
  have hB := ConcreteCategory.congr_hom reducedSingularHomologyδ_comp_closedBallComplToCircle γ
  simp only [ConcreteCategory.comp_apply] at hB
  have hδ := ConcreteCategory.congr_hom (TopPair.reducedSingularHomologyδ_comp_ι P R 1) γ
  have key : H.map (TopCat.ofHom closedBallComplToCircle) (P.singularHomologyδ R 2 1 rfl γ) =
      (Circle.singularHomologyOneIso R).inv 1 := calc
    _ = H.map (TopCat.ofHom closedBallComplToCircle)
          ((reducedSingularHomologyι R 1).app _ (P.reducedSingularHomologyδ R 1 γ)) :=
        congrArg _ hδ.symm
    _ = (reducedSingularHomologyι R 1).app _
          (H'.map (TopCat.ofHom closedBallComplToCircle) (P.reducedSingularHomologyδ R 1 γ)) :=
        (ConcreteCategory.congr_hom ((reducedSingularHomologyι R 1).naturality
          (TopCat.ofHom closedBallComplToCircle)) _).symm
    _ = (reducedSingularHomologyι R 1).app _ (H'.map e (H'.map c
          (Q.reducedSingularHomologyδ R 1
            (localHomologyMap R discVal preimage_discVal_subset_range 2 γ)))) :=
        congrArg _ hB
    _ = (reducedSingularHomologyι R 1).app _ (H'.map e (s.inv 1)) := by
        rw [localHomologyMap_fundamentalClassRel,
          reducedSingularHomologyδ_complexHomologicalOrientation]
    _ = H.map e ((reducedSingularHomologyι R 1).app _ (s.inv 1)) :=
        ConcreteCategory.congr_hom ((reducedSingularHomologyι R 1).naturality e) _
    _ = (Circle.singularHomologyOneIso R).inv 1 := by
        rw [Circle.singularHomologyOneIso_inv_eq_complexOrientation, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply]
  exact (congrArg _ key).trans ((Circle.singularHomologyOneIso R).inv_hom_id_apply 1)

end Disc

end SymplecticGeometry
