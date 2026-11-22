/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Circle
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# The boundary class of the closed unit disc

Let `D = closedBall (0 : ℂ) 1` be the closed unit disc. Its interior, the open unit disc, is an
open subset of `ℂ` and carries the orientation `TauCeti.complexHomologicalOrientation`; its
boundary is the unit circle. This file puts `D` in the setting of Tau Ceti's relative fundamental
class (`TauCeti.HomologicalOrientation.fundamentalClassRel`) and computes the sign of the boundary
class `∂[D, S¹] ∈ H₁(S¹; ℤ)`, the image of `[D, S¹]` under the connecting morphism of the pair.

The hypotheses of `fundamentalClassRel` hold in any real normed space: the inclusion of the open
unit ball into the closed one is an open embedding (`Topology.IsOpenEmbedding.inclusion`), its
range is the complement of the unit sphere (`SymplecticGeometry.range_inclusion_ball_eq_compl`),
and the unit sphere is collared by `(z, t) ↦ (1 - t) • z`, a homeomorphism from
`S × [0, 1)` onto the closed ball minus its centre
(`SymplecticGeometry.isCollared_inclusion_sphere_closedBall`).

The sign is `+1`: read in `Circle` (`SymplecticGeometry.closedBallComplToCircle`) and in `ℤ`
through `Circle.singularHomologyOneIso`, the boundary class is `1`
(`SymplecticGeometry.singularHomologyOneIso_singularHomologyδ_fundamentalClassRel_closedBall`).
So the boundary class of the disc is the generator of `H₁(Circle; ℤ)` that Tau Ceti fixes.

## Proof

The inclusion of `D` into `ℂ` is a map of pairs `(D, S¹) ⟶ (ℂ, ℂ ∖ {0})`. It carries `[D, S¹]` to
the local orientation of `ℂ` at `0`: restrict to the centre of the disc, where `[D, S¹]` is the
local orientation of the open disc, and that is the pull-back of the local orientation of `ℂ`
(`TauCeti.comap_subtypeVal_complexHomologicalOrientation`). By naturality of the connecting
morphism, and since radial projection is the identity on the unit circle, the boundary class is
the image of that local orientation under the connecting morphism of `(ℂ, ℂ ∖ {0})` followed by
radial projection onto the unit circle. By the definition of the local orientations of oriented
charts (`OpenPartialHomeomorph.localOrientationOfOrientedChart`), this image is the generator of
the unit circle selected by `Complex.orientation`, which is the generator of
`Circle.singularHomologyOneIso` (`Circle.singularHomologyOneIso_inv_eq`).

The naturality step follows Tau Ceti's
`TauCeti.localHomologyMap_translate_comp_reducedSingularHomologyδ` and
`TauCeti.snd_ofSubsetMap_translate_comp_complSingletonHomotopyEquivSphere`, which compare the
connecting morphisms and radial projections of the model at two points along a translation; here
the map is the inclusion of the disc.

## Main results

* `SymplecticGeometry.isCollared_inclusion_sphere_closedBall`: the unit sphere is collared in
  the closed unit ball of a real normed space.
* `SymplecticGeometry.range_inclusion_ball_eq_compl`: the open ball is the complement of the
  sphere in the closed ball.
* `SymplecticGeometry.singularHomologyOneIso_singularHomologyδ_fundamentalClassRel_closedBall`:
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

section Collar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball with its centre removed is `S × [0, 1)`, `S` the unit sphere, through
`(z, t) ↦ (1 - t) • z`. -/
private def sphereCollarHomeomorph :
    sphere (0 : E) 1 × Ico (0 : ℝ) 1 ≃ₜ ({w | (w : E) ≠ 0} : Set (closedBall (0 : E) 1)) where
  toFun p := ⟨⟨(1 - (p.2 : ℝ)) • (p.1 : E), by
      rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere p.1, mul_one,
        Real.norm_of_nonneg (by linarith [p.2.property.2])]
      linarith [p.2.property.1]⟩, by
    simp only [mem_ofPred_eq, ne_eq, smul_eq_zero, not_or]
    exact ⟨by linarith [p.2.property.2], ne_zero_of_mem_unit_sphere p.1⟩⟩
  invFun w := (⟨‖(w.val : E)‖⁻¹ • (w.val : E), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 w.property)]⟩,
    ⟨1 - ‖(w.val : E)‖, by linarith [mem_closedBall_zero_iff.1 w.val.property],
      by linarith [norm_pos_iff.2 w.property]⟩)
  left_inv p := by
    have ht : 0 < 1 - (p.2 : ℝ) := by linarith [p.2.property.2]
    have hn : ‖(1 - (p.2 : ℝ)) • (p.1 : E)‖ = 1 - p.2 := by
      rw [norm_smul, norm_eq_of_mem_sphere p.1, mul_one, Real.norm_of_nonneg ht.le]
    ext
    · simp only [hn, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    · simp only [hn, sub_sub_cancel]
  right_inv w := by
    ext
    simp only [sub_sub_cancel, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 w.property), one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hn : Continuous fun w : ({w | (w : E) ≠ 0} : Set (closedBall (0 : E) 1)) ↦
        ‖(w.val : E)‖ := by fun_prop
    exact (((hn.inv₀ fun w ↦ norm_ne_zero_iff.2 w.property).smul (by fun_prop)).subtype_mk _).prodMk
      ((continuous_const.sub hn).subtype_mk _)

/-- **The unit sphere is collared in the closed unit ball**, by `(z, t) ↦ (1 - t) • z`. -/
theorem isCollared_inclusion_sphere_closedBall :
    IsCollared (inclusion (sphere_subset_closedBall : sphere (0 : E) 1 ⊆ closedBall 0 1)) :=
  isCollared_iff.2 ⟨fun p ↦ (sphereCollarHomeomorph p).val,
    ⟨(isOpen_compl_singleton.preimage continuous_subtypeVal).isOpenEmbedding_subtypeVal.comp
      sphereCollarHomeomorph.isOpenEmbedding, fun z ↦ by
        ext
        simp [sphereCollarHomeomorph]⟩⟩

end Collar

/-- In a pseudometric space, the open ball is the complement of the sphere in the closed ball. -/
theorem range_inclusion_ball_eq_compl {α : Type*} [PseudoMetricSpace α] (x : α) (r : ℝ) :
    range (inclusion (ball_subset_closedBall : ball x r ⊆ closedBall x r)) =
      (range (inclusion (sphere_subset_closedBall : sphere x r ⊆ closedBall x r)))ᶜ := by
  ext w
  have hw := mem_closedBall.1 w.property
  simp only [range_inclusion, mem_ofPred_eq, mem_compl_iff, mem_ball, mem_sphere]
  exact ⟨ne_of_lt, fun h ↦ lt_of_le_of_ne hw h⟩

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
  have hx : complexHomologicalOrientation ℂ 0 =
      (OpenPartialHomeomorph.refl ℂ).localOrientationOfOrientedChart h0 Complex.orientation
        (n := 1) Complex.finrank_real_complex := by
    rw [complexHomologicalOrientation_apply]
    have : ∀ (φ : OpenPartialHomeomorph ℂ ℂ) (_ : φ = OpenPartialHomeomorph.refl ℂ)
        (h : (0 : ℂ) ∈ φ.source), φ.localOrientationOfOrientedChart h Complex.orientation
          (n := 1) Complex.finrank_real_complex =
        (OpenPartialHomeomorph.refl ℂ).localOrientationOfOrientedChart h0 Complex.orientation
          (n := 1) Complex.finrank_real_complex := by
      rintro _ rfl _
      rfl
    exact this _ chartAt_self_eq _
  have h := singularHomologyComplSingletonIsoOfOrientation_refl_hom R h0 Complex.orientation
    Complex.finrank_real_complex
  rw [hx, OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  set e := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl ℂ) h0
    Complex.orientation Complex.finrank_real_complex
  set s := reducedSingularHomologySphereIsoOfOrientation R Complex.orientation
    Complex.finrank_real_complex
  apply (ConcreteCategory.bijective_of_isIso s.hom).1
  calc s.hom _ = e.hom (e.inv 1) := by
        rw [h, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        -- The two sides differ only in how the degree of the local homology class is written,
        -- as `2` or as `1 + 1`.
        rfl
    _ = s.hom (s.inv 1) := by rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

/-- **The boundary class of the closed unit disc.** Orient the open unit disc as an open subset
of `ℂ` (`TauCeti.complexHomologicalOrientation`). The connecting morphism of the closed unit disc
relative to the unit circle sends its relative fundamental class
(`TauCeti.HomologicalOrientation.fundamentalClassRel`) to the class of `H₁(S¹; ℤ)` that, read in
`Circle` and through `Circle.singularHomologyOneIso`, is `1`: the generator of `H₁(Circle)` that
Tau Ceti fixes. -/
theorem singularHomologyOneIso_singularHomologyδ_fundamentalClassRel_closedBall :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom closedBallComplToCircle)
        ((TopPair.ofSubset ((range (inclusion
            (ball_subset_closedBall : ball (0 : ℂ) 1 ⊆ closedBall 0 1)))ᶜ :
              Set (TopCat.of (closedBall (0 : ℂ) 1)))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 1 rfl
          ((complexHomologicalOrientation
              (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)).fundamentalClassRel
            Complex.finrank_real_complex
            (.inclusion _ (isOpen_ball.preimage continuous_subtypeVal))
            (range_inclusion_ball_eq_compl 0 1) isCollared_inclusion_sphere_closedBall))) = 1 := by
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
        rw [Circle.singularHomologyOneIso_inv_eq, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply]
  exact (congrArg _ key).trans ((Circle.singularHomologyOneIso R).inv_hom_id_apply 1)

end Disc

end SymplecticGeometry
