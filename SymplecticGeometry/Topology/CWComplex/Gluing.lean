/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Pushout
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel
import TauCeti.Topology.Homotopy.Extension.CWComplex

/-!
# Gluing a relative CW model to a piece of a space

Let a space `Y` be the pushout of two subspaces `T` and `W` along a common subspace `A`, where
`A` has the homotopy extension property in `W`, and let `Z ⊆ T` be a deformation retract of `T`.
Given a relative CW model of `W` over `A`, that is a Hausdorff space `X`, an embedding
`j : A → X`, a CW structure on `X` relative to the image of `j` and a homotopy equivalence
`h : X ≃ₕ W` which is the inclusion on `A`, this file builds a relative CW model of `Y` over `Z`
with the same cells (`SymplecticGeometry.exists_relCWComplex_homotopyEquiv_of_isPushout`).

The model is the adjunction space `Z ∪ X` obtained by attaching `X` to `Z` along the retraction
`T → Z` restricted to `A`. It is built in two steps.

* The adjunction space `T ∪_A X` is homotopy equivalent to `Y = T ∪_A W`, by the map which is the
  identity on `T` and `h` on `X`
  (`SymplecticGeometry.exists_homotopyEquiv_relCWAdjunctionSpace_of_isPushout`). Since `A` and
  its image in `X` both have the homotopy extension property, `h` has a homotopy inverse which is
  `j` on `A`, and both composites are homotopic to the identity relative to `A`
  (`TauCeti.HasHomotopyExtensionProperty.exists_inverse_homotopicRel`); these homotopies glue
  with the constant homotopy on `T`
  (`CategoryTheory.IsPushout.homotopicRel_of_homotopicRel_comp_inl`). This is the gluing theorem
  for homotopy equivalences under cofibrations.
* Changing the base of the attachment along the homotopy equivalence `T ≃ₕ Z` given by the
  retraction keeps the cells and gives `Z ∪ X`
  (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_relCWAdjunctionSpace`), and the CW
  structure and its cells come from `TauCeti.relativeCWPushout`.

## Main results

* `SymplecticGeometry.exists_homotopyEquiv_relCWAdjunctionSpace_of_isPushout`: replacing `W` by a
  relative CW model of it in the pushout `T ∪_A W` does not change the homotopy type.
* `SymplecticGeometry.exists_relCWComplex_homotopyEquiv_of_isPushout`: a relative CW model of
  `Y` over the deformation retract `Z` of `T`, with the cells of the model of `W`.

## References

* R. Brown, *Topology and Groupoids*, 2006, Sections 7.4 and 7.5, for homotopy equivalences
  under cofibrations and the gluing theorem.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology TauCeti Topology.RelCWComplex ContinuousMap

namespace SymplecticGeometry

universe u

variable {Y : Type u} [TopologicalSpace Y] {A T W : Set Y} {hAT : A ⊆ T} {hAW : A ⊆ W}
  {X : Type u} [TopologicalSpace X] {j : C(A, X)}

/-- The map from the image of a relative CW model's base embedding `j : A → X` to a superset `T`
of `A`, which undoes `j`. It is the attaching map of `X` to `T` in
`SymplecticGeometry.exists_homotopyEquiv_relCWAdjunctionSpace_of_isPushout`. -/
def relCWModelAttachingMap (hAT : A ⊆ T) (hj : IsEmbedding j) : C(range j, T) :=
  (ContinuousMap.inclusion hAT).comp (hj.toHomeomorph.symm : C(range j, A))

theorem relCWModelAttachingMap_apply (hj : IsEmbedding j) (a : A) :
    relCWModelAttachingMap hAT hj ⟨j a, mem_range_self a⟩ = ContinuousMap.inclusion hAT a := by
  simp [relCWModelAttachingMap]

/-- **Gluing a relative CW model into a pushout.** Let `Y` be the pushout of `T` and `W` along
`A`, given as a pushout square of inclusions, with `A` having the homotopy extension property in
`W`. Let `X` be a relative CW complex over the image of an embedding `j : A → X`, and
`h : X ≃ₕ W` a homotopy equivalence which is the inclusion on `A`. Then the adjunction space
`T ∪_A X` is homotopy equivalent to `Y`, by a homotopy equivalence which is the inclusion on
`T`. -/
theorem exists_homotopyEquiv_relCWAdjunctionSpace_of_isPushout
    (hY : IsPushout (TopCat.ofHom (ContinuousMap.inclusion hAW))
      (TopCat.ofHom (ContinuousMap.inclusion hAT))
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(W, Y)))
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(T, Y))))
    (hA : HasHomotopyExtensionProperty (range (ContinuousMap.inclusion hAW)))
    [T2Space X] [RelCWComplex (univ : Set X) (range j)] (hj : IsEmbedding j) (h : X ≃ₕ W)
    (hh : ∀ a, (h (j a) : Y) = a) :
    ∃ e : relCWAdjunctionSpace (univ : Set X) (relCWModelAttachingMap hAT hj) ≃ₕ Y,
      ∀ t, e (pushout.inr (relCWBaseInclusion (univ : Set X))
        (TopCat.ofHom (relCWModelAttachingMap hAT hj)) t) = t := by
  set a₁ := relCWModelAttachingMap hAT hj
  have hP := IsPushout.of_hasPushout (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁)
  -- `h` restricts to a homeomorphism from the image of `j` onto `A`.
  let eA : range j ≃ₜ range (ContinuousMap.inclusion hAW) :=
    hj.toHomeomorph.symm.trans
      (IsEmbedding.toHomeomorph (f := ContinuousMap.inclusion hAW) (.inclusion hAW))
  have heA (x : range j) : h x = (eA x : W) := by
    have key (a : A) : h (j a) = (eA ⟨j a, mem_range_self a⟩ : W) := by
      apply Subtype.ext
      simp only [eA]
      rw [Homeomorph.trans_apply]
      rw [IsEmbedding.toHomeomorph_symm_apply]
      exact hh a
    obtain ⟨_, a, rfl⟩ := x
    exact key a
  have hX : HasHomotopyExtensionProperty (range j) := by
    have := (hasHomotopyExtensionProperty_base (C := (univ : Set X)) (D := range j)).image
      (Homeomorph.Set.univ X)
    convert this using 1
    ext x
    simp
  obtain ⟨g, hgA, hgh, hhg⟩ := hX.exists_inverse_homotopicRel hA h eA heA
  have hgj (a : A) : g (ContinuousMap.inclusion hAW a) = j a := by
    rw [hgA ⟨ContinuousMap.inclusion hAW a, mem_range_self a⟩]
    simp only [eA]
    rw [Homeomorph.symm_trans_apply]
    exact congrArg (fun b ↦ j b) ((IsEmbedding.inclusion hAW).toHomeomorph_symm_apply a)
  have hinl (a : A) : pushout.inl (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁)
      ⟨j a, mem_univ _⟩ = pushout.inr _ (TopCat.ofHom a₁) (ContinuousMap.inclusion hAT a) := by
    have := ConcreteCategory.congr_hom
      (pushout.condition (f := relCWBaseInclusion (univ : Set X)) (g := TopCat.ofHom a₁))
      ⟨j a, a, rfl⟩
    exact this.trans (congrArg _ (relCWModelAttachingMap_apply hj a))
  let valX : C((univ : Set X), X) := ⟨Subtype.val, continuous_subtypeVal⟩
  let cX : C(X, (univ : Set X)) := ⟨fun x ↦ ⟨x, mem_univ x⟩, by fun_prop⟩
  have hcX (x : X) : cX x = ⟨x, mem_univ x⟩ := rfl
  have hvalX (x : (univ : Set X)) : valX x = x := rfl
  -- The map `T ∪_A X → Y` which is the inclusion on `T` and `h` on `X`.
  let F : relCWAdjunctionSpace (univ : Set X) a₁ ⟶ TopCat.of Y :=
    hP.desc (TopCat.ofHom ((⟨Subtype.val, continuous_subtypeVal⟩ : C(W, Y)).comp
      (h.toFun.comp valX)))
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(T, Y))) (by
      ext ⟨_, a, rfl⟩
      simp [valX, a₁, relCWModelAttachingMap_apply, hh])
  -- The map `Y → T ∪_A X` which is the inclusion on `T` and `g` on `W`.
  let G : TopCat.of Y ⟶ relCWAdjunctionSpace (univ : Set X) a₁ :=
    hY.desc (TopCat.ofHom (cX.comp g) ≫ pushout.inl _ _) (pushout.inr _ _) (by
      ext a
      simp [cX, hgj, hinl])
  have hFinr (t : T) : F (pushout.inr (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁) t) =
      (t : Y) :=
    ConcreteCategory.congr_hom (hP.inr_desc _ _ _) t
  have hFinl (x : (univ : Set X)) :
      F (pushout.inl (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁) x) = (h x : Y) :=
    ConcreteCategory.congr_hom (hP.inl_desc _ _ _) x
  have hGT (t : T) :
      G (t : Y) = pushout.inr (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁) t :=
    ConcreteCategory.congr_hom (hY.inr_desc _ _ _) t
  have hGW (w : W) : G (w : Y) =
      pushout.inl (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁) ⟨g w, mem_univ _⟩ :=
    ConcreteCategory.congr_hom (hY.inl_desc _ _ _) w
  have hFG : (F.hom.comp G.hom).Homotopic (ContinuousMap.id Y) := by
    refine (hY.homotopicRel_of_homotopicRel_comp_inl (f := F.hom.comp G.hom)
      (g := ContinuousMap.id Y) (fun t ↦ ?_) ?_).homotopic
    · simpa [hFinr] using congrArg F (hGT t)
    · convert hhg.comp_continuousMap ⟨Subtype.val, continuous_subtypeVal⟩ using 1
      · ext w
        simpa [hFinl] using congrArg F (hGW w)
      · rfl
  have hGF : (G.hom.comp F.hom).Homotopic (ContinuousMap.id _) := by
    refine (hP.homotopicRel_of_homotopicRel_comp_inl (f := G.hom.comp F.hom)
      (g := ContinuousMap.id _) (fun t ↦ ?_) ?_).homotopic
    · simpa [hFinr] using hGT t
    · have := ((hgh.precomp valX).comp_continuousMap cX).comp_continuousMap
        (pushout.inl (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁)).hom
      convert this using 1
      · ext x
        simpa [hFinl, hcX, hvalX] using hGW (h x)
      · rfl
      · ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨⟨F.hom, G.hom, hGF, hFG⟩, hFinr⟩

end SymplecticGeometry

end
