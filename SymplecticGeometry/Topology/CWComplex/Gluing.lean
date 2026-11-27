/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Pushout
import SymplecticGeometry.Topology.Homotopy.Extension.CWComplex
import SymplecticGeometry.Topology.Homotopy.Extension.Pushout
import TauCeti.Topology.Homotopy.DeformationRetract

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
  identity on `T` and `h` on `X`. This is the gluing theorem for homotopy equivalences under
  cofibrations (`CategoryTheory.IsPushout.exists_homotopyEquiv_of_homotopyEquiv`), applied with
  the homotopy extension property of the base of `X`
  (`TauCeti.hasHomotopyExtensionProperty_base_univ`).
* Changing the base of the attachment along the homotopy equivalence `T ≃ₕ Z` given by the
  retraction keeps the cells and gives `Z ∪ X`
  (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_relCWAdjunctionSpace`), and the CW
  structure and its cells come from `TauCeti.relativeCWPushout`.

## Main results

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

/-- **A relative CW model of a pushout over a deformation retract.** Let `Y` be the pushout of
`T` and `W` along `A`, given as a pushout square of inclusions, with `A` having the homotopy
extension property in `W`, and let `Z ⊆ T` be a Hausdorff deformation retract of `T`, by a
retraction `r : T → Z` whose composite with the inclusion is homotopic to the identity of `T`.
Let `X` be a Hausdorff relative CW complex over the image of an embedding `j : A → X`, and
`h : X ≃ₕ W` a homotopy equivalence which is the inclusion on `A`. Then `Y` is homotopy
equivalent to a Hausdorff relative CW complex `X'` over the image of a closed embedding
`j' : Z → X'`, with the cells of `X` in each dimension, by a homotopy equivalence which is the
inclusion on `Z`. -/
theorem exists_relCWComplex_homotopyEquiv_of_isPushout
    (hY : IsPushout (TopCat.ofHom (ContinuousMap.inclusion hAW))
      (TopCat.ofHom (ContinuousMap.inclusion hAT))
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(W, Y)))
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(T, Y))))
    (hA : HasHomotopyExtensionProperty (range (ContinuousMap.inclusion hAW)))
    {Z : Set Y} [T2Space Z] (hZT : Z ⊆ T) (r : C(T, Z))
    (hr : ∀ z, r (ContinuousMap.inclusion hZT z) = z)
    (hr' : ((ContinuousMap.inclusion hZT).comp r).Homotopic (ContinuousMap.id T))
    [T2Space X] [RelCWComplex (univ : Set X) (range j)] (hj : IsEmbedding j) (h : X ≃ₕ W)
    (hh : ∀ a, (h (j a) : Y) = a) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : T2Space X') (j' : C(Z, X'))
      (_ : RelCWComplex (univ : Set X') (range j')) (h' : X' ≃ₕ Y),
      IsClosedEmbedding j' ∧ (∀ z, h' (j' z) = z) ∧
      Nonempty (∀ m, cell (univ : Set X') m ≃ cell (univ : Set X) m) := by
  -- The attaching map `range j → T`, which undoes `j` and includes `A` in `T`.
  let a₁ : C(range j, T) :=
    (ContinuousMap.inclusion hAT).comp (hj.toHomeomorph.symm : C(range j, A))
  -- `T ∪_A X`, read as a pushout of `T ← A → X`.
  have hP : IsPushout (TopCat.ofHom j) (TopCat.ofHom (ContinuousMap.inclusion hAT))
      ((TopCat.isoOfHomeo (Homeomorph.Set.univ X)).inv ≫
        pushout.inl (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁))
      (pushout.inr (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁)) := by
    refine (IsPushout.of_hasPushout (relCWBaseInclusion (univ : Set X)) (TopCat.ofHom a₁)).of_iso
      (TopCat.isoOfHomeo hj.toHomeomorph.symm) (TopCat.isoOfHomeo (Homeomorph.Set.univ X))
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ (by simp)
    · ext ⟨_, a, rfl⟩
      simp
    · ext ⟨_, a, rfl⟩
      simp [a₁]
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  -- `T ∪_A X ≃ₕ Y`, which is the inclusion on `T`.
  obtain ⟨e, -, he⟩ := hP.exists_homotopyEquiv_of_homotopyEquiv hY hj (.inclusion hAW)
    hasHomotopyExtensionProperty_base_univ hA h fun a ↦ Subtype.ext (hh a)
  -- The homotopy equivalence `Z ≃ₕ T` given by the inclusion and the retraction.
  let eZ : Z ≃ₕ T := .ofDeformationRetraction (ContinuousMap.inclusion hZT) r hr hr'
  obtain ⟨E, -, hE⟩ := eZ.symm.exists_homotopyEquiv_relCWAdjunctionSpace (univ : Set X) a₁
  refine ⟨_, inferInstance, inferInstance, _, relativeCWPushout (univ : Set X) _, E.symm.trans e,
    isClosedEmbedding_pushout_inr_relCWBaseInclusion (C := (univ : Set X)) _, fun z ↦ ?_,
    ⟨relativeCWPushoutCellEquiv (univ : Set X) _⟩⟩
  rw [HomotopyEquiv.trans_apply, hE, he]
  simp [eZ]

end SymplecticGeometry

end
