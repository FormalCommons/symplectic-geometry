/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.Category.TopCat.Basic
import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel
import TauCeti.Topology.Homotopy.Extension.Pushout

/-!
# Replacing the attached space by a homotopy equivalent one

Let `i : B → Y` and `i' : B → Y'` be embeddings whose images have the homotopy extension
property, and let `P = Z ∪_a Y` and `P' = Z ∪_a Y'` be obtained by attaching `Y` and `Y'` to the
same space `Z` along the same map `a : B → Z`, given as pushout squares in `TopCat`. A homotopy
equivalence `e : Y ≃ₕ Y'` with `e ∘ i = i'` then induces a homotopy equivalence `P ≃ₕ P'` which
is `e` on `Y` and the identity on `Z`
(`CategoryTheory.IsPushout.exists_homotopyEquiv_of_homotopyEquiv`). This is the gluing theorem
for homotopy equivalences under cofibrations, in the case where the equivalence on `Z` is the
identity.

Since both images have the homotopy extension property, `e` has a homotopy inverse `g` with
`g ∘ i' = i`, and both composites are homotopic to the identity relative to the images
(`TauCeti.HasHomotopyExtensionProperty.exists_inverse_homotopicRel`). These homotopies, together
with the constant homotopy on `Z`, descend to the pushouts
(`CategoryTheory.IsPushout.homotopicRel_of_homotopicRel_comp_inl`). Tau Ceti's
`CategoryTheory.IsPushout.exists_homotopic_id_of_homotopic_id` is the companion statement, in
which the attached space stays and the base `Z` changes.

## References

* R. Brown, *Topology and Groupoids*, 2006, Sections 7.4 and 7.5, for homotopy equivalences
  under cofibrations and the gluing theorem.
-/

public section

noncomputable section

open Set Topology ContinuousMap TauCeti

namespace CategoryTheory.IsPushout

universe u

variable {B Y Y' Z P P' : TopCat.{u}} {i : B ⟶ Y} {i' : B ⟶ Y'} {a : B ⟶ Z} {j : Y ⟶ P}
  {k : Z ⟶ P} {j' : Y' ⟶ P'} {k' : Z ⟶ P'}

/-- **Gluing a homotopy equivalence under cofibrations.** Let `P = Z ∪_a Y` and `P' = Z ∪_a Y'`
be obtained by attaching `Y` and `Y'` to `Z` along the same `a : B → Z`, through embeddings
`i : B → Y` and `i' : B → Y'` whose images have the homotopy extension property. A homotopy
equivalence `e : Y ≃ₕ Y'` with `e ∘ i = i'` induces a homotopy equivalence `E : P ≃ₕ P'` which is
`e` on `Y` and the identity on `Z`. -/
theorem exists_homotopyEquiv_of_homotopyEquiv (h : IsPushout i a j k) (h' : IsPushout i' a j' k')
    (hi : IsEmbedding i) (hi' : IsEmbedding i') (hA : HasHomotopyExtensionProperty (range i))
    (hA' : HasHomotopyExtensionProperty (range i')) (e : Y ≃ₕ Y') (he : ∀ b, e (i b) = i' b) :
    ∃ E : P ≃ₕ P', (∀ y, E (j y) = j' (e y)) ∧ ∀ z, E (k z) = k' z := by
  -- `e` restricts to a homeomorphism between the images of `i` and `i'`; it has a homotopy
  -- inverse `g` which undoes it there.
  let eB : range i ≃ₜ range i' := hi.toHomeomorph.symm.trans hi'.toHomeomorph
  have heB (y : range i) : e y = eB y := by
    obtain ⟨_, b, rfl⟩ := y
    simp [eB, he]
  obtain ⟨g, hgB, hge, heg⟩ := hA.exists_inverse_homotopicRel hA' e eB heB
  have hg (b : B) : g (i' b) = i b := by
    simpa [eB] using hgB ⟨i' b, mem_range_self b⟩
  -- The maps `P → P'` and `P' → P` induced by `e` and `g`.
  let F : P ⟶ P' := h.desc (TopCat.ofHom e.toFun ≫ j') k' (by ext b; simp [he, h'.w_apply])
  let G : P' ⟶ P := h'.desc (TopCat.ofHom g ≫ j) k (by ext b; simp [hg, h.w_apply])
  have hFj (y : Y) : F (j y) = j' (e y) := ConcreteCategory.congr_hom (h.inl_desc _ _ _) y
  have hFk (z : Z) : F (k z) = k' z := ConcreteCategory.congr_hom (h.inr_desc _ _ _) z
  have hGj (y : Y') : G (j' y) = j (g y) := ConcreteCategory.congr_hom (h'.inl_desc _ _ _) y
  have hGk (z : Z) : G (k' z) = k z := ConcreteCategory.congr_hom (h'.inr_desc _ _ _) z
  -- On `Y` and `Y'` the composites are those of `e` and `g`, so the homotopies relative to the
  -- images of `B` descend to the pushouts.
  have hGF : (G.hom.comp F.hom).Homotopic (ContinuousMap.id P) := by
    refine (h.homotopicRel_of_homotopicRel_comp_inl (f := G.hom.comp F.hom)
      (g := .id _) (fun z ↦ by simp [hFk, hGk]) ?_).homotopic
    convert hge.comp_continuousMap j.hom using 2 <;> ext y <;> simp [hFj, hGj]
  have hFG : (F.hom.comp G.hom).Homotopic (ContinuousMap.id P') := by
    refine (h'.homotopicRel_of_homotopicRel_comp_inl (f := F.hom.comp G.hom)
      (g := .id _) (fun z ↦ by simp [hFk, hGk]) ?_).homotopic
    convert heg.comp_continuousMap j'.hom using 2 <;> ext y <;> simp [hFj, hGj]
  exact ⟨⟨F.hom, G.hom, hGF, hFG⟩, hFj, hFk⟩

end CategoryTheory.IsPushout

end
