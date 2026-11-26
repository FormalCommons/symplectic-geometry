/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Topology.ContinuousMap.CodRestrict
import SymplecticGeometry.Topology.ContinuousMap.Basic

/-!
# Corestriction of morphisms of `TopCat`

A morphism `f : Z ⟶ X` of `TopCat` whose values lie in a subset `S` of `X` corestricts to a
morphism `TopCat.codRestrict f S h : Z ⟶ TopCat.of S`, the corestriction
`ContinuousMap.codRestrict` of the underlying continuous map. Followed by the inclusion of `S`, it
is `f` (`TopCat.codRestrict_comp_ofHom_subtypeVal`). The lemmas are those of
`ContinuousMap.codRestrict`, read in `TopCat`.
-/

public section

open CategoryTheory

universe u

namespace TopCat

variable {X Z : TopCat.{u}}

/-- The corestriction of a morphism `f : Z ⟶ X` to a subset `S` of `X` that contains its
values: the morphism `Z ⟶ TopCat.of S` given by `ContinuousMap.codRestrict f.hom S h`. -/
def codRestrict (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) : Z ⟶ TopCat.of S :=
  ofHom (f.hom.codRestrict S h)

lemma codRestrict_def (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) :
    codRestrict f S h = ofHom (f.hom.codRestrict S h) :=
  (rfl)

@[simp]
lemma hom_codRestrict (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) :
    (codRestrict f S h).hom = f.hom.codRestrict S h := by
  rw [codRestrict_def, hom_ofHom]

lemma coe_codRestrict_apply (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) (z : Z) :
    (codRestrict f S h z : X) = f z := by
  rw [← ContinuousMap.coe_codRestrict_apply f.hom S h, ← hom_codRestrict]

/-- The corestriction of `f` to `S`, followed by the inclusion of `S`, is `f`. -/
@[reassoc (attr := simp)]
lemma codRestrict_comp_ofHom_subtypeVal (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) :
    codRestrict f S h ≫ ofHom (ContinuousMap.subtypeVal S) = f := by
  rw [codRestrict_def, ← ofHom_comp, ContinuousMap.subtypeVal_comp_codRestrict, ofHom_hom]

/-- Corestriction commutes with precomposition. -/
lemma comp_codRestrict {Y : TopCat.{u}} (g : Y ⟶ Z) (f : Z ⟶ X) (S : Set X)
    (h : ∀ z, f z ∈ S) :
    g ≫ codRestrict f S h = codRestrict (g ≫ f) S fun y ↦ h (g y) := by
  refine hom_ext ?_
  simp only [hom_comp, hom_codRestrict, ContinuousMap.comp_codRestrict]

end TopCat

end
