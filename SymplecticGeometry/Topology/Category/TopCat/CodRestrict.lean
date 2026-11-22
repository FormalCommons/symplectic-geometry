/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Corestriction of morphisms of `TopCat`

A morphism `f : Z ⟶ X` of `TopCat` whose values lie in a subset `S` of `X` corestricts to a
morphism `TopCat.codRestrict f S h : Z ⟶ TopCat.of S`, the continuous map `Set.codRestrict f S h`.
Followed by the inclusion of `S`, it is `f` (`TopCat.codRestrict_comp_ofHom_subtypeVal`).

Mathlib corestricts bounded continuous maps (`BoundedContinuousFunction.codRestrict`) and
continuous linear maps, but not continuous maps or morphisms of `TopCat`.
-/

public section

open CategoryTheory

universe u

namespace TopCat

variable {X Z : TopCat.{u}}

/-- The corestriction of a morphism `f : Z ⟶ X` to a subset `S` of `X` that contains its
values: the morphism `Z ⟶ TopCat.of S` given by `Set.codRestrict f S h`. -/
def codRestrict (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) : Z ⟶ TopCat.of S :=
  ofHom ⟨S.codRestrict f h, by fun_prop⟩

lemma codRestrict_def (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) :
    codRestrict f S h = ofHom ⟨S.codRestrict f h, by fun_prop⟩ :=
  (rfl)

@[simp]
lemma coe_codRestrict_apply (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) (z : Z) :
    (codRestrict f S h z : X) = f z :=
  (rfl)

/-- The corestriction of `f` to `S`, followed by the inclusion of `S`, is `f`. -/
@[reassoc (attr := simp)]
lemma codRestrict_comp_ofHom_subtypeVal (f : Z ⟶ X) (S : Set X) (h : ∀ z, f z ∈ S) :
    codRestrict f S h ≫ ofHom (ContinuousMap.subtypeVal S) = f :=
  (rfl)

/-- Corestriction commutes with precomposition. -/
lemma comp_codRestrict {Y : TopCat.{u}} (g : Y ⟶ Z) (f : Z ⟶ X) (S : Set X)
    (h : ∀ z, f z ∈ S) :
    g ≫ codRestrict f S h = codRestrict (g ≫ f) S fun y ↦ h (g y) :=
  (rfl)

end TopCat

end
