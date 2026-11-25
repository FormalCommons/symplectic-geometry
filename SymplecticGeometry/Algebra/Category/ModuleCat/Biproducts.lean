/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Biproducts

/-!
# Maps into and out of binary biproducts of modules, as maps of product modules

This file is a part of Tau Ceti's file `TauCeti/Algebra/Category/ModuleCat/Biproducts.lean`, at
Tau Ceti commit `c58e054d1cafd4db22ff7a3626b04bdb6f0b2335`, which the version of Tau Ceti that
this library is pinned to does not have yet. It contains the two theorems of that file that the
commit adds, with their statements, proofs and docstrings unchanged. The rest of Tau Ceti's file
is in the pinned version, which this file imports in place of Tau Ceti's imports.

For a binary biproduct, Mathlib's `ModuleCat.biprodIsoProd` identifies `M ⊞ N` with the product
module `M × N`. Under it, `biprod.lift f g` and `biprod.desc f g` are the pair map
`f.hom.prod g.hom` and the sum map `f.hom.coprod g.hom`.

## Main results

* `ModuleCat.biprod_lift_comp_biprodIsoProd_hom`, `ModuleCat.biprodIsoProd_hom_comp_ofHom_coprod`:
  under `ModuleCat.biprodIsoProd`, `biprod.lift f g` and `biprod.desc f g` are the pair map
  `f.hom.prod g.hom` and the sum map `f.hom.coprod g.hom`.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R] (M N : ModuleCat.{v} R)

variable {M N} in
/-- The map `biprod.lift f g` into a biproduct, followed by the identification of the biproduct
with the product module, is the pair map `f.hom.prod g.hom`. -/
theorem biprod_lift_comp_biprodIsoProd_hom {X : ModuleCat.{v} R} (f : X ⟶ M) (g : X ⟶ N) :
    biprod.lift f g ≫ (biprodIsoProd M N).hom = ofHom (f.hom.prod g.hom) := by
  rw [← Iso.eq_comp_inv]
  apply biprod.hom_ext <;> ext x <;> simp

variable {M N} in
/-- The identification of the biproduct with the product module, followed by the sum map
`f.hom.coprod g.hom`, is the map `biprod.desc f g` out of the biproduct. -/
theorem biprodIsoProd_hom_comp_ofHom_coprod {Z : ModuleCat.{v} R} (f : M ⟶ Z) (g : N ⟶ Z) :
    (biprodIsoProd M N).hom ≫ ofHom (f.hom.coprod g.hom) = biprod.desc f g := by
  apply biprod.hom_ext' <;> ext x <;> simp

end ModuleCat
