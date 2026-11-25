/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Biproducts

/-!
# Maps into and out of binary biproducts of modules, as maps of product modules

Under the identification `ModuleCat.biprodIsoProd` of the biproduct `M ⊞ N` in `ModuleCat R` with
the product module `M × N`, the morphism `biprod.lift f g` into the biproduct becomes the linear
map `f.prod g` into the product, and `biprod.desc f g` out of the biproduct becomes
`f.coprod g`. These let exact sequences stated with biproducts be read as exact sequences of
linear maps between product modules.

## Main results

* `ModuleCat.biprod_lift_comp_biprodIsoProd_hom`
* `ModuleCat.biprodIsoProd_hom_comp_ofHom_coprod`
-/

public section

open CategoryTheory Limits

namespace ModuleCat

universe v

variable {R : Type*} [Ring R] {M N P : ModuleCat.{v} R}

/-- Under the identification of the biproduct with the product module, `biprod.lift` is
`LinearMap.prod`. -/
@[reassoc]
theorem biprod_lift_comp_biprodIsoProd_hom (f : P →ₗ[R] M) (g : P →ₗ[R] N) :
    biprod.lift (ofHom f) (ofHom g) ≫ (biprodIsoProd M N).hom = ofHom (f.prod g) := by
  rw [← Iso.eq_comp_inv]
  apply biprod.hom_ext <;> ext x <;> simp [biprodIsoProd_inv_comp_fst, biprodIsoProd_inv_comp_snd]

/-- Under the identification of the biproduct with the product module, `biprod.desc` is
`LinearMap.coprod`. -/
@[reassoc]
theorem biprodIsoProd_hom_comp_ofHom_coprod (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    (biprodIsoProd M N).hom ≫ ofHom (f.coprod g) = biprod.desc (ofHom f) (ofHom g) := by
  apply biprod.hom_ext' <;> ext x <;> simp

end ModuleCat
