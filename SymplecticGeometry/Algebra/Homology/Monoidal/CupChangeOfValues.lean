/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cup

/-!
# The cup product along a diagonal under a change of cochain values

Let `D : E ⟶ A ⊗ B` be a diagonal of chain complexes, as in Tau Ceti's
`TauCeti.ChainComplex.cup`. Morphisms `g₁ : M ⟶ M'`, `g₂ : N ⟶ N'` and `g : P ⟶ P'` of cochain
values that intertwine two pairings, `(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`, are compatible with the cup
product: composing the two factors with `g₁` and `g₂` and then cupping along `μ'` is the same as
cupping along `μ` and then composing with `g`. This holds for cochains and, through the maps
`ChainComplex.linearYonedaObjMap` that composition with a morphism of values induces, for classes
in cohomology.

The proof of `TauCeti.ChainComplex.cup_homologyMap_linearYonedaObjMap` follows that of Tau Ceti's
`TauCeti.ChainComplex.cup_naturality`, with the change of cochain values in place of the change of
chains.

## Main results

* `TauCeti.ChainComplex.cupCochain_comp_comp`: the cup product of cochains is natural in the
  pairing of the values.
* `TauCeti.ChainComplex.cup_homologyMap_linearYonedaObjMap`: the same on cohomology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Cochain

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {A B E : ChainComplex C ℕ} [A.HasTensor B] {M N P M' N' P' : C} {k : Type*} [CommSemiring k]
  [Linear k C] [MonoidalLinear k C]

/-- **Naturality of the cup product of cochains in the pairing**: if `g₁ : M ⟶ M'`,
`g₂ : N ⟶ N'` and `g : P ⟶ P'` intertwine the pairings, `(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`, then the cup
product along `μ'` of the cochains composed with `g₁` and `g₂` is the cup product along `μ`
composed with `g`. -/
theorem cupCochain_comp_comp (D : E ⟶ HomologicalComplex.tensorObj A B) {μ : M ⊗ N ⟶ P}
    {μ' : M' ⊗ N' ⟶ P'} {g₁ : M ⟶ M'} {g₂ : N ⟶ N'} {g : P ⟶ P'}
    (hμ : (g₁ ⊗ₘ g₂) ≫ μ' = μ ≫ g) (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M)
    (ψ : B.X q ⟶ N) :
    cupCochain k D μ' p q n h (φ ≫ g₁) (ψ ≫ g₂) = cupCochain k D μ p q n h φ ψ ≫ g := by
  rw [← cupCochain_whiskerLeft_comp, ← cupCochain_whiskerRight_comp, ← Category.assoc,
    ← tensorHom_def, hμ, cupCochain_apply, cupCochain_apply, Category.assoc, tensorCochain_comp]

end Cochain

section Cohomology

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  {A B E : ChainComplex C ℕ} [A.HasTensor B] {M N P M' N' P' : C} {k : Type*} [CommRing k]
  [Linear k C] [MonoidalLinear k C]

/-- **The change of cochain values carries cup products to cup products**: if `g₁ : M ⟶ M'`,
`g₂ : N ⟶ N'` and `g : P ⟶ P'` intertwine the pairings, `(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`, then the cup
product along `μ'` of the images of `a` and `b` under `g₁` and `g₂` is the image under `g` of
their cup product along `μ`. -/
theorem cup_homologyMap_linearYonedaObjMap (D : E ⟶ HomologicalComplex.tensorObj A B)
    {μ : M ⊗ N ⟶ P} {μ' : M' ⊗ N' ⟶ P'} {g₁ : M ⟶ M'} {g₂ : N ⟶ N'} {g : P ⟶ P'}
    (hμ : (g₁ ⊗ₘ g₂) ≫ μ' = μ ≫ g) (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).homology p) (b : (B.linearYonedaObj k N).homology q) :
    cup k D μ' p q n h (homologyMap (A.linearYonedaObjMap k g₁) p a)
        (homologyMap (B.linearYonedaObjMap k g₂) q b) =
      homologyMap (E.linearYonedaObjMap k g) n (cup k D μ p q n h a b) := by
  obtain ⟨a, rfl⟩ := moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := moduleCat_homologyπ_surjective _ q b
  rw [_root_.ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply,
    _root_.ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply, cup_homologyπ,
    cup_homologyπ, _root_.ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply]
  congr 1
  apply moduleCat_iCycles_injective
  rw [iCycles_cupCycles, _root_.ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply,
    _root_.ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply,
    _root_.ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply, iCycles_cupCycles]
  exact cupCochain_comp_comp D hμ p q n h _ _

end Cohomology

end TauCeti.ChainComplex

end
