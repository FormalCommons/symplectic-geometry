/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Monoidal
public import TauCeti.Algebra.Homology.Monoidal.Homology.Associativity

/-!
# Associativity of homology cross products followed by chain maps

Let `φ : K₁ ⊗ K₂ ⟶ L`, `ψ : L ⊗ K₃ ⟶ N`, `θ : K₂ ⊗ K₃ ⟶ L'` and `χ : K₁ ⊗ L' ⟶ N` be maps of
homological complexes such that the two composites `(φ ⊗ 𝟙) ≫ ψ` and `α ≫ (𝟙 ⊗ θ) ≫ χ` out of
`(K₁ ⊗ K₂) ⊗ K₃` are chain homotopic. Then the two products on homology that they define,
the homology cross product followed by the map induced by `φ` and then by `ψ`, and the same with
`θ` and `χ`, are associative (`HomologicalComplex.homologyCross_homologyMap_assoc_of_homotopy`).
This is how the associativity of the algebraic cross product
(Tau Ceti's `HomologicalComplex.homologyCross_assoc`) passes to products on homology defined
through maps of complexes, such as the shuffle maps of singular chains. The proof follows the
homology step of Tau Ceti's `TopCat.singularHomologyCross_assoc`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasZeroObject C] [CategoryWithHomology C]
  [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft T)]
  [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight T)]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- If `(φ ▷ K₃) ≫ ψ` and `(α_ K₁ K₂ K₃).hom ≫ (K₁ ◁ θ) ≫ χ` are chain homotopic, then the
products on homology `homologyCross K₁ K₂ ≫ homologyMap φ` and `homologyCross L K₃ ≫ homologyMap ψ`,
and `homologyCross K₂ K₃ ≫ homologyMap θ` and `homologyCross K₁ L' ≫ homologyMap χ`, satisfy
`(a × b) × d = a × (b × d)`. -/
@[reassoc]
theorem homologyCross_homologyMap_assoc_of_homotopy {K₁ K₂ K₃ L L' N : HomologicalComplex C c}
    (φ : K₁ ⊗ K₂ ⟶ L) (ψ : L ⊗ K₃ ⟶ N) (θ : K₂ ⊗ K₃ ⟶ L') (χ : K₁ ⊗ L' ⟶ N)
    (H : _root_.Homotopy ((φ ▷ K₃) ≫ ψ) ((α_ K₁ K₂ K₃).hom ≫ (K₁ ◁ θ) ≫ χ))
    (p q r pq qr n : I) (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n)
    (hn' : p + qr = n) :
    (homologyCross K₁ K₂ p q pq hpq ≫ homologyMap φ pq) ▷ K₃.homology r ≫
        homologyCross L K₃ pq r n hn ≫ homologyMap ψ n =
      (α_ (K₁.homology p) (K₂.homology q) (K₃.homology r)).hom ≫
        K₁.homology p ◁ (homologyCross K₂ K₃ q r qr hqr ≫ homologyMap θ qr) ≫
          homologyCross K₁ L' p qr n hn' ≫ homologyMap χ n := by
  have hL := homologyCross_naturality φ (𝟙 K₃) pq r n hn
  rw [homologyMap_id, tensorHom_id] at hL
  have hR := homologyCross_naturality (𝟙 K₁) θ p qr n hn'
  rw [homologyMap_id, id_tensorHom] at hR
  have hH : homologyMap (tensorHom φ (𝟙 K₃)) n ≫ homologyMap ψ n =
      homologyMap (α_ K₁ K₂ K₃).hom n ≫ homologyMap (tensorHom (𝟙 K₁) θ) n ≫
        homologyMap χ n := by
    have := H.homologyMap_eq n
    rw [homologyMap_comp, homologyMap_comp, homologyMap_comp] at this
    -- `▷` and `◁` of complexes are the tensor products with identities, by definition
    exact this
  rw [comp_whiskerRight_assoc, reassoc_of% hL, whiskerLeft_comp_assoc, reassoc_of% hR]
  -- the homology of `K ⊗ L` is that of `HomologicalComplex.tensorObj K L` only up to unfolding
  refine (congrArg (homologyCross K₁ K₂ p q pq hpq ▷ K₃.homology r ≫
    homologyCross (K₁ ⊗ K₂) K₃ pq r n hn ≫ ·) hH).trans ?_
  exact homologyCross_assoc_assoc K₁ K₂ K₃ p q r pq qr n hpq hqr hn hn' _

end HomologicalComplex

end
