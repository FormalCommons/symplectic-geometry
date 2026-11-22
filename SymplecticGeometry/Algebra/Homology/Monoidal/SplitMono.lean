/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensor products of degreewise split monomorphisms

If two morphisms `f : K₁ ⟶ L₁` and `g : K₂ ⟶ L₂` of homological complexes are split
monomorphisms in each degree, so is their tensor product `f ⊗ g : K₁ ⊗ K₂ ⟶ L₁ ⊗ L₂`
(`HomologicalComplex.isSplitMono_tensorHom_f`): in degree `n` a retraction is the sum, over the
summands `K₁ₚ ⊗ K₂_q` with `p + q = n`, of the tensor products of the retractions. The splittings
need not commute with the differentials.

This is what Tau Ceti's `HomologicalComplex.shortExact_tensorRightShortComplex` and
`HomologicalComplex.shortExact_tensorLeftShortComplex` ask of the first map of a short exact
sequence, so that they apply again to a sequence that is already tensored with a complex.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]
  [DecidableEq I]

/-- The tensor product of two morphisms of complexes that are split monomorphisms in each degree
is a split monomorphism in each degree. -/
lemma isSplitMono_tensorHom_f {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂] [∀ p, IsSplitMono (f.f p)] [∀ q, IsSplitMono (g.f q)]
    (n : I) : IsSplitMono ((tensorHom f g).f n) :=
  .mk' { retraction := mapBifunctorDesc fun p q h ↦
           (retraction (f.f p) ⊗ₘ retraction (g.f q)) ≫ ιTensorObj K₁ K₂ p q n h
         id := mapBifunctor.hom_ext fun p q h ↦ by
           simp [tensorHom, ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc] }

end HomologicalComplex

end
