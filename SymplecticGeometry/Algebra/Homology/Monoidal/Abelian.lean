/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The monoidal structure on chain complexes in an abelian category

Mathlib's `HomologicalComplex.monoidalCategory` makes `ChainComplex C ℕ` a monoidal category when
the tensor product of `C` preserves the finite coproducts that the tensor product of complexes
uses. This holds when `C` is abelian with an additive tensor product (`MonoidalPreadditive C`),
but instance search does not find the instance there. Each hypothesis of
`HomologicalComplex.monoidalCategory` is found on its own from `Abelian C` and
`MonoidalPreadditive C`, but the search for the whole instance goes over the default bound
`synthInstance.maxSize` (128) on the number of instances in a solution; it succeeds with a bound
of 256. With `Preadditive C`, `HasZeroObject C` and `HasFiniteCoproducts C` as hypotheses in
place of `Abelian C`, it succeeds within the default bound.

This file gives that instance as the scoped instance `ChainComplex.monoidalCategoryOfAbelian`,
active after `open scoped ChainComplex`. It is `HomologicalComplex.monoidalCategory` itself, so
the lemmas stated for that instance apply.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace ChainComplex

variable (C : Type*) [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]

/-- The monoidal structure on chain complexes in an abelian category with an additive tensor
product: Mathlib's `HomologicalComplex.monoidalCategory`, with its hypotheses found from
`Abelian C` and `MonoidalPreadditive C`. -/
scoped instance monoidalCategoryOfAbelian : MonoidalCategory (ChainComplex C ℕ) :=
  HomologicalComplex.monoidalCategory C (ComplexShape.down ℕ)

end ChainComplex

end
