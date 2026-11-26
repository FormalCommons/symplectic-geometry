/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The automorphism `𝟙 + n` for an endomorphism of square zero

In a preadditive category, an endomorphism `n` of `X` with `n ≫ n = 0` gives the automorphism
`CategoryTheory.Preadditive.idAddIso n hn` of `X`, with `𝟙 X + n` as morphism and `𝟙 X - n` as
inverse. This is the categorical form of the unit `1 + n` of a ring with `n * n = 0` (compare
`IsNilpotent.isUnit_one_add`). Elementary row and column operations on block matrices are of
this form.
-/

public section

namespace CategoryTheory.Preadditive

variable {C : Type*} [Category C] [Preadditive C] {X : C}

/-- For an endomorphism `n` of `X` with `n ≫ n = 0`, the automorphism `𝟙 X + n` of `X`, with
inverse `𝟙 X - n`. -/
def idAddIso (n : X ⟶ X) (hn : n ≫ n = 0) : X ≅ X where
  hom := 𝟙 X + n
  inv := 𝟙 X - n
  hom_inv_id := by simp [hn]
  inv_hom_id := by simp [hn]

@[simp]
theorem idAddIso_hom (n : X ⟶ X) (hn : n ≫ n = 0) : (idAddIso n hn).hom = 𝟙 X + n :=
  (rfl)

@[simp]
theorem idAddIso_inv (n : X ⟶ X) (hn : n ≫ n = 0) : (idAddIso n hn).inv = 𝟙 X - n :=
  (rfl)

/-- The inverse of `𝟙 X + n` is `𝟙 X + (-n)`. -/
theorem idAddIso_symm (n : X ⟶ X) (hn : n ≫ n = 0) :
    (idAddIso n hn).symm = idAddIso (-n) (by simp [hn]) := by
  ext
  simp [sub_eq_add_neg]

end CategoryTheory.Preadditive

end
