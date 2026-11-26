/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The automorphism `𝟙 + n` for an endomorphism of square zero

In a preadditive category, an endomorphism `n` of `X` with `n ≫ n = 0` gives the automorphism
`CategoryTheory.Preadditive.idAddIso n hn` of `X`, with `𝟙 X + n` as morphism and `𝟙 X - n` as
inverse. This is the categorical form of the unit `1 + n` of a ring with `n * n = 0` (compare
`IsNilpotent.isUnit_one_add`).

Elementary row and column operations on block matrices are of this form. For a binary bicone
`b` on `X₁` and `X₂`, `b.unipotentUpper r` for `r : X₁ ⟶ X₂` is `𝟙 + b.fst ≫ r ≫ b.inr`, with
block matrix `[[1, r], [0, 1]]`, and `b.unipotentLower r` for `r : X₂ ⟶ X₁` is
`𝟙 + b.snd ≫ r ≫ b.inl`, with block matrix `[[1, 0], [r, 1]]`. They follow the names and the
orientation of Mathlib's `Biprod.unipotentUpper` and `Biprod.unipotentLower`, which are the same
matrices on the chosen biproduct `X₁ ⊞ X₂`, but are stated for any bicone.

## Main definitions and results

* `CategoryTheory.Preadditive.idAddIso`: the automorphism `𝟙 + n`, for `n ≫ n = 0`;
* `CategoryTheory.Preadditive.idAddIso_trans`: `(𝟙 + n) ≫ (𝟙 + m) = 𝟙 + (n + m)` when
  `n ≫ m = 0` and `m ≫ n = 0`;
* `CategoryTheory.Preadditive.trans_idAddIso`: moving `𝟙 + n` across an isomorphism conjugates
  `n`;
* `CategoryTheory.Limits.BinaryBicone.unipotentUpper` and
  `CategoryTheory.Limits.BinaryBicone.unipotentLower`: the block unitriangular automorphisms of the
  point of a binary bicone;
* `CategoryTheory.Limits.BinaryBiproduct.bicone_unipotentUpper` and
  `CategoryTheory.Limits.BinaryBiproduct.bicone_unipotentLower`: on the chosen biproduct, they are
  Mathlib's `Biprod.unipotentUpper` and `Biprod.unipotentLower`.
-/

public section

namespace CategoryTheory.Preadditive

variable {C : Type*} [Category C] [Preadditive C] {X Y : C}

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

/-- `𝟙 X + 0` is the identity. -/
@[simp]
theorem idAddIso_zero : idAddIso (0 : X ⟶ X) (by simp) = Iso.refl X := by
  ext
  simp

/-- If `n` and `m` square to zero and `n ≫ m = 0 = m ≫ n`, then `(𝟙 X + n) ≫ (𝟙 X + m)` is
`𝟙 X + (n + m)`. -/
theorem idAddIso_trans {n m : X ⟶ X} (hn : n ≫ n = 0) (hm : m ≫ m = 0) (hnm : n ≫ m = 0)
    (hmn : m ≫ n = 0) :
    idAddIso n hn ≪≫ idAddIso m hm = idAddIso (n + m) (by simp [hn, hm, hnm, hmn]) := by
  ext
  simp [hnm, add_assoc]

/-- Composing an isomorphism `f : X ≅ Y` with `𝟙 Y + n` is composing `𝟙 X + f ≫ n ≫ f⁻¹`
with `f`. -/
theorem trans_idAddIso (f : X ≅ Y) {n : Y ⟶ Y} (hn : n ≫ n = 0) :
    f ≪≫ idAddIso n hn = idAddIso (f.hom ≫ n ≫ f.inv) (by simp [reassoc_of% hn]) ≪≫ f := by
  ext
  simp

end CategoryTheory.Preadditive

namespace CategoryTheory.Limits.BinaryBicone

open CategoryTheory.Preadditive

variable {C : Type*} [Category C] [Preadditive C] {X₁ X₂ : C} (b : BinaryBicone X₁ X₂)

/-- The upper unitriangular automorphism `𝟙 + b.fst ≫ r ≫ b.inr` of the point of a binary bicone,
for `r : X₁ ⟶ X₂`: the block matrix `[[1, r], [0, 1]]`, which adds `r` of the first component to
the second. -/
def unipotentUpper (r : X₁ ⟶ X₂) : b.pt ≅ b.pt :=
  idAddIso (b.fst ≫ r ≫ b.inr) (by simp)

@[simp]
theorem unipotentUpper_hom (r : X₁ ⟶ X₂) :
    (b.unipotentUpper r).hom = 𝟙 b.pt + b.fst ≫ r ≫ b.inr :=
  idAddIso_hom _ _

@[simp]
theorem unipotentUpper_inv (r : X₁ ⟶ X₂) :
    (b.unipotentUpper r).inv = 𝟙 b.pt - b.fst ≫ r ≫ b.inr :=
  idAddIso_inv _ _

/-- The inverse of the upper unitriangular automorphism by `r` is the one by `-r`. -/
theorem unipotentUpper_symm (r : X₁ ⟶ X₂) : (b.unipotentUpper r).symm = b.unipotentUpper (-r) := by
  ext : 1
  simp [sub_eq_add_neg]

@[simp]
theorem unipotentUpper_zero : b.unipotentUpper 0 = Iso.refl b.pt := by
  ext : 1
  simp

/-- Upper unitriangular automorphisms compose by adding their off-diagonal blocks. -/
theorem unipotentUpper_trans (r s : X₁ ⟶ X₂) :
    b.unipotentUpper r ≪≫ b.unipotentUpper s = b.unipotentUpper (r + s) := by
  ext : 1
  simp [add_assoc]

/-- The lower unitriangular automorphism `𝟙 + b.snd ≫ r ≫ b.inl` of the point of a binary bicone,
for `r : X₂ ⟶ X₁`: the block matrix `[[1, 0], [r, 1]]`, which adds `r` of the second component to
the first. -/
def unipotentLower (r : X₂ ⟶ X₁) : b.pt ≅ b.pt :=
  idAddIso (b.snd ≫ r ≫ b.inl) (by simp)

@[simp]
theorem unipotentLower_hom (r : X₂ ⟶ X₁) :
    (b.unipotentLower r).hom = 𝟙 b.pt + b.snd ≫ r ≫ b.inl :=
  idAddIso_hom _ _

@[simp]
theorem unipotentLower_inv (r : X₂ ⟶ X₁) :
    (b.unipotentLower r).inv = 𝟙 b.pt - b.snd ≫ r ≫ b.inl :=
  idAddIso_inv _ _

/-- The inverse of the lower unitriangular automorphism by `r` is the one by `-r`. -/
theorem unipotentLower_symm (r : X₂ ⟶ X₁) : (b.unipotentLower r).symm = b.unipotentLower (-r) := by
  ext : 1
  simp [sub_eq_add_neg]

@[simp]
theorem unipotentLower_zero : b.unipotentLower 0 = Iso.refl b.pt := by
  ext : 1
  simp

/-- Lower unitriangular automorphisms compose by adding their off-diagonal blocks. -/
theorem unipotentLower_trans (r s : X₂ ⟶ X₁) :
    b.unipotentLower r ≪≫ b.unipotentLower s = b.unipotentLower (r + s) := by
  ext : 1
  simp [add_assoc]

end CategoryTheory.Limits.BinaryBicone

namespace CategoryTheory.Limits.BinaryBiproduct

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {X₁ X₂ : C}

/-- On the chosen biproduct `X₁ ⊞ X₂`, the upper unitriangular automorphism by `r` is Mathlib's
`Biprod.unipotentUpper r`. -/
theorem bicone_unipotentUpper (r : X₁ ⟶ X₂) :
    (bicone X₁ X₂).unipotentUpper r = Biprod.unipotentUpper r := by
  ext : 1
  simp [Biprod.ofComponents, ← biprod.total]
  abel

/-- On the chosen biproduct `X₁ ⊞ X₂`, the lower unitriangular automorphism by `r` is Mathlib's
`Biprod.unipotentLower r`. -/
theorem bicone_unipotentLower (r : X₂ ⟶ X₁) :
    (bicone X₁ X₂).unipotentLower r = Biprod.unipotentLower r := by
  ext : 1
  simp [Biprod.ofComponents, ← biprod.total]
  abel

end CategoryTheory.Limits.BinaryBiproduct

end
