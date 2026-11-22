/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.Bundle

/-!
# Equations and negated functions in the fibres of a pull-back bundle

The fibre of the pull-back bundle `f *ᵖ E` at `y` is, by definition, the fibre `E (f y)`. A term
of `E (f y)` can therefore be read as a vector of `(f *ᵖ E) y`, and an equation between two such
terms can be stated at either type. Since `Bundle.Pullback` is not reducible, `simp` does not see
through it, and an equation stated at the type `(f *ᵖ E) y` between terms of type `E (f y)` is
not closed by `simp` even when both sides agree. `Bundle.Pullback.eq_iff` moves such an equation
to the type `E (f y)`, and `Bundle.Pullback.eq_fiber_iff` moves an equation stated at the type
`E (f y)` between terms of type `(f *ᵖ E) y` to the type `(f *ᵖ E) y`. Each applies only where
the type of the equation differs from the type of its two sides, so between them `simp` states
such an equation at the type of its sides.

For the same reason `Pi.neg_apply`, `Pi.add_apply` and `Pi.smul_apply` do not evaluate `-g`,
`g + h` or `c • g`, for functions on one of the two types, at a vector of the other;
`Bundle.Pullback.neg_apply_fiber`, `add_apply_fiber` and `smul_apply_fiber`, and
`neg_apply_pullback`, `add_apply_pullback` and `smul_apply_pullback`, do.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
-/

public section

namespace Bundle.Pullback

variable {B B' : Type*} {E : B → Type*} {f : B' → B} {y : B'}

/-- An equation in the fibre of `f *ᵖ E` at `y` between two vectors of `E (f y)` is the same
equation in `E (f y)`. -/
@[simp]
theorem eq_iff {v w : E (f y)} : @Eq ((f *ᵖ E) y) v w ↔ v = w := Iff.rfl

/-- An equation in `E (f y)` between two vectors of the fibre of `f *ᵖ E` at `y` is the same
equation in that fibre. -/
@[simp]
theorem eq_fiber_iff {v w : (f *ᵖ E) y} : @Eq (E (f y)) v w ↔ v = w := Iff.rfl

section Neg

variable {β : Type*} [Neg β]

/-- The negative of a function `g` on `E (f y)`, applied to a vector `v` of the fibre of
`f *ᵖ E` at `y`, is `-g v`. This is `Pi.neg_apply` for a vector of the pull-back fibre. -/
@[simp]
theorem neg_apply_fiber (g : E (f y) → β) (v : (f *ᵖ E) y) : (-g) v = -g v := (rfl)

/-- The negative of a function `g` on the fibre of `f *ᵖ E` at `y`, applied to a vector `v` of
`E (f y)`, is `-g v`. This is `Pi.neg_apply` for a vector of `E (f y)`. -/
@[simp]
theorem neg_apply_pullback (g : (f *ᵖ E) y → β) (v : E (f y)) : (-g) v = -g v := (rfl)

end Neg

section Add

variable {β : Type*} [Add β]

/-- The sum of two functions `g` and `h` on `E (f y)`, applied to a vector `v` of the fibre of
`f *ᵖ E` at `y`, is `g v + h v`. This is `Pi.add_apply` for a vector of the pull-back fibre. -/
@[simp]
theorem add_apply_fiber (g h : E (f y) → β) (v : (f *ᵖ E) y) : (g + h) v = g v + h v := (rfl)

/-- The sum of two functions `g` and `h` on the fibre of `f *ᵖ E` at `y`, applied to a vector `v`
of `E (f y)`, is `g v + h v`. This is `Pi.add_apply` for a vector of `E (f y)`. -/
@[simp]
theorem add_apply_pullback (g h : (f *ᵖ E) y → β) (v : E (f y)) : (g + h) v = g v + h v := (rfl)

end Add

section SMul

variable {α β : Type*} [SMul α β]

/-- The multiple `c • g` of a function `g` on `E (f y)`, applied to a vector `v` of the fibre of
`f *ᵖ E` at `y`, is `c • g v`. This is `Pi.smul_apply` for a vector of the pull-back fibre. -/
@[simp]
theorem smul_apply_fiber (c : α) (g : E (f y) → β) (v : (f *ᵖ E) y) : (c • g) v = c • g v :=
  (rfl)

/-- The multiple `c • g` of a function `g` on the fibre of `f *ᵖ E` at `y`, applied to a vector
`v` of `E (f y)`, is `c • g v`. This is `Pi.smul_apply` for a vector of `E (f y)`. -/
@[simp]
theorem smul_apply_pullback (c : α) (g : (f *ᵖ E) y → β) (v : E (f y)) : (c • g) v = c • g v :=
  (rfl)

end SMul

end Bundle.Pullback

end
