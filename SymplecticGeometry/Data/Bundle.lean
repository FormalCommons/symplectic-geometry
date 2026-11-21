/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Bundle
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Equations in the fibres of a pull-back bundle

The fibre of the pull-back bundle `f *ᵖ E` at `y` is, by definition, the fibre `E (f y)`. A term
of `E (f y)` can therefore be read as a vector of `(f *ᵖ E) y`, and the reverse, so equations and
operations can be taken at either type. Since `Bundle.Pullback` is not reducible, `simp` does
not see through it: a lemma about vectors of `E (f y)` does not apply to a vector of type
`(f *ᵖ E) y`, nor the reverse. The lemmas here move terms to one of the two types.

## Main results

* `Bundle.Pullback.eq_iff`: an equation stated at the type `(f *ᵖ E) y` between terms of type
  `E (f y)` is the same equation at `E (f y)`, where `simp` can close it.
* `Bundle.Pullback.neg_fiber`: the negative in `E (f y)` of a vector of type `(f *ᵖ E) y` is its
  negative in `(f *ᵖ E) y`, for Tau Ceti's group structure `Bundle.Pullback.instAddCommGroup`.

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

/-- The negative, taken in `E (f y)`, of a vector `v` of the fibre of `f *ᵖ E` at `y` is the
negative of `v` in that fibre. -/
@[simp]
theorem neg_fiber [∀ b, AddCommGroup (E b)] (v : (f *ᵖ E) y) :
    @Eq ((f *ᵖ E) y) (@Neg.neg (E (f y)) _ v) (-v) := (rfl)

end Bundle.Pullback

end
