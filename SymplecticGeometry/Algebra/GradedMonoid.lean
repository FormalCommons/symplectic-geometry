/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Changing the degree of a graded element along an equality

For a family of modules `A : ι → Type*`, transporting `x : A i` to `A j` along `h : i = j` by
`LinearEquiv.cast h` does not change it as an element of the graded monoid `GradedMonoid A`, nor
as an element of the direct sum `⨁ i, A i`.

## Main results

* `GradedMonoid.mk_linearEquivCast`: `GradedMonoid.mk j (LinearEquiv.cast h x)` is
  `GradedMonoid.mk i x`.
* `DirectSum.of_linearEquivCast`: `DirectSum.of A j (LinearEquiv.cast h x)` is
  `DirectSum.of A i x`.
-/

public section

namespace GradedMonoid

/-- Transporting an element of `A i` to `A j` along `h : i = j` by `LinearEquiv.cast` does not
change it as an element of the graded monoid. -/
theorem mk_linearEquivCast {R ι : Type*} [Semiring R] {A : ι → Type*}
    [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)] {i j : ι} (h : i = j) (x : A i) :
    GradedMonoid.mk j (LinearEquiv.cast (R := R) (M := A) h x) = GradedMonoid.mk i x := by
  cases h
  rfl

end GradedMonoid

namespace DirectSum

/-- Transporting an element of `A i` to `A j` along `h : i = j` by `LinearEquiv.cast` does not
change it as an element of the direct sum. -/
theorem of_linearEquivCast {R ι : Type*} [Semiring R] [DecidableEq ι] {A : ι → Type*}
    [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)] {i j : ι} (h : i = j) (x : A i) :
    DirectSum.of A j (LinearEquiv.cast (R := R) (M := A) h x) = DirectSum.of A i x := by
  cases h
  rfl

end DirectSum

end
