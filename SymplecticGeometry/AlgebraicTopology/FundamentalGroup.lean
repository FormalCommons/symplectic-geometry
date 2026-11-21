/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.NotSimplyConnected

/-!
# Maps to the circle from spaces with trivial fundamental group

The fundamental group of the unit circle is nontrivial (`Circle.nontrivial_fundamentalGroup`,
from `π₁(S¹) ≅ ℤ`). So no continuous map `f : X → S¹` out of a space whose fundamental group at
`x` is trivial can be surjective on `π₁`, whatever `f` is.

This is how the isomorphisms `π₁(U(n)) ≅ π₁(S¹)`, induced by the determinant, and
`π₁(Sp(2n)) ≅ π₁(S¹)`, induced by the Maslov phase, fail for `n = 0`: there the groups are a
point.

## Main results

* `FundamentalGroup.not_surjective_map_circle_of_subsingleton`: if `π₁(X, x)` is trivial, then
  no continuous map `X → S¹` is surjective on `π₁` at `x`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.7
  (`π₁(S¹) ≅ ℤ`).
-/

public section

namespace FundamentalGroup

/-- If the fundamental group of `X` at `x` is trivial, then no continuous map `f : X → S¹`
induces a surjection `π₁(X, x) → π₁(S¹, f x)`, since `π₁(S¹) ≅ ℤ` is nontrivial. -/
theorem not_surjective_map_circle_of_subsingleton {X : Type*} [TopologicalSpace X] (x : X)
    [Subsingleton (FundamentalGroup X x)] (f : C(X, Circle)) :
    ¬ Function.Surjective (FundamentalGroup.map f x) := fun h ↦
  have := Circle.nontrivial_fundamentalGroup (f x)
  not_subsingleton _ h.subsingleton

end FundamentalGroup

end
