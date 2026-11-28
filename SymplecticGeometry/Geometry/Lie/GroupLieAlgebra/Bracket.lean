/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Linearity of the bracket of a Lie group in its second argument

Mathlib's lemmas on the second argument of a bracket (`lie_zero`, `lie_neg`, `lie_add`,
`lie_sub`, `lie_smul`) are stated for a Lie module `M` over `L`. On `GroupLieAlgebra I G` they
apply when `LieGroup I (minSmoothness 𝕜 3) G` is a hypothesis. They do not match, unless `L` is
given explicitly, when that instance is derived from a hypothesis `LieGroup I ∞ G` through the
local instance `LieGroup.minSmoothness_of_isRCLikeNormedField`, as in many files of this library.
The lemmas on the first argument (`zero_lie`, `neg_lie`, `add_lie`, …) apply in both settings.

This file restates the lemmas on the second argument for `GroupLieAlgebra I G`, so that `rw` and
`simp` apply them in both settings.

## Main results

* `GroupLieAlgebra.lie_zero`: `⁅x, 0⁆ = 0`.
* `GroupLieAlgebra.lie_neg`: `⁅x, -y⁆ = -⁅x, y⁆`.
* `GroupLieAlgebra.lie_add`: `⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆`.
* `GroupLieAlgebra.lie_sub`: `⁅x, y - z⁆ = ⁅x, y⁆ - ⁅x, z⁆`.
* `GroupLieAlgebra.lie_smul`: `⁅x, c • y⁆ = c • ⁅x, y⁆`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness 𝕜 3) G]

namespace GroupLieAlgebra

/-! The `simpNF` linter reports that `simp` proves each lemma below by Mathlib's lemma of the same
name. That holds under a hypothesis `LieGroup I (minSmoothness 𝕜 3) G`, but Mathlib's lemmas do
not fire when that instance comes from `LieGroup.minSmoothness_of_isRCLikeNormedField`, and these
do; so they keep `@[simp]`, with `nolint simpNF`. -/

/-- The bracket of the Lie algebra of a Lie group vanishes when its second argument does. -/
@[simp, nolint simpNF]
protected theorem lie_zero (x : GroupLieAlgebra I G) : ⁅x, (0 : GroupLieAlgebra I G)⁆ = 0 :=
  _root_.lie_zero x

/-- The bracket of the Lie algebra of a Lie group commutes with negation of its second
argument. -/
@[simp, nolint simpNF]
protected theorem lie_neg (x y : GroupLieAlgebra I G) : ⁅x, -y⁆ = -⁅x, y⁆ :=
  _root_.lie_neg x y

/-- The bracket of the Lie algebra of a Lie group is additive in its second argument. -/
@[simp, nolint simpNF]
protected theorem lie_add (x y z : GroupLieAlgebra I G) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ :=
  _root_.lie_add x y z

/-- The bracket of the Lie algebra of a Lie group commutes with subtraction in its second
argument. -/
@[simp, nolint simpNF]
protected theorem lie_sub (x y z : GroupLieAlgebra I G) :
    ⁅x, y - z⁆ = ⁅x, y⁆ - ⁅x, z⁆ :=
  _root_.lie_sub x y z

/-- The bracket of the Lie algebra of a Lie group commutes with scalar multiplication of its
second argument. -/
@[simp, nolint simpNF]
protected theorem lie_smul (c : 𝕜) (x y : GroupLieAlgebra I G) :
    ⁅x, c • y⁆ = c • ⁅x, y⁆ :=
  _root_.lie_smul c x y

end GroupLieAlgebra

end
