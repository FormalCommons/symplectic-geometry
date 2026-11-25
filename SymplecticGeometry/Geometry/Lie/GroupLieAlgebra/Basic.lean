/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The Lie algebra of a Lie group as a vector space

Mathlib's `GroupLieAlgebra I G` is the tangent space of `G` at the identity, which is the model
vector space `E` of `G` by definition. This file records the consequences of that identification
for the linear algebra of `GroupLieAlgebra I G`, so that other files use them instead of unfolding
`GroupLieAlgebra` and `TangentSpace`.

## Main results

* `GroupLieAlgebra.finrank_eq`: the dimension of the Lie algebra is that of the model space.
  Tau Ceti's `groupLieAlgebraEquivModelVectorSpace` gives the same identification over `ℝ`, as a
  linear equivalence.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

namespace GroupLieAlgebra

/-- The Lie algebra of a Lie group modelled on `E` has the dimension of `E`. -/
@[simp]
theorem finrank_eq : Module.finrank 𝕜 (GroupLieAlgebra I G) = Module.finrank 𝕜 E :=
  rfl

end GroupLieAlgebra

end
