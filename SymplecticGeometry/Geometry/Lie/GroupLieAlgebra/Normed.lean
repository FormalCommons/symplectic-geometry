/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# The norm on the Lie algebra of a Lie group

Mathlib's `GroupLieAlgebra I G` is the tangent space of `G` at the identity, which is the model
space `E` of `G` by definition, but carries no norm. Differential forms with values in a vector
space, such as the connection forms of principal bundles and the Maurer–Cartan form, need a
normed space of values. This file gives `GroupLieAlgebra I G` the norm of `E`, once, so that every
file which takes forms with values in the Lie algebra uses the same instances. The underlying
additive group, module and topology are those of the tangent space, so the instances agree with
the ones that Mathlib puts on `TangentSpace I 1`.

## Implementation notes

The metric is that of `E` with its topology replaced (`PseudoMetricSpace.replaceTopology`) by the
topology instance of the tangent space, and the additive group is that of the tangent space. Both
are equal to those of `E`, but only up to unfolding `TangentSpace`; stating them this way makes
them agree at instance transparency, so that lemmas about continuous linear maps of the Lie
algebra, such as Tau Ceti's adjoint action, rewrite in terms built with this norm.
-/

public section

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

namespace GroupLieAlgebra

/-- The Lie algebra of a Lie group carries the norm of the model space. -/
instance instNormedAddCommGroup : NormedAddCommGroup (GroupLieAlgebra I G) :=
  let m : PseudoMetricSpace (GroupLieAlgebra I G) :=
    (inferInstanceAs (PseudoMetricSpace E) : PseudoMetricSpace E).replaceTopology
      (U := instTopologicalSpaceTangentSpace I (1 : G)) rfl
  { (inferInstanceAs (NormedAddCommGroup E) : NormedAddCommGroup E) with
    toPseudoMetricSpace := m
    toAddCommGroup := instAddCommGroupTangentSpace I (1 : G) }

/-- The Lie algebra of a Lie group is a normed space, with the norm of the model space. -/
instance instNormedSpace : NormedSpace 𝕜 (GroupLieAlgebra I G) :=
  inferInstanceAs (NormedSpace 𝕜 E)

end GroupLieAlgebra

end
