/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Topology.Algebra.Lie.Bracket

/-!
# The norm on the Lie algebra of a Lie group

Mathlib's `GroupLieAlgebra I G` is the tangent space of `G` at the identity, which is the model
space `E` of `G` by definition, but carries no norm. Differential forms with values in a vector
space, such as the connection forms of principal bundles and the Maurer–Cartan form, need a
normed space of values. This file gives `GroupLieAlgebra I G` the norm of `E`, once, so that every
file which takes forms with values in the Lie algebra uses the same instances. The underlying
additive group, module and topology are those of the tangent space, so the instances agree with
the ones that Mathlib puts on `TangentSpace I 1`. Two examples at the end check that, with these
instances, Mathlib's bracket and Tau Ceti's adjoint action rewrite inside Tau Ceti's forms.

## Implementation notes

The metric is that of `E` with its topology replaced (`PseudoMetricSpace.replaceTopology`) by the
topology instance of the tangent space, and the additive group is that of the tangent space. Both
are equal to those of `E`, but only up to unfolding `TangentSpace`; stating them this way makes
them agree at instance transparency, so that lemmas about continuous linear maps of the Lie
algebra, such as Tau Ceti's adjoint action, rewrite in terms built with this norm.

The two instances are scoped to the namespace `GroupLieAlgebra` (`open scoped GroupLieAlgebra`)
rather than global, as Mathlib does for `normedAddCommGroupTangentSpaceVectorSpace`. Since
`GroupLieAlgebra I G` is reducible to `TangentSpace I 1`, a global instance would put the norm of
`E` on the tangent space at the identity of every Lie group, and would win there over the norm of
a Riemannian metric on the tangent bundle, which differs from it, so that the tangent space at `1`
would carry two norms that are not definitionally equal.
Their bodies are exposed, so that the instances unfold to the tangent-space ones in other
files too.
-/

public section

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

namespace GroupLieAlgebra

/-- The Lie algebra of a Lie group carries the norm of the model space.

Not a global instance: see the module docstring. -/
@[expose, instance_reducible]
def instNormedAddCommGroup : NormedAddCommGroup (GroupLieAlgebra I G) :=
  let m : PseudoMetricSpace (GroupLieAlgebra I G) :=
    (inferInstanceAs (PseudoMetricSpace E) : PseudoMetricSpace E).replaceTopology
      (U := instTopologicalSpaceTangentSpace I (1 : G)) rfl
  { (inferInstanceAs (NormedAddCommGroup E) : NormedAddCommGroup E) with
    toPseudoMetricSpace := m
    toAddCommGroup := instAddCommGroupTangentSpace I (1 : G) }

scoped[GroupLieAlgebra] attribute [instance] GroupLieAlgebra.instNormedAddCommGroup

/-- The Lie algebra of a Lie group is a normed space, with the norm of the model space.

Not a global instance: see the module docstring. -/
@[expose, instance_reducible]
def instNormedSpace : NormedSpace 𝕜 (GroupLieAlgebra I G) :=
  inferInstanceAs (NormedSpace 𝕜 E)

scoped[GroupLieAlgebra] attribute [instance] GroupLieAlgebra.instNormedSpace

end GroupLieAlgebra

/-! ### Tests: forms with values in the Lie algebra

With the scoped instances above, Mathlib's bracket and Tau Ceti's adjoint action combine with Tau
Ceti's vector-valued forms without an instance mismatch: the bracket wedge `[A ∧ A]` of a
Lie-algebra-valued one-form `A` evaluates to `2 [A v, A w]`, and the adjoint action changes the
values of `A`. -/

section Tests

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff GroupLieAlgebra

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]

example (A : SmoothForm IM M (GroupLieAlgebra IG G) 1) (x : M) (v w : TangentSpace IM x) :
    (SmoothForm.wedgeWith (lieL ℝ _ _) A A).val x ![v, w] =
      (2 : ℕ) • ⁅A.val x ![v], A.val x ![w]⁆ := by
  rw [SmoothForm.wedgeWith_apply_one_one, lieL_apply, lieL_apply, ← lie_skew (A.val x ![w]),
    sub_neg_eq_add, two_smul]

example (g : G) (A : SmoothForm IM M (GroupLieAlgebra IG G) 1) (x : M)
    (v : TangentSpace IM x) :
    (SmoothForm.mapCoeff (adjointContinuousLinearMap g) A).val x ![v] =
      adjointContinuousLinearMap g (A.val x ![v]) := by
  rw [SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply]

end Tests

end
