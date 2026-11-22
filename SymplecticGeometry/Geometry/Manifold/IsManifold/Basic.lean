/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Instances for smooth manifolds and their tangent spaces

Two instances that Mathlib's `Mathlib/Geometry/Manifold/IsManifold/Basic.lean` lacks in a form
that instance search finds.

* `ENat.instLEInftyInftyAddOne`: the smoothness exponent `∞ + 1` is at most `∞` (the two are
  equal). With Mathlib's instances deducing `C^a` structures from `C^∞` ones for `a ≤ ∞`, a
  `C^∞` manifold `[IsManifold I ∞ M]` is then a `C^(∞ + 1)` manifold for instance search, and
  likewise for `C^∞` vector bundles and Lie groups. Mathlib states the smoothness of the tangent
  bundle and of Lie brackets for `C^(n + 1)` manifolds, so `n = ∞` needs this.
* `TangentSpace.instIsNormableSpace`: the tangent space `TangentSpace I x` is a normable space.
  Mathlib derives `instIsNormableSpaceTangentSpace` with `TangentSpace`, but the type of that
  instance carries the module structure of the model space `E` (`NormedSpace.toModule`) instead
  of the one of the tangent space (`instModuleTangentSpace`). The two agree only after
  unfolding `TangentSpace`, which instance search does not do, so it never applies. The instance
  here has the type that instance search looks for. It is the local instance of Tau Ceti's
  `Geometry/Manifold/Riemannian/Induced.lean` and `Geometry/Symplectic/Manifold/Flat.lean`,
  made global.
-/

public section

open scoped ContDiff Manifold

namespace ENat

/-- The smoothness exponent `∞ + 1` is at most `∞`, so that Mathlib's instances give
`C^(∞ + 1)` structures from `C^∞` ones. -/
instance instLEInftyInftyAddOne : LEInfty (∞ + 1) := ⟨by simp⟩

end ENat

namespace TangentSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The tangent space of a manifold at a point is a normable space, since the model space is
one. -/
instance instIsNormableSpace (x : M) : IsNormableSpace 𝕜 (TangentSpace I x) :=
  instIsNormableSpaceTangentSpace I x

end TangentSpace

end
