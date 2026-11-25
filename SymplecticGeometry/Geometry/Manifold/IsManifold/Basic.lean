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
that instance search finds, and the evaluation lemmas of its identification of a tangent space
with the model space.

* `ENat.instLEInftyAddOne`: if the smoothness exponent `m` is at most `∞`, so is `m + 1`.
  With Mathlib's instances deducing `C^a` structures from `C^∞` ones for `a ≤ ∞`, a `C^∞`
  manifold `[IsManifold I ∞ M]` is then a `C^(m + 1)` manifold for instance search whenever
  `[LEInfty m]`, such as `C^(∞ + 1)` and `C^(1 + 1)`, and likewise for `C^∞` vector bundles and
  Lie groups. Mathlib states the smoothness of the tangent
  bundle and of Lie brackets for `C^(n + 1)` manifolds, so `n = ∞` needs this.
* `TangentSpace.instIsNormableSpace`: the tangent space `TangentSpace I x` is a normable space.
  Mathlib derives `instIsNormableSpaceTangentSpace` with `TangentSpace`, but the type of that
  instance carries the module structure of the model space `E` (`NormedSpace.toModule`) instead
  of the one of the tangent space (`instModuleTangentSpace`). The two agree only after
  unfolding `TangentSpace`, which instance search does not do, so it never applies. The instance
  here has the type that instance search looks for. It is the local instance of Tau Ceti's
  `Geometry/Manifold/Riemannian/Induced.lean` and `Geometry/Symplectic/Manifold/Flat.lean`,
  made global.
* `tangentSpaceCastModel_apply` and `tangentSpaceCastModel_symm_apply`: Mathlib's
  `tangentSpaceCastModel I x : TangentSpace I x ≃L[𝕜] E` and its inverse send each vector to
  itself. With them a term passes between a tangent space `TangentSpace I x`, such as the Lie
  algebra `GroupLieAlgebra I G = TangentSpace I 1` of a Lie group, and the model space `E`
  through a named equivalence, instead of by unfolding `TangentSpace`.
-/

public section

open scoped ContDiff Manifold

namespace ENat

/-- If the smoothness exponent `m` is at most `∞`, then so is `m + 1`, so that Mathlib's
instances give `C^(m + 1)` structures from `C^∞` ones. -/
instance instLEInftyAddOne (m : ℕ∞ω) [h : LEInfty m] : LEInfty (m + 1) := by
  obtain ⟨h⟩ := h
  lift m to ℕ∞ using ne_top_of_le_ne_top (by simp) h
  exact ⟨mod_cast le_top⟩

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

section TangentSpaceCastModel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The identification of the tangent space at `x` with the model space sends each tangent
vector to itself, read in the model space. -/
@[simp]
theorem tangentSpaceCastModel_apply (x : M) (v : TangentSpace I x) :
    tangentSpaceCastModel I x v = v :=
  rfl

/-- The inverse of the identification of the tangent space at `x` with the model space sends
each vector of the model space to itself, read as a tangent vector. -/
@[simp]
theorem tangentSpaceCastModel_symm_apply (x : M) (v : E) :
    (tangentSpaceCastModel I x).symm v = v :=
  rfl

end TangentSpaceCastModel

end
