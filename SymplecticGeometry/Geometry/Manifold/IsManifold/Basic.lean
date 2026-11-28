/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Instances and lemmas for smooth manifolds and their tangent spaces

An instance that Mathlib's `Mathlib/Geometry/Manifold/IsManifold/Basic.lean` lacks in a form
that instance search finds: the tangent space `TangentSpace I x` is a normable space
(`TangentSpace.instIsNormableSpace`). Mathlib derives `instIsNormableSpaceTangentSpace` with
`TangentSpace`, but the type of that instance carries the module structure of the model space `E`
(`NormedSpace.toModule`) instead of the one of the tangent space (`instModuleTangentSpace`). The
two agree only after unfolding `TangentSpace`, which instance search does not do, so it never
applies. The instance here has the type that instance search looks for. It is the local instance
of Tau Ceti's `Geometry/Manifold/Riemannian/Induced.lean` and
`Geometry/Symplectic/Manifold/Flat.lean`, made global.

The file also evaluates Mathlib's `tangentSpaceCast I x y`, which identifies the tangent spaces
at two points through the identity of the model space: `tangentSpaceCast_apply` says that it sends
each vector to itself. Tau Ceti's `TauCeti.tangentSpaceCast_self` covers only the case of a single
point, while `Filter.EventuallyEq.mfderiv_eq` inserts the cast between two points that are equal
only propositionally; rewriting with `tangentSpaceCast_apply` removes it there.
In the same way, `tangentSpaceCastModel_apply` and `tangentSpaceCastModel_symm_apply` evaluate
Mathlib's `tangentSpaceCastModel I x`, which identifies the tangent space at `x` with the model
space, and its inverse.

Last, three instances compare smoothness exponents in `ℕ∞ω` as a `Fact`: `ENat.fact_le_refl`
(`m ≤ m`), `ENat.fact_le_infty` (`m ≤ ∞`, from Mathlib's `ENat.LEInfty m`) and
`ENat.fact_le_omega` (`m ≤ ω`). They let an instance that gives a `C^m` structure from a `C^n` one
under `[Fact (m ≤ n)]` apply at `n = m`, `n = ∞` and `n = ω`.
-/

public section

open scoped ContDiff Manifold

namespace TangentSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The tangent space of a manifold at a point is a normable space, since the model space is
one. -/
instance instIsNormableSpace (x : M) : IsNormableSpace 𝕜 (TangentSpace I x) :=
  instIsNormableSpaceTangentSpace I x

end TangentSpace

section tangentSpaceCast

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The identification `tangentSpaceCast I x y` of the tangent spaces of a manifold at `x` and at
`y` sends each tangent vector at `x` to itself, as a vector of the model space, now read as a
tangent vector at `y`.

This is not a `simp` lemma: for `x ≠ y` its right-hand side is a vector of `TangentSpace I x` in
a place that expects one of `TangentSpace I y`, so rewriting with it stops other lemmas, such as
`map_smul`, from matching. Use it explicitly, with `rw` or `simp only`. -/
theorem tangentSpaceCast_apply (x y : M) (v : TangentSpace I x) : tangentSpaceCast I x y v = v :=
  (rfl)

/-- The identification `tangentSpaceCastModel I x` of the tangent space at `x` with the model space
sends each tangent vector to itself, read as a vector of the model space. -/
theorem tangentSpaceCastModel_apply (x : M) (v : TangentSpace I x) :
    tangentSpaceCastModel I x v = v :=
  (rfl)

/-- The inverse of `tangentSpaceCastModel I x` sends each vector of the model space to itself,
read as a tangent vector at `x`. -/
theorem tangentSpaceCastModel_symm_apply (x : M) (v : E) :
    (tangentSpaceCastModel I x).symm v = v :=
  (rfl)

end tangentSpaceCast

namespace ENat

/-- Every smoothness exponent is at most itself. -/
instance fact_le_refl (m : ℕ∞ω) : Fact (m ≤ m) := ⟨le_rfl⟩

/-- A smoothness exponent with `ENat.LEInfty` is at most `∞`. -/
instance fact_le_infty (m : ℕ∞ω) [h : LEInfty m] : Fact (m ≤ ∞) := ⟨h.out⟩

/-- Every smoothness exponent is at most `ω`. -/
instance fact_le_omega (m : ℕ∞ω) : Fact (m ≤ ω) := ⟨le_top⟩

end ENat

end
