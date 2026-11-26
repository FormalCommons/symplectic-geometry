/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# A covariant derivative from local ones, each taken at its centre

Both conditions of Mathlib's `IsCovariantDerivativeOn`, additivity and the Leibniz rule, are
conditions at a single point. So if `cov b` is a covariant derivative on a set `U b` that contains
`b`, for every point `b` of the base, the operator that takes at `x` the value of `cov x`,
`σ ↦ (x ↦ cov x σ x)`, is a covariant derivative on the whole base. No comparison of the local
operators on the overlaps of the sets `U b` is needed.

This complements Mathlib's `CovariantDerivative.ofIsCovariantDerivativeOnOfOpenCover`, which
glues one operator that is a covariant derivative on each set of a cover.

## Main definitions

* `CovariantDerivative.ofIsCovariantDerivativeOnOfMem`: the covariant derivative
  `σ x ↦ cov x σ x`, for local covariant derivatives `cov b` on sets `U b ∋ b`.
-/

public section

noncomputable section

open Bundle

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/-- The covariant derivative that takes at each point `x` the value of a local covariant
derivative `cov x`, defined on a set `U x` that contains `x`: it sends a section `σ` to
`x ↦ cov x σ x`. -/
def ofIsCovariantDerivativeOnOfMem
    {cov : M → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {U : M → Set M}
    (hcov : ∀ b, IsCovariantDerivativeOn F (cov b) (U b)) (hU : ∀ b, b ∈ U b) :
    CovariantDerivative I F V where
  toFun σ x := cov x σ x
  isCovariantDerivativeOnUniv :=
    { add := fun hσ hσ' _ ↦ (hcov _).add hσ hσ' (hU _)
      leibniz := fun hσ hg _ ↦ (hcov _).leibniz hσ hg (hU _) }

/-- `ofIsCovariantDerivativeOnOfMem hcov hU` takes at `x` the value of `cov x`. -/
@[simp]
theorem ofIsCovariantDerivativeOnOfMem_apply
    {cov : M → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {U : M → Set M}
    (hcov : ∀ b, IsCovariantDerivativeOn F (cov b) (U b)) (hU : ∀ b, b ∈ U b)
    (σ : Π x : M, V x) (x : M) :
    ofIsCovariantDerivativeOnOfMem hcov hU σ x = cov x σ x :=
  (rfl)

end CovariantDerivative

end
