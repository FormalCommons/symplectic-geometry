/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Model fibres of vector bundles with equivalent fibres

The model fibre of a vector bundle is equivalent to each of its fibres, through Mathlib's
`VectorBundle.continuousLinearEquivAt`. So a continuous linear equivalence `E b ≃L[R] E' b` of the
fibres over one point `b` of two vector bundles, with models `F` and `F'`, gives one of the models,
`VectorBundle.modelEquiv b φ : F ≃L[R] F'`. In particular two vector bundles over a nonempty base
whose fibres are equivalent have models of the same dimension: `VectorBundle.finrank_model_eq`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (vector bundles and their isomorphisms).
-/

public section

open Bundle Module

namespace VectorBundle

variable {R : Type*} [NontriviallyNormedField R] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace R F]
  {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle R F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace R F']
  {E' : B → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module R (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [VectorBundle R F' E']

/-- The continuous linear equivalence `F ≃L[R] F'` of the models of two vector bundles `E` and
`E'` given by a continuous linear equivalence `φ : E b ≃L[R] E' b` of their fibres over `b`: the
composite `F ≃ E b ≃ E' b ≃ F'`, through the preferred trivializations at `b`. -/
noncomputable def modelEquiv (b : B) (φ : E b ≃L[R] E' b) : F ≃L[R] F' :=
  (continuousLinearEquivAt R F E b).symm.trans (φ.trans (continuousLinearEquivAt R F' E' b))

theorem modelEquiv_def (b : B) (φ : E b ≃L[R] E' b) :
    modelEquiv b φ =
      (continuousLinearEquivAt R F E b).symm.trans (φ.trans (continuousLinearEquivAt R F' E' b)) :=
  (rfl)

@[simp]
theorem modelEquiv_apply (b : B) (φ : E b ≃L[R] E' b) (v : F) :
    modelEquiv b φ v =
      continuousLinearEquivAt R F' E' b (φ ((continuousLinearEquivAt R F E b).symm v)) := by
  rw [modelEquiv_def, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply]

/-- Two vector bundles over a nonempty base whose fibres are equivalent, by continuous linear
equivalences `E b ≃L[R] E' b`, have models of the same dimension. -/
theorem finrank_model_eq [Nonempty B] (φ : ∀ b, E b ≃L[R] E' b) :
    finrank R F' = finrank R F :=
  (modelEquiv (F := F) (F' := F') _ (φ (Classical.arbitrary B))).toLinearEquiv.finrank_eq.symm

end VectorBundle

end
