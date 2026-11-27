/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Derivatives into a product under restriction of scalars

Let `A` be an algebra over the field `R`. Tau Ceti's
`MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply` says that, where a map
between manifolds modelled on the trivial models over `A` is differentiable over `A`, its
derivatives for the trivial models over `R` and over `A` agree. This file proves the same for a
map into a product `N × N'`, with the product of the trivial models as target model:
`MDifferentiableAt.mfderiv_modelWithCornersSelf_prod_restrictScalars_apply`. Its proof follows
that of Tau Ceti's lemma, from `MDifferentiableAt.mfderiv_restrictScalars`, using that
restriction of scalars commutes with products of models (`ModelWithCorners.restrictScalars_prod`)
and takes trivial models to trivial models (`modelWithCornersSelf_restrictScalars`).

For instance, the real derivative of a holomorphic map into a product of complex manifolds is
its complex derivative.
-/

public section

open scoped Manifold

namespace MDifferentiableAt

variable (R : Type*) {A : Type*} [NontriviallyNormedField R] [NontriviallyNormedField A]
  [Algebra R A] {E : Type*} [NormedAddCommGroup E] [NormedSpace A E] [NormedSpace R E]
  [IsScalarTower R A E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace A F] [NormedSpace R F] [IsScalarTower R A F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace A F'] [NormedSpace R F']
  [IsScalarTower R A F'] {N' : Type*} [TopologicalSpace N'] [ChartedSpace F' N']

/-- At a point where a map `f` into a product `N × N'` is differentiable over the larger field
`A`, for the trivial model on the source and the product of the trivial models on the target,
its derivatives for the corresponding models over `R` and over `A` agree on every vector of
`E`. This is the analogue for a product target of Tau Ceti's
`MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply`. -/
theorem mfderiv_modelWithCornersSelf_prod_restrictScalars_apply {f : M → N × N'} {x : M}
    (hf : MDifferentiableAt 𝓘(A, E) (𝓘(A, F).prod 𝓘(A, F')) f x) (v : E) :
    mfderiv 𝓘(R, E) (𝓘(R, F).prod 𝓘(R, F')) f x v =
      mfderiv 𝓘(A, E) (𝓘(A, F).prod 𝓘(A, F')) f x v := by
  have h := DFunLike.congr_fun (hf.mfderiv_restrictScalars R) v
  rw [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars,
    modelWithCornersSelf_restrictScalars, modelWithCornersSelf_restrictScalars] at h
  exact h.trans (ContinuousLinearMap.restrictScalarsTangent_apply _ _)

end MDifferentiableAt

end
