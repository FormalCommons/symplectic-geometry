/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Diffeomorphisms between empty manifolds

Two empty manifolds are diffeomorphic, whatever their models: the empty map is smooth in both
directions. Mathlib's `Diffeomorph.empty` gives this only when both manifolds have the same model
with corners; this file allows two models. The empty open set `⊥ : Opens M` of a manifold is
such an empty manifold, by the instance `TopologicalSpace.Opens.isEmpty_bot` of
`Topology/Sets/Opens/Basic.lean`.

## Main definitions

* `Diffeomorph.ofIsEmpty`: the diffeomorphism `M ≃ₘ^n⟮I, I'⟯ M'` between empty manifolds, modelled
  on `I` and `I'`.

## Implementation notes

The definition is Mathlib's `Diffeomorph.empty`, with the model of the target freed from that of
the source. It belongs upstream as a generalization of that definition.
-/

public section

open scoped Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' H H' M M' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  {n : WithTop ℕ∞} [IsEmpty M] [IsEmpty M']

/-- The diffeomorphism between two empty manifolds, modelled on possibly different models with
corners `I` and `I'`. -/
def ofIsEmpty : M ≃ₘ^n⟮I, I'⟯ M' where
  __ := Equiv.equivOfIsEmpty M M'
  contMDiff_toFun x := isEmptyElim x
  contMDiff_invFun x := isEmptyElim x

@[simp]
theorem ofIsEmpty_toEquiv :
    (ofIsEmpty : M ≃ₘ^n⟮I, I'⟯ M').toEquiv = Equiv.equivOfIsEmpty M M' :=
  (rfl)

/-- There is exactly one diffeomorphism between two empty manifolds. -/
instance : Unique (M ≃ₘ^n⟮I, I'⟯ M') where
  default := ofIsEmpty
  uniq _ := ext fun x ↦ isEmptyElim x

end Diffeomorph

end
