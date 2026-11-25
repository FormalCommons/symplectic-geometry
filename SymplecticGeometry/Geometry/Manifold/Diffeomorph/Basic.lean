/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Diffeomorphisms between empty manifolds, and translations

Two empty manifolds are diffeomorphic, whatever their models: the empty map is smooth in both
directions. Mathlib's `Diffeomorph.empty` gives this only when both manifolds have the same model
with corners; this file allows two models. The empty open set `⊥ : Opens M` of a manifold is
such an empty manifold, by the instance `TopologicalSpace.Opens.isEmpty_bot` of
`Topology/Sets/Opens/Basic.lean`.

The file also gives the translation `z ↦ z - p` of a normed space as a diffeomorphism for the
model `𝓘(𝕜, E)`. Mathlib's `Diffeomorph.vadd` does not give it, since `E` has no
`ContMDiffVAdd` instance for that model.

## Main definitions

* `Diffeomorph.ofIsEmpty`: the diffeomorphism `M ≃ₘ^n⟮I, I'⟯ M'` between empty manifolds, modelled
  on `I` and `I'`.
* `Diffeomorph.subRight 𝕜 n p`: the translation `z ↦ z - p` of a normed space `E`, as a
  diffeomorphism `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E` with inverse `z ↦ z + p`.

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

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {n : WithTop ℕ∞}

variable (𝕜 n) in
/-- The translation `z ↦ z - p` of a normed space `E`, as a diffeomorphism of `E` for the model
`𝓘(𝕜, E)`. Its inverse is `z ↦ z + p`. -/
def subRight (p : E) : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E where
  toEquiv := Equiv.subRight p
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

@[simp]
theorem subRight_toEquiv (p : E) : (subRight 𝕜 n p).toEquiv = Equiv.subRight p :=
  (rfl)

@[simp]
theorem coe_subRight (p : E) : ⇑(subRight 𝕜 n p) = fun z ↦ z - p :=
  (rfl)

@[simp]
theorem coe_subRight_symm (p : E) : ⇑(subRight 𝕜 n p).symm = fun z ↦ z + p :=
  (rfl)

end Diffeomorph

end
