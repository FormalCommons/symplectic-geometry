/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Basic facts about diffeomorphisms

Facts about Mathlib's diffeomorphisms `M ≃ₘ^n⟮I, I'⟯ M'` that Mathlib does not state: inverting a
diffeomorphism twice gives it back, a `C^n` diffeomorphism is a `C^m` one for `m ≤ n`, and two
empty manifolds are diffeomorphic even when their models differ.

Two empty manifolds are diffeomorphic, whatever their models: the empty map is smooth in both
directions. Mathlib's `Diffeomorph.empty` gives this only when both manifolds have the same model
with corners; this file allows two models. The empty open set `⊥ : Opens M` of a manifold is
such an empty manifold, by the instance `TopologicalSpace.Opens.isEmpty_bot` of
`Topology/Sets/Opens/Basic.lean`.

## Main results

* `Diffeomorph.symm_symm`, `Diffeomorph.symm_bijective`: `Diffeomorph.symm` is an involution.

## Main definitions

* `Diffeomorph.ofLE`: a `C^n` diffeomorphism as a `C^m` diffeomorphism, for `m ≤ n`.
* `Diffeomorph.ofIsEmpty`: the diffeomorphism `M ≃ₘ^n⟮I, I'⟯ M'` between empty manifolds, modelled
  on `I` and `I'`.

## Implementation notes

`Diffeomorph.symm_symm` and `Diffeomorph.symm_bijective` are Mathlib's `Equiv.symm_symm` and
`Equiv.symm_bijective`, for diffeomorphisms.

The definition `Diffeomorph.ofIsEmpty` is Mathlib's `Diffeomorph.empty`, with the model of the
target freed from that of the source. All of this file belongs upstream, `Diffeomorph.ofIsEmpty`
as a generalization of `Diffeomorph.empty`.
-/

public section

open scoped Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' H H' M M' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  {n : WithTop ℕ∞}

/-- Inverting a diffeomorphism twice gives it back. -/
@[simp]
theorem symm_symm (h : M ≃ₘ^n⟮I, I'⟯ M') : h.symm.symm = h :=
  rfl

/-- Inversion is a bijection from the diffeomorphisms `M → M'` to the diffeomorphisms
`M' → M`. -/
theorem symm_bijective :
    Function.Bijective (Diffeomorph.symm : (M ≃ₘ^n⟮I, I'⟯ M') → M' ≃ₘ^n⟮I', I⟯ M) :=
  Function.bijective_iff_has_inverse.2 ⟨_, symm_symm, symm_symm⟩

/-- A `C^n` diffeomorphism, seen as a `C^m` diffeomorphism for `m ≤ n`. -/
def ofLE {m : WithTop ℕ∞} (Φ : M ≃ₘ^n⟮I, I'⟯ M') (hmn : m ≤ n) : M ≃ₘ^m⟮I, I'⟯ M' where
  __ := Φ.toEquiv
  contMDiff_toFun := Φ.contMDiff.of_le hmn
  contMDiff_invFun := Φ.symm.contMDiff.of_le hmn

@[simp]
theorem coe_ofLE {m : WithTop ℕ∞} (Φ : M ≃ₘ^n⟮I, I'⟯ M') (hmn : m ≤ n) : ⇑(Φ.ofLE hmn) = Φ :=
  (rfl)

@[simp]
theorem ofLE_symm {m : WithTop ℕ∞} (Φ : M ≃ₘ^n⟮I, I'⟯ M') (hmn : m ≤ n) :
    (Φ.ofLE hmn).symm = Φ.symm.ofLE hmn :=
  (rfl)

variable [IsEmpty M] [IsEmpty M']

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
