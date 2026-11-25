/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Basic

/-!
# The neck of a connected sum

The two punctured summands of a connected sum `TauCeti.ConnectedSum e₁ e₂` overlap in the neck,
a copy of the punctured model space `{0}ᶜ ⊆ E`. This file gives the two maps of the neck into
the punctured summands and identifies it with the overlap.

## Main definitions

* `TauCeti.ConnectedSum.neckInl`: the map `v ↦ e₁ v` from `{0}ᶜ ⊆ E` to the first punctured
  summand.
* `TauCeti.ConnectedSum.neckInr`: the map `v ↦ e₂ (inversion 0 1 v)` from `{0}ᶜ ⊆ E` to the
  second punctured summand.
* `TauCeti.ConnectedSum.neckHomeomorph`: for open embeddings `e₁` and `e₂`, the homeomorphism
  from `{0}ᶜ ⊆ E` onto the overlap `range inl ∩ range inr` of the two punctured summands in the
  connected sum, given by `v ↦ inl (neckInl v)`.

## Main results

* `TauCeti.ConnectedSum.inl_neckInl_eq_inr_neckInr`: the two maps of the neck agree in the
  connected sum.

The homeomorphism `neckHomeomorph` combines the embedding of the neck and the computation of its
range that Tau Ceti's `TauCeti/Geometry/Manifold/ConnectedSum/FundamentalGroup.lean` makes as
the private declarations `TauCeti.ConnectedSum.neckMap`, `TauCeti.ConnectedSum.isEmbedding_neckMap`
and `TauCeti.ConnectedSum.range_neckMap`; its proof adapts theirs.

## References

* [A. Kosinski, *Differential Manifolds*][Kosinski1993], Chapter VI, Section 1.
-/

public section

open Set Function Topology EuclideanGeometry

namespace TauCeti.ConnectedSum

variable {E M N : Type*} [NormedAddCommGroup E]
  [TopologicalSpace M] [T1Space M] [TopologicalSpace N] [T1Space N]
  {e₁ : E → M} {e₂ : E → N}

/-- The map `v ↦ e₁ v` from the punctured model space to the first punctured summand. -/
def neckInl (h₁ : IsOpenEmbedding e₁) : C(({0}ᶜ : Set E), puncture e₁) where
  toFun v := ⟨e₁ v, mem_puncture.2 (h₁.injective.ne v.property)⟩
  continuous_toFun := (h₁.continuous.comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_neckInl_apply (h₁ : IsOpenEmbedding e₁) (v : ({0}ᶜ : Set E)) :
    (neckInl h₁ v : M) = e₁ v :=
  (rfl)

variable [InnerProductSpace ℝ E]

/-- The map `v ↦ e₂ (inversion 0 1 v)` from the punctured model space to the second punctured
summand. -/
noncomputable def neckInr (h₂ : IsOpenEmbedding e₂) : C(({0}ᶜ : Set E), puncture e₂) where
  toFun v := ⟨e₂ (inversion 0 1 v), apply_inversion_mem_puncture h₂.injective v.property⟩
  continuous_toFun := (h₂.continuous.comp (continuous_const.inversion continuous_const
    continuous_subtypeVal fun v ↦ v.property)).subtype_mk _

@[simp]
theorem coe_neckInr_apply (h₂ : IsOpenEmbedding e₂) (v : ({0}ᶜ : Set E)) :
    (neckInr h₂ v : N) = e₂ (inversion 0 1 v) :=
  (rfl)

/-- The two maps of the neck agree in the connected sum. -/
theorem inl_neckInl_eq_inr_neckInr (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (v : ({0}ᶜ : Set E)) : inl e₁ e₂ (neckInl h₁ v) = inr e₁ e₂ (neckInr h₂ v) :=
  inl_eq_inr (v : E) _ _

/-- The neck of the connected sum along open embeddings `e₁ : E → M` and `e₂ : E → N`: the
punctured model space `{0}ᶜ ⊆ E` is homeomorphic, by `v ↦ inl (neckInl v)`, to the overlap
`range inl ∩ range inr` of the two punctured summands. -/
noncomputable def neckHomeomorph (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    ({0}ᶜ : Set E) ≃ₜ (range (inl e₁ e₂) ∩ range (inr e₁ e₂) : Set (ConnectedSum e₁ e₂)) :=
  have he : IsEmbedding (inl e₁ e₂ ∘ neckInl h₁) :=
    (isOpenEmbedding_inl h₁ h₂).isEmbedding.comp
      (IsEmbedding.subtypeVal.of_comp_iff.mp (h₁.isEmbedding.comp IsEmbedding.subtypeVal))
  he.toHomeomorph.trans <| Homeomorph.setCongr <| by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨_, rfl⟩, ⟨_, (inl_neckInl_eq_inr_neckInr h₁ h₂ v).symm⟩⟩
    · rintro ⟨⟨x, rfl⟩, y, hy⟩
      obtain ⟨v, hv, hvx, -⟩ := (inl_eq_inr_iff h₁.injective).1 hy.symm
      exact ⟨⟨v, hv⟩, congrArg (inl e₁ e₂) (Subtype.ext hvx)⟩

@[simp]
theorem coe_neckHomeomorph_apply (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (v : ({0}ᶜ : Set E)) :
    (neckHomeomorph h₁ h₂ v : ConnectedSum e₁ e₂) = inl e₁ e₂ (neckInl h₁ v) :=
  (rfl)

end TauCeti.ConnectedSum

end
