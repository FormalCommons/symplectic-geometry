/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Map
public import SymplecticGeometry.Data.Set.Function

import SymplecticGeometry.Geometry.Manifold.ConnectedSum.Range
import SymplecticGeometry.Topology.Maps.Embedding
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# The connected sum with an open subset of the second summand

Let `e₁ : E → M` and `e₂ : E → N` be open embeddings, and let `U ⊆ N` be an open set containing
the range of `e₂`. Then `e₂` corestricts to a ball `Set.codRestrict e₂ U h : E → U` of `U`, and the
connected sum of `M` and `U` along `e₁` and this ball is homeomorphic to the open subset of
`TauCeti.ConnectedSum e₁ e₂` made of the whole punctured first summand and the points of the
punctured second summand that lie in `U`. In other words, removing from `N` a closed set that
misses the ball `e₂` removes the same set from the connected sum.

The homeomorphism is Tau Ceti's `TauCeti.ConnectedSum.map` for the identity of `M` and the
inclusion of `U` into `N`, an open embedding by `TauCeti.ConnectedSum.isOpenEmbedding_map`, onto
its range, which `TauCeti.ConnectedSum.range_map` computes. This generalizes the construction of
Tau Ceti's `TauCeti.ConnectedSum.leftHomeomorph` (in
`TauCeti/Geometry/Manifold/ConnectedSum/Assoc.lean`), where `U` is `N` with one point removed, to
any open `U` containing the ball.

## Main definitions

* `TauCeti.ConnectedSum.restrictRightHomeomorph`: the homeomorphism of the connected sum with
  `U` onto the open subset `range (inl e₁ e₂) ∪ inr e₁ e₂ '' {y | (y : N) ∈ U}` of the connected
  sum with `N`.

## Main results

* `TauCeti.ConnectedSum.isOpenEmbedding_map_id_subtypeVal`: the induced map of connected sums
  is an open embedding.
* `TauCeti.ConnectedSum.coe_restrictRightHomeomorph_inl`,
  `TauCeti.ConnectedSum.coe_restrictRightHomeomorph_inr`: the homeomorphism on the punctured
  summands.
* `TauCeti.ConnectedSum.isOpen_range_inl_union_image_inr`: that subset is open.
* `TauCeti.ConnectedSum.compl_range_inl_union_image_inr`: its complement is the image under
  `inr` of the points of the punctured `N` outside `U`.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (connected sums of manifolds).
-/

public section

noncomputable section

open Set Function Topology

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {N : Type*} [TopologicalSpace N] [T1Space N]
  {e₁ : E → M} {e₂ : E → N} {U : Set N}

/-- The map of connected sums induced by the identity of `M` and the inclusion of `U` into `N`
has as range the punctured first summand together with the points of the punctured second
summand that lie in `U`. -/
theorem range_map_id_subtypeVal (h : ∀ v, e₂ v ∈ U) :
    range (map id ((↑) : U → N) injective_id Subtype.val_injective (id_comp e₁)
        (val_comp_codRestrict e₂ U h)) =
      range (inl e₁ e₂) ∪ inr e₁ e₂ '' {y | (y : N) ∈ U} := by
  simp only [range_map, range_id, Subtype.range_coe, mem_univ, ofPred_true, image_univ]

/-- The map of connected sums induced by the identity of `M` and the inclusion of an open set
`U ⊆ N` containing the ball `e₂` is an open embedding. -/
theorem isOpenEmbedding_map_id_subtypeVal (he₁ : IsOpenEmbedding e₁) (he₂ : IsOpenEmbedding e₂)
    (hU : IsOpen U) (h : ∀ v, e₂ v ∈ U) :
    IsOpenEmbedding (map id ((↑) : U → N) injective_id Subtype.val_injective (id_comp e₁)
      (val_comp_codRestrict e₂ U h)) :=
  isOpenEmbedding_map injective_id Subtype.val_injective (id_comp e₁)
    (val_comp_codRestrict e₂ U h) IsOpenEmbedding.id hU.isOpenEmbedding_subtypeVal he₁
    (he₂.codRestrict U h)

/-- The points of the punctured first summand, and those of the punctured second summand that
lie in an open set `U` containing the ball `e₂`, form an open subset of the connected sum. -/
theorem isOpen_range_inl_union_image_inr (he₁ : IsOpenEmbedding e₁) (he₂ : IsOpenEmbedding e₂)
    (hU : IsOpen U) (h : ∀ v, e₂ v ∈ U) :
    IsOpen (range (inl e₁ e₂) ∪ inr e₁ e₂ '' {y | (y : N) ∈ U}) := by
  rw [← range_map_id_subtypeVal h]
  exact (isOpenEmbedding_map_id_subtypeVal he₁ he₂ hU h).isOpen_range

/-- If `U` contains the ball `e₂`, the points of the connected sum that are neither on the
punctured first summand nor on the points of the punctured second summand in `U` are the images
under `inr` of the points of the punctured second summand outside `U`. -/
theorem compl_range_inl_union_image_inr (he₁ : Injective e₁) (h : ∀ v, e₂ v ∈ U) :
    (range (inl e₁ e₂) ∪ inr e₁ e₂ '' {y | (y : N) ∈ U})ᶜ =
      inr e₁ e₂ '' {y | (y : N) ∉ U} := by
  ext p
  obtain ⟨x | y, rfl⟩ := mk_surjective e₁ e₂ p
  · simp only [mk_inl, mem_compl_iff, mem_union, mem_range_self, true_or, not_true_eq_false,
      false_iff, mem_image, mem_ofPred_eq, not_exists, not_and]
    intro y hy hyx
    obtain ⟨v, hv⟩ := mem_range_right_of_inl_eq_inr he₁ hyx.symm
    exact hy (hv ▸ h v)
  · simp only [mk_inr, mem_compl_iff, mem_union, mem_range, mem_image, mem_ofPred_eq,
      (inr_injective he₁).eq_iff, exists_eq_right, not_or, not_exists]
    refine ⟨fun hy ↦ hy.2, fun hy ↦ ⟨fun x hx ↦ ?_, hy⟩⟩
    obtain ⟨v, hv⟩ := mem_range_right_of_inl_eq_inr he₁ hx
    exact hy (hv ▸ h v)

/-- **The connected sum with an open subset of the second summand.** For open embeddings
`e₁ : E → M` and `e₂ : E → N` and an open set `U ⊆ N` containing the range of `e₂`, the connected
sum of `M` and `U` along `e₁` and the corestriction of `e₂` to `U` is homeomorphic to the open
subset of `ConnectedSum e₁ e₂` made of the punctured first summand and the points of the punctured
second summand lying in `U`. -/
def restrictRightHomeomorph (he₁ : IsOpenEmbedding e₁) (he₂ : IsOpenEmbedding e₂) (hU : IsOpen U)
    (h : ∀ v, e₂ v ∈ U) :
    ConnectedSum e₁ (codRestrict e₂ U h) ≃ₜ
      (range (inl e₁ e₂) ∪ inr e₁ e₂ '' {y | (y : N) ∈ U} : Set (ConnectedSum e₁ e₂)) :=
  (isOpenEmbedding_map_id_subtypeVal he₁ he₂ hU h).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_map_id_subtypeVal h))

variable (he₁ : IsOpenEmbedding e₁) (he₂ : IsOpenEmbedding e₂) (hU : IsOpen U)
  (h : ∀ v, e₂ v ∈ U)

/-- The homeomorphism `restrictRightHomeomorph`, followed by the inclusion of its target, is the
map of connected sums induced by the identity of `M` and the inclusion of `U` into `N`. -/
theorem coe_restrictRightHomeomorph (p : ConnectedSum e₁ (codRestrict e₂ U h)) :
    (restrictRightHomeomorph he₁ he₂ hU h p : ConnectedSum e₁ e₂) =
      map id ((↑) : U → N) injective_id Subtype.val_injective (id_comp e₁)
        (val_comp_codRestrict e₂ U h) p := by
  simp [restrictRightHomeomorph]

/-- `restrictRightHomeomorph` is the identity on the punctured first summand. -/
@[simp]
theorem coe_restrictRightHomeomorph_inl (x : puncture e₁) :
    (restrictRightHomeomorph he₁ he₂ hU h (inl _ _ x) : ConnectedSum e₁ e₂) = inl e₁ e₂ x := by
  rw [coe_restrictRightHomeomorph, map_inl, punctureMap_id]

/-- `restrictRightHomeomorph` is the inclusion of `U` into `N` on the punctured second summand. -/
@[simp]
theorem coe_restrictRightHomeomorph_inr (y : puncture (codRestrict e₂ U h)) :
    (restrictRightHomeomorph he₁ he₂ hU h (inr _ _ y) : ConnectedSum e₁ e₂) =
      inr e₁ e₂ (punctureMap ((↑) : U → N) Subtype.val_injective
        (congrFun (val_comp_codRestrict e₂ U h) 0) y) := by
  rw [coe_restrictRightHomeomorph, map_inr]

end TauCeti.ConnectedSum

end
