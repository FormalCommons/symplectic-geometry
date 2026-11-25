/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Basic

/-!
# Points of a connected sum that lie on both summands, or on a ball carried to the sum

Let `TauCeti.ConnectedSum e₁ e₂` be Tau Ceti's connected sum of `M` and `N` along the coordinate
balls `e₁ : E → M` and `e₂ : E → N`. A point of one punctured summand is glued to a point of the
other only inside the balls, so each of the two points lies in the range of the ball of its own
summand. A ball `g` of `N` that misses the centre of `e₂` passes to the sum as
`TauCeti.ConnectedSum.inrBall`, and a point of the punctured `N` lands in the range of that ball
exactly when it lies in the range of `g`; likewise for `M` and `TauCeti.ConnectedSum.inlBall`.
These follow from Tau Ceti's `TauCeti.ConnectedSum.inl_eq_inr_iff`,
`TauCeti.ConnectedSum.inl_injective` and `TauCeti.ConnectedSum.inr_injective`.

## Main results

* `TauCeti.ConnectedSum.mem_range_left_of_inl_eq_inr`,
  `TauCeti.ConnectedSum.mem_range_right_of_inl_eq_inr`: glued points lie in the ranges of the
  balls.
* `TauCeti.ConnectedSum.inl_mem_range_inlBall_iff`,
  `TauCeti.ConnectedSum.inr_mem_range_inrBall_iff`: a point of a punctured summand lies on a ball
  carried to the sum exactly when it lies on the ball it comes from.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (connected sums of manifolds).
-/

public section

open Set Function

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {N : Type*} [TopologicalSpace N] [T1Space N]
  {e₁ : E → M} {e₂ : E → N} {x : puncture e₁} {y : puncture e₂}

/-- A point of the punctured first summand glued to a point of the second lies in the range of
the ball `e₁`. -/
theorem mem_range_left_of_inl_eq_inr (he₁ : Injective e₁) (h : inl e₁ e₂ x = inr e₁ e₂ y) :
    (x : M) ∈ range e₁ := by
  obtain ⟨v, -, hv, -⟩ := (inl_eq_inr_iff he₁).1 h
  exact ⟨v, hv⟩

/-- A point of the punctured second summand glued to a point of the first lies in the range of
the ball `e₂`. -/
theorem mem_range_right_of_inl_eq_inr (he₁ : Injective e₁) (h : inl e₁ e₂ x = inr e₁ e₂ y) :
    (y : N) ∈ range e₂ := by
  obtain ⟨v, -, -, hv⟩ := (inl_eq_inr_iff he₁).1 h
  exact ⟨_, hv⟩

/-- A point of the punctured first summand lies on the ball `inlBall e₁ e₂ f h` of the connected
sum exactly when it lies on the ball `f`. -/
theorem inl_mem_range_inlBall_iff (he₂ : Injective e₂) {f : E → M} (h : e₁ 0 ∉ range f) :
    inl e₁ e₂ x ∈ range (inlBall e₁ e₂ f h) ↔ (x : M) ∈ range f := by
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, ?_⟩, fun ⟨w, hw⟩ ↦ ⟨w, ?_⟩⟩
  · rw [inlBall_apply] at hw
    rw [← inl_injective he₂ hw, coe_punctureBall]
  · rw [inlBall_apply]
    exact congrArg _ (Subtype.ext (by rw [coe_punctureBall, hw]))

/-- A point of the punctured second summand lies on the ball `inrBall e₁ e₂ g h` of the connected
sum exactly when it lies on the ball `g`. -/
theorem inr_mem_range_inrBall_iff (he₁ : Injective e₁) {g : E → N} (h : e₂ 0 ∉ range g) :
    inr e₁ e₂ y ∈ range (inrBall e₁ e₂ g h) ↔ (y : N) ∈ range g := by
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, ?_⟩, fun ⟨w, hw⟩ ↦ ⟨w, ?_⟩⟩
  · rw [inrBall_apply] at hw
    rw [← inr_injective he₁ hw, coe_punctureBall]
  · rw [inrBall_apply]
    exact congrArg _ (Subtype.ext (by rw [coe_punctureBall, hw]))

end TauCeti.ConnectedSum
