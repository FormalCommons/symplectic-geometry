/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.CapDiscs.Basic

/-!
# Capping with discs: connected

Let `capDiscs c γ hγ hinj` be the surface `S` capped with discs
(`Gluing/CapDiscs/Basic.lean`). This file proves that it is connected when `S` is: the interior
of `S` is connected (`ModelWithCorners.connectedSpace_interiorOpens`) and every disc is connected
and meets it. That it is Hausdorff when `S` is (`SymplecticGeometry.capDiscs.instT2Space`), and
compact when `S` is compact and the loops `γ i` cover its boundary
(`SymplecticGeometry.capDiscs.compactSpace`), is proved in `Basic.lean`, where the pieces of its
gluing data are.

## Main results

* `SymplecticGeometry.capDiscs.instConnectedSpace`: it is connected when `S` is.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number of bundles over surfaces).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
-/

public section

open Set Function Topology Filter Manifold TopologicalSpace Complex
open scoped Manifold ContDiff Real

noncomputable section

namespace SymplecticGeometry

open TauCeti TauCeti.EuclideanHalfSpace CoordinateDisc AddCircle

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

namespace capDiscs

variable (c : SmoothCollar 1 ∞ S) {ι : Type} (γ : ι → AddCircle (1 : ℝ) → (𝓡∂ 2).boundary S)
  (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i))
  (hinj : Function.Injective fun p : ι × AddCircle (1 : ℝ) ↦ γ p.1 p.2)

/-- The capped surface is connected when `S` is: the interior of `S` is connected, and every disc
is connected and meets it. -/
instance instConnectedSpace [ConnectedSpace S] : ConnectedSpace (capDiscs c γ hγ hinj) := by
  have hint := isConnected_range (isOpenEmbedding_capDiscs_inl c γ hγ hinj).continuous
  have hdisc (i : ι) := isConnected_range (isOpenEmbedding_capDiscs_inr c γ hγ hinj i).continuous
  -- The point `3 / 2` of each disc lies in the interior of `S`.
  have hmeet (i : ι) : (range (inl c γ hγ hinj) ∩ range (inr c γ hγ hinj i)).Nonempty := by
    have h32 : ‖((3 / 2 : ℝ) : ℂ)‖ = 3 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    obtain ⟨z, hz⟩ : ∃ z : ball, ‖(z : ℂ)‖ = 3 / 2 :=
      ⟨⟨((3 / 2 : ℝ) : ℂ), by rw [mem_ball_iff, h32]; norm_num⟩, h32⟩
    exact ⟨inr c γ hγ hinj i z, (inr_mem_range_inl_iff c γ hγ hinj).2 (by rw [hz]; norm_num),
      mem_range_self z⟩
  obtain ⟨x, hx⟩ := hint.nonempty
  let C : Set (Set (capDiscs c γ hγ hinj)) := insert (range (inl c γ hγ hinj))
    (range fun i ↦ range (inl c γ hγ hinj) ∪ range (inr c γ hγ hinj i))
  have hC : ⋃₀ C = univ := by
    refine eq_univ_of_univ_subset ?_
    rw [← range_inl_union_iUnion_range_inr c γ hγ hinj]
    rintro y (hy | hy)
    · exact ⟨_, mem_insert _ _, hy⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    exact ⟨_, mem_insert_of_mem _ ⟨i, rfl⟩, Or.inr hi⟩
  rw [connectedSpace_iff_univ, ← hC]
  refine ⟨⟨x, mem_sUnion_of_mem hx (mem_insert _ _)⟩, isPreconnected_sUnion x C ?_ ?_⟩
  · rintro s (rfl | ⟨i, rfl⟩)
    exacts [hx, Or.inl hx]
  · rintro s (rfl | ⟨i, rfl⟩)
    exacts [hint.isPreconnected, (hint.union (hmeet i) (hdisc i)).isPreconnected]

end capDiscs

end SymplecticGeometry

end
