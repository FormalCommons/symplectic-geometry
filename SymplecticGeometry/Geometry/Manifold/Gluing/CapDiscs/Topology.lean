/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.CapDiscs.Basic
import SymplecticGeometry.Topology.Compactness.LocallyFinite

/-!
# Capping with discs: compact and connected

Let `capDiscs c γ hγ hinj` be the surface `S` capped with discs
(`Gluing/CapDiscs/Basic.lean`). This file proves the point-set properties that make it a closed
surface when `S` is a compact surface whose boundary the loops `γ i` parametrize; that it is
Hausdorff when `S` is (`SymplecticGeometry.capDiscs.instT2Space`) is proved in `Basic.lean`,
where the pieces of its gluing data are.

* It is compact when `S` is compact and the `γ i` together cover the boundary. The ranges of the
  `γ i` are then a disjoint open cover of the compact boundary, so there are finitely many discs,
  and the capped surface is covered by the closed discs of radius `3 / 2` and the image of the
  compact set of points of `S` outside the collar points of depth less than `1 / 2`.
* It is connected when `S` is: the interior of `S` is connected
  (`ModelWithCorners.connectedSpace_interiorOpens`) and every disc is connected and meets it.

## Main results

* `SymplecticGeometry.capDiscs.compactSpace`: the capped surface is compact when `S` is compact
  and the loops cover the boundary of `S`; `finite_of_compactSpace`: there are then finitely
  many loops.
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

section Compact

omit [IsManifold (𝓡∂ 2) ∞ S] in
include hγ hinj in
/-- If `S` is compact and the loops `γ i` together cover the boundary of `S`, there are finitely
many of them: their ranges are disjoint, open and nonempty. -/
theorem finite_of_compactSpace [CompactSpace S]
    (hsurj : Surjective fun p : ι × AddCircle (1 : ℝ) ↦ γ p.1 p.2) : Finite ι := by
  refine finite_of_compactSpace_of_pairwise_disjoint (fun i ↦ (hγ i).isOpenMap.isOpen_range)
    (fun i ↦ range_nonempty _) (fun i j hij ↦ disjoint_left.2 ?_)
    (eq_univ_of_forall fun x ↦ ?_)
  · rintro _ ⟨θ, rfl⟩ ⟨θ', h⟩
    exact hij (congrArg Prod.fst (hinj (a₁ := (j, θ')) (a₂ := (i, θ)) h)).symm
  · obtain ⟨⟨i, θ⟩, rfl⟩ := hsurj x
    exact mem_iUnion.2 ⟨i, θ, rfl⟩

/-- The capped surface is compact when `S` is compact and the loops `γ i` together cover the
boundary of `S`. -/
theorem compactSpace [CompactSpace S]
    (hsurj : Surjective fun p : ι × AddCircle (1 : ℝ) ↦ γ p.1 p.2) :
    CompactSpace (capDiscs c γ hγ hinj) := by
  have := finite_of_compactSpace γ hγ hinj hsurj
  -- `K`: the points of `S` that are not collar points of depth less than `1 / 2`.
  let K : Set S := (c '' {q | (q.2 : EuclideanHalfSpace 1).val 0 < 1 / 2})ᶜ
  have hK : IsCompact K := by
    refine (IsClosed.isCompact (isOpen_compl_iff.1 ?_))
    rw [compl_compl]
    exact c.isOpenEmbedding.isOpenMap _ (isOpen_lt (by fun_prop) continuous_const)
  have hKint : K ⊆ range (Subtype.val : (𝓡∂ 2).interiorOpens S → S) := fun x hx ↦ by
    rw [Subtype.range_coe, ModelWithCorners.coe_interiorOpens]
    by_contra hxi
    rw [← mem_compl_iff, ModelWithCorners.compl_interior] at hxi
    refine hx ⟨(⟨x, hxi⟩, normalIioOpensZero one_pos), ?_, c.apply_zero _⟩
    simp [coe_normalIioOpensZero]
  have hD : IsCompact (((↑) : ball → ℂ) ⁻¹' Metric.closedBall 0 (3 / 2)) :=
    IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall 0 _) (fun w hw ↦ by
      rw [Subtype.range_coe, SetLike.mem_coe, mem_ball_iff]
      rw [mem_closedBall_zero_iff] at hw
      linarith)
  let T := inl c γ hγ hinj '' (Subtype.val ⁻¹' K) ∪
    ⋃ i, inr c γ hγ hinj i '' (((↑) : ball → ℂ) ⁻¹' Metric.closedBall 0 (3 / 2))
  have hT : IsCompact T :=
    ((IsInducing.subtypeVal.isCompact_preimage' hK hKint).image
      (isOpenEmbedding_capDiscs_inl c γ hγ hinj).continuous).union
      (isCompact_iUnion fun i ↦ hD.image (isOpenEmbedding_capDiscs_inr c γ hγ hinj i).continuous)
  have hinlT (p : (𝓡∂ 2).interiorOpens S) : inl c γ hγ hinj p ∈ T := by
    by_cases hp : (p : S) ∈ K
    · exact Or.inl ⟨p, hp, rfl⟩
    obtain ⟨⟨b, t⟩, ht, hpt⟩ := not_not.1 hp
    obtain ⟨⟨i, θ⟩, rfl⟩ := hsurj b
    have h : c (γ i θ, t) ∈ (𝓡∂ 2).interiorOpens S := hpt ▸ p.property
    refine Or.inr (mem_iUnion.2 ⟨i, _, ?_, (inr_ofReal_mul_toCircle_eq_inl c γ hγ hinj h).trans
      (congrArg _ (Subtype.ext hpt))⟩)
    have ht : (t : EuclideanHalfSpace 1).val 0 < 1 / 2 := ht
    rw [mem_preimage, mem_closedBall_zero_iff, norm_ofReal_one_add_mul_toCircle]
    linarith
  refine ⟨(eq_univ_of_univ_subset fun x _ ↦ ?_) ▸ hT⟩
  rcases exists_inl_or_exists_inr c γ hγ hinj x with ⟨p, rfl⟩ | ⟨i, z, rfl⟩
  · exact hinlT p
  by_cases hz : ‖(z : ℂ)‖ ≤ 3 / 2
  · exact Or.inr (mem_iUnion.2 ⟨i, z, mem_closedBall_zero_iff.2 hz, rfl⟩)
  rw [inr_eq_inl c γ hγ hinj (by linarith [not_le.1 hz])]
  exact hinlT _

end Compact

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
