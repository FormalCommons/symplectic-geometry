/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.CapDiscs.Basic
import SymplecticGeometry.Topology.Compactness.LocallyFinite

/-!
# Capping with discs: Hausdorff, compact and connected

Let `capDiscs c γ hγ hinj` be the surface `S` capped with discs
(`Gluing/CapDiscs/Basic.lean`). This file proves the point-set properties that make it a closed
surface when `S` is a compact surface whose boundary the loops `γ i` parametrize.

* It is Hausdorff when `S` is. Points of the interior of `S`, or of one disc, are separated
  there, and distinct discs are disjoint. A point `z` of the `i`-th disc with `‖z‖ ≤ 1` and an
  interior point `p` are separated by the collar: `p` is away from the compact circle `γ i`, so
  by compactness of the circle, `p` is also away from the collar points `c (γ i θ, t)` for all
  `θ` and all small `t`, which are the points of a thin annulus `1 < ‖z‖ < 1 + ε` of the disc.
* It is compact when `S` is compact and the `γ i` together cover the boundary. The ranges of the
  `γ i` are then a disjoint open cover of the compact boundary, so there are finitely many discs,
  and the capped surface is covered by the closed discs of radius `3 / 2` and the image of the
  compact set of points of `S` outside the collar points of depth less than `1 / 2`.
* It is connected when `S` is: the interior of `S` is connected
  (`ModelWithCorners.connectedSpace_interiorOpens`) and every disc is connected and meets it.

## Main results

* `SymplecticGeometry.capDiscs.instT2Space`: the capped surface is Hausdorff when `S` is.
* `SymplecticGeometry.capDiscs.compactSpace`: it is compact when `S` is compact and the loops
  cover the boundary of `S`; `finite_of_compactSpace`: there are then finitely many loops.
* `SymplecticGeometry.capDiscs.instConnectedSpace`: it is connected when `S` is.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number of bundles over surfaces).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 1 (the Hausdorff condition on a space glued from charts, as in the smooth manifold
  chart lemma; here it is proved directly for the glued surface).
-/

public section

open Set Function Topology Filter Manifold TopologicalSpace Complex
open scoped Manifold ContDiff Real

noncomputable section

namespace SymplecticGeometry

open TauCeti TauCeti.EuclideanHalfSpace CoordinateDisc AddCircle

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

local instance : IsManifold (𝓡 1) ∞ ((𝓡∂ 2).boundary S) := isManifold_boundary S

namespace capDiscs

variable (c : SmoothCollar 1 ∞ S) {ι : Type} (γ : ι → AddCircle (1 : ℝ) → (𝓡∂ 2).boundary S)
  (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i))
  (hinj : Function.Injective fun p : ι × AddCircle (1 : ℝ) ↦ γ p.1 p.2)

section T2

variable [T2Space S]

/-- An interior point `p` of `S` has a neighbourhood that the `i`-th disc meets only in a thin
annulus `1 < ‖z‖`, at distance `ε` from the boundary circle `‖z‖ = 1`. -/
private theorem exists_nhds_inr_ne_inl (i : ι) (p : (𝓡∂ 2).interiorOpens S) :
    ∃ ε > 0, ∃ V ∈ 𝓝 p, ∀ q ∈ V, ∀ z : ball, ‖(z : ℂ)‖ < 1 + ε →
      inr c γ hγ hinj i z ≠ inl c γ hγ hinj q := by
  -- Separate `p` from the compact boundary circle `γ i` by `A ∋ p` and an open `B ⊇ γ i`.
  have hC : IsCompact (range fun θ ↦ (γ i θ : S)) :=
    isCompact_range (continuous_subtypeVal.comp (hγ i).isLocalHomeomorph.continuous)
  have hp : (p : S) ∉ range fun θ ↦ (γ i θ : S) := by
    rintro ⟨θ, hθ⟩
    have hb : (p : S) ∈ (𝓡∂ 2).boundary S := hθ ▸ (γ i θ).property
    exact disjoint_left.1 ModelWithCorners.disjoint_interior_boundary
      (ModelWithCorners.mem_interiorOpens_iff_mem_interior.1 p.property) hb
  obtain ⟨B, hB, A, hA, hAB⟩ := Filter.disjoint_iff.1 (hC.disjoint_nhdsSet_nhds hp)
  obtain ⟨B', hB'o, hCB', hB'B⟩ := mem_nhdsSet_iff_exists.1 hB
  -- The collar coordinates `(γ i θ, t)` whose collar point lies in `B'`, read in `∂S × [0, ∞)`.
  let V : Set (↥((𝓡∂ 2).boundary S) × EuclideanHalfSpace 1) :=
    Prod.map id Subtype.val '' (c ⁻¹' B')
  have hV : IsOpen V :=
    (IsOpenEmbedding.id.prodMap (normalIioOpens 1).isOpen.isOpenEmbedding_subtypeVal).isOpenMap _
      (hB'o.preimage c.continuous)
  let F : ℝ × AddCircle (1 : ℝ) → ↥((𝓡∂ 2).boundary S) × EuclideanHalfSpace 1 :=
    fun x ↦ (γ i x.2, normalRay x.1)
  have hF : Continuous F :=
    ((hγ i).isLocalHomeomorph.continuous.comp continuous_snd).prodMk
      (continuous_normalRay.comp continuous_fst)
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ θ ∈ univ, F (r, θ) ∈ V := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun θ _ ↦ ?_
    refine hF.continuousAt.preimage_mem_nhds (hV.mem_nhds ⟨(γ i θ, normalIioOpensZero one_pos),
      ?_, ?_⟩)
    · rw [mem_preimage, c.apply_zero]
      exact hCB' ⟨θ, rfl⟩
    · simp [F, normalRay_zero]
  obtain ⟨ε, hε, hεV⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, Subtype.val ⁻¹' A, continuous_subtypeVal.continuousAt.preimage_mem_nhds hA,
    fun q hq z hzε hzq ↦ ?_⟩
  have hz : 1 < ‖(z : ℂ)‖ := (inr_mem_range_inl_iff c γ hγ hinj).1 ⟨q, hzq.symm⟩
  rw [inr_eq_inl c γ hγ hinj hz] at hzq
  obtain rfl := (isOpenEmbedding_capDiscs_inl c γ hγ hinj).injective hzq
  obtain ⟨w, hw, hwF⟩ := hεV (y := ‖(z : ℂ)‖ - 1)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    ((arg z / (2 * π) : ℝ) : AddCircle (1 : ℝ)) (mem_univ _)
  have hw' : w = gluingCoord γ i z :=
    Prod.ext ((congrArg Prod.fst hwF).trans (gluingCoord_fst i z).symm)
      (Subtype.ext ((congrArg Prod.snd hwF).trans (coe_gluingCoord_snd i z).symm))
  exact disjoint_left.1 hAB (hB'B (hw' ▸ hw)) hq

/-- The capped surface is Hausdorff when `S` is. -/
instance instT2Space : T2Space (capDiscs c γ hγ hinj) := by
  -- Distinct images of an open embedding of a Hausdorff space have disjoint neighbourhoods.
  have key {X : Type} [TopologicalSpace X] [T2Space X] {f : X → capDiscs c γ hγ hinj}
      (hf : IsOpenEmbedding f) {a b : X} (h : f a ≠ f b) : Disjoint (𝓝 (f a)) (𝓝 (f b)) := by
    rw [← hf.map_nhds_eq, ← hf.map_nhds_eq, Filter.disjoint_map hf.injective]
    exact disjoint_nhds_nhds.2 fun hab ↦ h (congrArg f hab)
  have hinl := isOpenEmbedding_capDiscs_inl c γ hγ hinj
  have hinr := isOpenEmbedding_capDiscs_inr c γ hγ hinj
  -- A point of a disc and a distinct point of the interior.
  have mixed {i : ι} {z : ball} {p : (𝓡∂ 2).interiorOpens S}
      (h : inr c γ hγ hinj i z ≠ inl c γ hγ hinj p) :
      Disjoint (𝓝 (inr c γ hγ hinj i z)) (𝓝 (inl c γ hγ hinj p)) := by
    by_cases hz : 1 < ‖(z : ℂ)‖
    · rw [inr_eq_inl c γ hγ hinj hz] at h ⊢
      exact key hinl h
    obtain ⟨ε, hε, V, hV, hsep⟩ := exists_nhds_inr_ne_inl c γ hγ hinj i p
    have hU : {w : ball | ‖(w : ℂ)‖ < 1 + ε} ∈ 𝓝 z :=
      (isOpen_lt (continuous_norm.comp continuous_subtypeVal) continuous_const).mem_nhds
        (show ‖(z : ℂ)‖ < 1 + ε by linarith [not_lt.1 hz])
    refine Filter.disjoint_iff.2 ⟨_, (hinr i).map_nhds_eq z ▸ image_mem_map hU, _,
      hinl.map_nhds_eq p ▸ image_mem_map hV, disjoint_left.2 ?_⟩
    rintro _ ⟨w, hw, rfl⟩ ⟨q, hq, hqw⟩
    exact hsep q hq w hw hqw.symm
  refine t2Space_iff_disjoint_nhds.2 fun x y hxy ↦ ?_
  have hcover := range_inl_union_iUnion_range_inr c γ hγ hinj
  have hx : x ∈ range (inl c γ hγ hinj) ∪ ⋃ i, range (inr c γ hγ hinj i) := hcover ▸ mem_univ x
  have hy : y ∈ range (inl c γ hγ hinj) ∪ ⋃ i, range (inr c γ hγ hinj i) := hcover ▸ mem_univ y
  simp only [mem_union, mem_iUnion] at hx hy
  rcases hx with ⟨p, rfl⟩ | ⟨i, z, rfl⟩ <;> rcases hy with ⟨q, rfl⟩ | ⟨j, w, rfl⟩
  · exact key hinl hxy
  · exact (mixed (Ne.symm hxy)).symm
  · exact mixed hxy
  · obtain rfl | hij := eq_or_ne i j
    · exact key (hinr i) hxy
    · exact Filter.disjoint_iff.2 ⟨_, (hinr i).isOpen_range.mem_nhds (mem_range_self z), _,
        (hinr j).isOpen_range.mem_nhds (mem_range_self w), disjoint_range_inr c γ hγ hinj hij⟩

end T2

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
  have hx : x ∈ range (inl c γ hγ hinj) ∪ ⋃ i, range (inr c γ hγ hinj i) :=
    range_inl_union_iUnion_range_inr c γ hγ hinj ▸ mem_univ x
  simp only [mem_union, mem_iUnion] at hx
  rcases hx with ⟨p, rfl⟩ | ⟨i, z, rfl⟩
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
