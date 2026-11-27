/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Topology.Homotopy.Path

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.GroupTheory.CoprodI
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# The plane minus real points: a free basis of loops

Let `c : ι → ℝ` be nonzero reals, any two of them at distance at least `δ > 0`. For finitely
many distinct nonzero reals, at least two of them, `δ = Set.infsep (Set.range c)` will do: it is
positive by `Set.Finite.infsep_pos_iff_nontrivial`, and at most each distance by
`Set.infsep_le_dist_of_mem` and `Real.dist_eq`; with fewer points any `δ > 0` will do. The
fundamental group of `ℂ` with the points `c i` removed, based at `0`, is free on the loops
`PlaneMinusRealPoints.loop hδ hc h0 k`. The loop about `c k` goes from `0` straight down to `-i`,
right or left to `c k + r - i` and straight up to `c k + r`, once counterclockwise around the
circle of radius `r = δ / 4` about `c k`, and back the same way.

## Main definitions

* `SymplecticGeometry.PlaneMinusRealPoints.approach x r`, `circle x r` and `loopInPlane x r`:
  the loop in `ℂ` about `x` of radius `r`, based at `0`, and the pieces it is made of.
* `SymplecticGeometry.PlaneMinusRealPoints.loop hδ hc h0 k`: the loop about `c k`, based at `0`, in
  the plane minus the points.
* `SymplecticGeometry.PlaneMinusRealPoints.fundamentalGroupMulEquiv hδ hc h0`: the isomorphism
  of `π₁(ℂ ∖ {c i}, 0)` with `FreeGroup ι`.

## Main results

* `SymplecticGeometry.PlaneMinusRealPoints.fundamentalGroupMulEquiv_loop`: the isomorphism sends
  the class of `loop hδ hc h0 k` to `FreeGroup.of k`; its inverse is `FreeGroup.lift` of the
  classes of the loops (`fundamentalGroupMulEquiv_symm_apply`).

## Implementation notes

The proof follows the strategy of Tau Ceti's
`TauCeti.nonempty_fundamentalGroup_compl_mulEquiv_freeGroup`
(`TauCeti/AlgebraicTopology/FundamentalGroup/PlaneMinusPoints.lean`, at Tau Ceti's commit
`994bb2246b869d826bb90a6298bd0f9423b83104`): the wide van Kampen theorem
`TauCeti.vanKampenWideEquiv`, for pieces that are the lower half-plane together with a vertical
strip about one point, punctured there, each star-convex about its puncture. That theorem names no
generators, and its cover is private, so the cover here is built anew, in another way. A single
deformation, which slides the imaginary part of a point towards `-1` with a weight that vanishes
near the vertical lines through the points (a function of the distance of the real part to the
points), retracts the punctured plane, in the weak sense, onto the union of the lower half-plane
and the strips, minus the points. The van Kampen theorem is applied to that union, at the base
point `-i`, and each piece is itself a punctured star-convex set, so that
`StarConvex.fundamentalGroupMulEquivInt_sphereLoop` gives its generator, the circle about the
puncture. A change of base point along the approach path turns it into the loop about the point,
and one along the segment from `-i` to `0` brings everything to `0`.

Some steps follow private lemmas of the same Tau Ceti file, at the same commit, adapted to the
pieces here: `starConvex_fan` follows `starConvex_model`, `sphere_subset_fan` follows
`sphere_subset_model`, `notMem_band_of_mem_band` follows the last case of
`piece_inter_piece_subset`, and `bijective_lift_loop_of_isEmpty` follows the case of no points
in `nonempty_fundamentalGroup_compl_range_mulEquiv_freeGroup`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.2, Theorem 1.20
  (the Seifert--van Kampen theorem), and Chapter 0, Exercise 4 (weak deformation retractions).
-/

public section

noncomputable section

open Set Metric Topology Complex
open scoped ContinuousMap
open FundamentalGroup (fromPath)

namespace SymplecticGeometry

namespace PlaneMinusRealPoints

variable {ι : Type*} {c : ι → ℝ} {δ : ℝ}

/-! ### The loops in `ℂ` -/

/-- The path from `-i` to the circle about `x` of radius `r`: straight to `x + r - i`, then
straight up to `x + r`. -/
def approach (x r : ℝ) : Path (-I) ((x + r : ℝ) : ℂ) :=
  (Path.segment (-I) ((x + r : ℝ) - I)).trans (Path.segment ((x + r : ℝ) - I) ((x + r : ℝ) : ℂ))

theorem approach_def (x r : ℝ) :
    approach x r =
      (Path.segment (-I) ((x + r : ℝ) - I)).trans
        (Path.segment ((x + r : ℝ) - I) ((x + r : ℝ) : ℂ)) :=
  (rfl)

/-- The circle about `x` of radius `r`, run once counterclockwise from `x + r`. -/
def circle (x r : ℝ) : Path ((x + r : ℝ) : ℂ) ((x + r : ℝ) : ℂ) where
  toFun t := x + r * exp ((2 * Real.pi * t : ℝ) * I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [exp_mul_I]

theorem circle_apply (x r : ℝ) (t : unitInterval) :
    circle x r t = circleMap x r (2 * Real.pi * t) := by
  simp [circle, circleMap]

/-- The loop in `ℂ` about `x` of radius `r`, based at `0`: straight down from `0` to `-i`, along
`approach x r` to `x + r`, once counterclockwise around the circle about `x`, and back the same
way. -/
def loopInPlane (x r : ℝ) : Path (0 : ℂ) 0 :=
  (Path.segment 0 (-I)).trans
    (((approach x r).trans ((circle x r).trans (approach x r).symm)).trans
      (Path.segment 0 (-I)).symm)

theorem loopInPlane_def (x r : ℝ) :
    loopInPlane x r =
      (Path.segment 0 (-I)).trans
        (((approach x r).trans ((circle x r).trans (approach x r).symm)).trans
          (Path.segment 0 (-I)).symm) :=
  (rfl)

/-! ### The pieces of the cover -/

/-- The open lower half-plane. -/
private def lowerHalf : Set ℂ := {z | z.im < 0}

private theorem mem_lowerHalf {z : ℂ} : z ∈ lowerHalf ↔ z.im < 0 := Iff.rfl

private theorem negI_mem_lowerHalf : -I ∈ lowerHalf := mem_lowerHalf.2 (by simp)

variable (c δ) in
/-- The open vertical strip of half-width `δ / 2` about the real point `c k`. -/
private def band (k : ι) : Set ℂ := {z | |z.re - c k| < δ / 2}

private theorem mem_band {k : ι} {z : ℂ} : z ∈ band c δ k ↔ |z.re - c k| < δ / 2 := Iff.rfl

variable (c δ) in
/-- The lower half-plane together with the strip about `c k`. -/
private def fan (k : ι) : Set ℂ := lowerHalf ∪ band c δ k

variable (c δ) in
/-- The lower half-plane together with all the strips, minus the points `c i`. -/
private def spine : Set ℂ := (lowerHalf ∪ ⋃ k, band c δ k) \ range fun i ↦ (c i : ℂ)

private theorem isOpen_lowerHalf : IsOpen lowerHalf := by
  unfold lowerHalf
  exact isOpen_lt continuous_im continuous_const

private theorem isOpen_band (k : ι) : IsOpen (band c δ k) := by
  unfold band
  exact isOpen_lt (by fun_prop) continuous_const

private theorem ofReal_notMem_lowerHalf (x : ℝ) : (x : ℂ) ∉ lowerHalf := by
  simp [mem_lowerHalf]

private theorem notMem_band_of_mem_band (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) {i j : ι}
    (hij : i ≠ j) {z : ℂ} (hi : z ∈ band c δ i) : z ∉ band c δ j := by
  rw [mem_band] at hi ⊢
  have h := abs_sub_le (c i) z.re (c j)
  rw [abs_sub_comm] at hi
  linarith [hc hij]

private theorem mem_band_self (hδ : 0 < δ) (k : ι) : (c k : ℂ) ∈ band c δ k := by
  simp [mem_band, hδ]

/-- The point `c i` lies in the strip about `c k` only for `i = k`. -/
private theorem eq_of_ofReal_mem_band (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    {i k : ι} (h : (c i : ℂ) ∈ band c δ k) : i = k := by
  by_contra hik
  exact notMem_band_of_mem_band hc hik (mem_band_self hδ i) h

/-- The lower half-plane together with the strip about `c k` is star-convex about `c k`. -/
private theorem starConvex_fan (hδ : 0 < δ) (k : ι) : StarConvex ℝ (c k : ℂ) (fan c δ k) := by
  refine (starConvex_iff_forall_pos (s := fan c δ k) (Or.inr (mem_band_self hδ k))).2
    fun z hz a b ha hb hab ↦ ?_
  have hre : (a • (c k : ℂ) + b • z).re - c k = b * (z.re - c k) := by
    simp only [add_re, smul_re, ofReal_re, smul_eq_mul]
    linear_combination c k * hab
  rcases hz with hz | hz
  · refine .inl ?_
    rw [mem_lowerHalf] at hz ⊢
    simpa using mul_neg_of_pos_of_neg hb hz
  · refine .inr ?_
    rw [mem_band] at hz ⊢
    rw [hre, abs_mul, abs_of_pos hb]
    nlinarith [abs_nonneg (z.re - c k)]

private theorem sphere_subset_fan (hδ : 0 < δ) (k : ι) :
    sphere (c k : ℂ) (δ / 4) ⊆ fan c δ k := by
  intro z hz
  refine .inr (mem_band.2 ?_)
  have h := abs_re_le_norm (z - c k)
  rw [mem_sphere_iff_norm] at hz
  rw [sub_re, ofReal_re] at h
  linarith

/-- The punctured fan lies in the spine. -/
private theorem fan_diff_subset_spine (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) : fan c δ k \ {(c k : ℂ)} ⊆ spine c δ := by
  rintro z ⟨hz, hzk⟩
  refine ⟨hz.imp_right fun h ↦ mem_iUnion.2 ⟨k, h⟩, ?_⟩
  rintro ⟨i, rfl⟩
  rcases hz with h | h
  · exact ofReal_notMem_lowerHalf _ h
  · obtain rfl := eq_of_ofReal_mem_band hδ hc h
    exact hzk (mem_singleton _)

private theorem lowerHalf_subset_spine : lowerHalf ⊆ spine c δ := fun z hz ↦
  ⟨.inl hz, by rintro ⟨i, rfl⟩; exact ofReal_notMem_lowerHalf _ hz⟩

private theorem spine_subset_compl_range : spine c δ ⊆ (range fun i ↦ (c i : ℂ))ᶜ :=
  sdiff_subset_compl _ _

/-! ### The retraction of the punctured plane onto the spine -/

variable (c δ) in
/-- The weight of the deformation at real part `x`: `0` when `x` is within `δ / 4` of some point
`c i`, and `1` when it is at distance at least `δ / 2` from all of them. -/
private def weight (x : ℝ) : ℝ := max 0 (min 1 (4 * infDist x (range c) / δ - 1))

private theorem weight_nonneg (x : ℝ) : 0 ≤ weight c δ x := le_max_left _ _

private theorem weight_le_one (x : ℝ) : weight c δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem weight_apply_self (i : ι) : weight c δ (c i) = 0 := by
  rw [weight, infDist_zero_of_mem (mem_range_self i), mul_zero, zero_div, zero_sub]
  exact max_eq_left (min_le_right _ _ |>.trans (by norm_num))

private theorem weight_eq_one (hδ : 0 < δ) {x : ℝ} (hx : δ / 2 ≤ infDist x (range c)) :
    weight c δ x = 1 := by
  have : 1 ≤ 4 * infDist x (range c) / δ - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hδ]
    linarith
  rw [weight, min_eq_left this, max_eq_right zero_le_one]

private theorem continuous_weight : Continuous (weight c δ) := by
  unfold weight
  exact continuous_const.max (continuous_const.min
    (((continuous_const.mul (continuous_infDist_pt _)).div_const δ).sub continuous_const))

/-- Move the imaginary part of `z` the fraction `s` of the way to `-1`, keeping the real part. -/
private def slide (s : ℝ) (z : ℂ) : ℂ := z.re + (((1 - s) * z.im - s : ℝ) : ℂ) * I

private theorem slide_re (s : ℝ) (z : ℂ) : (slide s z).re = z.re := by
  simp [slide]

private theorem slide_im (s : ℝ) (z : ℂ) : (slide s z).im = (1 - s) * z.im - s := by
  simp [slide]

private theorem slide_zero (z : ℂ) : slide 0 z = z := by
  apply Complex.ext <;> simp [slide_re, slide_im]

private theorem continuous_slide : Continuous fun p : ℝ × ℂ ↦ slide p.1 p.2 := by
  unfold slide
  fun_prop

private theorem slide_mem_lowerHalf {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : ℂ}
    (hz : z ∈ lowerHalf) : slide s z ∈ lowerHalf := by
  rw [mem_lowerHalf] at hz ⊢
  rw [slide_im]
  rcases hs1.lt_or_eq with h | rfl
  · nlinarith
  · norm_num

variable (c δ) in
/-- The time-`t` map of the deformation. -/
private def deform (t : ℝ) (z : ℂ) : ℂ := slide (t * weight c δ z.re) z

private theorem continuous_deform : Continuous fun p : ℝ × ℂ ↦ deform c δ p.1 p.2 :=
  continuous_slide.comp
    ((continuous_fst.mul (continuous_weight.comp (continuous_re.comp continuous_snd))).prodMk
      continuous_snd)

/-- The deformation moves no point onto one of the points `c i`. -/
private theorem deform_notMem_range (t : ℝ) {z : ℂ}
    (hz : z ∈ (range fun i ↦ (c i : ℂ))ᶜ) : deform c δ t z ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  have hre : z.re = c i := by simpa [deform, slide_re] using (congrArg re hi).symm
  rw [deform, hre, weight_apply_self, mul_zero, slide_zero] at hi
  exact hz ⟨i, hi⟩

private theorem deform_mem_spine {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℂ}
    (hz : z ∈ spine c δ) : deform c δ t z ∈ spine c δ := by
  refine ⟨?_, deform_notMem_range t hz.2⟩
  rcases hz.1 with h | h
  · exact .inl (slide_mem_lowerHalf (mul_nonneg ht0 (weight_nonneg _))
      (by nlinarith [weight_nonneg (c := c) (δ := δ) z.re, weight_le_one (c := c) (δ := δ) z.re]) h)
  · obtain ⟨k, hk⟩ := mem_iUnion.1 h
    exact .inr (mem_iUnion.2 ⟨k, by rwa [mem_band, deform, slide_re]⟩)

private theorem deform_one_mem_spine [Nonempty ι] (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ (range fun i ↦ (c i : ℂ))ᶜ) : deform c δ 1 z ∈ spine c δ := by
  refine ⟨?_, deform_notMem_range 1 hz⟩
  by_cases h : infDist z.re (range c) < δ / 2
  · obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (infDist_lt_iff (range_nonempty c)).1 h
    refine .inr (mem_iUnion.2 ⟨k, ?_⟩)
    rwa [mem_band, deform, slide_re, ← Real.dist_eq]
  · refine .inl ?_
    rw [mem_lowerHalf, deform, weight_eq_one hδ (not_lt.1 h), one_mul, slide_im]
    norm_num

/-- The spine is a weak deformation retract of the punctured plane. -/
private def spineHomotopyEquiv [Nonempty ι] (hδ : 0 < δ) :
    spine c δ ≃ₕ ((range fun i ↦ (c i : ℂ))ᶜ : Set ℂ) :=
  .ofWeakDeformationRetraction spine_subset_compl_range (fun p ↦ deform c δ p.1 p.2)
    (continuous_deform.comp ((continuous_subtypeVal.comp continuous_fst).prodMk
      (continuous_subtypeVal.comp continuous_snd)))
    (fun p ↦ deform_notMem_range _ p.2.property)
    (fun _ ↦ by simp [deform, slide_zero])
    (fun z ↦ deform_one_mem_spine hδ z.property)
    (fun t _ hz ↦ deform_mem_spine t.property.1 t.property.2 hz)

/-! ### The cover of the spine -/

variable (c δ) in
/-- The `k`-th member of the cover of the spine: its points in the punctured fan about `c k`. -/
private def member (k : ι) : Set (spine c δ) := Subtype.val ⁻¹' (fan c δ k \ {(c k : ℂ)})

variable (c δ) in
/-- The common part of the cover: the points of the spine in the lower half-plane. -/
private def lowerPart : Set (spine c δ) := Subtype.val ⁻¹' lowerHalf

private theorem mem_member_of_mem_lowerPart (k : ι) {z : spine c δ} (hz : z ∈ lowerPart c δ) :
    z ∈ member c δ k :=
  ⟨.inl hz, fun h ↦ ofReal_notMem_lowerHalf (c k) (mem_singleton_iff.1 h ▸ hz)⟩

private theorem member_inter_member_subset (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) {i j : ι}
    (hij : i ≠ j) : member c δ i ∩ member c δ j ⊆ lowerPart c δ := by
  rintro z ⟨⟨hi | hi, -⟩, hj | hj, -⟩
  · exact hi
  · exact hi
  · exact hj
  · exact (notMem_band_of_mem_band hc hij hi hj).elim

private theorem exists_member_mem_nhds [Nonempty ι] (z : spine c δ) :
    ∃ k, member c δ k ∈ 𝓝 z := by
  rcases z.property.1 with h | h
  · exact ⟨Classical.arbitrary ι, Filter.mem_of_superset
      ((isOpen_lowerHalf.preimage continuous_subtypeVal).mem_nhds h)
      fun _ ↦ mem_member_of_mem_lowerPart _⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 h
    refine ⟨k, Filter.mem_of_superset
      ((((isOpen_band k).sdiff isClosed_singleton).preimage continuous_subtypeVal).mem_nhds
        ⟨hk, fun h ↦ z.property.2 ⟨k, h.symm⟩⟩) ?_⟩
    rintro w ⟨hw, hwk⟩
    exact ⟨.inr hw, hwk⟩

private theorem isPathConnected_member (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) : IsPathConnected (member c δ k) := by
  have := (starConvex_fan (c := c) hδ k).pathConnectedSpace_diff_singleton
    (by simp [Complex.rank_real_complex]) (by positivity) (sphere_subset_fan hδ k)
  exact (isPathConnected_iff_pathConnectedSpace.2 this).preimage_coe
    (fan_diff_subset_spine hδ hc k)

private theorem isSimplyConnected_lowerPart : IsSimplyConnected (lowerPart c δ) :=
  have hsub : lowerHalf ⊆ range (Subtype.val : spine c δ → ℂ) := by
    rw [Subtype.range_coe]
    exact lowerHalf_subset_spine
  have hconv : Convex ℝ lowerHalf := by
    unfold lowerHalf
    exact convex_halfSpace_im_lt 0
  have : ContractibleSpace lowerHalf :=
    hconv.contractibleSpace ⟨-I, negI_mem_lowerHalf⟩
  have : ContractibleSpace (lowerPart c δ) :=
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsub).contractibleSpace
  SimplyConnectedSpace.ofContractible _

/-! ### The loops avoid the points -/

theorem zero_mem_compl_range (h0 : ∀ i, c i ≠ 0) : (0 : ℂ) ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  exact h0 i (by simpa using hi)

private theorem segment_mem_compl_range (h0 : ∀ i, c i ≠ 0) (t : unitInterval) :
    Path.segment (0 : ℂ) (-I) t ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  have hre : (Path.segment (0 : ℂ) (-I) t).re = 0 := by
    simp [AffineMap.lineMap_apply_module']
  rw [← hi, ofReal_re] at hre
  exact h0 i hre

private theorem negI_mem_fan (k : ι) : -I ∈ fan c δ k \ {(c k : ℂ)} :=
  ⟨.inl negI_mem_lowerHalf, fun h ↦ by
    simpa using congrArg im (mem_singleton_iff.1 h)⟩

private theorem approach_mem_fan (hδ : 0 < δ) (k : ι) (t : unitInterval) :
    approach (c k) (δ / 4) t ∈ fan c δ k \ {(c k : ℂ)} := by
  suffices h : range (approach (c k) (δ / 4)) ⊆ fan c δ k \ {(c k : ℂ)} from h (mem_range_self t)
  rw [approach_def, Path.trans_range, union_subset_iff, range_subset_iff, range_subset_iff]
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · have him : (Path.segment (-I) ((c k + δ / 4 : ℝ) - I) t).im = -1 := by
      simp [AffineMap.lineMap_apply_module']
    refine ⟨.inl (mem_lowerHalf.2 (by rw [him]; norm_num)), fun h ↦ ?_⟩
    have := congrArg im (mem_singleton_iff.1 h)
    rw [him, ofReal_im] at this
    norm_num at this
  · have hre : (Path.segment ((c k + δ / 4 : ℝ) - I) ((c k + δ / 4 : ℝ) : ℂ) t).re =
        c k + δ / 4 := by
      simp [AffineMap.lineMap_apply_module']
    refine ⟨.inr (mem_band.2 ?_), fun h ↦ ?_⟩
    · rw [hre, add_sub_cancel_left, abs_of_pos (by positivity)]
      linarith
    · have := congrArg re (mem_singleton_iff.1 h)
      rw [hre, ofReal_re] at this
      linarith

private theorem circle_mem_fan (hδ : 0 < δ) (k : ι) (t : unitInterval) :
    circle (c k) (δ / 4) t ∈ fan c δ k \ {(c k : ℂ)} := by
  have hn : ‖circle (c k) (δ / 4) t - c k‖ = δ / 4 := by
    rw [circle_apply, circleMap_sub_center, norm_circleMap_zero, abs_of_pos (by positivity)]
  refine ⟨sphere_subset_fan hδ k (mem_sphere_iff_norm.2 hn), fun h ↦ ?_⟩
  rw [mem_singleton_iff.1 h, sub_self, norm_zero] at hn
  linarith

/-- The loop about `x` of radius `r` based at `-i`: along `approach x r`, around the circle, and
back. -/
private def loopBelow (x r : ℝ) : Path (-I) (-I) :=
  (approach x r).trans ((circle x r).trans (approach x r).symm)

private theorem loopBelow_def (x r : ℝ) :
    loopBelow x r = (approach x r).trans ((circle x r).trans (approach x r).symm) :=
  (rfl)

private theorem loopInPlane_eq (x r : ℝ) :
    loopInPlane x r =
      (Path.segment 0 (-I)).trans ((loopBelow x r).trans (Path.segment 0 (-I)).symm) := by
  rw [loopInPlane_def, loopBelow_def]

private theorem loopBelow_mem_fan (hδ : 0 < δ) (k : ι) (t : unitInterval) :
    loopBelow (c k) (δ / 4) t ∈ fan c δ k \ {(c k : ℂ)} := by
  suffices h : range (loopBelow (c k) (δ / 4)) ⊆ fan c δ k \ {(c k : ℂ)} from h (mem_range_self t)
  rw [loopBelow_def, Path.trans_range, Path.trans_range, Path.symm_range, union_subset_iff,
    union_subset_iff, range_subset_iff, range_subset_iff]
  exact ⟨approach_mem_fan hδ k, circle_mem_fan hδ k, approach_mem_fan hδ k⟩

theorem loopInPlane_mem_compl_range (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (h0 : ∀ i, c i ≠ 0) (k : ι) (t : unitInterval) :
    loopInPlane (c k) (δ / 4) t ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  suffices h : range (loopInPlane (c k) (δ / 4)) ⊆ (range fun i ↦ (c i : ℂ))ᶜ from
    h (mem_range_self t)
  rw [loopInPlane_eq, Path.trans_range, Path.trans_range, Path.symm_range, union_subset_iff,
    union_subset_iff, range_subset_iff, range_subset_iff]
  exact ⟨segment_mem_compl_range h0, fun t ↦ spine_subset_compl_range
    (fan_diff_subset_spine hδ hc k (loopBelow_mem_fan hδ k t)), segment_mem_compl_range h0⟩

/-! ### The generator of each member of the cover -/

/-- In the punctured fan about `c k`, some isomorphism of the fundamental group at `-i` with `ℤ`
sends the class of the loop about `c k` to `1`. -/
private theorem exists_mulEquiv_fan (hδ : 0 < δ) (k : ι) :
    ∃ e : FundamentalGroup ↥(fan c δ k \ {(c k : ℂ)}) ⟨-I, negI_mem_fan k⟩ ≃* Multiplicative ℤ,
      e (fromPath (Path.Homotopic.Quotient.mk ((loopBelow (c k) (δ / 4)).codRestrict
        (x := ⟨-I, negI_mem_fan k⟩) (y := ⟨-I, negI_mem_fan k⟩) (loopBelow_mem_fan hδ k)))) =
        Multiplicative.ofAdd 1 := by
  have hV := starConvex_fan (c := c) hδ k
  have hr : (0 : ℝ) < δ / 4 := by positivity
  have hS := sphere_subset_fan (c := c) hδ k
  let S := hV.sphereHomotopyEquiv hr hS
  let x0 : sphere (c k : ℂ) (δ / 4) := (TauCeti.sphereCircleHomeomorph _ hr).symm 1
  let y : ↥(fan c δ k \ {(c k : ℂ)}) :=
    ⟨((c k + δ / 4 : ℝ) : ℂ), (circle (c k) (δ / 4)).source ▸ circle_mem_fan hδ k 0⟩
  let σ : Path y y := (circle (c k) (δ / 4)).codRestrict (x := y) (y := y) (circle_mem_fan hδ k)
  have hy : Homeomorph.refl _ (S x0) = y := Subtype.ext (by simp [S, x0, y])
  -- The circle `σ` is the loop `sphereLoop` of Tau Ceti, read at the base point `y`.
  have hσ : FundamentalGroup.homeomorphMulEquivOfEq (Homeomorph.refl _) hy
      (FundamentalGroup.map S.toFun x0
        (fromPath (Path.Homotopic.Quotient.mk (Complex.sphereLoop (c k : ℂ) hr)))) =
      fromPath (Path.Homotopic.Quotient.mk σ) := by
    rw [TauCeti.FundamentalGroup.map_fromPath, FundamentalGroup.homeomorphMulEquivOfEq_apply,
      FundamentalGroup.mapOfEq_fromPath_mk]
    congr 2
    ext t
    rw [Path.codRestrict_coe, circle_apply, Path.cast_coe, Path.map_coe, Function.comp_apply]
    simp only [Homeomorph.coe_refl, Path.map_coe, Function.comp_apply, ContinuousMap.id_apply,
      StarConvex.coe_sphereHomotopyEquiv_apply, S]
    exact Complex.coe_sphereLoop_apply _ hr t
  let ρ : Path (⟨-I, negI_mem_fan k⟩ : ↥(fan c δ k \ {(c k : ℂ)})) y :=
    (approach (c k) (δ / 4)).codRestrict (approach_mem_fan hδ k)
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath ρ).trans
    ((FundamentalGroup.homeomorphMulEquivOfEq (Homeomorph.refl _) hy).symm.trans
      (hV.fundamentalGroupMulEquivInt hr hS x0)), ?_⟩
  have hL : (loopBelow (c k) (δ / 4)).codRestrict (x := ⟨-I, negI_mem_fan k⟩)
      (y := ⟨-I, negI_mem_fan k⟩) (loopBelow_mem_fan hδ k) = ρ.trans (σ.trans ρ.symm) := by
    ext t
    rw [Path.codRestrict_coe, loopBelow_def]
    simp [ρ, σ, Path.trans_apply, apply_dite Subtype.val]
  rw [hL, ← FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_fromPath_mk,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply, ← hσ,
    MulEquiv.symm_apply_apply]
  exact hV.fundamentalGroupMulEquivInt_sphereLoop hr hS

private theorem mem_member {k : ι} {z : spine c δ} :
    z ∈ member c δ k ↔ (z : ℂ) ∈ fan c δ k \ {(c k : ℂ)} := Iff.rfl

/-- The base point `-i` of the spine. -/
private def spineBase : spine c δ := ⟨-I, lowerHalf_subset_spine negI_mem_lowerHalf⟩

private theorem coe_spineBase : (spineBase (c := c) (δ := δ) : ℂ) = -I := (rfl)

private theorem spineBase_mem_lowerPart : spineBase ∈ lowerPart c δ := negI_mem_lowerHalf

/-- The loop about `c k` based at `-i`, as a loop in the spine. -/
private def spineLoop (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (k : ι) :
    Path (spineBase (c := c) (δ := δ)) spineBase :=
  (loopBelow (c k) (δ / 4)).codRestrict fun t ↦
    fan_diff_subset_spine hδ hc k (loopBelow_mem_fan hδ k t)

private theorem coe_spineLoop_apply (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) (t : unitInterval) : (spineLoop hδ hc k t : ℂ) = loopBelow (c k) (δ / 4) t :=
  Path.codRestrict_coe _ _ t

private theorem spineLoop_mem_member (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) (t : unitInterval) : spineLoop hδ hc k t ∈ member c δ k := by
  rw [mem_member, coe_spineLoop_apply]
  exact loopBelow_mem_fan hδ k t

/-- In the `k`-th member of the cover of the spine, some isomorphism of the fundamental group at
`-i` with `ℤ` sends the class of the loop about `c k` to `1`. -/
private theorem exists_mulEquiv_member (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) :
    ∃ e : FundamentalGroup (member c δ k)
        ⟨spineBase, mem_member_of_mem_lowerPart k spineBase_mem_lowerPart⟩ ≃* Multiplicative ℤ,
      e (fromPath (Path.Homotopic.Quotient.mk
        ((spineLoop hδ hc k).codRestrict (spineLoop_mem_member hδ hc k)))) =
        Multiplicative.ofAdd 1 := by
  obtain ⟨e, he⟩ := exists_mulEquiv_fan (c := c) hδ k
  have hsub : fan c δ k \ {(c k : ℂ)} ⊆ range (Subtype.val : spine c δ → ℂ) := by
    rw [Subtype.range_coe]
    exact fan_diff_subset_spine hδ hc k
  let H : member c δ k ≃ₜ ↥(fan c δ k \ {(c k : ℂ)}) :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsub
  have hH : H ⟨spineBase, mem_member_of_mem_lowerPart k spineBase_mem_lowerPart⟩ =
      ⟨-I, negI_mem_fan k⟩ :=
    Subtype.ext ((Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe _ _ _).trans
      coe_spineBase)
  refine ⟨(FundamentalGroup.homeomorphMulEquivOfEq H hH).trans e, ?_⟩
  rw [MulEquiv.trans_apply, FundamentalGroup.homeomorphMulEquivOfEq_apply,
    FundamentalGroup.mapOfEq_fromPath_mk, ← he]
  congr 3
  ext t
  have hHc (z : member c δ k) : (H z : ℂ) = (z : spine c δ) :=
    Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe _ _ _
  simp only [Path.codRestrict_coe, Path.cast_coe, Path.map_coe, Function.comp_apply,
    ContinuousMap.coe_ofClass, hHc, coe_spineLoop_apply]

/-! ### The free basis -/

section Main

variable (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (h0 : ∀ i, c i ≠ 0)

/-- The loop about `c k`, based at `0`, in the plane minus the points `c i`: from `0` straight
down to `-i`, right or left to `c k + r - i`, straight up to `c k + r`, once counterclockwise
around the circle of radius `r = δ / 4` about `c k`, and back the same way. -/
def loop (k : ι) :
    Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ)
      ⟨0, zero_mem_compl_range h0⟩ :=
  (loopInPlane (c k) (δ / 4)).codRestrict (loopInPlane_mem_compl_range hδ hc h0 k)

theorem loop_def (k : ι) :
    loop hδ hc h0 k =
      (loopInPlane (c k) (δ / 4)).codRestrict (loopInPlane_mem_compl_range hδ hc h0 k) :=
  (rfl)

@[simp]
theorem coe_loop_apply (k : ι) (t : unitInterval) :
    (loop hδ hc h0 k t : ℂ) = loopInPlane (c k) (δ / 4) t := by
  rw [loop_def, Path.codRestrict_coe]

private theorem bijective_lift_loop_of_isEmpty [IsEmpty ι] :
    Function.Bijective (FreeGroup.lift fun k ↦ fromPath (Path.Homotopic.Quotient.mk
      (loop hδ hc h0 k))) := by
  have hconv : Convex ℝ (range fun i ↦ (c i : ℂ))ᶜ := by
    rw [range_eq_empty, compl_empty]
    exact convex_univ
  have := hconv.contractibleSpace ⟨0, zero_mem_compl_range h0⟩
  exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩

private theorem bijective_lift_loop_of_nonempty [Nonempty ι] :
    Function.Bijective (FreeGroup.lift fun k ↦ fromPath (Path.Homotopic.Quotient.mk
      (loop hδ hc h0 k))) := by
  let E := spineHomotopyEquiv (c := c) hδ
  let vK := TauCeti.vanKampenWideEquiv (U := member c δ) (C := lowerPart c δ)
    exists_member_mem_nhds (isPathConnected_member hδ hc) isSimplyConnected_lowerPart
    (fun k _ ↦ mem_member_of_mem_lowerPart k) (fun _ _ hij ↦ member_inter_member_subset hc hij)
    spineBase_mem_lowerPart
  let e (k : ι) := (exists_mulEquiv_member hδ hc k).choose
  have he (k : ι) := (exists_mulEquiv_member hδ hc k).choose_spec
  have hEc (z : spine c δ) : (E.toFun z : ℂ) = z := by simp [E, spineHomotopyEquiv]
  have hE : (E.toFun spineBase : ℂ) = -I := (hEc _).trans coe_spineBase
  let Φ := MulEquiv.ofBijective _ (E.fundamentalGroup_map_bijective spineBase)
  let D : Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ)
      (E.toFun spineBase) :=
    ((Path.segment (0 : ℂ) (-I)).cast rfl hE).codRestrict fun t ↦ by
      rw [Path.cast_coe]
      exact segment_mem_compl_range h0 t
  let ψ := freeGroupEquivCoprodI.trans ((MulEquiv.coprodICongr fun k ↦
    FreeGroup.mulEquivIntOfUnique.trans (e k).symm).trans
      (vK.trans (Φ.trans (FundamentalGroup.fundamentalGroupMulEquivOfPath D).symm)))
  have hψ : (FreeGroup.lift fun k ↦ fromPath (Path.Homotopic.Quotient.mk (loop hδ hc h0 k))) =
      ψ.toMonoidHom := by
    refine FreeGroup.ext_hom _ _ fun k ↦ ?_
    have hk : (e k).symm (Multiplicative.ofAdd 1) = fromPath (Path.Homotopic.Quotient.mk
        ((spineLoop hδ hc k).codRestrict (spineLoop_mem_member hδ hc k))) :=
      (e k).symm_apply_eq.mpr (he k).symm
    have hv : vK (Monoid.CoprodI.of (fromPath (Path.Homotopic.Quotient.mk
        ((spineLoop hδ hc k).codRestrict (spineLoop_mem_member hδ hc k))))) =
          fromPath (Path.Homotopic.Quotient.mk (spineLoop hδ hc k)) :=
      (TauCeti.vanKampenWideEquiv_apply _ _ _ _ _ _ _).trans
        ((TauCeti.vanKampenWideLift_of _ _ _ _).trans
          ((TauCeti.FundamentalGroup.map_fromPath _ _ _).trans
            (congrArg (fun q ↦ fromPath (Path.Homotopic.Quotient.mk q))
              (Path.map_codRestrict _ _))))
    have h1 : FreeGroup.mulEquivIntOfUnique (FreeGroup.of ()) = Multiplicative.ofAdd 1 := by
      simp [FreeGroup.mulEquivIntOfUnique, FreeGroup.equivIntOfUnique]
    simp only [FreeGroup.lift_apply_of, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, ψ,
      freeGroupEquivCoprodI_apply, MulEquiv.coprodICongr_apply_of, h1, hk, hv,
      Φ, MulEquiv.ofBijective_apply, TauCeti.FundamentalGroup.map_fromPath,
      FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_fromPath_mk]
    congr 2
    ext t
    simp [loopInPlane_eq, D, Path.trans_apply, apply_dite Subtype.val,
      Path.map_coe, Path.codRestrict_coe, coe_spineLoop_apply, AffineMap.lineMap_apply_one_sub, hE,
      Function.comp_apply, hEc]
  rw [hψ]
  exact ψ.bijective

/-- **The fundamental group of the plane minus the real points `c i`**, based at `0`, any two of
the points at distance at least `δ > 0` and none of them `0`, is the free group on `ι`, the class
of `loop hδ hc h0 k` corresponding to the generator `FreeGroup.of k`
(`fundamentalGroupMulEquiv_loop`). -/
def fundamentalGroupMulEquiv :
    FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩ ≃* FreeGroup ι :=
  (MulEquiv.ofBijective _ (by
    rcases isEmpty_or_nonempty ι with _ | _
    · exact bijective_lift_loop_of_isEmpty hδ hc h0
    · exact bijective_lift_loop_of_nonempty hδ hc h0)).symm

/-- The inverse of `fundamentalGroupMulEquiv` sends a word in the generators to the same word in
the classes of the loops. -/
theorem fundamentalGroupMulEquiv_symm_apply (g : FreeGroup ι) :
    (fundamentalGroupMulEquiv hδ hc h0).symm g =
      FreeGroup.lift (fun k ↦ fromPath (Path.Homotopic.Quotient.mk (loop hδ hc h0 k))) g :=
  (rfl)

theorem fundamentalGroupMulEquiv_symm_of (k : ι) :
    (fundamentalGroupMulEquiv hδ hc h0).symm (FreeGroup.of k) =
      fromPath (Path.Homotopic.Quotient.mk (loop hδ hc h0 k)) := by
  rw [fundamentalGroupMulEquiv_symm_apply, FreeGroup.lift_apply_of]

/-- `fundamentalGroupMulEquiv` sends the class of the loop about `c k` to the generator
`FreeGroup.of k`. -/
@[simp]
theorem fundamentalGroupMulEquiv_loop (k : ι) :
    fundamentalGroupMulEquiv hδ hc h0 (fromPath (Path.Homotopic.Quotient.mk (loop hδ hc h0 k))) =
      FreeGroup.of k := by
  rw [← fundamentalGroupMulEquiv_symm_of, MulEquiv.apply_symm_apply]

end Main

end PlaneMinusRealPoints

end SymplecticGeometry
