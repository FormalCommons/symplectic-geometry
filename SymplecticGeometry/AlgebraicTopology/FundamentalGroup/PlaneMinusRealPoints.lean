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
public import SymplecticGeometry.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Topology.Homotopy.Path

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.CategoryTheory.Groupoid.SingleObj
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.AlgebraicTopology.LocalCoefficient.Representation
import TauCeti.GroupTheory.CoprodI
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# The plane minus real points: a free basis of loops, and the large circle

Let `c : ι → ℝ` be nonzero reals, any two of them at distance at least `δ > 0`. For finitely
many distinct nonzero reals, at least two of them, `δ = Set.infsep (Set.range c)` will do: it is
positive by `Set.Finite.infsep_pos_iff_nontrivial`, and at most each distance by
`Set.infsep_le_dist_of_mem` and `Real.dist_eq`; with fewer points any `δ > 0` will do. The
fundamental group of `ℂ` with the points `c i` removed, based at `0`, is free on the loops
`PlaneMinusRealPoints.loop hδ hc h0 k`. The loop about `c k` goes from `0` straight down to `-i`,
right or left to `c k + r - i` and straight up to `c k + r`, once counterclockwise around the
circle of radius `r = δ / 4` about `c k`, and back the same way.

When the points are positive, `c 0 < c 1 < ⋯ < c (m - 1)`, and all less than `R`, the loop
`PlaneMinusRealPoints.outerLoop`, which runs out along a ray in the upper half-plane, once
counterclockwise around the circle of radius `R` about `0`, and back, is the product of these
loops: run one after the other from the largest point to the smallest, they are homotopic to it.

## Main definitions

* `SymplecticGeometry.PlaneMinusRealPoints.approach x r`, `circle x r` and `loopInPlane x r`:
  the loop in `ℂ` about `x` of radius `r`, based at `0`, and the pieces it is made of.
* `SymplecticGeometry.PlaneMinusRealPoints.fan c δ k`: the open lower half-plane together with
  the open vertical strip of half-width `δ / 2` about `c k`. It is star-convex about `c k`
  (`starConvex_fan`), and contains no other point `c i` (`eq_of_ofReal_mem_fan`).
* `SymplecticGeometry.PlaneMinusRealPoints.loop hδ hc h0 k`: the loop about `c k`, based at `0`, in
  the plane minus the points.
* `SymplecticGeometry.PlaneMinusRealPoints.fundamentalGroupMulEquiv hδ hc h0`: the isomorphism
  of `π₁(ℂ ∖ {c i}, 0)` with `FreeGroup ι`.
* `SymplecticGeometry.PlaneMinusRealPoints.outerLoopInPlane R θ` and
  `outerLoop h0 hR hθ₀ hθπ`: the loop based at `0` that runs along the ray at the angle `θ` out
  to the circle `circlePath 0 R θ`, around it, and back, in `ℂ` and in the plane minus the points.

## Main results

* `SymplecticGeometry.PlaneMinusRealPoints.fundamentalGroupMulEquiv_loop`: the isomorphism sends
  the class of `loop hδ hc h0 k` to `FreeGroup.of k`; its inverse is `FreeGroup.lift` of the
  classes of the loops (`fundamentalGroupMulEquiv_symm_apply`).
* `SymplecticGeometry.PlaneMinusRealPoints.fromPath_outerLoop_eq_prod`: for increasing positive
  points, the class of `outerLoop` is the product of the classes of the loops, in the order of the
  points, so that the loop about the largest point runs first.

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

The large circle is handled without the van Kampen theorem, as in the proof of Tau Ceti's
`TauCeti.ThricePuncturedSphere.αPlus_trans_δ_trans_symm_homotopic_γ0_trans_γ1`
(`TauCeti/AlgebraicTopology/ThricePuncturedSphere/LoopAtInfinity.lean`, same commit), which does
it for the two points `0` and `1`: the circles are cut where they meet the real axis, and the
pieces are compared in the closed upper and lower half-planes minus the points, each star-convex,
so that paths in one of them with the same end points are homotopic. `starConvex_halfPlane` and
`isPathHomotopyTrivial_half` follow the private lemmas `starConvex_setOf_mul_im` and
`isSimplyConnected_setOf_mul_im` of that file. For any number of points the comparisons are
bookkept in `π₁` through Tau Ceti's functor `TauCeti.Groupoid.functorOfEndHom`, for the paths from
`0` that Tau Ceti's `TauCeti.LocalCoefficientSystem.pathFromBase` chooses, so that it sends any
path to `π₁` and a loop at `0` to its class. For a real point `z` let `g z` be the class of the
loop that goes from `0` to `z` through the lower half-plane and back through the upper one. It is
constant between consecutive points and `1` left of them, the loop about `c k` is
`(g (c k - r))⁻¹ * g (c k + r)`, and the large loop is `g R * (g (-R))⁻¹`, so the product of the
loops telescopes to the large loop.

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

/-- The circle about `x` of radius `r`, run once counterclockwise from `x + r`: the path
`circlePath x r 0`, with its end points written as the real number `x + r`. -/
def circle (x r : ℝ) : Path ((x + r : ℝ) : ℂ) ((x + r : ℝ) : ℂ) :=
  (circlePath x r 0).cast (by simp [circleMap]) (by simp [circleMap])

theorem circle_def (x r : ℝ) :
    circle x r = (circlePath x r 0).cast (by simp [circleMap]) (by simp [circleMap]) :=
  (rfl)

theorem circle_apply (x r : ℝ) (t : unitInterval) :
    circle x r t = circleMap x r (2 * Real.pi * t) := by
  rw [circle_def, Path.cast_coe, circlePath_apply, zero_add]

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
/-- The open lower half-plane together with the open vertical strip of half-width `δ / 2` about the
real point `c k`. -/
def fan (k : ι) : Set ℂ := lowerHalf ∪ band c δ k

/-- A point lies in the fan about `c k` when it lies in the open lower half-plane or within `δ / 2`
of `c k` in its real part. -/
theorem mem_fan_iff {k : ι} {z : ℂ} : z ∈ fan c δ k ↔ z.im < 0 ∨ |z.re - c k| < δ / 2 :=
  Iff.rfl

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
theorem starConvex_fan (hδ : 0 < δ) (k : ι) : StarConvex ℝ (c k : ℂ) (fan c δ k) := by
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

/-- The circle of radius `δ / 4` about `c k` lies in the fan about `c k`. -/
theorem sphere_subset_fan (hδ : 0 < δ) (k : ι) :
    sphere (c k : ℂ) (δ / 4) ⊆ fan c δ k := by
  intro z hz
  refine .inr (mem_band.2 ?_)
  have h := abs_re_le_norm (z - c k)
  rw [mem_sphere_iff_norm] at hz
  rw [sub_re, ofReal_re] at h
  linarith

/-- The open disc of radius `δ / 2` about `c k` lies in the fan about `c k`. -/
theorem ball_subset_fan (k : ι) : ball (c k : ℂ) (δ / 2) ⊆ fan c δ k := by
  intro z hz
  refine .inr (mem_band.2 ?_)
  have h := abs_re_le_norm (z - c k)
  rw [mem_ball, dist_eq_norm] at hz
  rw [sub_re, ofReal_re] at h
  linarith

/-- A point of the open lower half-plane lies in the fan about `c k`, and is not `c k`. -/
theorem mem_fan_diff_of_im_neg (k : ι) {z : ℂ} (hz : z.im < 0) : z ∈ fan c δ k \ {(c k : ℂ)} :=
  ⟨.inl (mem_lowerHalf.2 hz), fun h ↦ by simp [mem_singleton_iff.1 h] at hz⟩

/-- Among the points `c i`, only `c k` lies in the fan about `c k`. -/
theorem eq_of_ofReal_mem_fan (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) {i k : ι}
    (h : (c i : ℂ) ∈ fan c δ k) : i = k :=
  h.elim (fun h ↦ (ofReal_notMem_lowerHalf _ h).elim) (eq_of_ofReal_mem_band hδ hc)

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

/-- The segment from `0` to `-i` avoids the points, if none of them is `0`. -/
theorem segment_mem_compl_range (h0 : ∀ i, c i ≠ 0) (t : unitInterval) :
    Path.segment (0 : ℂ) (-I) t ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  have hre : (Path.segment (0 : ℂ) (-I) t).re = 0 := by
    simp [AffineMap.lineMap_apply_module']
  rw [← hi, ofReal_re] at hre
  exact h0 i hre

/-- The point `-i` lies in the fan about `c k`, and is not `c k`. -/
theorem negI_mem_fan (k : ι) : -I ∈ fan c δ k \ {(c k : ℂ)} :=
  mem_fan_diff_of_im_neg k (by simp)

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
  rw [MulEquiv.trans_apply, FundamentalGroup.homeomorphMulEquivOfEq_fromPath_mk, ← he]
  congr 3
  ext t
  have hHc (z : member c δ k) : (H z : ℂ) = (z : spine c δ) :=
    Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe _ _ _
  simp only [Path.codRestrict_coe, Path.cast_coe, Path.map_coe, Function.comp_apply,
    hHc, coe_spineLoop_apply]

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

/-! ### The large circle -/

/-- The loop in `ℂ` based at `0` that runs along the ray at the angle `θ` out to the circle about
`0` of radius `R`, once counterclockwise around that circle, and back along the ray. -/
def outerLoopInPlane (R θ : ℝ) : Path (0 : ℂ) 0 :=
  (Path.segment 0 (circleMap 0 R θ)).trans
    ((circlePath 0 R θ).trans (Path.segment 0 (circleMap 0 R θ)).symm)

theorem outerLoopInPlane_def (R θ : ℝ) :
    outerLoopInPlane R θ =
      (Path.segment 0 (circleMap 0 R θ)).trans
        ((circlePath 0 R θ).trans (Path.segment 0 (circleMap 0 R θ)).symm) :=
  (rfl)

variable {R θ : ℝ}

private theorem segment_zero_circleMap_mem_compl_range (h0 : ∀ i, c i ≠ 0)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (t : unitInterval) :
    Path.segment 0 (circleMap 0 R θ) t ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  have hR : R ≠ 0 := by
    rintro rfl
    exact h0 i (by simpa [AffineMap.lineMap_apply_module'] using hi)
  have him := congrArg im hi
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
  simp only [ofReal_im, Path.segment_apply, AffineMap.lineMap_apply_module',
    sub_zero] at him
  simp only [circleMap, zero_add, real_smul, add_zero, mul_im, ofReal_re, exp_ofReal_mul_I_im,
    ofReal_im, exp_ofReal_mul_I_re, zero_mul, mul_re, sub_zero, zero_eq_mul, Icc.coe_eq_zero,
    mul_eq_zero, hR, hsin.ne', or_self, or_false] at him
  rcases him with rfl
  exact h0 i (by simpa [AffineMap.lineMap_apply_module'] using hi)

private theorem circleMap_zero_mem_compl_range (hR : ∀ i, |c i| < R) (φ : ℝ) :
    circleMap 0 R φ ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  have h := congrArg norm hi
  rw [norm_circleMap_zero, norm_real, Real.norm_eq_abs, abs_of_pos ((abs_nonneg _).trans_lt
    (hR i))] at h
  exact (hR i).ne h

theorem outerLoopInPlane_mem_compl_range (h0 : ∀ i, c i ≠ 0) (hR : ∀ i, |c i| < R)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (t : unitInterval) :
    outerLoopInPlane R θ t ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  suffices h : range (outerLoopInPlane R θ) ⊆ (range fun i ↦ (c i : ℂ))ᶜ from
    h (mem_range_self t)
  rw [outerLoopInPlane_def, Path.trans_range, Path.trans_range, Path.symm_range,
    union_subset_iff, union_subset_iff, range_subset_iff, range_subset_iff]
  exact ⟨segment_zero_circleMap_mem_compl_range h0 hθ₀ hθπ,
    fun t ↦ circlePath_apply 0 R θ t ▸ circleMap_zero_mem_compl_range hR _,
    segment_zero_circleMap_mem_compl_range h0 hθ₀ hθπ⟩

/-- The loop based at `0` in the plane minus the real points `c i`, all of absolute value less
than `R`, that runs along the ray at the angle `θ ∈ (0, π)` out to the circle about `0` of radius
`R`, once counterclockwise around it, and back along the ray. -/
def outerLoop (h0 : ∀ i, c i ≠ 0) (hR : ∀ i, |c i| < R) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) :
    Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ)
      ⟨0, zero_mem_compl_range h0⟩ :=
  (outerLoopInPlane R θ).codRestrict (outerLoopInPlane_mem_compl_range h0 hR hθ₀ hθπ)

theorem outerLoop_def (h0 : ∀ i, c i ≠ 0) (hR : ∀ i, |c i| < R) (hθ₀ : 0 < θ)
    (hθπ : θ < Real.pi) :
    outerLoop h0 hR hθ₀ hθπ =
      (outerLoopInPlane R θ).codRestrict (outerLoopInPlane_mem_compl_range h0 hR hθ₀ hθπ) :=
  (rfl)

@[simp]
theorem coe_outerLoop_apply (h0 : ∀ i, c i ≠ 0) (hR : ∀ i, |c i| < R) (hθ₀ : 0 < θ)
    (hθπ : θ < Real.pi) (t : unitInterval) :
    (outerLoop h0 hR hθ₀ hθπ t : ℂ) = outerLoopInPlane R θ t := by
  rw [outerLoop_def, Path.codRestrict_coe]

/-! ### The closed half-planes -/

private theorem mem_compl_range_inter_halfPlane (h0 : ∀ i, c i ≠ 0) (ε : ℝ) :
    (0 : ℂ) ∈ (range fun i ↦ (c i : ℂ))ᶜ ∩ {z | 0 ≤ ε * z.im} :=
  ⟨zero_mem_compl_range h0, by simp⟩

private theorem convex_halfPlane (ε : ℝ) : Convex ℝ {z : ℂ | 0 ≤ ε * z.im} :=
  convex_halfSpace_ge ((LinearMap.lsmul ℝ ℝ ε ∘ₗ Complex.imLm).isLinear) 0

/-- The closed upper (`ε > 0`) or lower (`ε < 0`) half-plane minus the real points `c i` is
star-convex about `ε i`. -/
private theorem starConvex_halfPlane {ε : ℝ} (hε : ε ≠ 0) :
    StarConvex ℝ (ε * I) ((range fun i ↦ (c i : ℂ))ᶜ ∩ {z | 0 ≤ ε * z.im}) := by
  have hmem : (ε * I : ℂ) ∈ (range fun i ↦ (c i : ℂ))ᶜ ∩ {z | 0 ≤ ε * z.im} := by
    refine ⟨?_, by simpa using mul_self_nonneg ε⟩
    rintro ⟨i, hi⟩
    exact hε (by simpa using congrArg im hi.symm)
  refine (starConvex_iff_forall_pos hmem).2 fun z hz a b ha hb _ ↦ ?_
  have h2 : 0 ≤ ε * z.im := hz.2
  have hpos : 0 < ε * (a • (ε * I) + b • z).im := by
    have : ε * (a • (ε * I) + b • z).im = a * ε ^ 2 + b * (ε * z.im) := by
      simp only [add_im, smul_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]
      ring
    rw [this]
    have : 0 < ε ^ 2 := by positivity
    positivity
  refine ⟨?_, hpos.le⟩
  rintro ⟨i, hi⟩
  rw [← hi, ofReal_im, mul_zero] at hpos
  exact lt_irrefl _ hpos

variable (c) in
/-- The points of the plane minus the real points `c i` in the closed upper (`ε > 0`) or lower
(`ε < 0`) half-plane. -/
private def half (ε : ℝ) : Set ↥(range fun i ↦ (c i : ℂ))ᶜ := {z | 0 ≤ ε * (z : ℂ).im}

private theorem isPathHomotopyTrivial_half {ε : ℝ} (hε : ε ≠ 0) :
    IsPathHomotopyTrivial (half c ε) := by
  refine IsSimplyConnected.isPathHomotopyTrivial ?_
  rw [← Topology.IsEmbedding.subtypeVal.isSimplyConnected_image]
  have himage : ((↑) : ↥(range fun i ↦ (c i : ℂ))ᶜ → ℂ) '' half c ε =
      (range fun i ↦ (c i : ℂ))ᶜ ∩ {z | 0 ≤ ε * z.im} :=
    Subtype.image_preimage_coe _ {z : ℂ | 0 ≤ ε * z.im}
  rw [himage]
  have hne : ((range fun i ↦ (c i : ℂ))ᶜ ∩ {z | 0 ≤ ε * z.im}).Nonempty := by
    refine ⟨ε * I, ?_, by simpa using mul_self_nonneg ε⟩
    rintro ⟨i, hi⟩
    exact hε (by simpa using congrArg im hi.symm)
  have := (starConvex_halfPlane (c := c) hε).contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

private theorem range_codRestrict_subset_half {ε : ℝ} {a b : ↥(range fun i ↦ (c i : ℂ))ᶜ}
    {γ : Path (a : ℂ) b} (hγ : ∀ t, γ t ∈ (range fun i ↦ (c i : ℂ))ᶜ)
    (h : range γ ⊆ {z : ℂ | 0 ≤ ε * z.im}) : range (γ.codRestrict hγ) ⊆ half c ε := by
  rintro _ ⟨t, rfl⟩
  exact h ⟨t, (Path.codRestrict_coe _ _ t).symm⟩

/-! ### Paths read in the fundamental group -/

section Telescope

open CategoryTheory

variable (h0 : ∀ i, c i ≠ 0)

include h0 in
private theorem range_segment_trans_segment_subset {ε : ℝ} (hε : ε ≠ 0)
    (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) (hz : z ∈ half c ε) :
    range ((Path.segment (0 : ℂ) (ε * I)).trans (Path.segment (ε * I) (z : ℂ))) ⊆
      (range fun i ↦ (c i : ℂ))ᶜ ∩ {z | 0 ≤ ε * z.im} := by
  rw [Path.trans_range, Path.range_segment, Path.range_segment, segment_symm]
  exact union_subset ((starConvex_halfPlane hε).segment_subset
    (mem_compl_range_inter_halfPlane h0 ε))
    ((starConvex_halfPlane hε).segment_subset ⟨z.property, hz⟩)

/-- The path from `0` straight to `ε i` and on straight to `z`, a point of the closed half-plane
of `ε`. -/
private def via {ε : ℝ} (hε : ε ≠ 0) (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) (hz : z ∈ half c ε) :
    Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ) z :=
  ((Path.segment (0 : ℂ) (ε * I)).trans (Path.segment (ε * I) (z : ℂ))).codRestrict fun t ↦
    (range_segment_trans_segment_subset h0 hε z hz (mem_range_self t)).1

private theorem range_via_subset {ε : ℝ} (hε : ε ≠ 0) (z : ↥(range fun i ↦ (c i : ℂ))ᶜ)
    (hz : z ∈ half c ε) : range (via h0 hε z hz) ⊆ half c ε := by
  exact range_codRestrict_subset_half _ fun _ hx ↦
    (range_segment_trans_segment_subset h0 hε z hz hx).2

variable [Countable ι]

/-- The plane minus countably many points is path-connected; a local instance, for Tau Ceti's
`TauCeti.LocalCoefficientSystem.pathFromBase`. -/
private theorem pathConnectedSpace_compl_range :
    PathConnectedSpace ↥(range fun i ↦ (c i : ℂ))ᶜ :=
  isPathConnected_iff_pathConnectedSpace.1
    ((countable_range fun i ↦ (c i : ℂ)).isPathConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]
      exact Nat.one_lt_ofNat))

attribute [local instance] pathConnectedSpace_compl_range

/-- The functor from the fundamental groupoid of the plane minus the points `c i` to `π₁` at `0`
that reads a path through Tau Ceti's chosen path classes from `0`,
`TauCeti.LocalCoefficientSystem.pathFromBase`. -/
private def toFundamentalGroup :
    FundamentalGroupoid ↥(range fun i ↦ (c i : ℂ))ᶜ ⥤
      SingleObj
        (FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩) :=
  TauCeti.Groupoid.functorOfEndHom _
    (TauCeti.LocalCoefficientSystem.pathFromBase (X := TopCat.of ↥(range fun i ↦ (c i : ℂ))ᶜ)
      ⟨0, zero_mem_compl_range h0⟩)
    (MonoidHom.id _)

/-- The class in `π₁` at `0` of a path `p` between any two points: its end points are joined to
`0` along the chosen path classes. -/
private def ofPath {z w : ↥(range fun i ↦ (c i : ℂ))ᶜ} (p : Path z w) :
    FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩ :=
  (toFundamentalGroup h0).map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p))

variable {z w u : ↥(range fun i ↦ (c i : ℂ))ᶜ}

private theorem ofPath_def (p : Path z w) :
    ofPath h0 p =
      (toFundamentalGroup h0).map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)) :=
  (rfl)

private theorem ofPath_congr {p q : Path z w} (hpq : p.Homotopic q) :
    ofPath h0 p = ofPath h0 q := by
  rw [ofPath_def, ofPath_def, (FundamentalGroupoid.fromPath_eq_iff_homotopic p q).2 hpq]

@[simp]
private theorem ofPath_trans (p : Path z w) (q : Path w u) :
    ofPath h0 (p.trans q) = ofPath h0 q * ofPath h0 p := by
  rw [ofPath_def, ofPath_def, ofPath_def, Path.Homotopic.Quotient.mk_trans,
    ← SingleObj.comp_as_mul, ← Functor.map_comp, FundamentalGroupoid.comp_eq]

@[simp]
private theorem ofPath_refl (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) : ofPath h0 (Path.refl z) = 1 := by
  have h := ofPath_trans h0 (Path.refl z) (Path.refl z)
  rw [ofPath_congr h0 ⟨Path.Homotopy.transRefl _⟩] at h
  exact mul_eq_left.1 h.symm

@[simp]
private theorem ofPath_symm (p : Path z w) : ofPath h0 p.symm = (ofPath h0 p)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ofPath_trans, ofPath_congr h0 (Path.Homotopic.trans_symm p),
    ofPath_refl]

@[simp]
private theorem ofPath_cast {z' w' : ↥(range fun i ↦ (c i : ℂ))ᶜ} (p : Path z w) (hz : z' = z)
    (hw : w' = w) : ofPath h0 (p.cast hz hw) = ofPath h0 p := by
  subst hz hw
  rw [Path.cast_rfl_rfl]

/-- On loops at `0`, `ofPath` is the class of the loop. -/
private theorem ofPath_loop (γ : Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ)
    ⟨0, zero_mem_compl_range h0⟩) : ofPath h0 γ = fromPath (Path.Homotopic.Quotient.mk γ) := by
  rw [ofPath_def, toFundamentalGroup, TauCeti.Groupoid.functorOfEndHom_map,
    TauCeti.LocalCoefficientSystem.pathFromBase_mk,
    IsIso.inv_id, Category.id_comp,
    Category.comp_id, MonoidHom.id_apply]

open Classical in
/-- The class in the fundamental group of `via`, or `1` off the half-plane. -/
private def V (ε : ℝ) (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) :
    FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩ :=
  if h : ε ≠ 0 ∧ z ∈ half c ε then ofPath h0 (via h0 h.1 z h.2) else 1

/-- A path in a closed half-plane is read in the fundamental group through `via`. -/
private theorem ofPath_eq_V {ε : ℝ} (hε : ε ≠ 0) (p : Path z w) (hp : range p ⊆ half c ε) :
    ofPath h0 p = V h0 ε w * (V h0 ε z)⁻¹ := by
  have hz : z ∈ half c ε := hp ⟨0, p.source⟩
  have hw : w ∈ half c ε := hp ⟨1, p.target⟩
  have h := ofPath_congr h0
    (isPathHomotopyTrivial_def.mp (isPathHomotopyTrivial_half (c := c) hε)
      ((via h0 hε z hz).trans p) (via h0 hε w hw)
      (by rw [Path.trans_range]; exact union_subset (range_via_subset h0 hε z hz) hp)
      (range_via_subset h0 hε w hw))
  rw [ofPath_trans] at h
  rw [V, V, dite_eq_left ⟨hε, hw⟩, dite_eq_left ⟨hε, hz⟩, ← h, mul_inv_cancel_right]

private theorem V_zero {ε : ℝ} (hε : ε ≠ 0) : V h0 ε ⟨0, zero_mem_compl_range h0⟩ = 1 := by
  have hmem : (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ) ∈ half c ε :=
    (mem_compl_range_inter_halfPlane h0 ε).2
  rw [V, dite_eq_left ⟨hε, hmem⟩, ← ofPath_refl h0 ⟨0, _⟩]
  exact ofPath_congr h0 (isPathHomotopyTrivial_def.mp
    (isPathHomotopyTrivial_half (c := c) hε) _ _
    (range_via_subset h0 hε _ hmem) (by rw [Path.refl_range]; exact singleton_subset_iff.2 hmem))

/-- The class of the loop from `0` to a point `z` through the lower half-plane and back through
the upper one. -/
private def g (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) :
    FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩ :=
  (V h0 1 z)⁻¹ * V h0 (-1) z

private theorem g_zero : g h0 ⟨0, zero_mem_compl_range h0⟩ = 1 := by
  rw [g, V_zero h0 one_ne_zero, V_zero h0 (neg_ne_zero.2 one_ne_zero), inv_one, one_mul]

/-- `g` is constant along a path on the real axis. -/
private theorem g_eq_of_path (σ : Path z w) (hσ : ∀ t, (σ t : ℂ).im = 0) : g h0 z = g h0 w := by
  have h1 := ofPath_eq_V h0 one_ne_zero σ (by rintro _ ⟨t, rfl⟩; simp [half, hσ t])
  have h2 := ofPath_eq_V h0 (neg_ne_zero.2 one_ne_zero) σ (by rintro _ ⟨t, rfl⟩; simp [half, hσ t])
  rw [eq_mul_inv_iff_mul_eq] at h1 h2
  rw [g, g, ← h1, ← h2, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- `g` takes the same value at two real points with no point `c i` between them. -/
private theorem g_eq_of_forall_notMem {x y : ℝ} (hz : (z : ℂ) = x) (hw : (w : ℂ) = y)
    (h : ∀ i, c i ∉ uIcc x y) : g h0 z = g h0 w := by
  have hσ (t : unitInterval) : Path.segment (z : ℂ) w t = (((1 - t) * x + t * y : ℝ) : ℂ) := by
    rw [hz, hw, Path.segment_apply, AffineMap.lineMap_apply_module, Complex.real_smul,
      Complex.real_smul]
    push_cast
    ring
  refine g_eq_of_path h0 ((Path.segment (z : ℂ) w).codRestrict fun t ↦ ?_) fun t ↦ ?_
  · rintro ⟨i, hi⟩
    rw [hσ, ofReal_inj] at hi
    refine h i (hi ▸ segment_subset_uIcc x y
      ⟨1 - (t : ℝ), t, sub_nonneg.2 t.property.2, t.property.1, by ring, ?_⟩)
    simp only [smul_eq_mul]
  · rw [Path.codRestrict_coe, hσ, ofReal_im]

end Telescope

/-! ### The large circle as a product of the loops -/

section Product

/-- A path in `ℂ` whose end points lie in a closed half-plane lies in it if it is a segment. -/
private theorem range_segment_subset_halfPlane {ε : ℝ} {a b : ℂ} (ha : 0 ≤ ε * a.im)
    (hb : 0 ≤ ε * b.im) : range (Path.segment a b) ⊆ {z : ℂ | 0 ≤ ε * z.im} := by
  rw [Path.range_segment]
  exact (convex_halfPlane ε).segment_subset ha hb

/-- The part `[s₀, s₁]` of a path whose points there lie in a closed half-plane. -/
private theorem range_subpath_subset_half {ε : ℝ} {a b : ↥(range fun i ↦ (c i : ℂ))ᶜ}
    (γ : Path a b) {s₀ s₁ : unitInterval} (hs : s₀ ≤ s₁)
    (h : ∀ t : unitInterval, (s₀ : ℝ) ≤ t → (t : ℝ) ≤ s₁ → 0 ≤ ε * (γ t : ℂ).im) :
    range (γ.subpath s₀ s₁) ⊆ half c ε := by
  rw [Path.range_subpath_of_le _ _ _ hs, image_subset_iff]
  exact fun t ht ↦ h t ht.1 ht.2

/-- The real numbers `x` and `y` lie between the same two consecutive points `c i`. -/
private theorem notMem_uIcc_of_lt_of_lt {x y a b : ℝ} (hab : ∀ i, c i ≤ a ∨ b ≤ c i)
    (hx : a < x) (hx' : x < b) (hy : a < y) (hy' : y < b) (i : ι) : c i ∉ uIcc x y := by
  intro hi
  rw [mem_uIcc] at hi
  rcases hab i with h | h <;> rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

variable [Countable ι] (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (h0 : ∀ i, c i ≠ 0)

/-- The class of the loop about `c k` is `g` at the right end point of its circle, after the
inverse of `g` at the left end point. -/
private theorem exists_ofPath_loop_eq (k : ι) :
    ∃ z w : ↥(range fun i ↦ (c i : ℂ))ᶜ, (z : ℂ) = (c k - δ / 4 : ℝ) ∧
      (w : ℂ) = (c k + δ / 4 : ℝ) ∧ ofPath h0 (loop hδ hc h0 k) = (g h0 z)⁻¹ * g h0 w := by
  have hr : 0 < δ / 4 := by positivity
  let q : ↥(range fun i ↦ (c i : ℂ))ᶜ := ⟨-I, by simpa using segment_mem_compl_range h0 1⟩
  let p : ↥(range fun i ↦ (c i : ℂ))ᶜ := ⟨((c k + δ / 4 : ℝ) : ℂ), by
    simpa using spine_subset_compl_range (fan_diff_subset_spine hδ hc k
      (approach_mem_fan hδ k 1))⟩
  let sX : Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ) q :=
    (Path.segment (0 : ℂ) (-I)).codRestrict (segment_mem_compl_range h0)
  let αX : Path q p := (approach (c k) (δ / 4)).codRestrict fun t ↦
    spine_subset_compl_range (fan_diff_subset_spine hδ hc k (approach_mem_fan hδ k t))
  let CX : Path p p := (circle (c k) (δ / 4)).codRestrict fun t ↦
    spine_subset_compl_range (fan_diff_subset_spine hδ hc k (circle_mem_fan hδ k t))
  have hloop : loop hδ hc h0 k = sX.trans ((αX.trans (CX.trans αX.symm)).trans sX.symm) := by
    ext t
    simp only [coe_loop_apply, loopInPlane_def, Path.trans_apply, Path.symm_apply,
      apply_dite Subtype.val, Path.codRestrict_coe, Function.comp_apply, sX, αX, CX]
  let h : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hh : (h : ℝ) = 1 / 2 := rfl
  -- Cut the small circle where it meets the real axis, at `c k - r`, and compare its two halves,
  -- and the approach, with the paths `via` in the closed half-planes.
  have hC : ofPath h0 CX = ofPath h0 (CX.subpath h 1) * ofPath h0 (CX.subpath 0 h) := by
    rw [← ofPath_trans, ofPath_congr h0 (Path.Homotopic.subpath_trans_subpath CX 0 h 1),
      Path.subpath_zero_one, ofPath_cast]
  have hU := ofPath_eq_V h0 one_ne_zero (CX.subpath 0 h) (range_subpath_subset_half _
    (by rw [← Subtype.coe_le_coe, hh]; norm_num) fun t _ ht ↦ by
      rw [Path.codRestrict_coe, circle_apply]
      rw [hh] at ht
      simpa using im_le_circleMap_im (z₀ := (c k : ℂ)) hr.le
        ⟨mul_nonneg (by positivity) t.property.1, by nlinarith [Real.pi_pos]⟩)
  have hD := ofPath_eq_V h0 (neg_ne_zero.2 one_ne_zero) (CX.subpath h 1)
    (range_subpath_subset_half _ (by rw [← Subtype.coe_le_coe, hh]; norm_num) fun t ht _ ↦ by
      rw [Path.codRestrict_coe, circle_apply]
      rw [hh] at ht
      simpa using circleMap_im_le_im (z₀ := (c k : ℂ)) hr.le ⟨by nlinarith [Real.pi_pos],
        by nlinarith [Real.pi_pos, t.property.2]⟩)
  have hL := ofPath_eq_V h0 (neg_ne_zero.2 one_ne_zero) (sX.trans αX) (by
    rw [Path.trans_range]
    refine union_subset (range_codRestrict_subset_half _ (range_segment_subset_halfPlane
      (by simp) (by simp))) (range_codRestrict_subset_half _ ?_)
    rw [approach_def, Path.trans_range]
    exact union_subset (range_segment_subset_halfPlane (by simp) (by simp))
      (range_segment_subset_halfPlane (by simp) (by simp)))
  refine ⟨CX h, p, ?_, rfl, ?_⟩
  · rw [Path.codRestrict_coe, circle_apply, hh]
    simp only [circleMap, ofReal_sub, ofReal_div]
    rw [show (((2 * Real.pi * (1 / 2) : ℝ)) : ℂ) * I = Real.pi * I by push_cast; ring, exp_pi_mul_I]
    push_cast
    ring
  · rw [ofPath_trans, V_zero h0 (neg_ne_zero.2 one_ne_zero), inv_one, mul_one] at hL
    rw [show V h0 1 (CX 0) = V h0 1 p from congrArg _ CX.source] at hU
    rw [show V h0 (-1) (CX 1) = V h0 (-1) p from congrArg _ CX.target] at hD
    rw [hloop]
    simp only [ofPath_trans, ofPath_symm, hC, hU, hD]
    rw [eq_mul_inv_iff_mul_eq.2 hL]
    simp only [g]
    group

/-- The class of the large loop is `g` at `R` after the inverse of `g` at `-R`. -/
private theorem exists_ofPath_outerLoop_eq (hR : ∀ i, |c i| < R) (hR₀ : 0 < R) (hθ₀ : 0 < θ)
    (hθπ : θ < Real.pi) :
    ∃ z w : ↥(range fun i ↦ (c i : ℂ))ᶜ, (z : ℂ) = (-R : ℝ) ∧ (w : ℂ) = (R : ℝ) ∧
      ofPath h0 (outerLoop h0 hR hθ₀ hθπ) = g h0 w * (g h0 z)⁻¹ := by
  have := Real.pi_pos
  let B : ↥(range fun i ↦ (c i : ℂ))ᶜ := ⟨circleMap 0 R θ, circleMap_zero_mem_compl_range hR θ⟩
  let ρX : Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ) B :=
    (Path.segment 0 (circleMap 0 R θ)).codRestrict
      (segment_zero_circleMap_mem_compl_range h0 hθ₀ hθπ)
  let CX : Path B B := (circlePath 0 R θ).codRestrict fun t ↦
    circlePath_apply 0 R θ t ▸ circleMap_zero_mem_compl_range hR _
  have hloop : outerLoop h0 hR hθ₀ hθπ = ρX.trans (CX.trans ρX.symm) := by
    ext t
    simp only [coe_outerLoop_apply, outerLoopInPlane_def, Path.trans_apply, Path.symm_apply,
      apply_dite Subtype.val, Path.codRestrict_coe, Function.comp_apply, ρX, CX]
  -- The large circle meets the real axis at `-R`, at the time `t₁`, and at `R`, at `t₂`.
  let t₁ : unitInterval := ⟨(Real.pi - θ) / (2 * Real.pi),
    div_nonneg (by linarith) (by positivity), (div_le_one (by positivity)).2 (by linarith)⟩
  let t₂ : unitInterval := ⟨(2 * Real.pi - θ) / (2 * Real.pi),
    div_nonneg (by linarith) (by positivity), (div_le_one (by positivity)).2 (by linarith)⟩
  have ht₁ : (t₁ : ℝ) = (Real.pi - θ) / (2 * Real.pi) := rfl
  have ht₂ : (t₂ : ℝ) = (2 * Real.pi - θ) / (2 * Real.pi) := rfl
  -- The angle at a time `t` is at most, or at least, `a` when `t` is at most, or at least, the
  -- time of the angle `a`.
  have hle (t : unitInterval) (a : ℝ) (ht : (t : ℝ) ≤ (a - θ) / (2 * Real.pi)) :
      θ + 2 * Real.pi * t ≤ a := by
    rw [le_div_iff₀ (by positivity)] at ht
    linarith
  have hge (t : unitInterval) (a : ℝ) (ht : (a - θ) / (2 * Real.pi) ≤ t) :
      a ≤ θ + 2 * Real.pi * t := by
    rw [div_le_iff₀ (by positivity)] at ht
    linarith
  have hC : ofPath h0 CX = ofPath h0 (CX.subpath t₂ 1) *
      (ofPath h0 (CX.subpath t₁ t₂) * ofPath h0 (CX.subpath 0 t₁)) := by
    rw [← ofPath_trans, ← ofPath_trans, ofPath_congr h0
        ((Path.Homotopic.subpath_trans_subpath CX 0 t₁ t₂).hcomp (Path.Homotopic.refl _)),
      ofPath_congr h0 (Path.Homotopic.subpath_trans_subpath CX 0 t₂ 1),
      Path.subpath_zero_one, ofPath_cast]
  have h1 := ofPath_eq_V h0 one_ne_zero (CX.subpath 0 t₁) (range_subpath_subset_half _
    (by rw [← Subtype.coe_le_coe, ht₁]; exact t₁.property.1) fun t _ ht ↦ by
      rw [Path.codRestrict_coe, circlePath_apply]
      simpa using im_le_circleMap_im (z₀ := 0) hR₀.le ⟨by nlinarith [t.property.1],
        hle t _ (ht.trans_eq ht₁)⟩)
  have h2 := ofPath_eq_V h0 (neg_ne_zero.2 one_ne_zero) (CX.subpath t₁ t₂)
    (range_subpath_subset_half _ (by rw [← Subtype.coe_le_coe, ht₁, ht₂]; gcongr; linarith)
      fun t ht ht' ↦ by
      rw [Path.codRestrict_coe, circlePath_apply]
      simpa using circleMap_im_le_im (z₀ := 0) hR₀.le ⟨hge t _ (ht₁ ▸ ht),
        hle t _ (ht'.trans_eq ht₂)⟩)
  have h3 := ofPath_eq_V h0 one_ne_zero (CX.subpath t₂ 1) (range_subpath_subset_half _
    t₂.property.2 fun t ht _ ↦ by
      rw [Path.codRestrict_coe, circlePath_apply, ← (periodic_circleMap _ _).sub_eq]
      have := hge t _ (ht₂ ▸ ht)
      simpa using im_le_circleMap_im (z₀ := 0) hR₀.le
        ⟨by linarith, by nlinarith [t.property.2]⟩)
  have hρ := ofPath_eq_V h0 one_ne_zero ρX (range_codRestrict_subset_half _
    (range_segment_subset_halfPlane (by simp) (by
      simpa using im_le_circleMap_im (z₀ := 0) hR₀.le ⟨hθ₀.le, hθπ.le⟩)))
  rw [V_zero h0 one_ne_zero, inv_one, mul_one] at hρ
  rw [show V h0 1 (CX 0) = V h0 1 B from congrArg _ CX.source] at h1
  rw [show V h0 1 (CX 1) = V h0 1 B from congrArg _ CX.target] at h3
  have hangle (t : unitInterval) (a : ℝ) (h : (t : ℝ) = (a - θ) / (2 * Real.pi)) :
      θ + 2 * Real.pi * t = a :=
    le_antisymm (hle t a h.le) (hge t a h.ge)
  refine ⟨CX t₁, CX t₂, ?_, ?_, ?_⟩
  · rw [Path.codRestrict_coe, circlePath_apply, hangle t₁ Real.pi ht₁]
    simp [circleMap]
  · rw [Path.codRestrict_coe, circlePath_apply, hangle t₂ (2 * Real.pi) ht₂]
    simp [circleMap]
  · rw [hloop]
    simp only [ofPath_trans, ofPath_symm, hC, h1, h2, h3, hρ, g]
    group

/-- **The large circle is the product of the loops.** Let `c 0 < c 1 < ⋯ < c (m - 1)` be positive
reals, any two of them at distance at least `δ > 0`, all of them less than `R`, and let
`0 < θ < π`. In the plane minus these points, based at `0`, the loop `outerLoop` along the ray at
the angle `θ`, once counterclockwise around the circle of radius `R` about `0`, and back along
the ray, is homotopic to the loops `loop` about the points run one after the other,
from the largest point to the smallest. In `FundamentalGroup`, where `x * y` runs `y` first, its
class is the product of the classes of the loops in the order of `k`. -/
theorem fromPath_outerLoop_eq_prod {m : ℕ} {c : Fin m → ℝ} (hδ : 0 < δ)
    (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (hpos : ∀ i, 0 < c i) (hR : ∀ i, c i < R)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hmono : StrictMono c) :
    fromPath (Path.Homotopic.Quotient.mk (outerLoop (fun i ↦ (hpos i).ne')
        (fun i ↦ (abs_of_pos (hpos i)).trans_lt (hR i)) hθ₀ hθπ)) =
      (List.ofFn fun k ↦
        fromPath (Path.Homotopic.Quotient.mk (loop hδ hc (fun i ↦ (hpos i).ne') k))).prod := by
  have h0 : ∀ i, c i ≠ 0 := fun i ↦ (hpos i).ne'
  have hR' : ∀ i, |c i| < R := fun i ↦ (abs_of_pos (hpos i)).trans_lt (hR i)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hconv : Convex ℝ (range fun i ↦ (c i : ℂ))ᶜ := by
      rw [range_eq_empty, compl_empty]
      exact convex_univ
    have := hconv.contractibleSpace ⟨0, zero_mem_compl_range h0⟩
    exact Subsingleton.elim _ _
  have hR₀ : 0 < R := (hpos ⟨0, hm⟩).trans (hR ⟨0, hm⟩)
  -- Consecutive points are at distance at least `δ`.
  have hgap {i j : Fin m} (hij : i < j) : c i + δ ≤ c j := by
    have := hc hij.ne
    simp only at this
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 (hmono hij))] at this
    linarith
  -- Write the loops, and the large loop, through the values of `g` at real points.
  rw [← ofPath_loop h0]
  simp only [← ofPath_loop h0]
  choose z w hz hw hl using exists_ofPath_loop_eq hδ hc h0
  obtain ⟨z', w', hz', hw', hL⟩ := exists_ofPath_outerLoop_eq h0 hR' hR₀ hθ₀ hθπ
  -- The value `F j` of `g` between the points `c (j - 1)` and `c j`, `1` left of `c 0`. It is
  -- `g` at both end points of the circle about `c j`, and at `R`.
  let F : ℕ → FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩ :=
    fun j ↦ if j = 0 then 1 else if h' : j - 1 < m then g h0 (w ⟨j - 1, h'⟩) else 1
  have hF (k : Fin m) : g h0 (w k) = F (k + 1) := by
    simp only [F, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceIte, dite_eq_left k.isLt]
  have hFz (k : Fin m) : g h0 (z k) = F k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · have hFk : F k = 1 := by simp only [F, hk, ↓reduceIte]
      rw [hFk, ← g_zero h0]
      refine g_eq_of_forall_notMem h0 (y := 0) (hz k) (by simp) (notMem_uIcc_of_lt_of_lt
        (a := min (c k - δ / 4) 0 - 1) (b := c k) (fun i ↦ .inr (hmono.monotone
          (Fin.le_def.2 (by omega)))) ?_ (by linarith) ?_ (hpos k)) <;>
        linarith [min_le_left (c k - δ / 4) 0, min_le_right (c k - δ / 4) 0]
    · let j : Fin m := ⟨k - 1, by omega⟩
      have hjk : j < k := Fin.lt_def.2 (by simp only [j]; omega)
      have hFk : F k = g h0 (w j) := by
        simp only [F, hk.ne', ↓reduceIte, dite_eq_left (by omega : (k : ℕ) - 1 < m), j]
      rw [hFk]
      have := hgap hjk
      refine g_eq_of_forall_notMem h0 (hz k) (hw j) (notMem_uIcc_of_lt_of_lt (a := c j) (b := c k)
        (fun i ↦ ?_) (by linarith) (by linarith) (by linarith) (by linarith))
      rcases le_or_gt i j with h | h
      · exact .inl (hmono.monotone h)
      · refine .inr (hmono.monotone (Fin.le_def.2 ?_))
        rw [Fin.lt_def] at h
        simp only [j] at h
        omega
  have hFm : g h0 w' = F m := by
    let j : Fin m := ⟨m - 1, by omega⟩
    have hFm : F m = g h0 (w j) := by
      simp only [F, hm.ne', ↓reduceIte, dite_eq_left (by omega : m - 1 < m), j]
    rw [hFm]
    have := hR j
    refine g_eq_of_forall_notMem h0 hw' (hw j) (notMem_uIcc_of_lt_of_lt (a := c j)
      (b := max R (c j + δ / 4) + 1) (fun i ↦ .inl (hmono.monotone (Fin.le_def.2 (by
        simp only [j]; omega)))) this ?_ (by linarith) ?_) <;>
      linarith [le_max_left R (c j + δ / 4), le_max_right R (c j + δ / 4)]
  have hFz' : g h0 z' = 1 := by
    rw [← g_zero h0]
    have := hpos ⟨0, hm⟩
    refine g_eq_of_forall_notMem h0 (y := 0) hz' (by simp) (notMem_uIcc_of_lt_of_lt (a := -R - 1)
      (b := c ⟨0, hm⟩) (fun i ↦ .inr (hmono.monotone (Fin.le_def.2 (Nat.zero_le _)))) ?_ ?_ ?_ ?_)
      <;> linarith
  -- The product telescopes.
  rw [hL, hFz', inv_one, mul_one, hFm]
  simp only [hl, hFz, hF]
  have htel := List.prod_range_div' m fun k ↦ (F k)⁻¹
  rw [← List.map_coe_finRange_eq_range, List.map_map] at htel
  have hF0 : F 0 = 1 := ite_eq_left rfl
  rw [List.ofFn_eq_map]
  simpa only [Function.comp_def, div_inv_eq_mul, hF0, inv_one, one_mul] using htel.symm

end Product

end PlaneMinusRealPoints

end SymplecticGeometry
