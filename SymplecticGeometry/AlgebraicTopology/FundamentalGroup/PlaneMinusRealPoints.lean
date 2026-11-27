/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Topology.Homotopy.Path

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.GroupTheory.CoprodI
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# The plane minus finitely many real points: a free basis of loops

Let `c : ι → ℝ` be finitely many distinct nonzero reals. The fundamental group of `ℂ` with the
points `c i` removed, based at `0`, is free on the loops `PlaneMinusRealPoints.loop hc h0 k`:
each goes from `0` straight down into the lower half-plane and over to below `c k + r`, up to the
circle of a small radius `r` about `c k`, once counterclockwise around that circle, and back the
same way.

## Main definitions

* `SymplecticGeometry.PlaneMinusRealPoints.radius hc h0`: the common radius of the circles, a
  quarter of a separation of the points from each other and from `0`.
* `SymplecticGeometry.PlaneMinusRealPoints.loop hc h0 k`: the loop about `c k`, based at `0`.
* `SymplecticGeometry.PlaneMinusRealPoints.fundamentalGroupMulEquiv hc h0`: the isomorphism of
  `π₁(ℂ ∖ {c i}, 0)` with `FreeGroup ι`.

## Main results

* `SymplecticGeometry.PlaneMinusRealPoints.fundamentalGroupMulEquiv_loop`: the isomorphism sends
  the class of `loop hc h0 k` to `FreeGroup.of k`.

## Implementation notes

The cover and its two deformations are those of Tau Ceti's proof of
`TauCeti.nonempty_fundamentalGroup_compl_mulEquiv_freeGroup`
(`TauCeti/AlgebraicTopology/FundamentalGroup/PlaneMinusPoints.lean`), whose declarations there
are private: the definitions `lower`, `teeth`, `strip`, `comb`, `piece`, `model`, `pushDown`,
`ramp`, `piecePush`, `cover` and the lemmas about them are taken from that file with their
proofs, and the wide van Kampen theorem `TauCeti.vanKampenWideEquiv` is applied as there, now at
the base point `0`, which lies in the comb. What is new is the generator of each factor: the
loop about `c k` is carried, by base-point change along its approach path, to the counterclockwise
circle about `c k`, which `TauCeti.StarConvex.fundamentalGroupMulEquivInt_sphereLoop` sends to
`1 : ℤ`; the inclusion of the punctured model into the `k`-th member is a homotopy equivalence.

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

/-! ### The pieces of the cover, as subsets of `ℂ` -/

/-- The open lower half-plane. -/
private def lower : Set ℂ := {z | z.im < 0}

variable (c δ) in
/-- The teeth of the comb: the points whose real part is at distance more than `δ / 4` from
every `c i`. -/
private def teeth : Set ℂ := {z | ∀ i, δ / 4 < |z.re - c i|}

variable (c δ) in
/-- The vertical strip of half-width `δ / 2` about the real point `c k`. -/
private def strip (k : ι) : Set ℂ := {z | |z.re - c k| < δ / 2}

variable (c δ) in
/-- The common part of the cover: the lower half-plane together with the teeth. -/
private def comb : Set ℂ := lower ∪ teeth c δ

variable (c δ) in
/-- The `k`-th member of the cover: the comb together with the strip about `c k`, punctured
at `c k`. -/
private def piece (k : ι) : Set ℂ := comb c δ ∪ (strip c δ k \ {(c k : ℂ)})

variable (c δ) in
/-- The lower half-plane together with the strip about `c k`, a set star-convex about `c k`. -/
private def model (k : ι) : Set ℂ := lower ∪ strip c δ k

private theorem convex_lower : Convex ℝ lower := by
  unfold lower
  exact convex_halfSpace_im_lt 0

private theorem neg_I_mem_lower : -I ∈ lower := by
  simp [lower]

private theorem ofReal_notMem_lower (x : ℝ) : (x : ℂ) ∉ lower := by
  simp [lower]

private theorem ofReal_notMem_comb (hδ : 0 < δ) (k : ι) : (c k : ℂ) ∉ comb c δ := by
  rintro (h | h)
  · exact ofReal_notMem_lower _ h
  · have := h k
    simp only [ofReal_re, sub_self, abs_zero] at this
    linarith

private theorem mem_strip_self (hδ : 0 < δ) (k : ι) : (c k : ℂ) ∈ strip c δ k := by
  simp [strip, hδ]

private theorem neg_I_mem_comb : -I ∈ comb c δ :=
  .inl neg_I_mem_lower

private theorem neg_I_mem_compl_range : -I ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  simpa using congrArg Complex.im hi

private theorem comb_subset_piece (k : ι) : comb c δ ⊆ piece c δ k :=
  subset_union_left

private theorem model_diff_subset_piece (k : ι) :
    model c δ k \ {(c k : ℂ)} ⊆ piece c δ k := by
  rintro z ⟨hz | hz, hzk⟩
  · exact .inl (.inl hz)
  · exact .inr ⟨hz, hzk⟩

/-- A member of the cover avoids every puncture. -/
private theorem piece_subset_compl_range (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) : piece c δ k ⊆ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro z hz ⟨i, rfl⟩
  rcases hz with h | ⟨h, hk⟩
  · exact ofReal_notMem_comb hδ i h
  · rcases eq_or_ne i k with rfl | hik
    · exact hk rfl
    · have h' : |c i - c k| < δ / 2 := by simpa [strip] using h
      linarith [hc hik]

private theorem comb_subset_compl_range (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    [Nonempty ι] : comb c δ ⊆ (range fun i ↦ (c i : ℂ))ᶜ :=
  (comb_subset_piece (Classical.arbitrary ι)).trans
    (piece_subset_compl_range hδ hc (Classical.arbitrary ι))

/-- Two distinct members of the cover meet inside the comb, as their strips are disjoint. -/
private theorem piece_inter_piece_subset (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) {i j : ι}
    (hij : i ≠ j) : piece c δ i ∩ piece c δ j ⊆ comb c δ := by
  rintro z ⟨hi | ⟨hi, -⟩, hj | ⟨hj, -⟩⟩
  · exact hi
  · exact hi
  · exact hj
  · simp only [strip, mem_ofPred_eq] at hi hj
    have := abs_sub_le (c i) z.re (c j)
    rw [abs_sub_comm] at hi
    linarith [hc hij]

/-- The union of the lower half-plane and the strip about `c k` is star-convex about `c k`. -/
private theorem starConvex_model (hδ : 0 < δ) (k : ι) : StarConvex ℝ (c k : ℂ) (model c δ k) := by
  intro z hz a b ha hb hab
  rcases hz with hz | hz
  · rcases hb.eq_or_lt with rfl | hb
    · rw [add_zero] at hab
      subst hab
      rw [one_smul, zero_smul, add_zero]
      exact .inr (mem_strip_self hδ k)
    · refine .inl ?_
      simp only [lower, mem_ofPred_eq, add_im, smul_im, ofReal_im, smul_eq_mul, mul_zero,
        zero_add] at hz ⊢
      exact mul_neg_of_pos_of_neg hb hz
  · refine .inr ?_
    simp only [strip, mem_ofPred_eq, add_re, smul_re, ofReal_re, smul_eq_mul] at hz ⊢
    have h : a * c k + b * z.re - c k = b * (z.re - c k) := by
      linear_combination c k * hab
    rw [h, abs_mul, abs_of_nonneg hb]
    nlinarith [abs_nonneg (z.re - c k)]

private theorem sphere_subset_model (hδ : 0 < δ) (k : ι) :
    sphere (c k : ℂ) (δ / 4) ⊆ model c δ k := by
  intro z hz
  refine .inr ?_
  have h := abs_re_le_norm (z - c k)
  rw [mem_sphere_iff_norm] at hz
  simp only [strip, mem_ofPred_eq]
  simp only [sub_re, ofReal_re] at h
  linarith

/-! ### Pushing points down -/

/-- Push `z` down by `s * (max z.im 0 + 1)`, keeping its real part. For `s = 1` the result lies in
the lower half-plane. -/
private def pushDown (s : ℝ) (z : ℂ) : ℂ := z - ((s * (max z.im 0 + 1) : ℝ) : ℂ) * I

@[simp]
private theorem pushDown_re (s : ℝ) (z : ℂ) : (pushDown s z).re = z.re := by
  simp [pushDown]

@[simp]
private theorem pushDown_im (s : ℝ) (z : ℂ) :
    (pushDown s z).im = z.im - s * (max z.im 0 + 1) := by
  simp [pushDown]

@[simp]
private theorem pushDown_zero (z : ℂ) : pushDown 0 z = z := by
  simp [pushDown]

@[fun_prop]
private theorem continuous_pushDown {X : Type*} [TopologicalSpace X] {s : X → ℝ} {z : X → ℂ}
    (hs : Continuous s) (hz : Continuous z) : Continuous fun x ↦ pushDown (s x) (z x) := by
  unfold pushDown
  fun_prop

private theorem pushDown_im_le {s : ℝ} (hs : 0 ≤ s) (z : ℂ) : (pushDown s z).im ≤ z.im := by
  rw [pushDown_im]
  nlinarith [le_max_right z.im 0]

private theorem pushDown_one_mem_lower (z : ℂ) : pushDown 1 z ∈ lower := by
  simp only [lower, mem_ofPred_eq, pushDown_im, one_mul]
  linarith [le_max_left z.im 0]

private theorem pushDown_mem_lower {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ lower) :
    pushDown s z ∈ lower :=
  lt_of_le_of_lt (pushDown_im_le hs z) hz

private theorem pushDown_mem_comb {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ comb c δ) :
    pushDown s z ∈ comb c δ := by
  rcases hz with hz | hz
  · exact .inl (pushDown_mem_lower hs hz)
  · exact .inr (by simpa [teeth] using hz)

/-- The weight of the push in the `k`-th member: `0` within `δ / 4` of `0`, `1` from `δ / 2` on. -/
private def ramp (δ x : ℝ) : ℝ := min 1 (max 0 (4 * |x| / δ - 1))

private theorem ramp_nonneg (δ x : ℝ) : 0 ≤ ramp δ x :=
  le_min zero_le_one (le_max_left _ _)

private theorem ramp_zero (δ : ℝ) : ramp δ 0 = 0 := by
  simp [ramp]

private theorem ramp_eq_one (hδ : 0 < δ) {x : ℝ} (hx : δ / 2 ≤ |x|) : ramp δ x = 1 := by
  refine min_eq_left (le_max_of_le_right ?_)
  rw [le_sub_iff_add_le, le_div_iff₀ hδ]
  linarith

@[fun_prop]
private theorem continuous_ramp (δ : ℝ) : Continuous (ramp δ) := by
  unfold ramp
  fun_prop

/-- The push in the `k`-th member never reaches the puncture `c k`: it moves only points whose real
part differs from `c k`. -/
private theorem pushDown_ramp_ne {k : ι} {t : ℝ} {z : ℂ} (hz : z ≠ c k) :
    pushDown (t * ramp δ (z.re - c k)) z ≠ c k := by
  intro h
  have hre : z.re = c k := by simpa using congrArg Complex.re h
  rw [hre, sub_self, ramp_zero, mul_zero, pushDown_zero] at h
  exact hz h

/-! ### The two deformations -/

/-- The comb deformation retracts, in the weak sense, onto the lower half-plane. -/
private def lowerHomotopyEquivComb : lower ≃ₕ comb c δ :=
  .ofWeakDeformationRetraction subset_union_left (fun p ↦ pushDown p.1 p.2)
    (by fun_prop)
    (fun p ↦ pushDown_mem_comb p.1.property.1 p.2.property)
    (fun _ ↦ pushDown_zero _)
    (fun _ ↦ pushDown_one_mem_lower _)
    (fun t _ hz ↦ pushDown_mem_lower t.property.1 hz)

/-- The comb is contractible. -/
private theorem contractibleSpace_comb : ContractibleSpace (comb c δ) :=
  haveI : ContractibleSpace lower := convex_lower.contractibleSpace ⟨-I, neg_I_mem_lower⟩
  lowerHomotopyEquivComb.symm.contractibleSpace

/-- The time-`t` push of a point of the `k`-th member. -/
private def piecePush (k : ι) (p : unitInterval × ℂ) : ℂ :=
  pushDown ((p.1 : ℝ) * ramp δ (p.2.re - c k)) p.2

private theorem continuous_piecePush (k : ι) : Continuous (piecePush (c := c) (δ := δ) k) := by
  unfold piecePush
  fun_prop

private theorem piecePush_mem_piece (k : ι) (t : unitInterval) {z : ℂ}
    (hz : z ∈ piece c δ k) : piecePush (c := c) (δ := δ) k (t, z) ∈ piece c δ k := by
  have hs : 0 ≤ (t : ℝ) * ramp δ (z.re - c k) := mul_nonneg t.property.1 (ramp_nonneg _ _)
  rcases hz with hz | ⟨hz, hzk⟩
  · exact .inl (pushDown_mem_comb hs hz)
  · exact .inr ⟨by simpa [strip, piecePush] using hz, pushDown_ramp_ne hzk⟩

private theorem piecePush_mem_model (k : ι) (t : unitInterval) {z : ℂ}
    (hz : z ∈ model c δ k \ {(c k : ℂ)}) :
    piecePush (c := c) (δ := δ) k (t, z) ∈ model c δ k \ {(c k : ℂ)} := by
  have hs : 0 ≤ (t : ℝ) * ramp δ (z.re - c k) := mul_nonneg t.property.1 (ramp_nonneg _ _)
  refine ⟨?_, pushDown_ramp_ne hz.2⟩
  rcases hz.1 with h | h
  · exact .inl (pushDown_mem_lower hs h)
  · exact .inr (by simpa [strip, piecePush] using h)

private theorem piecePush_one_mem_model (hδ : 0 < δ) (k : ι) {z : ℂ} (hz : z ∈ piece c δ k) :
    piecePush (c := c) (δ := δ) k (1, z) ∈ model c δ k \ {(c k : ℂ)} := by
  have hzk : z ≠ c k := by
    rintro rfl
    rcases hz with h | ⟨-, h⟩
    · exact ofReal_notMem_comb hδ k h
    · exact h rfl
  refine ⟨?_, pushDown_ramp_ne hzk⟩
  by_cases h : |z.re - c k| < δ / 2
  · exact .inr (by simpa [strip, piecePush] using h)
  · rw [piecePush, ramp_eq_one hδ (not_lt.1 h), Icc.coe_one, one_mul]
    exact .inl (pushDown_one_mem_lower z)

/-- The `k`-th member deformation retracts, in the weak sense, onto the union of the lower
half-plane and the strip about `c k`, punctured at `c k`. -/
private def modelHomotopyEquivPiece (hδ : 0 < δ) (k : ι) :
    ↥(model c δ k \ {(c k : ℂ)}) ≃ₕ piece c δ k :=
  .ofWeakDeformationRetraction (model_diff_subset_piece k) (fun p ↦ piecePush k (p.1, p.2))
    ((continuous_piecePush k).comp (by fun_prop))
    (fun p ↦ piecePush_mem_piece k p.1 p.2.property)
    (fun _ ↦ by simp [piecePush])
    (fun z ↦ piecePush_one_mem_model hδ k z.property)
    (fun t _ hz ↦ piecePush_mem_model k t hz)

/-! ### The cover of the punctured plane -/

/-- Every point of the punctured plane has a member of the cover as a neighbourhood. -/
private theorem exists_piece_mem_nhds [Nonempty ι] (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ (range fun i ↦ (c i : ℂ))ᶜ) : ∃ k, piece c δ k ∈ 𝓝 z := by
  by_cases h : ∃ k, |z.re - c k| < δ / 2
  · obtain ⟨k, hk⟩ := h
    have hopen : IsOpen (strip c δ k \ {(c k : ℂ)}) :=
      (isOpen_lt (by fun_prop) continuous_const).sdiff isClosed_singleton
    exact ⟨k, Filter.mem_of_superset (hopen.mem_nhds ⟨hk, fun h ↦ hz ⟨k, h.symm⟩⟩)
      subset_union_right⟩
  · simp only [not_exists, not_lt] at h
    refine ⟨Classical.arbitrary ι, Filter.mem_of_superset
      (ball_mem_nhds z (by positivity : 0 < δ / 4)) fun w hw ↦ .inl (.inr fun i ↦ ?_)⟩
    have hw' := abs_re_le_norm (w - z)
    rw [mem_ball_iff_norm] at hw
    simp only [sub_re] at hw'
    have := abs_sub_abs_le_abs_sub (z.re - c i) (w.re - c i)
    rw [show z.re - c i - (w.re - c i) = -(w.re - z.re) by ring, abs_neg] at this
    linarith [h i]

variable (c δ) in
/-- The `k`-th member of the cover, as a subset of the punctured plane. -/
private def cover (k : ι) : Set ↥(range fun i ↦ (c i : ℂ))ᶜ := Subtype.val ⁻¹' piece c δ k

/-- A member of the cover, as a subset of the punctured plane, is homeomorphic to the
corresponding subset of `ℂ`. -/
private def coverHomeomorph (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (k : ι) :
    cover c δ k ≃ₜ piece c δ k :=
  Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (by rw [Subtype.range_coe]; exact piece_subset_compl_range hδ hc k)

private theorem coe_coverHomeomorph_apply (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) (z : cover c δ k) : (coverHomeomorph hδ hc k z : ℂ) = (z : ℂ) :=
  Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe _ _ _

private theorem isPathConnected_cover (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) : IsPathConnected (cover c δ k) := by
  have := (starConvex_model (c := c) hδ k).pathConnectedSpace_diff_singleton
    (by simp [Complex.rank_real_complex]) (by positivity) (sphere_subset_model hδ k)
  have := (modelHomotopyEquivPiece (c := c) hδ k).pathConnectedSpace
  exact (isPathConnected_iff_pathConnectedSpace.2 ‹_›).preimage_coe
    (piece_subset_compl_range hδ hc k)

/-- Each member of the cover has infinite cyclic fundamental group. -/
private theorem nonempty_fundamentalGroup_cover_mulEquiv_int (hδ : 0 < δ)
    (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (k : ι) (z : cover c δ k) :
    Nonempty (FundamentalGroup (cover c δ k) z ≃* Multiplicative ℤ) := by
  have := isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_cover hδ hc k)
  have hV := starConvex_model (c := c) hδ k
  have hr : (0 : ℝ) < δ / 4 := by positivity
  let x : sphere (c k : ℂ) (δ / 4) := ⟨c k + (δ / 4 : ℝ), by simp [hδ.le]⟩
  obtain ⟨e⟩ := ((coverHomeomorph hδ hc k).toHomotopyEquiv.trans
    (modelHomotopyEquivPiece hδ k).symm).nonempty_fundamentalGroupMulEquiv z
      (hV.sphereHomotopyEquiv hr (sphere_subset_model hδ k) x)
  exact ⟨e.trans (hV.fundamentalGroupMulEquivInt hr (sphere_subset_model hδ k) x)⟩

/-- The punctured plane is path connected when there is at least one puncture. -/
private theorem pathConnectedSpace_compl_range [Nonempty ι] (hδ : 0 < δ)
    (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) :
    PathConnectedSpace ↥(range fun i ↦ (c i : ℂ))ᶜ := by
  let b : ↥(range fun i ↦ (c i : ℂ))ᶜ := ⟨-I, neg_I_mem_compl_range⟩
  have hb (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) : Joined z b := by
    obtain ⟨k, hk⟩ := exists_piece_mem_nhds hδ z.property
    exact ((isPathConnected_cover hδ hc k).joinedIn z (mem_preimage.2 (mem_of_mem_nhds hk)) b
      (comb_subset_piece k neg_I_mem_comb)).joined
  exact ⟨⟨b⟩, fun z w ↦ (hb z).trans (hb w).symm⟩


/-! ### Changing the base point of a generator -/

/-- An isomorphism of `π₁(P, y)` with a group, moved to an equal base point `y'` along loops with
the same points. -/
private theorem exists_mulEquiv_of_eq {P G : Type*} [TopologicalSpace P] [Group G] {y y' : P}
    (h : y = y') (σ : Path y y) (σ' : Path y' y') (hσ : ∀ t, σ t = σ' t)
    (e : FundamentalGroup P y ≃* G) :
    ∃ e' : FundamentalGroup P y' ≃* G,
      e' (fromPath (Path.Homotopic.Quotient.mk σ')) =
        e (fromPath (Path.Homotopic.Quotient.mk σ)) := by
  subst h
  obtain rfl : σ = σ' := Path.ext (funext hσ)
  exact ⟨e, rfl⟩

/-- An isomorphism of `π₁(P, y)` with a group, moved to the base point `a` along a path `ρ` from
`a` to `y`: the loop `ρ · σ · ρ⁻¹` at `a` takes the value of `σ`. -/
private theorem exists_mulEquiv_trans_trans_symm {P G : Type*} [TopologicalSpace P] [Group G]
    {a y : P} (ρ : Path a y) (σ : Path y y) (e : FundamentalGroup P y ≃* G) :
    ∃ e' : FundamentalGroup P a ≃* G,
      e' (fromPath (Path.Homotopic.Quotient.mk (ρ.trans (σ.trans ρ.symm)))) =
        e (fromPath (Path.Homotopic.Quotient.mk σ)) := by
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath ρ).trans e, ?_⟩
  have : fromPath (Path.Homotopic.Quotient.mk (ρ.trans (σ.trans ρ.symm))) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath ρ).symm
        (fromPath (Path.Homotopic.Quotient.mk σ)) := by
    rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply]
    rfl
  rw [this, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-! ### The separation of the points -/

private theorem exists_sep_of_finite [Finite ι] (hc : Function.Injective c) (h0 : ∀ i, c i ≠ 0) :
    ∃ δ, 0 < δ ∧ (Pairwise fun i j ↦ δ ≤ |c i - c j|) ∧ ∀ i, δ < |c i| := by
  have := Fintype.ofFinite ι
  obtain ⟨r, hr, -, hrc⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
    (T := insert 0 (Finset.univ.image c)) (U := fun _ ↦ univ) fun _ _ ↦ Filter.univ_mem
  have hmem (i : ι) : c i ∈ insert 0 (Finset.univ.image c) :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem c (Finset.mem_univ i))
  refine ⟨2 * r, by positivity, fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · simpa only [Real.dist_eq] using (hrc _ (hmem i) _ (hmem j) (hc.ne hij)).le
  · simpa only [Real.dist_eq, sub_zero] using
      hrc _ (hmem i) _ (Finset.mem_insert_self 0 _) (h0 i)

/-- A separation of finitely many distinct nonzero reals `c i`: a positive number at most the
distance between any two of them and less than the absolute value of each. -/
def sep [Finite ι] (hc : Function.Injective c) (h0 : ∀ i, c i ≠ 0) : ℝ :=
  (exists_sep_of_finite hc h0).choose

section Sep

variable [Finite ι] (hc : Function.Injective c) (h0 : ∀ i, c i ≠ 0)

theorem sep_pos : 0 < sep hc h0 :=
  (exists_sep_of_finite hc h0).choose_spec.1

theorem sep_le_abs_sub : Pairwise fun i j ↦ sep hc h0 ≤ |c i - c j| :=
  (exists_sep_of_finite hc h0).choose_spec.2.1

theorem sep_lt_abs (i : ι) : sep hc h0 < |c i| :=
  (exists_sep_of_finite hc h0).choose_spec.2.2 i

end Sep

/-! ### The loops -/

theorem zero_mem_compl_range (h0 : ∀ i, c i ≠ 0) : (0 : ℂ) ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  exact h0 i (by simpa using hi)

/-- The approach path to the circle about `x` of radius `r`: straight from `0` to `x + r - i`,
then straight up to `x + r`. -/
def approach (x r : ℝ) : Path (0 : ℂ) ((x + r : ℝ) : ℂ) :=
  (Path.segment (0 : ℂ) ((x + r : ℝ) - I)).trans (Path.segment ((x + r : ℝ) - I) ((x + r : ℝ) : ℂ))

/-- The circle about `x` of radius `r`, run once counterclockwise from `x + r`. -/
def circle (x r : ℝ) : Path ((x + r : ℝ) : ℂ) ((x + r : ℝ) : ℂ) where
  toFun t := x + r * exp ((2 * Real.pi * t : ℝ) * I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [exp_mul_I]

theorem circle_apply (x r : ℝ) (t : unitInterval) :
    circle x r t = circleMap x r (2 * Real.pi * t) := by
  simp [circle, circleMap]

/-- The loop about `x` of radius `r` in `ℂ`, based at `0`: the approach path, the circle, and the
approach path back. -/
def loopAux (x r : ℝ) : Path (0 : ℂ) 0 :=
  (approach x r).trans ((circle x r).trans (approach x r).symm)

theorem loopAux_def (x r : ℝ) :
    loopAux x r = (approach x r).trans ((circle x r).trans (approach x r).symm) :=
  (rfl)

private theorem mem_piece_of_abs_lt (k : ι) {z : ℂ} (h : |z.re - c k| < δ / 2) (hz : z ≠ c k) :
    z ∈ piece c δ k :=
  .inr ⟨h, hz⟩

private theorem circle_mem_piece (hδ : 0 < δ) (k : ι) (t : unitInterval) :
    circle (c k) (δ / 4) t ∈ piece c δ k := by
  have hn : ‖circle (c k) (δ / 4) t - c k‖ = δ / 4 := by
    rw [circle_apply, circleMap_sub_center, norm_circleMap_zero, abs_of_pos (by positivity)]
  refine mem_piece_of_abs_lt k ?_ fun h ↦ ?_
  · have := abs_re_le_norm (circle (c k) (δ / 4) t - c k)
    simp only [sub_re, ofReal_re] at this
    linarith
  · rw [h, sub_self, norm_zero] at hn
    linarith

private theorem approach_mem_piece (hδ : 0 < δ) (hcδ : ∀ i, δ < |c i|) (k : ι)
    (t : unitInterval) : approach (c k) (δ / 4) t ∈ piece c δ k := by
  have h : range (approach (c k) (δ / 4)) ⊆ piece c δ k := by
    rw [approach, Path.trans_range, union_subset_iff, range_subset_iff, range_subset_iff]
    constructor
    · intro t
      have hre : (Path.segment (0 : ℂ) ((c k + δ / 4 : ℝ) - I) t).re = t * (c k + δ / 4) := by
        simp [AffineMap.lineMap_apply_module']
      have him : (Path.segment (0 : ℂ) ((c k + δ / 4 : ℝ) - I) t).im = -t := by
        simp [AffineMap.lineMap_apply_module']
      rcases t.property.1.eq_or_lt with ht | ht
      · refine .inl (.inr fun i ↦ ?_)
        rw [hre, ← ht, zero_mul, zero_sub, abs_neg]
        linarith [hcδ i]
      · exact .inl (.inl (by change _ < (0 : ℝ); rw [him]; linarith))
    · intro t
      have hre : (Path.segment ((c k + δ / 4 : ℝ) - I) ((c k + δ / 4 : ℝ) : ℂ) t).re =
          c k + δ / 4 := by
        simp [AffineMap.lineMap_apply_module']
      refine mem_piece_of_abs_lt k ?_ fun h ↦ ?_
      · rw [hre, add_sub_cancel_left, abs_of_pos (by positivity)]
        linarith
      · have := congrArg Complex.re h
        rw [hre, ofReal_re] at this
        linarith
  exact h (mem_range_self t)

/-- The loop about `c k` of radius `δ / 4` stays in the `k`-th member of the cover. -/
private theorem loopAux_mem_piece (hδ : 0 < δ) (hcδ : ∀ i, δ < |c i|) (k : ι)
    (t : unitInterval) : loopAux (c k) (δ / 4) t ∈ piece c δ k := by
  have h : range (loopAux (c k) (δ / 4)) ⊆ piece c δ k := by
    rw [loopAux_def, Path.trans_range, Path.trans_range, Path.symm_range, union_subset_iff,
      union_subset_iff, range_subset_iff, range_subset_iff]
    exact ⟨approach_mem_piece hδ hcδ k, circle_mem_piece hδ k, approach_mem_piece hδ hcδ k⟩
  exact h (mem_range_self t)

/-! ### The generator of each member of the cover -/

private theorem zero_mem_piece (hδ : 0 < δ) (hcδ : ∀ i, δ < |c i|) (k : ι) :
    (0 : ℂ) ∈ piece c δ k := by
  simpa [loopAux] using loopAux_mem_piece hδ hcδ k 0

/-- In the `k`-th member of the cover, as a subset of `ℂ`, some isomorphism of the fundamental
group at `0` with `ℤ` sends the loop about `c k` of radius `δ / 4` to `1`. -/
private theorem exists_mulEquiv_piece (hδ : 0 < δ) (hcδ : ∀ i, δ < |c i|) (k : ι) :
    ∃ e : FundamentalGroup (piece c δ k) ⟨0, zero_mem_piece hδ hcδ k⟩ ≃* Multiplicative ℤ,
      e (fromPath (Path.Homotopic.Quotient.mk ((loopAux (c k) (δ / 4)).codRestrict
        (x := ⟨0, zero_mem_piece hδ hcδ k⟩) (y := ⟨0, zero_mem_piece hδ hcδ k⟩)
        (loopAux_mem_piece hδ hcδ k)))) = Multiplicative.ofAdd 1 := by
  have hV := starConvex_model (c := c) hδ k
  have hr : (0 : ℝ) < δ / 4 := by positivity
  have hS := sphere_subset_model (c := c) hδ k
  let S := hV.sphereHomotopyEquiv hr hS
  let x0 : sphere (c k : ℂ) (δ / 4) := (TauCeti.sphereCircleHomeomorph _ hr).symm 1
  let E := modelHomotopyEquivPiece (c := c) hδ k
  let e1 : FundamentalGroup (piece c δ k) (E.toFun (S x0)) ≃* Multiplicative ℤ :=
    (MulEquiv.ofBijective _ (E.fundamentalGroup_map_bijective (S x0))).symm.trans
      (hV.fundamentalGroupMulEquivInt hr hS x0)
  have he1 : e1 (fromPath (Path.Homotopic.Quotient.mk (((Complex.sphereLoop (c k : ℂ) hr).map
      S.toFun.continuous).map E.toFun.continuous))) = Multiplicative.ofAdd 1 := by
    have hm : fromPath (Path.Homotopic.Quotient.mk (((Complex.sphereLoop (c k : ℂ) hr).map
        S.toFun.continuous).map E.toFun.continuous)) = FundamentalGroup.map E.toFun _
          (FundamentalGroup.map S.toFun x0
            (fromPath (Path.Homotopic.Quotient.mk (Complex.sphereLoop (c k : ℂ) hr)))) := by
      rfl
    have := (MulEquiv.ofBijective _ (E.fundamentalGroup_map_bijective (S x0))).symm_apply_apply
      (FundamentalGroup.map S.toFun x0
        (fromPath (Path.Homotopic.Quotient.mk (Complex.sphereLoop (c k : ℂ) hr))))
    rw [MulEquiv.ofBijective_apply] at this
    rw [hm, MulEquiv.trans_apply, this]
    exact hV.fundamentalGroupMulEquivInt_sphereLoop hr hS
  have hy : ((c k + δ / 4 : ℝ) : ℂ) ∈ piece c δ k := by
    simpa using circle_mem_piece hδ k 0
  let y : piece c δ k := ⟨_, hy⟩
  let σP : Path y y := (circle (c k) (δ / 4)).codRestrict (x := y) (y := y) (circle_mem_piece hδ k)
  obtain ⟨e2, he2⟩ := exists_mulEquiv_of_eq (y' := y)
    (σ := ((Complex.sphereLoop (c k : ℂ) hr).map S.toFun.continuous).map E.toFun.continuous)
    (Subtype.ext (by simp [E, S, y, modelHomotopyEquivPiece])) σP
    (fun t ↦ Subtype.ext (by
      rw [Path.codRestrict_coe, circle_apply, ← Complex.coe_sphereLoop_apply (c k : ℂ) hr t]
      simp only [Path.map_coe, Function.comp_apply]
      simp [E, S, modelHomotopyEquivPiece])) e1
  let ρP : Path (⟨0, zero_mem_piece hδ hcδ k⟩ : piece c δ k) y :=
    (approach (c k) (δ / 4)).codRestrict (approach_mem_piece hδ hcδ k)
  obtain ⟨e3, he3⟩ := exists_mulEquiv_trans_trans_symm ρP σP e2
  refine ⟨e3, ?_⟩
  have h : (ρP.trans (σP.trans ρP.symm)).map continuous_subtypeVal = loopAux (c k) (δ / 4) := by
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
    simp only [ρP, σP, Path.map_codRestrict]
    rfl
  have hL : (loopAux (c k) (δ / 4)).codRestrict (x := ⟨0, zero_mem_piece hδ hcδ k⟩)
      (y := ⟨0, zero_mem_piece hδ hcδ k⟩) (loopAux_mem_piece hδ hcδ k) =
      ρP.trans (σP.trans ρP.symm) := by
    ext t
    have := congrArg (fun γ : Path (0 : ℂ) 0 ↦ γ t) h
    simp only [Path.map_coe, Function.comp_apply] at this
    rw [Path.codRestrict_coe]
    exact this.symm
  rw [hL, he3, he2, he1]

/-! ### The loops in the plane minus the points -/

section Main

variable [Finite ι] (hc : Function.Injective c) (h0 : ∀ i, c i ≠ 0)

theorem loopAux_mem_compl_range (k : ι) (t : unitInterval) :
    loopAux (c k) (sep hc h0 / 4) t ∈ (range fun i ↦ (c i : ℂ))ᶜ :=
  piece_subset_compl_range (sep_pos hc h0) (sep_le_abs_sub hc h0) k
    (loopAux_mem_piece (sep_pos hc h0) (sep_lt_abs hc h0) k t)

/-- The loop about `c k`, based at `0`, in the plane minus the points `c i`: from `0` straight
to `c k + r - i` and straight up to `c k + r`, once counterclockwise around the circle of
radius `r` about `c k`, and back the same way, for the radius `r = sep hc h0 / 4`. -/
def loop (k : ι) :
    Path (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ)
      ⟨0, zero_mem_compl_range h0⟩ :=
  (loopAux (c k) (sep hc h0 / 4)).codRestrict (loopAux_mem_compl_range hc h0 k)

@[simp]
theorem coe_loop_apply (k : ι) (t : unitInterval) :
    (loop hc h0 k t : ℂ) = loopAux (c k) (sep hc h0 / 4) t :=
  Path.codRestrict_coe _ _ t

private theorem zero_mem_comb : (0 : ℂ) ∈ comb c (sep hc h0) :=
  .inr fun i ↦ by
    rw [zero_re, zero_sub, abs_neg]
    linarith [sep_lt_abs hc h0 i, sep_pos hc h0]

private theorem zero_mem_cover (k : ι) :
    (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ) ∈ cover c (sep hc h0) k :=
  comb_subset_piece (c := c) k (zero_mem_comb hc h0)

private theorem loop_mem_cover (k : ι) (t : unitInterval) :
    loop hc h0 k t ∈ cover c (sep hc h0) k := by
  change (loop hc h0 k t : ℂ) ∈ piece c (sep hc h0) k
  rw [coe_loop_apply]
  exact loopAux_mem_piece (sep_pos hc h0) (sep_lt_abs hc h0) k t

/-- In the `k`-th member of the cover, some isomorphism of the fundamental group at `0` with `ℤ`
sends the loop about `c k` to `1`. -/
private theorem exists_mulEquiv_cover (k : ι) :
    ∃ e : FundamentalGroup (cover c (sep hc h0) k)
        ⟨⟨0, zero_mem_compl_range h0⟩, zero_mem_cover hc h0 k⟩ ≃*
        Multiplicative ℤ,
      e (fromPath (Path.Homotopic.Quotient.mk
        ((loop hc h0 k).codRestrict (loop_mem_cover hc h0 k)))) =
        Multiplicative.ofAdd 1 := by
  have hδ := sep_pos hc h0
  obtain ⟨e, he⟩ := exists_mulEquiv_piece hδ (sep_lt_abs hc h0) k
  refine ⟨(FundamentalGroup.homeomorphMulEquivOfEq
    (coverHomeomorph hδ (sep_le_abs_sub hc h0) k)
    (y := ⟨0, zero_mem_piece hδ (sep_lt_abs hc h0) k⟩) (Subtype.ext
      (coe_coverHomeomorph_apply _ _ _ _))).trans e,
    ?_⟩
  rw [MulEquiv.trans_apply, FundamentalGroup.homeomorphMulEquivOfEq_apply,
    FundamentalGroup.mapOfEq_fromPath_mk, ← he]
  congr 3
  ext t
  simp [Path.map_coe, coe_coverHomeomorph_apply]

/-- The free group on `ι` is identified with the fundamental group of the plane minus the points
`c i` at `0`, sending each generator to the class of its loop. -/
private theorem exists_mulEquiv_freeGroup :
    ∃ ψ : FreeGroup ι ≃* FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ
        ⟨0, zero_mem_compl_range h0⟩,
      ∀ k, ψ (FreeGroup.of k) = fromPath (Path.Homotopic.Quotient.mk (loop hc h0 k)) := by
  have hδ := sep_pos hc h0
  have hcδ := sep_le_abs_sub hc h0
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hconv : Convex ℝ (range fun i ↦ (c i : ℂ))ᶜ := by
      rw [range_eq_empty, compl_empty]
      exact convex_univ
    have := hconv.contractibleSpace ⟨0, zero_mem_compl_range h0⟩
    have : Unique (FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩) :=
      uniqueOfSubsingleton 1
    exact ⟨MulEquiv.ofUnique, isEmptyElim⟩
  let C : Set ↥(range fun i ↦ (c i : ℂ))ᶜ := Subtype.val ⁻¹' comb c (sep hc h0)
  have hC : IsSimplyConnected C :=
    have := contractibleSpace_comb (c := c) (δ := sep hc h0)
    have : ContractibleSpace C := (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by rw [Subtype.range_coe]; exact comb_subset_compl_range hδ hcδ)).contractibleSpace
    SimplyConnectedSpace.ofContractible C
  have hx : (⟨0, zero_mem_compl_range h0⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ) ∈ C :=
    zero_mem_comb hc h0
  let vK := TauCeti.vanKampenWideEquiv (U := cover c (sep hc h0)) (C := C)
    (fun y ↦ (exists_piece_mem_nhds hδ y.property).imp fun _ h ↦
      continuous_subtypeVal.continuousAt.preimage_mem_nhds h)
    (isPathConnected_cover hδ hcδ) hC (fun k ↦ preimage_mono (comb_subset_piece k))
    (fun _ _ hij _ hz ↦ piece_inter_piece_subset hcδ hij hz)
    hx
  let e (k : ι) := (exists_mulEquiv_cover hc h0 k).choose
  have he (k : ι) := (exists_mulEquiv_cover hc h0 k).choose_spec
  refine ⟨freeGroupEquivCoprodI.trans ((MulEquiv.coprodICongr fun k ↦
    FreeGroup.mulEquivIntOfUnique.trans (e k).symm).trans vK), fun k ↦ ?_⟩
  have hk : (e k).symm (Multiplicative.ofAdd 1) =
      fromPath (Path.Homotopic.Quotient.mk ((loop hc h0 k).codRestrict (loop_mem_cover hc h0 k))) :=
    (e k).symm_apply_eq.mpr (he k).symm
  simp only [MulEquiv.trans_apply, freeGroupEquivCoprodI_apply, FreeGroup.lift_apply_of,
    MulEquiv.coprodICongr_apply_of, vK]
  have h1 : FreeGroup.mulEquivIntOfUnique (FreeGroup.of ()) = Multiplicative.ofAdd 1 := by
    simp [FreeGroup.mulEquivIntOfUnique, FreeGroup.equivIntOfUnique]
  refine (TauCeti.vanKampenWideEquiv_apply _ _ _ _ _ _ _).trans
    ((TauCeti.vanKampenWideLift_of _ _ _ _).trans ?_)
  rw [h1, hk]
  exact congrArg (fun q ↦ fromPath (Path.Homotopic.Quotient.mk q))
    (Path.map_codRestrict _ _)

private theorem bijective_lift_loop :
    Function.Bijective (FreeGroup.lift fun k ↦ fromPath (Path.Homotopic.Quotient.mk
      (loop hc h0 k))) := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_freeGroup hc h0
  have : (FreeGroup.lift fun k ↦ fromPath (Path.Homotopic.Quotient.mk (loop hc h0 k))) =
      ψ.toMonoidHom :=
    FreeGroup.ext_hom _ _ fun k ↦ by simp [hψ]
  rw [this]
  exact ψ.bijective

/-- **The fundamental group of the plane minus finitely many distinct nonzero reals `c i`**, based
at `0`, is the free group on `ι`, the class of `loop hc h0 k` corresponding to the generator
`FreeGroup.of k` (`fundamentalGroupMulEquiv_loop`). -/
def fundamentalGroupMulEquiv :
    FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ ⟨0, zero_mem_compl_range h0⟩ ≃* FreeGroup ι :=
  (MulEquiv.ofBijective _ (bijective_lift_loop hc h0)).symm

/-- The inverse of `fundamentalGroupMulEquiv` sends a word in the generators to the same word in
the classes of the loops. -/
theorem fundamentalGroupMulEquiv_symm_apply (g : FreeGroup ι) :
    (fundamentalGroupMulEquiv hc h0).symm g =
      FreeGroup.lift (fun k ↦ fromPath (Path.Homotopic.Quotient.mk (loop hc h0 k))) g :=
  (rfl)

theorem fundamentalGroupMulEquiv_symm_of (k : ι) :
    (fundamentalGroupMulEquiv hc h0).symm (FreeGroup.of k) =
      fromPath (Path.Homotopic.Quotient.mk (loop hc h0 k)) := by
  rw [fundamentalGroupMulEquiv_symm_apply, FreeGroup.lift_apply_of]

/-- `fundamentalGroupMulEquiv` sends the class of the loop about `c k` to the generator
`FreeGroup.of k`. -/
@[simp]
theorem fundamentalGroupMulEquiv_loop (k : ι) :
    fundamentalGroupMulEquiv hc h0 (fromPath (Path.Homotopic.Quotient.mk (loop hc h0 k))) =
      FreeGroup.of k := by
  rw [← fundamentalGroupMulEquiv_symm_of, MulEquiv.apply_symm_apply]

end Main

end PlaneMinusRealPoints

end SymplecticGeometry
