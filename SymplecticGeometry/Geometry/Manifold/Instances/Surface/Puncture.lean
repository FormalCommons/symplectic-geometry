/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Genus
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.NestedOpens
public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.PuncturedTorus
import TauCeti.Topology.Homotopy.Path
import Mathlib.Analysis.Convex.PathConnected
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.FundamentalGroup
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Manifold.ConnectedSum.Sphere
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.Restrict
import TauCeti.Geometry.Manifold.Connected

/-!
# Punctures of the closed surface of genus `g`

Write `cⱼ = ClosedSurface.ball g j 0` for the centre of the `j`-th coordinate ball of the closed
surface of genus `g`. This file defines the open sets over which an induction on the genus
computes the fundamental groups of the punctured closed surfaces:

* `ClosedSurface.puncture g n`, the complement of `c₀, …, cₙ₋₁`;
* `ClosedSurface.tailPuncture g n`, the complement of `c₁, …, cₙ`, which contains the whole
  ball `0`.

Since the surface of genus `g + 1` is the connected sum of the torus with the surface of genus
`g` along its ball `0`, and its ball `j` is the ball `j + 1` of genus `g`
(`ClosedSurface.succDiffeomorph_ball`), removing `n` centres from the surface of genus `g + 1`
removes the centres `c₁, …, cₙ` from the second summand. In the language of
`TauCeti.ConnectedSum.restrictRightHomeomorph`, whose target is the open set
`range inl ∪ inr '' U` of the connected sum, this says that `puncture (g + 1) n` is that target
for `U = tailPuncture g n` (`ClosedSurface.image_succDiffeomorph_puncture`), and the punctured
second summand of the sum of the torus with `U` is `puncture g (n + 1)`
(`ClosedSurface.imageVal_puncture_codRestrict_ball`).

All these sets are complements of finite sets in a connected surface, so they are path
connected, by Tau Ceti's `TauCeti.isPathConnected_compl_of_finite_of_one_lt_rank`.

For the loops about the centres, the file gives two families of paths that meet no centre. The
circle `ClosedSurface.ballCircle g j` runs once around `cⱼ` in the ball `j`, and
`ClosedSurface.ballPath g j` joins the base point to its start. Both are carried into each
`puncture g n` by restricting their codomain. In genus `g + 1` both are those of the ball `j + 1`
of genus `g`, in the second summand. In the sphere, the paths are explicit segments in the two
charts `sphereBall v` and `w ↦ -sphereBall v (-w)` of Tau Ceti's
`TauCeti.isComplementaryBall_sphereBall`.

## Main definitions

* `SymplecticGeometry.ClosedSurface.puncture g n`: the closed surface of genus `g` with the
  centres of the balls `0, …, n - 1` removed.
* `SymplecticGeometry.ClosedSurface.tailPuncture g n`: the closed surface of genus `g` with the
  centres of the balls `1, …, n` removed.
* `SymplecticGeometry.ClosedSurface.ballCircle g j`: the circle of radius `1` of the ball `j`,
  counterclockwise in the coordinates `SymplecticGeometry.EuclideanTorus.neckIsometry`.
* `SymplecticGeometry.ClosedSurface.ballPath g j`: a path from the base point to the start of
  `ballCircle g j`.
* `SymplecticGeometry.ClosedSurface.puncturedBallCircle g n j`,
  `SymplecticGeometry.ClosedSurface.puncturedBallPath g n j`: the same, in `puncture g n`.

## Main results

* `SymplecticGeometry.ClosedSurface.puncture_zero`, `SymplecticGeometry.ClosedSurface.puncture_one`:
  no puncture is the whole surface, and one puncture is Tau Ceti's
  `TauCeti.ConnectedSum.puncture` of the ball `0`.
* `SymplecticGeometry.ClosedSurface.isPathConnected_puncture`,
  `SymplecticGeometry.ClosedSurface.isPathConnected_tailPuncture`: both are path connected.
* `SymplecticGeometry.ClosedSurface.image_succDiffeomorph_puncture`: `puncture (g + 1) n` is the
  part of the connected sum made of the punctured torus and the points of `tailPuncture g n`.
* `SymplecticGeometry.ClosedSurface.imageVal_puncture_codRestrict_ball`: the punctured second
  summand of the connected sum of the torus with `tailPuncture g n` is `puncture g (n + 1)`.
* `SymplecticGeometry.ClosedSurface.ballCircle_ne_ball`,
  `SymplecticGeometry.ClosedSurface.ballPath_ne_ball`: they meet no centre.
* `SymplecticGeometry.ClosedSurface.succDiffeomorph_ballCircle_apply`,
  `SymplecticGeometry.ClosedSurface.succDiffeomorph_ballPath_apply`: in genus `g + 1` they are
  those of the ball `j + 1` of genus `g`, in the second summand of the connected sum.
* `SymplecticGeometry.ClosedSurface.ballCircle_zero_apply`: the circle of the ball `0` is the
  circle of the neck of the connected sum along that ball, read in the second summand.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (connected sums of manifolds).
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace TauCeti

namespace SymplecticGeometry.ClosedSurface

variable (g n : ℕ)

/-- The closed surface of genus `g` with the centres `ball g j 0` of its balls `j < n` removed,
as an open subset. -/
def puncture : Opens (ClosedSurface g) :=
  ⟨((fun j ↦ ball g j 0) '' Iio n)ᶜ, ((finite_Iio n).image _).isClosed.isOpen_compl⟩

/-- The closed surface of genus `g` with the centres `ball g (j + 1) 0` of its balls
`1, …, n` removed, as an open subset. It contains the ball `0`
(`ClosedSurface.ball_zero_mem_tailPuncture`). -/
def tailPuncture : Opens (ClosedSurface g) :=
  ⟨((fun j ↦ ball g (j + 1) 0) '' Iio n)ᶜ, ((finite_Iio n).image _).isClosed.isOpen_compl⟩

theorem coe_puncture : (puncture g n : Set (ClosedSurface g)) = ((fun j ↦ ball g j 0) '' Iio n)ᶜ :=
  (rfl)

theorem coe_tailPuncture :
    (tailPuncture g n : Set (ClosedSurface g)) = ((fun j ↦ ball g (j + 1) 0) '' Iio n)ᶜ :=
  (rfl)

variable {g n}

theorem mem_puncture {x : ClosedSurface g} : x ∈ puncture g n ↔ ∀ j < n, x ≠ ball g j 0 := by
  rw [← SetLike.mem_coe, coe_puncture]
  simp [eq_comm]

theorem mem_tailPuncture {x : ClosedSurface g} :
    x ∈ tailPuncture g n ↔ ∀ j < n, x ≠ ball g (j + 1) 0 := by
  rw [← SetLike.mem_coe, coe_tailPuncture]
  simp [eq_comm]

variable (g) in
/-- With no centre removed, `puncture g 0` is the whole surface. -/
@[simp]
theorem puncture_zero : puncture g 0 = ⊤ := by
  ext x
  simp [mem_puncture]

variable (g) in
/-- With one centre removed, `puncture g 1` is the punctured summand
`TauCeti.ConnectedSum.puncture (ball g 0)`, along which the next torus is summed. -/
theorem puncture_one : puncture g 1 = ConnectedSum.puncture (ball g 0) :=
  SetLike.ext fun x ↦ by simp [mem_puncture]

variable (g) in
/-- Removing more centres gives a smaller set. -/
theorem puncture_antitone : Antitone (puncture g) :=
  fun _ _ hmn _ hx ↦ mem_puncture.2 fun j hj ↦ mem_puncture.1 hx j (hj.trans_le hmn)

/-- The base point lies in each `puncture g n`. For `n = 1` this is
`ClosedSurface.basePoint_mem_puncture`, read along `ClosedSurface.puncture_one`. -/
@[simp]
theorem basePoint_mem_puncture' : basePoint g ∈ puncture g n :=
  mem_puncture.2 fun j _ h ↦ basePoint_notMem_range_ball j ⟨0, h.symm⟩

/-- A point `ball g j v` lies in `puncture g n` exactly when it is not a centre, or its ball is
not among the balls `0, …, n - 1`. -/
@[simp]
theorem ball_mem_puncture_iff {j : ℕ} {v : EuclideanSpace ℝ (Fin 2)} :
    ball g j v ∈ puncture g n ↔ v ≠ 0 ∨ n ≤ j := by
  simp only [mem_puncture, ne_eq, ball_eq_ball_iff, not_and]
  constructor
  · intro h
    by_contra! hc
    exact h j hc.2 rfl hc.1
  · rintro (hv | hn) k hk rfl
    · exact hv
    · omega

/-- A point `ball g j v` lies in `tailPuncture g n` exactly when it is not a centre, or its ball
is not among the balls `1, …, n`. -/
@[simp]
theorem ball_mem_tailPuncture_iff {j : ℕ} {v : EuclideanSpace ℝ (Fin 2)} :
    ball g j v ∈ tailPuncture g n ↔ v ≠ 0 ∨ j = 0 ∨ n < j := by
  simp only [mem_tailPuncture, ne_eq, ball_eq_ball_iff, not_and]
  constructor
  · intro h
    by_contra! hc
    exact h (j - 1) (by omega) (by omega) hc.1
  · rintro (hv | hj | hn) k hk rfl
    · exact hv
    · omega
    · omega

/-- The ball `0` lies in `tailPuncture g n`. -/
theorem ball_zero_mem_tailPuncture (v : EuclideanSpace ℝ (Fin 2)) :
    ball g 0 v ∈ tailPuncture g n :=
  ball_mem_tailPuncture_iff.2 (Or.inr (Or.inl rfl))

/-- Removing the centre of the ball `0` from `tailPuncture g n` gives `puncture g (n + 1)`. -/
theorem puncture_succ_eq_tailPuncture_inf :
    puncture g (n + 1) = tailPuncture g n ⊓ ConnectedSum.puncture (ball g 0) := by
  refine SetLike.ext fun x ↦ ?_
  simp only [mem_puncture, Opens.mem_inf, mem_tailPuncture, ConnectedSum.mem_puncture]
  exact ⟨fun h ↦ ⟨fun j hj ↦ h (j + 1) (by omega), h 0 (by omega)⟩,
    fun h j hj ↦ j.casesOn (fun _ ↦ h.2) (fun j hj ↦ h.1 j (by omega)) hj⟩

/-- The set `puncture g (n + 1)` lies in `tailPuncture g n`. -/
theorem puncture_succ_le_tailPuncture : puncture g (n + 1) ≤ tailPuncture g n := by
  rw [puncture_succ_eq_tailPuncture_inf]
  exact inf_le_left

/-- The base point lies in each `tailPuncture g n`. -/
@[simp]
theorem basePoint_mem_tailPuncture : basePoint g ∈ tailPuncture g n :=
  puncture_succ_le_tailPuncture basePoint_mem_puncture'

variable (g n)

/-- The closed surface of genus `g` with finitely many centres removed is path connected. -/
theorem isPathConnected_puncture : IsPathConnected (puncture g n : Set (ClosedSurface g)) :=
  isPathConnected_compl_of_finite_of_one_lt_rank (E := EuclideanSpace ℝ (Fin 2))
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) ((finite_Iio n).image _)

theorem isPathConnected_tailPuncture :
    IsPathConnected (tailPuncture g n : Set (ClosedSurface g)) :=
  isPathConnected_compl_of_finite_of_one_lt_rank (E := EuclideanSpace ℝ (Fin 2))
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) ((finite_Iio n).image _)

instance : PathConnectedSpace (puncture g n) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_puncture g n)

instance : PathConnectedSpace (tailPuncture g n) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_tailPuncture g n)

/-- **Punctures of the sum with a torus.** Read as the connected sum of the torus with the closed
surface of genus `g` along its ball `0`, the closed surface of genus `g + 1` with `n` centres
removed is the punctured torus together with the points of `tailPuncture g n`: the target of
`TauCeti.ConnectedSum.restrictRightHomeomorph` for `U = tailPuncture g n`. -/
theorem image_succDiffeomorph_puncture :
    succDiffeomorph '' (puncture (g + 1) n : Set (ClosedSurface (g + 1))) =
      range (ConnectedSum.inl EuclideanTorus.ball (ball g 0)) ∪
        ConnectedSum.inr _ _ '' {y | (y : ClosedSurface g) ∈ (tailPuncture g n : Set _)} := by
  refine compl_injective ?_
  rw [ConnectedSum.compl_range_inl_union_image_inr EuclideanTorus.ball_injective
    ball_zero_mem_tailPuncture]
  ext p
  obtain ⟨x, rfl⟩ : ∃ x, succDiffeomorph x = p := succDiffeomorph.surjective p
  have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
  rw [mem_compl_iff, hinj.mem_set_image]
  simp only [SetLike.mem_coe, mem_puncture, mem_image, mem_ofPred_eq, mem_tailPuncture,
    not_forall, not_not, exists_prop]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨ball g (j + 1) 0, ?_⟩, ⟨j, hj, rfl⟩, ?_⟩
    · exact ConnectedSum.mem_puncture.2 (ball_zero_zero_notMem_range_ball j ⟨0, ·⟩)
    · rw [succDiffeomorph_ball, ConnectedSum.inrBall_apply]
      exact congrArg _ (Subtype.ext (by rw [ConnectedSum.coe_punctureBall]))
  · rintro ⟨y, ⟨j, hj, hy⟩, hyx⟩
    refine ⟨j, hj, hinj ?_⟩
    rw [← hyx, succDiffeomorph_ball, ConnectedSum.inrBall_apply]
    exact congrArg _ (Subtype.ext (by rw [hy, ConnectedSum.coe_punctureBall]))

/-- **The punctured second summand.** In the connected sum of the torus with `tailPuncture g n`,
along the ball `0` corestricted to it, the second summand punctured at the centre of that ball
is, read in the closed surface of genus `g`, the set `puncture g (n + 1)`. -/
theorem imageVal_puncture_codRestrict_ball :
    Opens.imageVal (ConnectedSum.puncture
      (codRestrict (ball g 0) (tailPuncture g n) ball_zero_mem_tailPuncture)) =
        puncture g (n + 1) := by
  refine SetLike.ext fun x ↦ ?_
  rw [puncture_succ_eq_tailPuncture_inf, Opens.mem_imageVal, Opens.mem_inf]
  simp only [ConnectedSum.mem_puncture, ne_eq, Subtype.ext_iff, val_codRestrict_apply,
    exists_prop]
/-! ### The circles of the balls -/

open EuclideanTorus (neckIsometry)

variable {g n}

variable (g) in
/-- The **circle of the ball `j`** of the closed surface of genus `g`: the loop
`t ↦ ball g j (neckIsometry e^{2πit})`, the circle of radius `1` of the ball, counterclockwise in
the coordinates `neckIsometry`. It is the image under the ball of
`LinearIsometryEquiv.circleLoop` for `neckIsometry` and radius `1`, and starts at
`ball g j (neckIsometry 1)`. -/
def ballCircle (j : ℕ) : Path (ball g j (neckIsometry 1)) (ball g j (neckIsometry 1)) :=
  ((neckIsometry.circleLoop one_pos).map
    ((isOpenEmbedding_ball j).continuous.comp continuous_subtypeVal)).cast
      (by simp) (by simp)

variable (g) in
theorem ballCircle_def (j : ℕ) :
    ballCircle g j = ((neckIsometry.circleLoop one_pos).map
      ((isOpenEmbedding_ball j).continuous.comp continuous_subtypeVal)).cast
        (by simp) (by simp) :=
  (rfl)

@[simp]
theorem ballCircle_apply (j : ℕ) (t : unitInterval) :
    ballCircle g j t = ball g j (neckIsometry (circleMap 0 1 (2 * Real.pi * t))) := by
  simp [ballCircle_def]

/-- The circle of a ball meets no centre of a ball. -/
theorem ballCircle_ne_ball (j : ℕ) (t : unitInterval) (k : ℕ) :
    ballCircle g j t ≠ ball g k 0 := by
  rw [ballCircle_apply, ne_eq, ball_eq_ball_iff, not_and]
  rintro -
  simp

/-- The circle of a ball lies in each `puncture g n`. -/
theorem ballCircle_mem_puncture (j : ℕ) (t : unitInterval) : ballCircle g j t ∈ puncture g n :=
  mem_puncture.2 fun k _ ↦ ballCircle_ne_ball j t k

/-- The start of the circle of a ball lies in each `puncture g n`. -/
theorem ball_neckIsometry_one_mem_puncture (j : ℕ) :
    ball g j (neckIsometry 1) ∈ puncture g n :=
  ball_mem_puncture_iff.2 (Or.inl (by simp))

variable (g n) in
/-- The circle of the ball `j`, as a loop in `puncture g n`. -/
def puncturedBallCircle (j : ℕ) :
    Path (⟨ball g j (neckIsometry 1), ball_neckIsometry_one_mem_puncture j⟩ : puncture g n)
      ⟨ball g j (neckIsometry 1), ball_neckIsometry_one_mem_puncture j⟩ :=
  (ballCircle g j).codRestrict fun t ↦ ballCircle_mem_puncture j t

@[simp]
theorem coe_puncturedBallCircle_apply (j : ℕ) (t : unitInterval) :
    (puncturedBallCircle g n j t : ClosedSurface g) = ballCircle g j t :=
  Path.codRestrict_coe _ _ t

@[simp]
theorem map_puncturedBallCircle (j : ℕ) :
    (puncturedBallCircle g n j).map continuous_subtypeVal = ballCircle g j :=
  Path.map_codRestrict _ _

/-- The circle of the ball `0` is the circle `LinearIsometryEquiv.circleLoop` of the neck of the
connected sum along the ball `0`, for `neckIsometry` and radius `1`, read in the second
summand. -/
theorem ballCircle_zero_apply (t : unitInterval) :
    ballCircle g 0 t = ((neckIsometry.circleLoop one_pos).map
      (ConnectedSum.neckInr (isOpenEmbedding_ball (g := g) 0)).continuous t : ClosedSurface g) := by
  rw [ConnectedSum.coe_map_neckInr_circleLoop_apply, inv_one, ballCircle_apply]

/-- In the closed surface of genus `g + 1`, the neck point of the connected sum is the start of
the circle of the ball `0` of genus `g`, in the second summand. -/
theorem inl_neckInl_circleBasepoint :
    ConnectedSum.inl EuclideanTorus.ball (ball g 0)
        (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
          (neckIsometry.circleBasepoint one_pos)) =
      ConnectedSum.inr _ _ ⟨ball g 0 (neckIsometry 1),
        ConnectedSum.mem_puncture.2 (by simp)⟩ := by
  rw [ConnectedSum.inl_neckInl_eq_inr_neckInr _ (isOpenEmbedding_ball 0)]
  exact congrArg _ (Subtype.ext (ConnectedSum.coe_neckInr_circleBasepoint_one _))

/-- The circle of the ball `j` of genus `g + 1` is the circle of the ball `j + 1` of genus `g`,
in the second summand of the connected sum. -/
theorem succDiffeomorph_ballCircle_apply (j : ℕ) (t : unitInterval) :
    succDiffeomorph (ballCircle (g + 1) j t) =
      ConnectedSum.inr _ _ ⟨ballCircle g (j + 1) t,
        ConnectedSum.mem_puncture.2 (ballCircle_ne_ball (j + 1) t 0)⟩ := by
  rw [ballCircle_apply, succDiffeomorph_ball, ConnectedSum.inrBall_apply]
  exact congrArg _ (Subtype.ext
    ((ConnectedSum.coe_punctureBall _ _).trans (ballCircle_apply (j + 1) t).symm))

/-! ### The paths to the balls of the sphere

The sphere `ClosedSurface 0` is read in two charts: the ball `sphereBall v` at its base point `v`,
through which its balls are defined (`ClosedSurface.zeroDiffeomorph_ball`), and the
complementary chart `w ↦ -sphereBall v (-w)`, which sends `0` to `v` and agrees with
`sphereBall v ∘ inversion 0 1` away from `0` (`TauCeti.isComplementaryBall_sphereBall`). In the
chart `sphereBall v`, the centre of the ball `j` is `j • e`, for `e = (1, 0)`, and the start of its
circle is `(j + 1 / 4, 1 / 4)`. In the complementary chart, the path to the ball `0` is the
segment from `0` to the start of its circle. The path to the ball `j + 1` is the segment from `0`
down to `(0, -1)`, a point that both charts share, then, in the chart `sphereBall v`, the segment
from `(0, -1)` to `(j + 5 / 4, -1)` and the segment up to `(j + 5 / 4, 1 / 4)`. -/

section Sphere

open OpenPartialHomeomorph

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- A point of the sphere, read in the chart `sphereBall v` at its base point `v`. -/
private def sphereChart (w : EuclideanSpace ℝ (Fin 2)) : ClosedSurface 0 :=
  zeroDiffeomorph.symm (sphereBall (zeroDiffeomorph (basePoint 0)) w)

private theorem continuous_sphereChart : Continuous sphereChart :=
  zeroDiffeomorph.symm.continuous.comp (isOpenEmbedding_sphereBall _).continuous

/-- A point of the sphere, read in the chart `w ↦ -sphereBall v (-w)` complementary to
`sphereBall v`. -/
private def sphereCoChart (w : EuclideanSpace ℝ (Fin 2)) : ClosedSurface 0 :=
  zeroDiffeomorph.symm (-sphereBall (zeroDiffeomorph (basePoint 0)) (-w))

private theorem continuous_sphereCoChart : Continuous sphereCoChart :=
  zeroDiffeomorph.symm.continuous.comp
    (isComplementaryBall_sphereBall _).isOpenEmbedding.continuous

private theorem sphereCoChart_zero : sphereCoChart 0 = basePoint 0 := by
  rw [sphereCoChart, neg_zero, sphereBall_zero, neg_neg, Diffeomorph.symm_apply_apply]

private theorem sphereCoChart_of_ne {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) :
    sphereCoChart w = sphereChart (EuclideanGeometry.inversion 0 1 w) := by
  rw [sphereCoChart, sphereChart, ← (isComplementaryBall_sphereBall _).apply_eq_inversion w hw]

private theorem ball_zero_eq_sphereChart (j : ℕ) (w : EuclideanSpace ℝ (Fin 2)) :
    ball 0 j w = sphereChart (univBall (j • EuclideanSpace.single 0 1) (1 / 2) w) := by
  rw [sphereChart, ← zeroDiffeomorph_ball, Diffeomorph.symm_apply_apply]

private theorem sphereChart_ne_ball {w : EuclideanSpace ℝ (Fin 2)}
    (hw : ∀ k : ℕ, w ≠ k • EuclideanSpace.single 0 1) (k : ℕ) : sphereChart w ≠ ball 0 k 0 := by
  rw [ball_zero_eq_sphereChart, univBall_apply_zero]
  exact fun h ↦ hw k ((isOpenEmbedding_sphereBall _).injective (zeroDiffeomorph.symm.injective h))

/-- In the chart `sphereBall v`, the start of the circle of the ball `j` is `(j + 1 / 4, 1 / 4)`. -/
private theorem univBall_neckIsometry_one (j : ℕ) :
    univBall (j • EuclideanSpace.single 0 1) (1 / 2) (neckIsometry 1) =
      !₂[(j : ℝ) + 1 / 4, 1 / 4] := by
  have h1 : (1 : ℂ) = circleMap 0 1 0 := by simp [circleMap]
  have hn : ‖neckIsometry 1‖ = 1 := by simp
  have h2 : √(1 + (1 : ℝ) ^ 2) = √2 := by norm_num
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [univBall_apply (by norm_num), hn, h2, h1, EuclideanTorus.neckIsometry_circleMap]
  ext i
  fin_cases i <;> simp [Real.cos_pi_div_four, Real.sin_pi_div_four] <;> field_simp <;>
    linarith [hs]

/-- The segment in the complementary chart from `0`, the base point, to the point that is `w` in
the chart `sphereBall v`. -/
private def sphereRay {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) :
    Path (basePoint 0) (sphereChart w) :=
  ((Path.segment 0 (EuclideanGeometry.inversion 0 1 w)).map continuous_sphereCoChart).cast
    sphereCoChart_zero.symm
    (by rw [sphereCoChart_of_ne (by simpa [EuclideanGeometry.inversion_eq_center] using hw),
      EuclideanGeometry.inversion_inversion _ one_ne_zero])

private theorem sphereRay_ne_ball {w : EuclideanSpace ℝ (Fin 2)} (hw : w 1 ≠ 0) (t : unitInterval)
    (k : ℕ) : sphereRay (w := w) (fun h ↦ hw (by simp [h])) t ≠ ball 0 k 0 := by
  -- The inversion in the unit circle keeps the sign of the second coordinate.
  have hinv {x : EuclideanSpace ℝ (Fin 2)} (hx : x 1 ≠ 0) :
      EuclideanGeometry.inversion 0 1 x 1 ≠ 0 := by
    have h : x ≠ 0 := fun h ↦ hx (by simp [h])
    simp [EuclideanGeometry.inversion, h, hx]
  rcases eq_or_ne (t : ℝ) 0 with ht | ht
  · rw [sphereRay, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply, ht,
      AffineMap.lineMap_apply_zero, sphereCoChart_zero]
    exact fun h ↦ basePoint_notMem_range_ball k ⟨0, h.symm⟩
  · have h1 : ((t : ℝ) • EuclideanGeometry.inversion 0 1 w) 1 ≠ 0 := by
      simpa [ht] using hinv hw
    rw [sphereRay, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
      AffineMap.lineMap_apply_module', sub_zero, add_zero,
      sphereCoChart_of_ne (fun h ↦ h1 (by simp [h]))]
    refine sphereChart_ne_ball (fun k h ↦ hinv h1 ?_) k
    simp [h]

/-- The segment from `a` to `b` in the chart `sphereBall v`. -/
private def sphereSegment (a b : EuclideanSpace ℝ (Fin 2)) : Path (sphereChart a) (sphereChart b) :=
  (Path.segment a b).map continuous_sphereChart

private theorem sphereSegment_ne_ball {a b : EuclideanSpace ℝ (Fin 2)}
    (h : ∀ (t : unitInterval) (k : ℕ),
      AffineMap.lineMap a b (t : ℝ) ≠ k • EuclideanSpace.single 0 1)
    (t : unitInterval) (k : ℕ) : sphereSegment a b t ≠ ball 0 k 0 := by
  rw [sphereSegment, Path.map_coe, Function.comp_apply, Path.segment_apply]
  exact sphereChart_ne_ball (h t) k

/-- The path from the base point of the sphere to the start of the circle of its ball `j`. -/
private def zeroBallPath : (j : ℕ) → Path (basePoint 0) (ball 0 j (neckIsometry 1))
  | 0 => (sphereRay (w := univBall ((0 : ℕ) • EuclideanSpace.single 0 1) (1 / 2) (neckIsometry 1))
      (by rw [univBall_neckIsometry_one]; simp)).cast rfl (ball_zero_eq_sphereChart 0 _)
  | j + 1 => ((sphereRay (w := !₂[0, -1]) (by simp)).trans
      ((sphereSegment !₂[0, -1] !₂[((j + 1 : ℕ) : ℝ) + 1 / 4, -1]).trans
        (sphereSegment !₂[((j + 1 : ℕ) : ℝ) + 1 / 4, -1]
          !₂[((j + 1 : ℕ) : ℝ) + 1 / 4, 1 / 4]))).cast
      rfl (by rw [ball_zero_eq_sphereChart, univBall_neckIsometry_one])

private theorem zeroBallPath_ne_ball (j : ℕ) (t : unitInterval) (k : ℕ) :
    zeroBallPath j t ≠ ball 0 k 0 := by
  cases j with
  | zero =>
    rw [zeroBallPath, Path.cast_coe]
    exact sphereRay_ne_ball (by rw [univBall_neckIsometry_one]; simp) t k
  | succ j =>
    suffices ball 0 k 0 ∉ range (zeroBallPath (j + 1)) from fun h ↦ this ⟨t, h⟩
    rw [zeroBallPath, Path.cast_coe, Path.trans_range, Path.trans_range]
    rintro (⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩)
    · exact sphereRay_ne_ball (w := !₂[0, -1]) (by simp) s k hs
    · refine sphereSegment_ne_ball (fun s k h ↦ ?_) s k hs
      have h1 := congrArg (· 1) h
      simp [AffineMap.lineMap_apply_module] at h1
      linarith
    · refine sphereSegment_ne_ball (fun s k h ↦ ?_) s k hs
      have h0 := congrArg (· 0) h
      simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul] at h0
      have : (4 * k : ℝ) = 4 * j + 5 := by simp at h0; linarith
      have : 4 * k = 4 * j + 5 := by exact_mod_cast this
      omega

end Sphere
/-! ### The paths to the balls -/

/-- The paths to the balls of the closed surface of genus `g`, defined together with the fact
that they meet no centre, which lets the recursion carry them into the second summand. -/
private def ballPathAux : (g j : ℕ) →
    {γ : Path (basePoint g) (ball g j (neckIsometry 1)) // ∀ t k, γ t ≠ ball g k 0}
  | 0, j => ⟨zeroBallPath j, zeroBallPath_ne_ball j⟩
  | g + 1, j =>
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
      EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
    ⟨((((ballPathAux g (j + 1)).val.codRestrict (s := ConnectedSum.puncture (ball g 0))
        (x := ⟨basePoint g, basePoint_mem_puncture⟩)
        (y := ⟨ball g (j + 1) (neckIsometry 1), ConnectedSum.mem_puncture.2 (by simp)⟩)
        fun t ↦ ConnectedSum.mem_puncture.2 ((ballPathAux g (j + 1)).property t 0)).map
          (ConnectedSum.continuous_inr _ _)).map (succDiffeomorph (g := g)).symm.continuous).cast
        (by rw [← succDiffeomorph_basePoint, Diffeomorph.symm_apply_apply])
        (by
          rw [← succDiffeomorph.symm_apply_apply (ball (g + 1) j _), succDiffeomorph_ball,
            ConnectedSum.inrBall_apply]
          exact congrArg _ (congrArg _ (Subtype.ext (ConnectedSum.coe_punctureBall _ _)))),
      fun t k h ↦ (ballPathAux g (j + 1)).property t (k + 1) <| by
        have h' := congrArg succDiffeomorph h
        simp only [Path.cast_coe, Path.map_coe, Function.comp_apply,
          Diffeomorph.apply_symm_apply, succDiffeomorph_ball, ConnectedSum.inrBall_apply] at h'
        have h'' :=
          congrArg Subtype.val (ConnectedSum.inr_injective EuclideanTorus.ball_injective h')
        rwa [Path.codRestrict_coe, ConnectedSum.coe_punctureBall] at h''⟩

variable (g) in
/-- The **path to the ball `j`** of the closed surface of genus `g`: a path from the base point
to the start `ball g j (neckIsometry 1)` of the circle `ClosedSurface.ballCircle g j`, which
meets no centre of a ball (`ClosedSurface.ballPath_ne_ball`). For `g + 1` it is the path to the
ball `j + 1` of genus `g`, in the second summand of the connected sum
(`ClosedSurface.succDiffeomorph_ballPath_apply`). For `g = 0`, read in the chart
`w ↦ -sphereBall v (-w)` of the sphere complementary to `sphereBall v`, in which the base point is
`0` and the centre of the ball `j + 1` is `(j + 1)⁻¹ • e`: the path to the ball `0` is the segment
from `0` at the angle `π / 4` out to the circle of the ball, a circle of radius `2 √2` about `0`,
and the path to the ball `j + 1` runs from `0` down into the lower half-plane, along it, and up to
the circle of the ball, crossing the real axis only inside that ball. -/
def ballPath (j : ℕ) : Path (basePoint g) (ball g j (neckIsometry 1)) :=
  (ballPathAux g j).val

/-- The path to a ball meets no centre of a ball. -/
theorem ballPath_ne_ball (j : ℕ) (t : unitInterval) (k : ℕ) : ballPath g j t ≠ ball g k 0 :=
  (ballPathAux g j).property t k

/-- The path to a ball lies in each `puncture g n`. -/
@[simp]
theorem ballPath_mem_puncture (j : ℕ) (t : unitInterval) : ballPath g j t ∈ puncture g n :=
  mem_puncture.2 fun k _ ↦ ballPath_ne_ball j t k

/-- The path to the ball `j` of genus `g + 1` is the path to the ball `j + 1` of genus `g`, in
the second summand of the connected sum. -/
theorem succDiffeomorph_ballPath_apply (j : ℕ) (t : unitInterval) :
    succDiffeomorph (ballPath (g + 1) j t) =
      ConnectedSum.inr _ _ ⟨ballPath g (j + 1) t,
        ConnectedSum.mem_puncture.2 (ballPath_ne_ball (j + 1) t 0)⟩ := by
  simp only [ballPath, ballPathAux, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Diffeomorph.apply_symm_apply]
  exact congrArg _ (Subtype.ext (Path.codRestrict_coe _ _ t))

variable (g n) in
/-- The path to the ball `j`, as a path in `puncture g n`. -/
def puncturedBallPath (j : ℕ) :
    Path (⟨basePoint g, basePoint_mem_puncture'⟩ : puncture g n)
      ⟨ball g j (neckIsometry 1), ball_neckIsometry_one_mem_puncture j⟩ :=
  (ballPath g j).codRestrict fun t ↦ ballPath_mem_puncture j t

@[simp]
theorem coe_puncturedBallPath_apply (j : ℕ) (t : unitInterval) :
    (puncturedBallPath g n j t : ClosedSurface g) = ballPath g j t :=
  Path.codRestrict_coe _ _ t

@[simp]
theorem map_puncturedBallPath (j : ℕ) :
    (puncturedBallPath g n j).map continuous_subtypeVal = ballPath g j :=
  Path.map_codRestrict _ _

end SymplecticGeometry.ClosedSurface

end
