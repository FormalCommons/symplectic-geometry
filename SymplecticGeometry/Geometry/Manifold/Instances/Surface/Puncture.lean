/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Genus
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.NestedOpens
public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.PuncturedTorus
public import TauCeti.Topology.Homotopy.Path
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
`TauCeti.isComplementaryBall_sphereBall`, which the file names `ClosedSurface.sphereChart` and
`ClosedSurface.sphereCoChart`.

From these the file builds the loops at the base point whose classes the computation of the
fundamental group uses. The path `ClosedSurface.summandPath g k` joins the base point to the point
`0` of the torus summand `k`; `ClosedSurface.circleLoop g k i` runs along it, once around the
circle `i` of that torus, and back. The loop `ClosedSurface.ballLoop g j` runs along
`ballPath g j`, backwards once around `ballCircle g j`, and back. The loop
`ClosedSurface.peripheralLoop g n i` of `puncture g n` is `ballLoop g i.rev` restricted to it, so
that the index `i` of a peripheral loop belongs to the ball `i.rev`: the ball `0`, along which
the next torus is summed, carries the last one. A path of genus `g` that misses the centre of the
ball `0` is carried to genus `g + 1` through the second summand by `ClosedSurface.succPath`, and
the paths and loops of genus `g + 1` are related in this way to those of genus `g`.

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
* `SymplecticGeometry.ClosedSurface.sphereChart`,
  `SymplecticGeometry.ClosedSurface.sphereCoChart`: the two charts of the sphere `ClosedSurface 0`,
  about the point opposite its base point and about the base point.
* `SymplecticGeometry.ClosedSurface.succPath`: a path of genus `g` missing the centre of the
  ball `0`, carried to genus `g + 1` through the second summand of the connected sum.
* `SymplecticGeometry.ClosedSurface.summandPath g k`: a path from the base point to the point `0`
  of the torus summand `k`.
* `SymplecticGeometry.ClosedSurface.circleLoop g k i`: the circle `i` of the torus summand `k`,
  as a loop at the base point.
* `SymplecticGeometry.ClosedSurface.puncturedSummandPath g n k`,
  `SymplecticGeometry.ClosedSurface.puncturedCircleLoop g n k i`: the same, in `puncture g n`.
* `SymplecticGeometry.ClosedSurface.ballLoop g j`: the loop at the base point about the centre
  of the ball `j`.
* `SymplecticGeometry.ClosedSurface.peripheralLoop g n i`: the loop of `puncture g n` at the base
  point about the centre of the ball `i.rev`.

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
* `SymplecticGeometry.ClosedSurface.ballPath_zero_zero`,
  `SymplecticGeometry.ClosedSurface.ballPath_zero_succ`: the paths to the balls of the sphere, as
  segments in its two charts.
* `SymplecticGeometry.ClosedSurface.isComplementaryBall_sphereChart`: the two charts of the sphere
  form a pair of complementary balls, in the sense of Tau Ceti's `TauCeti.IsComplementaryBall`.
* `SymplecticGeometry.ClosedSurface.range_sphereCoChart`: the complementary chart of the sphere
  misses only the centre of the ball `0`.
* `SymplecticGeometry.ClosedSurface.ball_zero_apply_zero_eq_sphereCoChart`: for `j ≠ 0`, the
  centre of the ball `j` of the sphere is `j⁻¹ • e` in the complementary chart, for `e = (1, 0)`.
* `SymplecticGeometry.ClosedSurface.summandPath_ne_ball`,
  `SymplecticGeometry.ClosedSurface.circleLoop_ne_ball`,
  `SymplecticGeometry.ClosedSurface.ballLoop_ne_ball`: they meet no centre.
* `SymplecticGeometry.ClosedSurface.summandPath_succ_zero`: the path to the torus summand `0` of
  genus `g + 1` crosses the neck from the second summand into the torus.
* `SymplecticGeometry.ClosedSurface.succDiffeomorph_summandPath_succ_apply`,
  `SymplecticGeometry.ClosedSurface.succDiffeomorph_circleLoop_succ_apply`,
  `SymplecticGeometry.ClosedSurface.succDiffeomorph_ballLoop_apply`,
  `SymplecticGeometry.ClosedSurface.succDiffeomorph_peripheralLoop_apply`: in genus `g + 1`, those
  of the summand `k + 1`, the loop about the ball `j` and the peripheral loop `i` are those of
  the summand `k`, the loop about the ball `j + 1` and the peripheral loop `Fin.castSucc i` of
  genus `g`, in the second summand.

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
`ClosedSurface.basePoint_mem_puncture_ball_zero`, read along `ClosedSurface.puncture_one`. -/
@[simp]
theorem basePoint_mem_puncture : basePoint g ∈ puncture g n :=
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
  puncture_succ_le_tailPuncture basePoint_mem_puncture

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
  exact congrArg _ (Subtype.ext (by
    rw [ConnectedSum.coe_neckInr_circleBasepoint, inv_one, Complex.ofReal_one]))

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

The sphere `ClosedSurface 0` is read in two charts: the ball `sphereBall v` for its base point `v`,
through which its balls are defined (`ClosedSurface.zeroDiffeomorph_ball`), and the
complementary chart `w ↦ -sphereBall v (-w)`, which sends `0` to `v` and agrees with
`sphereBall v ∘ inversion 0 1` away from `0` (`TauCeti.isComplementaryBall_sphereBall`). In the
chart `sphereBall v`, the centre of the ball `j` is `j • e`, for `e = (1, 0)`, and the start of its
circle is `(j + 1 / 4, 1 / 4)`, which is `(2, 2)` in the complementary chart when `j = 0`. In the
complementary chart, the path to the ball `0` is the segment from `0` to `(2, 2)`. The path to the
ball `j + 1` is the segment from `0` down to `(0, -1)`, a point that both charts share, then, in
the chart `sphereBall v`, the segment from `(0, -1)` to `(j + 5 / 4, -1)` and the segment up to
`(j + 5 / 4, 1 / 4)`. -/

section Sphere

open OpenPartialHomeomorph

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The **chart of the sphere opposite its base point**: the point of `ClosedSurface 0` that is `w`
in Tau Ceti's coordinate ball `sphereBall v` of the round sphere, for its base point `v`. That ball
is centred at `-v`, and the balls of the sphere are defined through it. -/
def sphereChart (w : EuclideanSpace ℝ (Fin 2)) : ClosedSurface 0 :=
  zeroDiffeomorph.symm (sphereBall (zeroDiffeomorph (basePoint 0)) w)

theorem sphereChart_def (w : EuclideanSpace ℝ (Fin 2)) :
    sphereChart w = zeroDiffeomorph.symm (sphereBall (zeroDiffeomorph (basePoint 0)) w) :=
  (rfl)

theorem continuous_sphereChart : Continuous sphereChart :=
  zeroDiffeomorph.symm.continuous.comp (isOpenEmbedding_sphereBall _).continuous

/-- The **complementary chart of the sphere**: the point of `ClosedSurface 0` that is `w` in the
chart `w ↦ -sphereBall v (-w)` complementary to `sphereBall v`, in which the base point is `0`
(`ClosedSurface.sphereCoChart_zero`). -/
def sphereCoChart (w : EuclideanSpace ℝ (Fin 2)) : ClosedSurface 0 :=
  zeroDiffeomorph.symm (-sphereBall (zeroDiffeomorph (basePoint 0)) (-w))

theorem sphereCoChart_def (w : EuclideanSpace ℝ (Fin 2)) :
    sphereCoChart w = zeroDiffeomorph.symm (-sphereBall (zeroDiffeomorph (basePoint 0)) (-w)) :=
  (rfl)

theorem continuous_sphereCoChart : Continuous sphereCoChart :=
  zeroDiffeomorph.symm.continuous.comp
    (isComplementaryBall_sphereBall _).isOpenEmbedding.continuous

/-- The complementary chart sends `0` to the base point of the sphere. -/
@[simp] theorem sphereCoChart_zero : sphereCoChart 0 = basePoint 0 := by
  rw [sphereCoChart_def, neg_zero, sphereBall_zero, neg_neg, Diffeomorph.symm_apply_apply]

/-- Away from `0`, the complementary chart is the chart `sphereChart` after the inversion in the
unit circle. -/
theorem sphereCoChart_of_ne {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) :
    sphereCoChart w = sphereChart (EuclideanGeometry.inversion 0 1 w) := by
  rw [sphereCoChart_def, sphereChart_def,
    ← (isComplementaryBall_sphereBall _).apply_eq_inversion w hw]

/-- Away from `0`, the complementary chart after the inversion in the unit circle is the chart
`sphereChart`. -/
theorem sphereCoChart_inversion {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) :
    sphereCoChart (EuclideanGeometry.inversion 0 1 w) = sphereChart w := by
  rw [sphereCoChart_of_ne (by simpa [EuclideanGeometry.inversion_eq_center] using hw),
    EuclideanGeometry.inversion_inversion _ one_ne_zero]

/-- On the unit circle the two charts of the sphere agree. -/
theorem sphereCoChart_of_norm_eq_one {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ = 1) :
    sphereCoChart w = sphereChart w := by
  rw [sphereCoChart_of_ne (by rintro rfl; simp at hw),
    EuclideanGeometry.inversion_of_mem_sphere (by simpa using hw)]

/-- The point `(0, -1)` is the same point in both charts of the sphere. -/
theorem sphereCoChart_zero_neg_one : sphereCoChart !₂[0, -1] = sphereChart !₂[0, -1] :=
  sphereCoChart_of_norm_eq_one (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_two])

/-- The ball `j` of the sphere, read in the chart `sphereChart`, is the ball of radius `1 / 2`
about `j • e`, for `e = (1, 0)`. -/
theorem ball_zero_eq_sphereChart (j : ℕ) (w : EuclideanSpace ℝ (Fin 2)) :
    ball 0 j w = sphereChart (univBall (j • EuclideanSpace.single 0 1) (1 / 2) w) := by
  rw [sphereChart_def, ← zeroDiffeomorph_ball, Diffeomorph.symm_apply_apply]

/-- The two charts of the sphere form a complementary pair of balls: the chart `sphereCoChart` is
an open embedding that misses only the centre of `sphereChart`, and the two are glued by the
inversion in the unit circle. -/
theorem isComplementaryBall_sphereChart : IsComplementaryBall sphereChart sphereCoChart :=
  have h := isComplementaryBall_sphereBall (n := 2) (zeroDiffeomorph (basePoint 0))
  have hc : sphereCoChart = zeroDiffeomorph.symm ∘
      fun w ↦ -sphereBall (zeroDiffeomorph (basePoint 0)) (-w) := by
    ext1 w
    rw [sphereCoChart_def, comp_apply]
  { isOpenEmbedding := by
      rw [hc]
      exact zeroDiffeomorph.symm.toHomeomorph.isOpenEmbedding.comp h.isOpenEmbedding
    range_eq := by
      rw [hc, range_comp, h.range_eq,
        image_compl_eq (f := zeroDiffeomorph.symm) zeroDiffeomorph.symm.toHomeomorph.bijective,
        image_singleton, sphereChart_def]
    apply_eq_inversion := fun _ hw ↦ sphereCoChart_of_ne hw }

/-- The complementary chart of the sphere covers everything but the centre of the ball `0`. -/
theorem range_sphereCoChart : range sphereCoChart = {ball 0 0 0}ᶜ := by
  rw [isComplementaryBall_sphereChart.range_eq, ball_zero_eq_sphereChart, univBall_apply_zero,
    zero_smul]

/-- For `j ≠ 0`, the centre of the ball `j` of the sphere is `j⁻¹ • e` in the complementary chart,
for `e = (1, 0)`. -/
theorem ball_zero_apply_zero_eq_sphereCoChart {j : ℕ} (hj : j ≠ 0) :
    ball 0 j 0 = sphereCoChart ((j : ℝ)⁻¹ • EuclideanSpace.single 0 1) := by
  have hj' : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hj
  rw [ball_zero_eq_sphereChart, univBall_apply_zero, sphereCoChart_of_ne (by simp [hj'])]
  congr 1
  simp only [EuclideanGeometry.inversion, dist_zero_right, norm_smul, norm_inv, RCLike.norm_natCast,
    PiLp.norm_single, norm_one, mul_one, div_inv_eq_mul, one_mul, vsub_eq_sub, sub_zero, smul_smul,
    vadd_eq_add, add_zero]
  rw [← Nat.cast_smul_eq_nsmul ℝ, sq, mul_assoc, mul_inv_cancel₀ hj', mul_one]

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

/-- In the chart `sphereChart`, the start of the circle of the ball `j` of the sphere is
`(j + 1 / 4, 1 / 4)`. -/
theorem ball_zero_neckIsometry_one (j : ℕ) :
    ball 0 j (neckIsometry 1) = sphereChart !₂[(j : ℝ) + 1 / 4, 1 / 4] := by
  rw [ball_zero_eq_sphereChart, univBall_neckIsometry_one]

/-- In the complementary chart, the start of the circle of the ball `0` of the sphere is
`(2, 2)`. -/
theorem ball_zero_zero_neckIsometry_one :
    ball 0 0 (neckIsometry 1) = sphereCoChart !₂[2, 2] := by
  rw [ball_zero_neckIsometry_one, sphereCoChart_of_ne (by simp)]
  have hn : dist (!₂[2, 2] : EuclideanSpace ℝ (Fin 2)) 0 = √8 := by
    rw [dist_zero_right, EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two]
  have hs : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  rw [EuclideanGeometry.inversion, hn, div_pow, hs]
  congr 1
  ext i
  fin_cases i <;> simp <;> norm_num

/-- A segment from `0` in the complementary chart, in a direction off the real axis, meets no
centre of a ball. -/
private theorem sphereCoChart_smul_ne_ball {w : EuclideanSpace ℝ (Fin 2)} (hw : w 1 ≠ 0)
    (t : ℝ) (k : ℕ) : sphereCoChart (t • w) ≠ ball 0 k 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [zero_smul, sphereCoChart_zero]
    exact fun h ↦ basePoint_notMem_range_ball k ⟨0, h.symm⟩
  · -- The inversion in the unit circle keeps the sign of the second coordinate.
    have h1 : (t • w) 1 ≠ 0 := by simpa [ht] using hw
    have h0 : t • w ≠ 0 := fun h ↦ h1 (by simp [h])
    rw [sphereCoChart_of_ne h0]
    refine sphereChart_ne_ball (fun k h ↦ ?_) k
    have := congrArg (· 1) h
    simp [EuclideanGeometry.inversion, h0, ht, hw] at this

private theorem sphereChart_segment_ne_ball {a b : EuclideanSpace ℝ (Fin 2)}
    (h : ∀ (t : unitInterval) (k : ℕ),
      AffineMap.lineMap a b (t : ℝ) ≠ k • EuclideanSpace.single 0 1)
    (t : unitInterval) (k : ℕ) :
    (Path.segment a b).map continuous_sphereChart t ≠ ball 0 k 0 := by
  rw [Path.map_coe, Function.comp_apply, Path.segment_apply]
  exact sphereChart_ne_ball (h t) k

/-- The path from the base point of the sphere to the start of the circle of its ball `j`. -/
private def zeroBallPath : (j : ℕ) → Path (basePoint 0) (ball 0 j (neckIsometry 1))
  | 0 => ((Path.segment 0 !₂[2, 2]).map continuous_sphereCoChart).cast sphereCoChart_zero.symm
      ball_zero_zero_neckIsometry_one
  | j + 1 => ((((Path.segment 0 !₂[0, -1]).map continuous_sphereCoChart).cast
        sphereCoChart_zero.symm sphereCoChart_zero_neg_one.symm).trans
      (((Path.segment !₂[0, -1] !₂[(j : ℝ) + 5 / 4, -1]).map continuous_sphereChart).trans
        ((Path.segment !₂[(j : ℝ) + 5 / 4, -1] !₂[(j : ℝ) + 5 / 4, 1 / 4]).map
          continuous_sphereChart))).cast
      rfl (by rw [ball_zero_neckIsometry_one]; push_cast; ring_nf)

private theorem zeroBallPath_ne_ball (j : ℕ) (t : unitInterval) (k : ℕ) :
    zeroBallPath j t ≠ ball 0 k 0 := by
  cases j with
  | zero =>
    rw [zeroBallPath, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
      AffineMap.lineMap_apply_module', sub_zero, add_zero]
    exact sphereCoChart_smul_ne_ball (by simp) _ k
  | succ j =>
    suffices ball 0 k 0 ∉ range (zeroBallPath (j + 1)) from fun h ↦ this ⟨t, h⟩
    rw [zeroBallPath, Path.cast_coe, Path.trans_range, Path.trans_range]
    rintro (⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩)
    · rw [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
        AffineMap.lineMap_apply_module', sub_zero, add_zero] at hs
      exact sphereCoChart_smul_ne_ball (w := !₂[0, -1]) (by simp) _ k hs
    · refine sphereChart_segment_ne_ball (fun s k h ↦ ?_) s k hs
      have h1 := congrArg (· 1) h
      simp [AffineMap.lineMap_apply_module] at h1
      linarith
    · refine sphereChart_segment_ne_ball (fun s k h ↦ ?_) s k hs
      have h0 := congrArg (· 0) h
      simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul] at h0
      have : (4 * k : ℝ) = 4 * j + 5 := by simp at h0; linarith
      have : 4 * k = 4 * j + 5 := by exact_mod_cast this
      omega

end Sphere

/-! ### Paths of genus `g` in genus `g + 1` -/

/-- A path `γ` of the closed surface of genus `g` that misses the centre of the ball `0`, as a
path of the closed surface of genus `g + 1` through the second summand of the connected sum
(`ClosedSurface.succDiffeomorph_succPath_apply`). Its ends are given as points `x'`, `y'` of
genus `g + 1` that `succDiffeomorph` sends to the ends of `γ` in the second summand. -/
def succPath {x y : ConnectedSum.puncture (ball g 0)} {x' y' : ClosedSurface (g + 1)}
    (γ : Path x.val y.val) (hγ : ∀ t, γ t ∈ ConnectedSum.puncture (ball g 0))
    (hx : succDiffeomorph x' = ConnectedSum.inr _ _ x)
    (hy : succDiffeomorph y' = ConnectedSum.inr _ _ y) : Path x' y' :=
  letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
    EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
  (((γ.codRestrict hγ).map (ConnectedSum.continuous_inr _ _)).map
    (succDiffeomorph (g := g)).symm.continuous).cast
    (by rw [← hx, Diffeomorph.symm_apply_apply])
    (by rw [← hy, Diffeomorph.symm_apply_apply])

theorem succPath_def {x y : ConnectedSum.puncture (ball g 0)} {x' y' : ClosedSurface (g + 1)}
    (γ : Path x.val y.val) (hγ : ∀ t, γ t ∈ ConnectedSum.puncture (ball g 0))
    (hx : succDiffeomorph x' = ConnectedSum.inr _ _ x)
    (hy : succDiffeomorph y' = ConnectedSum.inr _ _ y) :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
      EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
    succPath γ hγ hx hy = (((γ.codRestrict hγ).map (ConnectedSum.continuous_inr _ _)).map
      (succDiffeomorph (g := g)).symm.continuous).cast
      (by rw [← hx, Diffeomorph.symm_apply_apply])
      (by rw [← hy, Diffeomorph.symm_apply_apply]) :=
  (rfl)

/-- Read in the connected sum, a path of genus `g` carried to genus `g + 1` is the path itself,
in the second summand. -/
@[simp]
theorem succDiffeomorph_succPath_apply {x y : ConnectedSum.puncture (ball g 0)}
    {x' y' : ClosedSurface (g + 1)} (γ : Path x.val y.val)
    (hγ : ∀ t, γ t ∈ ConnectedSum.puncture (ball g 0))
    (hx : succDiffeomorph x' = ConnectedSum.inr _ _ x)
    (hy : succDiffeomorph y' = ConnectedSum.inr _ _ y) (t : unitInterval) :
    succDiffeomorph (succPath γ hγ hx hy t) = ConnectedSum.inr _ _ ⟨γ t, hγ t⟩ := by
  simp only [succPath_def, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Diffeomorph.apply_symm_apply]
  exact congrArg _ (Subtype.ext (Path.codRestrict_coe γ hγ t))

/-- A path of genus `g` that misses the centre of the ball `j + 1` misses, carried to genus
`g + 1`, the centre of the ball `j`. -/
theorem succPath_ne_ball {x y : ConnectedSum.puncture (ball g 0)}
    {x' y' : ClosedSurface (g + 1)} (γ : Path x.val y.val)
    (hγ : ∀ t, γ t ∈ ConnectedSum.puncture (ball g 0))
    (hx : succDiffeomorph x' = ConnectedSum.inr _ _ x)
    (hy : succDiffeomorph y' = ConnectedSum.inr _ _ y) {t : unitInterval} {j : ℕ}
    (h : γ t ≠ ball g (j + 1) 0) : succPath γ hγ hx hy t ≠ ball (g + 1) j 0 := fun h' ↦ h <| by
  have h'' := congrArg succDiffeomorph h'
  rw [succDiffeomorph_succPath_apply, succDiffeomorph_ball, ConnectedSum.inrBall_apply] at h''
  have := congrArg Subtype.val (ConnectedSum.inr_injective EuclideanTorus.ball_injective h'')
  rwa [ConnectedSum.coe_punctureBall] at this

/-! ### The paths to the balls -/

/-- The start of the circle of the ball `j` of genus `g + 1` is that of the ball `j + 1` of
genus `g`, in the second summand. -/
private theorem succDiffeomorph_ball_neckIsometry_one (j : ℕ) :
    succDiffeomorph (ball (g + 1) j (neckIsometry 1)) =
      ConnectedSum.inr _ _ ⟨ball g (j + 1) (neckIsometry 1),
        ConnectedSum.mem_puncture.2 (by simp)⟩ := by
  rw [succDiffeomorph_ball, ConnectedSum.inrBall_apply]
  exact congrArg _ (Subtype.ext (ConnectedSum.coe_punctureBall _ _))

/-- The paths to the balls of the closed surface of genus `g`, defined together with the fact
that they meet no centre, which lets the recursion carry them into the second summand. -/
private def ballPathAux : (g j : ℕ) →
    {γ : Path (basePoint g) (ball g j (neckIsometry 1)) // ∀ t k, γ t ≠ ball g k 0}
  | 0, j => ⟨zeroBallPath j, zeroBallPath_ne_ball j⟩
  | g + 1, j =>
    ⟨succPath (ballPathAux g (j + 1)).val
        (fun t ↦ ConnectedSum.mem_puncture.2 ((ballPathAux g (j + 1)).property t 0))
        succDiffeomorph_basePoint (succDiffeomorph_ball_neckIsometry_one j),
      fun t k ↦ succPath_ne_ball _ _ _ _ ((ballPathAux g (j + 1)).property t (k + 1))⟩

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
the circle of the ball, crossing the real axis only inside that ball
(`ClosedSurface.ballPath_zero_zero`, `ClosedSurface.ballPath_zero_succ`). -/
def ballPath (j : ℕ) : Path (basePoint g) (ball g j (neckIsometry 1)) :=
  (ballPathAux g j).val

/-- The path to a ball meets no centre of a ball. -/
theorem ballPath_ne_ball (j : ℕ) (t : unitInterval) (k : ℕ) : ballPath g j t ≠ ball g k 0 :=
  (ballPathAux g j).property t k

/-- In the sphere, the path to the ball `0` is the segment from `0` to `(2, 2)` in the
complementary chart `ClosedSurface.sphereCoChart`. -/
theorem ballPath_zero_zero :
    ballPath 0 0 = ((Path.segment 0 !₂[2, 2]).map continuous_sphereCoChart).cast
      sphereCoChart_zero.symm ball_zero_zero_neckIsometry_one :=
  (rfl)

/-- In the sphere, the path to the ball `j + 1` is the segment from `0` to `(0, -1)` in the
complementary chart `ClosedSurface.sphereCoChart`, followed, in the chart
`ClosedSurface.sphereChart`, by the segment from `(0, -1)` to `(j + 5 / 4, -1)` and the segment
from there to `(j + 5 / 4, 1 / 4)`. -/
theorem ballPath_zero_succ (j : ℕ) :
    ballPath 0 (j + 1) = ((((Path.segment 0 !₂[0, -1]).map continuous_sphereCoChart).cast
        sphereCoChart_zero.symm sphereCoChart_zero_neg_one.symm).trans
      (((Path.segment !₂[0, -1] !₂[(j : ℝ) + 5 / 4, -1]).map continuous_sphereChart).trans
        ((Path.segment !₂[(j : ℝ) + 5 / 4, -1] !₂[(j : ℝ) + 5 / 4, 1 / 4]).map
          continuous_sphereChart))).cast
      rfl (by rw [ball_zero_neckIsometry_one]; push_cast; ring_nf) :=
  (rfl)

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
  simp only [ballPath, ballPathAux]
  exact succDiffeomorph_succPath_apply _ _ _ _ t

variable (g n) in
/-- The path to the ball `j`, as a path in `puncture g n`. -/
def puncturedBallPath (j : ℕ) :
    Path (⟨basePoint g, basePoint_mem_puncture⟩ : puncture g n)
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

/-! ### The paths to the torus summands -/

/-- In the closed surface of genus `g + 1`, the image under the summand `0` of the neck point of
the torus is the start of the circle of the ball `0` of genus `g`, in the second summand. -/
theorem succDiffeomorph_summand_zero_neckInl :
    succDiffeomorph (summand (g := g + 1) 0
        (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
          (neckIsometry.circleBasepoint one_pos))) =
      ConnectedSum.inr _ _ ⟨ball g 0 (neckIsometry 1), ConnectedSum.mem_puncture.2 (by simp)⟩ :=
  (succDiffeomorph_summand_zero _).trans inl_neckInl_circleBasepoint

variable (g) in
/-- The path to the torus summand `0` of genus `g + 1`. -/
private def summandPathZero :
    Path (basePoint (g + 1)) (summand 0 ⟨0, EuclideanTorus.zero_mem_puncture⟩) :=
  (succPath (x := ⟨basePoint g, basePoint_mem_puncture_ball_zero⟩)
      (y := ⟨ball g 0 (neckIsometry 1), ConnectedSum.mem_puncture.2 (by simp)⟩) (ballPath g 0)
      (fun t ↦ ConnectedSum.mem_puncture.2 (ballPath_ne_ball 0 t 0))
      succDiffeomorph_basePoint succDiffeomorph_summand_zero_neckInl).trans
    (EuclideanTorus.peripheralPath.symm.map (continuous_summand 0))

private theorem summandPathZero_ne_ball (t : unitInterval) (j : ℕ) :
    summandPathZero g t ≠ ball (g + 1) j 0 := by
  have ht := mem_range_self (f := ⇑(summandPathZero g)) t
  rw [summandPathZero, Path.trans_range] at ht
  rw [summandPathZero]
  rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]
    exact succPath_ne_ball _ _ _ _ (ballPath_ne_ball 0 s (j + 1))
  · rw [← hs]
    exact summand_ne_ball 0 _ j

/-- The paths to the torus summands, defined together with the fact that they meet no centre,
which lets the recursion carry them into the second summand. -/
private def summandPathAux : (g : ℕ) → (k : Fin g) →
    {γ : Path (basePoint g) (summand k ⟨0, EuclideanTorus.zero_mem_puncture⟩) //
      ∀ t j, γ t ≠ ball g j 0}
  | g + 1, ⟨0, _⟩ => ⟨summandPathZero g, summandPathZero_ne_ball⟩
  | g + 1, ⟨k + 1, hk⟩ =>
    ⟨succPath (summandPathAux g ⟨k, Nat.lt_of_succ_lt_succ hk⟩).val
        (fun t ↦ ConnectedSum.mem_puncture.2
          ((summandPathAux g ⟨k, Nat.lt_of_succ_lt_succ hk⟩).property t 0))
        succDiffeomorph_basePoint (succDiffeomorph_summand_succ ⟨k, _⟩ _),
      fun t j ↦ succPath_ne_ball _ _ _ _
        ((summandPathAux g ⟨k, Nat.lt_of_succ_lt_succ hk⟩).property t (j + 1))⟩

variable (g) in
/-- The **path to the torus summand `k`** of the closed surface of genus `g`: a path from the base
point to the point `0` of the punctured torus `summand k`, which meets no centre of a ball
(`ClosedSurface.summandPath_ne_ball`). For genus `g + 1` and `k = 0` it is the path to the ball
`0` of genus `g`, in the second summand, followed by the reverse of
`SymplecticGeometry.EuclideanTorus.peripheralPath` in the first summand, from the neck point to
`0` (`ClosedSurface.summandPath_succ_zero`); for `k + 1` it is the path to the summand `k` of
genus `g`, in the second summand (`ClosedSurface.succDiffeomorph_summandPath_succ_apply`). -/
def summandPath (k : Fin g) :
    Path (basePoint g) (summand k ⟨0, EuclideanTorus.zero_mem_puncture⟩) :=
  (summandPathAux g k).val

/-- The path to a torus summand meets no centre of a ball. -/
theorem summandPath_ne_ball (k : Fin g) (t : unitInterval) (j : ℕ) :
    summandPath g k t ≠ ball g j 0 :=
  (summandPathAux g k).property t j

/-- The path to the torus summand `0` of genus `g + 1`: the path to the ball `0` of genus `g`, in
the second summand, then, from the neck point, the reverse of
`SymplecticGeometry.EuclideanTorus.peripheralPath` in the first summand. -/
theorem summandPath_succ_zero :
    summandPath (g + 1) 0 =
      (succPath (x := ⟨basePoint g, basePoint_mem_puncture_ball_zero⟩)
        (y := ⟨ball g 0 (neckIsometry 1), ConnectedSum.mem_puncture.2 (by simp)⟩) (ballPath g 0)
        (fun t ↦ ConnectedSum.mem_puncture.2 (ballPath_ne_ball 0 t 0))
        succDiffeomorph_basePoint succDiffeomorph_summand_zero_neckInl).trans
      (EuclideanTorus.peripheralPath.symm.map (continuous_summand 0)) :=
  (rfl)

/-- The path to the torus summand `k + 1` of genus `g + 1` is the path to the summand `k` of
genus `g`, in the second summand of the connected sum. -/
theorem succDiffeomorph_summandPath_succ_apply (k : Fin g) (t : unitInterval) :
    succDiffeomorph (summandPath (g + 1) k.succ t) =
      ConnectedSum.inr _ _ ⟨summandPath g k t,
        ConnectedSum.mem_puncture.2 (summandPath_ne_ball k t 0)⟩ :=
  succDiffeomorph_succPath_apply _ _ succDiffeomorph_basePoint (succDiffeomorph_summand_succ _ _) t

/-- The path to a torus summand lies in each `puncture g n`. -/
@[simp]
theorem summandPath_mem_puncture (k : Fin g) (t : unitInterval) :
    summandPath g k t ∈ puncture g n :=
  mem_puncture.2 fun j _ ↦ summandPath_ne_ball k t j

/-- A punctured torus summand lies in each `puncture g n`. -/
@[simp]
theorem summand_mem_puncture (k : Fin g) (x : ConnectedSum.puncture EuclideanTorus.ball) :
    summand k x ∈ puncture g n :=
  mem_puncture.2 fun j _ ↦ summand_ne_ball k x j

variable (g n) in
/-- The path to the torus summand `k`, as a path in `puncture g n`. -/
def puncturedSummandPath (k : Fin g) :
    Path (⟨basePoint g, basePoint_mem_puncture⟩ : puncture g n)
      ⟨summand k ⟨0, EuclideanTorus.zero_mem_puncture⟩, summand_mem_puncture k _⟩ :=
  (summandPath g k).codRestrict fun t ↦ summandPath_mem_puncture k t

@[simp]
theorem coe_puncturedSummandPath_apply (k : Fin g) (t : unitInterval) :
    (puncturedSummandPath g n k t : ClosedSurface g) = summandPath g k t :=
  Path.codRestrict_coe _ _ t

@[simp]
theorem map_puncturedSummandPath (k : Fin g) :
    (puncturedSummandPath g n k).map continuous_subtypeVal = summandPath g k :=
  Path.map_codRestrict _ _

/-! ### The standard loops -/

variable (g) in
/-- The **standard circle** `i` of the torus summand `k` of the closed surface of genus `g`, as a
loop at the base point: the path `ClosedSurface.summandPath g k` to the point `0` of the summand,
then the image under the summand of the circle `SymplecticGeometry.EuclideanTorus.circleLoop i`,
then `summandPath g k` back: for `i = 0` the circle `a k` and for `i = 1` the circle `b k` of the
surface. -/
def circleLoop (k : Fin g) (i : Fin 2) : Path (basePoint g) (basePoint g) :=
  ((summandPath g k).trans ((EuclideanTorus.circleLoop i).map (continuous_summand k))).trans
    (summandPath g k).symm

variable (g) in
theorem circleLoop_def (k : Fin g) (i : Fin 2) :
    circleLoop g k i =
      ((summandPath g k).trans ((EuclideanTorus.circleLoop i).map (continuous_summand k))).trans
        (summandPath g k).symm :=
  (rfl)

/-- A standard circle of a torus summand meets no centre of a ball. -/
theorem circleLoop_ne_ball (k : Fin g) (i : Fin 2) (t : unitInterval) (j : ℕ) :
    circleLoop g k i t ≠ ball g j 0 := by
  have ht := mem_range_self (f := ⇑(circleLoop g k i)) t
  rw [circleLoop_def, Path.trans_range, Path.trans_range, Path.symm_range] at ht
  rcases ht with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
  · exact hs ▸ summandPath_ne_ball k s j
  · exact hs ▸ summand_ne_ball k _ j
  · exact hs ▸ summandPath_ne_ball k s j

/-- A standard circle of a torus summand lies in each `puncture g n`. -/
@[simp]
theorem circleLoop_mem_puncture (k : Fin g) (i : Fin 2) (t : unitInterval) :
    circleLoop g k i t ∈ puncture g n :=
  mem_puncture.2 fun j _ ↦ circleLoop_ne_ball k i t j

variable (g n) in
/-- The standard circle `i` of the torus summand `k`, as a loop in `puncture g n`. -/
def puncturedCircleLoop (k : Fin g) (i : Fin 2) :
    Path (⟨basePoint g, basePoint_mem_puncture⟩ : puncture g n)
      ⟨basePoint g, basePoint_mem_puncture⟩ :=
  (circleLoop g k i).codRestrict fun t ↦ circleLoop_mem_puncture k i t

@[simp]
theorem coe_puncturedCircleLoop_apply (k : Fin g) (i : Fin 2) (t : unitInterval) :
    (puncturedCircleLoop g n k i t : ClosedSurface g) = circleLoop g k i t :=
  Path.codRestrict_coe _ _ t

@[simp]
theorem map_puncturedCircleLoop (k : Fin g) (i : Fin 2) :
    (puncturedCircleLoop g n k i).map continuous_subtypeVal = circleLoop g k i :=
  Path.map_codRestrict _ _

/-- The standard circle `i` of the torus summand `k + 1` of genus `g + 1` is that of the summand
`k` of genus `g`, in the second summand of the connected sum. -/
theorem succDiffeomorph_circleLoop_succ_apply (k : Fin g) (i : Fin 2) (t : unitInterval) :
    succDiffeomorph (circleLoop (g + 1) k.succ i t) =
      ConnectedSum.inr _ _ ⟨circleLoop g k i t,
        ConnectedSum.mem_puncture.2 (circleLoop_ne_ball k i t 0)⟩ := by
  simp only [circleLoop_def, Path.trans_apply, Path.symm_apply]
  split_ifs <;> simp [succDiffeomorph_summandPath_succ_apply]

variable (g) in
/-- The **loop about the ball `j`** of the closed surface of genus `g`, at the base point: the
path `ClosedSurface.ballPath g j` to the ball, then the circle `ClosedSurface.ballCircle g j` of
the ball run backwards, then `ballPath g j` back. -/
def ballLoop (j : ℕ) : Path (basePoint g) (basePoint g) :=
  ((ballPath g j).trans (ballCircle g j).symm).trans (ballPath g j).symm

variable (g) in
theorem ballLoop_def (j : ℕ) :
    ballLoop g j = ((ballPath g j).trans (ballCircle g j).symm).trans (ballPath g j).symm :=
  (rfl)

/-- The loop about a ball meets no centre of a ball. -/
theorem ballLoop_ne_ball (j : ℕ) (t : unitInterval) (k : ℕ) : ballLoop g j t ≠ ball g k 0 := by
  have ht := mem_range_self (f := ⇑(ballLoop g j)) t
  rw [ballLoop_def, Path.trans_range, Path.trans_range, Path.symm_range, Path.symm_range] at ht
  rcases ht with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
  · exact hs ▸ ballPath_ne_ball j s k
  · exact hs ▸ ballCircle_ne_ball j s k
  · exact hs ▸ ballPath_ne_ball j s k

/-- The loop about a ball lies in each `puncture g n`. -/
@[simp]
theorem ballLoop_mem_puncture (j : ℕ) (t : unitInterval) : ballLoop g j t ∈ puncture g n :=
  mem_puncture.2 fun k _ ↦ ballLoop_ne_ball j t k

/-- The loop about the ball `j` of genus `g + 1` is that about the ball `j + 1` of genus `g`, in
the second summand of the connected sum. -/
theorem succDiffeomorph_ballLoop_apply (j : ℕ) (t : unitInterval) :
    succDiffeomorph (ballLoop (g + 1) j t) =
      ConnectedSum.inr _ _ ⟨ballLoop g (j + 1) t,
        ConnectedSum.mem_puncture.2 (ballLoop_ne_ball (j + 1) t 0)⟩ := by
  simp only [ballLoop_def, Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact succDiffeomorph_ballPath_apply _ _
  · exact succDiffeomorph_ballCircle_apply _ _
  · exact succDiffeomorph_ballPath_apply _ _

variable (g n) in
/-- The **peripheral loop** `i` of `puncture g n`, about the centre of the ball `i.rev`, at the
base point: the loop `ClosedSurface.ballLoop g i.rev` about that ball, as a loop in
`puncture g n`. -/
def peripheralLoop (i : Fin n) :
    Path (⟨basePoint g, basePoint_mem_puncture⟩ : puncture g n)
      ⟨basePoint g, basePoint_mem_puncture⟩ :=
  (ballLoop g i.rev).codRestrict fun t ↦ ballLoop_mem_puncture i.rev t

variable (g n) in
theorem peripheralLoop_def (i : Fin n) :
    peripheralLoop g n i =
      (ballLoop g i.rev).codRestrict fun t ↦ ballLoop_mem_puncture i.rev t :=
  (rfl)

@[simp]
theorem coe_peripheralLoop_apply (i : Fin n) (t : unitInterval) :
    (peripheralLoop g n i t : ClosedSurface g) = ballLoop g i.rev t :=
  Path.codRestrict_coe _ _ t

@[simp]
theorem map_peripheralLoop (i : Fin n) :
    (peripheralLoop g n i).map continuous_subtypeVal = ballLoop g i.rev :=
  Path.map_codRestrict _ _

/-- The peripheral loop `i` of `puncture (g + 1) n` is the peripheral loop `Fin.castSucc i` of
`puncture g (n + 1)`, in the second summand of the connected sum: both run about the ball `i.rev`
of genus `g + 1`, which is the ball `(Fin.castSucc i).rev = i.rev.succ` of genus `g`. -/
theorem succDiffeomorph_peripheralLoop_apply (i : Fin n) (t : unitInterval) :
    succDiffeomorph (peripheralLoop (g + 1) n i t : ClosedSurface (g + 1)) =
      ConnectedSum.inr _ _ ⟨(peripheralLoop g (n + 1) (Fin.castSucc i) t : ClosedSurface g),
        ConnectedSum.mem_puncture.2 fun h ↦
          mem_puncture.1 (peripheralLoop g (n + 1) (Fin.castSucc i) t).property 0 (Nat.succ_pos n)
            h⟩ := by
  have hi : ((Fin.castSucc i).rev : ℕ) = i.rev + 1 := by simp; omega
  rw [coe_peripheralLoop_apply]
  refine (succDiffeomorph_ballLoop_apply _ t).trans (congrArg _ (Subtype.ext ?_))
  rw [coe_peripheralLoop_apply, hi]

end SymplecticGeometry.ClosedSurface

end
